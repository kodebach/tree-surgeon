use std::{
    borrow::BorrowMut,
    cell::{Ref, RefCell},
    collections::{HashMap, HashSet},
    fs,
    io::{self, Read, Write},
    iter::once,
    ops::{Index, Neg, Range},
    path::{Path, PathBuf},
};

use ariadne::{Cache, Color, Label, Report, ReportKind, Source};
use convert_case::Casing;
use lazycell::LazyCell;
use miette::{Diagnostic, IntoDiagnostic, NamedSource, SourceSpan};
use tree_sitter::{
    InputEdit, Node, Parser, Point, Query, QueryCursor, QueryPredicateArg, Tree, TreeCursor,
};

use crate::{
    dsl::{
        ast::{
            ContainsExpr, EqualsExpr, Insert, InsertLocation, JoinItem, Match,
            MatchAction, MatchClause, Remove, Replace, Script, Statement, StringExpression, Warn,
            WhereExpr,
        },
        parser::Parsable,
    },
    single::{Single, SingleError},
};

trait SourceCache: Cache<PathBuf> {
    fn bytes(&self) -> SourceSliceRef;
    fn file(&self) -> &Path;

    fn translate_range(&self, range: Range<usize>) -> Range<usize>;

    fn update<F>(&mut self, update_fn: F)
    where
        F: FnOnce(&mut Vec<u8>);
}

#[derive(Clone)]
struct FileCache {
    bytes: RefCell<Vec<u8>>,
    source: LazyCell<Source>,
    file: PathBuf,
}

impl FileCache {
    fn new(bytes: Vec<u8>, file: PathBuf) -> FileCache {
        FileCache {
            bytes: RefCell::new(bytes),
            source: LazyCell::new(),
            file,
        }
    }
}

impl SourceCache for FileCache {
    fn bytes(&self) -> SourceSliceRef {
        SourceSliceRef {
            data: self.bytes.borrow(),
            span: None,
        }
    }

    fn file(&self) -> &Path {
        &self.file
    }

    fn translate_range(&self, range: Range<usize>) -> Range<usize> {
        range
    }

    fn update<F>(&mut self, update_fn: F)
    where
        F: FnOnce(&mut Vec<u8>),
    {
        update_fn(&mut self.bytes.borrow_mut());
    }
}

impl Cache<PathBuf> for FileCache {
    fn fetch(&mut self, id: &PathBuf) -> Result<&Source, Box<dyn std::fmt::Debug + '_>> {
        if id == &self.file {
            if !self.source.filled() {
                self.source
                    .fill(Source::from(String::from_utf8_lossy(&self.bytes.borrow())))
                    .unwrap();
            }

            Ok(&self.source.borrow().unwrap())
        } else {
            Err(Box::new(format!(
                "Failed to fetch source '{}'",
                id.display()
            )))
        }
    }

    fn display<'a>(&self, id: &'a PathBuf) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new(id.display()))
    }
}

#[derive(Clone)]
struct MacroCache {
    file_cache: FileCache,
    span: Range<usize>,
}

impl MacroCache {
    fn new(file_cache: FileCache, span: Range<usize>) -> MacroCache {
        MacroCache { file_cache, span }
    }

    fn offset(&self) -> usize {
        self.span.start
    }
}

struct SourceSliceRef<'a> {
    data: Ref<'a, Vec<u8>>,
    span: Option<Range<usize>>,
}

impl<'a> SourceSliceRef<'a> {
    fn get(&'a self) -> &'a [u8] {
        if let Some(span) = self.span.clone() {
            self.data.index(span)
        } else {
            &self.data
        }
    }
}

impl<'a> AsRef<[u8]> for SourceSliceRef<'a> {
    fn as_ref(&self) -> &[u8] {
        self.get()
    }
}

impl SourceCache for MacroCache {
    fn bytes(&self) -> SourceSliceRef {
        SourceSliceRef {
            data: self.file_cache.bytes.borrow(),
            span: Some(self.span.clone()),
        }
    }

    fn file(&self) -> &Path {
        self.file_cache.file()
    }

    fn translate_range(&self, range: Range<usize>) -> Range<usize> {
        let offset = self.offset();
        range.start + offset..range.end + offset
    }

    fn update<F>(&mut self, update_fn: F)
    where
        F: FnOnce(&mut Vec<u8>),
    {
        let mut macro_bytes = self.bytes().get().to_vec();
        update_fn(&mut macro_bytes);
        let new_span = self.offset()..self.offset() + macro_bytes.len();

        self.file_cache.borrow_mut().update(|bytes| {
            bytes.splice(self.span.clone(), macro_bytes);
        });
        self.span = new_span;
    }
}

impl Cache<PathBuf> for MacroCache {
    fn fetch(&mut self, id: &PathBuf) -> Result<&Source, Box<dyn std::fmt::Debug + '_>> {
        self.file_cache.borrow_mut().fetch(id)
    }

    fn display<'a>(&self, id: &'a PathBuf) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new(id.display()))
    }
}

type FileSpan = (PathBuf, Range<usize>);

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum LogLevel {
    Advice,
    Warning,
    Error,
    None,
}

pub struct Interpreter {
    cache: FileCache,
    tree: Tree,
    script: Script,
    parser: Parser,
    log_level: LogLevel,
    in_place: bool,
    parse_macros: bool,
    config: ariadne::Config,
}

#[derive(Diagnostic, Debug, thiserror::Error)]
enum StatementError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    Match(#[from] MatchError),
    #[error("interpreter received invalid statement")]
    #[diagnostic(code(tree_surgeon::script::invalid_statement))]
    Invalid,
}

#[derive(Diagnostic, Debug, thiserror::Error)]
enum MatchError {
    #[error(transparent)]
    #[diagnostic(code(tree_surgeon::r#match::single))]
    Single(#[from] SingleError),
    #[error(transparent)]
    #[diagnostic(transparent)]
    Replacement(#[from] ReplacementError),
    #[error(transparent)]
    #[diagnostic(transparent)]
    EditInErrorNode(#[from] EditInErrorNode),
    #[error(transparent)]
    #[diagnostic(code(tree_surgeon::io_error))]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    #[diagnostic(code(tree_surgeon::string::from_utf8))]
    FromUtf8(#[from] std::string::FromUtf8Error),
    #[error(transparent)]
    #[diagnostic(code(tree_surgeon::string::utf8))]
    Utf8(#[from] std::str::Utf8Error),
    #[error("Capture not found: {0}")]
    #[diagnostic(code(tree_surgeon::r#match::capture_not_found))]
    CaptureNotFound(String),
    #[error("{0}")]
    #[diagnostic(code(tree_surgeon::r#match::predicate_error))]
    PredicateError(String),
    #[error("interpreter received invalid query")]
    #[diagnostic(code(tree_surgeon::r#match::invalid_query))]
    InvalidQuery,
    #[error("Unknown predicate: {0}")]
    #[diagnostic(code(tree_surgeon::r#match::unknown_predicate))]
    UnknownPredicate(String),
}

#[derive(Diagnostic, Debug, thiserror::Error)]
enum ReplacementError {
    #[error("capture {capture_name} not found")]
    #[diagnostic(code(tree_surgeon::replace::missing_capture))]
    MissingCapture { capture_name: String },
    #[error(transparent)]
    #[diagnostic(transparent)]
    TreeParse(#[from] TreeParseError),
}

#[derive(Diagnostic, Debug, thiserror::Error)]
#[error("tried to make and edit within an error node")]
#[diagnostic(code(tree_surgeon::script::replace::edit_in_error))]
struct EditInErrorNode {
    #[source_code]
    src: NamedSource,
    error_label: String,
    #[label("{error_label}")]
    error_span: SourceSpan,
    #[label("tried to edit this")]
    edit_span: SourceSpan,
}

#[derive(Diagnostic, Debug, thiserror::Error)]
#[error("tree-sitter couldn't parse the file {source_file}")]
#[diagnostic(code(tree_surgeon::tree_sitter::parse_error))]
struct TreeParseError {
    source_file: PathBuf,
}

#[derive(Diagnostic, Debug, thiserror::Error)]
#[error("couldn't parse the script {script_file}")]
#[diagnostic(code(tree_surgeon::script::parse_error))]
struct ScriptParseError {
    script_file: PathBuf,
}

trait TreeCusorExt {
    fn error_iter(&self) -> TreeErrorIter;
}

impl<'a> TreeCusorExt for TreeCursor<'a> {
    fn error_iter(&self) -> TreeErrorIter {
        TreeErrorIter {
            cursor: self.clone(),
            next_node: Some(self.node()),
        }
    }
}

struct TreeErrorIter<'a> {
    cursor: TreeCursor<'a>,
    next_node: Option<Node<'a>>,
}

impl<'a> Iterator for TreeErrorIter<'a> {
    type Item = Node<'a>;

    fn next<'b>(&'b mut self) -> Option<Self::Item> {
        fn goto_next<'a>(iter: &mut TreeErrorIter<'a>) {
            while !iter.cursor.goto_next_sibling() {
                if !iter.cursor.goto_parent() {
                    iter.next_node = None;
                    return;
                }
            }

            iter.next_node = Some(iter.cursor.node());
        }

        loop {
            let node = if let Some(node) = self.next_node {
                node
            } else {
                break;
            };

            if node.is_error() {
                goto_next(self);
                return Some(node);
            } else {
                if self.cursor.goto_first_child() {
                    continue;
                }
            }

            goto_next(self);
        }

        None
    }
}

fn parse_source(
    parser: &mut Parser,
    cache: &impl SourceCache,
    log_level: LogLevel,
    old_tree: Option<&Tree>,
    config: ariadne::Config,
) -> WithReports<Option<Tree>> {
    let file = cache.file().to_path_buf();
    let tree = parser.parse(cache.bytes().get(), old_tree);

    if let Some(tree) = tree {
        let mut errors: Vec<_> = if log_level <= LogLevel::Advice {
            let cursor = tree.walk();
            let error_iter = cursor.error_iter();

            error_iter
                .map(|node| {
                    let parent = node.parent().unwrap_or(node);

                    let node_range = cache.translate_range(node.byte_range());
                    let parent_range = cache.translate_range(parent.byte_range());

                    Report::build(ReportKind::Advice, file.clone(), node_range.start)
                        .with_config(config)
                        .with_message("tree-sitter couldn't parse code fragment")
                        .with_label(
                            Label::new((file.clone(), parent_range)).with_message(parent.to_sexp()),
                        )
                        .with_label(
                            Label::new((file.clone(), node_range))
                                .with_message(node.to_sexp())
                                .with_color(Color::Red),
                        )
                        .finish()
                })
                .collect()
        } else {
            Vec::new()
        };

        if log_level <= LogLevel::Warning && errors.len() > 0 {
            errors.insert(
                0,
                Report::build(ReportKind::Warning, file.clone(), 0)
                    .with_config(config)
                    .with_message(format!(
                        "tree-sitter returned {} parse errors",
                        errors.len()
                    ))
                    .finish(),
            )
        }

        WithReports {
            data: Some(tree),
            reports: errors,
        }
    } else {
        if log_level <= LogLevel::Error {
            let error = Report::build(ReportKind::Error, file.clone(), 0)
                .with_config(config)
                .with_message("tree-sitter couldn't parse source file")
                .finish();

            WithReports {
                data: None,
                reports: vec![error],
            }
        } else {
            WithReports {
                data: None,
                reports: Vec::default(),
            }
        }
    }
}

#[derive(Debug)]
struct TreeEdit {
    edit: InputEdit,
    new_text: String,
}

trait WithReportsData {
    fn combine(&mut self, second: Self);
}

impl WithReportsData for Vec<TreeEdit> {
    fn combine(&mut self, second: Self) {
        for other in second {
            let overlap = self.iter().any(|e| {
                e.edit.start_byte < other.edit.old_end_byte
                    && other.edit.start_byte < e.edit.old_end_byte
            });

            if !overlap {
                self.push(other);
            }
        }
    }
}

#[derive(Default, Debug)]
struct WithReports<T> {
    data: T,
    reports: Vec<Report<'static, FileSpan>>,
}

impl<T: WithReportsData> WithReports<T> {
    fn chain<F, E>(mut self, next: F) -> Result<Self, E>
    where
        F: FnOnce() -> Result<Self, E>,
    {
        let result = next()?;

        self.data.combine(result.data);
        self.reports.extend(result.reports);

        Ok(WithReports {
            data: self.data,
            reports: self.reports,
        })
    }
}

type MatchResult = Result<WithReports<Vec<TreeEdit>>, MatchError>;
type StatementResult = Result<WithReports<Vec<TreeEdit>>, StatementError>;

fn execute_match_in_macros(
    m: &Match,
    parser: &mut Parser,
    cache: &FileCache,
    tree: &Tree,
    log_level: LogLevel,
    config: ariadne::Config,
) -> MatchResult {
    let macro_query = Query::new(tree_sitter_c::language(), "((preproc_arg) @macro)")
        .expect("macro_query broken");

    let macros = get_matches(&macro_query, &[], tree, cache.bytes().get())?;

    macros
        .iter()
        .try_fold(WithReports::default(), |result, query_match| {
            result.chain(|| {
                let node = query_match.captures.get("macro").expect("@macro not found");
                let macro_cache = MacroCache::new(cache.clone(), node.byte_range());

                let WithReports {
                    data: tree,
                    reports,
                } = parse_source(parser, &macro_cache, log_level, None, config);

                WithReports {
                    data: Vec::default(),
                    reports,
                }
                .chain(|| {
                    if let Some(tree) = tree {
                        execute_match_on_tree(m, &macro_cache, &tree, config)
                    } else {
                        Ok(WithReports::default())
                    }
                })
            })
        })
}

fn execute_match_on_tree(
    m: &Match,
    cache: &impl SourceCache,
    tree: &Tree,
    config: ariadne::Config,
) -> MatchResult {
    let old_source = cache.bytes().get().to_vec();

    let crate::dsl::ast::Query::Query(query) = &m.query else {
        return Err(MatchError::InvalidQuery)
    };

    let matches = get_matches(query, &m.clauses, tree, &old_source)?;

    let get_src = || {
        Ok(NamedSource::new(
            cache.file().to_string_lossy(),
            String::from_utf8(cache.bytes().get().to_vec()).map_err(MatchError::FromUtf8)?,
        ))
    };

    matches
        .iter()
        .try_fold(WithReports::default(), |result, query_match| {
            result.chain(|| match &m.action {
                MatchAction::Replace(replace) => {
                    execute_replace(replace, &query_match, get_src, &old_source)
                }
                MatchAction::Warn(warn) => {
                    execute_warn(warn, &query_match, cache, &old_source, config)
                }
                MatchAction::Remove(remove) => {
                    execute_remove(remove, &query_match, get_src)
                }
                MatchAction::Insert(insert) => {
                    execute_insert(insert, &query_match, get_src, &old_source)
                }
            })
        })
}

fn execute_match(
    m: &Match,
    parser: &mut Parser,
    cache: &FileCache,
    tree: &Tree,
    log_level: LogLevel,
    parse_macros: bool,
    config: ariadne::Config,
) -> MatchResult {
    execute_match_on_tree(m, cache, tree, config)?.chain(|| {
        if parse_macros {
            execute_match_in_macros(m, parser, cache, tree, log_level, config)
        } else {
            Ok(WithReports::default())
        }
    })
}

fn error_ancestor(node: Node) -> Option<Node> {
    if let Some(parent) = node.parent() {
        if parent.is_error() {
            Some(parent)
        } else {
            error_ancestor(parent)
        }
    } else {
        None
    }
}

fn execute_replace<F>(
    replace: &Replace,
    query_match: &QueryMatch,
    get_src: F,
    source: &[u8],
) -> MatchResult
where
    F: FnOnce() -> Result<NamedSource, MatchError>,
{
    let node = query_match
        .captures
        .get(&replace.capture_name)
        .ok_or(MatchError::Replacement(ReplacementError::MissingCapture {
            capture_name: replace.capture_name.clone(),
        }))?
        .to_owned();
    let start_byte = node.start_byte();
    let old_end_byte = node.end_byte();
    let start_position = node.start_position();
    let old_end_position = node.end_position();

    if let Some(error) = error_ancestor(node) {
        let error_start_byte = error.start_byte();
        let error_end_byte = error.end_byte();

        return Err(MatchError::EditInErrorNode(EditInErrorNode {
            src: get_src()?,
            error_span: (error_start_byte, error_end_byte - error_start_byte).into(),
            error_label: error.to_sexp(),
            edit_span: (start_byte, old_end_byte - start_byte).into(),
        }));
    }

    let new_text = evaluate_string_expression(
        &replace.replacement,
        |name| {
            query_match
                .captures
                .get(name)
                .ok_or(MatchError::Replacement(ReplacementError::MissingCapture {
                    capture_name: name.to_string(),
                }))
                .copied()
        },
        source,
    )?;

    let line_ending_count = new_text.chars().filter(|c| *c == '\n').count();
    let last_line_len = new_text.chars().rev().take_while(|c| *c != '\n').count();

    let tree_edit = TreeEdit {
        edit: InputEdit {
            start_byte,
            old_end_byte,
            start_position,
            old_end_position,
            new_end_byte: start_byte + new_text.len(),
            new_end_position: Point {
                row: start_position.row + line_ending_count,
                column: if line_ending_count == 0 {
                    start_position.column + new_text.len()
                } else {
                    last_line_len
                },
            },
        },
        new_text,
    };

    Ok(WithReports {
        data: vec![tree_edit],
        reports: Vec::default(),
    })
}

fn execute_insert<F>(
    insert: &Insert,
    query_match: &QueryMatch,
    get_src: F,
    source: &[u8],
) -> MatchResult
where
    F: FnOnce() -> Result<NamedSource, MatchError>,
{
    let node = query_match
        .captures
        .get(&insert.capture_name)
        .ok_or(MatchError::Replacement(ReplacementError::MissingCapture {
            capture_name: insert.capture_name.clone(),
        }))?
        .to_owned();

    let start_byte = node.start_byte();
    let old_end_byte = node.end_byte();
    let start_position = node.start_position();
    let old_end_position = node.end_position();

    if let Some(error) = error_ancestor(node) {
        let error_start_byte = error.start_byte();
        let error_end_byte = error.end_byte();

        return Err(MatchError::EditInErrorNode(EditInErrorNode {
            src: get_src()?,
            error_span: (error_start_byte, error_end_byte - error_start_byte).into(),
            error_label: error.to_sexp(),
            edit_span: (start_byte, old_end_byte - start_byte).into(),
        }));
    }

    let new_text = evaluate_string_expression(
        &insert.insertion,
        |name| {
            query_match
                .captures
                .get(name)
                .ok_or(MatchError::Replacement(ReplacementError::MissingCapture {
                    capture_name: name.to_string(),
                }))
                .copied()
        },
        source,
    )?;

    let line_ending_count = new_text.chars().filter(|c| *c == '\n').count();
    let last_line_len = new_text.chars().rev().take_while(|c| *c != '\n').count();

    let tree_edit = match insert.location {
        InsertLocation::Before => TreeEdit {
            edit: InputEdit {
                start_byte,
                old_end_byte: start_byte,
                start_position,
                old_end_position: start_position,
                new_end_byte: start_byte + new_text.len(),
                new_end_position: Point {
                    row: start_position.row + line_ending_count,
                    column: if line_ending_count == 0 {
                        start_position.column + new_text.len()
                    } else {
                        last_line_len
                    },
                },
            },
            new_text,
        },
        InsertLocation::After => TreeEdit {
            edit: InputEdit {
                start_byte: old_end_byte,
                old_end_byte,
                start_position: old_end_position,
                old_end_position,
                new_end_byte: old_end_byte + new_text.len(),
                new_end_position: Point {
                    row: old_end_position.row + line_ending_count,
                    column: if line_ending_count == 0 {
                        old_end_position.column + new_text.len()
                    } else {
                        last_line_len
                    },
                },
            },
            new_text,
        },
    };

    Ok(WithReports {
        data: vec![tree_edit],
        reports: Vec::default(),
    })
}

fn execute_remove<F>(
    remove: &Remove,
    query_match: &QueryMatch,
    get_src: F,
) -> MatchResult
where
    F: FnOnce() -> Result<NamedSource, MatchError>,
{
    let node = query_match
        .captures
        .get(&remove.capture_name)
        .ok_or(MatchError::Replacement(ReplacementError::MissingCapture {
            capture_name: remove.capture_name.clone(),
        }))?
        .to_owned();

    let start_byte = node.start_byte();
    let old_end_byte = node.end_byte();
    let start_position = node.start_position();
    let old_end_position = node.end_position();

    if let Some(error) = error_ancestor(node) {
        let error_start_byte = error.start_byte();
        let error_end_byte = error.end_byte();

        return Err(MatchError::EditInErrorNode(EditInErrorNode {
            src: get_src()?,
            error_span: (error_start_byte, error_end_byte - error_start_byte).into(),
            error_label: error.to_sexp(),
            edit_span: (start_byte, old_end_byte - start_byte).into(),
        }));
    }

    let tree_edit = TreeEdit {
        edit: InputEdit {
            start_byte,
            old_end_byte,
            start_position,
            old_end_position,
            new_end_byte: start_byte,
            new_end_position: Point {
                row: start_position.row,
                column: start_position.column,
            },
        },
        new_text: String::default(),
    };

    Ok(WithReports {
        data: vec![tree_edit],
        reports: Vec::default(),
    })
}

fn evaluate_string_expression<'tree, F>(
    expression: &StringExpression,
    get_capture_node: F,
    source: &[u8],
) -> Result<String, MatchError>
where
    F: Fn(&str) -> Result<Node<'tree>, MatchError>,
{
    let value = match expression {
        StringExpression::Literal(new_text) => new_text.clone(),
        StringExpression::Join(items) => items
            .iter()
            .map(|item| match item {
                JoinItem::CaptureExpr(capture_expr) => get_capture_node(&capture_expr.capture_name)
                    .and_then(|n| n.utf8_text(source).map_err(MatchError::Utf8))
                    .map(|text| {
                        capture_expr
                            .target_case
                            .map_or(text.to_owned(), |case| text.to_case(case.into()))
                    })
                    .map(|text| {
                        capture_expr
                            .range
                            .as_ref()
                            .map(|Range { start, end }| {
                                start.map_or(0, |s| {
                                    if s.is_negative() {
                                        text.len() - s.neg() as usize
                                    } else {
                                        s as usize
                                    }
                                })..end.map_or(text.len(), |e| {
                                    if e.is_negative() {
                                        text.len() - e.neg() as usize
                                    } else {
                                        e as usize
                                    }
                                })
                            })
                            .map_or(text.to_owned(), |range| (&text[range]).to_owned())
                    }),
                JoinItem::Literal(new_text) => Ok(new_text.to_owned()),
            })
            .collect::<Result<String, _>>()?,
    };
    Ok(value)
}

fn execute_warn(
    warn: &Warn,
    query_match: &QueryMatch,
    cache: &impl SourceCache,
    source: &[u8],
    config: ariadne::Config,
) -> MatchResult {
    let node = query_match.captures.get(&warn.capture_name);

    let Some(node) = node else { return Ok(WithReports::default()); };

    let msg = evaluate_string_expression(
        &warn.message,
        |name| {
            query_match
                .captures
                .get(name)
                .ok_or(MatchError::CaptureNotFound(name.to_string()))
                .copied()
        },
        source,
    )?;

    let file = cache.file();

    let byte_range = cache.translate_range(node.byte_range());

    let report: Report<FileSpan> =
        Report::build(ReportKind::Warning, file.to_owned(), byte_range.start)
            .with_config(config)
            .with_label(
                Label::new((file.to_owned(), byte_range))
                    .with_message(msg)
                    .with_color(Color::Yellow),
            )
            .finish();

    Ok(WithReports {
        data: Vec::default(),
        reports: vec![report],
    })
}

struct QueryMatch<'tree> {
    captures: HashMap<String, Node<'tree>>,
}

fn evaluate_query_predicates(
    query: &Query,
    query_match: &tree_sitter::QueryMatch,
    source: &[u8],
) -> Result<bool, MatchError> {
    query
        .general_predicates(query_match.pattern_index)
        .iter()
        .try_fold(true, |result, predicate| {
            if !result {
                return Ok(false);
            }

            let invert: bool;
            let name = if predicate.operator.starts_with("not-") {
                invert = true;
                &predicate.operator[4..]
            } else {
                invert = false;
                &predicate.operator
            };

            let matching = match name {
                "in-list?" => {
                    if predicate.args.len() < 2 {
                        return Err(MatchError::PredicateError(
                            "#in-list? requires at least 2 arguments".to_string(),
                        ));
                    }

                    let QueryPredicateArg::Capture(capture) = predicate.args[0] else {
                            return Err(MatchError::PredicateError(
                                "The first argument to #in-list? must be a capture reference"
                                    .to_string(),
                            ));
                        };

                    let strings: HashSet<&str> = predicate.args[1..]
                        .iter()
                        .filter_map(|arg| {
                            if let QueryPredicateArg::String(s) = arg {
                                Some(s.as_ref())
                            } else {
                                None
                            }
                        })
                        .collect();

                    if strings.len() + 1 != predicate.args.len() {
                        return Err(MatchError::PredicateError(
                            "All arguments to #in-list? except for the first, must be strings"
                                .to_string(),
                        ));
                    }

                    let node = query_match
                        .nodes_for_capture_index(capture)
                        .single()
                        .map_err(MatchError::Single)?;

                    let node_text = node.utf8_text(source).map_err(MatchError::Utf8)?;

                    strings.contains(&node_text)
                }
                s => {
                    return Err(MatchError::UnknownPredicate(s.to_string()));
                }
            };

            Ok(invert ^ matching)
        })
}

fn get_matches<'t>(
    query: &Query,
    clauses: &[MatchClause],
    tree: &'t Tree,
    source: &[u8],
) -> Result<Vec<QueryMatch<'t>>, MatchError> {
    QueryCursor::new()
        .matches(&query, tree.root_node(), source)
        .try_fold(Vec::default(), |mut matches, query_match| {
            let predicates_matching = evaluate_query_predicates(query, &query_match, source)?;

            if !predicates_matching {
                return Ok(matches);
            }

            let captures: HashMap<_, _> = query_match
                .captures
                .iter()
                .map(|c| (query.capture_names()[c.index as usize].clone(), c.node))
                .chain(once(("".to_string(), tree.root_node())))
                .collect();

            let clauses_matching = clauses.iter().try_fold(true, |result, clause| {
                let result = result
                    && match clause {
                        MatchClause::Where(w) => evaluate_where(w, &captures, source)?,
                    };

                Ok::<bool, MatchError>(result)
            })?;

            if !clauses_matching {
                return Ok(matches);
            }

            matches.push(QueryMatch { captures });

            Ok(matches)
        })
}

fn evaluate_where(
    where_expr: &WhereExpr,
    captures: &HashMap<String, Node>,
    source: &[u8],
) -> Result<bool, MatchError> {
    let get_capture_node = |name: &str| {
        captures
            .get(name)
            .ok_or(MatchError::CaptureNotFound(name.to_string()))
            .copied()
    };

    return match where_expr {
        WhereExpr::Equals(EqualsExpr { left, right }) => {
            let left = evaluate_string_expression(left, get_capture_node, source)?;
            let right = evaluate_string_expression(right, get_capture_node, source)?;

            Ok(left == right)
        }
        WhereExpr::Contains(ContainsExpr {
            capture_name,
            query,
        }) => {
            let node = get_capture_node(&capture_name)?;

            let crate::dsl::ast::Query::Query(query) = query else {
                return Err(MatchError::InvalidQuery)
            };

            let contains = 'result: {
                for query_match in QueryCursor::new().matches(query, node, source) {
                    if evaluate_query_predicates(query, &query_match, source)? {
                        break 'result true;
                    }
                }
                false
            };

            Ok(contains)
        }
    };
}

fn execute_statement(
    statement: &Statement,
    parser: &mut Parser,
    cache: &FileCache,
    tree: &Tree,
    log_level: LogLevel,
    parse_macros: bool,
    config: ariadne::Config,
) -> StatementResult {
    match statement {
        Statement::Match(m) => {
            execute_match(m, parser, cache, tree, log_level, parse_macros, config)
                .map_err(StatementError::Match)
        }
        Statement::Invalid => Err(StatementError::Invalid),
    }
}

fn execute_script(
    script: &Script,
    parser: &mut Parser,
    cache: &FileCache,
    tree: &Tree,
    log_level: LogLevel,
    parse_macros: bool,
    config: ariadne::Config,
) -> StatementResult {
    script
        .statements
        .iter()
        .try_fold(WithReports::default(), |result, statement| {
            result.chain(|| {
                execute_statement(
                    statement,
                    parser,
                    cache,
                    tree,
                    log_level,
                    parse_macros,
                    config,
                )
            })
        })
}

impl Interpreter {
    pub fn new(
        source_file: PathBuf,
        script_file: Option<PathBuf>,
        log_level: LogLevel,
        in_place: bool,
        parse_macros: bool,
        config: ariadne::Config,
    ) -> miette::Result<Interpreter> {
        let mut parser = Parser::new();
        parser
            .set_language(tree_sitter_c::language())
            .into_diagnostic()?;

        let script_source = if let Some(ref script_file) = script_file {
            let script_buf = fs::read(&script_file).into_diagnostic()?;

            String::from_utf8(script_buf).into_diagnostic()?
        } else {
            let stdin = std::io::stdin();
            let mut source = String::new();
            stdin.lock().read_to_string(&mut source).into_diagnostic()?;

            source
        };

        let source = fs::read(&source_file).into_diagnostic()?;

        let cache = FileCache::new(source, source_file);

        let WithReports {
            data: tree,
            reports,
        } = parse_source(&mut parser, &cache, log_level, None, config);

        for report in reports {
            report.eprint(cache.clone()).into_diagnostic()?;
        }

        let tree = tree
            .ok_or(TreeParseError {
                source_file: cache.file.to_owned(),
            })
            .into_diagnostic()?;

        let script_file = script_file.unwrap_or(PathBuf::from("<stdin>"));

        let (script, reports) = Script::parse(&script_source, tree.language(), config);

        for report in reports {
            report
                .eprint(Source::from(&script_source))
                .into_diagnostic()?;
        }

        let script = script
            .ok_or(ScriptParseError { script_file })
            .into_diagnostic()?;

        Ok(Interpreter {
            cache,
            tree,
            script,
            parser,
            log_level,
            in_place,
            parse_macros,
            config,
        })
    }

    pub fn run(mut self) -> miette::Result<()> {
        let mut reports = Vec::default();
        loop {
            let mut result = execute_script(
                &self.script,
                &mut self.parser,
                &mut self.cache,
                &mut self.tree,
                self.log_level,
                self.parse_macros,
                self.config,
            )?;

            reports.append(&mut result.reports);

            let edits = result.data;

            if edits.is_empty() {
                break;
            }

            for TreeEdit { edit, new_text } in edits {
                self.cache.update(|bytes| {
                    bytes.splice(edit.start_byte..edit.old_end_byte, new_text.bytes());
                });
                self.tree.edit(&edit);

                let WithReports {
                    data: new_tree,
                    reports: mut new_reports,
                } = parse_source(
                    &mut self.parser,
                    &self.cache,
                    self.log_level,
                    Some(&self.tree),
                    self.config,
                );

                reports.append(&mut new_reports);

                self.tree = new_tree.ok_or(MatchError::Replacement(
                    ReplacementError::TreeParse(TreeParseError {
                        source_file: self.cache.file().to_owned(),
                    }),
                ))?;
            }
        }

        if self.in_place {
            fs::write(self.cache.file(), self.cache.bytes()).into_diagnostic()?;
        } else {
            io::stdout()
                .write(self.cache.bytes().get())
                .into_diagnostic()?;
        }

        for report in reports {
            report.eprint(self.cache.clone()).into_diagnostic()?;
        }

        Ok(())
    }
}

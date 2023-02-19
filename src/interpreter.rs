use std::{
    fs,
    io::{self, Read, Write},
    ops::Range,
    path::{Path, PathBuf},
};

use ariadne::{Cache, Color, Label, Report, ReportKind, Source, Span};
use convert_case::Casing;
use miette::{Diagnostic, IntoDiagnostic, NamedSource, SourceSpan};
use tree_sitter::{
    InputEdit, Node, Parser, Point, Query, QueryCapture, QueryCursor, QueryPredicateArg, Tree,
    TreeCursor,
};

use crate::{
    dsl::{
        ast::{JoinItem, Match, Replacement, Script, Statement},
        parser::Parsable,
    },
    single::{Single, SingleError},
};

trait SourceCache : Cache<PathBuf> {
    fn bytes(&self) -> &[u8];
    fn file(&self) -> &Path;

    fn update<F>(&mut self, update_fn: F)
    where
        F: FnOnce(&mut Vec<u8>);
}

struct FileCache {
    bytes: Vec<u8>,
    src: Source,
    file: PathBuf,
}

impl FileCache {
    fn new(bytes: Vec<u8>, file: PathBuf) -> FileCache {
        FileCache {
            src: Source::from(String::from_utf8_lossy(&bytes)),
            bytes,
            file,
        }
    }
}

impl SourceCache for FileCache {
    fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    fn file(&self) -> &Path {
        &self.file
    }

    fn update<F>(&mut self, update_fn: F)
    where
        F: FnOnce(&mut Vec<u8>),
    {
        update_fn(&mut self.bytes);
        self.src = Source::from(String::from_utf8_lossy(&self.bytes));
    }
}

impl Cache<PathBuf> for FileCache {
    fn fetch(&mut self, id: &PathBuf) -> Result<&Source, Box<dyn std::fmt::Debug + '_>> {
        if id == &self.file {
            Ok(&self.src)
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

struct MacroCache<'file> {
    file_cache: &'file mut FileCache,
    span: Range<usize>,
}

impl<'file> MacroCache<'file> {
    fn new(file_cache: &'file mut FileCache, span: Range<usize>) -> MacroCache<'file> {
        MacroCache { file_cache, span }
    }
}

impl<'file> SourceCache for MacroCache<'file> {
    fn bytes(&self) -> &[u8] {
        &self.file_cache.bytes[self.span.clone()]
    }

    fn file(&self) -> &Path {
        self.file_cache.file()
    }

    fn update<F>(&mut self, update_fn: F)
    where
        F: FnOnce(&mut Vec<u8>),
    {
        let mut macro_bytes = self.bytes().to_vec();
        update_fn(&mut macro_bytes);

        self.file_cache.update(|bytes| {
            bytes.splice(self.span.clone(), macro_bytes);
        });
    }
}

impl<'file> Cache<PathBuf> for MacroCache<'file> {
    fn fetch(&mut self, id: &PathBuf) -> Result<&Source, Box<dyn std::fmt::Debug + '_>> {
        self.file_cache.fetch(id)
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
    bytes: &[u8],
    file: &Path,
    log_level: LogLevel,
    old_tree: Option<&Tree>,
) -> (Option<Tree>, Vec<Report<FileSpan>>) {
    let file = file.to_path_buf();
    let tree = parser.parse(bytes, old_tree);

    if let Some(tree) = tree {
        let mut errors: Vec<_> = if log_level <= LogLevel::Advice {
            let cursor = tree.walk();
            let error_iter = cursor.error_iter();

            error_iter
                .map(|node| {
                    let parent = node.parent().unwrap_or(node);
                    Report::build(ReportKind::Advice, file.clone(), node.start_byte())
                        .with_message("tree-sitter couldn't parse code fragment")
                        .with_label(
                            Label::new((file.clone(), parent.byte_range()))
                                .with_message(parent.to_sexp()),
                        )
                        .with_label(
                            Label::new((file.clone(), node.byte_range()))
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
                    .with_message(format!(
                        "tree-sitter returned {} parse errors",
                        errors.len()
                    ))
                    .finish(),
            )
        }

        (Some(tree), errors)
    } else {
        if log_level <= LogLevel::Error {
            let error = Report::build(ReportKind::Error, file.clone(), 0)
                .with_message("tree-sitter couldn't parse source file")
                .finish();

            (None, vec![error])
        } else {
            (None, Vec::new())
        }
    }
}

fn get_capture_node<'tree>(
    query: &Query,
    captures: &[QueryCapture<'tree>],
    capture_name: &str,
) -> Result<Node<'tree>, MatchError> {
    let capture_index = if let Some(capture_index) = query.capture_index_for_name(capture_name) {
        capture_index
    } else {
        return Err(MatchError::Replacement(ReplacementError::MissingCapture {
            capture_name: capture_name.to_string(),
        }));
    };

    captures
        .iter()
        .filter_map(move |capture| {
            if capture.index == capture_index {
                Some(capture.node)
            } else {
                None
            }
        })
        .single()
        .map_err(MatchError::Single)
}

fn execute_match(
    m: &Match,
    parser: &mut Parser,
    cache: &mut impl SourceCache,
    tree: &mut Tree,
    log_level: LogLevel,
) -> Result<(), MatchError> {
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

    let query = m.query();

    loop {
        let old_tree = tree.clone();
        let old_source = cache.bytes().to_vec();

        let matches = get_matches(query, &old_tree, &old_source);

        if let Some(query_match) = matches.iter().next() {
            let replacement = m.replacement();
            let capture_name = replacement.capture_name();

            let node = get_capture_node(query, &query_match.captures, capture_name)?;

            let start_byte = node.start_byte();
            let old_end_byte = node.end_byte();
            let start_position = node.start_position();
            let old_end_position = node.end_position();

            if let Some(error) = error_ancestor(node) {
                let error_start_byte = error.start_byte();
                let error_end_byte = error.end_byte();

                return Err(MatchError::EditInErrorNode(EditInErrorNode {
                    src: NamedSource::new(
                        cache.file().to_string_lossy(),
                        String::from_utf8(cache.bytes().to_vec()).map_err(MatchError::FromUtf8)?,
                    ),
                    error_span: (error_start_byte, error_end_byte - error_start_byte).into(),
                    error_label: error.to_sexp(),
                    edit_span: (start_byte, old_end_byte - start_byte).into(),
                }));
            }

            let new_text = match &replacement.replacement() {
                Replacement::Literal(new_text) => new_text.clone(),
                Replacement::Join(items) => items
                    .iter()
                    .map(|item| match item {
                        JoinItem::CaptureExpr(capture_expr) => get_capture_node(
                            query,
                            &query_match.captures,
                            capture_expr.capture_name(),
                        )
                        .and_then(|n| n.utf8_text(&old_source).map_err(MatchError::Utf8))
                        .map(|text| {
                            capture_expr
                                .target_case()
                                .map_or(text.to_owned(), |case| text.to_case(case.into()))
                        })
                        .map(|text| {
                            capture_expr
                                .range()
                                .map(|Range { start, end }| {
                                    start.unwrap_or(0)..end.unwrap_or(text.len())
                                })
                                .map_or(text.to_owned(), |range| (&text[range]).to_owned())
                        }),
                        JoinItem::Literal(new_text) => Ok(new_text.to_owned()),
                    })
                    .collect::<Result<String, _>>()?,
            };

            let line_ending_count = new_text.chars().filter(|c| *c == '\n').count();
            let last_line_len = new_text.chars().rev().take_while(|c| *c != '\n').count();

            let edit = InputEdit {
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
            };

            cache.update(|bytes| {
                bytes.splice(edit.start_byte..edit.old_end_byte, new_text.bytes());
            });

            tree.edit(&edit);

            // TODO (opti): instead of re-parsing the tree after every change, try to apply as many changes as possible without overlap before parsing again
            *tree = parse_source(parser, cache.bytes(), cache.file(), log_level, Some(tree))
                .print_reports(cache)
                .map_err(MatchError::Io)?
                .ok_or(MatchError::Replacement(ReplacementError::TreeParse(
                    TreeParseError {
                        source_file: cache.file().to_owned(),
                    },
                )))?;
        } else {
            break Ok(());
        }
    }
}

struct QueryMatch<'tree> {
    captures: Vec<QueryCapture<'tree>>,
}

fn get_matches<'t>(query: &Query, old_tree: &'t Tree, old_source: &Vec<u8>) -> Vec<QueryMatch<'t>> {
    let mut cursor = QueryCursor::new();

    cursor
        .matches(&query, old_tree.root_node(), old_source.as_slice())
        .filter(|query_match| {
            query
                .general_predicates(query_match.pattern_index)
                .iter()
                .all(|predicate| {
                    let invert: bool;
                    let name = if predicate.operator.starts_with("not-") {
                        invert = true;
                        &predicate.operator[4..]
                    } else {
                        invert = false;
                        &predicate.operator
                    };

                    let result = match name {
                        "in-list?" => {
                            if predicate.args.len() < 2 {
                                eprintln!("Too few args");
                                return false; // TODO: error
                            }

                            if let QueryPredicateArg::Capture(capture) = predicate.args[0] {
                                let strings: Vec<&str> = predicate.args[1..]
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
                                    eprintln!("rest not all strings");
                                    return false; // TODO: error
                                }

                                let node = query_match
                                    .nodes_for_capture_index(capture)
                                    .single()
                                    .unwrap(); // TODO: error

                                let node_text = node.utf8_text(old_source).unwrap(); // TODO: error

                                strings.contains(&node_text)
                            } else {
                                eprintln!("first not capture");
                                false // TODO: error
                            }
                        }
                        s => {
                            // TODO: report error
                            eprintln!("unknown predicate {}", s);
                            false
                        }
                    };

                    invert ^ result
                })
        })
        .map(|query_match| QueryMatch {
            captures: query_match.captures.to_owned(),
        })
        .collect()
}

fn execute_match_in_macros(
    m: &Match,
    parser: &mut Parser,
    cache: &mut FileCache,
    tree: &mut Tree,
    log_level: LogLevel,
) -> Result<(), MatchError> {
    let macro_query = Query::new(tree_sitter_c::language(), "((preproc_arg) @macro)")
        .expect("macro_query broken");

    let macros = get_matches(&macro_query, &tree, &cache.bytes);

    for query_match in macros {
        let node = get_capture_node(&macro_query, &query_match.captures, "macro")
            .expect("@macro not found");
        let text = node.utf8_text(&cache.bytes)?.as_bytes().to_owned();

        let mut macro_cache = MacroCache::new(cache, node.byte_range());

        if let Some(mut tree) = parse_source(parser, &text, &PathBuf::new(), log_level, None)
            .print_reports(&mut macro_cache)?
        {
            execute_match(m, parser, &mut macro_cache, &mut tree, log_level)?;
        }
    }

    Ok(())
}

fn execute_statement(
    statement: &Statement,
    parser: &mut Parser,
    cache: &mut FileCache,
    tree: &mut Tree,
    log_level: LogLevel,
) -> Result<(), StatementError> {
    match statement {
        Statement::Match(m) => {
            execute_match(m, parser, cache, tree, log_level)?;
            execute_match_in_macros(m, parser, cache, tree, log_level)?;

            Ok(())
        }
        Statement::Invalid => Err(StatementError::Invalid),
    }
}

trait ParseResult<C, S>
where
    C: Cache<S::SourceId>,
    S: Span,
{
    type Data;

    fn print_reports(self, cache: &mut C) -> std::io::Result<Self::Data>;
}

impl<'a, T, C, S> ParseResult<C, S> for (Option<T>, Vec<Report<S>>)
where
    C: Cache<S::SourceId>,
    S: Span,
{
    type Data = Option<T>;

    fn print_reports(self, cache: &mut C) -> std::io::Result<Self::Data> {
        for report in &self.1 {
            report.write(&mut *cache, io::stderr())?;
        }

        Ok(self.0)
    }
}

impl Interpreter {
    pub fn new(
        source_file: PathBuf,
        script_file: Option<PathBuf>,
        log_level: LogLevel,
        in_place: bool,
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

        let mut cache = FileCache::new(source, source_file);

        let tree = parse_source(&mut parser, &cache.bytes, &cache.file, log_level, None)
            .print_reports(&mut cache)
            .into_diagnostic()?
            .ok_or(TreeParseError {
                source_file: cache.file.to_owned(),
            })
            .into_diagnostic()?;

        let script_file = script_file.unwrap_or(PathBuf::from("<stdin>"));

        let script = Script::parse(&script_source, tree.language())
            .print_reports(&mut Source::from(&script_source))
            .into_diagnostic()?
            .ok_or(ScriptParseError { script_file })
            .into_diagnostic()?;

        Ok(Interpreter {
            cache,
            tree,
            script,
            parser,
            log_level,
            in_place,
        })
    }

    pub fn run(mut self) -> miette::Result<()> {
        for statement in self.script.statements() {
            execute_statement(
                statement,
                &mut self.parser,
                &mut self.cache,
                &mut self.tree,
                self.log_level,
            )?
        }

        if self.in_place {
            fs::write(&self.cache.file, &self.cache.bytes).into_diagnostic()?;
        } else {
            io::stdout().write(&self.cache.bytes).into_diagnostic()?;
        }

        Ok(())
    }
}

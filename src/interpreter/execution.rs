use std::{
    collections::{HashMap, HashSet},
    iter::once,
    ops::{Neg, Range},
    rc::Rc,
    vec,
};

use ariadne::{Color, Label, Report, ReportKind};
use convert_case::Casing;
use miette::{NamedSource, SourceSpan};
use tree_sitter::{InputEdit, Node, Point, QueryCursor, QueryPredicateArg, Tree};

use crate::{
    dsl::ast::{
        AndExpr, ContainsExpr, EqualsExpr, Insert, InsertLocation, JoinItem, Match, MatchAction,
        MatchClause, NotExpr, OrExpr, Query, Remove, Replace, Script, Statement, StringExpression,
        Warn, WhereExpr,
    },
    single::Single,
};

use super::cache::{FileCache, FileSpan, SourceCache};

struct QueryMatch<'tree> {
    captures: HashMap<String, Node<'tree>>,
}

#[derive(Debug)]
pub struct TreeEdit {
    edit: InputEdit,
    new_text: String,
}

impl TreeEdit {
    pub fn apply(&self, cache: &mut FileCache, tree: &mut Tree) {
        cache.update(|bytes| {
            bytes.splice(
                self.edit.start_byte..self.edit.old_end_byte,
                self.new_text.bytes(),
            );
        });
        tree.edit(&self.edit);
    }
}

#[derive(Default)]
pub struct ExecutionResult {
    pub edits: Vec<TreeEdit>,
    pub reports: Vec<Report<'static, FileSpan>>,
}

impl ExecutionResult {
    fn combine(&mut self, other: Self) {
        for other in other.edits {
            let overlap = self.edits.iter().any(|e| {
                e.edit.start_byte < other.edit.old_end_byte
                    && other.edit.start_byte < e.edit.old_end_byte
            });

            if !overlap {
                self.edits.push(other);
            }
        }

        self.reports.extend(other.reports);
    }
}

pub trait Executable<Ctx> {
    type Error: std::error::Error;

    fn execute(&self, ctx: &mut Ctx) -> Result<ExecutionResult, Self::Error>;
}

pub struct ScriptContext {
    pub(crate) cache: FileCache,
    pub(crate) file_tree: Tree,
    pub(crate) macro_trees: Vec<Tree>,
    pub(crate) parse_macros: bool,
    pub(crate) report_config: ariadne::Config,
}

impl ScriptContext {
    fn named_source(&self) -> Result<NamedSource, std::string::FromUtf8Error> {
        Ok(NamedSource::new(
            self.cache.file().to_string_lossy(),
            String::from_utf8(self.cache.bytes().get().to_vec())?,
        ))
    }

    pub fn get_node_string(&self, node: Node) -> Result<&str, std::str::Utf8Error> {
        self.cache.get_node_string(node)
    }
}

struct MatchContext<'a> {
    #[allow(clippy::redundant_allocation)]
    script_ctx: Rc<&'a mut ScriptContext>,
    query_match: &'a QueryMatch<'a>,
}

#[derive(miette::Diagnostic, Debug, thiserror::Error)]
pub enum ScriptError {
    #[error("tried to execute invalid statement")]
    #[diagnostic(code(tree_surgeon::statement::invalid))]
    InvalidStatement,
    #[error("tried to execute invalid query")]
    #[diagnostic(code(tree_surgeon::query::invalid))]
    InvalidQuery,
    #[error("Capture not found: {0}")]
    #[diagnostic(code(tree_surgeon::r#match::capture_not_found))]
    CaptureNotFound(String),
    #[error("capture {capture_name} not found")]
    #[diagnostic(code(tree_surgeon::r#match::missing_capture))]
    MissingCapture { capture_name: String },
    #[error("string wasn't valid UTF-8")]
    #[diagnostic(code(tree_surgeon::utf8))]
    Utf8(#[from] std::str::Utf8Error),
    #[error("string wasn't valid UTF-8")]
    #[diagnostic(code(tree_surgeon::utf8))]
    FromUtf8(#[from] std::string::FromUtf8Error),

    #[error(transparent)]
    #[diagnostic(transparent)]
    Query(#[from] QueryError),
    #[error(transparent)]
    #[diagnostic(transparent)]
    EditInErrorNode(#[from] EditInErrorNodeError),
}

#[derive(miette::Diagnostic, Debug, thiserror::Error)]
#[error("tried to make and edit within an error node")]
#[diagnostic(code(tree_surgeon::script::replace::edit_in_error))]
pub struct EditInErrorNodeError {
    #[source_code]
    src: NamedSource,
    error_label: String,
    #[label("{error_label}")]
    error_span: SourceSpan,
    #[label("tried to edit this")]
    edit_span: SourceSpan,
}

impl Executable<ScriptContext> for Script {
    type Error = ScriptError;

    fn execute(&self, ctx: &mut ScriptContext) -> Result<ExecutionResult, Self::Error> {
        let mut result = ExecutionResult::default();

        for stmt in &self.statements {
            result.combine(stmt.execute(ctx)?);
        }

        Ok(result)
    }
}

impl Executable<ScriptContext> for Statement {
    type Error = ScriptError;

    fn execute(&self, ctx: &mut ScriptContext) -> Result<ExecutionResult, Self::Error> {
        match self {
            Statement::Match(m) => m.execute(ctx),
            Statement::Invalid => Err(ScriptError::InvalidStatement),
        }
    }
}

impl Executable<ScriptContext> for Match {
    type Error = ScriptError;

    fn execute(&self, ctx: &mut ScriptContext) -> Result<ExecutionResult, Self::Error> {
        let Query::Query(query) = &self.query else {
            return Err(ScriptError::InvalidQuery)
        };

        let mut cursor = QueryCursor::new();

        let ctx = Rc::new(ctx);

        let mut trees = vec![&ctx.file_tree];
        if ctx.parse_macros {
            trees.extend(&ctx.macro_trees);
        }

        let mut result = ExecutionResult::default();

        for tree in trees {
            let matches = {
                let clauses = &self.clauses;

                let mut matches = Vec::default();

                for query_match in cursor.matches(query, tree.root_node(), &ctx.cache) {
                    let mut captures = HashMap::default();

                    let predicates_matching = query
                        .evaluate(&mut QueryContext {
                            cache: &ctx.cache,
                            query_match: &query_match,
                            captures: &captures,
                        })
                        .map_err(ScriptError::Query)?;

                    if !predicates_matching {
                        continue;
                    }

                    captures.extend(
                        query_match
                            .captures
                            .iter()
                            .map(|c| (query.capture_names()[c.index as usize].clone(), c.node))
                            .chain(once(("".to_string(), tree.root_node()))),
                    );

                    let clauses_matching = clauses.iter().try_fold(true, |result, clause| {
                        let result = result
                            && match clause {
                                MatchClause::Where(w) => w
                                    .evaluate(&mut QueryContext {
                                        cache: &ctx.cache,
                                        query_match: &query_match,
                                        captures: &captures,
                                    })
                                    .map_err(ScriptError::Query)?,
                            };

                        Ok::<bool, ScriptError>(result)
                    })?;

                    if !clauses_matching {
                        continue;
                    }

                    matches.push(QueryMatch { captures });
                }

                matches
            };

            for query_match in &matches {
                let mut match_ctx = MatchContext {
                    script_ctx: ctx.clone(),
                    query_match,
                };

                let new_result = match &self.action {
                    MatchAction::Replace(replace) => replace.execute(&mut match_ctx)?,
                    MatchAction::Warn(warn) => warn.execute(&mut match_ctx)?,
                    MatchAction::Remove(remove) => remove.execute(&mut match_ctx)?,
                    MatchAction::Insert(insert) => insert.execute(&mut match_ctx)?,
                };

                result.combine(new_result);
            }
        }

        Ok(result)
    }
}

impl<'a> Executable<MatchContext<'a>> for Replace {
    type Error = ScriptError;

    fn execute(&self, ctx: &mut MatchContext) -> Result<ExecutionResult, Self::Error> {
        let node = ctx
            .query_match
            .captures
            .get(&self.capture_name)
            .ok_or(ScriptError::MissingCapture {
                capture_name: self.capture_name.clone(),
            })?
            .to_owned();
        let start_byte = node.start_byte();
        let old_end_byte = node.end_byte();
        let start_position = node.start_position();
        let old_end_position = node.end_position();

        if let Some(error) = error_ancestor(node) {
            let error_start_byte = error.start_byte();
            let error_end_byte = error.end_byte();

            return Err(ScriptError::EditInErrorNode(EditInErrorNodeError {
                src: ctx
                    .script_ctx
                    .named_source()
                    .map_err(ScriptError::FromUtf8)?,
                error_span: (error_start_byte, error_end_byte - error_start_byte).into(),
                error_label: error.to_sexp(),
                edit_span: (start_byte, old_end_byte - start_byte).into(),
            }));
        }

        let new_text = self.replacement.evaluate(ctx)?;

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

        Ok(ExecutionResult {
            edits: vec![tree_edit],
            reports: vec![],
        })
    }
}

impl<'a> Executable<MatchContext<'a>> for Warn {
    type Error = ScriptError;

    fn execute(&self, ctx: &mut MatchContext) -> Result<ExecutionResult, Self::Error> {
        let msg = self.message.evaluate(ctx)?;

        let node = ctx.query_match.captures.get(&self.capture_name);
        let Some(node) = node else { return Ok(ExecutionResult::default()); };

        let byte_range = ctx.script_ctx.cache.translate_range(node.byte_range());

        let file = ctx.script_ctx.cache.file().to_owned();
        let report: Report<FileSpan> =
            Report::build(ReportKind::Warning, file.clone(), byte_range.start)
                .with_config(ctx.script_ctx.report_config)
                .with_label(
                    Label::new((file, byte_range))
                        .with_message(msg)
                        .with_color(Color::Yellow),
                )
                .finish();

        Ok(ExecutionResult {
            edits: vec![],
            reports: vec![report],
        })
    }
}

impl<'a> Executable<MatchContext<'a>> for Remove {
    type Error = ScriptError;

    fn execute(&self, ctx: &mut MatchContext) -> Result<ExecutionResult, Self::Error> {
        let node = ctx
            .query_match
            .captures
            .get(&self.capture_name)
            .ok_or(ScriptError::MissingCapture {
                capture_name: self.capture_name.clone(),
            })?
            .to_owned();

        let start_byte = node.start_byte();
        let old_end_byte = node.end_byte();
        let start_position = node.start_position();
        let old_end_position = node.end_position();

        if let Some(error) = error_ancestor(node) {
            let error_start_byte = error.start_byte();
            let error_end_byte = error.end_byte();

            return Err(ScriptError::EditInErrorNode(EditInErrorNodeError {
                src: ctx
                    .script_ctx
                    .named_source()
                    .map_err(ScriptError::FromUtf8)?,
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

        Ok(ExecutionResult {
            edits: vec![tree_edit],
            reports: vec![],
        })
    }
}

impl<'a> Executable<MatchContext<'a>> for Insert {
    type Error = ScriptError;

    fn execute(&self, ctx: &mut MatchContext) -> Result<ExecutionResult, Self::Error> {
        let node = ctx
            .query_match
            .captures
            .get(&self.capture_name)
            .ok_or(ScriptError::MissingCapture {
                capture_name: self.capture_name.clone(),
            })?
            .to_owned();

        let start_byte = node.start_byte();
        let old_end_byte = node.end_byte();
        let start_position = node.start_position();
        let old_end_position = node.end_position();

        if let Some(error) = error_ancestor(node) {
            let error_start_byte = error.start_byte();
            let error_end_byte = error.end_byte();

            return Err(ScriptError::EditInErrorNode(EditInErrorNodeError {
                src: ctx
                    .script_ctx
                    .named_source()
                    .map_err(ScriptError::FromUtf8)?,
                error_span: (error_start_byte, error_end_byte - error_start_byte).into(),
                error_label: error.to_sexp(),
                edit_span: (start_byte, old_end_byte - start_byte).into(),
            }));
        }

        let new_text = self.insertion.evaluate(ctx)?;

        let line_ending_count = new_text.chars().filter(|c| *c == '\n').count();
        let last_line_len = new_text.chars().rev().take_while(|c| *c != '\n').count();

        let tree_edit = match self.location {
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

        Ok(ExecutionResult {
            edits: vec![tree_edit],
            reports: vec![],
        })
    }
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

trait Evaluatable<T, Ctx> {
    type Error: std::error::Error;

    fn evaluate(&self, ctx: &mut Ctx) -> Result<T, Self::Error>;
}

fn evaluate_string_expression<F, E>(
    expression: &StringExpression,
    get_capture_node_text: F,
) -> Result<String, E>
where
    F: Fn(&str) -> Result<String, E>,
{
    let value = match expression {
        StringExpression::Literal(new_text) => new_text.clone(),
        StringExpression::Join(items) => items
            .iter()
            .map(|item| match item {
                JoinItem::CaptureExpr(capture_expr) => {
                    get_capture_node_text(&capture_expr.capture_name)
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
                                    })
                                        ..end.map_or(text.len(), |e| {
                                            if e.is_negative() {
                                                text.len() - e.neg() as usize
                                            } else {
                                                e as usize
                                            }
                                        })
                                })
                                .map_or(text.to_owned(), |range| text[range].to_owned())
                        })
                }
                JoinItem::Literal(new_text) => Ok(new_text.to_owned()),
            })
            .collect::<Result<String, _>>()?,
    };
    Ok(value)
}

impl<'mat> Evaluatable<String, MatchContext<'mat>> for StringExpression {
    type Error = ScriptError;

    fn evaluate(&self, ctx: &mut MatchContext) -> Result<String, Self::Error> {
        evaluate_string_expression(self, |name| {
            ctx.query_match
                .captures
                .get(name)
                .ok_or(ScriptError::CaptureNotFound(name.to_string()))
                .and_then(|&node| {
                    ctx.script_ctx
                        .get_node_string(node)
                        .map(ToString::to_string)
                        .map_err(ScriptError::Utf8)
                })
        })
    }
}

impl<'a> Evaluatable<String, QueryContext<'a>> for StringExpression {
    type Error = QueryError;

    fn evaluate(&self, ctx: &mut QueryContext) -> Result<String, Self::Error> {
        evaluate_string_expression(self, |name| {
            ctx.captures
                .get(name)
                .ok_or(QueryError::CaptureNotFound(name.to_string()))
                .and_then(|&node| {
                    ctx.cache
                        .get_node_string(node)
                        .map(ToString::to_string)
                        .map_err(QueryError::Utf8)
                })
        })
    }
}

struct QueryContext<'a> {
    cache: &'a FileCache,
    query_match: &'a tree_sitter::QueryMatch<'a, 'a>,
    captures: &'a HashMap<String, Node<'a>>,
}

#[derive(miette::Diagnostic, thiserror::Error, Debug)]
pub enum QueryError {
    #[error("{0}")]
    #[diagnostic(code(tree_surgeon::query::predicate_error))]
    PredicateError(String),
    #[error("Unknown predicate: {0}")]
    #[diagnostic(code(tree_surgeon::query::unknown_predicate))]
    UnknownPredicate(String),
    #[error("Capture not found: {0}")]
    #[diagnostic(code(tree_surgeon::r#match::capture_not_found))]
    CaptureNotFound(String),
    #[error("tried to execute invalid query")]
    #[diagnostic(code(tree_surgeon::query::invalid))]
    InvalidQuery,
    #[error("string wasn't valid UTF-8")]
    #[diagnostic(code(tree_surgeon::utf8))]
    Utf8(#[from] std::str::Utf8Error),
}

impl<'a> Evaluatable<bool, QueryContext<'a>> for tree_sitter::Query {
    type Error = QueryError;

    fn evaluate(&self, ctx: &mut QueryContext) -> Result<bool, Self::Error> {
        self.general_predicates(ctx.query_match.pattern_index)
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
                            return Err(QueryError::PredicateError(
                                "#in-list? requires at least 2 arguments".to_string(),
                            ));
                        }

                        let QueryPredicateArg::Capture(capture) = predicate.args[0] else {
                            return Err(QueryError::PredicateError(
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
                            return Err(QueryError::PredicateError(
                                "All arguments to #in-list? except for the first, must be strings"
                                    .to_string(),
                            ));
                        }

                        let node = ctx
                            .query_match
                            .nodes_for_capture_index(capture)
                            .single()
                            .expect("non-unique capture index");

                        let node_text =
                            ctx.cache.get_node_string(node).map_err(QueryError::Utf8)?;

                        strings.contains(node_text)
                    }
                    s => {
                        return Err(QueryError::UnknownPredicate(s.to_string()));
                    }
                };

                Ok(invert ^ matching)
            })
    }
}

impl<'a> Evaluatable<bool, QueryContext<'a>> for WhereExpr {
    type Error = QueryError;

    fn evaluate(&self, ctx: &mut QueryContext) -> Result<bool, Self::Error> {
        match self {
            WhereExpr::Equals(EqualsExpr { left, right }) => {
                let left = left.evaluate(ctx)?;
                let right = right.evaluate(ctx)?;

                Ok(left == right)
            }
            WhereExpr::Contains(ContainsExpr {
                capture_name,
                query,
            }) => {
                let node = ctx
                    .captures
                    .get(capture_name)
                    .ok_or(QueryError::CaptureNotFound(capture_name.clone()))
                    .copied()?;

                let crate::dsl::ast::Query::Query(query) = query else {
                    return Err(QueryError::InvalidQuery)
                };

                let contains = 'result: {
                    for query_match in QueryCursor::new().matches(query, node, ctx.cache) {
                        if query.evaluate(&mut QueryContext {
                            cache: ctx.cache,
                            query_match: &query_match,
                            captures: &HashMap::default(),
                        })? {
                            break 'result true;
                        }
                    }
                    false
                };

                Ok(contains)
            }
            WhereExpr::And(AndExpr { left, right }) => {
                Ok(left.evaluate(ctx)? && right.evaluate(ctx)?)
            }
            WhereExpr::Or(OrExpr { left, right }) => {
                Ok(left.evaluate(ctx)? || right.evaluate(ctx)?)
            }
            WhereExpr::Not(NotExpr(inner)) => inner.evaluate(ctx).map(std::ops::Not::not),
        }
    }
}

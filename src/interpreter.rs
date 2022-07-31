use std::{
    collections::HashMap,
    fmt, fs,
    io::Read,
    ops::Range,
    path::{Path, PathBuf},
};

use ariadne::{Cache, Color, FileCache, Label, Report, ReportKind, Source, Span};
use miette::{Diagnostic, IntoDiagnostic, LabeledSpan, SourceOffset, SourceSpan};
use tree_sitter::{InputEdit, Node, Parser, Point, QueryCursor, Tree, TreeCursor};

use crate::{
    dsl::{
        ast::{Match, Script, Statement},
        parser::Parsable,
    },
    single::{Single, SingleError},
};

pub struct Interpreter {
    source_file: PathBuf,
    source: Vec<u8>,
    tree: Tree,
    script: Script,
    parser: Parser,
    verbose: bool,
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
    Utf8(#[from] std::string::FromUtf8Error),
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
    src: String,
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

struct TreeErrorIter<'a>(TreeCursor<'a>);

impl<'a> Iterator for TreeErrorIter<'a> {
    type Item = Node<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        fn goto_next(cursor: &mut TreeCursor) -> bool {
            while !cursor.goto_next_sibling() {
                if !cursor.goto_parent() {
                    return false;
                }
            }

            true
        }

        loop {
            let node = self.0.node();
            if node.is_error() {
                goto_next(&mut self.0);
                return Some(node);
            } else {
                if self.0.goto_first_child() {
                    continue;
                }
            }

            if !goto_next(&mut self.0) {
                break;
            }
        }

        None
    }
}

fn parse_source(
    parser: &mut Parser,
    source: &Vec<u8>,
    old_tree: Option<&Tree>,
) -> (Option<Tree>, Vec<Report>) {
    let tree = parser.parse(source, old_tree);

    if let Some(tree) = tree {
        let error_iter = TreeErrorIter(tree.walk());

        let errors = error_iter
            .map(|node| {
                let parent = node.parent().unwrap_or(node);
                Report::build(ReportKind::Advice, (), node.start_byte())
                    .with_message("tree-sitter couldn't parse code fragment")
                    .with_label(Label::new(parent.byte_range()).with_message(parent.to_sexp()))
                    .with_label(
                        Label::new(node.byte_range())
                            .with_message(node.to_sexp())
                            .with_color(Color::Red),
                    )
                    .finish()
            })
            .collect();

        (Some(tree), errors)
    } else {
        (None, Vec::new())
    }
}

fn execute_match(
    m: &Match,
    parser: &mut Parser,
    source_file: &PathBuf,
    source: &mut Vec<u8>,
    tree: &mut Tree,
    verbose: bool,
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

    let mut cursor = QueryCursor::new();

    loop {
        let old_tree = tree.clone();
        let old_source = source.clone();

        let mut matches = cursor.matches(&query, old_tree.root_node(), old_source.as_slice());

        if let Some(query_match) = matches.next() {
            let capture_name = m.replacement().capture_name();
            let replacement = m.replacement().replacement();

            let capture_index =
                if let Some(capture_index) = query.capture_index_for_name(capture_name) {
                    capture_index
                } else {
                    return Err(MatchError::Replacement(ReplacementError::MissingCapture {
                        capture_name: capture_name.to_string(),
                    }));
                };

            let node = query_match
                .nodes_for_capture_index(capture_index)
                .single()
                .map_err(MatchError::Single)?;

            let start_byte = node.start_byte();
            let old_end_byte = node.end_byte();
            let start_position = node.start_position();
            let old_end_position = node.end_position();

            if let Some(error) = error_ancestor(node) {
                let error_start_byte = error.start_byte();
                let error_end_byte = error.end_byte();

                return Err(MatchError::EditInErrorNode(EditInErrorNode {
                    src: String::from_utf8(source.clone()).map_err(MatchError::Utf8)?,
                    error_span: (error_start_byte, error_end_byte - error_start_byte).into(),
                    error_label: error.to_sexp(),
                    edit_span: (start_byte, old_end_byte - start_byte).into(),
                }));
            }

            let line_ending_count = replacement.chars().filter(|c| *c == '\n').count();
            let last_line_len = replacement.chars().rev().take_while(|c| *c != '\n').count();

            let edit = InputEdit {
                start_byte,
                old_end_byte,
                start_position,
                old_end_position,
                new_end_byte: start_byte + replacement.len(),
                new_end_position: Point {
                    row: start_position.row + line_ending_count,
                    column: if line_ending_count == 0 {
                        start_position.column + replacement.len()
                    } else {
                        last_line_len
                    },
                },
            };

            source.splice(edit.start_byte..edit.old_end_byte, replacement.bytes());

            tree.edit(&edit);

            // TODO (opti): instead of re-parsing the tree after every change, try to apply as many changes as possible without overlap before parsing again
            let tree_with_errors = parse_source(parser, &source, None);

            let report: Report = if let (None, _) = &tree_with_errors {
                Report::build(ReportKind::Error, (), 0)
                    .with_message("tree-sitter couldn't parse source file")
                    .finish()
            } else {
                Report::build(ReportKind::Warning, (), 0)
                    .with_message("tree-sitter returned parse errors")
                    .finish()
            };

            report
                .eprint(Source::from(String::from_utf8_lossy(&source)))
                .map_err(MatchError::Io)?;

            *tree = tree_with_errors
                .print_reports(String::from_utf8_lossy(&source), verbose)
                .map_err(MatchError::Io)?
                .ok_or(MatchError::Replacement(ReplacementError::TreeParse(
                    TreeParseError {
                        source_file: source_file.to_owned(),
                    },
                )))?;
        } else {
            break Ok(());
        }
    }
}

fn execute_statement(
    statement: &Statement,
    parser: &mut Parser,
    source_file: &PathBuf,
    source: &mut Vec<u8>,
    tree: &mut Tree,
    verbose: bool,
) -> Result<(), StatementError> {
    match statement {
        Statement::Match(m) => execute_match(m, parser, source_file, source, tree, verbose)
            .map_err(StatementError::Match),
        Statement::Invalid => Err(StatementError::Invalid),
    }
}

trait ParseResult<T, S> {
    fn print_reports(self, source: S, verbose: bool) -> std::io::Result<T>;
}

impl<'a, T, S: AsRef<str>> ParseResult<T, S> for (T, Vec<Report>) {
    fn print_reports(self, source: S, verbose: bool) -> std::io::Result<T> {
        if verbose {
            for report in &self.1 {
                report.eprint(Source::from(&source))?;
            }
        }

        Ok(self.0)
    }
}

impl Interpreter {
    pub fn new(
        source_file: PathBuf,
        script_file: Option<PathBuf>,
        verbose: bool,
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

        let tree_with_errors = parse_source(&mut parser, &source, None);

        let report: Report = if let (None, _) = &tree_with_errors {
            Report::build(ReportKind::Error, (), 0)
                .with_message("tree-sitter couldn't parse source file")
                .finish()
        } else {
            Report::build(ReportKind::Warning, (), 0)
                .with_message("tree-sitter returned parse errors")
                .finish()
        };

        report
            .eprint(Source::from(String::from_utf8_lossy(&source)))
            .into_diagnostic()?;

        let tree = tree_with_errors
            .print_reports(String::from_utf8_lossy(&source), verbose)
            .into_diagnostic()?
            .ok_or(TreeParseError {
                source_file: source_file.to_owned(),
            })
            .into_diagnostic()?;

        let script = Script::parse(&script_source, tree.language())
            .print_reports(&script_source, verbose)
            .into_diagnostic()?
            .ok_or(ScriptParseError {
                script_file: script_file.unwrap_or(PathBuf::from("<stdin>")),
            })
            .into_diagnostic()?;

        Ok(Interpreter {
            source,
            source_file,
            tree,
            script,
            parser,
            verbose,
        })
    }

    pub fn run(mut self) -> miette::Result<()> {
        for statement in self.script.statements() {
            execute_statement(
                statement,
                &mut self.parser,
                &self.source_file,
                &mut self.source,
                &mut self.tree,
                self.verbose,
            )?
        }

        print!("{}", String::from_utf8(self.source).into_diagnostic()?);

        Ok(())
    }
}

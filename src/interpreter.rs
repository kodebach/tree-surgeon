use std::{
    ffi::OsStr,
    fs,
    io::Read,
    path::{Path, PathBuf},
};

use ariadne::Source;
use miette::IntoDiagnostic;
use tree_sitter::{InputEdit, Language, Parser, Point, QueryCursor, Tree};

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
}

#[derive(Debug, thiserror::Error)]
enum MatchError {
    #[error(transparent)]
    Single(SingleError),
}

#[derive(Debug, thiserror::Error)]
enum ReplacementError {
    #[error("capture {capture_name} not found")]
    MissingCapture { capture_name: String },
}

#[derive(Debug, thiserror::Error)]
#[error("tree-sitter couldn't parse the file {source_file}")]
struct TreeParseError {
    source_file: PathBuf,
}

#[derive(Debug, thiserror::Error)]
#[error("couldn't parse the script {script_file}")]
struct ScriptParseError {
    script_file: PathBuf,
}

#[derive(Debug, thiserror::Error)]
#[error("interpreter received invalid statement")]
struct InvalidStatementError;

fn parse_source(
    parser: &mut Parser,
    source_file: &PathBuf,
    source: &Vec<u8>,
    old_tree: Option<&Tree>,
) -> Result<Tree, TreeParseError> {
    parser
        .parse(source, old_tree)
        .ok_or(TreeParseError {
            source_file: source_file.clone(),
        })
        .and_then(|tree| {
            if tree.root_node().has_error() {
                Err(TreeParseError {
                    source_file: source_file.clone(),
                })
            } else {
                Ok(tree)
            }
        })
}

fn execute_match(
    m: &Match,
    parser: &mut Parser,
    source_file: &PathBuf,
    source: &mut Vec<u8>,
    tree: &mut Tree,
) -> miette::Result<()> {
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
                    Err(ReplacementError::MissingCapture {
                        capture_name: capture_name.to_string(),
                    })
                    .into_diagnostic()?;
                    unreachable!("reached line after error");
                };

            let node = query_match
                .nodes_for_capture_index(capture_index)
                .single()
                .map_err(MatchError::Single)
                .into_diagnostic()?;

            let start_byte = node.start_byte();
            let old_end_byte = node.end_byte();
            let start_position = node.start_position();
            let old_end_position = node.end_position();

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

            *tree = parse_source(parser, &PathBuf::from("<edited>"), source, Some(tree))
                .into_diagnostic()?;
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
) -> miette::Result<()> {
    match statement {
        Statement::Match(m) => execute_match(m, parser, source_file, source, tree),
        Statement::Invalid => Err(InvalidStatementError).into_diagnostic()?,
    }
}

impl Interpreter {
    pub fn new(source_file: PathBuf, script_file: Option<PathBuf>) -> miette::Result<Interpreter> {
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

        let tree = parse_source(&mut parser, &source_file, &source, None).into_diagnostic()?;

        let (script, reports) = Script::parse(&script_source, tree.language());

        for report in reports {
            report
                .print(Source::from(&script_source))
                .into_diagnostic()?;
        }

        let script = script
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
            )?
        }

        print!("{}", String::from_utf8(self.source).into_diagnostic()?);

        Ok(())
    }
}

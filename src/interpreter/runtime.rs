use std::{
    fs::File,
    io::{BufReader, Read},
    path::PathBuf,
};

use miette::{miette, LabeledSpan, Severity};
use ropey::Rope;
use tree_sitter::{Parser, QueryCursor, Tree};

use crate::{dsl::ast::Script, parser::Parsable, single::Single};

use super::{
    cache::{FileCache, MacroCache, SourceCache},
    execution::{Executable, ExecutionResult, ScriptContext, ScriptError},
    tree_cursor::TreeCusorExt,
};

fn parse_source<C>(
    parser: &mut Parser,
    cache: &C,
    log_level: LogLevel,
    old_tree: Option<&Tree>,
) -> Option<Tree>
where
    C: SourceCache,
{
    let tree = cache.parse(parser, old_tree);

    if let Some(tree) = tree {
        let mut reports: Vec<_> = if log_level <= LogLevel::Advice {
            let cursor = tree.walk();
            let error_iter = cursor.error_iter();

            error_iter
                .map(|node| {
                    let parent = node.parent().unwrap_or(node);

                    let node_span = cache.translate_span(node.byte_range().into());
                    let parent_span = cache.translate_span(parent.byte_range().into());

                    miette!(
                        severity = Severity::Advice,
                        labels = [
                            LabeledSpan::new_with_span(Some(parent.to_sexp()), parent_span),
                            LabeledSpan::new_with_span(Some(node.to_sexp()), node_span),
                        ],
                        "tree-sitter couldn't parse code fragment"
                    )
                })
                .collect()
        } else {
            Vec::new()
        };

        if log_level <= LogLevel::Warning && !reports.is_empty() {
            reports.insert(
                0,
                miette!(
                    severity = Severity::Error,
                    "tree-sitter returned {} parse errors",
                    reports.len()
                ),
            )
        }

        for report in reports {
            eprintln!("{:?}", report.with_source_code(cache.to_string()));
        }

        Some(tree)
    } else if log_level <= LogLevel::Error {
        let report = miette!(
            severity = Severity::Error,
            "tree-sitter couldn't parse source file"
        )
        .with_source_code(cache.to_string());

        eprintln!("{:?}", report);

        None
    } else {
        None
    }
}

fn parse_macros(
    file_tree: &Tree,
    cache: &FileCache,
    parser: &mut Parser,
    log_level: LogLevel,
) -> Vec<(MacroCache, Tree)> {
    let macro_query = tree_sitter::Query::new(tree_sitter_c::language(), "((preproc_arg) @macro)")
        .expect("macro_query broken");

    let capture_idx = macro_query
        .capture_index_for_name("macro")
        .expect("macro_query broken (idx)");

    let mut cursor = QueryCursor::new();
    let macros = cursor.matches(&macro_query, file_tree.root_node(), cache);

    let mut results = vec![];

    for query_match in macros {
        let node = query_match
            .nodes_for_capture_index(capture_idx)
            .single()
            .expect("macro_query broken (get)");

        let macro_cache = MacroCache::new(cache, node.byte_range());

        let tree = parse_source(parser, &macro_cache, log_level, None);

        if let Some(tree) = tree {
            results.push((macro_cache, tree));
        }
    }

    results
}

pub struct Interpreter {
    parser: Parser,
    script: Script,
    config: InterpreterConfig,
}

pub struct InterpreterConfig {
    pub log_level: LogLevel,
    pub in_place: bool,
    pub parse_macros: bool,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum LogLevel {
    Advice,
    Warning,
    Error,
    None,
}

#[derive(miette::Diagnostic, thiserror::Error, Debug)]
pub enum InterpreterError {
    #[error("tree-sitter couldn't parse the file {source_file}")]
    #[diagnostic(code(tree_surgeon::tree_sitter::parse_error))]
    TreeParse { source_file: PathBuf },

    #[error("couldn't parse the script {script_file}")]
    #[diagnostic(code(tree_surgeon::script::parse_error))]
    ScriptParse { script_file: PathBuf },

    #[error(transparent)]
    #[diagnostic(transparent)]
    Execution(#[from] ScriptError),

    #[error(transparent)]
    #[diagnostic(code(tree_surgeon::io))]
    Io(#[from] std::io::Error),

    #[error("string wasn't valid UTF-8")]
    #[diagnostic(code(tree_surgeon::utf8))]
    Utf8(#[from] std::string::FromUtf8Error),
}

impl Interpreter {
    pub fn new(
        script_file: Option<PathBuf>,
        config: InterpreterConfig,
    ) -> Result<Self, InterpreterError> {
        let mut parser = Parser::new();
        parser
            .set_language(tree_sitter_c::language())
            .expect("parser construction failed");

        let script_source = if let Some(ref script_file) = script_file {
            let script_buf = std::fs::read(script_file).map_err(InterpreterError::Io)?;

            String::from_utf8(script_buf).map_err(InterpreterError::Utf8)?
        } else {
            let stdin = std::io::stdin();
            let mut source = String::new();
            stdin
                .lock()
                .read_to_string(&mut source)
                .map_err(InterpreterError::Io)?;

            source
        };

        let (script, reports) = Script::parse(&script_source, tree_sitter_c::language());

        for report in reports {
            eprintln!("{:?}", report.with_source_code(script_source.clone()));
        }

        let script = script.ok_or(InterpreterError::ScriptParse {
            script_file: script_file.unwrap_or(PathBuf::from("<stdin>")),
        })?;

        Ok(Self {
            parser,
            config,
            script,
        })
    }

    pub fn run(&mut self, source_file: PathBuf) -> Result<(), InterpreterError> {
        let source = Rope::from_reader(BufReader::new(
            File::open(&source_file).map_err(InterpreterError::Io)?,
        ))
        .map_err(InterpreterError::Io)?;
        let cache = FileCache::new(source, source_file);

        let file_tree = parse_source(&mut self.parser, &cache, self.config.log_level, None);

        let file_tree = file_tree.ok_or(InterpreterError::TreeParse {
            source_file: cache.file().to_owned(),
        })?;

        let mut script_ctx = ScriptContext {
            file_cache: cache,
            file_tree,
            macros: vec![],
        };

        loop {
            let macros = parse_macros(
                &script_ctx.file_tree,
                &script_ctx.file_cache,
                &mut self.parser,
                self.config.log_level,
            );
            script_ctx.macros = macros;

            let ExecutionResult { edits, reports } = self
                .script
                .execute(&mut script_ctx)
                .map_err(InterpreterError::Execution)?;

            for report in reports {
                eprintln!(
                    "{:?}",
                    report.with_source_code(script_ctx.file_cache.to_string())
                );
            }

            if edits.is_empty() {
                break;
            }

            for edit in edits {
                edit.apply(&mut script_ctx);

                let new_tree = parse_source(
                    &mut self.parser,
                    &script_ctx.file_cache,
                    self.config.log_level,
                    Some(&script_ctx.file_tree),
                );

                script_ctx.file_tree = new_tree.ok_or(InterpreterError::TreeParse {
                    source_file: script_ctx.file_cache.file().to_owned(),
                })?;
            }
        }

        if self.config.in_place {
            let mut file =
                File::create(script_ctx.file_cache.file()).map_err(InterpreterError::Io)?;
            script_ctx
                .file_cache
                .write_to(&mut file)
                .map_err(InterpreterError::Io)?;
        } else {
            let mut stdout = std::io::stdout();
            script_ctx
                .file_cache
                .write_to(&mut stdout)
                .map_err(InterpreterError::Io)?;
        };

        Ok(())
    }
}

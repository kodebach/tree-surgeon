use std::{
    io::{Read, Write},
    path::PathBuf,
};

use ariadne::{Color, Label, Report, ReportKind, Source};
use tree_sitter::{Parser, QueryCursor, Tree};

use crate::{dsl::ast::Script, parser::Parsable, single::Single};

use super::{
    cache::{FileCache, FileSpan, MacroCache, SourceCache},
    execution::{Executable, ExecutionResult, ScriptContext, ScriptError},
    tree_cursor::TreeCusorExt,
};

fn parse_source<'a>(
    parser: &mut Parser,
    cache: &impl SourceCache,
    log_level: LogLevel,
    old_tree: Option<&Tree>,
    config: ariadne::Config,
) -> (Option<Tree>, Vec<Report<'a, FileSpan>>) {
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

        if log_level <= LogLevel::Warning && !errors.is_empty() {
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

        (Some(tree), errors)
    } else if log_level <= LogLevel::Error {
        let error = Report::build(ReportKind::Error, file, 0)
            .with_config(config)
            .with_message("tree-sitter couldn't parse source file")
            .finish();

        (None, vec![error])
    } else {
        (None, Vec::default())
    }
}

fn parse_macros<'a>(
    file_tree: &Tree,
    cache: &FileCache,
    parser: &mut Parser,
    log_level: LogLevel,
    config: ariadne::Config,
) -> (Vec<Tree>, Vec<Report<'a, FileSpan>>) {
    let macro_query = tree_sitter::Query::new(tree_sitter_c::language(), "((preproc_arg) @macro)")
        .expect("macro_query broken");

    let capture_idx = macro_query
        .capture_index_for_name("macro")
        .expect("macro_query broken (idx)");

    let mut cursor = QueryCursor::new();
    let macros = cursor.matches(&macro_query, file_tree.root_node(), cache);

    let mut trees = vec![];
    let mut reports = vec![];

    for query_match in macros {
        let node = query_match
            .nodes_for_capture_index(capture_idx)
            .single()
            .expect("macro_query broken (get)");
        let macro_cache = MacroCache {
            file_cache: cache.clone(),
            span: node.byte_range(),
        };

        let (tree, mut new_reports) = parse_source(parser, &macro_cache, log_level, None, config);

        reports.append(&mut new_reports);

        if let Some(tree) = tree {
            trees.push(tree);
        }
    }

    (trees, reports)
}

pub struct Interpreter {
    parser: Parser,
    script: Script,
    config: InterpreterConfig,
}

pub struct InterpreterConfig {
    pub report_config: ariadne::Config,
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
    ) -> Result<Interpreter, InterpreterError> {
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

        let (script, reports) = Script::parse(
            &script_source,
            tree_sitter_c::language(),
            config.report_config,
        );

        for report in reports {
            report
                .eprint(Source::from(&script_source))
                .map_err(InterpreterError::Io)?;
        }

        let script = script.ok_or(InterpreterError::ScriptParse {
            script_file: script_file.unwrap_or(PathBuf::from("<stdin>")),
        })?;

        Ok(Interpreter {
            parser,
            config,
            script,
        })
    }

    pub fn run(&mut self, source_file: PathBuf) -> Result<(), InterpreterError> {
        let source = std::fs::read(&source_file).map_err(InterpreterError::Io)?;

        let cache = FileCache::new(source, source_file);

        let (file_tree, reports) = parse_source(
            &mut self.parser,
            &cache,
            self.config.log_level,
            None,
            self.config.report_config,
        );

        for report in reports {
            report
                .eprint(cache.clone())
                .map_err(InterpreterError::Io)?;
        }

        let file_tree = file_tree.ok_or(InterpreterError::TreeParse {
            source_file: cache.file().to_owned(),
        })?;

        let mut reports = Vec::default();

        let mut script_ctx = ScriptContext {
            cache,
            file_tree,
            macro_trees: vec![],
            parse_macros: self.config.parse_macros,
            report_config: self.config.report_config,
        };

        loop {
            let (macro_trees, mut new_reports) = parse_macros(
                &script_ctx.file_tree,
                &script_ctx.cache,
                &mut self.parser,
                self.config.log_level,
                self.config.report_config,
            );
            reports.append(&mut new_reports);
            script_ctx.macro_trees = macro_trees;

            let ExecutionResult {
                edits,
                reports: mut new_reports,
            } = self
                .script
                .execute(&mut script_ctx)
                .map_err(InterpreterError::Execution)?;
            reports.append(&mut new_reports);

            if edits.is_empty() {
                break;
            }

            for edit in edits {
                edit.apply(&mut script_ctx.cache, &mut script_ctx.file_tree);

                let (new_tree, mut new_reports) = parse_source(
                    &mut self.parser,
                    &script_ctx.cache,
                    self.config.log_level,
                    Some(&script_ctx.file_tree),
                    self.config.report_config,
                );

                reports.append(&mut new_reports);

                script_ctx.file_tree = new_tree.ok_or(InterpreterError::TreeParse {
                    source_file: script_ctx.cache.file().to_owned(),
                })?;
            }
        }

        if self.config.in_place {
            std::fs::write(script_ctx.cache.file(), script_ctx.cache.bytes())
                .map_err(InterpreterError::Io)?;
        } else {
            std::io::stdout()
                .write(script_ctx.cache.bytes().get())
                .map_err(InterpreterError::Io)?;
        }

        for report in reports {
            report
                .eprint(script_ctx.cache.clone())
                .map_err(InterpreterError::Io)?;
        }

        Ok(())
    }
}

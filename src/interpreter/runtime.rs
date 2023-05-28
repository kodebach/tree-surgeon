use std::{
    fs::File,
    io::{self, BufReader, Read},
    path::PathBuf,
};

use miette::{miette, LabeledSpan, Severity};
use ropey::Rope;
use rstest::rstest;
use tree_sitter::{Parser, QueryCursor, Tree};

use crate::{dsl::ast::Script, parser::Parsable, single::Single};

use super::{
    cache::{FileCache, MacroCache, SourceCache},
    execution::{Executable, ExecutionResult, ScriptContext, ScriptError},
    tree_cursor::TreeCusorExt,
};

fn parse_source<C, E>(
    parser: &mut Parser,
    cache: &C,
    log_level: LogLevel,
    old_tree: Option<&Tree>,
    output: &mut E,
) -> Option<Tree>
where
    C: SourceCache,
    E: io::Write,
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
            output
                .write_fmt(format_args!(
                    "{:?}",
                    report.with_source_code(cache.to_string())
                ))
                .unwrap();
        }

        Some(tree)
    } else if log_level <= LogLevel::Error {
        let report = miette!(
            severity = Severity::Error,
            "tree-sitter couldn't parse source file"
        )
        .with_source_code(cache.to_string());

        output.write_fmt(format_args!("{:?}", report)).unwrap();

        None
    } else {
        None
    }
}

fn parse_macros<E>(
    file_tree: &Tree,
    cache: &FileCache,
    parser: &mut Parser,
    log_level: LogLevel,
    language: tree_sitter::Language,
    output: &mut E,
) -> Vec<(MacroCache, Tree)>
where
    E: io::Write,
{
    let macro_query =
        tree_sitter::Query::new(language, "((preproc_arg) @macro)").expect("macro_query broken");

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

        let tree = parse_source(parser, &macro_cache, log_level, None, output);

        if let Some(tree) = tree {
            results.push((macro_cache, tree));
        }
    }

    results
}

pub struct Interpreter<'a, E: io::Write> {
    parser: Parser,
    script: Script,
    output: &'a mut E,
    config: InterpreterConfig,
}

pub struct InterpreterConfig {
    pub language: tree_sitter::Language,
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

impl<'a, E: io::Write> Interpreter<'a, E> {
    fn from_script(
        script_source: String,
        script_file: Option<PathBuf>,
        output: &'a mut E,
        config: InterpreterConfig,
    ) -> Result<Self, InterpreterError> {
        let (script, reports) = Script::parse(&script_source, config.language);

        for report in reports {
            output
                .write_fmt(format_args!(
                    "{:?}",
                    report.with_source_code(script_source.clone())
                ))
                .unwrap();
        }

        let script = script.ok_or(InterpreterError::ScriptParse {
            script_file: script_file.unwrap_or(PathBuf::from("<stdin>")),
        })?;

        let mut parser = Parser::new();
        parser
            .set_language(config.language)
            .expect("parser construction failed");

        Ok(Self {
            parser,
            config,
            script,
            output,
        })
    }

    pub fn new(
        script_file: Option<PathBuf>,
        output: &'a mut E,
        config: InterpreterConfig,
    ) -> Result<Self, InterpreterError> {
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

        Self::from_script(script_source, script_file, output, config)
    }

    fn run_impl(&mut self, cache: FileCache) -> Result<ScriptContext, InterpreterError> {
        let file_tree = parse_source(
            &mut self.parser,
            &cache,
            self.config.log_level,
            None,
            &mut self.output,
        );

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
                self.config.language,
                &mut self.output,
            );
            script_ctx.macros = macros;

            let ExecutionResult { edits, reports } = self
                .script
                .execute(&mut script_ctx)
                .map_err(InterpreterError::Execution)?;

            for report in reports {
                self.output
                    .write_fmt(format_args!(
                        "{:?}",
                        report.with_source_code(script_ctx.file_cache.to_string())
                    ))
                    .unwrap();
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
                    &mut self.output,
                );

                script_ctx.file_tree = new_tree.ok_or(InterpreterError::TreeParse {
                    source_file: script_ctx.file_cache.file().to_owned(),
                })?;
            }
        }

        Ok(script_ctx)
    }

    pub fn run(&mut self, source_file: PathBuf) -> Result<(), InterpreterError> {
        let source = Rope::from_reader(BufReader::new(
            File::open(&source_file).map_err(InterpreterError::Io)?,
        ))
        .map_err(InterpreterError::Io)?;

        let script_ctx = self.run_impl(FileCache::new(source, source_file))?;

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

#[rstest]
#[case("empty", "", "")]
#[case(
    "basic-warn",
    r#"match ((translation_unit) @t) warn @t "warning";"#,
    r##"
    #include <test.h>
    "##,
)]
#[case(
    "include-no-match",
    r##"match ((preproc_include path: ((_) @str)) @inc (#eq? @str "<test.h>")) where @ contains 
        (((identifier) @id) (#in-list? @id "TEST" )) insert after @inc "#include <other.h>\n";"##,
    r##"
    #include <test.h>
    "##,
)]
#[case(
    "include-match",
    r##"
    match ((preproc_include path: ((_) @str)) @inc (#eq? @str "<test.h>")) where @ contains 
        (((identifier) @id) (#in-list? @id "TEST" )) insert after @inc "#include <other.h>\n";
    match ((preproc_include path: ((_) @str)) @inc (#eq? @str "<test.h>")) remove @inc;
    "##,
    r##"
    #include <test.h>
    #define TEST x
    "##,
)]
#[case(
    "include-match-2",
    r##"
    match ((preproc_include path: ((_) @str)) @inc (#eq? @str "<test.h>")) where @ contains 
        (((identifier) @id) (#in-list? @id "TEST" )) insert after @inc "#include <other.h>\n";
    match ((preproc_include path: ((_) @str)) @inc (#eq? @str "<test.h>")) remove @inc;
    "##,
    r##"
    #include <first.h>
    #include <test.h>
    #include <second.h>

    void foo(void) { call(TEST); }
    "##,
)]
#[case(
    "replace-foo-bar",
    r##"
    match (((type_identifier) @id) (#eq? @id "foo")) replace @id with "bar";
    "##,
    r##"
    void test(void) {
        foo x;
    }
    "##,
)]
#[case(
    "replace-foo-bar-macro",
    r##"
    match (((type_identifier) @id) (#eq? @id "foo")) replace @id with "bar";
    "##,
    r##"
    #define do_test do { foo x; } while(0)

    void test(void) {
        foo x;
    }
    "##,
)]
fn test_interpreter(#[case] test_name: &str, #[case] script: &str, #[case] source: &str) {
    let _ = miette::set_hook(Box::new(|_| Box::<miette::JSONReportHandler>::default()));

    let source = Rope::from_str(source);

    let mut output = Vec::default();

    let mut interpreter = Interpreter::from_script(
        script.to_string(),
        Some(PathBuf::new()),
        &mut output,
        InterpreterConfig {
            language: tree_sitter_c::language(),
            log_level: LogLevel::None,
            in_place: true,
            parse_macros: true,
        },
    )
    .unwrap();

    let result = interpreter.run_impl(FileCache::new(source, PathBuf::new()));

    insta::with_settings!({ snapshot_suffix => format!("{}-output", test_name) }, {
        insta::assert_snapshot!(String::from_utf8(output).unwrap());
    });

    match result {
        Ok(ctx) => {
            insta::with_settings!({ snapshot_suffix => format!("{}-tree", test_name) }, {
                insta::assert_snapshot!(ctx.file_tree.root_node().to_sexp());
            });

            insta::with_settings!({ snapshot_suffix => format!("{}-file", test_name) }, {
                insta::assert_snapshot!(ctx.file_cache.to_string());
            });
        }
        Err(error) => {
            insta::with_settings!({ snapshot_suffix => format!("{}-error", test_name) }, {
                insta::assert_debug_snapshot!(error);
            });
        }
    }
}

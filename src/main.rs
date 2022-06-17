use std::{
    collections::HashMap,
    fs,
    io::{self, Read},
    str::Utf8Error,
};

use clap::Parser;
use miette::IntoDiagnostic;
use thiserror::Error;
use tree_sitter::{Language, Parser as TreeParser, QueryCursor};
use tree_surgeon::{
    dsl::ast::Script,
    dsl::parser::Parsable,
    single::{Single, SingleError},
};

extern "C" {
    fn tree_sitter_c() -> Language;
}

#[derive(clap::Parser, Debug)]
#[clap(author, version, about, long_about=None)]
struct Cli {
    #[clap(value_parser)]
    source_file: String,

    #[clap(value_parser)]
    script_file: Option<String>,
}

fn main() -> miette::Result<()> {
    let cli = Cli::parse();

    let mut parser = TreeParser::new();
    let language = unsafe { tree_sitter_c() };
    parser.set_language(language).into_diagnostic()?;

    let source_text = fs::read(cli.source_file).into_diagnostic()?;

    let tree = parser
        .parse(&source_text, Option::None)
        .ok_or(io::Error::new(io::ErrorKind::Other, "Parsing failed"))
        .into_diagnostic()?;

    let script_source = if let Some(script_file) = cli.script_file {
        let script_buf = fs::read(&script_file).into_diagnostic()?;

        String::from_utf8(script_buf).into_diagnostic()?
    } else {
        let stdin = io::stdin();
        let mut source = String::new();
        stdin.lock().read_to_string(&mut source).into_diagnostic()?;

        source
    };

    let script = Script::parse(&script_source, language).map_err(|e| e.into_owned())?;

    for statement in script.statements() {
        match statement {
            tree_surgeon::dsl::ast::Statement::Match(m) => {
                let query = m.query();
                let mut cursor = QueryCursor::new();
                let matches = cursor.matches(&query, tree.root_node(), source_text.as_slice());

                let capture_indices: HashMap<_, _> = query
                    .capture_names()
                    .iter()
                    .filter_map(|name| {
                        query
                            .capture_index_for_name(name)
                            .map(|index| (name, index))
                    })
                    .collect();

                #[derive(Debug, Error)]
                enum Err {
                    #[error(transparent)]
                    Single(SingleError),
                    #[error(transparent)]
                    Utf8(Utf8Error),
                }

                let res: Result<Vec<HashMap<_, _>>, _> = matches
                    .map(|m| {
                        capture_indices
                            .iter()
                            .map(|(name, &index)| {
                                m.nodes_for_capture_index(index)
                                    .single()
                                    .map_err(Err::Single)
                                    .and_then(|node| {
                                        node.utf8_text(&source_text).map_err(Err::Utf8)
                                    })
                                    .map(|text| (name, text))
                            })
                            .collect()
                    })
                    .collect();

                let captures = res.into_diagnostic()?;

                println!("{:#?}", captures);
            }
        }
    }

    Ok(())
}

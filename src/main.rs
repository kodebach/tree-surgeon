use std::{
    fs,
    io::{self, BufRead, Read},
};

use clap::Parser;
use tree_sitter::{Language, Parser as TreeParser, Query, QueryCursor};

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

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    let mut parser = TreeParser::new();
    let language = unsafe { tree_sitter_c() };
    parser.set_language(language)?;

    let source_text = fs::read(cli.source_file)?;

    let tree = parser
        .parse(&source_text, Option::None)
        .ok_or(io::Error::new(io::ErrorKind::Other, "Parsing failed"))?;

    let mut script;

    if let Some(script_file) = cli.script_file {
        let script_buf = fs::read(script_file)?;
        script = String::from_utf8(script_buf)?;
    } else {
        let stdin = io::stdin();
        script = String::new();
        stdin.lock().read_to_string(&mut script)?;
    }

    let query = Query::new(language, &script)?;
    let mut cursor = QueryCursor::new();
    let matches = cursor.matches(&query, tree.root_node(), source_text.as_slice());

    let v: Result<Vec<_>, _> = matches
        .flat_map(|m| {
            m.captures
                .iter()
                .zip(query.capture_names())
                .map(|(capture, name)| {
                    capture
                        .node
                        .utf8_text(&source_text)
                        .map(|text| (name, text))
                })
        })
        .collect();

    println!("{:#?}", v?);

    Ok(())
}

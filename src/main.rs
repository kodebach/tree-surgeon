use std::{
    fs,
    io::{self, Read},
    path::{Path, PathBuf},
};

use clap::Parser;
use miette::IntoDiagnostic;

use nom::error;
use tree_sitter::{Language, Parser as TreeParser};
use tree_surgeon::{dsl::ast::Script, dsl::parser::Parsable, interpreter::Interpreter};

#[derive(clap::Parser, Debug)]
#[clap(author, version, about, long_about=None)]
struct Cli {
    #[clap(value_parser)]
    source_file: PathBuf,

    #[clap(value_parser)]
    script_file: Option<String>,
}

fn main() -> miette::Result<()> {
    let cli = Cli::parse();

    let script_source = if let Some(script_file) = cli.script_file {
        let script_buf = fs::read(&script_file).into_diagnostic()?;

        String::from_utf8(script_buf).into_diagnostic()?
    } else {
        let stdin = io::stdin();
        let mut source = String::new();
        stdin.lock().read_to_string(&mut source).into_diagnostic()?;

        source
    };

    let interpreter = Interpreter::new(cli.source_file, script_source)?;

    interpreter.run()
}

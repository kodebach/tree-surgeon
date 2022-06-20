use std::path::PathBuf;

use clap::Parser;

use tree_surgeon::interpreter::Interpreter;

#[derive(clap::Parser, Debug)]
#[clap(author, version, about, long_about=None)]
struct Cli {
    #[clap(value_parser)]
    source_file: PathBuf,

    #[clap(value_parser)]
    script_file: Option<PathBuf>,
}

fn main() -> miette::Result<()> {
    let cli = Cli::parse();

    let interpreter = Interpreter::new(cli.source_file, cli.script_file)?;

    interpreter.run()
}

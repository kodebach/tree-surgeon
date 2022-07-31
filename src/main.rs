use std::path::PathBuf;

use clap::Parser;

use tree_surgeon::interpreter::Interpreter;

#[derive(clap::Parser, Debug)]
#[clap(author, version, about, long_about=None)]
struct Cli {
    /// source file to edit
    #[clap(value_parser)]
    source_file: PathBuf,

    /// script to execute, if missing use stdin
    #[clap(value_parser)]
    script_file: Option<PathBuf>,

    /// print additional information
    #[clap(short, long)]
    verbose: bool,
}

fn main() -> miette::Result<()> {
    let cli = Cli::parse();

    let interpreter = Interpreter::new(cli.source_file, cli.script_file, cli.verbose)?;

    interpreter.run()
}

use std::path::PathBuf;

use clap::{ArgAction, Parser};

use is_terminal::IsTerminal;
use tree_surgeon::interpreter::{self, Interpreter, InterpreterConfig};

#[derive(clap::Parser, Debug)]
#[clap(author, version, about, long_about=None)]
struct Cli {
    /// source file to edit
    #[clap(value_parser)]
    source_file: PathBuf,

    /// script to execute, if missing use stdin
    #[clap(value_parser)]
    script_file: Option<PathBuf>,

    /// amount of information to print
    #[clap(arg_enum, short, long, default_value_t = LogLevel::Warning)]
    log_level: LogLevel,

    /// write output to the input source file
    #[clap(short, long)]
    in_place: bool,

    /// search in macros
    #[clap(long, action = ArgAction::Set, default_value_t = true)]
    parse_macros: bool,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, clap::ArgEnum)]
enum LogLevel {
    Advice,
    Warning,
    Error,
    None,
}

fn main() -> miette::Result<()> {
    let cli = Cli::parse();

    let log_level = match cli.log_level {
        LogLevel::Advice => interpreter::LogLevel::Advice,
        LogLevel::Warning => interpreter::LogLevel::Warning,
        LogLevel::Error => interpreter::LogLevel::Error,
        LogLevel::None => interpreter::LogLevel::None,
    };

    let report_config = ariadne::Config::default().with_color(std::io::stderr().is_terminal());

    let mut interpreter = Interpreter::new(
        cli.script_file,
        InterpreterConfig {
            report_config,
            log_level,
            in_place: cli.in_place,
            parse_macros: cli.parse_macros,
        },
    )?;

    interpreter.run(cli.source_file)?;

    Ok(())
}

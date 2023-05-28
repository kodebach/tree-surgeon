use std::path::PathBuf;

use clap::{command, ArgAction, Parser};

use tree_surgeon::interpreter::{self, Interpreter, InterpreterConfig};

#[derive(clap::Parser, Debug)]
#[command(author, version, about, long_about=None)]
struct Cli {
    /// source file to edit
    #[arg()]
    source_file: PathBuf,

    /// script to execute, if missing use stdin
    #[arg()]
    script_file: Option<PathBuf>,

    /// amount of information to print
    #[arg(value_enum, short, long, default_value_t = LogLevel::Warning)]
    log_level: LogLevel,

    /// write output to the input source file
    #[arg(short, long)]
    in_place: bool,

    /// search in macros
    #[arg(long, action = ArgAction::Set, default_value_t = true)]
    parse_macros: bool,

    #[arg(value_enum, long, default_value_t = Language::C)]
    language: Language,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum)]
enum LogLevel {
    Advice,
    Warning,
    Error,
    None,
}

impl LogLevel {
    fn interpreter_level(&self) -> interpreter::LogLevel {
        match self {
            LogLevel::Advice => interpreter::LogLevel::Advice,
            LogLevel::Warning => interpreter::LogLevel::Warning,
            LogLevel::Error => interpreter::LogLevel::Error,
            LogLevel::None => interpreter::LogLevel::None,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum)]
enum Language {
    C,
}

impl Language {
    fn tree_sitter_language(&self) -> tree_sitter::Language {
        match self {
            Language::C => tree_sitter_c::language(),
        }
    }
}

fn main() -> miette::Result<()> {
    let cli = Cli::parse();

    let mut stderr = std::io::stderr();
    let mut interpreter = Interpreter::new(
        cli.script_file,
        &mut stderr,
        InterpreterConfig {
            log_level: cli.log_level.interpreter_level(),
            language: cli.language.tree_sitter_language(),
            in_place: cli.in_place,
            parse_macros: cli.parse_macros,
        },
    )?;

    interpreter.run(cli.source_file)?;

    Ok(())
}

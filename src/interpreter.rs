use std::{collections::HashMap, fs, path::PathBuf, str::Utf8Error};

use miette::IntoDiagnostic;
use tree_sitter::{Language, Parser, QueryCursor, Tree};

use crate::{
    dsl::{
        ast::{Match, Script, Statement},
        parser::Parsable,
    },
    single::{Single, SingleError},
};

pub struct Interpreter {
    source: Vec<u8>,
    tree: Tree,
    script: Script,
}

#[derive(Debug, thiserror::Error)]
enum MatchError {
    #[error(transparent)]
    Single(SingleError),
    #[error(transparent)]
    Utf8(Utf8Error),
}

#[derive(Debug, thiserror::Error)]
#[error("tree-sitter couldn't parse the file {source_file}")]
struct TreeParseError {
    source_file: PathBuf,
}

impl Interpreter {
    pub fn new(source_file: PathBuf, script_source: String) -> miette::Result<Interpreter> {
        extern "C" {
            fn tree_sitter_c() -> Language;
        }

        let mut parser = Parser::new();
        parser
            .set_language(unsafe { tree_sitter_c() })
            .into_diagnostic()?;

        let source = fs::read(&source_file).into_diagnostic()?;

        let tree = parser
            .parse(&source, Option::None)
            .ok_or(TreeParseError { source_file })
            .into_diagnostic()?;

        let script = Script::parse(&script_source, tree.language()).map_err(|e| e.into_owned())?;

        Ok(Interpreter {
            source,
            tree,
            script,
        })
    }

    fn execute_match(&self, m: &Match) -> miette::Result<()> {
        let query = m.query();

        let mut cursor = QueryCursor::new();
        let source = self.source.as_slice();
        let matches = cursor.matches(&query, self.tree.root_node(), source);

        let capture_indices: HashMap<_, _> = query
            .capture_names()
            .iter()
            .filter_map(|name| {
                query
                    .capture_index_for_name(name)
                    .map(|index| (name, index))
            })
            .collect();

        let res: Result<Vec<HashMap<_, _>>, _> = matches
            .map(|query_match| {
                capture_indices
                    .iter()
                    .map(|(name, &index)| {
                        query_match
                            .nodes_for_capture_index(index)
                            .single()
                            .map_err(MatchError::Single)
                            .and_then(|node| node.utf8_text(source).map_err(MatchError::Utf8))
                            .map(|text| {
                                (
                                    name,
                                    (
                                        text,
                                        if m.replacement().capture_name() == *name {
                                            Some(m.replacement().replacement())
                                        } else {
                                            None
                                        },
                                    ),
                                )
                            })
                    })
                    .collect()
            })
            .collect();

        let captures = res.into_diagnostic()?;

        println!("{:#?}", captures);

        Ok(())
    }

    fn execute_statement(&self, statement: &Statement) -> miette::Result<()> {
        match statement {
            Statement::Match(m) => self.execute_match(m),
        }
    }

    pub fn run(&self) -> miette::Result<()> {
        for statement in self.script.statements() {
            self.execute_statement(statement)?
        }

        Ok(())
    }
}

use nom::{
    branch::alt,
    character::complete::{
        alphanumeric1, char as nom_char, multispace0, multispace1, none_of, one_of, satisfy,
    },
    combinator::{eof, opt},
    multi::{many0, many1, many_till},
    sequence::{delimited, tuple},
    IResult, Parser,
};

use nom_supreme::{
    final_parser::final_parser,
    tag::complete::{tag, tag_no_case},
    ParserExt,
};
use pori::{Located, Location, Stateful};
use tree_sitter::{Language, Query, QueryError};

use crate::single::Error;
use std::{borrow::Cow, fmt::Display};

use miette::{Diagnostic, LabeledSpan, SourceCode};
use nom_supreme::error::GenericErrorTree;
use thiserror::Error;

#[derive(Debug)]
pub struct Script {
    statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct Match {
    query: Query,
}

#[derive(Debug)]
pub enum Statement {
    Match(Match),
}

// TODO: taken from https://github.com/olson-sean-k/wax/blob/1c72837149bcdb3aaa08cbecb420450ed9ad7d79/src/token/parse.rs

type InputData<'a> = Located<'a, str>;
type Input<'a> = Stateful<InputData<'a>, ParserState>;
type ErrorTree<'i> = nom_supreme::error::ErrorTree<Input<'i>>;

#[derive(Clone, Copy, Debug)]
pub struct ParserState {
    language: Language,
}

#[derive(Debug, Error)]
#[error("failed to parse tree-surgeon script")]
pub struct ParseError<'t> {
    input: Cow<'t, str>,
    error: nom_supreme::error::ErrorTree<usize>,
}

impl<'t> ParseError<'t> {
    pub fn new(expression: &'t str, error: ErrorTree<'t>) -> Self {
        ParseError {
            input: expression.into(),
            error: error.map_locations(|l| l.location()),
        }
    }

    /// Clones any borrowed data into an owning instance.
    pub fn into_owned(self) -> ParseError<'static> {
        let ParseError {
            input: expression,
            error,
        } = self;
        ParseError {
            input: expression.into_owned().into(),
            error,
        }
    }

    /// Gets the glob expression that failed to parse.
    pub fn expression(&self) -> &str {
        self.input.as_ref()
    }
}

impl Diagnostic for ParseError<'_> {
    fn code<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        Some(Box::new("tree_surgeon::dsl::parse"))
    }

    fn source_code(&self) -> Option<&dyn SourceCode> {
        Some(&self.input)
    }

    // Surfacing useful parsing errors is difficult. This code replaces any
    // lower bound errors with a simple label noting the beginning of the
    // parsing error. Details are discarded, because these are typically
    // top-level alternative errors that do not provide any useful insight.
    // Upper bound errors are labeled as-is, though they only sometimes provide
    // useful context.
    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        fn labels<'a>(
            error: &'a nom_supreme::error::ErrorTree<usize>,
        ) -> Box<dyn Iterator<Item = LabeledSpan> + 'a> {
            match error {
                GenericErrorTree::Base { location, kind } => Box::new(
                    Some(LabeledSpan::new(Some(format!("{}", kind)), *location, 1)).into_iter(),
                ),
                GenericErrorTree::Stack { base, contexts } => Box::new(labels(base).chain(
                    contexts.iter().map(|(location, context)| {
                        LabeledSpan::new(Some(format!("{}", context)), *location, 1)
                    }),
                )),
                GenericErrorTree::Alt(ref trees) => Box::new(trees.iter().flat_map(labels)),
            }
        }

        let l = Vec::from_iter(labels(&self.error));
        eprintln!("{}", self.error);
        Some(Box::new(l.into_iter()))
    }
}

struct SExpr {}

impl SExpr {
    fn s_exp<'a, F>(inner: F) -> impl Parser<Input<'a>, (), ErrorTree<'a>>
    where
        F: Parser<Input<'a>, (), ErrorTree<'a>>,
    {
        delimited(
            nom_char('('),
            inner.preceded_by(multispace0),
            nom_char(')')
                .preceded_by(multispace0)
                .cut()
                .context("closing paren"),
        )
    }

    fn parse_atom<'a>(input: Input<'a>) -> IResult<Input<'a>, (), ErrorTree<'a>> {
        many1(satisfy(|c| !c.is_whitespace() && c != '(' && c != ')'))
            .context("atom")
            .map(|_| ())
            .parse(input)
    }

    fn parse_application<'a>(input: Input<'a>) -> IResult<Input<'a>, (), ErrorTree<'a>> {
        let inner = tuple((Self::parse_expr, many0(Self::parse_expr))).map(|_| ());
        Self::s_exp(inner).parse(input)
    }

    fn parse_expr<'a>(input: Input<'a>) -> IResult<Input<'a>, (), ErrorTree<'a>> {
        alt((Self::parse_atom, Self::parse_application))
            .preceded_by(multispace0)
            .parse(input)
    }

    fn parser<'a>() -> impl Parser<Input<'a>, &'a str, ErrorTree<'a>> {
        Self::parse_application.recognize().map(|s| s.into_data())
    }
}

impl Match {
    fn parse<'a>(input: Input<'a>) -> IResult<Input<'a>, Self, ErrorTree<'a>> {
        tag_no_case("MATCH")
            .preceded_by(multispace0)
            .cut()
            .context("MATCH")
            .and(
                SExpr::parser()
                    .delimited_by(multispace0)
                    .map_res(|query| Query::new(input.state.language, query)),
            )
            .map(|(_, query)| Match { query })
            .parse(input)
    }

    pub fn query<'a>(self: &'a Self) -> &'a Query {
        &self.query
    }
}

impl Statement {
    fn parser<'a>() -> impl Parser<Input<'a>, Self, ErrorTree<'a>> {
        alt((Match::parse.map(Statement::Match),))
            .preceded_by(multispace0)
            .context("statement")
            .cut()
    }
}

pub struct ScriptParser {
    source: String,
}

impl ScriptParser {
    pub fn new(input: String) -> Self {
        ScriptParser { source: input }
    }

    pub fn parse<'a>(self: &'a Self, language: Language) -> Result<Script, ParseError> {
        let inputData = InputData::from(self.source.as_str());
        let input = Input::new(inputData, ParserState { language });

        Script::parser()
            .complete()
            .all_consuming()
            .parse(input)
            .map(|(_, script)| script)
            .map_err(|err| match err {
                nom::Err::Incomplete(_) => {
                    unreachable!("Complete combinator should make this impossible")
                }
                nom::Err::Error(e) | nom::Err::Failure(e) => {
                    ParseError::new(self.source.as_str(), e)
                }
            })
    }
}

impl Script {
    fn parser<'a>() -> impl Parser<Input<'a>, Self, ErrorTree<'a>> {
        many_till(Statement::parser(), eof).map(|(s, _)| Script { statements: s })
    }

    pub fn statements<'a>(self: &'a Self) -> &'a [Statement] {
        &self.statements
    }
}

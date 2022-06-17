use nom::{
    branch::alt,
    character::complete::{char as nom_char, multispace0, multispace1, satisfy},
    combinator::eof,
    multi::{many0, many1, many_till},
    sequence::{delimited, separated_pair, tuple},
    IResult, Parser,
};

use nom_supreme::{tag::complete::tag_no_case, ParserExt};
use pori::{Located, Location, Stateful};
use tree_sitter::{Language, Query};

use std::{borrow::Cow, fmt::Display};

use miette::{Diagnostic, LabeledSpan, SourceCode};
use nom_supreme::error::GenericErrorTree;
use thiserror::Error;

use super::{
    ast::{Match, Replacement, Script, Statement},
    string::parse_string,
};

type InputData<'a> = Located<'a, str>;
type Input<'a> = Stateful<InputData<'a>, ParserState>;
type ErrorTree<'i> = nom_supreme::error::ErrorTree<Input<'i>>;
type ParseResult<'a, T> = IResult<Input<'a>, T, ErrorTree<'a>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        fn labels<'a>(
            input_size: usize,
            error: &'a nom_supreme::error::ErrorTree<usize>,
        ) -> Box<dyn Iterator<Item = LabeledSpan> + 'a> {
            match error {
                GenericErrorTree::Base { location, kind } => Box::new(
                    Some(LabeledSpan::new(
                        Some(format!("{}", kind)),
                        (input_size - 1).min(*location),
                        1,
                    ))
                    .into_iter(),
                ),
                GenericErrorTree::Stack { base, contexts } => {
                    Box::new(labels(input_size, base).chain(contexts.iter().map(
                        move |(location, context)| {
                            LabeledSpan::new(
                                Some(format!("{}", context)),
                                (input_size - 1).min(*location),
                                1,
                            )
                        },
                    )))
                }
                GenericErrorTree::Alt(ref trees) => Box::new(
                    trees
                        .iter()
                        .flat_map(move |error| labels(input_size, error)),
                ),
            }
        }

        Some(labels(self.input.len(), &self.error))
    }
}

fn s_exp<'a, F>(inner: F) -> impl Parser<Input<'a>, (), ErrorTree<'a>>
where
    F: Parser<Input<'a>, (), ErrorTree<'a>>,
{
    delimited(
        nom_char('('),
        inner.preceded_by(multispace0),
        nom_char(')').preceded_by(multispace0).cut(),
    )
}

fn parse_atom<'a>(input: Input<'a>) -> IResult<Input<'a>, (), ErrorTree<'a>> {
    many1(satisfy(|c| !c.is_whitespace() && c != '(' && c != ')'))
        .context("atom")
        .map(|_| ())
        .parse(input)
}

fn parse_application<'a>(input: Input<'a>) -> IResult<Input<'a>, (), ErrorTree<'a>> {
    let inner = tuple((parse_expr, many0(parse_expr))).map(|_| ());
    s_exp(inner).parse(input)
}

fn parse_expr<'a>(input: Input<'a>) -> IResult<Input<'a>, (), ErrorTree<'a>> {
    alt((parse_atom, parse_application))
        .preceded_by(multispace0)
        .parse(input)
}

fn parse_sexpr<'a>(input: Input<'a>) -> ParseResult<&'a str> {
    parse_application
        .recognize()
        .map(|s| s.into_data())
        .parse(input)
}

fn parse_match<'a>(input: Input<'a>) -> ParseResult<Match> {
    let query = parse_sexpr
        .context("query")
        .preceded_by(multispace0)
        .map_res(|query| Query::new(input.state.language, query));

    let capture_ref = nom_char('@')
        .context("capture reference")
        .precedes(many1(satisfy(|c| {
            !c.is_whitespace() && c != '(' && c != ')'
        })))
        .map(|v| v.into_iter().collect());

    let replacement = tag_no_case("REPLACE")
        .context("replacement")
        .preceded_by(multispace0)
        .precedes(
            separated_pair(
                capture_ref.preceded_by(multispace0),
                tag_no_case("WITH").preceded_by(multispace1),
                parse_string.preceded_by(multispace0),
            )
            .map(|(c, r)| Replacement::new(c, r)),
        );

    tag_no_case("MATCH")
        .preceded_by(multispace0)
        .cut()
        .context("match")
        .and(query)
        .and(replacement)
        .map(|((_, query), replacement)| Match::new(query, replacement))
        .parse(input)
}

fn parse_statement<'a>(input: Input<'a>) -> ParseResult<Statement> {
    alt((parse_match.map(Statement::Match),))
        .terminated(nom_char(';').preceded_by(multispace0))
        .context("statement")
        .delimited_by(multispace0)
        .cut()
        .parse(input)
}

fn parse_script<'a>(input: Input<'a>) -> ParseResult<Script> {
    many_till(parse_statement, eof)
        .map(|(s, _)| Script::new(s))
        .parse(input)
}

pub trait Parsable: Sized {
    fn parse<'a>(source: &'a str, language: Language) -> Result<Self, ParseError>;
}

impl Parsable for Script {
    fn parse<'a>(source: &'a str, language: Language) -> Result<Script, ParseError> {
        let input_data = InputData::from(source);
        let input = Input::new(input_data, ParserState { language });

        parse_script
            .complete()
            .all_consuming()
            .parse(input)
            .map(|(_, script)| script)
            .map_err(|err| match err {
                nom::Err::Incomplete(_) => {
                    unreachable!("Complete combinator should make this impossible")
                }
                nom::Err::Error(e) | nom::Err::Failure(e) => ParseError::new(source, e),
            })
    }
}

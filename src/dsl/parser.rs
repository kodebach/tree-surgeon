use std::fmt;

use ariadne::{Color, Fmt, Label, Report, ReportKind};

use chumsky::{prelude::*, text::Character, Stream};
use tree_sitter::{Language, Query};

use super::ast::{Match, Replacement, Script, Span, Statement};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Token {
    Str(String),
    CaptureRef(String),
    SExpr(String),
    Keyword(Keyword),
    Ctrl(Ctrl),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Str(s) => write!(f, "{}", s),
            Token::CaptureRef(name) => write!(f, "@{}", name),
            Token::SExpr(expr) => write!(f, "{}", expr),
            Token::Keyword(keyword) => match keyword {
                Keyword::Match => write!(f, "match"),
                Keyword::Replace => write!(f, "replace"),
                Keyword::With => write!(f, "with"),
            },
            Token::Ctrl(ctrl) => match ctrl {
                Ctrl::Semicolon => write!(f, ";"),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Keyword {
    Match,
    Replace,
    With,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Ctrl {
    Semicolon,
}

pub trait Parsable: Sized {
    fn parse<'a>(source: &'a str, language: Language) -> (Option<Script>, Vec<Report>);
}

fn lexer() -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
    let escape = just('\\').ignore_then(
        just('\\')
            .or(just('/'))
            .or(just('"'))
            .or(just('b').to('\x08'))
            .or(just('f').to('\x0C'))
            .or(just('n').to('\n'))
            .or(just('r').to('\r'))
            .or(just('t').to('\t'))
            .or(just('u').ignore_then(
                filter(|c: &char| c.is_digit(16))
                    .repeated()
                    .exactly(4)
                    .collect::<String>()
                    .validate(|digits, span, emit| {
                        char::from_u32(u32::from_str_radix(&digits, 16).unwrap()).unwrap_or_else(
                            || {
                                emit(Simple::custom(span, "invalid unicode character"));
                                '\u{FFFD}' // unicode replacement character
                            },
                        )
                    }),
            )),
    );

    let string = just('"')
        .ignore_then(filter(|c| *c != '\\' && *c != '"').or(escape).repeated())
        .then_ignore(just('"'))
        .collect::<String>()
        .map(Token::Str)
        .labelled("string");

    let ctrl = choice((just(";").to(Ctrl::Semicolon),)).map(Token::Ctrl);

    let keyword = choice((
        just("match").to(Keyword::Match),
        just("replace").to(Keyword::Replace),
        just("with").to(Keyword::With),
    ))
    .map(Token::Keyword);

    let capture_ref = just("@")
        .ignore_then(filter(|c: &char| !c.is_whitespace() && *c != '(' && *c != ')').repeated())
        .collect::<String>()
        .map(Token::CaptureRef);

    let sexpr = recursive(|sexpr| {
        let atom = filter(|c: &char| !c.is_whitespace() && *c != '(' && *c != ')')
            .repeated()
            .collect::<String>();

        choice((sexpr.clone(), atom))
            .separated_by(filter(|c: &char| c.is_whitespace()))
            .map(|atoms| atoms.join(" "))
            .or_not()
            .delimited_by(just("("), just(")"))
            .map(|nested| format!("({})", nested.unwrap_or(String::new())))
    })
    .map(Token::SExpr);

    let token = string
        .or(ctrl)
        .or(keyword)
        .or(capture_ref)
        .or(sexpr)
        .recover_with(skip_then_retry_until([]));

    token
        .map_with_span(|tok, span| (tok, span))
        .padded()
        .repeated()
}

struct DslParser {
    language: Language,
}

impl DslParser {
    fn replacement(&self) -> impl Parser<Token, Replacement, Error = Simple<Token>> + Clone {
        let capture_ref = filter_map(|span, tok| match tok {
            Token::CaptureRef(capture_ref) => Ok(capture_ref.clone()),
            _ => Err(Simple::expected_input_found(span, Vec::new(), Some(tok))),
        });

        let str_ = filter_map(|span, tok| match tok {
            Token::Str(str_) => Ok(str_.clone()),
            _ => Err(Simple::expected_input_found(span, Vec::new(), Some(tok))),
        });

        just(Token::Keyword(Keyword::Replace))
            .then(capture_ref.labelled("capture reference"))
            .then(just(Token::Keyword(Keyword::With)))
            .then(str_.labelled("replacement literal"))
            .map(|(((_, capture_name), _), replacement)| {
                Replacement::new(capture_name, replacement)
            })
    }

    fn match_<'a>(&'a self) -> impl Parser<Token, Match, Error = Simple<Token>> + Clone + 'a {
        let sexpr = filter_map(|span, tok| match tok {
            Token::SExpr(sexpr) => Ok(sexpr.clone()),
            _ => Err(Simple::expected_input_found(span, Vec::new(), Some(tok))),
        });

        just(Token::Keyword(Keyword::Match))
            .then(
                sexpr
                    .try_map(|query, span| {
                        Query::new(self.language, &query)
                            .map_err(|e| Simple::custom(span, format!("malformatted query: {}", e)))
                    })
                    .labelled("query"),
            )
            .then(self.replacement().labelled("replacement"))
            .map(|((_, query), replacement)| Match::new(query, replacement))
    }

    fn statement<'a>(
        &'a self,
    ) -> impl Parser<Token, Statement, Error = Simple<Token>> + Clone + 'a {
        self.match_()
            .then_ignore(just(Token::Ctrl(Ctrl::Semicolon)))
            .map(|m| Statement::Match(m))
    }

    fn script<'a>(&'a self) -> impl Parser<Token, Script, Error = Simple<Token>> + Clone + 'a {
        self.statement()
            .repeated()
            .then_ignore(end())
            .map(Script::new)
    }
}

impl Parsable for Script {
    fn parse<'a>(source: &'a str, language: Language) -> (Option<Script>, Vec<Report>) {
        let (tokens, errs) = lexer().parse_recovery(source);

        let (script, parse_errs) = if let Some(tokens) = tokens {
            let parser = DslParser { language };

            let len = source.chars().count();
            let (ast, parse_errs) = parser
                .script()
                .parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));

            if let Some(script) = ast.filter(|_| errs.len() + parse_errs.len() == 0) {
                (Some(script), parse_errs)
            } else {
                (None, parse_errs)
            }
        } else {
            (None, Vec::new())
        };

        let reports: Vec<_> = errs
            .into_iter()
            .map(|e| e.map(|c| c.to_string()))
            .chain(parse_errs.into_iter().map(|e| e.map(|tok| tok.to_string())))
            .map(|e| {
                let report = Report::build(ReportKind::Error, (), e.span().start);

                let report = match e.reason() {
                    chumsky::error::SimpleReason::Unclosed { span, delimiter } => report
                        .with_message(format!(
                            "Unclosed delimiter {}",
                            delimiter.fg(Color::Yellow)
                        ))
                        .with_label(
                            Label::new(span.clone())
                                .with_message(format!(
                                    "Unclosed delimiter {}",
                                    delimiter.fg(Color::Yellow)
                                ))
                                .with_color(Color::Yellow),
                        )
                        .with_label(
                            Label::new(e.span())
                                .with_message(format!(
                                    "Must be closed before this {}",
                                    e.found()
                                        .unwrap_or(&"end of file".to_string())
                                        .fg(Color::Red)
                                ))
                                .with_color(Color::Red),
                        ),
                    chumsky::error::SimpleReason::Unexpected => report
                        .with_message(format!(
                            "{}, expected {}",
                            if e.found().is_some() {
                                "Unexpected token in input"
                            } else {
                                "Unexpected end of input"
                            },
                            if e.expected().len() == 0 {
                                "something else".to_string()
                            } else {
                                e.expected()
                                    .map(|expected| match expected {
                                        Some(expected) => expected.to_string(),
                                        None => "end of input".to_string(),
                                    })
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            }
                        ))
                        .with_label(
                            Label::new(e.span())
                                .with_message(format!(
                                    "Unexpected token {}",
                                    e.found()
                                        .unwrap_or(&"end of file".to_string())
                                        .fg(Color::Red)
                                ))
                                .with_color(Color::Red),
                        ),
                    chumsky::error::SimpleReason::Custom(msg) => {
                        report.with_message(msg).with_label(
                            Label::new(e.span())
                                .with_message(format!("{}", msg.fg(Color::Red)))
                                .with_color(Color::Red),
                        )
                    }
                };

                report.finish()
            })
            .collect();

        (script, reports)
    }
}

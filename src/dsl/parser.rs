use logos::Logos;

use std::marker::PhantomData;

use ariadne::{Color, Label, Report, ReportKind};

use chumsky::{
    input::{Stream, ValueInput},
    prelude::*,
};
use tree_sitter::{Language, Query as TsQuery};

use super::{ast::*, lexer::Token, query::*};

trait TokenInput<'a>: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan> {}

pub trait Parsable: Sized {
    fn parse<'a, 'b>(
        source: &'a str,
        language: Language,
        config: ariadne::Config,
    ) -> (Option<Script>, Vec<Report<'b>>);
}

struct DslParser<'a, I>
where
    I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>,
{
    language: Language,
    marker: PhantomData<&'a I>,
}

type Err<'a> = extra::Err<Rich<'a, Token<'a>>>;

impl<'a, I> DslParser<'a, I>
where
    I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>,
{
    fn capture() -> impl Parser<'a, I, &'a str, Err<'a>> + Clone {
        select! {
            Token::Capture(name) => name.clone()
        }
    }

    fn string_literal() -> impl Parser<'a, I, String, Err<'a>> + Clone {
        select! {
            Token::String(s) => s,
        }
    }

    fn ident() -> impl Parser<'a, I, &'a str, Err<'a>> + Clone {
        select! {
            Token::Identifier(i) => i,
        }
    }

    fn num() -> impl Parser<'a, I, isize, Err<'a>> + Clone {
        select! {
            Token::Number(n) => n,
        }
        .try_map(|n, span| {
            n.parse::<isize>()
                .map_err(|e| Rich::custom(span, e.to_string()))
        })
    }

    fn join_expr() -> impl Parser<'a, I, Vec<JoinItem>, Err<'a>> + Clone {
        let recase_ident = Self::ident()
            .from_str::<Case>()
            .try_map(|res, span| res.map_err(|e| Rich::custom(span, e.to_string())));

        let recase_suffix = just(Token::Dollar)
            .ignore_then(recase_ident)
            .labelled("recase suffix");

        let index = Self::num().labelled("index");

        let range_suffix = index
            .clone()
            .or_not()
            .then_ignore(just(Token::Colon))
            .then(index.clone().or_not())
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .labelled("index range");

        let capture_expr = Self::capture()
            .then(recase_suffix.or_not())
            .then(range_suffix.or_not());

        choice((
            Self::string_literal().map(JoinItem::Literal),
            capture_expr.map(|((capture, case), range)| {
                if let Some((from, to)) = range {
                    JoinItem::CaptureExpr(CaptureExpr::new(
                        capture.to_string(),
                        case,
                        Some(from..to),
                    ))
                } else {
                    JoinItem::CaptureExpr(CaptureExpr::new(capture.to_string(), case, None))
                }
            }),
        ))
        .repeated()
        .collect()
        .delimited_by(just(Token::LBracket), just(Token::RBracket))
    }

    fn string_expression() -> impl Parser<'a, I, StringExpression, Err<'a>> + Clone {
        choice((
            Self::string_literal()
                .labelled("string literal")
                .map(StringExpression::Literal),
            Self::join_expr()
                .labelled("string join expression")
                .map(StringExpression::Join),
        ))
    }

    fn replacement() -> impl Parser<'a, I, Replace, Err<'a>> + Clone {
        just(Token::Replace)
            .ignore_then(Self::capture().labelled("capture reference"))
            .then(choice((
                just(Token::With)
                    .ignore_then(Self::string_literal())
                    .map(StringExpression::Literal),
                just(Token::By).ignore_then(Self::string_expression()),
            )))
            .map(|(capture, replacement)| Replace::new(capture.to_string(), replacement))
    }

    fn warning() -> impl Parser<'a, I, Warn, Err<'a>> + Clone {
        just(Token::Warn)
            .ignore_then(Self::capture().labelled("capture reference"))
            .then(Self::string_expression())
            .map(|(capture, string_expr)| Warn::new(capture.to_string(), string_expr))
    }

    fn query() -> impl Parser<'a, I, Query, Err<'a>> + Clone {
        let capture = select! {
            Token::Capture(c) => c
        }
        .map(ToString::to_string)
        .labelled("capture");

        let string = select! {
            Token::String(s) => s,
        }
        .labelled("string");

        let predicate = {
            let predicate_name = select! {
                Token::PredicateName(p) => p,
            }
            .map(ToString::to_string)
            .labelled("predicate name");

            let ident = select! {
                Token::Identifier(ident) => ident,
            }
            .map(ToString::to_string)
            .labelled("identifier");

            predicate_name
                .then(
                    choice((
                        capture.map(PredicateArg::Capture),
                        string.map(PredicateArg::Str),
                        ident.map(PredicateArg::Ident),
                    ))
                    .repeated()
                    .collect(),
                )
                .map(|(name, args)| Predicate { name, args })
                .labelled("predicate")
        };

        let pattern = recursive(|pattern| {
            let quantifier = select! {
                Token::Plus => Quantifier::OneOrMore,
                Token::QuestionMark => Quantifier::ZeroOrOne,
                Token::Asterisk => Quantifier::ZeroOrMore,
            }
            .labelled("quantifier");

            let anonymous_leaf = string
                .map(PatternData::AnonymousLeaf)
                .labelled("anonymous leaf");

            let wildcard_node = choice((
                just(Token::Underscore).ignored(),
                just([Token::LParen, Token::Underscore, Token::RParen]).ignored(),
            ))
            .to(PatternData::WildcardNode)
            .labelled("wildcard node");

            let alternation = pattern
                .clone()
                .map(AlternationItem::Choice)
                .or(predicate.clone().map(AlternationItem::Predicate))
                .repeated()
                .collect()
                .delimited_by(just(Token::LBracket), just(Token::RBracket))
                .map(PatternData::Alternation)
                .labelled("alternation");

            let group = pattern
                .clone()
                .map(GroupItem::Pattern)
                .or(predicate.clone().map(GroupItem::Predicate))
                .repeated()
                .collect()
                .delimited_by(just(Token::LParen), just(Token::RParen))
                .map(PatternData::Group)
                .labelled("group");

            let named_node = {
                let ident = select! {
                    Token::Identifier(i) => i
                }
                .map(ToString::to_string);

                let node_name = ident.clone().labelled("node name");

                let field_name = ident.clone().labelled("field name");

                let anchor = just(Token::Dot).to(Anchor).labelled("anchor");

                let child = field_name
                    .then_ignore(just(Token::Colon))
                    .or_not()
                    .then(pattern.clone())
                    .map(|(i, p)| NamedNodeItem::Child(i, p))
                    .labelled("child");

                let negated_child = just(Token::Bang)
                    .ignore_then(field_name)
                    .map(NamedNodeItem::NegatedChild)
                    .labelled("negated child");

                node_name
                    .then(
                        anchor
                            .clone()
                            .or_not()
                            .then(choice((
                                child,
                                negated_child,
                                predicate.clone().map(NamedNodeItem::Predicate),
                            )))
                            .map(|(anchor, item)| AnchoredNamedNodeItem {
                                anchor: anchor.is_some(),
                                item,
                            })
                            .repeated()
                            .collect()
                            .then(anchor.clone().or_not()),
                    )
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .map(|(name, (items, anchor))| PatternData::NamedNode(name, items, anchor))
                    .labelled("named node")
            };

            choice((
                wildcard_node,
                alternation,
                anonymous_leaf,
                group,
                named_node,
            ))
            .then(quantifier.or_not())
            .then(capture.or_not())
            .map(|((pattern, quantifier), capture)| Pattern {
                pattern,
                quantifier,
                capture,
            })
            .labelled("pattern")
        });

        pattern
            .map(QueryItem::Pattern)
            .or(predicate.map(QueryItem::Predicate))
            .recover_with(via_parser(nested_delimiters(
                Token::LParen,
                Token::RParen,
                [(Token::LBracket, Token::RBracket)],
                |_| QueryItem::Invalid,
            )))
            .recover_with(via_parser(nested_delimiters(
                Token::LBracket,
                Token::RBracket,
                [(Token::LParen, Token::RParen)],
                |_| QueryItem::Invalid,
            )))
            .repeated()
            .collect()
            .map(|items| Query { items })
            .labelled("query")
    }

    fn match_action() -> impl Parser<'a, I, MatchAction, Err<'a>> + Clone {
        choice((
            Self::replacement()
                .labelled("replacement")
                .map(MatchAction::Replace),
            Self::warning().labelled("warning").map(MatchAction::Warn),
        ))
    }

    fn match_(&self) -> impl Parser<'a, I, Option<Match>, Err<'a>> + Clone + '_ {
        just(Token::Match)
            .ignore_then(
                Self::query()
                    .validate(|query, span, emitter| {
                        if query.items.iter().any(|item| item == &QueryItem::Invalid) {
                            emitter.emit(Rich::custom(span, "malformatted query"));
                            None
                        } else {
                            TsQuery::new(self.language, &query.to_string())
                                .map(Some)
                                .unwrap_or_else(|e| {
                                    emitter.emit(Rich::custom(
                                        span,
                                        format!("malformatted query: {}", e),
                                    ));
                                    None
                                })
                        }
                    })
                    .labelled("query"),
            )
            .then(Self::match_action().labelled("action"))
            .map(|(query, action)| query.map(|query| Match::new(query, action)))
    }

    fn statement(&self) -> impl Parser<'a, I, Statement, Err<'a>> + Clone + '_ {
        self.match_()
            .then_ignore(just(Token::Semicolon))
            .validate(|m, span, emitter| {
                m.map(|m| Statement::Match(m)).unwrap_or_else(|| {
                    emitter.emit(Rich::custom(span, "invalid match"));
                    Statement::Invalid
                })
            })
    }

    fn script(&self) -> impl Parser<'a, I, Script, Err<'a>> + Clone + '_ {
        self.statement()
            .repeated()
            .collect()
            .then_ignore(end())
            .map(Script::new)
    }
}

impl Parsable for Script {
    fn parse<'a, 'b>(
        source: &'a str,
        language: Language,
        config: ariadne::Config,
    ) -> (Option<Script>, Vec<Report<'b>>) {
        let parser = DslParser {
            language,
            marker: Default::default(),
        };

        let tokens: Vec<_> = Token::lexer(source).spanned().collect();

        // eprintln!("{:?}", tokens);

        let token_iter = tokens
            .into_iter()
            .filter(|(token, _)| !matches!(token, Token::Comment))
            .map(|(tok, span)| (tok, SimpleSpan::from(span)));

        let eoi = SimpleSpan::new(source.len(), source.len());

        let token_stream = Stream::from_iter(token_iter).spanned(eoi);

        let (script, parse_errs) = parser.script().parse(token_stream).into_output_errors();

        let reports: Vec<_> = parse_errs
            .into_iter()
            .map(|e| e.map_token(|tok| tok.to_string()))
            .map(|e| {
                Report::build(ReportKind::Error, (), e.span().start)
                    .with_config(config)
                    .with_message(e.to_string())
                    .with_label(
                        Label::new(e.span().into_range())
                            .with_message(e.reason().to_string())
                            .with_color(Color::Red),
                    )
                    .finish()
            })
            .collect();

        if reports.is_empty() {
            (script, reports)
        } else {
            (None, reports)
        }
    }
}

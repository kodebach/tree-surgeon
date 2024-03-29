use chumsky::{
    input::{SliceInput, ValueInput},
    prelude::*,
};
use miette::{miette, LabeledSpan, Report, Severity};
use rstest::rstest;
use std::{fmt::Write, marker::PhantomData};
use tree_sitter::{Language, Query as TsQuery};

use super::lexer::*;
use super::query::*;
use crate::dsl::ast::*;

trait TokenInput<'a>: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan> {}

pub trait Parsable: Sized {
    fn parse(source: &str, language: Language) -> (Option<Script>, Vec<Report>);
}

struct DslParser<'a, I> {
    source: &'a str,
    language: Language,
    marker: PhantomData<I>,
}

type Err<'a> = extra::Err<Rich<'a, Token<'a>>>;

impl<'a, I> DslParser<'a, I>
where
    I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>
        + SliceInput<'a, Slice = &'a [(Token<'a>, SimpleSpan)]>,
{
    fn capture() -> impl Parser<'a, I, &'a str, Err<'a>> + Clone {
        select! {
            Token::Capture(name) => name
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
            .map(|(start, end)| start..end)
            .labelled("index range");

        let capture_expr = group((
            Self::capture().map(ToString::to_string),
            recase_suffix.or_not(),
            range_suffix.or_not(),
        ))
        .map(|(capture_name, target_case, range)| CaptureExpr {
            capture_name,
            target_case,
            range,
        });

        choice((
            Self::string_literal().map(JoinItem::Literal),
            capture_expr.map(JoinItem::CaptureExpr),
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
            .ignore_then(
                Self::capture()
                    .map(ToString::to_string)
                    .labelled("capture reference"),
            )
            .then(choice((
                just(Token::With)
                    .ignore_then(Self::string_literal())
                    .map(StringExpression::Literal),
                just(Token::By).ignore_then(Self::string_expression()),
            )))
            .map(|(capture_name, replacement)| Replace {
                capture_name,
                replacement,
            })
    }

    fn warning() -> impl Parser<'a, I, Warn, Err<'a>> + Clone {
        just(Token::Warn)
            .ignore_then(
                Self::capture()
                    .map(ToString::to_string)
                    .labelled("capture reference"),
            )
            .then(Self::string_expression())
            .map(|(capture_name, message)| Warn {
                capture_name,
                message,
            })
    }

    fn query(&self) -> impl Parser<'a, I, Query, Err<'a>> + Clone + '_ {
        // TODO: better recovery

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
                .or(predicate.map(AlternationItem::Predicate))
                .repeated()
                .collect()
                .delimited_by(just(Token::LBracket), just(Token::RBracket))
                .map(PatternData::Alternation)
                .labelled("alternation");

            let group = pattern
                .clone()
                .map(GroupItem::Pattern)
                .or(predicate.map(GroupItem::Predicate))
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

                let node_name = ident.labelled("node name");

                let field_name = ident.labelled("field name");

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
                                predicate.map(NamedNodeItem::Predicate),
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

        choice((
            pattern.map(QueryItem::Pattern),
            predicate.map(QueryItem::Predicate),
        ))
        .repeated()
        .at_least(1)
        .collect::<Vec<QueryItem>>()
        .slice()
        .validate(|tokens: &[(Token, SimpleSpan)], span, emitter| {
            /*let text = tokens
            .iter()
            .map(|(t, _)| t.to_string())
            .intersperse(" ".to_string())
            .collect::<String>();*/

            let range = tokens.first().unwrap().1.start..tokens.last().unwrap().1.end;
            let text = &self.source[range];

            TsQuery::new(self.language, text)
                .map(|_| Query::Query(self.language, text.to_string()))
                .unwrap_or_else(|e| {
                    emitter.emit(Rich::custom(span, format!("malformatted query: {}", e)));
                    Query::Invalid
                })
        })
        .recover_with(via_parser(nested_delimiters(
            Token::LParen,
            Token::RParen,
            [(Token::LBracket, Token::RBracket)],
            |_| Query::Invalid,
        )))
        .recover_with(via_parser(nested_delimiters(
            Token::LBracket,
            Token::RBracket,
            [(Token::LParen, Token::RParen)],
            |_| Query::Invalid,
        )))
        .recover_with(skip_until(
            any().ignored(),
            one_of([Token::RParen, Token::RBracket]).ignored(),
            || Query::Invalid,
        ))
    }

    fn remove() -> impl Parser<'a, I, Remove, Err<'a>> + Clone {
        group((
            just(Token::Remove).ignored(),
            Self::capture()
                .map(ToString::to_string)
                .labelled("capture reference"),
        ))
        .map(|(_, capture_name)| Remove { capture_name })
    }

    fn insert() -> impl Parser<'a, I, Insert, Err<'a>> + Clone {
        group((
            just(Token::Insert).ignored(),
            choice((
                just(Token::After).to(InsertLocation::After),
                just(Token::Before).to(InsertLocation::Before),
            )),
            Self::capture()
                .map(ToString::to_string)
                .labelled("capture reference"),
            Self::string_expression().labelled("insertion"),
        ))
        .map(|(_, location, capture_name, insertion)| Insert {
            location,
            capture_name,
            insertion,
        })
    }

    fn match_action() -> impl Parser<'a, I, MatchAction, Err<'a>> + Clone {
        choice((
            Self::replacement()
                .labelled("replacement")
                .map(MatchAction::Replace),
            Self::warning().labelled("warning").map(MatchAction::Warn),
            Self::remove().labelled("remove").map(MatchAction::Remove),
            Self::insert().labelled("insert").map(MatchAction::Insert),
        ))
    }

    fn equals_expr() -> impl Parser<'a, I, EqualsExpr, Err<'a>> + Clone {
        group((
            Self::string_expression().labelled("left"),
            just(Token::Equals).ignored(),
            Self::string_expression().labelled("right"),
        ))
        .map(|(left, _, right)| EqualsExpr { left, right })
    }

    fn contains_expr(&self) -> impl Parser<'a, I, ContainsExpr, Err<'a>> + Clone + '_ {
        group((
            Self::capture()
                .map(ToString::to_string)
                .labelled("capture name"),
            just(Token::Contains).ignored(),
            self.query().labelled("query"),
        ))
        .map(|(capture_name, _, query)| ContainsExpr {
            capture_name,
            query,
        })
    }

    fn where_expr(&self) -> impl Parser<'a, I, WhereExpr, Err<'a>> + Clone + '_ {
        recursive(|where_expr| {
            let atom = choice((
                Self::equals_expr().map(WhereExpr::Equals),
                self.contains_expr().map(WhereExpr::Contains),
                where_expr.delimited_by(just(Token::LParen), just(Token::RParen)),
            ));

            let not = just(Token::Not)
                .repeated()
                .foldr(atom, |_, expr| WhereExpr::Not(NotExpr(Box::new(expr))));

            let and =
                not.clone()
                    .foldl(just(Token::And).then(not).repeated(), |left, (_, right)| {
                        WhereExpr::And(AndExpr {
                            left: Box::new(left),
                            right: Box::new(right),
                        })
                    });

            let or = and
                .clone()
                .foldl(just(Token::Or).then(and).repeated(), |left, (_, right)| {
                    WhereExpr::Or(OrExpr {
                        left: Box::new(left),
                        right: Box::new(right),
                    })
                });

            #[allow(clippy::let_and_return)]
            or
        })
    }

    fn match_clause(&self) -> impl Parser<'a, I, MatchClause, Err<'a>> + Clone + '_ {
        choice((just(Token::Where)
            .ignore_then(self.where_expr())
            .labelled("where")
            .map(MatchClause::Where),))
    }

    fn match_(&self) -> impl Parser<'a, I, Match, Err<'a>> + Clone + '_ {
        group((
            just(Token::Match).ignored(),
            self.query().labelled("query"),
            self.match_clause()
                .repeated()
                .collect()
                .labelled("extra clauses"),
            Self::match_action().labelled("action"),
        ))
        .map(|(_, query, clauses, action)| Match {
            query,
            clauses,
            action,
        })
    }

    fn statement(&self) -> impl Parser<'a, I, Statement, Err<'a>> + Clone + '_ {
        self.match_()
            .then_ignore(just(Token::Semicolon))
            .map(Statement::Match)
            .recover_with(skip_until(
                any().ignored(),
                just(Token::Semicolon).ignored(),
                || Statement::Invalid,
            ))
    }

    fn script(&self) -> impl Parser<'a, I, Script, Err<'a>> + Clone + '_ {
        self.statement()
            .repeated()
            .collect()
            .then_ignore(end())
            .map(|statements| Script { statements })
    }
}

impl Parsable for Script {
    fn parse(source: &str, language: Language) -> (Option<Script>, Vec<Report>) {
        let parser = DslParser {
            source,
            language,
            marker: Default::default(),
        };

        let mut reports = vec![];

        let tokens: Vec<_> = run_lexer(source)
            .into_iter()
            .filter_map(|(result, span)| match result {
                Ok(token) => Some((token, span)),
                Result::Err(e) => {
                    reports.push(miette!(
                        severity = Severity::Error,
                        code = "tree_surgeon::dsl::lexer",
                        "{}",
                        e
                    ));
                    None
                }
            })
            .collect();

        let eoi = SimpleSpan::new(source.len(), source.len());

        let token_input = tokens.as_slice().spanned(eoi);

        let (script, parse_errs) = parser.script().parse(token_input).into_output_errors();

        let parse_reports = parse_errs
            .into_iter()
            .map(|e| {
                e.map_token(|tok| {
                    let mut s = String::new();
                    s.write_fmt(format_args!("{:?}", tok))
                        .expect("Debug implementation failed");
                    s
                })
            })
            .map(|e| {
                let span = e.span();

                miette!(
                    severity = Severity::Error,
                    code = "tree_surgeon::dsl::parse",
                    labels = [LabeledSpan::new(
                        Some(e.reason().to_string()),
                        span.start,
                        span.end - span.start
                    )],
                    "{}",
                    e,
                )
            });
        reports.extend(parse_reports);

        if reports.is_empty() {
            (script, reports)
        } else {
            (None, reports)
        }
    }
}

#[rstest]
#[case(
    r#"match (translation_unit (declaration declarator: (init_declarator)) @decl) warn @decl "Global variable detected";
    match (translation_unit (preproc_ifdef (declaration declarator: (init_declarator)) @decl)) warn @decl "Global variable detected";"#,
    tree_sitter_c::language(),
    (
        Some(Script {
                statements: vec![
                    Statement::Match(Match {
                        query: Query::Query(tree_sitter_c::language(), "(translation_unit (declaration declarator: (init_declarator)) @decl)".to_string()),
                        clauses: vec![],
                        action: MatchAction::Warn(Warn {
                            capture_name: "decl".to_string(),
                            message: StringExpression::Literal("Global variable detected".to_string()),
                        }),
                    }),
                    Statement::Match(Match {
                        query: Query::Query(tree_sitter_c::language(), "(translation_unit (preproc_ifdef (declaration declarator: (init_declarator)) @decl))".to_string()),
                        clauses: vec![],
                        action: MatchAction::Warn(Warn {
                            capture_name: "decl".to_string(),
                            message: StringExpression::Literal("Global variable detected".to_string()),
                        }),
                    }),
                ],
        }),
        vec![]
    ),
)]
fn test_script(
    #[case] source: &str,
    #[case] language: Language,
    #[case] expected: (Option<Script>, Vec<Report>),
) {
    let (expected_script, expected_reports) = expected;
    let (actual_script, actual_reports) = Script::parse(source, language);

    similar_asserts::assert_eq!(actual_script, expected_script);
    assert_eq!(actual_reports.len(), expected_reports.len());
}

#[allow(unused_imports)]
mod proptests {
    use proptest::prelude::*;

    use crate::{
        dsl::ast::Script,
        parser::{lexer::Token, Parsable},
    };

    proptest! {
        #[test]
        fn doesnt_crash(source in ".*") {
            Script::parse(source.as_str(), tree_sitter_c::language());
        }
    }
}

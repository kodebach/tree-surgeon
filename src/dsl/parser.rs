use std::fmt;

use ariadne::{Color, Fmt, Label, Report, ReportKind};

use chumsky::{prelude::*, text::Character, Stream};
use strum::IntoEnumIterator;
use tree_sitter::{Language, Query as TsQuery};

use super::ast::{
    CaptureExpr, Case, JoinItem, Match, Replace, Replacement, Script, Span, Statement,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Token {
    Str(Str),
    Num(String),
    Ident(Ident),
    Capture(Capture),
    PredicateName(PredicateName),
    Keyword(Keyword),
    Ctrl(char),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Str(s) => s.fmt(f),
            Token::Capture(c) => c.fmt(f),
            Token::PredicateName(p) => p.fmt(f),
            Token::Num(num) => write!(f, "{}", num),
            Token::Ident(ident) => ident.fmt(f),
            Token::Keyword(keyword) => match keyword {
                Keyword::Match => write!(f, "match"),
                Keyword::Replace => write!(f, "replace"),
                Keyword::With => write!(f, "with"),
                Keyword::By => write!(f, "by"),
            },
            Token::Ctrl(c) => write!(f, "{}", c),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Keyword {
    Match,
    Replace,
    With,
    By,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Str(String);

impl fmt::Display for Str {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{}\"", self.0.escape_default())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Capture(String);

impl fmt::Display for Capture {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct PredicateName(String);

impl fmt::Display for PredicateName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, derive_more::Display)]
struct Ident(String);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum PredicateArg {
    Capture(Capture),
    Str(Str),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Quantifier {
    OneOrMore,
    ZeroOrOne,
    ZeroOrMore,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Predicate(PredicateName, Vec<PredicateArg>);

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        self.0.fmt(f)?;
        for arg in &self.1 {
            write!(f, " ")?;
            match arg {
                PredicateArg::Capture(c) => c.fmt(f)?,
                PredicateArg::Str(s) => s.fmt(f)?,
            }
        }
        write!(f, ")")
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum AlternationItem {
    Choice(Pattern),
    Predicate(Predicate),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum GroupItem {
    Pattern(Pattern),
    Predicate(Predicate),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Anchor;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct AnchoredNamedNodeItem(Option<Anchor>, NamedNodeItem);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum NamedNodeItem {
    Child(Option<Ident>, Pattern),
    NegatedChild(Ident),
    Predicate(Predicate),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Pattern(PatternData, Option<Quantifier>, Option<Capture>);

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)?;
        if let Some(q) = &self.1 {
            match q {
                Quantifier::OneOrMore => write!(f, "+")?,
                Quantifier::ZeroOrOne => write!(f, "?")?,
                Quantifier::ZeroOrMore => write!(f, "*")?,
            }
        }
        if let Some(c) = &self.2 {
            write!(f, " ")?;
            c.fmt(f)
        } else {
            Ok(())
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum PatternData {
    Alternation(Vec<AlternationItem>),
    AnonymousLeaf(Str),
    Group(Vec<GroupItem>),
    NamedNode(Ident, Vec<AnchoredNamedNodeItem>, Option<Anchor>),
    WildcardNode,
}

impl fmt::Display for PatternData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatternData::Alternation(items) => {
                write!(f, "(")?;
                for (idx, item) in items.iter().enumerate() {
                    if idx > 0 {
                        write!(f, " ")?;
                    }
                    match item {
                        AlternationItem::Choice(c) => c.fmt(f)?,
                        AlternationItem::Predicate(p) => p.fmt(f)?,
                    }
                }
                write!(f, ")")
            }
            PatternData::AnonymousLeaf(s) => s.fmt(f),
            PatternData::Group(items) => {
                write!(f, "(")?;
                for (idx, item) in items.iter().enumerate() {
                    if idx > 0 {
                        write!(f, " ")?;
                    }
                    match item {
                        GroupItem::Pattern(p) => p.fmt(f)?,
                        GroupItem::Predicate(p) => p.fmt(f)?,
                    }
                }
                write!(f, ")")
            }
            PatternData::NamedNode(name, items, anchor) => {
                write!(f, "(")?;
                name.fmt(f)?;
                for item in items {
                    write!(f, " ")?;

                    if let Some(_) = item.0 {
                        write!(f, ".")?;
                    }
                    match &item.1 {
                        NamedNodeItem::Child(field_name, pattern) => {
                            if let Some(field_name) = field_name {
                                field_name.fmt(f)?;
                                write!(f, ": ")?;
                            }
                            pattern.fmt(f)?;
                        }
                        NamedNodeItem::NegatedChild(field_name) => {
                            write!(f, "!")?;
                            field_name.fmt(f)?;
                        }
                        NamedNodeItem::Predicate(p) => p.fmt(f)?,
                    }
                    if let Some(_) = anchor {
                        write!(f, ".")?;
                    }
                }
                write!(f, ")")
            }
            PatternData::WildcardNode => write!(f, "_"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum QueryItem {
    Pattern(Pattern),
    Predicate(Predicate),
    Invalid,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Query(Vec<QueryItem>);

impl fmt::Display for Query {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (idx, item) in self.0.iter().enumerate() {
            if idx > 0 {
                write!(f, " ")?;
            }
            match item {
                QueryItem::Pattern(p) => p.fmt(f),
                QueryItem::Predicate(p) => p.fmt(f),
                QueryItem::Invalid => unreachable!("should only happen in error branch"),
            }?
        }
        Ok(())
    }
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
        .map(Str)
        .map(Token::Str)
        .labelled("string");

    let ctrl = one_of(";()[]:.+?!$").map(Token::Ctrl);

    let keyword = choice((
        just("match").to(Keyword::Match).labelled("match"),
        just("replace").to(Keyword::Replace).labelled("replace"),
        just("by").to(Keyword::By).labelled("by"),
        just("with").to(Keyword::With).labelled("with"),
    ))
    .labelled("keyword")
    .map(Token::Keyword);

    let capture = just("@")
        .ignore_then(
            filter(|c: &char| {
                !c.is_whitespace() && *c != '(' && *c != ')' && *c != '[' && *c != ']' && *c != '$'
            })
            .repeated(),
        )
        .collect::<String>()
        .map(Capture)
        .labelled("capture")
        .map(Token::Capture);

    let predicate_name = just("#")
        .ignore_then(
            filter(|c: &char| {
                !c.is_whitespace() && *c != '(' && *c != ')' && *c != '[' && *c != ']'
            })
            .repeated(),
        )
        .collect::<String>()
        .map(PredicateName)
        .labelled("predicate name")
        .map(Token::PredicateName);

    let ident = filter(|c: &char| c.is_ascii_alphanumeric() || *c == '_' || *c == '-')
        .then(
            filter(|c: &char| {
                c.is_ascii_alphanumeric()
                    || *c == '_'
                    || *c == '-'
                    || *c == '?'
                    || *c == '!'
                    || *c == '.'
            })
            .repeated()
            .or_not(),
        )
        .map(|(first, rest)| {
            let mut chars = rest.unwrap_or_default();
            chars.insert(0, first);
            chars.iter().collect()
        })
        .map(Ident)
        .labelled("identifier")
        .map(Token::Ident);

    let num = {
        let frac = just('.').chain(text::digits(10));

        let exp = just('e')
            .or(just('E'))
            .chain(just('+').or(just('-')).or_not())
            .chain(text::digits(10));

        just('-')
            .or_not()
            .chain(text::int(10))
            .chain(frac.or_not().flatten())
            .chain::<char, _, _>(exp.or_not().flatten())
            .collect::<String>()
            .map(Token::Num)
            .labelled("number")
    };

    let token = keyword
        .or(ctrl)
        .or(string)
        .or(capture)
        .or(predicate_name)
        .or(num)
        .or(ident)
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
    fn replacement(&self) -> impl Parser<Token, Replace, Error = Simple<Token>> + Clone {
        let capture = filter_map(|span, tok| match tok {
            Token::Capture(name) => Ok(name.clone()),
            _ => Err(Simple::expected_input_found(
                span,
                vec![Some(Token::Capture(Capture(String::from("_"))))],
                Some(tok),
            )),
        });

        let str_ = filter_map(|span, tok| match tok {
            Token::Str(str_) => Ok(str_.clone()),
            _ => Err(Simple::expected_input_found(
                span,
                vec![Some(Token::Str(Str(String::from("_"))))],
                Some(tok),
            )),
        });

        let literal_replace = just(Token::Keyword(Keyword::With))
            .then(str_.labelled("replacement literal"))
            .map(|(_, literal)| Replacement::Literal(literal.0));

        let recase_ident = filter_map(move |span, tok| match tok {
            Token::Ident(ident) => Ok(ident.0),
            _ => Err(Simple::expected_input_found(
                span,
                Case::iter().map(|case| Some(Token::Ident(Ident(case.as_ref().to_owned())))),
                Some(tok),
            )),
        })
        .from_str::<Case>()
        .try_map(|res, span| res.map_err(|e| Simple::custom(span, e.to_string())));

        let recase_suffix = just(Token::Ctrl('$'))
            .then(recase_ident)
            .map(|(_, case)| case)
            .labelled("recase suffix");

        let index = filter_map(|span, tok| match tok {
            Token::Num(ref num) => num
                .parse::<usize>()
                .map_err(|e| Simple::custom(span, e.to_string())),
            _ => Err(Simple::expected_input_found(
                span,
                vec![Some(Token::Num(String::from("123")))],
                Some(tok),
            )),
        })
        .labelled("index");

        let range_suffix = index
            .or_not()
            .then(just(Token::Ctrl(':')))
            .then(index.or_not())
            .delimited_by(just(Token::Ctrl('[')), just(Token::Ctrl(']')))
            .labelled("index range");

        let capture_expr = capture
            .then(recase_suffix.or_not())
            .then(range_suffix.or_not());

        let join_replace = just(Token::Keyword(Keyword::By))
            .then(
                choice((
                    str_.map(|str| JoinItem::Literal(str.0)),
                    capture_expr.map(|((capture, case), range)| {
                        if let Some(((from, _), to)) = range {
                            JoinItem::CaptureExpr(CaptureExpr::new(capture.0, case, Some(from..to)))
                        } else {
                            JoinItem::CaptureExpr(CaptureExpr::new(capture.0, case, None))
                        }
                    }),
                ))
                .repeated()
                .delimited_by(just(Token::Ctrl('[')), just(Token::Ctrl(']')))
                .labelled("replacement expression"),
            )
            .map(|(_, items)| Replacement::Join(items));

        just(Token::Keyword(Keyword::Replace))
            .then(capture.labelled("capture reference"))
            .then(choice((literal_replace, join_replace)))
            .map(|((_, capture), replacement)| Replace::new(capture.0, replacement))
    }

    fn query(&self) -> impl Parser<Token, Query, Error = Simple<Token>> + Clone {
        let capture = filter_map(|span, tok| match tok {
            Token::Capture(c) => Ok(c),
            _ => Err(Simple::expected_input_found(
                span,
                vec![Some(Token::Capture(Capture(String::from("_"))))],
                Some(tok),
            )),
        })
        .labelled("capture");

        let string = filter_map(|span, tok| match tok {
            Token::Str(s) => Ok(s),
            _ => Err(Simple::expected_input_found(
                span,
                vec![Some(Token::Str(Str(String::from("_"))))],
                Some(tok),
            )),
        })
        .labelled("string");

        let predicate = {
            let predicate_name = filter_map(|span, tok| match tok {
                Token::PredicateName(p) => Ok(p),
                _ => Err(Simple::expected_input_found(
                    span,
                    vec![Some(Token::PredicateName(PredicateName(String::from("_"))))],
                    Some(tok),
                )),
            })
            .labelled("predicate name");

            predicate_name
                .then(
                    capture
                        .map(PredicateArg::Capture)
                        .or(string.map(PredicateArg::Str))
                        .repeated()
                        .or_not()
                        .map(|v| v.unwrap_or_default()),
                )
                .map(|(n, a)| Predicate(n, a))
                .labelled("predicate")
        };

        let pattern = recursive(|pattern| {
            let quantifier = filter_map(|span, tok| match tok {
                Token::Ctrl(c) => match &c {
                    '+' => Ok(Quantifier::OneOrMore),
                    '?' => Ok(Quantifier::ZeroOrOne),
                    '*' => Ok(Quantifier::ZeroOrMore),
                    _ => Err(Simple::expected_input_found(
                        span,
                        vec![
                            Some(Token::Ctrl('+')),
                            Some(Token::Ctrl('?')),
                            Some(Token::Ctrl('*')),
                        ],
                        Some(tok),
                    )),
                },
                _ => Err(Simple::expected_input_found(
                    span,
                    vec![
                        Some(Token::Ctrl('+')),
                        Some(Token::Ctrl('?')),
                        Some(Token::Ctrl('*')),
                    ],
                    Some(tok),
                )),
            })
            .labelled("quantifier");

            let anonymous_leaf = string
                .map(PatternData::AnonymousLeaf)
                .labelled("anonymous leaf");

            let wildcard_node = choice((
                just(Token::Ctrl('_')).ignored(),
                just([Token::Ctrl('('), Token::Ctrl('_'), Token::Ctrl(')')]).ignored(),
            ))
            .to(PatternData::WildcardNode)
            .labelled("wildcard node");

            let alternation = pattern
                .clone()
                .map(AlternationItem::Choice)
                .or(predicate.clone().map(AlternationItem::Predicate))
                .repeated()
                .delimited_by(just(Token::Ctrl('[')), just(Token::Ctrl(']')))
                .map(PatternData::Alternation)
                .labelled("alternation");

            let group = pattern
                .clone()
                .map(GroupItem::Pattern)
                .or(predicate.clone().map(GroupItem::Predicate))
                .repeated()
                .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
                .map(PatternData::Group)
                .labelled("group");

            let named_node = {
                let ident = filter_map(|span, tok| match tok {
                    Token::Ident(i) => Ok(i),
                    _ => Err(Simple::expected_input_found(
                        span,
                        vec![Some(Token::Ident(Ident(String::from("_"))))],
                        Some(tok),
                    )),
                });

                let node_name = ident.clone().labelled("node name");

                let field_name = ident.clone().labelled("field name");

                let anchor = just(Token::Ctrl('.')).to(Anchor).labelled("anchor");

                let child = field_name
                    .then_ignore(just(Token::Ctrl(':')))
                    .or_not()
                    .then(pattern.clone())
                    .map(|(i, p)| NamedNodeItem::Child(i, p))
                    .labelled("child");

                let negated_child = just(Token::Ctrl('!'))
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
                            .map(|(a, i)| AnchoredNamedNodeItem(a, i))
                            .repeated()
                            .then(anchor.clone().or_not()),
                    )
                    .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
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
            .map(|((p, q), c)| Pattern(p, q, c))
            .labelled("pattern")
        });

        pattern
            .map(QueryItem::Pattern)
            .or(predicate.map(QueryItem::Predicate))
            .recover_with(nested_delimiters(
                Token::Ctrl('('),
                Token::Ctrl(')'),
                [(Token::Ctrl('['), Token::Ctrl(']'))],
                |_| QueryItem::Invalid,
            ))
            .recover_with(nested_delimiters(
                Token::Ctrl('['),
                Token::Ctrl(']'),
                [(Token::Ctrl('('), Token::Ctrl(')'))],
                |_| QueryItem::Invalid,
            ))
            .repeated()
            .or_not()
            .map(|items| Query(items.unwrap_or_default()))
            .labelled("query")
    }

    fn match_<'a>(
        &'a self,
    ) -> impl Parser<Token, Option<Match>, Error = Simple<Token>> + Clone + 'a {
        just(Token::Keyword(Keyword::Match))
            .then(
                self.query()
                    .validate(|query, span, emit| {
                        if query.0.iter().any(|item| item == &QueryItem::Invalid) {
                            emit(Simple::custom(span, "malformatted query"));
                            None
                        } else {
                            TsQuery::new(self.language, &query.to_string())
                                .map(Some)
                                .unwrap_or_else(|e| {
                                    emit(Simple::custom(
                                        span,
                                        format!("malformatted query: {}", e),
                                    ));
                                    None
                                })
                        }
                    })
                    .labelled("query"),
            )
            .then(self.replacement().labelled("replacement"))
            .map(|((_, query), replacement)| query.map(|query| Match::new(query, replacement)))
    }

    fn statement<'a>(
        &'a self,
    ) -> impl Parser<Token, Statement, Error = Simple<Token>> + Clone + 'a {
        self.match_()
            .then_ignore(just(Token::Ctrl(';')))
            .validate(|m, span, emit| {
                m.map(|m| Statement::Match(m)).unwrap_or_else(|| {
                    emit(Simple::custom(span, "invalid match"));
                    Statement::Invalid
                })
            })
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

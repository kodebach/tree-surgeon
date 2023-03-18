use std::{fmt, marker::PhantomData};

use ariadne::{Color, Label, Report, ReportKind};

use chumsky::{
    input::{Stream, ValueInput},
    prelude::*,
};
use tree_sitter::{Language, Query as TsQuery};

use super::ast::{
    CaptureExpr, Case, JoinItem, Match, MatchAction, Replace, Script, Spanned, Statement,
    StringExpression, Warn,
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
    Comment,
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
                Keyword::Warn => write!(f, "warn"),
                Keyword::With => write!(f, "with"),
                Keyword::By => write!(f, "by"),
            },
            Token::Ctrl(c) => write!(f, "{}", c),
            Token::Comment => Ok(()),
        }
    }
}

trait TokenInput<'a>: ValueInput<'a, Token = Token, Span = SimpleSpan> {}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Keyword {
    Match,
    Replace,
    Warn,
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
    Ident(Ident),
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
                PredicateArg::Ident(i) => i.fmt(f)?,
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
    fn parse<'a, 'b>(
        source: &'a str,
        language: Language,
        config: ariadne::Config,
    ) -> (Option<Script>, Vec<Report<'b>>);
}

fn lexer<'a>() -> impl Parser<'a, &'a str, Vec<Spanned<Token>>, extra::Err<Rich<'a, char>>> {
    let escape = just('\\')
        .then(choice((
            just('\\'),
            just('/'),
            just('"'),
            just('b').to('\x08'),
            just('f').to('\x0C'),
            just('n').to('\n'),
            just('r').to('\r'),
            just('t').to('\t'),
            just('u').ignore_then(text::digits(16).exactly(4).slice().validate(
                |digits, span, emitter| {
                    char::from_u32(u32::from_str_radix(digits, 16).unwrap()).unwrap_or_else(|| {
                        emitter.emit(Rich::custom(span, "invalid unicode character"));
                        '\u{FFFD}' // unicode replacement character
                    })
                },
            )),
        )))
        .ignored();

    let string = none_of(r#"\""#)
        .ignored()
        .or(escape)
        .repeated()
        .slice()
        .map(ToString::to_string)
        .delimited_by(just('"'), just('"'))
        .map(Str)
        .map(Token::Str)
        .labelled("string");

    let ctrl = one_of(";()[]:.+?!$").map(Token::Ctrl);

    let keyword = choice((
        just("match").to(Keyword::Match).labelled("match"),
        just("replace").to(Keyword::Replace).labelled("replace"),
        just("warn").to(Keyword::Warn).labelled("warn"),
        just("by").to(Keyword::By).labelled("by"),
        just("with").to(Keyword::With).labelled("with"),
    ))
    .labelled("keyword")
    .map(Token::Keyword);

    const SPECIAL_CHARS: &str = "()[]$.";

    let capture = just("@")
        .ignore_then(
            any()
                .filter(|c: &char| !c.is_whitespace() && !SPECIAL_CHARS.contains(*c))
                .repeated()
                .map_slice(|c: &str| Capture(c.to_string())),
        )
        .labelled("capture")
        .map(Token::Capture);

    let predicate_name = just("#")
        .ignore_then(
            any()
                .filter(|c: &char| !c.is_whitespace() && !SPECIAL_CHARS.contains(*c))
                .repeated()
                .map_slice(|c: &str| PredicateName(c.to_string())),
        )
        .labelled("predicate name")
        .map(Token::PredicateName);

    let ident = any()
        .filter(|c: &char| c.is_ascii_alphanumeric() || *c == '_' || *c == '-')
        .then(
            any()
                .filter(|c: &char| {
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
        .map_slice(|i: &str| Ident(i.to_string()))
        .labelled("identifier")
        .map(Token::Ident);

    let num = {
        let digits = text::digits(10).slice();

        let frac = just('.').then(digits.clone());

        let exp = one_of("eE")
            .then(one_of("+-").or_not())
            .then(digits.clone());

        just('-')
            .or_not()
            .then(text::int(10))
            .then(frac.or_not())
            .then(exp.or_not())
            .map_slice(|n: &str| Token::Num(n.to_string()))
            .labelled("number")
    };

    let comment = just("--")
        .then(any().and_is(just('\n').not()).repeated())
        .padded();

    let token = choice((keyword, ctrl, string, capture, predicate_name, num, ident));

    token
        .map_with_span(|tok, span| (tok, span))
        .padded_by(comment.repeated())
        .padded()
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}

struct DslParser<'a, I>
where
    I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
    language: Language,
    marker: PhantomData<&'a I>,
}

type Err<'a> = extra::Err<Rich<'a, Token>>;

impl<'a, I> DslParser<'a, I>
where
    I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
    fn capture() -> impl Parser<'a, I, Capture, Err<'a>> + Clone {
        select! {
            Token::Capture(name) => name.clone()
        }
    }

    fn string_literal() -> impl Parser<'a, I, String, Err<'a>> + Clone {
        select! {
            Token::Str(str_) => str_.clone(),
        }
        .map(|str| str.0)
    }

    fn ident() -> impl Parser<'a, I, Ident, Err<'a>> + Clone {
        select! {
            Token::Ident(ident) => ident,
        }
    }

    fn num() -> impl Parser<'a, I, isize, Err<'a>> + Clone {
        select! {
            Token::Num(n) => n,
        }
        .try_map(|n, span| {
            n.parse::<isize>()
                .map_err(|e| Rich::custom(span, e.to_string()))
        })
    }

    fn join_expr() -> impl Parser<'a, I, Vec<JoinItem>, Err<'a>> + Clone {
        let recase_ident = Self::ident()
            .map(|i| i.0)
            .from_str::<Case>()
            .try_map(|res, span| res.map_err(|e| Rich::custom(span, e.to_string())));

        let recase_suffix = just(Token::Ctrl('$'))
            .ignore_then(recase_ident)
            .labelled("recase suffix");

        let index = Self::num().labelled("index");

        let range_suffix = index
            .clone()
            .or_not()
            .then_ignore(just(Token::Ctrl(':')))
            .then(index.clone().or_not())
            .delimited_by(just(Token::Ctrl('[')), just(Token::Ctrl(']')))
            .labelled("index range");

        let capture_expr = Self::capture()
            .then(recase_suffix.or_not())
            .then(range_suffix.or_not());

        choice((
            Self::string_literal().map(JoinItem::Literal),
            capture_expr.map(|((capture, case), range)| {
                if let Some((from, to)) = range {
                    JoinItem::CaptureExpr(CaptureExpr::new(capture.0, case, Some(from..to)))
                } else {
                    JoinItem::CaptureExpr(CaptureExpr::new(capture.0, case, None))
                }
            }),
        ))
        .repeated()
        .collect()
        .delimited_by(just(Token::Ctrl('[')), just(Token::Ctrl(']')))
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
        just(Token::Keyword(Keyword::Replace))
            .ignore_then(Self::capture().labelled("capture reference").map(|c| c.0))
            .then(choice((
                just(Token::Keyword(Keyword::With))
                    .ignore_then(Self::string_literal())
                    .map(StringExpression::Literal),
                just(Token::Keyword(Keyword::By)).ignore_then(Self::string_expression()),
            )))
            .map(|(capture, replacement)| Replace::new(capture, replacement))
    }

    fn warning() -> impl Parser<'a, I, Warn, Err<'a>> + Clone {
        just(Token::Keyword(Keyword::Warn))
            .ignore_then(Self::capture().labelled("capture reference").map(|c| c.0))
            .then(Self::string_expression())
            .map(|(capture, string_expr)| Warn::new(capture, string_expr))
    }

    fn query() -> impl Parser<'a, I, Query, Err<'a>> + Clone {
        let capture = select! {
            Token::Capture(c) => c
        }
        .labelled("capture");

        let string = select! {
            Token::Str(s) => s,
        }
        .labelled("string");

        let predicate = {
            let predicate_name = select! {
                Token::PredicateName(p) => p,
            }
            .labelled("predicate name");

            let ident = select! {
                Token::Ident(ident) => ident,
            }
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
                .map(|(n, a)| Predicate(n, a))
                .labelled("predicate")
        };

        let pattern = recursive(|pattern| {
            let quantifier = select! {
                Token::Ctrl(c) if c == '+' => Quantifier::OneOrMore,
                Token::Ctrl(c) if c == '?' => Quantifier::ZeroOrOne,
                Token::Ctrl(c) if c == '*' => Quantifier::ZeroOrMore,
            }
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
                .collect()
                .delimited_by(just(Token::Ctrl('[')), just(Token::Ctrl(']')))
                .map(PatternData::Alternation)
                .labelled("alternation");

            let group = pattern
                .clone()
                .map(GroupItem::Pattern)
                .or(predicate.clone().map(GroupItem::Predicate))
                .repeated()
                .collect()
                .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
                .map(PatternData::Group)
                .labelled("group");

            let named_node = {
                let ident = select! {
                    Token::Ident(i) => i
                };

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
                            .collect()
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
            .recover_with(via_parser(nested_delimiters(
                Token::Ctrl('('),
                Token::Ctrl(')'),
                [(Token::Ctrl('['), Token::Ctrl(']'))],
                |_| QueryItem::Invalid,
            )))
            .recover_with(via_parser(nested_delimiters(
                Token::Ctrl('['),
                Token::Ctrl(']'),
                [(Token::Ctrl('('), Token::Ctrl(')'))],
                |_| QueryItem::Invalid,
            )))
            .repeated()
            .collect()
            .map(Query)
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
        just(Token::Keyword(Keyword::Match))
            .ignore_then(
                Self::query()
                    .validate(|query, span, emitter| {
                        if query.0.iter().any(|item| item == &QueryItem::Invalid) {
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
            .then_ignore(just(Token::Ctrl(';')))
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
        let (tokens, errs) = lexer().parse(source).into_output_errors();

        let (script, parse_errs) = if let Some(tokens) = tokens {
            let parser = DslParser {
                language,
                marker: Default::default(),
            };

            let token_iter = tokens
                .into_iter()
                .filter(|(token, _)| !matches!(token, Token::Comment));

            let token_stream =
                Stream::from_iter(token_iter).spanned((source.len()..source.len()).into());

            let (ast, parse_errs) = parser.script().parse(token_stream).into_output_errors();

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
            .map(|e| e.map_token(|c| c.to_string()))
            .chain(
                parse_errs
                    .into_iter()
                    .map(|e| e.map_token(|tok| tok.to_string())),
            )
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

        (script, reports)
    }
}

use chumsky::{span::SimpleSpan};
use logos::{Lexer, Logos};

#[derive(Debug, PartialEq, Clone, Default, thiserror::Error)]
pub enum TokenError {
    #[error("invalid string")]
    InvalidString(#[from] StringError),
    #[default]
    #[error("unknown error")]
    Other,
}

#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"\s+", error = TokenError)]
pub enum Token<'a> {
    #[regex(r"-?[[:digit:]]+(\.[[:digit:]]+)?([eE][+-]?[[:digit:]]+)?", priority = 2, callback = |lex| lex.slice())]
    Number(&'a str),
    #[regex(
        r#""([^"\\]|\\[\\/"bfnrt]|\\u[[:xdigit:]][[:xdigit:]][[:xdigit:]][[:xdigit:]])*""#,
        parse_string
    )]
    String(String),
    #[regex(r"[-_[:alpha:]][-_?!.[:alnum:]]*", |lex| lex.slice())]
    Identifier(&'a str),
    #[regex(r"@[-_[:alpha:]]?[-_?!.[:alnum:]]*", |lex| &lex.slice()[1..])]
    Capture(&'a str),
    #[regex(r"#[-_[:alpha:]][-_?!.[:alnum:]]*", |lex| &lex.slice()[1..])]
    PredicateName(&'a str),

    // keywords
    #[token("match")]
    Match,
    #[token("replace")]
    Replace,
    #[token("warn")]
    Warn,
    #[token("with")]
    With,
    #[token("by")]
    By,
    #[token("where")]
    Where,
    #[token("contains")]
    Contains,
    #[token("remove")]
    Remove,
    #[token("insert")]
    Insert,
    #[token("before")]
    Before,
    #[token("after")]
    After,
    #[token("and")]
    And,
    #[token("or")]
    Or,
    #[token("not")]
    Not,

    // control chars
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("$")]
    Dollar,
    #[token(":")]
    Colon,
    #[token("+")]
    Plus,
    #[token("*")]
    Asterisk,
    #[token("?")]
    QuestionMark,
    #[token("_")]
    Underscore,
    #[token(".")]
    Dot,
    #[token("!")]
    Bang,
    #[token(";")]
    Semicolon,
    #[token("=")]
    Equals,

    #[regex(r"--.*\r?\n", logos::skip)]
    Comment,
}

fn parse_string<'a>(lexer: &mut Lexer<'a, Token<'a>>) -> Result<String, TokenError> {
    let s = lexer.slice();
    StringToken::lexer(&s[1..s.len() - 1])
        .map(|result| {
            result
                .map(|t| match t {
                    StringToken::Escape(c) => c,
                    StringToken::Unicode(c) => c,
                    StringToken::Other(c) => c,
                })
                .map_err(TokenError::InvalidString)
        })
        .collect::<Result<String, _>>()
}

#[derive(Debug, PartialEq, Clone, Default, thiserror::Error)]
pub enum StringError {
    #[error("invalid escape sequence '\\{0}'")]
    InvalidEscape(char),
    #[error("invalid unicode codepoint '\\u{0:#04x}'")]
    InvalidUnicode(u32),
    #[default]
    #[error("unknown error")]
    Other,
}

#[derive(Logos, Debug)]
#[logos(error = StringError)]
enum StringToken {
    #[regex(r#"\\[bfnrt\\/"]"#, parse_escape)]
    Escape(char),
    #[regex(
        r#"\\u[[:xdigit:]][[:xdigit:]][[:xdigit:]][[:xdigit:]]"#,
        parse_unicode
    )]
    Unicode(char),
    #[regex(r#"[^"\\]"#, |lex| lex.slice().chars().next())]
    Other(char),
}

fn parse_escape(lexer: &mut Lexer<StringToken>) -> Result<char, StringError> {
    match lexer.slice().chars().nth(1).unwrap() {
        'b' => Ok('\x08'),
        'f' => Ok('\x0C'),
        'n' => Ok('\n'),
        'r' => Ok('\r'),
        't' => Ok('\t'),
        '"' => Ok('\"'),
        '\\' => Ok('\\'),
        '/' => Ok('/'),
        c => Err(StringError::InvalidEscape(c)),
    }
}

fn parse_unicode(lexer: &mut Lexer<StringToken>) -> Result<char, StringError> {
    let codepoint = u32::from_str_radix(&lexer.slice()[2..], 16).unwrap();
    char::from_u32(codepoint).ok_or(StringError::InvalidUnicode(codepoint))
}

type SpannedLexerResult<'a> = Vec<(Result<Token<'a>, TokenError>, SimpleSpan)>;

fn run_lexer_impl(source: &str, filter_comments: bool) -> SpannedLexerResult {
    Token::lexer(source)
        .spanned()
        .filter(|(result, _)| !filter_comments || !matches!(result, Ok(Token::Comment)))
        .map(|(result, span)| (result, SimpleSpan::from(span)))
        .collect::<Vec<_>>()
}

pub fn run_lexer(source: &str) -> SpannedLexerResult {
    run_lexer_impl(source, true)
}

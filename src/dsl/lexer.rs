use std::fmt::Display;

use logos::{Lexer, Logos};

#[derive(Logos, Debug, Clone, PartialEq)]
pub enum Token<'a> {
    #[regex(r"-?[[:digit:]]+(\.[[:digit:]]+)?([eE][+-]?[[:digit]]+)", |lex| lex.slice())]
    Number(&'a str),
    #[regex(
        r#""([^"\\]|\\[\\/"bfnrt]|\\u[[:xdigit:]][[:xdigit:]][[:xdigit:]][[:xdigit:]])*""#,
        parse_string
    )]
    String(String),
    #[regex(r"[-_[:alnum:]][-_?!.[:alnum:]]*", |lex| lex.slice())]
    Identifier(&'a str),
    #[regex(r"@[^()\[\]$.\s]+", |lex| &lex.slice()[1..])]
    Capture(&'a str),
    #[regex(r"#[^()\[\]$.\s]+", |lex| &lex.slice()[1..])]
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

    #[regex(r"--.*\r?\n", logos::skip)]
    Comment,

    #[error]
    #[regex(r"\s+", logos::skip)]
    Error,
}

fn parse_string<'a>(lexer: &mut Lexer<'a, Token<'a>>) -> Option<String> {
    let s = lexer.slice();
    StringToken::lexer(&s[1..s.len() - 1])
        .map(|t| match t {
            StringToken::Escape(c) => Ok(c),
            StringToken::Unicode(c) => Ok(c),
            StringToken::Other(c) => Ok(c),
            StringToken::Error => Err(Token::ERROR),
        })
        .collect::<Result<String, _>>()
        .ok()
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Number(s) => write!(f, "{}", s),
            Token::String(s) => write_string(f, s),
            Token::Identifier(s) => write!(f, "{}", s),
            Token::Capture(s) => write!(f, "@{}", s),
            Token::PredicateName(s) => write!(f, "#{}", s),
            Token::Match => write!(f, "match"),
            Token::Replace => write!(f, "replace"),
            Token::Warn => write!(f, "warn"),
            Token::With => write!(f, "with"),
            Token::By => write!(f, "by"),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::Dollar => write!(f, "$"),
            Token::Colon => write!(f, ":"),
            Token::Plus => write!(f, "+"),
            Token::Asterisk => write!(f, "*"),
            Token::QuestionMark => write!(f, "?"),
            Token::Underscore => write!(f, "_"),
            Token::Dot => write!(f, "."),
            Token::Bang => write!(f, "!"),
            Token::Semicolon => write!(f, ";"),
            Token::Comment => Ok(()),
            Token::Error => Ok(()),
        }
    }
}

fn write_string(f: &mut std::fmt::Formatter<'_>, s: &str) -> std::fmt::Result {
    write!(f, "\"")?;
    for c in s.chars() {
        match c {
            '\x08' => write!(f, "\\t"),
            '\x0C' => write!(f, "\\f"),
            '\n' => write!(f, "\\n"),
            '\r' => write!(f, "\\r"),
            '\t' => write!(f, "\\t"),
            _ if c.is_ascii_graphic() => write!(f, "{}", c),
            _ => write!(f, "{:04x}", c as u32),
        }?
    }
    write!(f, "\"")
}

#[derive(Logos, Debug)]
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

    #[error]
    Error,
}

fn parse_escape(lexer: &mut Lexer<StringToken>) -> Option<char> {
    lexer.slice().chars().nth(1).and_then(|c| match c {
        'b' => Some('\x08'),
        'f' => Some('\x0C'),
        'n' => Some('\n'),
        'r' => Some('\r'),
        't' => Some('\t'),
        '"' => Some('\"'),
        '\\' => Some('\\'),
        '/' => Some('/'),
        _ => None,
    })
}

fn parse_unicode(lexer: &mut Lexer<StringToken>) -> Option<char> {
    u32::from_str_radix(&lexer.slice()[2..], 16)
        .ok()
        .and_then(char::from_u32)
}

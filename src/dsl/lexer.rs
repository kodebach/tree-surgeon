use logos::{Lexer, Logos};

#[derive(Logos, Debug, Clone, PartialEq)]
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

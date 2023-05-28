use chumsky::span::SimpleSpan;
use logos::{Lexer, Logos};
use rstest::rstest;

#[derive(Debug, PartialEq, Clone, Default, thiserror::Error)]
pub enum TokenError {
    #[error("invalid string")]
    InvalidString(#[from] StringError),
    #[default]
    #[error("unknown error")]
    Other,
}

#[derive(Logos, Debug, Clone, PartialEq, Eq)]
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
    #[error("invalid unicode codepoint '\\u{0:04x?}'")]
    InvalidUnicode(u32),
    #[default]
    #[error("unknown error")]
    Other,
}

#[derive(Logos, Debug, PartialEq, Eq)]
#[logos(error = StringError)]
enum StringToken {
    #[regex(r#"\\[bfnrt\\/"]"#, parse_escape)]
    Escape(char),
    #[regex(
        r#"\\u[[:xdigit:]][[:xdigit:]][[:xdigit:]][[:xdigit:]]"#,
        parse_unicode
    )]
    Unicode(char),
    #[regex(r#"[^"\\]"#, parse_other)]
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

fn parse_other(lexer: &mut Lexer<StringToken>) -> char {
    let span = lexer.span();
    let c = lexer.source()[span.start..].chars().next().unwrap();
    lexer.bump(c.len_utf8() - span.len());
    c
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

#[rstest]
#[case(
    "ñ\u{009f}\u{0098}\u{009c}&L}¦�\x0b\x1b$X\x1b%`ð²\u{009e}\u{008c}/RÂ\u{008c}\"ð´¿\u{0081}\x00\r$�dXåó©\u{0098}®\x08&\"}",
    vec![
        Err(TokenError::Other),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Ok(Token::Identifier("L")),
        Ok(Token::RBrace),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Ok(Token::Dollar),
        Ok(Token::Identifier("X")),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Ok(Token::Identifier("R")),
        Err(TokenError::Other),
        Err(TokenError::Other),
        Ok(Token::String("ð´¿\u{0081}\x00\r$�dXåó©\u{0098}®\x08&".to_string())),
        Ok(Token::RBrace),
    ],
)]
#[case(
    r#"match (translation_unit (declaration declarator: (init_declarator)) @decl) warn @decl "Global variable detected";
    match (translation_unit (preproc_ifdef (declaration declarator: (init_declarator)) @decl)) warn @decl "Global variable detected";"#,
    vec![
        Ok(Token::Match),
        Ok(Token::LParen),
        Ok(Token::Identifier("translation_unit")),
        Ok(Token::LParen),
        Ok(Token::Identifier("declaration")),
        Ok(Token::Identifier("declarator")),
        Ok(Token::Colon),
        Ok(Token::LParen),
        Ok(Token::Identifier("init_declarator")),
        Ok(Token::RParen),
        Ok(Token::RParen),
        Ok(Token::Capture("decl")),
        Ok(Token::RParen),
        Ok(Token::Warn),
        Ok(Token::Capture("decl")),
        Ok(Token::String("Global variable detected".to_string())),
        Ok(Token::Semicolon),

        Ok(Token::Match),
        Ok(Token::LParen),
        Ok(Token::Identifier("translation_unit")),
        Ok(Token::LParen),
        Ok(Token::Identifier("preproc_ifdef")),
        Ok(Token::LParen),
        Ok(Token::Identifier("declaration")),
        Ok(Token::Identifier("declarator")),
        Ok(Token::Colon),
        Ok(Token::LParen),
        Ok(Token::Identifier("init_declarator")),
        Ok(Token::RParen),
        Ok(Token::RParen),
        Ok(Token::Capture("decl")),
        Ok(Token::RParen),
        Ok(Token::RParen),
        Ok(Token::Warn),
        Ok(Token::Capture("decl")),
        Ok(Token::String("Global variable detected".to_string())),
        Ok(Token::Semicolon),
    ],
)]
fn test_token(#[case] source: &str, #[case] expected: Vec<Result<Token, TokenError>>) {
    let actual = Token::lexer(source).collect::<Vec<_>>();
    similar_asserts::assert_eq!(actual, expected);
}

#[rstest]
#[case("ð´¿\u{0081}\x00\r$�dXåó©\u{0098}®\x08&")]
fn test_string(#[case] source: &str) {
    let tokens = StringToken::lexer(source)
        .map(|result| {
            assert!(matches!(result, Ok(_)));
            result.unwrap()
        })
        .collect::<Vec<_>>();

    similar_asserts::assert_eq!(
        tokens,
        source.chars().map(StringToken::Other).collect::<Vec<_>>()
    );
}

#[allow(unused_imports)]
mod proptests {
    use super::*;
    use proptest::{char, collection::vec, prop_assert, prop_assert_eq, proptest};

    proptest! {
        #[test]
        fn doesnt_crash(source in ".*") {
            run_lexer_impl(source.as_str(), false);
        }

        #[test]
        fn string_escape(source in r#"(\\[bfnrt\\/"])*"#) {
            let mut tokens = StringToken::lexer(source.as_str());
            prop_assert!(tokens.all(|token| matches!(token, Ok(StringToken::Escape(_)))));
        }

        #[test]
        fn string_unicode(codepoints in proptest::collection::vec(char::range('\u{1}', '\u{FFFF}'), 0..100)) {
            let source = codepoints
                .iter()
                .map(|&c| format!("\\u{:04X?}", c as u32))
                .collect::<String>();
            let expected = codepoints
                .iter()
                .map(|&c| Ok(StringToken::Unicode(c)))
                .collect::<Vec<_>>();
            let tokens = StringToken::lexer(source.as_str()).collect::<Vec<_>>();
            prop_assert_eq!(tokens, expected);
        }

        #[test]
        fn string_other(source in r#"[^\\"]*"#) {
            let mut tokens = StringToken::lexer(source.as_str());
            prop_assert!(tokens.all(|token| matches!(token, Ok(StringToken::Other(_)))));
        }
    }
}

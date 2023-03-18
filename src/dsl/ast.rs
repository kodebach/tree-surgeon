use std::ops::Range;

use strum::{AsRefStr, EnumIter, EnumString};
use tree_sitter::Query;

pub type Span = std::ops::Range<usize>;
pub type Spanned<T> = (T, Span);

#[derive(Eq, PartialEq, Hash, Clone, Copy, Debug, EnumIter, EnumString, AsRefStr)]
pub enum Case {
    Camel,
    UpperCamel,
    Snake,
    UpperSnake,
    Kebab,
    UpperKebab,
}

impl From<Case> for convert_case::Case {
    fn from(case: Case) -> Self {
        match case {
            Case::Camel => convert_case::Case::Camel,
            Case::UpperCamel => convert_case::Case::UpperCamel,
            Case::Snake => convert_case::Case::Snake,
            Case::UpperSnake => convert_case::Case::UpperSnake,
            Case::Kebab => convert_case::Case::Kebab,
            Case::UpperKebab => convert_case::Case::UpperKebab,
        }
    }
}

#[derive(Debug)]
pub struct Script {
    statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct Match {
    query: Query,
    action: MatchAction,
}

#[derive(Debug)]
pub enum MatchAction {
    Replace(Replace),
    Warn(Warn),
}

#[derive(Debug)]
pub struct Replace {
    capture_name: String,
    replacement: StringExpression,
}

#[derive(Debug)]
pub struct Warn {
    capture_name: String,
    message: StringExpression,
}

#[derive(Debug)]
pub enum StringExpression {
    Literal(String),
    Join(Vec<JoinItem>),
}

#[derive(Debug)]
pub enum JoinItem {
    CaptureExpr(CaptureExpr),
    Literal(String),
}

#[derive(Debug)]
pub struct CaptureExpr {
    capture_name: String,
    target_case: Option<Case>,
    range: Option<Range<Option<isize>>>,
}

#[derive(Debug)]
pub enum Statement {
    Match(Match),
    Invalid,
}

impl CaptureExpr {
    pub fn new(
        capture_name: String,
        target_case: Option<Case>,
        range: Option<Range<Option<isize>>>,
    ) -> Self {
        Self {
            capture_name,
            target_case,
            range,
        }
    }

    pub fn capture_name(&self) -> &str {
        self.capture_name.as_ref()
    }

    pub fn target_case(&self) -> Option<Case> {
        self.target_case
    }

    pub fn range(&self) -> Option<&Range<Option<isize>>> {
        self.range.as_ref()
    }
}

impl Replace {
    pub fn new(capture_name: String, replacement: StringExpression) -> Self {
        Self {
            capture_name,
            replacement,
        }
    }

    pub fn capture_name<'a>(&'a self) -> &'a str {
        &self.capture_name
    }

    pub fn replacement<'a>(&'a self) -> &'a StringExpression {
        &self.replacement
    }
}

impl Warn {
    pub fn new(capture_name: String, message: StringExpression) -> Self {
        Self {
            capture_name,
            message,
        }
    }

    pub fn capture_name<'a>(&'a self) -> &'a str {
        &self.capture_name
    }

    pub fn message<'a>(&'a self) -> &'a StringExpression {
        &self.message
    }
}

impl Match {
    pub fn new(query: Query, action: MatchAction) -> Self {
        Self { query, action }
    }

    pub fn query(&self) -> &Query {
        &self.query
    }

    pub fn action(&self) -> &MatchAction {
        &self.action
    }
}

impl Script {
    pub fn new(statements: Vec<Statement>) -> Self {
        Self { statements }
    }

    pub fn statements<'a>(self: &'a Self) -> &'a [Statement] {
        &self.statements
    }
}

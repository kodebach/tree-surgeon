use std::ops::Range;

use chumsky::span::SimpleSpan;
use strum::{AsRefStr, EnumIter, EnumString};

pub type Span = SimpleSpan;
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

#[derive(Debug, PartialEq, Eq)]
pub struct Script {
    pub statements: Vec<Statement>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Match {
    pub query: Query,
    pub clauses: Vec<MatchClause>,
    pub action: MatchAction,
}

#[derive(Debug, PartialEq, Eq)]
pub enum MatchClause {
    Where(WhereExpr),
}

#[derive(Debug, PartialEq, Eq)]
pub enum WhereExpr {
    Equals(EqualsExpr),
    Contains(ContainsExpr),
    And(AndExpr),
    Or(OrExpr),
    Not(NotExpr),
}

#[derive(Debug, PartialEq, Eq)]
pub struct EqualsExpr {
    pub left: StringExpression,
    pub right: StringExpression,
}

#[derive(Debug, PartialEq, Eq)]
pub struct AndExpr {
    pub left: Box<WhereExpr>,
    pub right: Box<WhereExpr>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct OrExpr {
    pub left: Box<WhereExpr>,
    pub right: Box<WhereExpr>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct NotExpr(pub Box<WhereExpr>);

#[derive(Debug, PartialEq, Eq)]
pub struct ContainsExpr {
    pub capture_name: String,
    pub query: Query,
}

#[derive(Debug, PartialEq, Eq)]
pub enum MatchAction {
    Replace(Replace),
    Warn(Warn),
    Remove(Remove),
    Insert(Insert),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Replace {
    pub capture_name: String,
    pub replacement: StringExpression,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Warn {
    pub capture_name: String,
    pub message: StringExpression,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Remove {
    pub capture_name: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InsertLocation {
    Before,
    After,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Insert {
    pub location: InsertLocation,
    pub capture_name: String,
    pub insertion: StringExpression,
}

#[derive(Debug, PartialEq, Eq)]
pub enum StringExpression {
    Literal(String),
    Join(Vec<JoinItem>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum JoinItem {
    CaptureExpr(CaptureExpr),
    Literal(String),
}

#[derive(Debug, PartialEq, Eq)]
pub struct CaptureExpr {
    pub capture_name: String,
    pub target_case: Option<Case>,
    pub range: Option<Range<Option<isize>>>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Statement {
    Match(Match),
    Invalid,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Query {
    Query(tree_sitter::Language, String),
    Invalid,
}

impl Query {
    pub fn ts_query(&self) -> Option<tree_sitter::Query> {
        match self {
            Query::Query(language, text) => tree_sitter::Query::new(*language, text.as_str()).ok(),
            Query::Invalid => None,
        }
    }
}

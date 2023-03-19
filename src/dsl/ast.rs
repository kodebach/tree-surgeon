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

#[derive(Debug)]
pub struct Script {
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct Match {
    pub query: Query,
    pub clauses: Vec<MatchClause>,
    pub action: MatchAction,
}

#[derive(Debug)]
pub enum MatchClause {
    Where(WhereExpr),
}

#[derive(Debug)]
pub enum WhereExpr {
    Equals(EqualsExpr),
    Contains(ContainsExpr),
    And(AndExpr),
    Or(OrExpr),
    Not(NotExpr),
}

#[derive(Debug)]
pub struct EqualsExpr {
    pub left: StringExpression,
    pub right: StringExpression,
}

#[derive(Debug)]
pub struct AndExpr {
    pub left: Box<WhereExpr>,
    pub right: Box<WhereExpr>,
}

#[derive(Debug)]
pub struct OrExpr {
    pub left: Box<WhereExpr>,
    pub right: Box<WhereExpr>,
}

#[derive(Debug)]
pub struct NotExpr(pub Box<WhereExpr>);

#[derive(Debug)]
pub struct ContainsExpr {
    pub capture_name: String,
    pub query: Query,
}

#[derive(Debug)]
pub enum MatchAction {
    Replace(Replace),
    Warn(Warn),
    Remove(Remove),
    Insert(Insert),
}

#[derive(Debug)]
pub struct Replace {
    pub capture_name: String,
    pub replacement: StringExpression,
}

#[derive(Debug)]
pub struct Warn {
    pub capture_name: String,
    pub message: StringExpression,
}

#[derive(Debug)]
pub struct Remove {
    pub capture_name: String,
}

#[derive(Debug, Clone, Copy)]
pub enum InsertLocation {
    Before,
    After,
}

#[derive(Debug)]
pub struct Insert {
    pub location: InsertLocation,
    pub capture_name: String,
    pub insertion: StringExpression,
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
    pub capture_name: String,
    pub target_case: Option<Case>,
    pub range: Option<Range<Option<isize>>>,
}

#[derive(Debug)]
pub enum Statement {
    Match(Match),
    Invalid,
}

#[derive(Debug)]
pub enum Query {
    Query(tree_sitter::Query),
    Invalid,
}

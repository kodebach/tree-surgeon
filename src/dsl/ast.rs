use tree_sitter::Query;

pub type Span = std::ops::Range<usize>;
pub type Spanned<T> = (T, Span);

#[derive(Debug)]
pub struct Script {
    statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct Match {
    query: Query,
    replacement: Replace,
}

#[derive(Debug)]
pub struct Replace {
    capture_name: String,
    replacement: Replacement,
}

#[derive(Debug)]
pub enum Replacement {
    Literal(String),
    Join(Vec<JoinItem>),
}

#[derive(Debug)]
pub enum JoinItem {
    CaptureName(String),
    Literal(String),
}

#[derive(Debug)]
pub enum Statement {
    Match(Match),
    Invalid,
}

impl Replace {
    pub fn new(capture_name: String, replacement: Replacement) -> Replace {
        Replace { capture_name, replacement }
    }

    pub fn capture_name<'a>(&'a self) -> &'a str {
        &self.capture_name
    }

    pub fn replacement<'a>(&'a self) -> &'a Replacement {
        &self.replacement
    }
}

impl Match {
    pub fn new(query: Query, replacement: Replace) -> Match {
        Match { query, replacement }
    }

    pub fn query<'a>(self: &'a Self) -> &'a Query {
        &self.query
    }

    pub fn replacement<'a>(self: &'a Self) -> &'a Replace {
        &self.replacement
    }
}

impl Script {
    pub fn new(statements: Vec<Statement>) -> Script {
        Script { statements }
    }

    pub fn statements<'a>(self: &'a Self) -> &'a [Statement] {
        &self.statements
    }
}

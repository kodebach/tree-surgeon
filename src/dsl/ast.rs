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
    replacement: Replacement,
}

#[derive(Debug)]
pub struct Replacement {
    capture_name: String,
    replacement: String,
}

#[derive(Debug)]
pub enum Statement {
    Match(Match),
    Invalid,
}

impl Replacement {
    pub fn new(capture_name: String, replacement: String) -> Replacement {
        Replacement { capture_name, replacement }
    }

    pub fn capture_name<'a>(self: &'a Self) -> &'a str {
        &self.capture_name
    }

    pub fn replacement<'a>(self: &'a Self) -> &'a str {
        &self.replacement
    }
}

impl Match {
    pub fn new(query: Query, replacement: Replacement) -> Match {
        Match { query, replacement }
    }

    pub fn query<'a>(self: &'a Self) -> &'a Query {
        &self.query
    }

    pub fn replacement<'a>(self: &'a Self) -> &'a Replacement {
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

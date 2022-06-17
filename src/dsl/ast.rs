use tree_sitter::Query;

#[derive(Debug)]
pub struct Script {
    statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct Match {
    query: Query,
}

#[derive(Debug)]
pub enum Statement {
    Match(Match),
}

impl Match {
    pub fn new(query: Query) -> Match {
        Match { query }
    }

    pub fn query<'a>(self: &'a Self) -> &'a Query {
        &self.query
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

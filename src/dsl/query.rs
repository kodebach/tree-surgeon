use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PredicateArg {
    Capture(String),
    Str(String),
    Ident(String),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Quantifier {
    OneOrMore,
    ZeroOrOne,
    ZeroOrMore,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Predicate {
    pub name: String,
    pub args: Vec<PredicateArg>,
}

fn write_string(s: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "\"{}\"", s)
}

fn write_capture(s: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "@{}", s)
}

fn write_predicate(s: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "#{}", s)
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        write_predicate(&self.name, f)?;
        for arg in &self.args {
            write!(f, " ")?;
            match arg {
                PredicateArg::Capture(c) => write_capture(c, f),
                PredicateArg::Ident(i) => write!(f, "{}", i),
                PredicateArg::Str(s) => write_string(s, f),
            }?
        }
        write!(f, ")")
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AlternationItem {
    Choice(Pattern),
    Predicate(Predicate),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum GroupItem {
    Pattern(Pattern),
    Predicate(Predicate),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Anchor;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AnchoredNamedNodeItem {
    pub anchor: bool,
    pub item: NamedNodeItem,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum NamedNodeItem {
    Child(Option<String>, Pattern),
    NegatedChild(String),
    Predicate(Predicate),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Pattern {
    pub pattern: PatternData,
    pub quantifier: Option<Quantifier>,
    pub capture: Option<String>,
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.pattern.fmt(f)?;
        if let Some(q) = &self.quantifier {
            match q {
                Quantifier::OneOrMore => write!(f, "+")?,
                Quantifier::ZeroOrOne => write!(f, "?")?,
                Quantifier::ZeroOrMore => write!(f, "*")?,
            }
        }
        if let Some(c) = &self.capture {
            write!(f, " ")?;
            write_capture(c, f)
        } else {
            Ok(())
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PatternData {
    Alternation(Vec<AlternationItem>),
    AnonymousLeaf(String),
    Group(Vec<GroupItem>),
    NamedNode(String, Vec<AnchoredNamedNodeItem>, Option<Anchor>),
    WildcardNode,
}

impl fmt::Display for PatternData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatternData::Alternation(items) => {
                write!(f, "(")?;
                for (idx, item) in items.iter().enumerate() {
                    if idx > 0 {
                        write!(f, " ")?;
                    }
                    match item {
                        AlternationItem::Choice(c) => c.fmt(f)?,
                        AlternationItem::Predicate(p) => p.fmt(f)?,
                    }
                }
                write!(f, ")")
            }
            PatternData::AnonymousLeaf(s) => s.fmt(f),
            PatternData::Group(items) => {
                write!(f, "(")?;
                for (idx, item) in items.iter().enumerate() {
                    if idx > 0 {
                        write!(f, " ")?;
                    }
                    match item {
                        GroupItem::Pattern(p) => p.fmt(f)?,
                        GroupItem::Predicate(p) => p.fmt(f)?,
                    }
                }
                write!(f, ")")
            }
            PatternData::NamedNode(name, items, anchor) => {
                write!(f, "(")?;
                name.fmt(f)?;
                for item in items {
                    write!(f, " ")?;

                    if item.anchor {
                        write!(f, ".")?;
                    }
                    match &item.item {
                        NamedNodeItem::Child(field_name, pattern) => {
                            if let Some(field_name) = field_name {
                                field_name.fmt(f)?;
                                write!(f, ": ")?;
                            }
                            pattern.fmt(f)?;
                        }
                        NamedNodeItem::NegatedChild(field_name) => {
                            write!(f, "!")?;
                            field_name.fmt(f)?;
                        }
                        NamedNodeItem::Predicate(p) => p.fmt(f)?,
                    }
                    if let Some(_) = anchor {
                        write!(f, ".")?;
                    }
                }
                write!(f, ")")
            }
            PatternData::WildcardNode => write!(f, "_"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum QueryItem {
    Pattern(Pattern),
    Predicate(Predicate),
    Invalid,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Query {
    pub items: Vec<QueryItem>,
}

impl fmt::Display for Query {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (idx, item) in self.items.iter().enumerate() {
            if idx > 0 {
                write!(f, " ")?;
            }
            match item {
                QueryItem::Pattern(p) => p.fmt(f),
                QueryItem::Predicate(p) => p.fmt(f),
                QueryItem::Invalid => unreachable!("should only happen in error branch"),
            }?
        }
        Ok(())
    }
}

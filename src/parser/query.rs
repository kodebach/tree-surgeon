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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PatternData {
    Alternation(Vec<AlternationItem>),
    AnonymousLeaf(String),
    Group(Vec<GroupItem>),
    NamedNode(String, Vec<AnchoredNamedNodeItem>, Option<Anchor>),
    WildcardNode,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QueryItem {
    Pattern(Pattern),
    Predicate(Predicate),
}

use crate::{kast::Sort, provenance::SourceId};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Position {
    pub offset: usize,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Span {
    pub start: Position,
    pub end: Position,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Attribute {
    pub key: String,
    pub value: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceFile {
    pub source: String,
    pub source_id: SourceId,
    pub requires: Vec<Require>,
    pub modules: Vec<Module>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Require {
    pub path: String,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Module {
    pub name: String,
    pub attributes: Vec<Attribute>,
    pub imports: Vec<Import>,
    pub sentences: Vec<Sentence>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Import {
    pub module: String,
    pub public: bool,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Sentence {
    Syntax(SyntaxDeclaration),
    Priority(SyntaxPriority),
    Associativity(SyntaxAssociativity),
    Lexical(SyntaxLexical),
    Bubble(Bubble),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxDeclaration {
    pub parameters: Vec<Sort>,
    pub sort: Sort,
    pub body: SyntaxBody,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SyntaxBody {
    Sort(Vec<Attribute>),
    Productions(Vec<PriorityBlock>),
    Synonym {
        old_sort: Sort,
        attributes: Vec<Attribute>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Associativity {
    Left,
    Right,
    NonAssoc,
    Unspecified,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PriorityBlock {
    pub associativity: Associativity,
    pub productions: Vec<Production>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Production {
    pub items: Vec<ProductionItem>,
    pub attributes: Vec<Attribute>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProductionItem {
    Terminal(String),
    Regex(String),
    NonTerminal {
        name: Option<String>,
        sort: Sort,
    },
    UserList {
        sort: Sort,
        separator: String,
        non_empty: bool,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxPriority {
    pub groups: Vec<Vec<String>>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxAssociativity {
    pub associativity: Associativity,
    pub tags: Vec<String>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxLexical {
    pub name: String,
    pub regex: String,
    pub attributes: Vec<Attribute>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BubbleKind {
    Rule,
    Claim,
    Context,
    ContextAlias,
    Configuration,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Bubble {
    pub kind: BubbleKind,
    pub content: String,
    pub label: Option<String>,
    pub attributes: Vec<Attribute>,
    pub content_span: Span,
    pub span: Span,
}

//! Syntax tree for textual KORE.

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition {
    pub attributes: Attributes,
    pub modules: Vec<Module>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Module {
    pub name: String,
    pub sentences: Vec<Sentence>,
    pub attributes: Attributes,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Sentence {
    Import {
        module: String,
        attributes: Attributes,
    },
    SortDeclaration {
        hooked: bool,
        name: String,
        parameters: Vec<String>,
        attributes: Attributes,
    },
    SymbolDeclaration {
        hooked: bool,
        symbol: Symbol,
        argument_sorts: Vec<Sort>,
        result_sort: Sort,
        attributes: Attributes,
    },
    AliasDeclaration {
        alias: Symbol,
        argument_sorts: Vec<Sort>,
        result_sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
        attributes: Attributes,
    },
    Axiom {
        parameters: Vec<String>,
        pattern: Box<Pattern>,
        attributes: Attributes,
    },
    Claim {
        parameters: Vec<String>,
        pattern: Box<Pattern>,
        attributes: Attributes,
    },
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Attributes(pub Vec<Pattern>);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Sort {
    Variable(String),
    Application { name: String, arguments: Vec<Sort> },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Symbol {
    pub name: String,
    pub sort_parameters: Vec<Sort>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VariableKind {
    Element,
    Set,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Variable {
    pub kind: VariableKind,
    pub name: String,
    pub sort: Sort,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Associativity {
    Left,
    Right,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Pattern {
    String(String),
    Variable(Variable),
    Application {
        symbol: Symbol,
        arguments: Vec<Pattern>,
    },
    Top {
        sort: Sort,
    },
    Bottom {
        sort: Sort,
    },
    And {
        sort: Sort,
        arguments: Vec<Pattern>,
    },
    Or {
        sort: Sort,
        arguments: Vec<Pattern>,
    },
    Not {
        sort: Sort,
        argument: Box<Pattern>,
    },
    Next {
        sort: Sort,
        argument: Box<Pattern>,
    },
    Implies {
        sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    Iff {
        sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    Rewrites {
        sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    Exists {
        sort: Sort,
        variable: Variable,
        body: Box<Pattern>,
    },
    Forall {
        sort: Sort,
        variable: Variable,
        body: Box<Pattern>,
    },
    Mu {
        variable: Variable,
        body: Box<Pattern>,
    },
    Nu {
        variable: Variable,
        body: Box<Pattern>,
    },
    Ceil {
        operand_sort: Sort,
        result_sort: Sort,
        argument: Box<Pattern>,
    },
    Floor {
        operand_sort: Sort,
        result_sort: Sort,
        argument: Box<Pattern>,
    },
    Equals {
        operand_sort: Sort,
        result_sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    In {
        operand_sort: Sort,
        result_sort: Sort,
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    DomainValue {
        sort: Sort,
        value: String,
    },
    AssociativeApplication {
        associativity: Associativity,
        symbol: Symbol,
        arguments: Vec<Pattern>,
    },
}

//! The user-facing K term model.

use std::fmt::{self, Display, Formatter};

use super::printer::Printer;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Sort {
    pub name: String,
    pub parameters: Vec<Sort>,
}

impl Sort {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            parameters: Vec::new(),
        }
    }

    pub fn with_parameters(name: impl Into<String>, parameters: Vec<Self>) -> Self {
        Self {
            name: name.into(),
            parameters,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Label {
    pub name: String,
    pub parameters: Vec<Sort>,
}

impl Label {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            parameters: Vec::new(),
        }
    }

    pub fn with_parameters(name: impl Into<String>, parameters: Vec<Sort>) -> Self {
        Self {
            name: name.into(),
            parameters,
        }
    }
}

/// A K term. Variant order follows the Scala frontend's total ordering.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Term {
    InjectedLabel(Label),
    Rewrite {
        left: Box<Term>,
        right: Box<Term>,
    },
    As {
        pattern: Box<Term>,
        alias: Box<Term>,
    },
    Variable {
        name: String,
        sort: Option<Sort>,
    },
    Sequence(Vec<Term>),
    Apply {
        label: Label,
        arguments: Vec<Term>,
    },
    Token {
        token: String,
        sort: Sort,
    },
}

impl Term {
    pub fn variable(name: impl Into<String>) -> Self {
        Self::Variable {
            name: name.into(),
            sort: None,
        }
    }

    pub fn apply(label: impl Into<String>, arguments: Vec<Self>) -> Self {
        Self::Apply {
            label: Label::new(label),
            arguments,
        }
    }

    pub fn sequence(items: impl IntoIterator<Item = Self>) -> Self {
        let mut flattened = Vec::new();
        for item in items {
            match item {
                Self::Sequence(nested) => flattened.extend(nested),
                item => flattened.push(item),
            }
        }
        Self::Sequence(flattened)
    }
}

impl Display for Sort {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&Printer::new().print_sort(self))
    }
}

impl Display for Label {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&Printer::new().print_label(self))
    }
}

impl Display for Term {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&Printer::new().print_term(self))
    }
}

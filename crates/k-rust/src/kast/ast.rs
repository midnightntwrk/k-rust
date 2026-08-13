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

/// A byte range relative to the source fragment parsed into a term.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TermSpan {
    pub start: usize,
    pub end: usize,
}

/// The catalog-scoped production index selected while parsing a term.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ResolvedProductionId(pub usize);

/// Compiler metadata carried by a nested term.
///
/// User-facing equality, ordering, debug output, textual KAST, and KAST JSON all
/// intentionally ignore this metadata.
#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct TermMetadata {
    pub span: Option<TermSpan>,
    pub production: Option<ResolvedProductionId>,
    /// An explicit compiler sort attached by transformations such as semantic-cast resolution.
    pub sort: Option<Sort>,
}

/// A K term. Semantic variant order follows the Scala frontend's total ordering.
#[derive(Clone)]
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
    #[doc(hidden)]
    Annotated {
        term: Box<Term>,
        metadata: TermMetadata,
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
                Self::Annotated { term, .. } if matches!(*term, Self::Sequence(_)) => {
                    let Self::Sequence(nested) = *term else {
                        unreachable!()
                    };
                    flattened.extend(nested);
                }
                item => flattened.push(item),
            }
        }
        Self::Sequence(flattened)
    }

    pub fn with_metadata(self, metadata: TermMetadata) -> Self {
        if metadata == TermMetadata::default() {
            return self;
        }
        match self {
            Self::Annotated {
                term,
                metadata: mut existing,
            } => {
                if metadata.span.is_some() {
                    existing.span = metadata.span;
                }
                if metadata.production.is_some() {
                    existing.production = metadata.production;
                }
                if metadata.sort.is_some() {
                    existing.sort = metadata.sort;
                }
                Self::Annotated {
                    term,
                    metadata: existing,
                }
            }
            term => Self::Annotated {
                term: Box::new(term),
                metadata,
            },
        }
    }

    pub fn metadata(&self) -> Option<&TermMetadata> {
        match self {
            Self::Annotated { metadata, .. } => Some(metadata),
            _ => None,
        }
    }

    pub fn unannotated(&self) -> &Self {
        let mut term = self;
        while let Self::Annotated { term: inner, .. } = term {
            term = inner;
        }
        term
    }

    pub fn into_unannotated(self) -> Self {
        let mut term = self;
        while let Self::Annotated { term: inner, .. } = term {
            term = *inner;
        }
        term
    }

    /// Visit this term and its descendants in deterministic pre-order.
    pub fn visit_preorder(&self, visitor: &mut impl FnMut(&Self)) {
        let term = self.unannotated();
        visitor(term);
        match term {
            Self::Rewrite { left, right } => {
                left.visit_preorder(visitor);
                right.visit_preorder(visitor);
            }
            Self::As { pattern, alias } => {
                pattern.visit_preorder(visitor);
                alias.visit_preorder(visitor);
            }
            Self::Sequence(items)
            | Self::Apply {
                arguments: items, ..
            } => {
                for item in items {
                    item.visit_preorder(visitor);
                }
            }
            Self::InjectedLabel(_) | Self::Variable { .. } | Self::Token { .. } => {}
            Self::Annotated { .. } => unreachable!(),
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self.unannotated() {
            Self::InjectedLabel(label) => {
                formatter.debug_tuple("InjectedLabel").field(label).finish()
            }
            Self::Rewrite { left, right } => formatter
                .debug_struct("Rewrite")
                .field("left", left)
                .field("right", right)
                .finish(),
            Self::As { pattern, alias } => formatter
                .debug_struct("As")
                .field("pattern", pattern)
                .field("alias", alias)
                .finish(),
            Self::Variable { name, sort } => formatter
                .debug_struct("Variable")
                .field("name", name)
                .field("sort", sort)
                .finish(),
            Self::Sequence(items) => formatter.debug_tuple("Sequence").field(items).finish(),
            Self::Apply { label, arguments } => formatter
                .debug_struct("Apply")
                .field("label", label)
                .field("arguments", arguments)
                .finish(),
            Self::Token { token, sort } => formatter
                .debug_struct("Token")
                .field("token", token)
                .field("sort", sort)
                .finish(),
            Self::Annotated { .. } => unreachable!(),
        }
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl Eq for Term {}

impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Term {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let left = self.unannotated();
        let right = other.unannotated();
        let rank = |term: &Self| match term {
            Self::InjectedLabel(_) => 0,
            Self::Rewrite { .. } => 1,
            Self::As { .. } => 2,
            Self::Variable { .. } => 3,
            Self::Sequence(_) => 4,
            Self::Apply { .. } => 5,
            Self::Token { .. } => 6,
            Self::Annotated { .. } => unreachable!(),
        };
        match rank(left).cmp(&rank(right)) {
            Ordering::Equal => {}
            ordering => return ordering,
        }
        match (left, right) {
            (Self::InjectedLabel(left), Self::InjectedLabel(right)) => left.cmp(right),
            (
                Self::Rewrite {
                    left: left_left,
                    right: left_right,
                },
                Self::Rewrite {
                    left: right_left,
                    right: right_right,
                },
            ) => (left_left, left_right).cmp(&(right_left, right_right)),
            (
                Self::As {
                    pattern: left_pattern,
                    alias: left_alias,
                },
                Self::As {
                    pattern: right_pattern,
                    alias: right_alias,
                },
            ) => (left_pattern, left_alias).cmp(&(right_pattern, right_alias)),
            (
                Self::Variable {
                    name: left_name,
                    sort: left_sort,
                },
                Self::Variable {
                    name: right_name,
                    sort: right_sort,
                },
            ) => (left_name, left_sort).cmp(&(right_name, right_sort)),
            (Self::Sequence(left), Self::Sequence(right)) => left.cmp(right),
            (
                Self::Apply {
                    label: left_label,
                    arguments: left_arguments,
                },
                Self::Apply {
                    label: right_label,
                    arguments: right_arguments,
                },
            ) => (left_label, left_arguments).cmp(&(right_label, right_arguments)),
            (
                Self::Token {
                    token: left_token,
                    sort: left_sort,
                },
                Self::Token {
                    token: right_token,
                    sort: right_sort,
                },
            ) => (left_token, left_sort).cmp(&(right_token, right_sort)),
            _ => unreachable!("equal term ranks have matching variants"),
        }
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

//! The user-facing K term model.

use std::{
    fmt::{self, Display, Formatter},
    sync::Arc,
};

use crate::names::BuiltinSort;
#[cfg(test)]
use crate::names::WellKnownSymbol;
use crate::provenance::{OriginRecord, SourceId};

use super::names::LabelName;
use super::printer::Printer;

/// A K sort: a name applied to sort parameters.
///
/// A sort is dropped with an explicit work list, so a sort nested to any depth is dropped on
/// any thread. Because of that `Drop`, a sort cannot be destructured by move; take its fields
/// with `std::mem::take` instead.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Sort {
    pub name: String,
    pub parameters: Vec<Sort>,
}

/// Dropping a sort frees each of its levels in turn rather than recursing into its parameters,
/// so its depth does not bound the stack it takes: a reader accepts sorts of any depth, and
/// their owner drops them wherever it is.
impl Drop for Sort {
    #[inline]
    fn drop(&mut self) {
        // Most sorts have no parameters; this check is all their drop adds.
        if !self.parameters.is_empty() {
            self.drop_parameters();
        }
    }
}

impl Sort {
    #[inline(never)]
    fn drop_parameters(&mut self) {
        if self
            .parameters
            .iter()
            .all(|parameter| parameter.parameters.is_empty())
        {
            // The parameters' own drops free them without going any deeper.
            return;
        }
        let mut work = std::mem::take(&mut self.parameters);
        // Invariant: `work` holds the detached sorts whose parameters are still attached; each
        // pop detaches one sort's parameters into `work`, so each sort is popped once and is
        // dropped with no parameters left.
        while let Some(mut sort) = work.pop() {
            work.append(&mut sort.parameters);
        }
    }
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

    /// The nullary sort with the builtin's K spelling.
    pub fn builtin(sort: BuiltinSort) -> Self {
        Self::new(sort.k_name())
    }

    /// True for the nullary sort with the builtin's K spelling.
    pub fn is_builtin(&self, sort: BuiltinSort) -> bool {
        self.parameters.is_empty() && self.name == sort.k_name()
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

    /// True when the label's name is the well-known KORE symbol's or the internal label's
    /// spelling; parameters are ignored.
    pub fn is(&self, label: impl LabelName) -> bool {
        self.name == label.spelling()
    }
}

/// An absolute byte range in one logical source's semantic text.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TermSpan {
    pub source: SourceId,
    pub start: usize,
    pub end: usize,
}

/// A collision-resistant content identity for a production.
///
/// The identity is the first 128 bits of SHA-256 over the canonical production payload. Equal
/// payloads always have equal identities. The compiler relies on SHA-256 collision resistance
/// when using identity equality as a substitute for comparing the payloads.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProductionIdentity([u8; 16]);

impl ProductionIdentity {
    pub(crate) fn from_digest(digest: [u8; 16]) -> Self {
        Self(digest)
    }

    /// Encode this identity as 32 lowercase hexadecimal characters.
    pub fn to_hex(self) -> String {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut encoded = String::with_capacity(32);
        for byte in self.0 {
            encoded.push(HEX[usize::from(byte >> 4)] as char);
            encoded.push(HEX[usize::from(byte & 0x0f)] as char);
        }
        encoded
    }

    /// Decode exactly 32 lowercase hexadecimal characters.
    pub fn from_hex(text: &str) -> Option<Self> {
        if text.len() != 32 {
            return None;
        }
        let mut digest = [0; 16];
        for (index, byte) in digest.iter_mut().enumerate() {
            let high = decode_lower_hex(text.as_bytes()[index * 2])?;
            let low = decode_lower_hex(text.as_bytes()[index * 2 + 1])?;
            *byte = (high << 4) | low;
        }
        Some(Self(digest))
    }

    /// Return the digest bytes used by deterministic compiler fingerprints.
    pub fn as_bytes(&self) -> &[u8; 16] {
        &self.0
    }
}

impl Display for ProductionIdentity {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.to_hex())
    }
}

fn decode_lower_hex(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

/// Compiler metadata carried by a nested term.
///
/// User-facing equality, ordering, debug output, textual KAST, and KAST JSON all
/// intentionally ignore this metadata.
#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct TermMetadata {
    pub span: Option<TermSpan>,
    pub production: Option<ProductionIdentity>,
    /// An explicit compiler sort attached by transformations such as semantic-cast resolution.
    /// Sort injection consumes a strict subsort of an application's natural result as runtime
    /// projection metadata; equal, wider, and unrelated sorts do not authorize a projection.
    pub sort: Option<Sort>,
    pub origin: Option<Arc<OriginRecord>>,
}

/// A K term. Semantic variant order follows the Scala frontend's total ordering.
///
/// A term is dropped with an explicit work list, so a term nested to any depth is dropped on
/// any thread. Because of that `Drop`, a term cannot be destructured by move: match on
/// [`Term::into_parts`] to take a term apart by value.
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

/// The fields of one [`Term`] node, owned, in a type without `Drop`, so that a term taken apart
/// by value can be destructured by move: `match term.into_parts() { TermParts::Apply { label,
/// arguments } => ..., parts => Term::from(parts) }`. Each variant has the fields of the
/// [`Term`] variant of the same name.
pub enum TermParts {
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

impl From<TermParts> for Term {
    fn from(parts: TermParts) -> Self {
        match parts {
            TermParts::InjectedLabel(label) => Self::InjectedLabel(label),
            TermParts::Rewrite { left, right } => Self::Rewrite { left, right },
            TermParts::As { pattern, alias } => Self::As { pattern, alias },
            TermParts::Variable { name, sort } => Self::Variable { name, sort },
            TermParts::Sequence(items) => Self::Sequence(items),
            TermParts::Apply { label, arguments } => Self::Apply { label, arguments },
            TermParts::Token { token, sort } => Self::Token { token, sort },
            TermParts::Annotated { term, metadata } => Self::Annotated { term, metadata },
        }
    }
}

/// The height up to which a term is dropped by its fields' own drops, recursively: a few frames
/// of stack, no work list, and each node is looked at by at most this many checks above it.
const SHALLOW_DROP_HEIGHT: usize = 4;

/// Dropping a term frees each of its nodes in turn rather than recursing into its children, so
/// its depth does not bound the stack it takes. A term outlives the stack of the work that built
/// it (a reader accepts terms of any depth, and a pass returns what it built), and its owner
/// drops it wherever it is.
impl Drop for Term {
    #[inline]
    fn drop(&mut self) {
        // A term without subterms, a leaf or a node already taken apart, is freed by its fields'
        // drops; this check is all its drop adds.
        let has_children = match self {
            Self::Sequence(items)
            | Self::Apply {
                arguments: items, ..
            } => !items.is_empty(),
            Self::Rewrite { .. } | Self::As { .. } | Self::Annotated { .. } => true,
            Self::InjectedLabel(_) | Self::Variable { .. } | Self::Token { .. } => false,
        };
        if has_children {
            self.drop_children();
        }
    }
}

impl Term {
    #[inline(never)]
    fn drop_children(&mut self) {
        if self.height_at_most(SHALLOW_DROP_HEIGHT) {
            // The fields' drops free a term this shallow within a few frames.
            return;
        }
        let mut work = Vec::new();
        self.detach_children(&mut work);
        // Invariant: `work` holds the detached terms whose children are still attached; each
        // pop detaches one term's children into `work`, so each term is popped once and is
        // dropped with no children left.
        while let Some(mut term) = work.pop() {
            term.detach_children(&mut work);
        }
    }
}

impl Term {
    /// Take this term apart into its owned fields; see [`TermParts`].
    pub fn into_parts(self) -> TermParts {
        let term = std::mem::ManuallyDrop::new(self);
        // SAFETY: `term` is never used again and, being `ManuallyDrop`, never dropped, so each
        // field of its variant is moved out exactly once, by the one `ptr::read` of that field
        // below, and is owned by the result alone.
        unsafe {
            use std::ptr::read;
            match &*term {
                Self::InjectedLabel(label) => TermParts::InjectedLabel(read(label)),
                Self::Rewrite { left, right } => TermParts::Rewrite {
                    left: read(left),
                    right: read(right),
                },
                Self::As { pattern, alias } => TermParts::As {
                    pattern: read(pattern),
                    alias: read(alias),
                },
                Self::Variable { name, sort } => TermParts::Variable {
                    name: read(name),
                    sort: read(sort),
                },
                Self::Sequence(items) => TermParts::Sequence(read(items)),
                Self::Apply { label, arguments } => TermParts::Apply {
                    label: read(label),
                    arguments: read(arguments),
                },
                Self::Token { token, sort } => TermParts::Token {
                    token: read(token),
                    sort: read(sort),
                },
                Self::Annotated { term, metadata } => TermParts::Annotated {
                    term: read(term),
                    metadata: read(metadata),
                },
            }
        }
    }

    /// Whether no path from this node down to a leaf has more than `bound` nodes, annotations
    /// counted; it looks at most `bound` levels down.
    fn height_at_most(&self, bound: usize) -> bool {
        let Some(below) = bound.checked_sub(1) else {
            return false;
        };
        match self {
            Self::Rewrite { left, right } => {
                left.height_at_most(below) && right.height_at_most(below)
            }
            Self::As { pattern, alias } => {
                pattern.height_at_most(below) && alias.height_at_most(below)
            }
            Self::Annotated { term, .. } => term.height_at_most(below),
            Self::Sequence(items)
            | Self::Apply {
                arguments: items, ..
            } => items.iter().all(|item| item.height_at_most(below)),
            Self::InjectedLabel(_) | Self::Variable { .. } | Self::Token { .. } => true,
        }
    }

    /// Move the immediate subterms of this node to `work`, leaving it without children. The
    /// first list of children moved to an empty `work` becomes `work`, so a chain of
    /// applications is taken apart without any allocation of its own.
    fn detach_children(&mut self, work: &mut Vec<Self>) {
        let mut detach = |child: &mut Box<Self>| {
            work.push(std::mem::replace(
                child.as_mut(),
                Self::Sequence(Vec::new()),
            ));
        };
        match self {
            Self::Rewrite { left, right } => {
                detach(left);
                detach(right);
            }
            Self::As { pattern, alias } => {
                detach(pattern);
                detach(alias);
            }
            Self::Annotated { term, .. } => detach(term),
            Self::Sequence(items)
            | Self::Apply {
                arguments: items, ..
            } => {
                if work.capacity() == 0 {
                    std::mem::swap(work, items);
                } else {
                    work.append(items);
                }
            }
            Self::InjectedLabel(_) | Self::Variable { .. } | Self::Token { .. } => {}
        }
    }

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
            match item.into_parts() {
                TermParts::Sequence(nested) => flattened.extend(nested),
                TermParts::Annotated { term, .. } if matches!(*term, Self::Sequence(_)) => {
                    let TermParts::Sequence(nested) = term.into_parts() else {
                        unreachable!()
                    };
                    flattened.extend(nested);
                }
                parts => flattened.push(Self::from(parts)),
            }
        }
        Self::Sequence(flattened)
    }

    pub fn with_metadata(self, metadata: TermMetadata) -> Self {
        if metadata == TermMetadata::default() {
            return self;
        }
        match self.into_parts() {
            TermParts::Annotated {
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
                if metadata.origin.is_some() {
                    existing.origin = metadata.origin;
                }
                Self::Annotated {
                    term,
                    metadata: existing,
                }
            }
            parts => Self::Annotated {
                term: Box::new(Self::from(parts)),
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
        while matches!(term, Self::Annotated { .. }) {
            let TermParts::Annotated { term: inner, .. } = term.into_parts() else {
                unreachable!()
            };
            term = *inner;
        }
        term
    }

    /// Strict structural equality used by incremental definition resolution.
    /// Semantic equality intentionally ignores compiler annotations; reuse cannot.
    pub(crate) fn identical(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Annotated {
                    term: left,
                    metadata: left_metadata,
                },
                Self::Annotated {
                    term: right,
                    metadata: right_metadata,
                },
            ) => left_metadata == right_metadata && left.identical(right),
            (Self::Annotated { .. }, _) | (_, Self::Annotated { .. }) => false,
            (Self::InjectedLabel(left), Self::InjectedLabel(right)) => left == right,
            (
                Self::Rewrite {
                    left: left_left,
                    right: left_right,
                },
                Self::Rewrite {
                    left: right_left,
                    right: right_right,
                },
            ) => left_left.identical(right_left) && left_right.identical(right_right),
            (
                Self::As {
                    pattern: left_pattern,
                    alias: left_alias,
                },
                Self::As {
                    pattern: right_pattern,
                    alias: right_alias,
                },
            ) => left_pattern.identical(right_pattern) && left_alias.identical(right_alias),
            (
                Self::Variable {
                    name: left_name,
                    sort: left_sort,
                },
                Self::Variable {
                    name: right_name,
                    sort: right_sort,
                },
            ) => left_name == right_name && left_sort == right_sort,
            (Self::Sequence(left), Self::Sequence(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(right)
                        .all(|(left, right)| left.identical(right))
            }
            (
                Self::Apply {
                    label: left_label,
                    arguments: left_arguments,
                },
                Self::Apply {
                    label: right_label,
                    arguments: right_arguments,
                },
            ) => {
                left_label == right_label
                    && left_arguments.len() == right_arguments.len()
                    && left_arguments
                        .iter()
                        .zip(right_arguments)
                        .all(|(left, right)| left.identical(right))
            }
            (
                Self::Token {
                    token: left_token,
                    sort: left_sort,
                },
                Self::Token {
                    token: right_token,
                    sort: right_sort,
                },
            ) => left_token == right_token && left_sort == right_sort,
            _ => false,
        }
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

/// Terms, sorts and labels that are dropped with explicit work lists.
///
/// A [`Term`] or [`Sort`] drops by recursion, one native frame per level, so a value nested
/// deeper than the dropping thread's stack allows aborts the process when it is dropped. A
/// reader that decodes input of any depth, and fails after it has built part of it, hands what
/// it built to a `DeepDrop`, so that the failure is returned without recursing over the depth of
/// the input. Dropping it takes each value apart level by level: the children of a node are moved
/// to the work lists before the node, then childless, is dropped.
#[derive(Default)]
pub(crate) struct DeepDrop {
    terms: Vec<Term>,
    sorts: Vec<Sort>,
}

impl DeepDrop {
    /// Drop `terms` with explicit work lists.
    pub(crate) fn drop_terms(terms: impl IntoIterator<Item = Term>) {
        Self::default().terms(terms);
    }

    /// Drop `sorts` with explicit work lists.
    pub(crate) fn drop_sorts(sorts: impl IntoIterator<Item = Sort>) {
        Self::default().sorts(sorts);
    }

    pub(crate) fn term(&mut self, term: Term) {
        self.terms.push(term);
    }

    pub(crate) fn terms(&mut self, terms: impl IntoIterator<Item = Term>) {
        self.terms.extend(terms);
    }

    pub(crate) fn sort(&mut self, sort: Sort) {
        self.sorts.push(sort);
    }

    pub(crate) fn sorts(&mut self, sorts: impl IntoIterator<Item = Sort>) {
        self.sorts.extend(sorts);
    }

    pub(crate) fn label(&mut self, mut label: Label) {
        self.sorts.append(&mut label.parameters);
    }

    /// Move the children of `term`, and the sorts it carries, to the work lists.
    fn take_children(&mut self, term: &mut Term) {
        let take = |term: &mut Term| std::mem::replace(term, Term::Sequence(Vec::new()));
        match term {
            Term::Rewrite { left, right } => {
                self.terms.push(take(left));
                self.terms.push(take(right));
            }
            Term::As { pattern, alias } => {
                self.terms.push(take(pattern));
                self.terms.push(take(alias));
            }
            Term::Sequence(items) => self.terms.append(items),
            Term::Apply { label, arguments } => {
                self.terms.append(arguments);
                self.sorts.append(&mut label.parameters);
            }
            Term::InjectedLabel(label) => self.sorts.append(&mut label.parameters),
            Term::Variable { sort, .. } => self.sorts.extend(sort.take()),
            Term::Token { sort, .. } => self.sorts.append(&mut sort.parameters),
            Term::Annotated { term, metadata } => {
                self.terms.push(take(term));
                self.sorts.extend(metadata.sort.take());
            }
        }
    }
}

impl Drop for DeepDrop {
    fn drop(&mut self) {
        loop {
            if let Some(mut term) = self.terms.pop() {
                self.take_children(&mut term);
            } else if let Some(mut sort) = self.sorts.pop() {
                self.sorts.append(&mut sort.parameters);
            } else {
                return;
            }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builtin_sort_agrees_with_its_k_spelling() {
        for sort in BuiltinSort::ALL {
            assert_eq!(Sort::builtin(sort), Sort::new(sort.k_name()), "{sort:?}");
            assert!(Sort::builtin(sort).is_builtin(sort), "{sort:?}");
            assert!(Sort::new(sort.k_name()).is_builtin(sort), "{sort:?}");
            assert!(
                !Sort::with_parameters(sort.k_name(), vec![Sort::new("Int")]).is_builtin(sort),
                "{sort:?}"
            );
        }
        assert!(!Sort::new("SortK").is_builtin(BuiltinSort::K));
    }

    #[test]
    fn label_is_matches_the_kore_spelling_only() {
        assert!(Label::new("inj").is(WellKnownSymbol::Inj));
        assert!(Label::with_parameters("inj", vec![Sort::new("Int")]).is(WellKnownSymbol::Inj));
        assert!(!Label::new("Lblinj").is(WellKnownSymbol::Inj));
        assert!(!Label::new("inj").is(WellKnownSymbol::KSeq));
    }

    /// Levels of the deep values below: more than a recursive drop takes on a 64 KiB thread in
    /// any build.
    const DEEP: usize = 100_000;

    /// Run `work` on a thread with `bytes` of stack.
    fn on_stack(bytes: usize, work: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .stack_size(bytes)
            .spawn(work)
            .expect("the worker should spawn")
            .join()
            .expect("the worker should finish");
    }

    fn deep_sort() -> Sort {
        let mut sort = Sort::new("S");
        for _ in 0..DEEP {
            sort = Sort::with_parameters("S", vec![Sort::new("T"), sort]);
        }
        sort
    }

    fn origin() -> Arc<OriginRecord> {
        Arc::new(OriginRecord {
            pass: crate::provenance::GeneratingPass::ResolveFun,
            origins: Arc::from(Vec::new()),
            destination: None,
        })
    }

    /// `DEEP` levels around a variable, the `index`th level being `wrap(index, term)`.
    fn chain(wrap: impl Fn(usize, Term) -> Term) -> Term {
        let mut term = Term::variable("X");
        for index in 0..DEEP {
            term = wrap(index, term);
        }
        term
    }

    /// One level of the `index`th kind of node a term nests through, around `term`, with a
    /// sibling leaf where the node has more than one child.
    fn level(index: usize, term: Term) -> Term {
        let leaf = || Term::variable("Y");
        match index % 8 {
            0 => Term::apply("f", vec![leaf(), term, leaf()]),
            1 => Term::Sequence(vec![term, leaf()]),
            2 => Term::Rewrite {
                left: Box::new(term),
                right: Box::new(leaf()),
            },
            3 => Term::Rewrite {
                left: Box::new(leaf()),
                right: Box::new(term),
            },
            4 => Term::As {
                pattern: Box::new(term),
                alias: Box::new(leaf()),
            },
            5 => Term::As {
                pattern: Box::new(leaf()),
                alias: Box::new(term),
            },
            6 => Term::Annotated {
                term: Box::new(term),
                metadata: TermMetadata::default(),
            },
            _ => Term::apply("g", vec![term]),
        }
    }

    /// Terms `DEEP` levels deep through each kind of child and each kind of sort a term holds.
    fn deep_terms() -> Vec<(&'static str, Term)> {
        vec![
            ("applications", chain(|_, term| level(0, term))),
            ("sequences", chain(|_, term| level(1, term))),
            ("rewrite left sides", chain(|_, term| level(2, term))),
            ("rewrite right sides", chain(|_, term| level(3, term))),
            ("as patterns", chain(|_, term| level(4, term))),
            ("as aliases", chain(|_, term| level(5, term))),
            ("annotations", chain(|_, term| level(6, term))),
            ("every kind of node", chain(level)),
            (
                "a variable's sort",
                Term::Variable {
                    name: "X".into(),
                    sort: Some(deep_sort()),
                },
            ),
            (
                "a token's sort",
                Term::Token {
                    token: "t".into(),
                    sort: deep_sort(),
                },
            ),
            (
                "a label's parameters",
                Term::Apply {
                    label: Label::with_parameters("f", vec![deep_sort()]),
                    arguments: Vec::new(),
                },
            ),
            (
                "an injected label's parameters",
                Term::InjectedLabel(Label::with_parameters("f", vec![deep_sort()])),
            ),
            (
                "an annotation's sort",
                Term::Annotated {
                    term: Box::new(Term::variable("X")),
                    metadata: TermMetadata {
                        sort: Some(deep_sort()),
                        ..TermMetadata::default()
                    },
                },
            ),
        ]
    }

    /// Dropping takes a term apart level by level, so a term of any depth, through any kind of
    /// child or sort, and a sort of any depth, are dropped on a thread of 64 KiB of stack.
    #[test]
    fn terms_and_sorts_of_any_depth_are_dropped_on_a_small_stack() {
        for (shape, term) in deep_terms() {
            eprintln!("dropping a term deep through {shape}");
            on_stack(64 << 10, move || drop(term));
        }
        let sort = deep_sort();
        on_stack(64 << 10, move || drop(sort));
    }

    /// Dropping a deep term drops each of its nodes: every annotation of a term with deep and
    /// wide parts holds a reference to one shared record, and dropping the term on a small stack
    /// releases every reference.
    #[test]
    fn dropping_a_deep_term_drops_every_node() {
        let record = origin();
        let annotate = |term: Term| Term::Annotated {
            term: Box::new(term),
            metadata: TermMetadata {
                origin: Some(Arc::clone(&record)),
                ..TermMetadata::default()
            },
        };
        let wide = |index: usize| {
            Term::Sequence(
                (0..index % 5)
                    .map(|_| annotate(Term::variable("W")))
                    .collect(),
            )
        };
        let mut term = annotate(Term::variable("X"));
        for index in 0..DEEP / 10 {
            let node = match level(index, term).into_parts() {
                TermParts::Apply {
                    label,
                    mut arguments,
                } => {
                    arguments.push(wide(index));
                    Term::Apply { label, arguments }
                }
                node => Term::from(node),
            };
            term = annotate(node);
        }
        assert!(Arc::strong_count(&record) > DEEP / 10);
        on_stack(64 << 10, move || drop(term));
        assert_eq!(Arc::strong_count(&record), 1);
    }

    /// Taking a node apart and putting it back together gives the same node, every field
    /// included, and moves each field exactly once: no reference a node holds is lost or
    /// released twice.
    #[test]
    fn a_term_taken_apart_is_rebuilt_from_its_parts() {
        let record = origin();
        let metadata = TermMetadata {
            span: None,
            production: Some(ProductionIdentity::from_digest([7; 16])),
            sort: Some(Sort::with_parameters("S", vec![Sort::new("T")])),
            origin: Some(Arc::clone(&record)),
        };
        let annotated = |term: Term| Term::Annotated {
            term: Box::new(term),
            metadata: metadata.clone(),
        };
        let leaf = || annotated(Term::variable("X"));
        let label = Label::with_parameters("f", vec![Sort::new("Int")]);
        let nodes = vec![
            Term::InjectedLabel(label.clone()),
            Term::Rewrite {
                left: Box::new(leaf()),
                right: Box::new(Term::variable("Y")),
            },
            Term::As {
                pattern: Box::new(Term::variable("Y")),
                alias: Box::new(leaf()),
            },
            Term::Variable {
                name: "X".into(),
                sort: Some(Sort::new("Int")),
            },
            Term::Sequence(vec![leaf(), Term::variable("Y")]),
            Term::Apply {
                label,
                arguments: vec![leaf(), leaf()],
            },
            Term::Token {
                token: "1".into(),
                sort: Sort::new("Int"),
            },
            annotated(Term::apply("g", vec![leaf()])),
        ];
        for node in &nodes {
            let references = Arc::strong_count(&record);
            let rebuilt = Term::from(node.clone().into_parts());
            assert!(rebuilt.identical(node), "{node:?} became {rebuilt:?}");
            drop(rebuilt);
            assert_eq!(Arc::strong_count(&record), references, "{node:?}");
        }
        drop((nodes, metadata));
        assert_eq!(Arc::strong_count(&record), 1);
    }
}

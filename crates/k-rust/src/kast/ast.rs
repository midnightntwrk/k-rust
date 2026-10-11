//! The user-facing K term model.

use std::{
    borrow::Cow,
    fmt::{self, Display, Formatter},
    sync::Arc,
};

use k_rust_kore::measure::{self, Counter};

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
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
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
    /// Sort injection accepts it only at or above the term's natural sort: a semantic cast
    /// computes nothing, so a sort strictly below or unrelated to the natural one is rejected.
    pub sort: Option<Sort>,
    pub origin: Option<Arc<OriginRecord>>,
}

impl TermMetadata {
    /// Strict equality for incremental definition resolution ([`Term::identical`]), counted in
    /// `kompile.resolve_metadata_compares`.
    ///
    /// The span, production and sort are the node's own data and are compared by value; a receipt
    /// is identical only to itself, one allocation. A resolved module is reused only when this
    /// says its sentences are unchanged, so it must imply that the kept node is interchangeable
    /// with a rebuilt one, while a false "changed" only costs a rebuild. One allocation is equal
    /// to itself in every respect, so pointer identity is sound, and it reads none of the
    /// receipt's origin set or destination path, so the comparison costs the same whatever their
    /// size. It forgoes no reuse in the pipeline: a pass gives a node a new receipt only when
    /// the node differs from its counterpart ignoring metadata, so wherever two receipts are
    /// separate allocations the terms differ at that position too, and every other node keeps
    /// its receipt by `Arc` clone.
    ///
    /// [`Term::identical`] has two other callers, in sort inference
    /// (`LoweredTerm::same_lowering` and the checked engines' `checked_lowered_result`). Both
    /// compare lowered parse results, whose metadata holds a span, a production and a sort and
    /// never a receipt: receipts are allocated only by the generating passes' recorder and by the
    /// provenance reader. There the receipts are both absent, which is "identical" by pointer as
    /// by value, so comparing receipts by identity changes neither caller's verdict.
    pub(crate) fn identical(&self, other: &Self) -> bool {
        measure::bump(Counter::KompileResolveMetadataCompares);
        self.span == other.span
            && self.production == other.production
            && self.sort == other.sort
            && match (&self.origin, &other.origin) {
                (None, None) => true,
                (Some(left), Some(right)) => Arc::ptr_eq(left, right),
                (None, Some(_)) | (Some(_), None) => false,
            }
    }
}

/// A K term. Its total order (`Ord`) ranks the variants in declaration order before comparing
/// their fields, ignoring annotations.
///
/// A term is dropped with an explicit work list, and copied and compared one level at a time
/// with stack for one more level (`crate::stack::guarded`), so a term nested to any depth is
/// dropped, copied and compared on any thread. Because of that `Drop`, a term cannot be
/// destructured by move: match on [`Term::into_parts`] to take a term apart by value.
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

/// A term copies one level at a time, each with stack for one more level, so the copy of a term
/// of any depth does not overflow the thread it runs on.
impl Clone for Term {
    fn clone(&self) -> Self {
        crate::stack::guarded(|| match self {
            Self::InjectedLabel(label) => Self::InjectedLabel(label.clone()),
            Self::Rewrite { left, right } => Self::Rewrite {
                left: left.clone(),
                right: right.clone(),
            },
            Self::As { pattern, alias } => Self::As {
                pattern: pattern.clone(),
                alias: alias.clone(),
            },
            Self::Variable { name, sort } => Self::Variable {
                name: name.clone(),
                sort: sort.clone(),
            },
            Self::Sequence(items) => Self::Sequence(items.clone()),
            Self::Apply { label, arguments } => Self::Apply {
                label: label.clone(),
                arguments: arguments.clone(),
            },
            Self::Token { token, sort } => Self::Token {
                token: token.clone(),
                sort: sort.clone(),
            },
            Self::Annotated { term, metadata } => Self::Annotated {
                term: term.clone(),
                metadata: metadata.clone(),
            },
        })
    }
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

    /// The children of this term in step order, each as stored, its annotation included.
    ///
    /// A step is one level of a destination path ([`Term::at_path`]), taken from the term with
    /// its annotations removed, since an annotation records facts about the node it wraps and is
    /// not a node itself. Step 0 of a `Rewrite` is its left side and step 1 its right side; step
    /// 0 of an `As` is its pattern and step 1 its alias; step `i` of a sequence or an application
    /// is its item `i`. Injected labels, variables and tokens have no children.
    pub fn children(&self) -> Vec<&Self> {
        match self.unannotated() {
            Self::Rewrite { left, right } => vec![left, right],
            Self::As { pattern, alias } => vec![pattern, alias],
            Self::Sequence(items)
            | Self::Apply {
                arguments: items, ..
            } => items.iter().collect(),
            Self::InjectedLabel(_) | Self::Variable { .. } | Self::Token { .. } => Vec::new(),
            Self::Annotated { .. } => unreachable!("unannotated strips annotations"),
        }
    }

    /// The mutable counterpart of [`Term::children`], in the same step order.
    pub fn children_mut(&mut self) -> Vec<&mut Self> {
        let mut term = self;
        while let Self::Annotated { term: inner, .. } = term {
            term = inner;
        }
        match term {
            Self::Rewrite { left, right } => vec![&mut **left, &mut **right],
            Self::As { pattern, alias } => vec![&mut **pattern, &mut **alias],
            Self::Sequence(items)
            | Self::Apply {
                arguments: items, ..
            } => items.iter_mut().collect(),
            Self::InjectedLabel(_) | Self::Variable { .. } | Self::Token { .. } => Vec::new(),
            Self::Annotated { .. } => unreachable!("the loop strips annotations"),
        }
    }

    /// The subterm `steps` lead to from this term, one step of [`Term::children`] per level, as
    /// stored, its annotation included; `None` when a step names no child. The empty path leads
    /// to this term.
    pub fn at_path(&self, steps: &[u32]) -> Option<&Self> {
        let mut term = self;
        for &step in steps {
            term = term
                .children()
                .into_iter()
                .nth(usize::try_from(step).ok()?)?;
        }
        Some(term)
    }

    /// The mutable counterpart of [`Term::at_path`], resolving `steps` the same way.
    pub fn at_path_mut(&mut self, steps: &[u32]) -> Option<&mut Self> {
        let mut term = self;
        for &step in steps {
            term = term
                .children_mut()
                .into_iter()
                .nth(usize::try_from(step).ok()?)?;
        }
        Some(term)
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
            ) => left_metadata.identical(right_metadata) && left.identical(right),
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
    ///
    /// A term may be of any depth, so the walk keeps the subterms still to visit in an explicit
    /// work list rather than on the native stack: the first child of each term is visited next,
    /// and its later siblings wait on the list, last first, so a chain needs no list at all.
    pub fn visit_preorder(&self, visitor: &mut impl FnMut(&Self)) {
        let mut pending = Vec::new();
        let mut next = Some(self);
        // Invariant: every term visited so far was visited in pre-order, and `next` followed by
        // `pending` from its end are the subterms still to visit in pre-order; each iteration
        // visits one term and replaces it by its children.
        while let Some(term) = next.take().or_else(|| pending.pop()) {
            let term = term.unannotated();
            visitor(term);
            match term {
                Self::Rewrite { left, right } => {
                    pending.push(&**right);
                    next = Some(&**left);
                }
                Self::As { pattern, alias } => {
                    pending.push(&**alias);
                    next = Some(&**pattern);
                }
                Self::Sequence(items)
                | Self::Apply {
                    arguments: items, ..
                } => {
                    if let Some((first, rest)) = items.split_first() {
                        pending.extend(rest.iter().rev());
                        next = Some(first);
                    }
                }
                Self::InjectedLabel(_) | Self::Variable { .. } | Self::Token { .. } => {}
                Self::Annotated { .. } => unreachable!(),
            }
        }
    }
}

// stack-accepted(kast-debug): `Debug` is for diagnostics, and about 20,000 levels format on 8 MiB in a release build. See docs/backend-port.md#stack-bounds.
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

/// Two terms are compared one level at a time, each with stack for one more level, so the
/// comparison of terms of any depth does not overflow the thread it runs on.
impl Ord for Term {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        crate::stack::guarded(|| self.cmp_level(other))
    }
}

/// The fields of one node that the comparison of terms ([`Term::cmp`], and so [`Term::eq`])
/// reads besides its children: its variant, and its label, or its token or variable name with
/// its sort. Annotations are not among them.
///
/// The derived order is the comparison's order on nodes that differ in these fields: variants in
/// the order [`Term`] declares them, then the fields in order. [`NodeHead::of`] borrows them from
/// a term; [`NodeHead::into_owned`] keeps them past the term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) enum NodeHead<'t> {
    InjectedLabel(Cow<'t, Label>),
    Rewrite,
    As,
    Variable(Cow<'t, str>, Option<Cow<'t, Sort>>),
    Sequence,
    Apply(Cow<'t, Label>),
    Token(Cow<'t, str>, Cow<'t, Sort>),
}

impl<'t> NodeHead<'t> {
    /// The head of `term`, its annotations removed.
    pub(crate) fn of(term: &'t Term) -> Self {
        match term.unannotated() {
            Term::InjectedLabel(label) => Self::InjectedLabel(Cow::Borrowed(label)),
            Term::Rewrite { .. } => Self::Rewrite,
            Term::As { .. } => Self::As,
            Term::Variable { name, sort } => {
                Self::Variable(Cow::Borrowed(name), sort.as_ref().map(Cow::Borrowed))
            }
            Term::Sequence(_) => Self::Sequence,
            Term::Apply { label, .. } => Self::Apply(Cow::Borrowed(label)),
            Term::Token { token, sort } => Self::Token(Cow::Borrowed(token), Cow::Borrowed(sort)),
            Term::Annotated { .. } => unreachable!("unannotated strips annotations"),
        }
    }

    /// This head with its fields owned.
    pub(crate) fn into_owned(self) -> NodeHead<'static> {
        let owned = |sort: Cow<'_, Sort>| Cow::Owned(sort.into_owned());
        match self {
            Self::InjectedLabel(label) => NodeHead::InjectedLabel(Cow::Owned(label.into_owned())),
            Self::Rewrite => NodeHead::Rewrite,
            Self::As => NodeHead::As,
            Self::Variable(name, sort) => {
                NodeHead::Variable(Cow::Owned(name.into_owned()), sort.map(owned))
            }
            Self::Sequence => NodeHead::Sequence,
            Self::Apply(label) => NodeHead::Apply(Cow::Owned(label.into_owned())),
            Self::Token(token, sort) => {
                NodeHead::Token(Cow::Owned(token.into_owned()), owned(sort))
            }
        }
    }
}

impl Term {
    /// One level of [`Term::cmp`], which runs it with stack for one more level: the heads, then
    /// the children in order, each compared by [`Term::cmp`].
    fn cmp_level(&self, other: &Self) -> std::cmp::Ordering {
        let (left, right) = (self.unannotated(), other.unannotated());
        NodeHead::of(left)
            .cmp(&NodeHead::of(right))
            .then_with(|| match (left, right) {
                (
                    Self::Rewrite { left: a, right: b }
                    | Self::As {
                        pattern: a,
                        alias: b,
                    },
                    Self::Rewrite { left: c, right: d }
                    | Self::As {
                        pattern: c,
                        alias: d,
                    },
                ) => (a, b).cmp(&(c, d)),
                (
                    Self::Sequence(l) | Self::Apply { arguments: l, .. },
                    Self::Sequence(r) | Self::Apply { arguments: r, .. },
                ) => l.cmp(r),
                _ => std::cmp::Ordering::Equal,
            })
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
            origins: crate::provenance::OriginSet::new(),
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

    /// The pre-order of `term`, as the recursive definition gives it: the term without its
    /// annotations, then the pre-order of each child in turn.
    fn recursive_preorder(term: &Term, order: &mut Vec<String>) {
        let term = term.unannotated();
        order.push(term.to_string());
        match term {
            Term::Rewrite { left, right } => {
                recursive_preorder(left, order);
                recursive_preorder(right, order);
            }
            Term::As { pattern, alias } => {
                recursive_preorder(pattern, order);
                recursive_preorder(alias, order);
            }
            Term::Sequence(items)
            | Term::Apply {
                arguments: items, ..
            } => {
                for item in items {
                    recursive_preorder(item, order);
                }
            }
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!(),
        }
    }

    /// `visit_preorder` visits every subterm once, in pre-order, through every kind of child and
    /// through annotations, and visits a term of any depth on a thread of 64 KiB of stack.
    #[test]
    fn terms_of_any_depth_are_visited_in_preorder_on_a_small_stack() {
        let leaf = |name: &str| Term::variable(name);
        let mixed = Term::apply(
            "f",
            vec![
                Term::Rewrite {
                    left: Box::new(Term::apply("g", vec![leaf("A"), leaf("B")])),
                    right: Box::new(Term::Sequence(vec![leaf("C"), leaf("D")])),
                },
                Term::As {
                    pattern: Box::new(leaf("E")),
                    alias: Box::new(
                        Term::apply("h", vec![]).with_metadata(TermMetadata::default()),
                    ),
                },
                Term::InjectedLabel(Label::new("k")),
            ],
        );
        let mut expected = Vec::new();
        recursive_preorder(&mixed, &mut expected);
        let mut visited = Vec::new();
        mixed.visit_preorder(&mut |term| visited.push(term.to_string()));
        assert_eq!(visited, expected);
        assert_eq!(visited.len(), 12);

        let deep = (0..100_000).fold(leaf("X"), |term, index| match index % 3 {
            0 => Term::apply("s", vec![term]),
            1 => Term::Rewrite {
                left: Box::new(leaf("L")),
                right: Box::new(term),
            },
            _ => Term::Sequence(vec![leaf("Y"), term]),
        });
        std::thread::Builder::new()
            .stack_size(64 << 10)
            .spawn(move || {
                let mut count = 0;
                deep.visit_preorder(&mut |_| count += 1);
                assert_eq!(count, 1 + 100_000 + 66_666);
            })
            .expect("the worker should spawn")
            .join()
            .expect("the worker should finish");
    }

    /// Copying and comparing run each level of a term with stack for one more, so a term of any
    /// depth through its children (applications, sequences, rewrites, `#as` patterns and
    /// annotations) is copied and compared with its copy on a thread of 64 KiB of stack. (The
    /// sorts and labels a term carries are copied by their own derived traits.)
    #[test]
    fn terms_of_any_depth_are_copied_and_compared_on_a_small_stack() {
        for (shape, term) in deep_terms().into_iter().take(8) {
            eprintln!("copying and comparing a term deep through {shape}");
            on_stack(64 << 10, move || {
                let copy = term.clone();
                assert_eq!(copy.cmp(&term), std::cmp::Ordering::Equal);
                assert!(copy == term);
                drop((copy, term));
            });
        }
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

    /// A node's children come in step order whatever annotates it, each with its own annotation:
    /// a rewrite's left then right side, an alias's pattern then alias, a sequence's or an
    /// application's items in order, and none for a leaf. A path takes one such step per level.
    #[test]
    fn children_come_in_step_order_and_a_path_takes_one_per_level() {
        let sorted = |term: Term| {
            term.with_metadata(TermMetadata {
                sort: Some(Sort::new("S")),
                ..TermMetadata::default()
            })
        };
        let (x, y) = (sorted(Term::variable("X")), Term::variable("Y"));
        let rewrite = sorted(Term::Rewrite {
            left: Box::new(x.clone()),
            right: Box::new(y.clone()),
        });
        let alias = Term::As {
            pattern: Box::new(y.clone()),
            alias: Box::new(x.clone()),
        };
        let cases = [
            (rewrite.clone(), vec![&x, &y]),
            (alias.clone(), vec![&y, &x]),
            (
                Term::Sequence(vec![x.clone(), y.clone(), x.clone()]),
                vec![&x, &y, &x],
            ),
            (
                sorted(Term::apply("f", vec![y.clone(), x.clone()])),
                vec![&y, &x],
            ),
            (Term::InjectedLabel(Label::new("f")), vec![]),
            (x.clone(), vec![]),
            (
                sorted(Term::Token {
                    token: "1".into(),
                    sort: Sort::new("Int"),
                }),
                vec![],
            ),
        ];
        let same = |children: &[&Term], expected: &[&Term]| {
            children.len() == expected.len()
                && children
                    .iter()
                    .zip(expected)
                    .all(|(child, expected)| child.identical(expected))
        };
        for (mut node, expected) in cases {
            assert!(same(&node.children(), &expected), "children of {node:?}");
            let expected = expected.into_iter().cloned().collect::<Vec<_>>();
            let children = node
                .children_mut()
                .into_iter()
                .map(|child| &*child)
                .cloned();
            let children = children.collect::<Vec<_>>();
            assert!(
                same(
                    &children.iter().collect::<Vec<_>>(),
                    &expected.iter().collect::<Vec<_>>()
                ),
                "children_mut of {node:?}"
            );
        }

        let mut term = sorted(Term::apply("g", vec![rewrite, alias]));
        assert!(term.at_path(&[]).is_some_and(|node| node.identical(&term)));
        assert!(term.at_path(&[0, 1]).is_some_and(|node| node.identical(&y)));
        assert!(term.at_path(&[1, 1]).is_some_and(|node| node.identical(&x)));
        assert!(term.at_path(&[2]).is_none(), "g has two children");
        assert!(
            term.at_path(&[0, 0, 0]).is_none(),
            "a variable has no children"
        );
        *term.at_path_mut(&[1, 1]).expect("the alias of the alias") = Term::variable("Z");
        assert!(
            term.at_path(&[1, 1])
                .is_some_and(|node| node.identical(&Term::variable("Z")))
        );
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

    /// A term without its annotations, in a type whose comparison is derived: variants in the
    /// order `Term` declares them, then each variant's fields in order, children included.
    #[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
    enum Derived {
        InjectedLabel(Label),
        Rewrite(Box<Self>, Box<Self>),
        As(Box<Self>, Box<Self>),
        Variable(String, Option<Sort>),
        Sequence(Vec<Self>),
        Apply(Label, Vec<Self>),
        Token(String, Sort),
    }

    impl From<&Term> for Derived {
        fn from(term: &Term) -> Self {
            let boxed = |term: &Term| Box::new(Self::from(term));
            match term.unannotated() {
                Term::InjectedLabel(label) => Self::InjectedLabel(label.clone()),
                Term::Rewrite { left, right } => Self::Rewrite(boxed(left), boxed(right)),
                Term::As { pattern, alias } => Self::As(boxed(pattern), boxed(alias)),
                Term::Variable { name, sort } => Self::Variable(name.clone(), sort.clone()),
                Term::Sequence(items) => Self::Sequence(items.iter().map(Self::from).collect()),
                Term::Apply { label, arguments } => {
                    Self::Apply(label.clone(), arguments.iter().map(Self::from).collect())
                }
                Term::Token { token, sort } => Self::Token(token.clone(), sort.clone()),
                Term::Annotated { .. } => unreachable!("unannotated strips annotations"),
            }
        }
    }

    /// The comparison of terms, and so `Term::eq`, is the derived comparison of the terms without
    /// their annotations. A field is decided only by pairs that agree on every field before it, so
    /// each term is compared with each of its one-edit neighbours (one token text or sort,
    /// variable name or sort, label name or parameter changed at any depth), and with the
    /// previous draw for the order of variants and of children; one side of each pair carries
    /// annotations on some of its nodes.
    #[test]
    fn the_comparison_is_the_derived_comparison_on_one_edit_neighbours() {
        use proptest::{
            strategy::{Strategy, ValueTree},
            test_runner::{Config, RngAlgorithm, TestRng, TestRunner},
        };

        use crate::kast::test_terms::{decorated, one_edit_neighbours, varied_fields};

        let check = |left: &Term, right: &Term| {
            let mut count = 0_u32;
            let annotated = decorated(left, &mut || {
                count += 1;
                count.is_multiple_of(2).then(|| TermMetadata {
                    sort: Some(Sort::new("K")),
                    ..TermMetadata::default()
                })
            });
            let derived = Derived::from(left).cmp(&Derived::from(right));
            for left in [left, &annotated] {
                assert_eq!(left.cmp(right), derived, "{left:?} and {right:?}");
                assert_eq!(right.cmp(left), derived.reverse(), "{right:?} and {left:?}");
                assert_eq!(left == right, derived.is_eq(), "{left:?} and {right:?}");
            }
        };
        let mut runner = TestRunner::new_with_rng(
            Config::default(),
            TestRng::deterministic_rng(RngAlgorithm::ChaCha),
        );
        let strategy = varied_fields();
        let mut previous = Term::Sequence(Vec::new());
        for _ in 0..1024 {
            let term = strategy.new_tree(&mut runner).expect("a case").current();
            check(&term, &term.clone());
            check(&term, &previous);
            for (_, neighbour) in one_edit_neighbours(&term) {
                check(&term, &neighbour);
            }
            previous = term;
        }
    }
}

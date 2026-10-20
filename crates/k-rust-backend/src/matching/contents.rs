//! The one refutation of a collection pattern by the number of items a subject holds.
//!
//! A map, set or list term fixes some items and may have an opaque part: a rest, which is a
//! frame variable, a function application or any other term of the collection sort. A frame
//! variable ranges over every collection of its sort, the unit and any collection of the items
//! a pattern leaves over among them, and a function application may evaluate to any of them. So
//! whether an opaque part could complete a match is a question about what the subject denotes,
//! which the match mode does not change: [`ContentsClash::between`] answers it from the two
//! terms alone, and a [`ContentsClash`] is built nowhere else.

use crate::term::{Term, TermKind};

/// Two collections, the parts of a pattern and of a subject that matching has not paired, whose
/// item counts exclude each other on every valuation of their variables: no instance of the
/// subject is an instance of the pattern.
///
/// A defined instance of a collection term holds exactly the items it fixes when it has no
/// opaque part, and at least as many when it has one: a map or set that would bind a key or hold
/// an element twice is `\bottom`, which is no instance of anything, so a defined instance holds
/// its fixed items as distinct keys or elements, and a list holds every item it fixes. A clash is
/// therefore a side without an opaque part that fixes fewer items than the other side fixes.
/// Where the counts admit a common size, some valuation of an opaque part (the unit, or the
/// items the other side leaves over) may make the two equal, and the pair is no refutation.
///
/// A caller outside the matcher can read a clash but not state one:
///
/// ```compile_fail
/// use k_rust_backend::{matching::ContentsClash, term::Term};
/// fn refute(pattern: Term, subject: Term) -> ContentsClash {
///     ContentsClash { pattern, subject }
/// }
/// ```
///
/// ```
/// use k_rust_backend::{matching::ContentsClash, term::Term};
/// fn read(clash: &ContentsClash) -> (&Term, &Term) {
///     (clash.pattern(), clash.subject())
/// }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContentsClash {
    pattern: Term,
    subject: Term,
}

impl ContentsClash {
    /// The clash of `pattern` and `subject` when their item counts exclude each other, or the two
    /// terms back when some valuation of an opaque part may make them equal.
    pub(super) fn between(pattern: Term, subject: Term) -> Result<Self, (Term, Term)> {
        let (left, right) = (Extent::of(&pattern), Extent::of(&subject));
        if left.excludes(right) {
            Ok(Self { pattern, subject })
        } else {
            Err((pattern, subject))
        }
    }

    /// The pattern's unpaired part.
    #[must_use]
    pub fn pattern(&self) -> &Term {
        &self.pattern
    }

    /// The subject's unpaired part.
    #[must_use]
    pub fn subject(&self) -> &Term {
        &self.subject
    }
}

/// The items a collection term fixes, and whether it has an opaque part, which may hold any
/// number of further items.
#[derive(Clone, Copy, Debug)]
struct Extent {
    fixed: usize,
    open: bool,
}

impl Extent {
    /// A term that is not a map, set or list node, a variable or an application of the
    /// collection sort, fixes no item and is opaque as a whole.
    fn of(term: &Term) -> Self {
        match term.kind() {
            TermKind::List { heads, rest, .. } => Self {
                fixed: heads.len() + rest.as_ref().map_or(0, |(_, tails)| tails.len()),
                open: rest.is_some(),
            },
            TermKind::Map { entries, rest, .. } => Self {
                fixed: entries.len(),
                open: rest.is_some(),
            },
            TermKind::Set { elements, rest, .. } => Self {
                fixed: elements.len(),
                open: rest.is_some(),
            },
            TermKind::Variable(_)
            | TermKind::Application { .. }
            | TermKind::And(..)
            | TermKind::DomainValue { .. }
            | TermKind::Injection { .. } => Self {
                fixed: 0,
                open: true,
            },
        }
    }

    /// Whether no size is the size of a defined instance of both: one side is closed and the
    /// other fixes more items.
    fn excludes(self, other: Self) -> bool {
        (!self.open && other.fixed > self.fixed) || (!other.open && self.fixed > other.fixed)
    }
}

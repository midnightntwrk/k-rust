//! Summaries an item type composes its own from: counts of items failing named flags, a
//! saturating count, a disjunction, the one value all items share, and tuples of these.
//!
//! Each is a monoid of constant size, so a copied node recombines it from its children at a
//! cost that does not grow with the items. A count is also a [`Group`]; the multiset of the
//! variables the items mention, whose size does grow, is [`Multiset`](super::multiset::Multiset).

use std::fmt;

use super::{Group, Summary};

/// The number of items summarized.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Count(pub(crate) usize);

impl Count {
    /// One for an item that `counts`, none otherwise.
    pub(crate) fn of(counts: bool) -> Self {
        Self(usize::from(counts))
    }
}

impl Summary for Count {
    fn identity() -> Self {
        Self(0)
    }

    fn combine(self, right: &Self) -> Self {
        Self(self.0 + right.0)
    }
}

impl Group for Count {
    fn subtract(self, part: &Self) -> Self {
        Self(self.0 - part.0)
    }

    fn weight(&self) -> usize {
        1
    }
}

/// For each of `N` named flags, the number of items that fail it. A flag holds of a sequence
/// when no item fails it, and a seek for the items failing it enters only the subtrees whose
/// count is not zero.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Failing<const N: usize>([usize; N]);

impl<const N: usize> Failing<N> {
    /// The summary of one item, given whether it satisfies each flag.
    pub(crate) fn of(holds: [bool; N]) -> Self {
        Self(holds.map(|holds| usize::from(!holds)))
    }

    /// The number of items failing flag `flag`.
    pub(crate) fn failing(&self, flag: usize) -> usize {
        self.0[flag]
    }

    /// Whether every item satisfies flag `flag`.
    pub(crate) fn holds(&self, flag: usize) -> bool {
        self.0[flag] == 0
    }
}

impl<const N: usize> Summary for Failing<N> {
    fn identity() -> Self {
        Self([0; N])
    }

    fn combine(self, right: &Self) -> Self {
        let mut sum = self.0;
        for (count, other) in sum.iter_mut().zip(right.0) {
            *count += other;
        }
        Self(sum)
    }
}

/// A count that stops at `CAP`: enough to tell none, one and several apart (at `CAP = 2`)
/// without the exact number, which a stored attribute does not need.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Saturating<const CAP: usize>(usize);

impl<const CAP: usize> Saturating<CAP> {
    /// The summary of one item that contributes `count`.
    pub(crate) fn of(count: usize) -> Self {
        Self(count.min(CAP))
    }

    pub(crate) fn get(self) -> usize {
        self.0
    }
}

impl<const CAP: usize> Summary for Saturating<CAP> {
    fn identity() -> Self {
        Self(0)
    }

    fn combine(self, right: &Self) -> Self {
        Self((self.0 + right.0).min(CAP))
    }
}

/// Whether some item has a property.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Any(pub(crate) bool);

impl Summary for Any {
    fn identity() -> Self {
        Self(false)
    }

    fn combine(self, right: &Self) -> Self {
        Self(self.0 || right.0)
    }
}

/// The value every item has, when they all have the same one: none for no item, `Mixed` for
/// items with different values.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Uniform<T> {
    Empty,
    One(T),
    Mixed,
}

impl<T: Clone + Eq + fmt::Debug> Summary for Uniform<T> {
    fn identity() -> Self {
        Self::Empty
    }

    fn combine(self, right: &Self) -> Self {
        match (self, right) {
            (Self::Empty, right) => right.clone(),
            (left, Self::Empty) => left,
            (Self::One(left), Self::One(right)) if left == *right => Self::One(left),
            _ => Self::Mixed,
        }
    }
}

/// Summaries side by side, each combined with its own kind.
macro_rules! tuple_summary {
    ($($name:ident $index:tt),+) => {
        impl<$($name: Summary),+> Summary for ($($name,)+) {
            fn identity() -> Self {
                ($($name::identity(),)+)
            }

            fn combine(self, right: &Self) -> Self {
                ($(self.$index.combine(&right.$index),)+)
            }
        }
    };
}

tuple_summary!(A 0, B 1);
tuple_summary!(A 0, B 1, C 2);
tuple_summary!(A 0, B 1, C 2, D 3);
tuple_summary!(A 0, B 1, C 2, D 3, E 4);
tuple_summary!(A 0, B 1, C 2, D 3, E 4, F 5);

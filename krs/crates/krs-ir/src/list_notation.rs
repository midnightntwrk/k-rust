//! Bracket list notation: cons lists (F6) and K's builtin `List`.
//!
//! A cons-list sort has one empty constructor and one cons constructor whose
//! second field is the list itself: a `#[k::syntax_list]` sort, or the sort of
//! a `#[k::cons_list]` constructors enum. In a term, `[]` is its empty
//! constructor and `[head, ..tail]` its cons constructor applied to the head
//! and the tail, so `[a, b]` is `Cons(a, Cons(b, Empty()))`. At K's builtin
//! `List` the same brackets are the list of their elements: `[a, ..rest, z]`
//! is `ListItem(a) rest ListItem(z)`. The brackets do not name the sort: the
//! position's expected sort does. The parser writes each bracket level as an
//! application of a [`ListNotation`] marker, and semantic analysis replaces
//! it by the terms of the list the position expects; every later phase sees
//! those terms.

use serde::{Deserialize, Serialize};

use crate::FacadeMarker;

/// One level of bracket list notation, before semantic analysis knows the
/// cons-list sort it builds.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ListNotation {
    /// `[head, ..tail]`: the cons constructor of the list, applied to the
    /// head and the tail; at `List`, `ListItem(head) tail`.
    Cons,
    /// `[]`: the empty constructor of the list; at `List`, `.List`.
    Empty,
    /// `[..init, last]`: at `List`, `init ListItem(last)`. A cons list is
    /// built from its front, so it has no such level.
    Snoc,
}

impl ListNotation {
    /// Every level, in stable semantic order.
    pub const ALL: [Self; 3] = [Self::Cons, Self::Empty, Self::Snoc];

    /// The number of operands: the head and the tail of a cons, the init
    /// and the last element of a snoc, none for the empty list.
    #[must_use]
    pub const fn arity(self) -> usize {
        match self {
            Self::Cons | Self::Snoc => 2,
            Self::Empty => 0,
        }
    }

    /// The facade marker the parser writes for the level
    /// (`builtin::__list::cons`).
    #[must_use]
    pub const fn facade_marker(self) -> FacadeMarker {
        FacadeMarker {
            module: "__list",
            name: match self {
                Self::Cons => "cons",
                Self::Empty => "empty",
                Self::Snoc => "snoc",
            },
        }
    }
}

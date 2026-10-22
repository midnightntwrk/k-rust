//! Bracket notation for cons lists (F6).
//!
//! A cons-list sort has one empty constructor and one cons constructor whose
//! second field is the list itself: a `#[k::syntax_list]` sort, or the sort of
//! a `#[k::cons_list]` constructors enum. In a term, `[]` is its empty
//! constructor and `[head, ..tail]` its cons constructor applied to the head
//! and the tail, so `[a, b]` is `Cons(a, Cons(b, Empty()))`. The brackets do
//! not name the sort: the position's expected sort does. The parser writes
//! each bracket level as an application of a [`ListNotation`] marker, and
//! semantic analysis replaces it by the constructor of the cons list the
//! position expects; every later phase sees that constructor.

use serde::{Deserialize, Serialize};

use crate::FacadeMarker;

/// One level of bracket list notation, before semantic analysis knows the
/// cons-list sort it builds.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ListNotation {
    /// `[head, ..tail]`: the cons constructor of the list, applied to the
    /// head and the tail.
    Cons,
    /// `[]`: the empty constructor of the list.
    Empty,
}

impl ListNotation {
    /// Every level, in stable semantic order.
    pub const ALL: [Self; 2] = [Self::Cons, Self::Empty];

    /// The number of operands: the head and the tail of a cons, none for the
    /// empty list.
    #[must_use]
    pub const fn arity(self) -> usize {
        match self {
            Self::Cons => 2,
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
            },
        }
    }
}

//! Edit B of the introduction's specification (plus_succ drops s), generated from ../../plus by scripts/sync-story.py. Do not edit.

use k::builtin::KSequence;
use k::{KItem, Term};

k::sorts! {
    Nat: KItem;
}

// [!region constructors]
#[k::constructors(sort = Nat, result = KResult)]
#[k::precedence((Zero, Succ))]
pub enum NatSyntax {
    #[k::syntax("zero")]
    Zero(),
    #[k::syntax("s({n})")]
    Succ { n: Nat },
}
// [!endregion constructors]

// [!region function]
#[k::function(total, sort = Nat, syntax = "plus({lhs}, {rhs})")]
pub struct Plus {
    pub lhs: Term<Nat>,
    pub rhs: Term<Nat>,
}
// [!endregion function]

// [!region plus-zero]
#[k::equation]
fn plus_zero(k::term![Plus(NatSyntax::Zero(), n)]: Term<Nat>) -> Term<Nat> {
    n
}
// [!endregion plus-zero]

// [!region plus-succ]
#[k::equation]
fn plus_succ(k::term![Plus(NatSyntax::Succ(m), n)]: Term<Nat>) -> Term<Nat> {
    Plus(m, n)
}
// [!endregion plus-succ]

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Nat) -> Self {
        Self { k: k::k![pgm] }
    }
}

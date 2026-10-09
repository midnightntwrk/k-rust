//! The evaluation order of `heat-cool` from strictness: K tutorial lesson 14-D.
//!
//! `#[k::seqstrict]` asks K to generate the heating and cooling rules and the
//! freezers that `heat-cool` writes by hand; both definitions run programs
//! to the same final configuration.

use k::KResult;
use k::builtin::{Bool, Int, KSequence, bool, int};

k::sorts! {
    #[k::bracket("(", ")")]
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence(left add (Add) > left and (And))]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("{lhs} + {rhs}")] #[k::seqstrict]
    Add { lhs: Exp, rhs: Exp },
    #[k::syntax("{lhs} && {rhs}")] #[k::seqstrict]
    And { lhs: Exp, rhs: Exp },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}

k::rules! {
    for Exp;
    use Op::*;

    add: Add { lhs, rhs } => int::add(lhs, rhs)  where lhs: Int, rhs: Int;
    and: And { lhs, rhs } => bool::and(lhs, rhs) where lhs: Bool, rhs: Bool;
}

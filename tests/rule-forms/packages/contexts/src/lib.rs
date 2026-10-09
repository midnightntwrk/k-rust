//! Contexts (KF-021): K tutorial lesson 14-B.
//!
//! A context says where evaluation may happen. `#[k::context(hole = h)]` on
//! a fn whose subject is `Add(e, h)` is K's `context E + HOLE`: K turns it
//! into a heat rule, which moves `h` to the front of the computation when it
//! is not yet a result, and a cool rule, which plugs the result back, and
//! labels them `add-rhs-heat` and `add-rhs-cool`. Compare `heat-cool`,
//! which writes those rules and their freezers by hand, and
//! `heat-cool-strict`, where `#[k::seqstrict]` generates them; all three
//! run programs to the same final configuration.

use k::KResult;
use k::Term;
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
    #[k::syntax("{lhs} + {rhs}")]
    Add { lhs: Exp, rhs: Exp },
    #[k::syntax("{lhs} && {rhs}")]
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

/// `+` evaluates its left operand first: K's `context HOLE + _`.
#[k::context(hole = h)]
fn add_lhs(k::term![Op::Add(h, _)]: Term<Exp>) {}

/// Then its right operand, once the left one is a result.
#[k::context(hole = h)]
#[k::requires(k::is!(KResult, e))]
fn add_rhs(k::term![Op::Add(e, h)]: Term<Exp>) {}

/// `&&` names its result sort, K's `result(Value)`.
#[k::context(hole = h, result = Value)]
fn and_lhs(k::term![Op::And(h, _)]: Term<Exp>) {}

#[k::context(hole = h, result = Value)]
#[k::requires(k::is!(Value, e))]
fn and_rhs(k::term![Op::And(e, h)]: Term<Exp>) {}

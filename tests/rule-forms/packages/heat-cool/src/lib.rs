//! Hand-written heating and cooling (KF-014): K tutorial lesson 14-A.
//!
//! A heat rule moves the subterm its `hole` names to the front of the
//! computation and leaves a freezer behind; a cool rule plugs a finished
//! value back into the freezer's place. K adds "the hole is not yet a
//! result" to every heat rule and "the hole is a result" to every cool rule,
//! so the rules below carry no such guard. `+` evaluates its left operand
//! first: `heat_add_rhs` heats the right operand only once the left one is a
//! result. The `&&` rules name their result sort, `result = Value`, K's
//! `result(Value)`; `Value` holds the same terms as `KResult` here.
//! `heat-cool-strict` gets the same rules from `#[k::seqstrict]`.

use k::KResult;
use k::builtin::{Bool, Int, KSequence, bool, int};

k::sorts! {
    #[k::bracket("(", ")")]
    Exp: k::KItem;
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

/// Freezers: the operand that waits while the other one is evaluated.
#[k::constructors(sort = k::KItem, reference)]
#[rustfmt::skip]
pub enum Freezer {
    #[k::syntax("freezer1({e})", group = "freezer", format = "freezer1({e})")]
    AddRhs { e: k::Term<dyn ExpSort> },
    #[k::syntax("freezer2({e})", group = "freezer", format = "freezer2({e})")]
    AddLhs { e: k::Term<dyn ExpSort> },
    #[k::syntax("freezer3({e})", group = "freezer", format = "freezer3({e})")]
    AndRhs { e: k::Term<dyn ExpSort> },
    #[k::syntax("freezer4({e})", group = "freezer", format = "freezer4({e})")]
    AndLhs { e: k::Term<dyn ExpSort> },
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

k::rules! {
    for Machine;
    use Op::*;

    #[k::rule(heat, hole = h)]
    #[k::requires(k::is!(KResult, e))]
    heat_add_rhs: {
        k: [Add(e, h), ..]
    } => {
        k: [h, Freezer::AddRhs(e), ..]
    };
    #[k::rule(heat, hole = h)]
    heat_add_lhs: {
        k: [Add(h, e), ..]
    } => {
        k: [h, Freezer::AddLhs(e), ..]
    };
    #[k::rule(heat, hole = h, result = Value)]
    #[k::requires(k::is!(Value, e))]
    heat_and_rhs: {
        k: [And(e, h), ..]
    } => {
        k: [h, Freezer::AndRhs(e), ..]
    };
    #[k::rule(heat, hole = h, result = Value)]
    heat_and_lhs: {
        k: [And(h, e), ..]
    } => {
        k: [h, Freezer::AndLhs(e), ..]
    };
}

// A readable machine record matches one computation-cell head, and a cool
// rule matches two items, the value and the freezer, so the cool rules are
// written in the reference form.
#[k::rule(cool, hole = h, label = "cool-add-rhs")]
pub fn cool_add_rhs(
    h: Exp,
    e: Exp,
    k::cells! { k: k::configuration::KCell(h, Freezer::AddRhs(e), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(Op::Add(e, h), ..tail), ..state }
}

#[k::rule(cool, hole = h, label = "cool-add-lhs")]
pub fn cool_add_lhs(
    h: Exp,
    e: Exp,
    k::cells! { k: k::configuration::KCell(h, Freezer::AddLhs(e), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(Op::Add(h, e), ..tail), ..state }
}

#[k::rule(cool, hole = h, result = Value, label = "cool-and-rhs")]
pub fn cool_and_rhs(
    h: Exp,
    e: Exp,
    k::cells! { k: k::configuration::KCell(h, Freezer::AndRhs(e), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(Op::And(e, h), ..tail), ..state }
}

#[k::rule(cool, hole = h, result = Value, label = "cool-and-lhs")]
pub fn cool_and_lhs(
    h: Exp,
    e: Exp,
    k::cells! { k: k::configuration::KCell(h, Freezer::AndLhs(e), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(Op::And(h, e), ..tail), ..state }
}

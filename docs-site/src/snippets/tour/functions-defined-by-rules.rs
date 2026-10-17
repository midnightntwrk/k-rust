//! Peano natural numbers with three functions: total `plus` and `times`, and partial `pred`.

use k::builtin::KSequence;
use k::{KItem, Term};

k::sorts! {
    Nat: KItem;
}

#[k::constructors(sort = Nat, result = KResult)]
#[k::precedence((Zero, Succ))]
pub enum NatSyntax {
    #[k::syntax("zero")]
    Zero(),
    #[k::syntax("s({n})")]
    Succ { n: Nat },
}

// [!region plus]
/// `plus(m, n)` is the sum of `m` and `n`.
#[k::function(total, sort = Nat, syntax = "plus({lhs}, {rhs})")]
pub struct Plus {
    pub lhs: Term<Nat>,
    pub rhs: Term<Nat>,
}

#[k::equation]
fn plus_zero(k::term![Plus(NatSyntax::Zero(), n)]: Term<Nat>) -> Term<Nat> {
    n
}

#[k::equation]
fn plus_succ(k::term![Plus(NatSyntax::Succ(m), n)]: Term<Nat>) -> Term<Nat> {
    NatSyntax::Succ(Plus(m, n))
}
// [!endregion plus]

// [!region pred]
/// `pred(n)` is the number before `n`; `pred(zero)` has no value.
#[k::function(partial, sort = Nat, syntax = "pred({value})")]
pub struct Pred {
    pub value: Term<Nat>,
}

#[k::equation]
fn pred_succ(k::term![Pred(NatSyntax::Succ(n))]: Term<Nat>) -> Term<Nat> {
    n
}
// [!endregion pred]

// [!region times]
/// `times(m, n)` is the product of `m` and `n`.
#[k::function(total, sort = Nat, syntax = "times({lhs}, {rhs})")]
pub struct Times {
    pub lhs: Term<Nat>,
    pub rhs: Term<Nat>,
}

#[k::equation]
fn times_zero(k::term![Times(NatSyntax::Zero(), _)]: Term<Nat>) -> Term<Nat> {
    NatSyntax::Zero()
}

#[k::equation]
fn times_succ(k::term![Times(NatSyntax::Succ(m), n)]: Term<Nat>) -> Term<Nat> {
    Plus(n, Times(m, n))
}
// [!endregion times]

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

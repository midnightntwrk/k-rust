//! Peano natural numbers and answers, with equations whose patterns use
//! variables, a wildcard, and a repeated variable.

use k::builtin::KSequence;
use k::{KItem, Term};

k::sorts! {
    Nat: KItem;
    Answer: KItem;
}

#[k::constructors(sort = Nat, result = KResult)]
#[k::precedence((Zero, Succ))]
pub enum NatSyntax {
    #[k::syntax("zero")]
    Zero(),
    #[k::syntax("s({n})")]
    Succ { n: Nat },
}

// [!region answer]
#[k::constructors(sort = Answer, result = KResult)]
#[k::precedence((Yes, No))]
pub enum AnswerSyntax {
    #[k::syntax("yes")]
    Yes(),
    #[k::syntax("no")]
    No(),
}
// [!endregion answer]

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

// [!region is-zero]
/// `isZero(n)` answers whether `n` is `zero`.
#[k::function(total, sort = Answer, syntax = "isZero({value})")]
pub struct IsZero {
    pub value: Term<Nat>,
}

#[k::equation]
fn is_zero_zero(k::term![IsZero(NatSyntax::Zero())]: Term<Answer>) -> Term<Answer> {
    AnswerSyntax::Yes()
}

#[k::equation]
fn is_zero_succ(k::term![IsZero(NatSyntax::Succ(_))]: Term<Answer>) -> Term<Answer> {
    AnswerSyntax::No()
}
// [!endregion is-zero]

// [!region same]
/// `same(m, n)` is `yes` when `m` and `n` are the same number.
#[k::function(partial, sort = Answer, syntax = "same({lhs}, {rhs})")]
pub struct Same {
    pub lhs: Term<Nat>,
    pub rhs: Term<Nat>,
}

#[k::equation]
fn same_equal(k::term![Same(n, n)]: Term<Answer>) -> Term<Answer> {
    AnswerSyntax::Yes()
}
// [!endregion same]

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Answer) -> Self {
        Self { k: k::k![pgm] }
    }
}

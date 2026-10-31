//! `owise` over a symbolic argument.
//!
//! `isOne(V)` is `true` where `V ==Int 1` and, by its `owise` equation,
//! `false` where no other equation of `isOne` applies. That is a statement
//! about every argument, so over a symbolic `V` the `owise` equation gives
//! `false` only where `V =/=Int 1` is known. `go(V)` rewrites to `V`.
//!
//! - `one-reaches-one`: from `go(V)` with `isOne(V)`, every path reaches `1`.
//!   True: `isOne(V)` holds only at 1.
//! - `one-reaches-two`: the same start reaches `2`. False: a prover must not
//!   prove it. Applying the `owise` equation before the guard of the other is
//!   decided would read `isOne(V)` as `false`, and so prove it vacuously.
//!
//! `pick(V)` rewrites to `1` where `V ==Int 1` and, by its `owise`
//! transition, to `0` where no other transition applies.
//!
//! - `pick-one`: from `pick(V)` with `V ==Int 1`, every path reaches `1`.
//! - `pick-zero`: the same start reaches `0`. False.

use k::builtin::{Bool, Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
    impl Exp for Bool;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Go, Pick))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("go({value})")] Go { value: Int },
    #[k::syntax("pick({value})")] Pick { value: Int },
}

/// `true` at 1 and `false` at every other integer.
#[k::function(total, sort = Bool, syntax = "isOne({value})")]
pub struct IsOne {
    pub value: Term<Int>,
}

#[k::requires(int::eq(value, 1))]
#[k::equation]
fn is_one(k::term![IsOne(value)]: Term<Bool>) -> Term<Bool> {
    true
}

#[k::equation(owise)]
fn is_not_one(k::term![IsOne(_)]: Term<Bool>) -> Term<Bool> {
    false
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

#[k::rule(label = "go")]
fn go(k::term![ExpSyntax::Go { value }]: Term<Exp>) -> Term<Exp> {
    value
}

#[k::rule(label = "pick-one-rule")]
#[k::requires(int::eq(value, 1))]
fn pick_one_rule(k::term![ExpSyntax::Pick { value }]: Term<Exp>) -> Term<Exp> {
    1
}

#[k::rule(owise, label = "pick-other-rule")]
fn pick_other_rule(k::term![ExpSyntax::Pick { .. }]: Term<Exp>) -> Term<Exp> {
    0
}

/// `isOne(V)` holds only at 1, so `go(V)` reaches 1.
#[k::claim(all_paths, label = "one-reaches-one")]
#[k::requires(IsOne(i))]
pub fn one_reaches_one(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Go(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(1, ..tail), ..state }
}

/// False: `go(V)` with `isOne(V)` reaches 1, not 2.
#[k::claim(all_paths, label = "one-reaches-two")]
#[k::requires(IsOne(i))]
pub fn one_reaches_two(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Go(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(2, ..tail), ..state }
}

/// `pick(1)` reaches 1 alone: the `owise` transition does not apply there.
#[k::claim(all_paths, label = "pick-one")]
#[k::requires(int::eq(i, 1))]
pub fn pick_one(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Pick(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(1, ..tail), ..state }
}

/// False: `pick(1)` reaches 1, not 0.
#[k::claim(all_paths, label = "pick-zero")]
#[k::requires(int::eq(i, 1))]
pub fn pick_zero(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Pick(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(0, ..tail), ..state }
}

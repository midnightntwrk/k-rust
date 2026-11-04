//! The definition the front end's mutation checks judge (`tests/kink.rs`,
//! `tests/mutant_theory.rs`): two transitions on one head with complementary guards, two in one
//! nondet group, two on one head ordered by a priority, one on a head of its own, a branching
//! function, a division in a condition (so KRS states its test), and a function only a claim
//! applies (a claim helper).

use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("step({value})")] Step { value: Int },
    #[k::syntax("toss({value})")] Toss { value: Int },
    #[k::syntax("other({value})")] Other { value: Int },
    #[k::syntax("half({value})")] Half { value: Int },
    #[k::syntax("go({value})")] Go { value: Int },
    #[k::syntax("pick({value})")] Pick { value: Int },
    #[k::syntax("done({value})")] Done { value: Int },
}

#[k::rule]
#[k::requires(int::lt(value, 0))]
fn step_neg(k::term![ExpSyntax::Step { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Done(0)
}

#[k::rule]
#[k::requires(int::ge(value, 0))]
fn step_nonneg(k::term![ExpSyntax::Step { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Done(Clamp(value))
}

#[k::rule(nondet = toss)]
fn toss_heads(k::term![ExpSyntax::Toss { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Done(1)
}

#[k::rule(nondet = toss)]
fn toss_tails(k::term![ExpSyntax::Toss { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Done(0)
}

#[k::rule(priority = 40)]
fn pick_first(k::term![ExpSyntax::Pick { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Done(1)
}

#[k::rule]
fn pick_second(k::term![ExpSyntax::Pick { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Done(2)
}

#[k::rule]
fn other(k::term![ExpSyntax::Other { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Done(value)
}

#[k::rule]
#[k::requires(10 / value > 1)]
fn half(k::term![ExpSyntax::Half { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Done(1)
}

#[k::function(total, internal)]
pub fn Clamp(value: Term<Int>) -> Term<Int> {
    if value < 0 { 0 } else if value > 255 { 255 } else { value }
}

#[k::function(total, internal)]
pub fn Expected(value: Term<Int>) -> Term<Int> {
    value + 1
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

#[k::claim(all_paths, label = "other-done")]
pub fn other_done(
    i: Term<Int>,
    k::cells! { k: k::configuration::KCell(ExpSyntax::Other(i), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(ExpSyntax::Done(Expected(i)), ..tail), ..state }
}

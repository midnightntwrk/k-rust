//! A matching-logic predicate is not a transition condition.

use k::builtin::{Int, KSequence, int};
use k::ml;
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
}

#[k::function(partial, sort = Int, syntax = "half({value})")]
pub struct Half {
    pub value: Term<Int>,
}

#[k::equation]
#[k::requires(int::eq(int::rem(value, 2), 0))]
fn half_even(k::term![Half(value)]: Term<Int>) -> Term<Int> {
    int::div(value, 2)
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

#[k::rule(label = "step")]
#[k::requires(ml::not(ml::equals(a, 0)))]
fn step(
    a: Term<Int>,
    k::cells! { k: k::configuration::KCell(a, tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(0, ..tail), ..state }
}

//! `ml::equals` operands share a sort: `Left` and `Right` have two least
//! common supersorts, so no one sort is theirs.

use k::builtin::{Int, KSequence, int};
use k::ml;
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
    Both1;
    Both2;
    Left: Both1 + Both2;
    Right: Both1 + Both2;
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

/// The computation that remains.
#[k::function(partial, sort = KSequence, syntax = "rest({value})")]
pub struct Rest {
    pub value: Term<Int>,
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

#[k::claim(all_paths, label = "probe")]
#[k::requires(ml::equals(l, r))]
fn probe(
    l: Term<Left>,
    r: Term<Right>,
    k::cells! { k: k::configuration::KCell(l, r, tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(l, r, ..tail), ..state }
}

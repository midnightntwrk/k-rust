//! An existential cannot reuse the name of a value the rule matched.

use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
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

#[k::rule(label = "replace")]
#[k::exists(x: Int)]
pub fn replace(
    x: Term<Int>,
    k::cells! { k: k::configuration::KCell(x, tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(x, ..tail), ..state }
}

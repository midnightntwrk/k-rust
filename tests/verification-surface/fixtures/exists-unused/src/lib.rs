//! An existential that neither the result nor the ensures condition mentions declares nothing.

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

#[k::rule(label = "zero-to-one")]
#[k::exists(x: Int)]
pub fn zero_to_one(
    k::cells! { k: k::configuration::KCell(0, tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(1, ..tail), ..state }
}

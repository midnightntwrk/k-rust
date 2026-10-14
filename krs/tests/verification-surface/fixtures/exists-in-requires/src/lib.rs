//! An existential names a value the step creates, so `requires` cannot test it.

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

#[k::rule(label = "zero-to-unknown")]
#[k::requires(int::gt(x, 0))]
#[k::exists(x: Int)]
pub fn zero_to_unknown(
    k::cells! { k: k::configuration::KCell(0, tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(x, ..tail), ..state }
}

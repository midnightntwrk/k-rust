//! A transition with an ensures condition and no existential builds for LLVM,
//! which ignores the condition, with a warning.

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

#[k::rule(label = "count-down")]
#[k::ensures(int::ge(n, 0))]
pub fn count_down(
    n: Term<Int>,
    k::cells! { k: k::configuration::KCell(n, tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(int::sub(n, 1), ..tail), ..state }
}

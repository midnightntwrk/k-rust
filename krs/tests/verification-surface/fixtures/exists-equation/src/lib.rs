//! An equation computes a function's value; it cannot introduce a symbolic one.

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

#[k::function(total, sort = Int, syntax = "pick({value})")]
pub struct Pick {
    pub value: Term<Int>,
}

#[k::equation]
#[k::exists(x: Int)]
fn pick(k::term![Pick(_)]: Term<Int>) -> Term<Int> {
    x
}

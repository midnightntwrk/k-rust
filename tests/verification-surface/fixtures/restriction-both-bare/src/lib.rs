//! Bare `concrete` and bare `symbolic` together: no binder can be both.

use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
}

#[k::function(total, sort = Int, syntax = "h({value})", smtlib = "probeH")]
pub struct H {
    pub value: Term<Int>,
}

#[k::simplification(concrete, symbolic)]
fn h_both(k::term![H(x)]: Term<Int>) -> Term<Int> {
    int::add(x, 1)
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

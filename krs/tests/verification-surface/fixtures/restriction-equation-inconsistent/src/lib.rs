//! One equation of `h` is `concrete` and the other is not: K requires all or none.

use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
}

#[k::function(total, sort = Int, syntax = "h({value})")]
pub struct H {
    pub value: Term<Int>,
}

#[k::equation(concrete)]
fn h_zero(k::term![H(0)]: Term<Int>) -> Term<Int> {
    1
}

#[k::equation(owise)]
fn h_other(k::term![H(x)]: Term<Int>) -> Term<Int> {
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

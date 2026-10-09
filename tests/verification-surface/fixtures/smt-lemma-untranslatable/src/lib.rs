//! An `smt_lemma` over a function Z3 cannot see: `h` has no `smtlib` or `smt_hook`.

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

#[k::simplification(smt_lemma)]
fn h_lemma(k::term![H(x)]: Term<Int>) -> Term<Int> {
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

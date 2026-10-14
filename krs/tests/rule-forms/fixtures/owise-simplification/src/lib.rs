//! `owise` has no meaning on a simplification.

use k::Term;
use k::builtin::{Int, KSequence};

k::sorts! {
    Pgm: k::KItem;
}

#[k::constructors(sort = Pgm, result = k::KResult)]
#[k::precedence((Toss, Heads, Tails))]
#[rustfmt::skip]
pub enum Coin {
    #[k::syntax("toss")] Toss(),
    #[k::syntax("heads")] Heads(),
    #[k::syntax("tails")] Tails(),
}

#[k::function(total, sort = Int, syntax = "choose({value})")]
pub struct Choose {
    pub value: Term<Int>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Pgm) -> Self {
        Self { k: k::k![pgm] }
    }
}

#[k::simplification(owise)]
fn choose_zero(k::term![Choose(0)]: Term<Int>) -> Term<Int> {
    0
}

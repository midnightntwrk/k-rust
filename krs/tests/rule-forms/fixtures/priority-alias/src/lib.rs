//! An alias clause is a static rule and has no priority.

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

#[k::constructors(sort = Pgm, result = k::KResult)]
#[k::precedence((Zero))]
pub enum Static {
    #[k::syntax("zero")]
    #[k::alias]
    Zero(),
}

#[k::alias(priority = 40)]
fn zero(k::term![Static::Zero]: Term<Pgm>) -> Term<Pgm> {
    k::term![Coin::Heads()]
}

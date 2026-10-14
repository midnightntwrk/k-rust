//! Two functions declare `smtlib = "probe"`: Z3 would treat them as one.

use k::builtin::{Int, KSequence};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
    impl Exp for Int;
}

#[k::function(total, sort = Int, syntax = "first({value})", smtlib = "probe")]
pub struct First {
    pub value: Term<Int>,
}

#[k::function(total, sort = Int, syntax = "second({value})", smtlib = "probe")]
pub struct Second {
    pub value: Term<Int>,
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

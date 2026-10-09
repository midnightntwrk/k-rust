//! A let-bound name is visible only in the rest of its block.

use k::KResult;
use k::Term;
use k::builtin::{Bool, Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Swap, Pair))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("swap({e})")]
    Swap { e: Exp },
    #[k::syntax("pair({fst}, {snd})")]
    Pair { fst: Exp, snd: Exp },
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

/// The second component of a pair.
#[k::function(partial, sort = Exp, syntax = "second({e})")]
pub struct Second {
    pub e: Term<Exp>,
}

/// A Bool marker, so `Bool` is used.
#[k::function(total, sort = Bool, syntax = "flag({e})")]
pub struct Flag {
    pub e: Term<Exp>,
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    swap: Swap { e } => Pair({ let Pair(x, y) = e; y }, x);
}

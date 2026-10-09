//! A desugar production that no clause expands.

use k::Term;
use k::builtin::KSequence;

k::sorts! {
    Pgm: k::KItem;
}

#[k::constructors(sort = Pgm, result = k::KResult)]
#[k::precedence((Heads, Tails))]
#[rustfmt::skip]
pub enum Coin {
    #[k::syntax("heads")] Heads(),
    #[k::syntax("tails")] Tails(),
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
#[k::precedence((Flip))]
pub enum Static {
    #[k::syntax("flip")]
    #[k::desugar]
    Flip(),
}

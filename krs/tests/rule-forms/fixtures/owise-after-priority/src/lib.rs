//! A transition at priority 250 overlaps an `owise` one: `owise` comes after
//! every other transition that applies, but the emitted `owise` attribute
//! fixes no rank against priorities 200 to 254, so the two have no single
//! order.

use k::Term;
use k::builtin::KSequence;

k::sorts! {
    Pgm: k::KItem;
}

#[k::constructors(sort = Pgm, result = k::KResult)]
#[k::precedence((Flip, Low, High))]
#[rustfmt::skip]
pub enum Coin {
    #[k::syntax("flip")] Flip(),
    #[k::syntax("low")] Low(),
    #[k::syntax("high")] High(),
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

#[k::rule(priority = 250)]
fn flip_low(k::term![Coin::Flip()]: Term<Pgm>) -> Term<Pgm> {
    k::term![Coin::Low()]
}

#[k::rule(owise)]
fn flip_high(k::term![Coin::Flip()]: Term<Pgm>) -> Term<Pgm> {
    k::term![Coin::High()]
}

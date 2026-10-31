//! A transition at priority 250 overlaps an `owise` one: `owise` applies only
//! where no other rule applies, so no rule it meets is ranked with or after it.

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

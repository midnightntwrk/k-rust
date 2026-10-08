//! Rules at different priorities never compete, so one group cannot mix them.

use k::Term;
use k::builtin::{Int, KSequence};

k::sorts! {
    Pgm: k::KItem;
}

#[k::constructors(sort = Pgm, result = k::KResult)]
#[k::precedence((Toss, Heads, Tails, Flip, High))]
#[rustfmt::skip]
pub enum Coin {
    #[k::syntax("toss")] Toss(),
    #[k::syntax("heads")] Heads(),
    #[k::syntax("tails")] Tails(),
    #[k::syntax("flip")] Flip(),
    #[k::syntax("high")] High(),
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

#[k::rule(nondet = toss)]
fn heads(k::term![Coin::Toss()]: Term<Pgm>) -> Term<Pgm> {
    k::term![Coin::Heads()]
}

#[k::rule(owise, nondet = toss)]
fn tails(k::term![Coin::Toss()]: Term<Pgm>) -> Term<Pgm> {
    k::term![Coin::Tails()]
}

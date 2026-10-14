//! `name @ ..` is a remainder, which binds only in a sequence, collection, or cells! pattern.

use k::Term;
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    impl Exp for Int;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Pair, Dup))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("pair({fst}, {snd})")]
    Pair { fst: Exp, snd: Exp },
    #[k::syntax("dup({e})")]
    Dup { e: Exp },
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

#[k::rule]
fn dup(k::term![ExpSyntax::Dup(p @ ..)]: Term<Exp>) -> Term<Exp> {
    p
}

//! K tests `k::matches!(t, P)` with a generated equation that matches `P` at
//! the root of its argument, so alternatives below a symbol of `P`,
//! `Pair(_, Red() | Green())`, do not compile there; write them at the root.

use k::KResult;
use k::Term;
use k::builtin::{Bool, Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Pair, Red, Green))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("pair({fst}, {snd})")]
    Pair { fst: Exp, snd: Exp },
    #[k::syntax("red()")]
    Red(),
    #[k::syntax("green()")]
    Green(),
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

#[k::function(partial, sort = Bool, syntax = "warmPair({e})")]
pub struct WarmPair {
    pub e: Term<Exp>,
}

#[k::equation]
fn warm_pair(k::term![WarmPair(e)]: Term<Bool>) -> Term<Bool> {
    k::matches!(e, ExpSyntax::Pair(_, ExpSyntax::Red() | ExpSyntax::Green()))
}

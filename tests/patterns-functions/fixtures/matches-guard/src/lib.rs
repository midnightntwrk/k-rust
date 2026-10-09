//! K's `:=K` has no guard.

use k::KResult;
use k::builtin::bool::{self, Bool};
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((IsPair, Pair, Unit))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("isPair({e})")]
    IsPair { e: Exp },
    #[k::syntax("pair({fst}, {snd})")]
    Pair { fst: Exp, snd: Exp },
    #[k::syntax("unit()")]
    Unit(),
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

k::rules! {
    for Exp;
    use ExpSyntax::*;

    #[k::requires(k::matches!(e, Pair(x, _) if bool::eq(x, true)))]
    is_pair: IsPair { e } => true;
}

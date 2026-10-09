//! A pattern name read once is a wildcard.

use k::KResult;
use k::builtin::{Bool, Int, KSequence};

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

    #[k::requires(k::matches!(e, Pair(x, _)))]
    is_pair: IsPair { e } => true;
}

//! The pinned native prover cannot resolve K's `:=K` in a claim, so a claim cannot test a shape with `k::matches!`.

use k::KResult;
use k::Term;
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

    is_pair: IsPair { e } => true;
}

#[k::claim(all_paths, label = "is-pair-claim")]
#[k::requires(k::matches!(e, crate::ExpSyntax::Pair(_, _)))]
pub fn is_pair_claim(
    e: Term<Exp>,
    k::cells! { k: k::configuration::KCell(crate::ExpSyntax::IsPair(e), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(true, ..tail), ..state }
}

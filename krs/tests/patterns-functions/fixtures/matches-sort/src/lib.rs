//! A pattern whose sort cannot meet the subject's sort makes the test always false.

use k::KResult;
use k::builtin::{Bool, Int, KSequence};

k::sorts! {
    Exp;
    Color;
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

#[k::constructors(sort = Color, result = KResult)]
#[k::precedence((Red))]
#[rustfmt::skip]
pub enum ColorSyntax {
    #[k::syntax("red()")]
    Red(),
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

    #[k::requires(k::matches!(e, ColorSyntax::Red()))]
    is_pair: IsPair { e } => true;
}

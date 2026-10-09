//! Or-patterns combine terms, not remainders.

use k::KResult;
use k::builtin::{Bool, Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Pair, Pick, Red, Green))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("pair({fst}, {snd})")]
    Pair { fst: Exp, snd: Exp },
    #[k::syntax("pick({p})")]
    Pick { p: Exp },
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

#[k::rule(label = "drop-red")]
pub fn drop_red(
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Red(), tail @ .. | ExpSyntax::Green()),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        ..state
    }
}

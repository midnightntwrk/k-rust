//! The hole names one subterm; a left side that binds it twice names two.

use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp: k::KItem;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence(left (Add))]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("{lhs} + {rhs}")]
    Add { lhs: Exp, rhs: Exp },
}

#[k::constructors(sort = k::KItem, reference)]
#[rustfmt::skip]
pub enum Freezer {
    #[k::syntax("freezer({e})", group = "freezer", format = "freezer({e})")]
    AddRhs { e: k::Term<dyn ExpSort> },
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
    for Machine;
    use Op::*;

    #[k::rule(heat, hole = h)]
    heat_twice: { k: [Add(h, h), ..] } => { k: [h, Freezer::AddRhs(h), ..] };
}

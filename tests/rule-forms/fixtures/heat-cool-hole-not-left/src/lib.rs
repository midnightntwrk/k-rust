//! A heat rule must match its hole on the left side: K adds a condition on it.

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

    #[k::rule(heat, hole = x)]
    heat_add_rhs: { k: [Add(e, h), ..] } => { k: [h, Freezer::AddRhs(e), ..] };
}

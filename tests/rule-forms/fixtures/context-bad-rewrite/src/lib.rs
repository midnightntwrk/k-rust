//! A context may rewrite only its hole, to a term that contains it.

use k::builtin::{Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Inc, Wrap) > left (Add))]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("++ {target}")]
    Inc { target: Exp },
    #[k::syntax("wrap({inner})")]
    Wrap { inner: Exp },
    #[k::syntax("{lhs} + {rhs}")]
    Add { lhs: Exp, rhs: Exp },
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

#[k::context(hole = h)]
fn increment_target(k::term![Op::Inc(k::rewrite!(h => Op::Wrap(Op::Add(1, 2))))]: Term<Exp>) {}

//! A context names the subterm K evaluates with `hole = x`, which its
//! pattern must bind.

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

#[k::context(hole = x)]
fn add_rhs(k::term![Op::Add(e, h)]: Term<Exp>) {}

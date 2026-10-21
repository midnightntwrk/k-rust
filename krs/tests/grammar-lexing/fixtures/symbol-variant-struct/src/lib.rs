//! `Op::Add` derives `opAdd`, the symbol of the struct `OpAdd`: the pair is
//! rejected, and neither production is renamed to make room.

use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Add))]
pub enum Op {
    #[k::syntax("{lhs} + {rhs}")]
    Add { lhs: Exp, rhs: Exp },
}

#[k::constructor(sort = Exp, syntax = "plus({lhs}, {rhs})")]
pub struct OpAdd {
    pub lhs: k::Term<Exp>,
    pub rhs: k::Term<Exp>,
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

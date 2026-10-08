//! An overload has its target's arity: `LvalField` drops the field.

use k::KResult;
use k::builtin::{Id, KSequence};

k::sorts! {
    Exp;
    LVal: Exp;
    impl LVal for Id;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Dot))]
pub enum ExpSyntax {
    #[k::syntax("{base}.{field}")]
    Dot { base: Exp, field: Id },
}

#[k::constructors(sort = LVal, result = KResult)]
#[k::precedence((LvalField))]
pub enum LValSyntax {
    #[k::syntax("{base}.", overload = ExpSyntax::Dot)]
    LvalField { base: LVal },
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

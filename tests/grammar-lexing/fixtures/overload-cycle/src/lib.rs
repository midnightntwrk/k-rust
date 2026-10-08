//! Overload targets lead to one root: two productions that name each other
//! have none.

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
    #[k::syntax("{base}.{field}", overload = LValSyntax::LvalDot)]
    Dot { base: Exp, field: Id },
}

#[k::constructors(sort = LVal, result = KResult)]
#[k::precedence((LvalDot))]
pub enum LValSyntax {
    #[k::syntax("{base}.{field}", overload = ExpSyntax::Dot)]
    LvalDot { base: LVal, field: Id },
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

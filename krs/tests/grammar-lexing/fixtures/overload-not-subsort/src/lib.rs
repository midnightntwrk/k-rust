//! An overload specialises its target: the `Id` field of `LvalDot` is not a
//! subsort of the `Int` field of `ExpSyntax::Dot`.

use k::KResult;
use k::builtin::{Id, Int, KSequence};

k::sorts! {
    Exp;
    LVal: Exp;
    impl LVal for Id;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Dot))]
pub enum ExpSyntax {
    #[k::syntax("{base}.{field}")]
    Dot { base: Exp, field: Int },
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

//! The function `IsExp` derives `isExp`, which K generates as the sort
//! predicate of `Exp`.

use k::Term;
use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Zero))]
pub enum ExpSyntax {
    #[k::syntax("zero")]
    Zero(),
}

#[k::function(total, sort = Int, syntax = "isExp({value})")]
pub struct IsExp {
    pub value: Term<Exp>,
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

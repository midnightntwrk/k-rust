//! Two explicit symbols with one final component name one emitted symbol,
//! `same`: an explicit name collides like any other.

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
    #[k::symbol("first::Same")]
    #[k::syntax("zero")]
    Zero(),
}

#[k::symbol("second::Same")]
#[k::constructor(sort = Exp, syntax = "one")]
pub struct One;

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

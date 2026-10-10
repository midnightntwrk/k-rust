//! The `overload` fixture without the key.
//!
//! Without `overload`, `ExpSyntax::Dot` and `LValSyntax::Dot` are two
//! unrelated productions with the same text, so `a.b`, whose base is an `LVal`
//! and therefore also an `Exp`, has two parses and both routes reject it.
//! `1.b` still has one parse.

use k::KResult;
use k::builtin::{Id, Int, KSequence};

k::sorts! {
    Exp;
    LVal: Exp;
    impl LVal for Id;
    impl Exp for Int;
    Kind: Exp + KResult;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Dot))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("{base}.{field}")]
    Dot { base: Exp, field: Id },
}

#[k::constructors(sort = LVal, result = KResult)]
#[k::precedence((Dot))]
#[rustfmt::skip]
pub enum LValSyntax {
    #[k::syntax("{base}.{field}")]
    Dot { base: LVal, field: Id },
}

#[k::constructors(sort = Kind, result = KResult)]
#[k::precedence((IsValue))]
#[rustfmt::skip]
pub enum Kinds {
    #[k::syntax("value")]
    IsValue(),
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
    for Exp;
    use ExpSyntax::*;

    value: Dot { base, field: _ } => Kinds::IsValue() where base: Int;
}

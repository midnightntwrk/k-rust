//! `overload` says that one production specialises another.
//!
//! `a.b` reads as an `Exp` field access and as an `LVal` field access: the two
//! productions have the same text in different sorts. `overload =
//! ExpSyntax::Dot` puts `LValSyntax::Dot` in the family of
//! `ExpSyntax::Dot`, so parsing picks the most specific production,
//! `LValSyntax::Dot`, and the rule `lval` fires on `a.b`. `1.b` has a base
//! that is not an `LVal`, so it parses as `ExpSyntax::Dot`. Both definitions
//! carry K's overload axiom. The two variants share the name `Dot`, so each
//! symbol takes its enum's name: `expSyntaxDot` and `lValSyntaxDot`.

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
    /// The same `.` syntax, but an `LVal` when its base is an `LVal`.
    #[k::syntax("{base}.{field}", overload = ExpSyntax::Dot)]
    Dot { base: LVal, field: Id },
}

#[k::constructors(sort = Kind, result = KResult)]
#[k::precedence((IsLval, IsValue))]
#[rustfmt::skip]
pub enum Kinds {
    #[k::syntax("lvalue")]
    IsLval(),
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

k::rules! {
    for Exp;
    use LValSyntax::*;

    lval: Dot { base: _, field: _ } => Kinds::IsLval();
}

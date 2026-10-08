//! Members of one overload family are one head for the overlap check: K's
//! overload axioms make `dot(inj(L), F)` equal to `inj(lvalDot(L, F))`, so a
//! rule on `Dot` whose base is an `LVal` and a rule on `LvalDot` both apply
//! to `a.b`.

use k::KResult;
use k::builtin::{Id, KSequence};

k::sorts! {
    Exp;
    LVal: Exp;
    impl LVal for Id;
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
#[k::precedence((LvalDot))]
#[rustfmt::skip]
pub enum LValSyntax {
    #[k::syntax("{base}.{field}", overload = ExpSyntax::Dot)]
    LvalDot { base: LVal, field: Id },
}

#[k::constructors(sort = Kind, result = KResult)]
#[k::precedence((General, Specific))]
#[rustfmt::skip]
pub enum Kinds {
    #[k::syntax("general")]
    General(),
    #[k::syntax("specific")]
    Specific(),
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

    general: Dot { base, field: _ } => Kinds::General() where base: LVal;
}

k::rules! {
    for Exp;
    use LValSyntax::*;

    specific: LvalDot { base: _, field: _ } => Kinds::Specific();
}

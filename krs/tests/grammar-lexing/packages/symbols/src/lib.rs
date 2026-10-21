//! A production's K symbol depends only on its own declaration.
//!
//! An enum variant is `lowerCamel(Enum)` + `Variant` whatever else the
//! definition declares: `Ops::Dot` is `opsDot` and `Other::Dot` is
//! `otherDot`, and `Ops::Solo`, whose name nothing else shares, is still
//! `opsSolo`. A struct keeps its own name (`Plain` is `plain`), and
//! `#[k::symbol("symbols::Plus")]` on `Ops::Add` names it `plus`.

use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Dot, Solo, Add))]
#[rustfmt::skip]
pub enum Ops {
    #[k::syntax("{lhs} . {rhs}")]
    Dot { lhs: Exp, rhs: Exp },
    #[k::syntax("solo")]
    Solo(),
    #[k::symbol("symbols::Plus")]
    #[k::syntax("{lhs} + {rhs}")]
    Add { lhs: Exp, rhs: Exp },
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Dot))]
#[rustfmt::skip]
pub enum Other {
    #[k::syntax("{lhs} ; {rhs}")]
    Dot { lhs: Exp, rhs: Exp },
}

#[k::constructor(sort = Exp, syntax = "plain")]
pub struct Plain;

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

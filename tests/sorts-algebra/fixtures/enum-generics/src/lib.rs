//! Generics on an enum family, whose K parameters would span productions.

use k::builtin::{Bool, Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Go))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("go({n})")]
    Go { n: Int },
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

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Boxed))]
#[rustfmt::skip]
pub enum Boxes<S: ?Sized> {
    #[k::syntax("boxed({value})")]
    Boxed { value: Term<S> },
}

//! A declared sort must be accepted by every occurrence of its binder.

use k::Term;
use k::builtin::{Bool, Int, KSequence};

k::sorts! {
    Exp;
    impl Exp for Int;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[k::precedence((Pair, Wrap))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("pair({left}, {right})")]
    Pair { left: Exp, right: Exp },
    #[k::syntax("wrap({value})")]
    Wrap { value: Exp },
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

#[k::rule]
fn unwrap(value: Term<Bool>, k::term![ExpSyntax::Wrap { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Wrap { value }
}

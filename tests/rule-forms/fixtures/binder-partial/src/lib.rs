//! A term sentence declares no binders or all of them; narrowing one binder does not list only that one.

use k::Term;
use k::builtin::{Int, KSequence};

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
fn swap(left: Term<Int>, k::term![ExpSyntax::Pair { left, right }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Pair {
        left: right,
        right: left,
    }
}

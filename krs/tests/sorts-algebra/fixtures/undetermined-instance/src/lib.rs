//! A term whose instance K cannot determine from its arguments.

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

#[k::function(total, sort = Bool, syntax = "same({left}, {right})")]
pub struct Same<S: ?Sized> {
    pub left: Term<S>,
    pub right: Term<S>,
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    #[k::requires(crate::Same { left: n, right: true })]
    go: Go(n) => n;
}

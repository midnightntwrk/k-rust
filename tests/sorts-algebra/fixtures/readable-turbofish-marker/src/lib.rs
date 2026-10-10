//! A readable clause whose turbofish names a sort marker instead of the sort.

use k::builtin::{Bool, KSequence};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Pick))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("pick({cond}, {first}, {second})")]
    Pick { cond: Bool, first: Exp, second: Exp },
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

#[k::function(total, sort = S, syntax = "choose({cond}, {then_branch}, {else_branch})")]
pub struct Choose<S: ?Sized> {
    pub cond: Term<Bool>,
    pub then_branch: Term<S>,
    pub else_branch: Term<S>,
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    pick: Pick(c, x, y) => crate::Choose::<dyn ExpSort> { cond: c, then_branch: x, else_branch: y };
}

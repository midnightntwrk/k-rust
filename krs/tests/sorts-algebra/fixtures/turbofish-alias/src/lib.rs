//! A reference-layer turbofish that names a sort's alias instead of its sort marker.

use k::builtin::{Bool, KSequence};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Go))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("go({b})")]
    Go { b: Bool },
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

#[k::equation]
fn choose_true(
    k::term![Choose::<Exp> { cond: true, then_branch: a, else_branch: _ }]: Term<Exp>,
) -> Term<Exp> {
    a
}

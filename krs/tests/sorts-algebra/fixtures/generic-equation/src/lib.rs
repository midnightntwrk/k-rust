//! A generic equation: K rules never quantify over sorts.

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

#[k::function(total, sort = S, syntax = "choose({cond}, {then_branch}, {else_branch})")]
pub struct Choose<S: ?Sized> {
    pub cond: Term<Bool>,
    pub then_branch: Term<S>,
    pub else_branch: Term<S>,
}

#[k::equation]
fn choose_true<S: ?Sized>(
    k::term![Choose::<S> { cond: true, then_branch: a, else_branch: _ }]: Term<S>,
) -> Term<S> {
    a
}

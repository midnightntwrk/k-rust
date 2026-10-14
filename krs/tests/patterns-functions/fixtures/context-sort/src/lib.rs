//! A function-context binder declared at a sort its cell does not have.

use k::KResult;
use k::Term;
use k::builtin::KSequence;
use k::builtin::int::{self, Int};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((ReadBar))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("readBar()")]
    ReadBar(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub bar: Int,
    #[k::cell]
    pub baz: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            bar: 42,
            baz: 0,
        }
    }
}

#[k::function(total, sort = Int, syntax = "barPlus({n})")]
pub struct BarPlus {
    pub n: Term<Int>,
}

#[k::equation]
fn bar_plus(
    n: Term<Int>,
    b: Term<k::builtin::bool::Bool>,
    k::term![BarPlus(n)]: Term<Int>,
    k::cells! {
        bar: k::configuration::Cell(b),
        ..
    }: Machine,
) -> Term<Int> {
    n
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    read: ReadBar() => crate::BarPlus(1);
}

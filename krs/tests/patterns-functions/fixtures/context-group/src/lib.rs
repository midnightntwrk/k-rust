//! A function context that reads a whole nested cell.

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

/// A nested cell with one leaf.
#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub bar: Int,
    #[k::cell]
    pub baz: Int,
    #[k::cell(nested)]
    pub frame: Frame,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            bar: 42,
            baz: 0,
            frame: Frame { pc: 0 },
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
    f: crate::Frame,
    k::term![BarPlus(n)]: Term<Int>,
    k::cells! {
        frame: f,
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

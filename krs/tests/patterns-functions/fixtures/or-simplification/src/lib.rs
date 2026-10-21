//! A simplification rewrites one term, and `Red() | Green()` in its
//! left-hand side is not one; write one simplification per alternative.

use k::KResult;
use k::Term;
use k::builtin::{Bool, Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Red, Green))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("red()")]
    Red(),
    #[k::syntax("green()")]
    Green(),
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

#[k::function(partial, sort = Int, syntax = "code({c})")]
pub struct Code {
    pub c: Term<Exp>,
}

#[k::simplification]
fn code_red_green(
    k::term![Code(ExpSyntax::Red() | ExpSyntax::Green())]: Term<Int>,
) -> Term<Int> {
    1
}

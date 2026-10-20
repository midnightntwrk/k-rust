//! An alias over alternatives in an equation, `op @ (Red() | Green())`, puts
//! them below `#as`, but an equation's alternatives compile only at the root
//! of an argument; `(op @ Red()) | (op @ Green())` means the same and does.

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

#[k::function(partial, sort = Exp, syntax = "warm({c})")]
pub struct Warm {
    pub c: Term<Exp>,
}

#[k::equation]
fn warm_red_green(
    k::term![Warm(op @ (ExpSyntax::Red() | ExpSyntax::Green()))]: Term<Exp>,
) -> Term<Exp> {
    op
}

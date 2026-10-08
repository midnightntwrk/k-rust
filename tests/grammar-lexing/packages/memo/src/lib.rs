//! `memo` is K's memoization hint on a function.
//!
//! The Haskell backend may cache a memo function's results; the LLVM backend
//! and k-rust accept the hint and ignore it, so `compute 3` evaluates
//! `square(3)` to `9` on both routes, and both KOREs carry `memo{}()` on the
//! function's symbol.

use k::builtin::{Int, KSequence, int};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Compute))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("compute {value}")]
    Compute { value: Exp },
}

#[k::function(total, memo, sort = Int, syntax = "square({value})")]
pub struct Square {
    pub value: Term<Int>,
}

#[k::equation]
fn square(k::term![Square(value)]: Term<Int>) -> Term<Int> {
    int::mul(value, value)
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

k::rules! {
    for Exp;
    use ExpSyntax::*;

    compute: Compute { value } => crate::Square(value) where value: Int;
}

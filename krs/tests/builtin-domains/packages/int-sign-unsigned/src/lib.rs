//! A rule literal `-1` in a package whose programs use unsigned literals.
//!
//! With `int-literals = "unsigned"`, a program cannot write `-1`, but the rules
//! can: `<NS>` imports K's signed `INT-SYNTAX` whenever Int occurs, so `-1`
//! lexes as one Int token although the package uses no `int::` operation.

use k::KResult;
use k::builtin::{Bool, Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((MinusOne, Check))]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("minusOne()")]
    MinusOne(),
    #[k::syntax("check({value})")] #[k::strict]
    Check { value: Exp },
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
    use Op::*;

    minus_one      : MinusOne() => -1;
    check_minus_one: Check(-1)  => true;
    check_one      : Check(1)   => false;
}

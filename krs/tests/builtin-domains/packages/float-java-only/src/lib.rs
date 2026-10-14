//! Float sentences that only Java K evaluates (KF-033).
//!
//! The pinned native frontend folds every FLOAT-hooked application whose
//! arguments are all tokens, which needs MPFR, and k-rust evaluates only the
//! binary32 and binary64 formats. KRS records both as capability requirements,
//! so the native routes refuse this definition before compiling it, while Java
//! K's LLVM backend runs it.

use k::builtin::{Bool, Float, KSequence, float};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool;
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

/// A ground application: `1.0 /Float 2.0` has only token arguments.
#[k::function(total, sort = Bool, syntax = "isHalf({a})")]
pub struct IsHalf {
    pub a: Term<Float>,
}

#[k::equation]
fn is_half(k::term![IsHalf(a)]: Term<Bool>) -> Term<Bool> {
    float::eq(a, float::div(1.0, 2.0))
}

/// A binary128 token, `1.0p113x15`.
#[k::function(total, sort = Bool, syntax = "belowOne({a})")]
pub struct BelowOne {
    pub a: Term<Float>,
}

#[k::equation]
fn below_one(k::term![BelowOne(a)]: Term<Bool>) -> Term<Bool> {
    float::lt(a, 1.0p113x15)
}

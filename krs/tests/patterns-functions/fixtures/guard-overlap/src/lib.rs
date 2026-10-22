//! A sign whose guards both admit 0: `value >= 0` and `value <= 0` bound
//! the argument on one side each, so no finite set of arguments decides
//! them, but both hold at 0 with different results.

use k::Term;
use k::builtin::{Int, KSequence, int};

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::k![] }
    }
}

/// The sign of an integer.
#[k::function(total, internal)]
pub fn Sign(value: Term<Int>) -> Term<Int>;

#[k::requires(int::ge(value, 0))]
#[k::equation]
fn sign_nonnegative(k::term![Sign(value)]: Term<Int>) -> Term<Int> {
    k::term![1]
}

#[k::requires(int::le(value, 0))]
#[k::equation]
fn sign_nonpositive(k::term![Sign(value)]: Term<Int>) -> Term<Int> {
    k::term![-1]
}

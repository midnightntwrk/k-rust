//! K tutorial lesson 1.21 in the readable layer.
//!
//! `#[k::exists]` and `#[k::ensures]` are written on a readable clause
//! exactly as on a reference `#[k::rule]` fn; `krs expand` keeps them
//! verbatim before the clause's `#[k::rule(label = ..)]`. The existential
//! `x` names a value the step creates, so it occurs only on the right.

use k::KItem;
use k::builtin::{Int, KSequence, int};

// Programs are integers, as in the lesson's `krun` of `0`.
k::sorts! {
    Exp: KItem;
    impl Exp for Int;
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
    for Machine;

    /// `0` becomes an unknown non-zero integer.
    #[k::exists(x: Int)]
    #[k::ensures(int::ne(x, 0))]
    zero_to_unknown: {
        k: [0, ..]
    } => {
        k: [x, ..]
    };

    /// A large integer becomes five.
    #[k::requires(int::ge(n, 10))]
    big_to_five: {
        k: [n, ..]
    } => {
        k: [5, ..]
    }
    where n: Int;
}

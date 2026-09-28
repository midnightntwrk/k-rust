//@ check-pass
#![deny(clippy::must_use_candidate, clippy::needless_pass_by_value)]

use krs_macros::{configuration, init};
use renamed_krs::Term;
use renamed_krs::builtin::KSequence;
use renamed_krs::configuration::KCell;

pub trait KItem {}

#[configuration]
pub struct Machine {
    pub k: KCell<KSequence>,
}

impl Machine {
    #[init]
    pub fn init(#[renamed_krs::config_var(name = "PGM", main)] program: Term<dyn KItem>) -> Self {
        Self {
            k: KCell::new(renamed_krs::k![program]),
        }
    }

    pub fn ordinary() -> Self {
        unreachable!()
    }
}

fn main() {}

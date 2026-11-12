//! `#[k::end(finished)]` on the function `Twice`: a function is evaluated away, so no state's
//! computation starts with it.

use k::Term;
use k::builtin::{Int, KSequence, int};

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Int) -> Self {
        Self { k: k::k![pgm] }
    }
}

/// Twice `n`.
#[k::function(total, sort = Int, syntax = "twice({n})")]
#[k::end(finished)]
pub struct Twice {
    pub n: Term<Int>,
}

#[k::equation]
fn twice(k::term![Twice(n)]: Term<Int>) -> Term<Int> {
    int::add(n, n)
}

//! `cell_type = "Bag"` declares a cell bag, which K's LLVM and Haskell
//! backends do not support; KRS accepts Set, Map, and List collections only.

use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Go))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go {n}")] Go { n: Int },
}

#[k::cell]
pub struct Jobs {
    #[k::cell(multiplicity = "*", cell_type = "Bag", nested)]
    pub job: Job,
}

#[k::cell]
pub struct Job {
    #[k::cell]
    pub id: Int,
    #[k::cell]
    pub payload: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub jobs: Jobs,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            jobs: Jobs {
                job: Job { id: 0, payload: 0 },
            },
        }
    }
}

k::rules! {
    for Machine;
    use Cmd::*;

    go: { k: [Go(n), ..] } => { k: [n, ..] };
}

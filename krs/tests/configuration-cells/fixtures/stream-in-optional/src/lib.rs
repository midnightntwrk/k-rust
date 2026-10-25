//! A stream is one channel, so its cell is outside every `?` and `*` cell:
//! the stdout cell of an optional group has no instance while the group is
//! absent.

use k::KResult;
use k::builtin::{Int, KSequence, List, list};

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
pub struct Console {
    #[k::cell(stream = "stdout")]
    pub output: List,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(multiplicity = "?", nested)]
    pub console: Option<Console>,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            console: Some(Console {
                output: list::empty(),
            }),
        }
    }
}

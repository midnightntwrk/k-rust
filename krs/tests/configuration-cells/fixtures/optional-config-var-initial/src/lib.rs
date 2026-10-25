//! A `?` cell whose template reads the configuration variable `$START`
//! says `initial`, so its text and its meaning agree: it starts present,
//! holding `$START`, and `go n` adds `n` to it.

use k::KResult;
use k::builtin::{Int, KSequence, int};

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

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(multiplicity = "?", initial)]
    pub counter: Option<Int>,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "START")] start: Int,
    ) -> Self {
        Self {
            k: k::k![pgm],
            counter: Some(start),
        }
    }
}

k::rules! {
    for Machine;
    use Cmd::*;

    /// Write the counter plus `n` to the computation cell; the counter is only read.
    go: {
        k: [Go { n }, ..],
        counter: Some(c),
    } => {
        k: [int::add(c, n), ..],
    };
}

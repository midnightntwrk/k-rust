//! An `Option<T>` field is an optional cell, which K spells
//! `multiplicity = "?"`; the attribute is required.

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

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub counter: Option<Int>,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            counter: Some(0),
        }
    }
}

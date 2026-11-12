//! `probe` rewrites to `EndDrained()`, the function the end `drained` is emitted as: an end's
//! functions are applied by tools, to a whole configuration, and by no sentence.

use k::KResult;
use k::builtin::{Bool, KSequence};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Bool;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("probe")] Probe(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm] }
    }
}

/// Nothing is left to compute.
#[k::end(finished)]
pub fn drained(
    k::cells! {
        k: k::configuration::KCell(),
        ..
    }: Machine,
) {
}

k::rules! {
    for Stmt;
    use Cmd::*;

    probe: Probe() => crate::EndDrained();
}

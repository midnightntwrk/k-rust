//! A definition whose main parameter is inferred and is not `$PGM`: no parameter is marked
//! `main`, and the computation cell reads `entry`, whose configuration variable is `$ENTRY`.
//! A program file binds it.

use k::builtin::KSequence;
use k::KResult;

k::sorts! {
    Op: KResult;
}

#[k::constructors(sort = Op, result = KResult)]
#[k::precedence((Go, Halt))]
#[rustfmt::skip]
pub enum Instr {
    #[k::syntax("go")] Go,
    #[k::syntax("halt")] Halt,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "ENTRY")] entry: Op) -> Self {
        Self { k: k::k![entry] }
    }
}

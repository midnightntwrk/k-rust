//! A definition whose main parameter is a `Bytes`: `rom`, marked main, whose configuration
//! variable is `$ROM`, beside an `Int` program counter `pc`. Each is copied into its own cell, so
//! a run of depth 0 shows the values a program file and the other inputs gave.

use k::builtin::{Bytes, Int, KSequence};

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub rom: Bytes,
    #[k::cell]
    pub pc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "ROM", main)] rom: Bytes, pc: Int) -> Self {
        Self {
            k: k::k![],
            rom,
            pc,
        }
    }
}

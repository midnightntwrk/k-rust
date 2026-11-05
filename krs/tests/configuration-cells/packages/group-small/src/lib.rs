//! A definition that holds the group `Core` beside a memory.
//!
//! `Small { core, mem }` nests the dependency's group and resolves its bus
//! items from `mem`: `read` answers `busRead(addr)` with the value `mem` maps
//! `addr` to, and `write` updates `mem`. Every other rule is the group's, from
//! the dependency. A read of an address `mem` does not map is stuck.

use k::builtin::{Int, Map, map};

#[k::configuration]
pub struct Small {
    #[k::cell(nested)]
    pub core: group_core::Core,
    #[k::cell]
    pub mem: Map<Int, Int>,
}

impl Small {
    #[k::init]
    pub fn init(pgm: group_core::Prog) -> Self {
        Self {
            core: group_core::Core {
                k: k::k![pgm],
                pc: 0,
                acc: 0,
            },
            mem: map::empty(),
        }
    }
}

k::rules! {
    for Small;
    use group_core::BusOp::*;

    /// Answer a read with the value at `addr`.
    read: {
        k: [Read { addr }, ..],
        mem: { addr -> value, .. },
    } => {
        k: [Reply { value }, ..],
    };

    /// Write `value` at `addr`.
    write: {
        k: [Write { addr, value }, ..],
        mem,
    } => {
        k: [..],
        mem: map::update(mem, addr, value),
    };
}

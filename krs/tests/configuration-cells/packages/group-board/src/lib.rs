//! A definition that holds the group `Core` beside a timer and a memory.
//!
//! `Board { core, timer, mem }` holds the same group as the `Small`
//! definition, with a cell of its own: its bus rules resolve `busRead` and
//! `busWrite` from `mem` as `Small`'s do, and advance `timer` in the same
//! step, so the timer counts the core's memory accesses. The group's rules
//! name no `timer`, so they frame it.

use k::builtin::{Int, Map, int, map};

#[k::configuration]
pub struct Board {
    #[k::cell(nested)]
    pub core: group_core::Core,
    #[k::cell]
    pub timer: Int,
    #[k::cell]
    pub mem: Map<Int, Int>,
}

impl Board {
    #[k::init]
    pub fn init(pgm: group_core::Prog) -> Self {
        Self {
            core: group_core::Core {
                k: k::k![pgm],
                pc: 0,
                acc: 0,
            },
            timer: 0,
            mem: map::empty(),
        }
    }
}

k::rules! {
    for Board;
    use group_core::BusOp::*;

    /// Answer a read with the value at `addr`, one tick later.
    read: {
        k: [Read { addr }, ..],
        timer,
        mem: { addr -> value, .. },
    } => {
        k: [Reply { value }, ..],
        timer: int::add(timer, 1),
    };

    /// Write `value` at `addr`, one tick later.
    write: {
        k: [Write { addr, value }, ..],
        timer,
        mem,
    } => {
        k: [..],
        timer: int::add(timer, 1),
        mem: map::update(mem, addr, value),
    };
}

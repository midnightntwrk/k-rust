//! A definition that holds the group `Core` and computes its initial state.
//!
//! `Booted { core, timer, mode, mem, shadow }` holds the group as `Board`
//! does, and its initializer calls productions no program can contain:
//!
//! - `rom::RomImage()`, `internal` and `Map`-valued, of a package that
//!   depends on the group's, whose equation calls `rom::RomWord()`;
//! - `rom::Cost(..)`, over `Instr`, a sort of the group's package;
//! - `Shadow()`, `internal` and `Map`-valued, of this package;
//! - `Tick(..)`, of this package, which the bus rules apply too;
//! - `Mode::Cold()`, a constructor that is not `pub`.
//!
//! The group's rules need the configuration, so it is emitted in
//! `KRS-GROUP-BOOT-BOARD-CONFIGURATION`, below the group's module. That
//! module declares the five productions its configuration names; their
//! equations, and `RomWord`, which only an equation names, stay in the
//! modules of their packages.

use k::Term;
use k::builtin::{Int, Map, map};

k::sorts! {
    Phase;
}

/// Whether the board has answered the bus since it started.
#[k::constructors(sort = Phase, result = KResult)]
#[rustfmt::skip]
enum Mode {
    #[k::syntax("cold")] Cold(),
    #[k::syntax("warm")] Warm(),
}

/// The timer after one more bus access.
#[k::function(total, internal)]
pub fn Tick(timer: Term<Int>) -> Term<Int> {
    timer + 10
}

/// The second memory at start.
#[k::function(total, internal)]
pub fn Shadow() -> Term<Map<Int, Int>> {
    k::map![0 -> Tick(0)]
}

#[k::configuration]
pub struct Booted {
    #[k::cell(nested)]
    pub core: group_core::Core,
    #[k::cell]
    pub timer: Int,
    #[k::cell]
    pub mode: Phase,
    #[k::cell]
    pub mem: Map<Int, Int>,
    #[k::cell]
    pub shadow: Map<Int, Int>,
}

impl Booted {
    #[k::init]
    pub fn init(pgm: group_core::Prog) -> Self {
        Self {
            core: group_core::Core {
                k: k::k![pgm],
                pc: 0,
                acc: rom::Cost(group_core::Op::Store { addr: 0 }),
            },
            timer: Tick(1),
            mode: Mode::Cold(),
            mem: rom::RomImage(),
            shadow: Shadow(),
        }
    }
}

k::rules! {
    for Booted;
    use group_core::BusOp::*;

    /// Answer a read with the value at `addr`, one tick later.
    read: {
        k: [Read { addr }, ..],
        timer,
        mode: _,
        mem: { addr -> value, .. },
    } => {
        k: [Reply { value }, ..],
        timer: Tick(timer),
        mode: Mode::Warm(),
    };

    /// Write `value` at `addr`, one tick later.
    write: {
        k: [Write { addr, value }, ..],
        timer,
        mode: _,
        mem,
    } => {
        k: [..],
        timer: Tick(timer),
        mode: Mode::Warm(),
        mem: map::update(mem, addr, value),
    };
}

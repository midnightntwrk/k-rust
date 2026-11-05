//! Harts as the instances of a Map collection keyed by `id`.
//!
//! The library's rules for `Hart` are local steps of one hart, so a system
//! of several harts runs by interleaving them. Everything between harts is
//! this definition's own, over the collection: `spawn` starts a hart keyed
//! by `nextId` running the given program, `join(n)` waits until hart `n` has
//! finished and removes it, and `read` and `write` answer a hart's bus items
//! from the one memory every hart shares. Two harts that store at one
//! address race: the order of their `write` steps decides what a later
//! load reads.

use hart::{BusOp, Hart, Job, Jobs, Op, Prog, Regs};
use k::builtin::{Int, Map, int, map};

/// The collection's parent.
#[k::cell]
pub struct Harts {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub hart: Hart,
}

#[k::configuration]
pub struct Smp {
    #[k::cell(nested)]
    pub harts: Harts,
    #[k::cell]
    pub mem: Map<Int, Int>,
    #[k::cell(name = "nextId")]
    pub next_id: Int,
}

impl Smp {
    #[k::init]
    pub fn init(pgm: Prog) -> Self {
        Self {
            harts: Harts {
                hart: Hart {
                    id: 0,
                    k: k::k![pgm],
                    pc: 0,
                    regs: Regs { a: 1, b: 2 },
                    reservation: k::absent!(0),
                    jobs: Jobs {
                        job: Job { jid: 0, payload: 0 },
                    },
                },
            },
            mem: map::empty(),
            next_id: 1,
        }
    }
}

k::rules! {
    for Smp;
    use BusOp::*;
    use Op::*;

    /// Start a hart keyed by `nextId`, running `body`.
    spawn: {
        hart: { me @ Hart { k: [Spawn { body }, ..], .. }, .. },
        next_id: n,
    } => {
        hart: { Hart { k: [..], ..me }, Hart { id: n, k: [body], .. }, .. },
        next_id: int::add(n, 1),
    };

    /// Wait until hart `n` has finished, then remove it.
    join: {
        hart: { me @ Hart { k: [Join { id: n }, ..], .. }, Hart { id: n, k: [], .. }, .. },
    } => {
        hart: { Hart { k: [..], ..me }, .. },
    };

    /// Answer a read with the value at `addr`.
    read: {
        hart: { me @ Hart { k: [Read { addr }, ..], .. }, .. },
        mem: { addr -> value, .. },
    } => {
        hart: { Hart { k: [value, ..], ..me }, .. },
    };

    /// Write `value` at `addr`.
    write: {
        hart: { me @ Hart { k: [Write { addr, value }, ..], .. }, .. },
        mem,
    } => {
        hart: { Hart { k: [..], ..me }, .. },
        mem: map::update(mem, addr, value),
    };
}

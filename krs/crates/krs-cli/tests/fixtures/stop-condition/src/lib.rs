//! A free-running counter (`tests/stop_condition.rs`): `tick` adds 1 to `n` and 2 to `m` and
//! queues the next `#tick`, so a run never ends on its own, and its end is a stop at `tick`.
//! Every step is an arrival at `tick`; a stop condition decides which of them are stops.
//!
//! Beside them: an unobservable cell, a group cell, a repeated cell's instance and an optional
//! cell, which a condition may not read, and functions a condition may not be (of the wrong
//! arity, of a parameter sort that does not admit a cell's, or not of result sort `Bool`).

use k::builtin::{Bool, Int, KSequence};
use k::{KItem, Term};

k::sorts! {
    Op: KItem;
}

#[k::constructors(sort = Op, result = k::KResult)]
pub enum Step {
    /// Count, then tick again.
    #[k::syntax("#tick")]
    Tick,
}

#[k::cell]
pub struct Cpu {
    #[k::cell]
    pub a: Int,
}

#[k::cell]
pub struct Threads {
    #[k::cell(multiplicity = "*", cell_type = "List", initial, nested)]
    pub thread: Thread,
}

#[k::cell]
pub struct Thread {
    #[k::cell]
    pub id: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub n: Int,
    #[k::cell]
    pub m: Int,
    #[k::cell]
    pub on: Bool,
    #[k::cell(unobservable)]
    pub hidden: Int,
    #[k::cell(nested)]
    pub cpu: Cpu,
    #[k::cell(nested)]
    pub threads: Threads,
    #[k::cell(multiplicity = "?")]
    pub timer: Option<Int>,
}

impl Machine {
    #[k::init]
    pub fn init(start: Int) -> Self {
        Self {
            k: k::k![Step::Tick],
            n: start,
            m: 0,
            on: true,
            hidden: 0,
            cpu: Cpu { a: 0 },
            threads: Threads {
                thread: Thread { id: 0 },
            },
            timer: k::absent!(0),
        }
    }
}

k::rules! {
    for Machine;

    tick: {
        k: [Step::Tick, ..],
        n,
        m,
    } => {
        k: [Step::Tick, ..],
        n: n + 1,
        m: m + 2,
    };
}

/// Whether `n` is a multiple of 3: a condition of one cell, which the definition itself holds.
#[k::function(total, internal)]
pub fn Third(n: Term<Int>) -> Term<Bool> {
    n % 3 == 0
}

/// The sum of two `Int`s: no condition, since its result is no `Bool`.
#[k::function(total, internal)]
pub fn Total(n: Term<Int>, m: Term<Int>) -> Term<Int> {
    n + m
}

/// Whether a flag is set: of a parameter sort that admits no `Int` cell.
#[k::function(total, internal)]
pub fn Set(flag: Term<Bool>) -> Term<Bool> {
    flag
}

//! A free-running machine (`tests/observation_core.rs`): each step adds 1 to `n`, and every third
//! step (`emit`, where `n % 3 == 2`) also appends `out(n)` to the `out` log and replaces the
//! `ring` list by `[out(n)]`, which no log may read since it does not only grow. `phase` is a
//! bookkeeping cell no rule rewrites, and `hole` holds what the run is configured with.
//!
//! Beside them: an unobservable cell, a group cell and an optional cell, which no observation may
//! read, and a function, which is no rule a point may name.

use k::builtin::{Int, KSequence, List};
use k::{KItem, Term};

k::sorts! {
    Out;
    Op: KItem;
}

#[k::constructors(sort = Out, result = k::KResult)]
pub enum Emitted {
    /// An output of the machine.
    #[k::syntax("out({n})")]
    Out { n: Int },
}

#[k::constructors(sort = Op, result = k::KResult)]
pub enum Step {
    /// Count, then step again.
    #[k::syntax("#tick")]
    Tick,
}

#[k::cell]
pub struct Cpu {
    #[k::cell]
    pub a: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub n: Int,
    #[k::cell]
    pub phase: Int,
    #[k::cell]
    pub hole: Int,
    #[k::cell]
    pub out: List<Out>,
    #[k::cell]
    pub ring: List<Out>,
    #[k::cell(unobservable)]
    pub hidden: Int,
    #[k::cell(nested)]
    pub cpu: Cpu,
    #[k::cell(multiplicity = "?")]
    pub timer: Option<Int>,
}

impl Machine {
    #[k::init]
    pub fn init(start: Int, hole: Int) -> Self {
        Self {
            k: k::k![Step::Tick],
            n: start,
            phase: 7,
            hole,
            out: [],
            ring: [],
            hidden: 0,
            cpu: Cpu { a: 0 },
            timer: k::absent!(0),
        }
    }
}

k::rules! {
    for Machine;

    #[k::requires(n % 3 < 2)]
    tick: {
        k: [Step::Tick, ..],
        n,
    } => {
        k: [Step::Tick, ..],
        n: n + 1,
    };

    #[k::requires(n % 3 == 2)]
    emit: {
        k: [Step::Tick, ..],
        n,
        out: log,
        ring: _,
    } => {
        k: [Step::Tick, ..],
        n: n + 1,
        out: [..log, Emitted::Out { n }],
        ring: [Emitted::Out { n }],
    };
}

/// `n` where it is not negative: partial, defined by its equation alone, so `Natural(-1)` has no
/// value.
#[k::function(partial, internal)]
#[k::requires(n >= 0)]
pub fn Natural(n: Term<Int>) -> Term<Int> {
    n
}

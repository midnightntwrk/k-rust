//! Claims holding `let` blocks and `k::matches!` in their states and conditions (NT-15).
//!
//! A `let` block denotes the term it computes and `k::matches!` a Bool, so a claim's states and
//! conditions hold them as a rule's do. Neither prover lowers K's `#let` and `:=K` in a claim, so
//! KRS lifts each into a function of the names it reads, declared beside the definition's
//! sentences with the one equation whose result is the construct. `load` sets `pc` to the length
//! of `program`. `starts` (a block in the start state), `ends` (in the end state), `tests`
//! (`k::matches!` in `requires`), `ensured` (a block in `ensures`) and `refutes` (a refutable
//! pattern in `requires`) must be proved by `krs prove` and by Java `kprove`; `off-by-one` ends
//! with a block one more than the length, which no run reaches, and must fail on both routes.

use k::builtin::{Bytes, Int, KSequence, bytes};

k::sorts! {
    Exp: k::KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
pub enum Op {
    #[k::syntax("load")]
    Load(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub program: Bytes,
    #[k::cell]
    pub pc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            program: bytes::empty(),
            pc: 0,
        }
    }
}

k::rules! {
    for Machine;
    use Op::*;

    load: {
        k: [Load(), ..],
        program: p,
        pc: n,
    } => {
        k: [..],
        pc: bytes::length(p),
    };
}

k::claims! {
    for Machine;
    use Op::*;

    #[k::claim(all_paths)]
    starts: {
        k: [Load()],
        program: p,
        pc: bytes::length({ let q = p; q }),
    } => {
        k: [],
        program: p,
        pc: bytes::length(p),
    };

    #[k::claim(all_paths)]
    ends: {
        k: [Load()],
        program: p,
        pc: 0,
    } => {
        k: [],
        program: p,
        pc: { let m = bytes::length(p); m },
    };

    #[k::claim(all_paths)]
    #[k::requires(k::matches!(n, 0))]
    tests: {
        k: [Load()],
        program: p,
        pc: n,
    } => {
        k: [],
        program: p,
        pc: bytes::length(p),
    };

    #[k::claim(all_paths)]
    #[k::ensures({ let m = 0; m == 0 })]
    ensured: {
        k: [Load()],
        program: p,
        pc: 0,
    } => {
        k: [],
        program: p,
        pc: bytes::length(p),
    };

    #[k::claim(all_paths)]
    #[k::requires({ let 0 = n; true })]
    refutes: {
        k: [Load()],
        program: p,
        pc: n,
    } => {
        k: [],
        program: p,
        pc: bytes::length(p),
    };

    #[k::claim(all_paths)]
    off_by_one: {
        k: [Load()],
        program: p,
        pc: 0,
    } => {
        k: [],
        program: p,
        pc: { let m = bytes::length(p); m + 1 },
    };
}

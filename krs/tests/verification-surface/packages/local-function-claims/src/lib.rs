//! Claims holding `let` blocks and `k::matches!` in their states and conditions (NT-15).
//!
//! A `let` block denotes the term it computes and `k::matches!` a Bool, so a claim's states and
//! conditions hold them as a rule's do. Neither prover lowers K's `#let` and `:=K` in a claim, so
//! KRS lifts each into a function of the names it reads, which the definition declares: a block's
//! one equation's result is the block, and a test's two equations are `true` under the test as
//! their condition and `false` otherwise, so its pattern stays a pattern, `name @ pattern`
//! included. `load` sets `pc` to the length of `program` and leaves the rest of the computation.
//! `starts` (a block in the start state, read in the `pr` the end state names), `ends` (in the
//! end state), `tests` (`k::matches!` in `requires`, which fixes `n`), `ensured` (a block in
//! `ensures`), `aliased` (a test whose pattern holds `@`, inside a block in `ensures`) and `twice`
//! (two blocks in one state) hold only through their constructs' values, and must be proved by
//! `krs prove` and by Java `kprove`; `starts-wrong`, `tests-wrong`, `aliased-wrong` and
//! `off-by-one` state a value their construct does not have, and must fail on both routes.
//! `refutes` (a refutable pattern in `requires`) and `aliased-requires` (an aliased test in
//! `requires`) end in a state that holds whatever `n` is, and show those conditions lifted: Java
//! `kprove` does not infer `n` from either condition (krs-cli `readable_claims` proves
//! `refutes`'s dependent form natively).

use k::builtin::{Bytes, Int, KSequence, bytes, int};

k::sorts! {
    Exp: k::KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
pub enum Op {
    #[k::syntax("load")]
    Load(),
    #[k::syntax("pr({a}, {b})")]
    Pr { a: Int, b: Int },
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
        k: [Load(), Pr({ let a = n; a }, 0)],
        program: p,
        pc: n,
    } => {
        k: [Pr(n, 0)],
        program: p,
        pc: bytes::length(p),
    };

    #[k::claim(all_paths)]
    starts_wrong: {
        k: [Load(), Pr({ let a = n; a + 1 }, 0)],
        program: p,
        pc: n,
    } => {
        k: [Pr(n, 0)],
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
    off_by_one: {
        k: [Load()],
        program: p,
        pc: 0,
    } => {
        k: [],
        program: p,
        pc: { let m = bytes::length(p); m + 1 },
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
        pc: bytes::length(p) + n,
    };

    #[k::claim(all_paths)]
    #[k::requires(k::matches!(n, 1))]
    tests_wrong: {
        k: [Load()],
        program: p,
        pc: n,
    } => {
        k: [],
        program: p,
        pc: bytes::length(p) + n,
    };

    #[k::claim(all_paths)]
    #[k::exists(left: Int)]
    #[k::ensures({ let l = left; l == bytes::length(p) })]
    ensured: {
        k: [Load()],
        program: p,
        pc: 0,
    } => {
        k: [],
        program: p,
        pc: left,
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
    #[k::exists(left: Int)]
    #[k::ensures({ let zero = k::matches!(Pr(left, left), Pr(m @ 0, m)); zero })]
    aliased: {
        k: [Load()],
        program: bytes::empty(),
        pc: 5,
    } => {
        k: [],
        program: bytes::empty(),
        pc: left,
    };

    #[k::claim(all_paths)]
    #[k::exists(left: Int)]
    #[k::ensures(k::matches!(Pr(left, left), Pr(m @ 1, m)))]
    aliased_wrong: {
        k: [Load()],
        program: bytes::empty(),
        pc: 5,
    } => {
        k: [],
        program: bytes::empty(),
        pc: left,
    };

    #[k::claim(all_paths)]
    #[k::requires(k::matches!(Pr(n, n), Pr(m @ 0, m)))]
    aliased_requires: {
        k: [Load()],
        program: p,
        pc: n,
    } => {
        k: [],
        program: p,
        pc: bytes::length(p),
    };

    #[k::claim(all_paths)]
    twice: {
        k: [Load()],
        program: p,
        pc: 0,
    } => {
        k: [],
        program: p,
        pc: int::add({ let a = bytes::length(p); a }, { let b = 0; b }),
    };
}

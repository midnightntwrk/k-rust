//! Cores as the instances of a Map collection keyed by `cid`, beside one
//! memory every core shares.
//!
//! The main cell `k` lies in each core, so a clause for an instruction is a
//! step of one core. `load` and `peek` also read `mem`, which lies outside
//! every instance: the configuration holds it once, so each such step
//! matches one core's computation and the one memory beside the cores. Its
//! emitted rule writes the memory's clause at the top, beside the core's
//! cell. `peek` adds the core's own id, which `cidPlus` reads through its
//! function context typed by `Core`, so the step passes the core's key as
//! any step inside the core does.
//!
//! `store`, `mark`, `spawn` and `join` are rules for the configuration, over
//! the cores' instance list: `store` and `mark` write the memory (`mark` the
//! core's own id), `spawn` starts a core keyed by `next`, and `join(n)` takes
//! the value core `n` ended with and removes it. Two cores that mark one
//! address race: the order of their `mark` steps decides what a later load
//! reads.

use k::builtin::{Int, KSequence, Map, int, map};
use k::{KResult, Term};

k::sorts! {
    Instr;
    Value: Instr + KResult;
    impl Value for Int;
    Prog;
    impl Prog for Instr;
}

#[k::constructors(sort = Instr, result = KResult)]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("load ( {addr} )")] Load { addr: Int },
    #[k::syntax("store ( {addr} , {value} )")] Store { addr: Int, value: Int },
    #[k::syntax("peek ( {addr} )")] Peek { addr: Int },
    #[k::syntax("mark ( {addr} )")] Mark { addr: Int },
    #[k::syntax("spawn {{ {body} }}")] Spawn { body: Prog },
    #[k::syntax("join ( {id} )")] Join { id: Int },
}

#[k::constructors(sort = Prog, result = KResult)]
#[k::precedence(right (Then))]
#[rustfmt::skip]
pub enum Code {
    #[k::syntax("{head} ; {tail}")] Then { head: Instr, tail: Prog },
}

/// One core; its first child `cid` is its key.
#[k::cell]
pub struct Core {
    #[k::cell]
    pub cid: Int,
    #[k::cell]
    pub k: KSequence,
}

/// The cores' collection.
#[k::cell]
pub struct Cores {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub core: Core,
}

#[k::configuration]
pub struct Machine {
    #[k::cell(nested)]
    pub cores: Cores,
    #[k::cell]
    pub mem: Map<Int, Int>,
    #[k::cell]
    pub next: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Prog) -> Self {
        Self {
            cores: Cores {
                core: Core {
                    cid: 0,
                    k: k::k![pgm],
                },
            },
            mem: map::empty(),
            next: 1,
        }
    }
}

/// `cidPlus(n)` is `n` plus the id of the core it is evaluated in.
#[k::function(total, sort = Int, syntax = "cidPlus ( {n} )")]
pub struct CidPlus {
    pub n: Term<Int>,
}

#[k::equation]
fn cid_plus(
    n: Term<Int>,
    c: Term<Int>,
    k::term![CidPlus(n)]: Term<Int>,
    k::cells! {
        cid: k::configuration::Cell(c),
        ..
    }: Core,
) -> Term<Int> {
    int::add(c, n)
}

k::rules! {
    for Core;
    use Code::*;

    /// Run the head of a sequence, then its tail.
    then: {
        k: [Then { head, tail }, ..],
    } => {
        k: [head, tail, ..],
    };
}

k::rules! {
    for Instr;
    use Op::*;

    /// Read the value at `addr` from the shared memory.
    load: Load { addr } => v          where have mem[addr -> let v];

    /// Read the value at `addr` from the shared memory, plus the core's own id.
    peek: Peek { addr } => CidPlus(v) where have mem[addr -> let v];
}

k::rules! {
    for Machine;
    use Op::*;

    /// Write `value` at `addr`.
    store: {
        core: { me @ Core { k: [Store { addr, value }, ..], .. }, .. },
        mem,
    } => {
        core: { Core { k: [..], ..me }, .. },
        mem: map::update(mem, addr, value),
    };

    /// Write the core's own id at `addr`.
    mark: {
        core: { me @ Core { cid: c, k: [Mark { addr }, ..], .. }, .. },
        mem,
    } => {
        core: { Core { k: [..], ..me }, .. },
        mem: map::update(mem, addr, c),
    };

    /// Start a core keyed by `next`, running `body`.
    spawn: {
        core: { me @ Core { k: [Spawn { body }, ..], .. }, .. },
        next: n,
    } => {
        core: { Core { k: [..], ..me }, Core { cid: n, k: [body], .. }, .. },
        next: int::add(n, 1),
    };

    /// Wait until core `n` has ended with a value, then take the value and remove the core.
    join: {
        core: { me @ Core { k: [Join { id: n }, ..], .. }, Core { cid: n, k: [r], .. }, .. },
    } => {
        core: { Core { k: [r, ..], ..me }, .. },
    }
    where r: Int;
}

//! A hart: a cell group with its own computation cell, written once for
//! every definition that holds it, at a fixed position, in an optional cell or
//! as the instance type of a Map collection.
//!
//! A rule typed by the group (`for Hart`) names only the group's cells, so
//! wherever a definition holds harts it is a local step of one hart: it
//! rewrites that hart's cells and frames every other cell, the other harts
//! included. The rules here state each form a rule may hold inside the hart:
//!
//! - leaf cells: `inc`, and `tick`, which restates the Map key `id: 0`, so
//!   that it applies to the hart keyed `0` alone;
//! - a whole group child: `swap` rewrites `regs` as one readable record;
//! - an optional child: `reserve` creates `reservation` and `release`
//!   deletes it;
//! - an instance record of a collection inside the hart: `post` creates a job
//!   keyed by the hart's own id, and `work` updates a job in place;
//! - a context alias, `hart_eval`, through which `wait` is strict, and a
//!   `#[k::context]`, `hop_operand`, which evaluates the operand of `hop`;
//!   both evaluate `here`, which a rule rewrites to the hart's own program
//!   counter, and a `#[k::context]` whose condition reads the hart's register
//!   `a`, `guard_operand`, so that `guard`'s operand is evaluated only in a
//!   hart whose `a` is 1;
//! - `report` writes a digest of the hart's own cells to the bus, so that a
//!   definition can observe a hart after it is gone.
//!
//! Memory, starting harts and waiting for them are not a hart's: `load` and
//! `store` hand the access to the containing definition as the open items
//! `busRead(addr)` and `busWrite(addr, value)`, and `spawn` and `join` are
//! left on the computation cell for the containing definition's rules over
//! its collection.

use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
    Instr;
    Prog;
    impl Prog for Instr;
    Bus;
}

#[k::constructors(sort = Instr, result = KResult)]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("inc")] Inc(),
    #[k::syntax("tick")] Tick(),
    #[k::syntax("swap")] Swap(),
    #[k::syntax("reserve")] Reserve(),
    #[k::syntax("release")] Release(),
    #[k::syntax("post")] Post(),
    #[k::syntax("work")] Work(),
    #[k::syntax("load ( {addr} )")] Load { addr: Int },
    #[k::syntax("store ( {addr} )")] Store { addr: Int },
    #[k::syntax("wait ( {n} )")] #[k::strict(using = hart_eval)] Wait { n: Exp },
    #[k::syntax("hop ( {n} )")] Hop { n: Exp },
    #[k::syntax("spawn {{ {body} }}")] Spawn { body: Prog },
    #[k::syntax("join ( {id} )")] Join { id: Int },
    #[k::syntax("guard ( {n} )")] Guard { n: Exp },
    #[k::syntax("report ( {addr} )")] Report { addr: Int },
}

#[k::constructors(sort = Prog, result = KResult)]
#[k::precedence(right (Then))]
#[rustfmt::skip]
pub enum Code {
    #[k::syntax("{head} ; {tail}")] Then { head: Instr, tail: Prog },
}

/// An expression a hart evaluates: `here` is its own program counter.
#[k::constructors(sort = Exp, result = KResult)]
#[rustfmt::skip]
pub enum Reg {
    #[k::syntax("here")] Here(),
}

/// What a hart asks of the definition that holds it.
#[k::constructors(sort = Bus, result = KResult, internal)]
#[rustfmt::skip]
pub enum BusOp {
    #[k::syntax("busRead ( {addr} )")] Read { addr: Int },
    #[k::syntax("busWrite ( {addr} , {value} )")] Write { addr: Int, value: Int },
}

/// One hart; in a Map collection, its first child `id` is its key.
#[k::cell]
pub struct Hart {
    #[k::cell]
    pub id: Int,
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell(nested)]
    pub regs: Regs,
    #[k::cell(multiplicity = "?")]
    pub reservation: Option<Int>,
    #[k::cell(nested)]
    pub jobs: Jobs,
}

/// Two registers, rewritten as one group.
#[k::cell]
pub struct Regs {
    #[k::cell]
    pub a: Int,
    #[k::cell]
    pub b: Int,
}

/// The hart's jobs, a Map collection inside the hart keyed by `jid`.
#[k::cell]
pub struct Jobs {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub job: Job,
}

/// One job.
#[k::cell]
pub struct Job {
    #[k::cell]
    pub jid: Int,
    #[k::cell]
    pub payload: Int,
}

/// Evaluate at the head of the hart's computation.
#[k::context_alias(name = hart_eval, here = site)]
fn hart_eval(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        state @ ..
    }: Hart,
) {
}

/// Evaluate the operand of `hop` at the head of the hart's computation.
#[k::context(hole = h)]
fn hop_operand(
    h: Exp,
    k::cells! {
        k: k::configuration::KCell(Op::Hop(h), ..),
        state @ ..
    }: Hart,
) {
}

/// Evaluate the operand of `guard` only where the hart's register `a` is 1: the context's
/// condition reads a second cell of the same hart.
#[k::context(hole = h)]
#[k::requires(int::eq(one, 1))]
fn guard_operand(
    h: Exp,
    one: Int,
    k::cells! {
        k: k::configuration::KCell(Op::Guard(h), ..),
        Regs::a: k::configuration::Cell(one),
        state @ ..
    }: Hart,
) {
}

k::rules! {
    for Hart;
    use BusOp::*;
    use Code::*;
    use Op::*;
    use Reg::*;

    /// Run the program's first instruction, then the rest.
    next: {
        k: [Then { head, tail }, ..],
    } => {
        k: [head, tail, ..],
    };

    /// Count one instruction.
    inc: {
        k: [Inc(), ..],
        pc,
    } => {
        k: [..],
        pc: int::add(pc, 1),
    };

    /// The hart keyed `0` alone counts two.
    tick: {
        id: 0,
        k: [Tick(), ..],
        pc,
    } => {
        id: 0,
        k: [..],
        pc: int::add(pc, 2),
    };

    /// Exchange the registers.
    swap: {
        k: [Swap(), ..],
        regs: Regs { a, b },
    } => {
        k: [..],
        regs: Regs { a: b, b: a },
    };

    /// Reserve the program counter.
    reserve: {
        k: [Reserve(), ..],
        pc,
        reservation: None,
    } => {
        k: [..],
        reservation: Some(pc),
    };

    /// Release the reservation, adding it to the program counter.
    release: {
        k: [Release(), ..],
        pc,
        reservation: Some(r),
    } => {
        k: [..],
        pc: int::add(pc, r),
        reservation: None,
    };

    /// Create a job keyed by the hart's own id.
    post: {
        id: me,
        k: [Post(), ..],
        job: { .. },
    } => {
        k: [..],
        job: { Job { jid: me, payload: 0 }, .. },
    };

    /// Work on some job.
    work: {
        k: [Work(), ..],
        job: { j @ Job { payload: p, .. }, .. },
    } => {
        k: [..],
        job: { Job { payload: int::add(p, 1), ..j }, .. },
    };

    /// The hart's own program counter.
    here: {
        k: [Here(), ..],
        pc,
    } => {
        k: [pc, ..],
    };

    /// Wait for `n`, counting it.
    wait: {
        k: [Wait { n }, ..],
        pc,
    } => {
        k: [..],
        pc: int::add(pc, n),
    }
    where n: Int;

    /// Hop by `n`.
    hop: {
        k: [Hop { n }, ..],
        pc,
    } => {
        k: [..],
        pc: int::add(pc, n),
    }
    where n: Int;

    /// Ask the bus for the value at `addr`.
    load: {
        k: [Load { addr }, ..],
    } => {
        k: [Read { addr }, ..],
    };

    /// Ask the bus to write the hart's own id at `addr`.
    store: {
        id: me,
        k: [Store { addr }, ..],
    } => {
        k: [Write { addr, value: me }, ..],
    };

    /// Guard by `n`, counting it.
    guard: {
        k: [Guard { n }, ..],
        pc,
    } => {
        k: [..],
        pc: int::add(pc, n),
    }
    where n: Int;

    /// Ask the bus to write a digest of the hart's cells at `addr`: its program counter, ten
    /// times its register `a` and a hundred times the payload of one of its jobs.
    report: {
        k: [Report { addr }, ..],
        pc,
        a,
        job: { j @ Job { payload, .. }, .. },
    } => {
        k: [
            Write { addr, value: int::add(pc, int::add(int::mul(10, a), int::mul(100, payload))) },
            ..,
        ],
        job: { Job { ..j }, .. },
    };
}

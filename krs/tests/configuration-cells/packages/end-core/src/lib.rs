//! A cell group that declares ends, for every definition that holds it.
//!
//! An end is a set of states where the definition says the run is over, in one of two classes:
//! `finished`, or `refused` with a reason. `Core` is a `#[k::cell]` group with its own
//! computation cell, and this package declares no configuration: each end below is an end of
//! every definition whose configuration holds `Core`, under one item name.
//!
//! - `halt` and `trap ( code )` carry `#[k::end(..)]` on their constructors: the definition is
//!   at that end wherever its main computation cell starts with the constructor. No rule
//!   executes either. `halt` is `finished`; `trap` is `refused`, and its reason is the
//!   instruction.
//! - `drained` and `overflow` are written on a `fn` whose pattern is typed by the group, so
//!   they read the group's cells where the holder places them. `drained` is `finished`: the
//!   computation is empty. `overflow` is `refused` with the accumulator as its reason: `inc`
//!   applies only below 3, so a core at `inc` with the accumulator at 3 has no rule.
//!
//! Memory is not the core's: `load` leaves the open item `busRead(addr)` on the computation
//! cell, which the definition that holds the core answers, or declares an end at.

use k::Term;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Instr;
    Prog;
    Bus;
}

#[k::constructors(sort = Instr, result = KResult)]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("inc")] Inc(),
    #[k::syntax("load ( {addr} )")] Load { addr: Int },
    /// The program asks to stop.
    #[k::end(finished)]
    #[k::syntax("halt")] Halt(),
    /// An instruction no core executes.
    #[k::end(refused)]
    #[k::syntax("trap ( {code} )")] Trap { code: Int },
}

#[k::constructors(sort = Prog, result = KResult)]
#[k::precedence((Done, Then))]
#[rustfmt::skip]
pub enum Code {
    #[k::syntax("done")] Done(),
    #[k::syntax("{head} ; {tail}")] Then { head: Instr, tail: Prog },
}

/// What the core asks of the definition that holds it, and the answer to a read.
#[k::constructors(sort = Bus, result = KResult, internal)]
#[rustfmt::skip]
pub enum BusOp {
    #[k::syntax("busRead ( {addr} )")] Read { addr: Int },
    #[k::syntax("busReply ( {value} )")] Reply { value: Int },
}

/// A reusable core: its own computation cell, a program counter and an accumulator.
#[k::cell]
pub struct Core {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub acc: Int,
}

/// The core ran its program to the end: nothing is left to compute.
#[k::end(finished)]
pub fn drained(
    k::cells! {
        k: k::configuration::KCell(),
        ..
    }: Core,
) {
}

/// The accumulator holds at most 3: an `inc` beyond it is refused, with the accumulator.
#[k::end(refused)]
#[k::requires(int::le(3, acc))]
pub fn overflow(
    acc: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Op::Inc(), ..),
        acc: k::configuration::Cell(acc),
        ..
    }: Core,
) -> Term<Int> {
    acc
}

k::rules! {
    for Core;
    use BusOp::*;
    use Code::*;
    use Op::*;

    /// Run the program's first instruction, then the rest.
    next: {
        k: [Then { head, tail }, ..],
    } => {
        k: [head, tail, ..],
    };

    /// The program is done.
    end: {
        k: [Done(), ..],
    } => {
        k: [..],
    };

    /// Count one instruction and add one to the accumulator, while it is below 3.
    #[k::requires(int::lt(acc, 3))]
    inc: {
        k: [Inc(), ..],
        pc,
        acc,
    } => {
        k: [..],
        pc: int::add(pc, 1),
        acc: int::add(acc, 1),
    };

    /// Count one instruction and ask the bus for the value at `addr`.
    load: {
        k: [Load { addr }, ..],
        pc,
    } => {
        k: [Read { addr }, ..],
        pc: int::add(pc, 1),
    };

    /// Latch the value the bus read into the accumulator.
    reply: {
        k: [Reply { value }, ..],
        acc: _,
    } => {
        k: [..],
        acc: value,
    };
}

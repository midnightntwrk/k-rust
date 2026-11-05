//! Rules for a cell group, written once for every definition that holds it.
//!
//! `Core` is a `#[k::cell]` group with its own computation cell, a program
//! counter and an accumulator, and this package declares no configuration.
//! Its rules are typed by the group (`for Core`): each names only the
//! group's cells, and is a rule of every definition whose configuration holds
//! `Core` at one fixed position, where it frames every cell it does not name.
//!
//! Memory is not the core's: `load` and `store` hand the access to the
//! containing definition as an open item on the core's computation cell,
//! `busRead(addr)` and `busWrite(addr, value)`, which no rule here consumes.
//! Each containing definition resolves them with rules for its own
//! configuration; an item no rule of the definition resolves leaves the
//! computation stuck at it. A read is answered with `busReply(value)`, which `reply` latches into the
//! accumulator, so what a load does with the value it reads stays the core's.
//! The bus items are `pub`, so that a dependent package's rules may name
//! them, and `internal`, since they are not program syntax.

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
    #[k::syntax("store ( {addr} )")] Store { addr: Int },
}

#[k::constructors(sort = Prog, result = KResult)]
#[k::precedence((Done, Then))]
#[rustfmt::skip]
pub enum Code {
    #[k::syntax("done")] Done(),
    #[k::syntax("{head} ; {tail}")] Then { head: Instr, tail: Prog },
}

/// What the core asks of the definition that holds it, and the answer to a
/// read.
#[k::constructors(sort = Bus, result = KResult, internal)]
#[rustfmt::skip]
pub enum BusOp {
    #[k::syntax("busRead ( {addr} )")] Read { addr: Int },
    #[k::syntax("busWrite ( {addr} , {value} )")] Write { addr: Int, value: Int },
    #[k::syntax("busReply ( {value} )")] Reply { value: Int },
}

/// A reusable core: its own computation cell, a program counter and an
/// accumulator.
#[k::cell]
pub struct Core {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub acc: Int,
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

    /// Count one instruction and add one to the accumulator.
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

    /// Count one instruction and ask the bus to write the accumulator at
    /// `addr`.
    store: {
        k: [Store { addr }, ..],
        pc,
        acc,
    } => {
        k: [Write { addr, value: acc }, ..],
        pc: int::add(pc, 1),
    };
}

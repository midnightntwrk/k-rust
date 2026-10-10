//! Whole nested-cell variables (KF-016).
//!
//! A nested cell is a value too: K gives `<frame>` the sort `FrameCell`, so
//! one variable captures the whole cell, as KEVM saves `<callState>` on its
//! call stack. `push` binds `frame: f` and pushes it onto `stack`; `pop`
//! restores the saved frame with `frame: f` on the result side. The emitted
//! rules name `F:FrameCell`, never the cells inside `<frame>`.
//!
//! `save` and `restore` are the same machine written the long way: they
//! restate every leaf of `<frame>` and rebuild it with `k::fragment!`.
//! `call` and `ret` are `push` and `pop` in the reference spelling `krs
//! expand` prints: a nested field's `cells!` entry has no wrapper, and the
//! group binder is typed by the nested `#[k::cell]` struct.
//!
//! Starting from an empty stack, pc 0 and gas 13
//! (`-cSTACK=.List -cPC=0 -cGAS=13`), the program
//! `bump bump push bump pop bump report`, and its twins with `save`/`restore`
//! and `call`/`ret`, end with pc 3 and gas 10: the frame saved after two bumps
//! (pc 2, gas 11) is restored after the third, and the last bump runs from
//! there. `report` writes `100 * pc + gas`, 310, to the computation cell, so
//! both routes agree on the frame.
//!
//! `jump` matches and rebuilds the frame with a readable record: in a group
//! position `Frame { pc: p, gas: g }` is the whole nested cell, the same term
//! as `k::fragment![Frame { pc: p, gas: g }]`. `bump jump report` writes
//! 1112 (pc 11, gas 12).

use k::KResult;
use k::builtin::{Int, KSequence, List, int, list};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(
    cmd (Bump, Push, Pop, Save, Restore, Call, Ret, Report, Jump)
    > right seq (Seq)
)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("bump")] Bump(),
    #[k::syntax("push")] Push(),
    #[k::syntax("pop")] Pop(),
    #[k::syntax("save")] Save(),
    #[k::syntax("restore")] Restore(),
    #[k::syntax("call")] Call(),
    #[k::syntax("ret")] Ret(),
    #[k::syntax("report")] Report(),
    #[k::syntax("jump")] Jump(),
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

/// The current frame: a nested cell with two leaves.
#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub gas: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub stack: List,
    #[k::cell(nested)]
    pub frame: Frame,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "STACK")] stack: List,
        #[k::config_var(name = "PC")] pc: Int,
        #[k::config_var(name = "GAS")] gas: Int,
    ) -> Self {
        Self {
            k: k::k![pgm],
            stack,
            frame: Frame { pc, gas },
        }
    }
}

k::rules! {
    for Stmt;
    use Cmd::*;

    seq: Seq(s1, s2) => k::k![s1, s2];
}

k::rules! {
    for Machine;
    use Cmd::*;

    /// Advance the program counter and spend one unit of gas.
    bump: {
        k: [Bump(), ..],
        pc: p,
        gas: g,
    } => {
        k: [..],
        pc: int::add(p, 1),
        gas: int::sub(g, 1),
    };

    /// Save the whole current frame on the stack.
    push: {
        k: [Push(), ..],
        stack: s,
        frame: f,
    } => {
        k: [..],
        stack: list::concat(list::item(f), s),
        frame: f,
    };

    /// Restore the most recently saved frame.
    pop: {
        k: [Pop(), ..],
        stack: list::concat(list::item(f), s),
        frame: _,
    } => {
        k: [..],
        stack: s,
        frame: f,
    };

    /// Write the frame to the computation cell as `100 * pc + gas`.
    report: {
        k: [Report(), ..],
        pc: p,
        gas: g,
    } => {
        k: [int::add(int::mul(p, 100), g), ..],
        pc: p,
        gas: g,
    };

    /// Skip ten instructions, matching and rebuilding the whole frame.
    jump: {
        k: [Jump(), ..],
        frame: Frame { pc: p, gas: g },
    } => {
        k: [..],
        frame: Frame { pc: int::add(p, 10), gas: g },
    };

    /// `push` written the long way: restate every leaf of the frame.
    save: {
        k: [Save(), ..],
        stack: s,
        pc: p,
        gas: g,
    } => {
        k: [..],
        stack: list::concat(list::item(k::fragment![Frame { pc: p, gas: g }]), s),
        pc: p,
        gas: g,
    };

    /// `pop` written the long way.
    restore: {
        k: [Restore(), ..],
        stack: k::term![list::concat(list::item(k::fragment![Frame { pc: p, gas: g }]), s)],
        pc: _,
        gas: _,
    } => {
        k: [..],
        stack: s,
        pc: p,
        gas: g,
    };
}

/// `push` in the reference spelling.
#[k::rule(label = "call")]
pub fn call(
    s: k::Term<List>,
    f: crate::Frame,
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Call(), tail @ ..),
        stack: k::configuration::Cell(s),
        frame: f,
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        stack: k::configuration::Cell(list::concat(list::item(f), s)),
        frame: f,
        ..state
    }
}

/// `pop` in the reference spelling.
#[k::rule(label = "ret")]
pub fn ret(
    f: crate::Frame,
    s: k::Term<List>,
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Ret(), tail @ ..),
        stack: k::configuration::Cell(list::concat(list::item(f), s)),
        frame: _,
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        stack: k::configuration::Cell(s),
        frame: f,
        ..state
    }
}

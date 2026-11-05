//! A definition whose ends `tests/end_comparison.rs` compares: an unobservable top-level cell
//! and one inside a group, a constructor-valued cell with fields, a `List` and two `Map` cells,
//! a group, an optional leaf cell and an optional group cell, and a `List`, a `Set` and a `Map`
//! collection of repeated cells. Every configuration variable is copied into its own cell, so a
//! run of depth 0 ends with the values it was given; `toss` steps to `done(0)` or `done(1)`, so a
//! search has two final states; `finish(v)` steps to `done(v)` by the rule `finish`, at which a
//! run can stop; and `OnlyZero` is a partial function with no value but at 0.

use k::KResult;
use k::Term;
use k::builtin::{Bool, Int, KSequence, List, Map};

k::sorts! {
    Reg;
    Flags;
    Event;
    Stmt;
}

#[k::constructors(sort = Reg, result = KResult)]
#[k::precedence((A, B, C))]
#[rustfmt::skip]
pub enum Register {
    #[k::syntax("a")] A,
    #[k::syntax("b")] B,
    #[k::syntax("c")] C,
}

#[k::constructors(sort = Flags, result = KResult)]
#[rustfmt::skip]
pub enum FlagSet {
    #[k::syntax("flags({zf}, {cf})")] Flags { zf: Bool, cf: Bool },
}

#[k::constructors(sort = Event, result = KResult)]
#[k::precedence((Read, Write))]
#[rustfmt::skip]
pub enum CpuEvent {
    #[k::syntax("read({addr})")] Read { addr: Int },
    #[k::syntax("write({addr}, {value})")] Write { addr: Int, value: Int },
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Toss, Done, Finish))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("toss({value})")] Toss { value: Int },
    #[k::syntax("done({value})")] Done { value: Int },
    #[k::syntax("finish({value})")] Finish { value: Int },
}

#[k::rule(nondet = toss)]
fn toss_heads(k::term![Cmd::Toss { value }]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Done(1)
}

#[k::rule(nondet = toss)]
fn toss_tails(k::term![Cmd::Toss { value }]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Done(0)
}

#[k::rule]
fn finish(k::term![Cmd::Finish { value }]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Done(value)
}

/// `1` at `0`, and no value elsewhere.
#[k::function(partial, internal)]
#[k::requires(n.eq::<Int>(0))]
pub fn OnlyZero(n: Term<Int>) -> Term<Int> {
    1
}

#[k::cell]
pub struct Cpu {
    #[k::cell]
    pub ime: Bool,
    #[k::cell(unobservable)]
    pub w: Int,
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
    #[k::cell]
    pub count: Int,
}

#[k::cell]
pub struct Objects {
    #[k::cell(multiplicity = "*", cell_type = "Set", initial, nested)]
    pub obj: Obj,
}

#[k::cell]
pub struct Obj {
    #[k::cell]
    pub oid: Int,
}

#[k::cell]
pub struct Procs {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub process: Process,
}

/// One process; its first cell, `pid`, is the collection's key.
#[k::cell]
pub struct Process {
    #[k::cell]
    pub pid: Int,
    #[k::cell]
    pub ticks: Int,
}

#[k::cell]
pub struct Mark {
    #[k::cell]
    pub seen: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub regs: Map<Reg, Int>,
    #[k::cell]
    pub f: Flags,
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub bus: List<Event>,
    #[k::cell]
    pub memory: Map<Int, Int>,
    #[k::cell(nested)]
    pub cpu: Cpu,
    #[k::cell(unobservable)]
    pub z: Int,
    #[k::cell(multiplicity = "?")]
    pub timer: Option<Int>,
    #[k::cell(nested)]
    pub threads: Threads,
    #[k::cell(nested)]
    pub objects: Objects,
    #[k::cell(nested)]
    pub procs: Procs,
    #[k::cell(multiplicity = "?", nested)]
    pub mark: Option<Mark>,
}

impl Machine {
    #[k::init]
    #[expect(
        clippy::too_many_arguments,
        reason = "one parameter per configuration variable"
    )]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "REGS")] regs: Map<Reg, Int>,
        #[k::config_var(name = "F")] f: Flags,
        #[k::config_var(name = "PC")] pc: Int,
        #[k::config_var(name = "BUS")] bus: List<Event>,
        #[k::config_var(name = "MEMORY")] memory: Map<Int, Int>,
        #[k::config_var(name = "IME")] ime: Bool,
        #[k::config_var(name = "W")] w: Int,
        #[k::config_var(name = "Z")] z: Int,
    ) -> Self {
        Self {
            k: k::k![pgm],
            regs,
            f,
            pc,
            bus,
            memory,
            cpu: Cpu { ime, w },
            z,
            timer: k::absent!(0),
            threads: Threads {
                thread: Thread { id: 0, count: 0 },
            },
            objects: Objects {
                obj: Obj { oid: 0 },
            },
            procs: Procs {
                process: Process { pid: 0, ticks: 0 },
            },
            mark: k::absent!(Mark { seen: 0 }),
        }
    }
}

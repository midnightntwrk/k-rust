//! A definition whose configuration variables and cells cover every kind of `krs-exec` value:
//! enum variants (two named `C`, one of them spelled like the other), a struct variant, a
//! parametric constructor, a token sort, the builtins, the collections, a declared sort with
//! builtin subsorts and one whose only builtin subsort is `Float`, a renamed cell, a nested
//! group, an optional cell, a repeated cell, a function a value may apply, and a parameter whose
//! Rust name is not its K name. Every variable is copied into its own cell, so a run of depth 0
//! shows the values the configuration was given.

use k::builtin::{Bool, Bytes, Float, Id, Int, KSequence, List, Map, Set, String};
use k::{KResult, Term};

k::sorts! {
    Reg;
    Cond;
    Bus;
    Val: KResult;
    impl Val for Int;
    impl Val for String;
    impl Val for Float;
    Real: KResult;
    impl Real for Float;
}

#[k::constructors(sort = Reg, result = KResult)]
#[k::precedence((A, C))]
#[rustfmt::skip]
pub enum Register {
    #[k::syntax("a")] A,
    #[k::syntax("c")] C,
}

/// `c` is a register and a condition: at `KItem`, the text `c` has two readings.
#[k::constructors(sort = Cond, result = KResult)]
#[k::precedence((C, Z))]
#[rustfmt::skip]
pub enum Condition {
    #[k::syntax("c")] C,
    #[k::syntax("z")] Z,
}

#[k::constructors(sort = Bus, result = KResult)]
#[k::precedence((Read, Idle))]
#[rustfmt::skip]
pub enum Cycle {
    #[k::syntax("read({addr}, {value})")] Read { addr: Int, value: Int },
    #[k::syntax("idle")] Idle,
}

#[k::constructors(sort = Val, result = KResult)]
#[k::precedence((V, R, Nothing))]
#[rustfmt::skip]
pub enum ValSyntax {
    #[k::syntax("v({n})")] V { n: Int },
    #[k::syntax("r({x})")] R { x: Real },
    #[k::syntax("nothing")] Nothing,
}

/// `readBack(addr)` is the read of `addr` that returns `addr`: a function, whose application
/// in a configuration value is evaluated before the first step.
#[k::function(total, sort = Bus, syntax = "readBack({addr})")]
pub struct ReadBack {
    pub addr: Term<Int>,
}

#[k::equation]
fn read_back(k::term![ReadBack(addr)]: Term<Bus>) -> Term<Bus> {
    Cycle::Read(addr, addr)
}

/// `wrap(x)` has the sort of `x`.
#[k::constructor(sort = S, syntax = "wrap({inner})")]
pub struct Wrap<S: ?Sized> {
    pub inner: Term<S>,
}

/// `@`-prefixed names.
#[k::token(regex = r"@[a-z]+")]
pub struct Label(pub std::string::String);

#[k::cell]
pub struct Cpu {
    #[k::cell]
    pub regs: Map<Reg, Int>,
    #[k::cell(name = "eiPending")]
    pub ei_pending: Bool,
}

#[k::cell]
pub struct Threads {
    #[k::cell(multiplicity = "*", cell_type = "Map", initial, nested)]
    pub thread: Thread,
}

#[k::cell]
pub struct Thread {
    #[k::cell]
    pub id: Int,
    #[k::cell]
    pub count: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub cpu: Cpu,
    #[k::cell]
    pub bus: List<Bus>,
    #[k::cell]
    pub conds: Set<Cond>,
    #[k::cell]
    pub name: String,
    #[k::cell]
    pub blob: Bytes,
    #[k::cell]
    pub ratio: Float,
    #[k::cell]
    pub label: Label,
    #[k::cell]
    pub ident: Id,
    #[k::cell]
    pub val: Val,
    #[k::cell(multiplicity = "?")]
    pub timer: Option<Int>,
    #[k::cell(nested)]
    pub threads: Threads,
}

impl Machine {
    #[k::init]
    #[expect(
        clippy::too_many_arguments,
        reason = "one parameter per configuration variable"
    )]
    pub fn init(
        #[k::config_var(name = "REGS")] regs: Map<Reg, Int>,
        #[k::config_var(name = "EI")] ei: Bool,
        #[k::config_var(name = "BUS")] bus: List<Bus>,
        #[k::config_var(name = "CONDS")] conds: Set<Cond>,
        #[k::config_var(name = "NAME")] name: String,
        #[k::config_var(name = "BLOB")] rom: Bytes,
        #[k::config_var(name = "RATIO")] ratio: Float,
        #[k::config_var(name = "LABEL")] label: Label,
        #[k::config_var(name = "IDENT")] ident: Id,
        #[k::config_var(name = "VAL")] val: Val,
    ) -> Self {
        Self {
            k: k::k![],
            cpu: Cpu {
                regs,
                ei_pending: ei,
            },
            bus,
            conds,
            name,
            blob: rom,
            ratio,
            label,
            ident,
            val,
            timer: k::absent!(0),
            threads: Threads {
                thread: Thread { id: 0, count: 0 },
            },
        }
    }
}

//! A definition whose inputs are all data: no `#[k::init]` parameter is main (none is marked and
//! the computation cell reads none), so a case binds each by name. The parameters are a
//! `Map<Int, Int>`, a `Bytes`, an `Int` and a declared sort with a nullary and a struct
//! constructor, and each is copied into its own cell, so a run of depth 0 shows the values the
//! configuration was given. `Boot` is a total function and `OnlyZero` a partial one, defined
//! at 0 only, for inputs that apply a function.

use k::builtin::{Bytes, Int, KSequence, Map, int};
use k::KResult;

k::sorts! {
    Op: KResult;
}

#[k::constructors(sort = Op, result = KResult)]
#[k::precedence((Load, Halt))]
#[rustfmt::skip]
pub enum Instr {
    #[k::syntax("load({addr}, {len})")] Load { addr: Int, len: Int },
    #[k::syntax("halt")] Halt,
}

/// The entry address of a cartridge whose header word is `n`.
#[k::function(total, internal)]
pub fn Boot(n: k::Term<Int>) -> k::Term<Int> {
    int::add(n, 256)
}

/// `1` at `0`, and no value elsewhere.
#[k::function(partial, internal)]
#[k::requires(n.eq::<Int>(0))]
pub fn OnlyZero(n: k::Term<Int>) -> k::Term<Int> {
    1
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub memory: Map<Int, Int>,
    #[k::cell]
    pub rom: Bytes,
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub entry: Op,
}

impl Machine {
    #[k::init]
    pub fn init(memory: Map<Int, Int>, rom: Bytes, pc: Int, entry: Op) -> Self {
        Self {
            k: k::k![],
            memory,
            rom,
            pc,
            entry,
        }
    }
}

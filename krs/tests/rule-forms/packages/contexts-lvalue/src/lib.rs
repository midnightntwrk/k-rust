//! An lvalue context (KF-021): `++x` evaluates its operand to a location.
//!
//! `k::rewrite!(h => Op::LValue(h))` in a context's subject is K's
//! `context ++(HOLE => lvalue(HOLE))`: heating puts `lvalue(x)`, not `x`,
//! in front of the computation, so the variable is resolved to its location
//! and never read; cooling plugs the evaluated `lvalue(..)`'s operand back
//! as `++ loc(x)`, and the increment updates the store.

use k::KResult;
use k::builtin::{Id, Int, KSequence, Map, int};
use k::{Term, map};

k::sorts! {
    Exp;
    impl Exp for Id;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Inc, LValue))]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("++ {target}")]
    Inc { target: Exp },
    #[k::syntax("lvalue({target})")]
    LValue { target: Exp },
}

/// A variable's location, the result an lvalue evaluates to.
#[k::constructors(sort = Value, result = KResult)]
#[k::precedence((Loc))]
#[rustfmt::skip]
pub enum Location {
    #[k::syntax("loc({name})")]
    Loc { name: Id },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub store: Map<Id, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp, store: Map<Id, Int>) -> Self {
        Self {
            k: k::k![pgm],
            store,
        }
    }
}

/// K's `context ++(HOLE => lvalue(HOLE))`.
#[k::context(hole = h)]
fn increment_target(k::term![Op::Inc(k::rewrite!(h => Op::LValue(h)))]: Term<Exp>) {}

k::rules! {
    for Exp;
    use Op::*;

    /// An lvalue variable evaluates to its location.
    lvalue: LValue(name) => LValue(Location::Loc(name)) where name: Id;
}

/// `[inc]`: increment the variable at a location and return the new value.
#[k::rule(label = "inc")]
pub fn inc(
    name: Term<Id>,
    value: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(k::rewrite!(Op::Inc(Location::Loc(name)) => int::add(value, 1)), ..),
        store: k::configuration::Cell(map![name -> k::rewrite!(value => int::add(value, 1)), ..]),
        state @ ..
    }: Machine,
) {
}

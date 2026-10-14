//! Fresh values: `#[k::fresh(l: Loc)]` is K's `!L:Loc`.
//!
//! A fresh binder names a value the step creates: K calls the sort's
//! `freshGenerator` on the next value of the shared `<generatedCounter>`
//! cell, so the value does not exist until the step happens and occurs only
//! on the result side. `fresh_loc` is the generator of `Loc`; Int has K's
//! own (`freshInt`).
//!
//! The counter is shared across sorts: `alloc a; tx; alloc b; tx;` allocates
//! `loc(0)`, records transaction `1`, allocates `loc(2)`, and records
//! transaction `3`. Each rule has one fresh binder, because K assigns the
//! counter offsets of several binders in an unspecified order.

use k::builtin::{Id, Int, KSequence, Map, map};
use k::{KResult, Term};

k::sorts! {
    Stmt;
    Loc: KResult;
}

#[k::constructors(sort = Loc, result = KResult)]
#[k::precedence((Loc))]
#[rustfmt::skip]
pub enum LocSyntax {
    #[k::syntax("loc({n})")] Loc { n: Int },
}

/// The generator of `Loc`: K calls it with the counter value.
#[k::function(total, fresh_generator, sort = Loc, syntax = "freshLoc({seed})")]
pub struct FreshLoc {
    pub seed: Term<Int>,
}

#[k::equation]
fn fresh_loc(k::term![FreshLoc(seed)]: Term<Loc>) -> Term<Loc> {
    LocSyntax::Loc(seed)
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(
    stmt (Alloc, Tx)
    > right seq_stmt (Sequence)
)]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("alloc {name};")] Alloc { name: Id },
    #[k::syntax("tx;")] Tx(),
    #[k::syntax("{first} {second}")] Sequence { first: Stmt, second: Stmt },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Loc>,
    #[k::cell]
    pub store: Map<Loc, Int>,
    #[k::cell]
    pub txs: Map<Int, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: k::map![],
            store: k::map![],
            txs: k::map![],
        }
    }
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    /// Expose the right-associated statement pair as K sequencing.
    step: Sequence(s1, s2) => k::k![s1, s2];
}

k::rules! {
    for Machine;
    use StmtSyntax::Alloc;

    /// Bind `x` to a newly allocated location holding 0.
    #[k::fresh(l: Loc)]
    alloc: {
        k: [Alloc(x), ..],
        env: e,
        store: s,
    } => {
        k: [..],
        env: map::update(e, x, l),
        store: map::update(s, l, 0),
    };
}

/// Record a new transaction number: the reference spelling of a fresh Int.
#[k::fresh(t: Int)]
#[k::rule(label = "tx")]
pub fn tx(
    ts: Term<Map>,
    k::cells! {
        k: k::configuration::KCell(StmtSyntax::Tx(), tail @ ..),
        txs: k::configuration::Cell(ts),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        txs: k::configuration::Cell(map::update(ts, t, 1)),
        ..state
    }
}

//! A Set cell collection (KF-023): objects created with template defaults.
//!
//! `<obj>` is a `cell_type = "Set"` collection; braces match *some*
//! instances. `mk n` creates `Obj { oid: n, .. }`, whose `hits` takes the
//! template default 0 (K's right-hand `...`); `touch n` updates the matched
//! object in place; `rm n` removes it; `count n` reads its hits. `single` names
//! the collection exactly, with no `..`: it applies only when exactly one
//! object exists, and K writes it inside the parent `<objects>` cell.

use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(
    cmd (Mk, Touch, Rm, Count, Single)
    > right seq (Seq)
)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("mk {oid}")] Mk { oid: Int },
    #[k::syntax("touch {oid}")] Touch { oid: Int },
    #[k::syntax("rm {oid}")] Rm { oid: Int },
    #[k::syntax("count {oid}")] Count { oid: Int },
    #[k::syntax("single")] Single(),
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

/// The object collection's parent.
#[k::cell]
pub struct Objects {
    #[k::cell(multiplicity = "*", cell_type = "Set", nested)]
    pub obj: Obj,
}

/// One object.
#[k::cell]
pub struct Obj {
    #[k::cell]
    pub oid: Int,
    #[k::cell]
    pub hits: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub objects: Objects,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            objects: Objects {
                obj: Obj { oid: 0, hits: 0 },
            },
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

    /// Create an object; its `hits` takes the template default.
    mk: {
        k: [Mk(n), ..],
        obj: { .. },
    } => {
        k: [..],
        obj: { Obj { oid: n, .. }, .. },
    };

    /// Count one hit on object `n`.
    touch: {
        k: [Touch(n), ..],
        obj: { o @ Obj { oid: n, hits: h }, .. },
    } => {
        k: [..],
        obj: { Obj { hits: int::add(h, 1), .. o }, .. },
    };

    /// Remove object `n`.
    rm: {
        k: [Rm(n), ..],
        obj: { Obj { oid: n, .. }, .. },
    } => {
        k: [..],
        obj: { .. },
    };

    /// Write the hits of object `n` to the computation cell.
    count: {
        k: [Count(n), ..],
        obj: { Obj { oid: n, hits: h }, .. },
    } => {
        k: [h, ..],
    };

    /// Write the id of the only object; stuck unless exactly one exists.
    single: {
        k: [Single(), ..],
        obj: { o @ Obj { oid: n, .. } },
    } => {
        k: [n, ..],
        obj: { Obj { .. o } },
    };
}

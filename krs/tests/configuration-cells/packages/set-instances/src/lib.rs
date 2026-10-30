//! Set cell collections matched by computed instances (NT-10).
//!
//! `<obj>` and `<bag>` are `cell_type = "Set"` collections. A rule's
//! instance pattern holds terms computed from the rule's other bindings
//! (`oid: n + 1`), so it selects the instance whose cells equal the computed
//! values, as a map key that is computed is looked up. `mk n` creates an
//! object with the template's hits 0; `touch n` adds a hit; `probe n` needs
//! the object `n + 1` with no hits, `drop n` removes it, `bump n` sets its
//! hits to 1 and `find n` matches it with a name and rebuilds it; `next n`
//! needs the objects `n` and `n + 1` with equal hits, and `dup n` two equal
//! objects, which a set never holds; `dz n` and `check n` guard the match
//! with a condition; `via x` computes the id from an `env` entry. `mkb n`
//! creates a bag whose set and map cells are computed from `n`, and `bags`,
//! `bagm` and `bagc` match a bag by its whole set and map cells, the last in
//! a `cells!` rule. A stuck program ends with its command at the
//! computation's head.

use k::KResult;
use k::builtin::{Int, KSequence, Map, Set, int, map};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(
    cmd (Mk, Touch, Probe, Drop, Bump, Next, Via, Find, Check, Dup, Dz, Mkb, Bags, Bagm, Bagc)
    > right seq (Seq)
)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("mk {oid}")] Mk { oid: Int },
    #[k::syntax("touch {oid}")] Touch { oid: Int },
    #[k::syntax("probe {oid}")] Probe { oid: Int },
    #[k::syntax("drop {oid}")] Drop { oid: Int },
    #[k::syntax("bump {oid}")] Bump { oid: Int },
    #[k::syntax("next {oid}")] Next { oid: Int },
    #[k::syntax("via {key}")] Via { key: Int },
    #[k::syntax("find {oid}")] Find { oid: Int },
    #[k::syntax("check {oid}")] Check { oid: Int },
    #[k::syntax("dup {oid}")] Dup { oid: Int },
    #[k::syntax("dz {oid}")] Dz { oid: Int },
    #[k::syntax("mkb {id}")] Mkb { id: Int },
    #[k::syntax("bags {id}")] Bags { id: Int },
    #[k::syntax("bagm {id}")] Bagm { id: Int },
    #[k::syntax("bagc {id}")] Bagc { id: Int },
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::cell]
pub struct Objects {
    #[k::cell(multiplicity = "*", cell_type = "Set", nested)]
    pub obj: Obj,
}

#[k::cell]
pub struct Obj {
    #[k::cell]
    pub oid: Int,
    #[k::cell]
    pub hits: Int,
}

/// A Set collection whose instances hold a set and a map.
#[k::cell]
pub struct Sacks {
    #[k::cell(multiplicity = "*", cell_type = "Set", nested)]
    pub bag: Bag,
}

#[k::cell]
pub struct Bag {
    #[k::cell]
    pub key: Int,
    #[k::cell]
    pub s: Set,
    #[k::cell]
    pub m: Map,
}

#[k::cell]
pub struct Meta {
    #[k::cell]
    pub a: Int,
    #[k::cell]
    pub b: Int,
}

#[k::cell]
pub struct Table {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub row: Row,
}

#[k::cell]
pub struct Row {
    #[k::cell]
    pub id: Int,
    #[k::cell]
    pub value: Stmt,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell(nested)]
    pub objects: Objects,
    #[k::cell(nested)]
    pub table: Table,
    #[k::cell(nested)]
    pub sacks: Sacks,
    #[k::cell(nested)]
    pub meta: Meta,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: map![1 -> 4],
            objects: Objects {
                obj: Obj { oid: 0, hits: 0 },
            },
            table: Table {
                row: Row {
                    id: 0,
                    value: Cmd::Mk(0),
                },
            },
            sacks: Sacks {
                bag: Bag {
                    key: 0,
                    s: set![],
                    m: map![],
                },
            },
            meta: Meta { a: 0, b: 0 },
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

    mk: {
        k: [Mk(n), ..],
        obj: { .. },
    } => {
        k: [..],
        obj: { Obj { oid: n, .. }, .. },
    };

    touch: {
        k: [Touch(n), ..],
        obj: { o @ Obj { oid: n, hits: h }, .. },
    } => {
        k: [..],
        obj: { Obj { hits: int::add(h, 1), ..o }, .. },
    };

    probe: {
        k: [Probe(n), ..],
        obj: { Obj { oid: n + 1, hits: 0 }, .. },
    } => {
        k: [..],
    };

    drop: {
        k: [Drop(n), ..],
        obj: { Obj { oid: n + 1, hits: 0 }, .. },
    } => {
        k: [..],
        obj: { .. },
    };

    bump: {
        k: [Bump(n), ..],
        obj: { o @ Obj { oid: n + 1, hits: 0 }, .. },
    } => {
        k: [..],
        obj: { Obj { hits: 1, ..o }, .. },
    };

    next: {
        k: [Next(n), ..],
        obj: { Obj { oid: n, hits: h }, Obj { oid: n + 1, hits: h }, .. },
    } => {
        k: [..],
    };

    dup: {
        k: [Dup(n), ..],
        obj: { Obj { oid: n + 1, hits: 0 }, Obj { oid: n + 1, hits: 0 }, .. },
    } => {
        k: [..],
    };

    #[k::requires(10 / n > 0)]
    dz: {
        k: [Dz(n), ..],
        obj: { Obj { oid: n + 100, hits: 0 }, .. },
    } => {
        k: [..],
    };

    mkb: {
        k: [Mkb(n), ..],
        bag: { .. },
    } => {
        k: [..],
        bag: { Bag { key: n, s: set![n, n + 1], m: map![n -> n + 1] }, .. },
    };

    bags: {
        k: [Bags(n), ..],
        bag: { Bag { key: n, s: set![n + 1, n], m: map![n -> n + 1] }, .. },
    } => {
        k: [..],
    };

    bagm: {
        k: [Bagm(n), ..],
        bag: { Bag { key: n - 1, s: set![n - 1, n], m: map![n - 1 -> n] }, .. },
    } => {
        k: [..],
    };

    #[k::requires(n > 0)]
    check: {
        k: [Check(n), ..],
        obj: { Obj { oid: n * 2, hits: n - 1 }, .. },
    } => {
        k: [..],
    };
}

#[k::rule(label = "find")]
fn find(
    n: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Find(n), tail @ ..),
        Objects::obj: {
            me @ k::fragment![crate::Obj { oid: n + 1, hits: 0 }],
            instances0 @ ..
        },
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Objects::obj: { k::fragment![crate::Obj { ..me }], ..instances0 },
        ..state
    }
}

/// A readable map read's value binder stays fresh, so a `cells!` rule reads
/// the instance's id from an `env` entry.
#[k::rule(label = "via")]
fn via(
    x: k::Term<Int>,
    v: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Via(x), tail @ ..),
        env: k::configuration::Cell(map![x -> v, ..]),
        Objects::obj: {
            k::fragment![crate::Obj { oid: int::add(v, 1), hits: 0 }],
            instances0 @ ..
        },
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Objects::obj: { ..instances0 },
        ..state
    }
}

/// An exact map cell is part of the instance's value, its key read as a
/// key is.
#[k::rule(label = "bagc")]
fn bagc(
    n: k::Term<Int>,
    k::cells! {
        k: k::configuration::KCell(Cmd::Bagc(n), tail @ ..),
        Sacks::bag: {
            k::fragment![crate::Bag { key: n + 1, s: set![n + 2, n + 1], m: map![n + 1 -> int::add(n, 2)] }],
            instances0 @ ..
        },
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        Sacks::bag: { ..instances0 },
        ..state
    }
}

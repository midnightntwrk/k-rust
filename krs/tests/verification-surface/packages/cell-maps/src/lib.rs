//! Claims over a map cell with symbolic keys.
//!
//! The `env` cell is a map from integers to integers, and every key a claim
//! names is a variable. A claim's map is the whole cell: `map![a -> 0]` is
//! the map holding exactly the key `a`. Each claim must be proved by
//! `krs prove` and by Java `kprove` on the emitted K:
//!
//! - `sym-one`: `two(a, b)` rewrites the entry of `a` to 10 in a map that
//!   holds one key;
//! - `sym-two`: the same step in a map that holds `a` and `b`, two distinct
//!   keys since a map holds each key once; only the entry of `a` changes;
//! - `set-get`: `set(a)` replaces the whole map by `map![a -> 10]` and
//!   `get(a)` reads the entry back, so the computation ends with `got(10)`
//!   and some map;
//! - `unmatched-keys`: `put(a, 10)` and `put(b, 11)` write keys the empty
//!   start map does not hold, so the end map is the update chain
//!   `.Map [ a <- 10 ] [ b <- 11 ]`, whatever `a` and `b` are.
//!
//! Each claim has a negative control, `<label>-false`, whose end state no
//! path reaches; neither prover may prove it.

use k::builtin::{Int, KSequence, Map, map};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("two({a},{b})")] Two { a: Int, b: Int },
    #[k::syntax("set({a})")] Set { a: Int },
    #[k::syntax("get({a})")] Get { a: Int },
    #[k::syntax("got({a})")] Got { a: Int },
    #[k::syntax("put({a},{v})")] Put { a: Int, v: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            env: map![],
        }
    }
}

/// `two(a, b)` writes 10 at the key `a`, which the map holds.
#[k::rule(label = "two")]
fn two(
    a: Term<Int>,
    b: Term<Int>,
    v: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Two(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> v, rest @ ..]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10, ..rest]),
        ..state
    }
}

/// `set(a)` replaces the whole map by the one that holds 10 at `a`.
#[k::rule(label = "set")]
fn set(
    a: Term<Int>,
    e: Term<Map>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Set(a), tail @ ..),
        env: k::configuration::Cell(e),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10]),
        ..state
    }
}

/// `get(a)` reads the entry of `a`.
#[k::rule(label = "get")]
fn get(
    a: Term<Int>,
    v: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Get(a), tail @ ..),
        env: k::configuration::Cell(map![a -> v, ..]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Got(v), ..tail),
        ..state
    }
}

/// `put(a, v)` writes `v` at the key `a`, held or not.
#[k::rule(label = "put")]
fn put(
    a: Term<Int>,
    v: Term<Int>,
    e: Term<Map>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Put(a, v), tail @ ..),
        env: k::configuration::Cell(e),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> v, ..e]),
        ..state
    }
}

/// One key: its entry becomes 10.
#[k::claim(all_paths, label = "sym-one")]
fn sym_one(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Two(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10]),
        ..state
    }
}

/// Two matched keys: only the entry of `a` changes.
#[k::claim(all_paths, label = "sym-two")]
fn sym_two(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Two(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> 0, b -> 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10, b -> 0]),
        ..state
    }
}

/// A rule's result read back: `set(a)` then `get(a)` ends with `got(10)`.
#[k::claim(all_paths, label = "set-get")]
#[k::exists(after: Map)]
fn set_get(
    a: Term<Int>,
    e: Term<Map>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Set(a), ExpSyntax::Get(a), tail @ ..),
        env: k::configuration::Cell(e),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Got(10), ..tail),
        env: k::configuration::Cell(after),
        ..state
    }
}

/// Two keys the empty start map does not hold: the end map is the update chain.
#[k::claim(all_paths, label = "unmatched-keys")]
fn unmatched_keys(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Put(a, 10), ExpSyntax::Put(b, 11), tail @ ..),
        env: k::configuration::Cell(map![]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10, b -> 11]),
        ..state
    }
}

// Negative controls: each claim above with a false end state, which neither prover may prove.

/// `sym-one` ending with 11, a value no step writes.
#[k::claim(all_paths, label = "sym-one-false")]
fn sym_one_false(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Two(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 11]),
        ..state
    }
}

/// `sym-two` with the entry of `b` changed too.
#[k::claim(all_paths, label = "sym-two-false")]
fn sym_two_false(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Two(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> 0, b -> 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10, b -> 10]),
        ..state
    }
}

/// `set-get` reading back 11, a value `set` never writes.
#[k::claim(all_paths, label = "set-get-false")]
#[k::exists(after: Map)]
fn set_get_false(
    a: Term<Int>,
    e: Term<Map>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Set(a), ExpSyntax::Get(a), tail @ ..),
        env: k::configuration::Cell(e),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Got(11), ..tail),
        env: k::configuration::Cell(after),
        ..state
    }
}

/// `unmatched-keys` with 11 at `a`, where `put(a, 10)` wrote 10.
#[k::claim(all_paths, label = "unmatched-keys-false")]
fn unmatched_keys_false(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Put(a, 10), ExpSyntax::Put(b, 11), tail @ ..),
        env: k::configuration::Cell(map![]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 11, b -> 11]),
        ..state
    }
}

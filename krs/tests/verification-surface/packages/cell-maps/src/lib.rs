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
//!   `.Map [ a <- 10 ] [ b <- 11 ]`, whatever `a` and `b` are;
//! - `moved-one` and `moved-rest`: `move(a, b)` matches `a` and writes 10 at
//!   `a`, then 0 at `b`, over the rest of the map, which the rule binds on the
//!   left only (finding NT-9-1); the end map is that rest with the two entries
//!   written over it in that order, so where `b` is `a` the later entry's 0 is
//!   the value at `a`, and where `b` is a key of the rest it is overwritten.
//!   `moved-one`'s rest is empty; `moved-rest`'s is any map, `rest`;
//! - `moved-anon`: `movea(a, b)` writes the same entries over the rest its
//!   rule leaves anonymous (`..`), which the rule binds on the left only to a
//!   name it generates; the end map is `moved-rest`'s.
//!
//! Each claim has a negative control, `<label>-false`, whose end state no
//! path reaches; neither prover may prove it. The `moved` controls write the
//! same entries in the other order, which differs from the rule's map only
//! where `b` is `a`: a prover that took the symbolic keys for distinct would
//! prove them.

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
    #[k::syntax("move({a},{b})")] Move { a: Int, b: Int },
    #[k::syntax("movea({a},{b})")] MoveAnon { a: Int, b: Int },
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

/// `move(a, b)` writes 10 at `a`, then the old value at `b`, over the rest of the map: `b` may
/// be any key, so the result is the update chain over the rest.
#[k::rule(label = "move")]
fn move_rule(
    a: Term<Int>,
    b: Term<Int>,
    v: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Move(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> v, rest @ ..]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10, b -> v, ..rest]),
        ..state
    }
}

/// `movea(a, b)` is `move(a, b)` over a rest the rule does not name.
#[k::rule(label = "movea")]
fn move_anon(
    a: Term<Int>,
    b: Term<Int>,
    v: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::MoveAnon(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> v, ..]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10, b -> v]),
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

/// `move(a, b)` over the map holding `a` alone: 10 then 0 written over the empty rest.
#[k::claim(all_paths, label = "moved-one")]
fn moved_one(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Move(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10, b -> 0]),
        ..state
    }
}

/// `move(a, b)` over `a` and any rest: that rest with 10 at `a`, then 0 at `b`, written over it.
#[k::claim(all_paths, label = "moved-rest")]
fn moved_rest(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Move(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> 0, rest @ ..]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10, b -> 0, ..rest]),
        ..state
    }
}

/// `movea(a, b)` over `a` and any rest: that rest with 10 at `a`, then 0 at `b`, written over it.
#[k::claim(all_paths, label = "moved-anon")]
fn moved_anon(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::MoveAnon(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> 0, rest @ ..]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![a -> 10, b -> 0, ..rest]),
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

/// `moved-one` with the two entries in the other order: wrong where `b` is `a`.
#[k::claim(all_paths, label = "moved-one-false")]
fn moved_one_false(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Move(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![b -> 0, a -> 10]),
        ..state
    }
}

/// `moved-rest` with the two entries in the other order: wrong where `b` is `a`.
#[k::claim(all_paths, label = "moved-rest-false")]
fn moved_rest_false(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::Move(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> 0, rest @ ..]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![b -> 0, a -> 10, ..rest]),
        ..state
    }
}

/// `moved-anon` with the two entries in the other order: wrong where `b` is `a`.
#[k::claim(all_paths, label = "moved-anon-false")]
fn moved_anon_false(
    a: Term<Int>,
    b: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(ExpSyntax::MoveAnon(a, b), tail @ ..),
        env: k::configuration::Cell(map![a -> 0, rest @ ..]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![b -> 0, a -> 10, ..rest]),
        ..state
    }
}

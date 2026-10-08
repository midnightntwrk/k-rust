//! Builtin MAP operations: one rule per operation over the map in the `m` cell.
//!
//! K has no MAP-SYNTAX module, so a program cannot contain a map. The
//! configuration starts with `m` holding `1 |-> 10 2 |-> 20 3 |-> 30`, and each
//! program is one operation whose rule reads that cell and leaves an Int or a
//! Bool in `k`. A lookup's result is projected to the sort its position
//! expects, so the lookups sit in an `int::add(.., 0)`, whose operand is Int.

use k::KResult;
use k::builtin::{Bool, Int, KSequence, Map, int, list, map, set};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

/// One case per Map operation; `key` and `default` are program values.
#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Remove, RemoveAll, Keys, KeysList, Values, Size, UpdateAll, GetOrDefault))]
#[rustfmt::skip]
pub enum Case {
    #[k::syntax("removeKey({key})")]
    Remove { key: Int },
    #[k::syntax("removeKeys({key})")]
    RemoveAll { key: Int },
    #[k::syntax("hasKey({key})")]
    Keys { key: Int },
    #[k::syntax("keyCount()")]
    KeysList,
    #[k::syntax("hasValue({key})")]
    Values { key: Int },
    #[k::syntax("entryCount()")]
    Size,
    #[k::syntax("restore({key})")]
    UpdateAll { key: Int },
    #[k::syntax("lookup({key}, {default})")]
    GetOrDefault { key: Int, default: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub m: Map<Int, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            m: k::map![1 -> 10, 2 -> 20, 3 -> 30],
        }
    }
}

k::rules! {
    for Machine;
    use Case::*;

    /// `map::remove`: the size after removing `key`.
    remove: {
        k: [Remove { key }, ..],
        m: m,
    } => {
        k: [map::size(map::remove(m, key)), ..],
        m: m,
    };

    /// `map::remove_all`: the size after removing the keys `{key, 3}`.
    remove_all: {
        k: [RemoveAll { key }, ..],
        m: m,
    } => {
        k: [map::size(map::remove_all(m, set::union(set::item(key), set::item(3)))), ..],
        m: m,
    };

    /// `map::keys`: whether `key` is a key.
    keys: {
        k: [Keys { key }, ..],
        m: m,
    } => {
        k: [set::contains(key, map::keys(m)), ..],
        m: m,
    };

    /// `map::keys_list`: the number of keys.
    keys_list: {
        k: [KeysList(), ..],
        m: m,
    } => {
        k: [list::size(map::keys_list(m)), ..],
        m: m,
    };

    /// `map::values`: whether `key` is a value.
    values: {
        k: [Values { key }, ..],
        m: m,
    } => {
        k: [list::contains(key, map::values(m)), ..],
        m: m,
    };

    /// `map::size`.
    size: {
        k: [Size(), ..],
        m: m,
    } => {
        k: [map::size(m), ..],
        m: m,
    };

    /// `map::update_all`: `m` without `key`, updated with `m`, maps `key` to its value again.
    update_all: {
        k: [UpdateAll { key }, ..],
        m: m,
    } => {
        k: [int::add(map::get_or_default(map::update_all(map::remove(m, key), m), key, 0), 0), ..],
        m: m,
    };

    /// `map::get_or_default`.
    get_or_default: {
        k: [GetOrDefault { key, default }, ..],
        m: m,
    } => {
        k: [int::add(map::get_or_default(m, key, default), 0), ..],
        m: m,
    };
}

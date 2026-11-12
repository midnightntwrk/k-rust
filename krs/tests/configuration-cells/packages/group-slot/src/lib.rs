//! A definition that holds the group `Core` and starts cells at sorts above
//! the sorts of their initial values.
//!
//! `Slotted { core, mem, store, trail, journal }` holds the group as `Board`
//! does. Three of its cells start from a term of a subsort of the cell's
//! sort or of an argument's sort:
//!
//! - `store`, of sort `Store`, starts as `Image()`, a `Map`;
//! - `trail`, of sort `Trail`, starts as a one-item `List`;
//! - `journal` starts as `Was { store: Image() }`, whose field is a `Store`.
//!
//! K has no `MAP-SYNTAX` or `LIST-SYNTAX` module, so `syntax Store ::= Map`
//! and `syntax Trail ::= List` are not program syntax. The group's rules need
//! the configuration, so it is emitted in `KRS-GROUP-SLOT-CONFIGURATION`,
//! below the group's module, and a K module reads only its own subsort
//! sentences and those of the modules it imports. That module therefore
//! holds the two subsort sentences, with the declaration of `Image`; the
//! equation of `Image` and the bus rules, which use the same subsorts, stay
//! in `KRS-GROUP-SLOT`, which imports it.

use k::Term;
use k::builtin::{Int, List, Map, list, map};

k::sorts! {
    Store;
    Trail;
    Journal;
    impl Store for Map;
    impl Trail for List;
}

/// What the store was when the definition started.
#[k::constructors(sort = Journal, result = KResult)]
#[rustfmt::skip]
pub enum Entry {
    #[k::syntax("was ( {store} )")] Was { store: Store },
}

/// The memory a definition starts with.
#[k::function(total, internal)]
pub fn Image() -> Term<Map<Int, Int>> {
    k::map![3 -> 9, 4 -> 10]
}

#[k::configuration]
pub struct Slotted {
    #[k::cell(nested)]
    pub core: group_core::Core,
    #[k::cell]
    pub mem: Map<Int, Int>,
    #[k::cell]
    pub store: Store,
    #[k::cell]
    pub trail: Trail,
    #[k::cell]
    pub journal: Journal,
}

impl Slotted {
    #[k::init]
    pub fn init(pgm: group_core::Prog) -> Self {
        Self {
            core: group_core::Core {
                k: k::k![pgm],
                pc: 0,
                acc: 0,
            },
            mem: Image(),
            store: Image(),
            trail: list::item(0),
            journal: { Entry::Was { store: Image() } },
        }
    }
}

k::rules! {
    for Slotted;
    use group_core::BusOp::*;

    /// Answer a read with the value at `addr`.
    read: {
        k: [Read { addr }, ..],
        mem: { addr -> value, .. },
    } => {
        k: [Reply { value }, ..],
    };

    /// Write `value` at `addr`, and keep the memory and the address written.
    write: {
        k: [Write { addr, value }, ..],
        mem,
        store: _,
        trail: _,
    } => {
        k: [..],
        mem: map::update(mem, addr, value),
        store: map::update(mem, addr, value),
        trail: list::item(addr),
    };
}

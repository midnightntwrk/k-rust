//! A definition that holds the group `Core` beside a memory, with an end of its own.
//!
//! `Small { core, mem }` answers the core's `busRead(addr)` from `mem`. A read of the guarded
//! address 13 becomes `guarded ( 13 )`, which no rule executes: `#[k::end(refused)]` on the
//! variant `Guarded` declares that state an end, whose reason is the item. A read of any other
//! address `mem` does not map has no rule: `unmapped_read` declares that state a `refused` end,
//! whose reason is the address. It is typed by the configuration and names the group's
//! computation cell beside `mem`, as a rule for `Small` does, and its condition leaves out the
//! guarded address, at which the rule `guard` applies.
//!
//! The group's own ends (`end_core::halt`, `end_core::trap`, `end_core::drained`,
//! `end_core::overflow`) are ends of this definition too, under those names.

use k::Term;
use k::builtin::{Int, Map, int, map};

k::sorts! {
    Fault;
}

/// What a read of the guarded address leaves on the computation.
#[k::constructors(sort = Fault, result = KResult, internal)]
#[rustfmt::skip]
pub enum Guard {
    #[k::end(refused)]
    #[k::syntax("guarded ( {addr} )")] Guarded { addr: Int },
}

#[k::configuration]
pub struct Small {
    #[k::cell(nested)]
    pub core: end_core::Core,
    #[k::cell]
    pub mem: Map<Int, Int>,
}

impl Small {
    #[k::init]
    pub fn init(pgm: end_core::Prog) -> Self {
        Self {
            core: end_core::Core {
                k: k::k![pgm],
                pc: 0,
                acc: 0,
            },
            mem: k::map![7 -> 2],
        }
    }
}

/// A read of an address the memory does not map is refused, with the address.
#[k::end(refused)]
#[k::requires(!map::in_keys(addr, mem) && int::ne(addr, 13))]
fn unmapped_read(
    addr: Term<Int>,
    mem: Term<Map>,
    k::cells! {
        end_core::Core::k: k::configuration::KCell(end_core::BusOp::Read { addr }, ..),
        mem: k::configuration::Cell(mem),
        ..
    }: Small,
) -> Term<Int> {
    addr
}

k::rules! {
    for Small;
    use Guard::*;
    use end_core::BusOp::*;

    /// A read of the guarded address faults.
    #[k::requires(int::eq(addr, 13))]
    guard: {
        k: [Read { addr }, ..],
    } => {
        k: [Guarded { addr }, ..],
    };

    /// Answer a read of any other address with the value at `addr`.
    #[k::requires(int::ne(addr, 13))]
    read: {
        k: [Read { addr }, ..],
        mem: { addr -> value, .. },
    } => {
        k: [Reply { value }, ..],
    };
}

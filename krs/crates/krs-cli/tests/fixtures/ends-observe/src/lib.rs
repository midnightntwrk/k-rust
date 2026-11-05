//! An observer of the `ends` fixture (`tests/end_comparison.rs`): a package that depends on it,
//! declares a sort of its own and views of its `bus` cell, and is imported by no definition, so
//! the views are resolved and evaluated in this package's definition and the compared one does
//! not hold them. `WithRead` builds a value with the fixture's constructor.

use k::KResult;
use k::Term;
use k::builtin::{Int, List};

k::sorts! {
    Summary;
}

#[k::constructors(sort = Summary, result = KResult)]
#[rustfmt::skip]
pub enum Shape {
    #[k::syntax("counted({events})")] Counted { events: Int },
}

/// The shape of an event log, as a value of this package's own sort.
#[k::function(total, internal)]
pub fn LogShape(log: Term<List>) -> Term<Summary> {
    Shape::Counted(log.len())
}

/// The log with one more read, built from the compared definition's constructor.
#[k::function(total, internal)]
pub fn WithRead(log: Term<List>) -> Term<List> {
    [..log, ends::CpuEvent::Read(0)]
}

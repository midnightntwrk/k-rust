//! An observer of the `observations` fixture (`tests/observation_core.rs`): a package that
//! depends on it and that no definition imports, so the observations' functions are resolved and
//! evaluated in this package's definition and the machine's definition does not hold them.

use k::builtin::{Bool, Int, List};
use k::Term;

/// A view of `n`: twice its value.
#[k::function(total, internal)]
pub fn Twice(n: Term<Int>) -> Term<Int> {
    n * 2
}

/// A component of two cells: how far `n` is past `phase`.
#[k::function(total, internal)]
pub fn Gap(n: Term<Int>, phase: Term<Int>) -> Term<Int> {
    n - phase
}

/// A filter: whether `n` is even.
#[k::function(total, internal)]
pub fn Even(n: Term<Int>) -> Term<Bool> {
    n % 2 == 0
}

/// Whether a flag is set: of a parameter sort that admits no `Int` cell.
#[k::function(total, internal)]
pub fn Flag(flag: Term<Bool>) -> Term<Bool> {
    flag
}

/// A component with no value from 3 on: partial, defined by its equation alone.
#[k::function(partial, internal)]
#[k::requires(n < 3)]
pub fn Small(n: Term<Int>) -> Term<Int> {
    n
}

/// A component whose evaluation climbs for ever: it spends any budget.
#[k::function(total, internal)]
pub fn Climb(n: Term<Int>) -> Term<Int> {
    Rise(n)
}

/// `Rise(n + 1)`, for ever.
#[k::function(total, internal)]
pub fn Rise(n: Term<Int>) -> Term<Int> {
    Rise(n + 1)
}

/// An element function of the `out` log: each output twice.
#[k::function(total, internal)]
pub fn Twin(item: Term<machine::Out>) -> Term<List<machine::Out>> {
    [item, item]
}

/// No element function: its result is no List.
#[k::function(total, internal)]
pub fn Number(item: Term<machine::Out>) -> Term<Int> {
    0
}

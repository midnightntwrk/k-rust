//! An observer of the `stop-condition` fixture (`tests/stop_condition.rs`): a package that
//! depends on it and that no definition imports, so its conditions are resolved and evaluated in
//! this package's definition and the counter's definition does not hold them.

use k::builtin::{Bool, Int};
use k::Term;

/// Whether `m` has passed `n` by at least 4: a condition of two cells, `n` and `m`, which holds
/// from the arrival where `m - n` is at least 4.
#[k::function(total, internal)]
pub fn Apart(n: Term<Int>, m: Term<Int>) -> Term<Bool> {
    m - n >= 4
}

/// A condition with no value below 0: partial, defined by its equation alone.
#[k::function(partial, internal)]
#[k::requires(n >= 0)]
pub fn Natural(n: Term<Int>) -> Term<Bool> {
    n >= 10
}

/// A condition whose evaluation climbs for ever: it spends any budget.
#[k::function(total, internal)]
pub fn Climb(n: Term<Int>) -> Term<Bool> {
    Rise(n)
}

/// `Rise(n + 1)`, for ever.
#[k::function(total, internal)]
pub fn Rise(n: Term<Int>) -> Term<Bool> {
    Rise(n + 1)
}

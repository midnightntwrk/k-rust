//! The work counters of the k-rust backend that krs links, for `krs run --counters` and
//! `krs search --counters`.
//!
//! k-rust counts its algorithmic work in thread-local counters (`k_rust::measure`), which a
//! release build leaves off until it is asked to count. [`count`] asks, and [`Work::taken`] reads
//! what the current thread did since a [`Work::start`]: the run's own work, without the load of
//! the definition before it, so that a compiled stage restored from the cache and one compiled
//! anew count the same.
//!
//! Counting writes thread-local cells and nothing a computation reads, so it changes no result;
//! it takes time, so a caller counts only when the counters are asked for.

use k_rust::measure::{self, Snapshot};

/// The counter families the backend's execution counts: rule attempts and steps (`rewrite`,
/// `execution`), matching and unification, the simplifier's equations and builtins
/// (`simplify`), the solver (`smt`), search, term construction, and coverage probes.
///
/// The compiler's and the parser's families are left out: a run does that work only when the
/// compiled stage is not restored. `allocation` needs an allocator krs does not install, and
/// `output` counts k-rust's own writers, which krs does not use.
const FAMILIES: &[&str] = &[
    "rewrite",
    "execution",
    "matching",
    "unification",
    "simplify",
    "smt",
    "search",
    "term",
    "coverage",
];

/// Turn the backend's work counters on for the process, from now on.
pub fn count() {
    measure::count_at_run_time(true);
}

/// The current thread's counters at one moment.
pub struct Work(Snapshot);

impl Work {
    /// The counters of the current thread now.
    #[must_use]
    pub fn start() -> Self {
        Self(measure::snapshot())
    }

    /// What the current thread counted since [`Work::start`]: every counter of the execution
    /// families by its k-rust name (`rewrite.steps`, `simplify.equation_attempts`,
    /// `smt.queries`, ..), zeros included, in k-rust's order.
    #[must_use]
    pub fn taken(&self) -> Vec<(&'static str, u64)> {
        measure::snapshot()
            .delta(&self.0)
            .iter()
            .filter(|(name, _)| {
                name.split_once('.')
                    .is_some_and(|(family, _)| FAMILIES.contains(&family))
            })
            .collect()
    }
}

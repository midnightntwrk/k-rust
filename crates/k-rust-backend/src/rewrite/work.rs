//! The execution work budget (`ExecutionOptions::max_work`): the unit an execution counts and
//! the test that stops it.
//!
//! The unit is the state visited: each state `Execution::run` takes from its worklist, whatever
//! becomes of it (expanded into successors, ended as a leaf, or met again after another path
//! reached the same configuration), the count `Counter::RewriteSteps` measures. Exploration takes
//! states in a fixed order (depth first, successors pushed to the front), so the state at which
//! the count reaches a bound, and every leaf finished before it, are as deterministic as the
//! result: within the execution determinism contract and its exclusions (docs/compatibility.md,
//! "Determinism and concurrency", "Execute"), which leave out, among others, a run in which an
//! SMT query timed out.
//!
//! This module decides what is counted and when the budget is spent. A change of unit changes
//! [`Work`] and the sites that report a counted state to it: today the one call in
//! `Execution::run`; counting the states expanded instead, leaving out the arrivals a state-set
//! merge recognises, would also need a report at that merge point, after the arrival's
//! normalisation, while the budget test stays where states are taken.

/// The states an execution has visited, and its budget.
#[derive(Clone, Copy, Debug)]
pub(super) struct Work {
    visited: u64,
    bound: Option<u64>,
}

impl Work {
    pub(super) const fn new(bound: Option<u64>) -> Self {
        Self { visited: 0, bound }
    }

    /// Account for the state just taken from the worklist: `false` when the budget is spent, so
    /// the run ends at that state without visiting it; otherwise the state is counted.
    ///
    /// Asked only when a state remains, so a budget equal to an unbounded run's count never
    /// stops it.
    pub(super) fn visit(&mut self) -> bool {
        if self.bound.is_some_and(|bound| self.visited >= bound) {
            return false;
        }
        self.visited += 1;
        true
    }

    /// The states visited so far.
    pub(super) const fn visited(&self) -> u64 {
        self.visited
    }
}

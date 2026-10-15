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
//! It also counts the states expanded, those whose successors the run computed (its rewrite step
//! answered), which the result reports beside the states visited ([`Work`]); the budget bounds
//! the states visited, which bound the merge lookups as well as the expansions.
//!
//! This module decides what is counted and when the budget is spent. A change of unit changes
//! [`Work`] and the sites that report a counted state to it: today the one call in
//! `Execution::run`; counting the states expanded instead, leaving out the arrivals a state-set
//! merge recognises, would also need a report at that merge point, after the arrival's
//! normalisation, while the budget test stays where states are taken.

/// The states an execution has visited and those it expanded, and its budget.
///
/// A state is expanded when the run computed its successors: its rewrite step answered (with
/// successors, a branch or cut-point report, a stuck or undefined-step verdict, or a failure the
/// step reported), so the step's matching and condition work was done on it. Every expanded state
/// was visited first, and is expanded at most once: [`Work::expand`] is reported only while the
/// state that [`Work::visit`] counted is processed, after its step answered, and each visited
/// state takes at most one step. So `expanded <= visited`, with equality exactly when every
/// visited state was stepped.
///
/// A visited state that is not expanded is one the run ended before or instead of its step: a
/// state-set arrival equal at its depth to an expanded state (merged), a state at the depth bound,
/// one whose constraints or term simplified to a vacuous or undefined state, a remainder (its
/// parent's step decided it), a surviving macro or alias, and a state a stop interrupted before
/// its step answered. The state at which the work budget ends the run is neither visited nor
/// expanded.
#[derive(Clone, Copy, Debug)]
pub(super) struct Work {
    visited: u64,
    expanded: u64,
    bound: Option<u64>,
}

impl Work {
    pub(super) const fn new(bound: Option<u64>) -> Self {
        Self {
            visited: 0,
            expanded: 0,
            bound,
        }
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

    /// Account for the visited state being processed: its rewrite step answered, so the run
    /// computed its successors. Called at most once per visited state.
    pub(super) fn expand(&mut self) {
        debug_assert!(
            self.expanded < self.visited,
            "a state is expanded once, after its visit"
        );
        self.expanded += 1;
    }

    /// The states expanded so far: at most [`Work::visited`].
    pub(super) const fn expanded(&self) -> u64 {
        self.expanded
    }
}

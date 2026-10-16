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
//! It also counts the states expanded, the visited states whose rewrite step ran and answered
//! ([`Work`]), which the result reports beside the states visited.
//!
//! This module decides what is counted and when the budget is spent. It has two report sites:
//! [`Work::visit`], called in `Execution::run` when a state is taken from the worklist, which
//! counts the state and holds the budget test; and [`Work::expand`], called in
//! `Execution::expand` once the state's step answered. A change of unit changes [`Work`] and
//! these sites; a budget on expanded states would move the budget test to the second.
//!
//! The budget bounds the states visited, not the states expanded. One step may yield any number
//! of successors, and each successor that ends without a step of its own (a merged arrival, a
//! remainder, a state at the depth bound, a vacuous or undefined successor) is pending until it
//! is taken, and then costs a visit, its own simplification or a merge lookup, and becomes a leaf
//! unless it is merged. A budget on expansions would bound neither the visits, nor the leaves,
//! nor the pending states; and it could stop the run at a state only once that state's
//! simplification showed it would be stepped, so its `WorkBound` leaf would no longer be the
//! state as taken from the worklist, unexpanded and unnormalised.

/// The states an execution has visited and those it expanded, and its budget.
///
/// A state is expanded exactly when its rewrite step ran on it and answered, whatever the
/// answer: successors, a branch or cut-point report, or a verdict that ends the state (stuck,
/// trivial, vacuous, indeterminate, or a simplification failure). The step begins with two guards
/// that answer without matching any rule (`Vacuous` for constraints that are `\bottom`,
/// `Indeterminate` for a surviving macro or alias); a state that reaches one is expanded although
/// no rule was matched against it. A depth-0 state whose contradiction only the input
/// substitution exposes is stepped from its unsimplified pattern, so it is expanded, and reported
/// vacuous when no rule applies.
///
/// A visited state is not expanded when its step does not run or does not answer: the run ended
/// it before the step (merged, at the depth bound, ended by its own simplification, vanished in
/// normalisation, or a successor carrying a surviving macro or alias), it is a remainder (its
/// parent's step decided it, and it takes no step of its own), or a stop interrupted the step. A
/// state a stop cut short after its step answered is expanded. The state at which the work budget
/// ends the run is neither visited nor expanded.
///
/// Every expanded state was visited first, and is expanded at most once: [`Work::expand`] is
/// reported only while the state that [`Work::visit`] counted is processed, after its one step
/// answered. So `expanded <= visited`, with equality exactly when every visited state was
/// stepped; `stepped` checks the "at most once" per visit in debug builds.
#[derive(Clone, Copy, Debug)]
pub(super) struct Work {
    visited: u64,
    expanded: u64,
    /// Whether the state the last [`Work::visit`] counted has been expanded.
    stepped: bool,
    bound: Option<u64>,
}

impl Work {
    pub(super) const fn new(bound: Option<u64>) -> Self {
        Self {
            visited: 0,
            expanded: 0,
            stepped: false,
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
        self.stepped = false;
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
            self.visited > 0 && !self.stepped,
            "a state is expanded once, after its visit"
        );
        self.stepped = true;
        self.expanded += 1;
    }

    /// The states expanded so far: at most [`Work::visited`].
    pub(super) const fn expanded(&self) -> u64 {
        self.expanded
    }
}

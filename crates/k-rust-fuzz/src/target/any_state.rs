//! Pattern targets `at: any-state` (ARCHITECTURE 4.1): the target is reached when a
//! configuration the run reaches matches the pattern. Owners: FZ-ANYSTATE, FZ-STATESET-MATCH.
//!
//! A case runs once, through `Backend::execute` with `matchStates` set to the target's pattern
//! ([`Executor::run_any_state`]), under the same cancellation scope, per-case safety limit and
//! work budget as every case; under all paths as a state set. k-rust matches every state the
//! run reaches in normal form and does not merge into an equal state of its depth, as it reaches
//! it, and reports a summary (`ExecutionResult::state_matches`, docs/compatibility.md "State
//! matches"):
//! - a state *reaches* when it is decided (no constraint, no variable), ceil-free and matched
//!   with empty constraints, in execution mode and, unless the pattern evaluates nothing, in
//!   proof mode too (D16, review B1), exactly as an end leaf's state is judged (ARCHITECTURE
//!   5.2);
//! - a reach is *clean* when the diagnostics of the path that reached it, up to it, carry none of
//!   the leaf facts of ARCHITECTURE 5.2 (an implementation-chosen value, a contradicted claim,
//!   iteration exhaustion, a failed condition simplification, undecided initial definedness);
//! - a state merged into an equal recorded state has that state's verdict (a pattern reads only
//!   the configuration and its constraints), and an arrival on a clean path merged into a
//!   reaching state with a dirty one is reported as the clean reach, with its own prefix.
//!
//! The case is a hit when the summary has a first clean reach and the run has no run-level
//! reason (an unsupported hook observed in the run, D21; the clock, stack and solver reasons put
//! the case outside the determinism contract, below). What follows the reaching state on its
//! path cannot unmake the reach, so a reaching path a bound later cuts is still a hit
//! (CUT-PATH-HIT); only its prefix's facts bear on it. Under `run-to-completion` the hit also
//! needs the reaching path to end cleanly and naturally (and in data with `data-end`), and a
//! reached state names no leaf: it is a hit only when every leaf of the run is such an end and no
//! run fact lies off the leaves, and `reached-unfinished` when no path ends naturally at all
//! (`no_path_ends_naturally`); otherwise `unsupported` with `any-state-unattributed` (S4).
//!
//! Without a clean reach, a dirty reach or an undecided state may hide a hit: the case is then
//! `unsupported`, with the first reason in [`UnjudgedReason`]'s order among theirs and the
//! leaves'. Otherwise every matched state was refuted, and the case is classed by its leaves as
//! a case whose leaves reach nothing ([`crate::exec::classify_ends_explained`]): a state the
//! matcher did not see is the stopped state of a `work-bound`, `timeout` or `cancelled` leaf, or
//! lies on a vanished path whose facts are off the leaves, and either keeps the case from `miss`.
//!
//! The witness records the reaching configuration and its depth ([`HitSite::StateMatch`]); the
//! depth is the first clean reach's in the run's depth-first order, not the least depth at which
//! some path reaches the pattern (kink's query may find a shallower one). Below a merged state a
//! reach keeps the prefix of the arrival the run expanded, so such a reach can be a hit or
//! `unsupported` by the depth-first order, never `miss` (V8). The order is a function of the
//! definition and the request, so the verdict is deterministic.
//!
//! Cost: one match per distinct reached state (two when the pattern evaluates something), inside
//! the run, and nothing held beyond a few matched states (ANY-STATE-MEM: the observed path set
//! held every configuration of every path at once).

use k_rust::backend::{
    BackendDiagnosticOutput, CancellationToken, StateMatchOutput, UndecidedMatchReasonOutput,
};

use super::{
    HitSite, Judgement, ResolvedTarget, every_leaf_qualifies, no_path_ends_naturally,
    observer::{defect, explained, unobserved},
};
use crate::{
    exec::{self, AnyStateRun, CaseResult, DeterminismBreak, OutcomeClass, UnjudgedReason},
    report::EngineDefect,
};

#[cfg(test)]
#[path = "any_state_tests.rs"]
mod tests;

/// An any-state hit's reaching configuration (the first clean reach of the run's state
/// matches): its depth and its state, as KORE.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StateMatchHit {
    /// Committed steps from the initial configuration to it.
    pub(crate) depth: u64,
    /// The configuration, as k-rust reported it.
    pub(crate) configuration: k_rust::kore::ast::Pattern,
}

/// The reasons of a reach whose prefix is not clean: the leaf facts its path's diagnostics
/// carry, as a leaf's would give them (ARCHITECTURE 5.2, `Judge::leaf_reasons`).
fn prefix_reasons(reach: &StateMatchOutput) -> Vec<UnjudgedReason> {
    reach
        .diagnostics
        .iter()
        .filter_map(|diagnostic| match diagnostic {
            BackendDiagnosticOutput::ImplementationChosenValue { .. } => {
                Some(UnjudgedReason::ImplementationChosenValue)
            }
            BackendDiagnosticOutput::ContradictedClaim(_) => {
                Some(UnjudgedReason::ContradictedClaim)
            }
            BackendDiagnosticOutput::SimplificationBudgetExhausted { .. }
            | BackendDiagnosticOutput::RuleConditionUnsimplified { .. } => {
                Some(UnjudgedReason::IterationExhaustion)
            }
            BackendDiagnosticOutput::RuleConditionFailed { .. } => {
                Some(UnjudgedReason::SimplificationFailure)
            }
            BackendDiagnosticOutput::UndefinedInitialInstances { .. } => {
                Some(UnjudgedReason::UndecidedState)
            }
            BackendDiagnosticOutput::UndecidedCondition { .. }
            | BackendDiagnosticOutput::UndecidedPredicate { .. }
            | BackendDiagnosticOutput::UnsupportedHookUnevaluated { .. } => None,
        })
        .collect()
}

/// The reason of an undecided state.
fn undecided_reason(reason: UndecidedMatchReasonOutput) -> UnjudgedReason {
    match reason {
        UndecidedMatchReasonOutput::UndecidedState => UnjudgedReason::UndecidedState,
        UndecidedMatchReasonOutput::NotCeilFree => UnjudgedReason::NotCeilFree,
        UndecidedMatchReasonOutput::UndecidedMatch => UnjudgedReason::UndecidedMatch,
    }
}

impl ResolvedTarget {
    /// Judge an any-state case from its judged `result` and the run's state matches `run`
    /// ([`Executor::run_any_state`]), with the reaching configuration for a hit (module
    /// documentation).
    ///
    /// A failed run is classed by its failure alone. A case outside the determinism contract,
    /// or whose `cancel` is cancelled by the time it is judged, is classed with no leaf reaching
    /// the target and lifted to `timeout` or `unsupported`, as an observer case is: such a stop
    /// may have hidden a reaching configuration, or decided one by the clock.
    ///
    /// # Errors
    ///
    /// [`EngineDefect`] from classification, when a successful run reports no state matches,
    /// and when a dirty reach carries none of the facts that make a prefix unclean.
    ///
    /// [`Executor::run_any_state`]: crate::exec::Executor::run_any_state
    pub(super) fn judge_any_state(
        &self,
        result: &CaseResult,
        run: Option<&AnyStateRun>,
        cancel: Option<&CancellationToken>,
    ) -> Result<(Judgement, Option<StateMatchHit>), EngineDefect> {
        let run_to_completion = self.target.run_to_completion;
        let data_end = self.target.requires_data_end();
        if result.failure.is_some() {
            return exec::classify_explained(result, &[], run_to_completion)
                .map(|(class, reason)| (explained(class, reason), None));
        }
        let cancelled = cancel.is_some_and(CancellationToken::is_cancelled);
        let breaks = result.determinism_breaks();
        if result.safety_limit_hit || !breaks.is_empty() || cancelled {
            let clock =
                result.safety_limit_hit || breaks.contains(&DeterminismBreak::Clock) || cancelled;
            return unobserved(result, run_to_completion, clock).map(|judgement| (judgement, None));
        }
        let Some(run) = run else {
            return Err(defect("an any-state run reported no state matches"));
        };
        let matches = &run.matches;
        if let Some(reach) = &matches.first_clean_reach {
            // A run-level reason taints every path (ARCHITECTURE 5.2), the reaching one too.
            if let Some(reason) = run
                .run_reasons
                .iter()
                .filter_map(UnjudgedReason::of_unclean)
                .min()
            {
                return Ok((explained(OutcomeClass::Unsupported, Some(reason)), None));
            }
            if run_to_completion && !every_leaf_qualifies(result, run_to_completion, data_end) {
                // The reached state names no leaf; whether the path through it ends cleanly and
                // naturally is shown only when every path does, or when none does.
                let judgement = if no_path_ends_naturally(result) {
                    explained(OutcomeClass::ReachedUnfinished, None)
                } else {
                    explained(
                        OutcomeClass::Unsupported,
                        Some(UnjudgedReason::AnyStateUnattributed),
                    )
                };
                return Ok((judgement, None));
            }
            let judgement = self.confirmable(
                Judgement {
                    class: OutcomeClass::Hit,
                    hit_site: Some(HitSite::StateMatch { depth: reach.depth }),
                    blocked: false,
                    reason: None,
                    demoted_from: None,
                },
                result,
                reach.term_conjunction,
            );
            if judgement.class != OutcomeClass::Hit {
                return Ok((judgement, None));
            }
            let configuration = k_rust::kore::codec::from_value(&reach.state).map_err(|error| {
                defect(&format!(
                    "the reaching state does not decode as KORE: {error}"
                ))
            })?;
            return Ok((
                judgement,
                Some(StateMatchHit {
                    depth: reach.depth,
                    configuration,
                }),
            ));
        }
        let unreached = vec![false; result.leaves.len()];
        let (class, reason) =
            exec::classify_ends_explained(result, &unreached, run_to_completion, data_end)?;
        // No clean reach: a dirty reach or an undecided state may hide one.
        let mut unresolved: Vec<UnjudgedReason> = Vec::new();
        if let Some(reach) = &matches.first_dirty_reach {
            let reasons = prefix_reasons(reach);
            if reasons.is_empty() {
                return Err(defect(
                    "a reach k-rust reports on a dirty prefix carries no fact that makes a prefix unclean",
                ));
            }
            unresolved.extend(reasons);
        }
        unresolved.extend(
            matches
                .undecided
                .iter()
                .map(|entry| undecided_reason(entry.reason)),
        );
        if let Some(unresolved) = unresolved.into_iter().min() {
            // A configuration that could not be decided may reach the target: never a `miss`.
            let reason = reason.map_or(unresolved, |reason| reason.min(unresolved));
            return Ok((explained(OutcomeClass::Unsupported, Some(reason)), None));
        }
        if class == OutcomeClass::Hit {
            return Err(defect("leaves that reach nothing were classed `hit`"));
        }
        Ok((explained(class, reason), None))
    }
}

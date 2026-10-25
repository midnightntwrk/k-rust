//! The `comparable-end` and `query-confirmable` options of rule and pattern targets
//! ([`super::Target::comparable`], [`super::Target::query_confirmable`]; P7-ADDENDUM section 4).
//! Owners: FZ-COMPARABLE-A and -Q.
//!
//! Both read k-rust's facts on a case result through [`crate::exec::comparable`]; neither runs
//! kink's own rules.
//!
//! - A rule or pattern hit is judged against the witness program's run of every path
//!   ([`end_conditions`], with k-rust's data judgement of every end and undefined step for P3).
//!   When the hit case ran every path with no terminal rule (a run that stops at the target's
//!   rule is not the program's run), that run is the case's own, and the judgement is made in
//!   the case ([`ResolvedTarget::judge_comparable`]): it adds no execution, and the case's run
//!   is a hit only inside the determinism contract, so the judgement repeats with the case.
//!   Otherwise it takes one more run of every path, a state set with the campaign's bounds (and
//!   [`crate::spec::DEFAULT_MAX_WORK`] when the campaign sets no work bound) and no matcher:
//!   - under `comparable-end` the judgement decides whether the case is a hit, so that run is
//!     part of the case ([`ResolvedTarget::judge_comparable`]), which counts its work, load
//!     records and determinism as the differential's re-run is counted; a hit that fails becomes
//!     `unsupported`, or `timeout` when a clock stopped that run, as every case a clock was
//!     involved in;
//!   - without the option the judgement decides nothing in the campaign, so that run stays out
//!     of every case: the loop makes it once per reported witness case, after shrinking
//!     ([`ResolvedTarget::comparability`]), and charges its work to the campaign's total alone.
//!     Its determinism breaks then reach neither the case's determinism nor its coverage; the
//!     judgement names them ([`crate::exec::ComparableCondition::breaks_determinism`]), so a
//!     reader (and `--replay`) can tell a judgement that repeats from one that may not.
//! - A pattern hit under `query-confirmable` is judged against the whole hit run
//!   ([`ResolvedTarget::confirmable`]), at `final` and at `any-state`.

use k_rust::{
    backend::{CancellationToken, HaltReasonOutput},
    kore::ast::Pattern as KorePattern,
};

use super::{Judgement, Resolved, ResolvedTarget};
use crate::{
    exec::{
        Abort, CaseRequestShape, CaseResult, ComparableCondition, Executor, OutcomeClass,
        UnjudgedReason,
        comparable::{end_conditions, query_conditions},
        hooks::condition_hooks,
        reasons::{EndNotComparable, QueryNotConfirmable},
    },
    report::{Comparability, EngineDefect, ReasonHooks},
};

/// What [`ResolvedTarget::judge_comparable`] gives: the judgement (demoted under
/// `comparable-end` when the run is not comparable), the comparable judgement a hit's witness
/// carries when the case made it, and the extra run of every path when the case made one.
pub(super) type Compared = (
    Result<Judgement, EngineDefect>,
    Option<Comparability>,
    Option<CaseResult>,
);

impl ResolvedTarget {
    /// Under `query-confirmable`, a pattern `judgement` of `result` that is a hit becomes
    /// `unsupported` when [`query_conditions`] names a condition, the first one being the
    /// reason; `term_conjunction` says whether the matched state (the hit leaf's at `final`, the
    /// first reaching configuration's at `any-state`) holds a term-level `\and`. Every other
    /// judgement is returned as it is.
    pub(super) fn confirmable(
        &self,
        judgement: Judgement,
        result: &CaseResult,
        term_conjunction: bool,
    ) -> Judgement {
        let pattern = matches!(
            self.resolved,
            Resolved::PatternFinal | Resolved::PatternAnyState
        );
        if judgement.class != OutcomeClass::Hit || !pattern || !self.target.query_confirmable {
            return judgement;
        }
        match query_conditions(result, term_conjunction).first() {
            None => judgement,
            Some(condition) => Judgement {
                class: OutcomeClass::Unsupported,
                hit_site: None,
                blocked: judgement.blocked,
                reason: Some(UnjudgedReason::QueryNotConfirmable(QueryNotConfirmable(
                    *condition,
                ))),
                demoted_from: None,
            },
        }
    }

    /// Whether this target's hits carry a comparable judgement: a rule or pattern target.
    fn judges_comparability(&self) -> bool {
        matches!(
            self.resolved,
            Resolved::Rule { .. } | Resolved::PatternFinal | Resolved::PatternAnyState
        )
    }

    /// For a rule or pattern case whose `judgement` of `result` (run from `initial` with
    /// `shape`) is a hit, the comparable judgement of the program's run of every path
    /// ([`end_conditions`]; module documentation), when the case makes it:
    /// - when `shape` runs every path with no terminal rule, of `result` itself;
    /// - otherwise, under `comparable-end`, of a run of every path made here on `executor`
    ///   within `cancel`'s scope, returned so that the case counts its work, load records and
    ///   determinism;
    /// - otherwise none: the loop judges the witness case outside the case
    ///   ([`Self::comparability`]).
    ///
    /// Under `comparable-end` a hit that is not comparable carries no judgement and becomes
    /// `timeout` when a clock stopped the run, as every case a clock was involved in, and
    /// otherwise `unsupported`, the first condition being the reason. Every other judgement and
    /// target is returned as it is, with neither.
    ///
    /// # Errors
    ///
    /// [`Abort`] for a failed solver prelude of the extra run.
    pub(super) fn judge_comparable(
        &self,
        executor: &mut Executor,
        initial: &KorePattern,
        shape: &CaseRequestShape,
        cancel: Option<&CancellationToken>,
        result: &CaseResult,
        judgement: Result<Judgement, EngineDefect>,
    ) -> Result<Compared, Abort> {
        let hit = match &judgement {
            Ok(judged) if self.judges_comparability() && judged.class == OutcomeClass::Hit => {
                judged
            }
            Ok(_) | Err(_) => return Ok((judgement, None, None)),
        };
        let (conditions, every_path) = if own_run_of_every_path(shape) {
            (conditions_here(executor, result), None)
        } else if self.target.comparable {
            let every_path = executor.run(initial, &shape.every_path(), &[], cancel)?;
            (conditions_here(executor, &every_path), Some(every_path))
        } else {
            return Ok((judgement, None, None));
        };
        // A crash of the run of every path is the case's crash: its reason is the crash's
        // (`panic`, `internal-error`, `internal-halt`), which precedes the condition it fails
        // (FZ-CRASH, FZ-CRASH-CAUSE).
        let crashed = every_path.as_ref().and_then(CaseResult::crash_reason);
        if self.target.comparable
            && let Some(condition) = conditions.first()
        {
            let refused = if conditions.contains(&ComparableCondition::Clock) {
                Judgement {
                    class: OutcomeClass::Timeout,
                    hit_site: None,
                    blocked: hit.blocked,
                    reason: None,
                    demoted_from: None,
                }
            } else {
                Judgement {
                    class: OutcomeClass::Unsupported,
                    hit_site: None,
                    blocked: hit.blocked,
                    reason: Some(crashed.unwrap_or(UnjudgedReason::EndNotComparable(
                        EndNotComparable(*condition),
                    ))),
                    demoted_from: None,
                }
            };
            return Ok((Ok(refused), None, every_path));
        }
        let judged = every_path.as_ref().unwrap_or(result);
        let comparable = comparability(conditions, Some(judged));
        Ok((judgement, Some(comparable), every_path))
    }

    /// Whether a witness case of a case run with `shape` takes its comparable judgement outside
    /// its case ([`Self::comparability`]).
    pub(crate) fn judges_outside_the_case(&self, shape: &CaseRequestShape) -> bool {
        self.judges_comparability() && !self.target.comparable && !own_run_of_every_path(shape)
    }

    /// The comparable judgement of a reported witness case that its case did not make
    /// ([`Self::judge_comparable`]): a rule or pattern target without `comparable-end` whose
    /// case `shape` runs one path, names a terminal rule or asks for a path set (an all-paths
    /// `at: any-state` case, FZ-STATESET N2). It runs the program from `initial`
    /// on every path on `executor` within `cancel`'s scope, outside every case, and gives the
    /// judgement with that run's work (at least 1) for the campaign's total. A failed solver
    /// prelude, which the witness's own run passed, reads as `run-failed`. `None` when the case
    /// made the judgement or the target carries none.
    ///
    /// The run of every path is returned beside the judgement, so that a crash of it is noted
    /// (FZ-CRASH); `None` for a run that aborted.
    pub(crate) fn comparability(
        &self,
        executor: &mut Executor,
        initial: &KorePattern,
        shape: &CaseRequestShape,
        cancel: Option<&CancellationToken>,
    ) -> Option<(Comparability, u64, Option<CaseResult>)> {
        if !self.judges_outside_the_case(shape) {
            return None;
        }
        Some(
            match executor.run(initial, &shape.every_path(), &[], cancel) {
                Ok(every_path) => (
                    comparability(conditions_here(executor, &every_path), Some(&every_path)),
                    every_path.work.max(1),
                    Some(every_path),
                ),
                Err(_) => (
                    comparability(vec![ComparableCondition::RunFailed], None),
                    0,
                    None,
                ),
            },
        )
    }
}

/// Whether a case run with `shape` is the program's own run of every path: strategy `all`, no
/// terminal rule, and a state set, as [`CaseRequestShape::every_path`] runs it (FZ-STATESET N2:
/// an `at: any-state` case runs a path set, which is not that run).
fn own_run_of_every_path(shape: &CaseRequestShape) -> bool {
    shape.all_paths() && !shape.has_terminal_rules() && shape.state_set()
}

/// The judgement of `conditions`, failed by `judged` (the run of every path they were read
/// from, when there is one), with the hooks each condition's facts name there (UNNAMED-HOOK).
fn comparability(
    conditions: Vec<ComparableCondition>,
    judged: Option<&CaseResult>,
) -> Comparability {
    let hooks = judged
        .map(|judged| {
            conditions
                .iter()
                .filter_map(|condition| {
                    ReasonHooks::of(&condition_hooks(judged, *condition))
                        .map(|hooks| (*condition, hooks))
                })
                .collect()
        })
        .unwrap_or_default();
    Comparability {
        holds: conditions.is_empty(),
        reasons: conditions,
        hooks,
    }
}

/// [`end_conditions`] of `result`, with the data judgement made on `executor` for every end and
/// undefined step the run did not judge (a case whose target reads no data end), so that P3 is
/// read on every one.
fn conditions_here(executor: &mut Executor, result: &CaseResult) -> Vec<ComparableCondition> {
    let unjudged = |leaf: &crate::exec::LeafReport| {
        leaf.data_end.is_none()
            && matches!(
                leaf.halt,
                HaltReasonOutput::Stuck | HaltReasonOutput::Trivial
            )
    };
    if !result.leaves.iter().any(unjudged) {
        return end_conditions(result);
    }
    let mut judged = result.clone();
    for leaf in &mut judged.leaves {
        if unjudged(leaf) {
            leaf.data_end = Some(executor.is_data_here(&leaf.state));
        }
    }
    end_conditions(&judged)
}

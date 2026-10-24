//! The `comparable-end` and `query-confirmable` options of rule and pattern targets
//! ([`super::Target::comparable`], [`super::Target::query_confirmable`]; P7-ADDENDUM section 4).
//! Owners: FZ-COMPARABLE-A and -Q.
//!
//! Both read k-rust's facts on a case result through [`crate::exec::comparable`]; neither runs
//! kink's own rules.
//!
//! - A rule or pattern hit is judged against the witness program's run of every path
//!   ([`ResolvedTarget::judge_comparable`]): the hit case's own run when it ran every path with
//!   no terminal rule (a run that stops at the target's rule is not the program's run), otherwise
//!   one more run of every path, a path set with the campaign's bounds and no matcher, whose work
//!   the case counts as the differential's re-run is counted. The judgement goes into the
//!   witness; under `comparable-end` a hit that fails becomes `unsupported`.
//! - A pattern hit under `query-confirmable` is judged against the whole hit run
//!   ([`ResolvedTarget::confirmable`]), at `final` and at `any-state`.

use k_rust::{backend::CancellationToken, kore::ast::Pattern as KorePattern};

use super::{Judgement, Resolved, ResolvedTarget};
use crate::{
    exec::{
        Abort, CaseRequestShape, CaseResult, Executor, OutcomeClass, UnjudgedReason,
        comparable::{end_conditions, query_conditions},
        reasons::{EndNotComparable, QueryNotConfirmable},
    },
    report::{Comparability, EngineDefect},
};

/// What [`ResolvedTarget::judge_comparable`] gives: the judgement (demoted under
/// `comparable-end` when the run is not comparable), the comparable judgement a hit's witness
/// carries, and the extra run of every path when one was made.
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
            },
        }
    }

    /// For a rule or pattern case whose `judgement` of `result` (run from `initial` with
    /// `shape`) is a hit, the comparable judgement of the program's run of every path
    /// ([`end_conditions`]): `result` itself when `shape` runs every path with no terminal rule,
    /// otherwise a run of every path made here on `executor` within `cancel`'s scope, returned so
    /// that the case counts its work. Under `comparable-end` a hit that is not comparable
    /// becomes `unsupported`, the first condition being the reason, and carries no judgement.
    /// Every other judgement and target is returned as it is, with neither.
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
        let applies = matches!(
            self.resolved,
            Resolved::Rule { .. } | Resolved::PatternFinal | Resolved::PatternAnyState
        );
        let hit = match &judgement {
            Ok(judged) if applies && judged.class == OutcomeClass::Hit => judged,
            Ok(_) | Err(_) => return Ok((judgement, None, None)),
        };
        let (conditions, every_path) = if shape.all_paths() && !shape.has_terminal_rules() {
            (end_conditions(result), None)
        } else {
            let every_path = executor.run(initial, &shape.every_path(), &[], cancel)?;
            (end_conditions(&every_path), Some(every_path))
        };
        if self.target.comparable
            && let Some(condition) = conditions.first()
        {
            let refused = Judgement {
                class: OutcomeClass::Unsupported,
                hit_site: None,
                blocked: hit.blocked,
                reason: Some(UnjudgedReason::EndNotComparable(EndNotComparable(
                    *condition,
                ))),
            };
            return Ok((Ok(refused), None, every_path));
        }
        let comparability = Comparability {
            holds: conditions.is_empty(),
            reasons: conditions,
        };
        Ok((judgement, Some(comparability), every_path))
    }
}

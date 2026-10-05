//! Equation scans: the outcome of one equation attempt, the scan of one priority group, and the
//! priority loop over the groups a term theory offers a term.
//!
//! The loop is the only place that states "no equation offered this term matched it"
//! ([`NoOfferedEquationMatched`]), the premise of the simplifier's normal-form certificate
//! (`term::head::NormalFormCertificate`). It selects the groups itself, so the statement covers
//! every group equation selection offers the term, and it states it only when every attempt of
//! every group ended in a failed match of the equation's left-hand side
//! ([`EquationAttempt::NotApplicable`] carrying a [`MatchFailed`]).

use std::{marker::PhantomData, sync::Arc};

use crate::{
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic},
    matching::MatchFailed,
    rule::{RewriteRule, Theory, applicable_groups, term_index},
    term::Term,
};

use super::{ConditionIndeterminacy, Simplification, SimplifyResult};

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum IndeterminateEquation {
    Block,
    Continue,
}

/// One of the two term theories whose scans the evaluated mark rests on, as a type, so that a
/// statement about one theory's scan cannot stand in for the other's.
pub(super) trait TermTheory {
    /// What an undecided equation does to the rest of the scan.
    const INDETERMINATE_EQUATION: IndeterminateEquation;

    /// The equations of the theory.
    fn theory(definition: &BackendDefinition) -> &Theory;
}

/// The function equations: an undecided equation blocks the lower-priority groups, because
/// function evaluation must keep the application rather than fall through to an `owise` or
/// otherwise lower-priority equation.
pub(crate) struct FunctionTheory;

impl TermTheory for FunctionTheory {
    const INDETERMINATE_EQUATION: IndeterminateEquation = IndeterminateEquation::Block;

    fn theory(definition: &BackendDefinition) -> &Theory {
        definition.function_theory()
    }
}

/// The simplification equations: an undecided equation does not keep the lower-priority groups
/// from applying.
pub(crate) struct SimplificationTheory;

impl TermTheory for SimplificationTheory {
    const INDETERMINATE_EQUATION: IndeterminateEquation = IndeterminateEquation::Continue;

    fn theory(definition: &BackendDefinition) -> &Theory {
        definition.simplification_theory()
    }
}

/// Every equation that selection offers a term in theory `K`, under the term's index and under
/// a bare variable, failed to match it: its left-hand side has no instance in common with the
/// term. Minted only by [`scan_term_theory`]; neither `Clone` nor `Copy`, so one scan yields
/// one statement.
pub(crate) struct NoOfferedEquationMatched<K>(PhantomData<K>);

pub(super) enum TheoryScan<K> {
    /// The result of the equation that applied, and that equation.
    Applied(Simplification, Arc<RewriteRule>),
    Blocked,
    /// No equation applied, but some equation was set aside for a reason other than a failed
    /// match (see [`GroupScan::NotCacheable`]); the term is not a fixed point to record.
    NotCacheable,
    /// Every equation offered the term failed to match it.
    NotApplicable(NoOfferedEquationMatched<K>),
}

/// The priority loop of term theory `K`: scan the groups equation selection offers `term` in
/// priority order, trying each equation with `attempt`, until one applies or a group blocks the
/// scan. Every equation passed over for its unbound result variables is recorded in
/// `passed_over` (see [`scan_group`]). The only mint of [`NoOfferedEquationMatched`]: it is
/// returned when every attempt of every offered group ended `NotApplicable`, which for a term
/// theory carries a [`MatchFailed`].
///
/// ```toml algorithm-site
/// id = "backend.simplify.term"
/// role = "part"
/// sites = ["scan_term_theory", "scan_group"]
/// ```
#[deny(clippy::wildcard_enum_match_arm)]
pub(super) fn scan_term_theory<K: TermTheory>(
    definition: &BackendDefinition,
    term: &Term,
    passed_over: &mut PassedOver,
    mut attempt: impl FnMut(
        &Arc<RewriteRule>,
    ) -> SimplifyResult<EquationAttempt<Simplification, MatchFailed>>,
) -> SimplifyResult<TheoryScan<K>> {
    let groups = applicable_groups(K::theory(definition), &term_index(term));
    let mut blocked = false;
    let mut not_cacheable = false;
    for rules in groups.values() {
        match scan_group(rules, passed_over, |rule| {
            Ok(match attempt(rule)? {
                EquationAttempt::Applied(result) => {
                    EquationAttempt::Applied((result, Arc::clone(rule)))
                }
                EquationAttempt::NotApplicable(failed) => EquationAttempt::NotApplicable(failed),
                EquationAttempt::ContextDependent => EquationAttempt::ContextDependent,
                EquationAttempt::Unused => EquationAttempt::Unused,
                EquationAttempt::Indeterminate(reason) => EquationAttempt::Indeterminate(reason),
                EquationAttempt::PassedOver(report) => EquationAttempt::PassedOver(report),
            })
        })? {
            GroupScan::Applied((result, rule)) => return Ok(TheoryScan::Applied(result, rule)),
            GroupScan::Blocked if K::INDETERMINATE_EQUATION == IndeterminateEquation::Block => {
                // A rule at this priority may apply after the symbolic subject becomes more
                // concrete. Function evaluation must preserve the application and must not fall
                // through to an owise or otherwise lower-priority equation.
                return Ok(TheoryScan::Blocked);
            }
            GroupScan::Blocked => blocked = true,
            GroupScan::NotCacheable => not_cacheable = true,
            GroupScan::NotApplicable => {}
        }
    }
    Ok(if blocked {
        TheoryScan::Blocked
    } else if not_cacheable {
        TheoryScan::NotCacheable
    } else {
        // Every group of `groups`, the whole of what selection offers `term` in `K`, ended
        // `GroupScan::NotApplicable`: each of its attempts was `NotApplicable(MatchFailed)`.
        TheoryScan::NotApplicable(NoOfferedEquationMatched(PhantomData))
    })
}

/// The outcome of one equation attempt. `N` is the evidence a `NotApplicable` attempt carries:
/// [`MatchFailed`] for the term theories, whose scans the evaluated mark rests on, so that only
/// a failed match of the left-hand side can be `NotApplicable` there; `()` for the ceil and
/// predicate scans, which never feed the mark.
pub(super) enum EquationAttempt<T, N> {
    NotApplicable(N),
    /// The equation is inapplicable under the current path condition, but may apply if the same
    /// term is simplified under different assumptions. Unlike `Indeterminate`, this does not
    /// block lower-priority equations in the current scan.
    ContextDependent,
    /// The equation's left-hand side matched, or its shape keeps the evaluator from using it as
    /// a term rewrite, and the evaluator does not use it on this term: a `concrete` or
    /// `symbolic` attribute rejected the binding, the match bound a variable outside the
    /// left-hand side, or the right-hand side is a predicate. These are choices of when the
    /// evaluator uses an equation, not of what the definition means: the equation still holds,
    /// so the term may equal its right-hand side. Like `ContextDependent`, this lets
    /// lower-priority equations of the scan fire and keeps the term out of the evaluated cache.
    Unused,
    Indeterminate(ConditionIndeterminacy),
    /// `Indeterminate(UnboundResultVariables)`: the equation's result has variables its
    /// left-hand side does not bind and its `requires` is not refuted, so the instance is not
    /// used. The diagnostic explains a subject that no other equation rewrites; see
    /// [`PassedOver`].
    PassedOver(BackendDiagnostic),
    Applied(T),
}

/// The diagnostics of the equation instances a scan passed over because their results have
/// variables their left-hand sides do not bind ([`EquationAttempt::PassedOver`]).
///
/// Such an instance is not used whatever the other equations do, but it explains the subject
/// only if the subject is kept: when another equation of the scan, or of a scan of another
/// theory on the same subject, rewrites it, the subject is evaluated and there is nothing to
/// explain. So the scans record the diagnostics here, and the caller that sees the subject kept
/// emits them ([`PassedOver::emit`]); a caller whose subject was rewritten drops them.
#[derive(Default)]
pub(super) struct PassedOver(Vec<BackendDiagnostic>);

impl PassedOver {
    /// Report the subject as kept: emit every recorded diagnostic, in the order recorded.
    pub(super) fn emit(self) {
        for report in self.0 {
            diagnostic::emit(report);
        }
    }
}

pub(super) enum GroupScan<T> {
    Applied(T),
    Blocked,
    /// No equation applied, and some equation was `ContextDependent` or `Unused`: the scan's
    /// answer may differ under another path condition, or an equation that matched was set aside,
    /// so the term must not be recorded as a fixed point.
    NotCacheable,
    /// Every attempt of the group was `NotApplicable`.
    NotApplicable,
}

/// Try the equations of one priority group in order until one applies. An attempt that is
/// [`EquationAttempt::PassedOver`] counts as indeterminate, and its diagnostic is recorded in
/// `passed_over` for the caller to emit if the subject is kept.
#[deny(clippy::wildcard_enum_match_arm)]
pub(super) fn scan_group<R, T, N>(
    rules: &[Arc<R>],
    passed_over: &mut PassedOver,
    mut attempt: impl FnMut(&Arc<R>) -> SimplifyResult<EquationAttempt<T, N>>,
) -> SimplifyResult<GroupScan<T>> {
    let mut indeterminate = false;
    let mut not_cacheable = false;
    for rule in rules {
        match attempt(rule)? {
            EquationAttempt::Applied(result) => return Ok(GroupScan::Applied(result)),
            EquationAttempt::Indeterminate(_reason) => indeterminate = true,
            EquationAttempt::PassedOver(report) => {
                passed_over.0.push(report);
                indeterminate = true;
            }
            EquationAttempt::ContextDependent | EquationAttempt::Unused => not_cacheable = true,
            EquationAttempt::NotApplicable(_evidence) => {}
        }
    }
    Ok(if indeterminate {
        GroupScan::Blocked
    } else if not_cacheable {
        GroupScan::NotCacheable
    } else {
        GroupScan::NotApplicable
    })
}

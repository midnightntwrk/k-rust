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
    diagnostic::{self, Buffered, Subject},
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
pub(crate) struct NoOfferedEquationMatched<K> {
    /// Whether every one of those failures is a [`FailedMatch`] that certifies values: then no
    /// valuation of any offered left-hand side denotes the term's value either.
    values: bool,
    theory: PhantomData<K>,
}

impl<K> NoOfferedEquationMatched<K> {
    /// Whether the statement is about the term's value as well as about the term.
    pub(crate) fn certifies_values(&self) -> bool {
        self.values
    }
}

/// The evidence a failed attempt of a term-theory equation carries: the matcher's refutation of
/// the left-hand side on the term, and whether that refutation is about values.
///
/// A failed match shows that no instance of the left-hand side is the term. An equation
/// constrains the value its left-hand side denotes, so the failure shows that the equation does
/// not hold of the term's value only when no instance of the left-hand side has the term as a
/// reduct below its root (`BackendDefinition::failed_match_is_about_values`). Otherwise
/// (`w(h(3))` under `h(3) = h(1)`, tried on `w(h(1))`) the equation does not apply, so the term
/// stays a fixed point of the simplifier, but its value is not certified.
pub(crate) struct FailedMatch {
    _refutation: MatchFailed,
    values: bool,
}

impl FailedMatch {
    pub(super) fn new(refutation: MatchFailed, values: bool) -> Self {
        Self {
            _refutation: refutation,
            values,
        }
    }
}

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
/// scan. The diagnostics of each indeterminate attempt are held in `indeterminate` (see
/// [`scan_group`]). The only mint of [`NoOfferedEquationMatched`]: it is
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
    indeterminate: &mut IndeterminateAttempts,
    mut attempt: impl FnMut(
        &Arc<RewriteRule>,
    ) -> SimplifyResult<EquationAttempt<Simplification, FailedMatch>>,
) -> SimplifyResult<TheoryScan<K>> {
    let groups = applicable_groups(K::theory(definition), &term_index(term));
    let mut blocked = false;
    let mut not_cacheable = false;
    let mut values = true;
    for rules in groups.values() {
        match scan_group(rules, indeterminate, |rule| {
            Ok(match attempt(rule)? {
                EquationAttempt::Applied(result) => {
                    EquationAttempt::Applied((result, Arc::clone(rule)))
                }
                EquationAttempt::NotApplicable(failed) => {
                    values &= failed.values;
                    EquationAttempt::NotApplicable(failed)
                }
                EquationAttempt::ContextDependent => EquationAttempt::ContextDependent,
                EquationAttempt::Unused => EquationAttempt::Unused,
                EquationAttempt::Indeterminate(reason) => EquationAttempt::Indeterminate(reason),
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
        // `GroupScan::NotApplicable`: each of its attempts was `NotApplicable(FailedMatch)`, and
        // `values` records whether each of those failures certifies values.
        TheoryScan::NotApplicable(NoOfferedEquationMatched {
            values,
            theory: PhantomData,
        })
    })
}

/// The outcome of one equation attempt. `N` is the evidence a `NotApplicable` attempt carries:
/// [`FailedMatch`] (a [`MatchFailed`] and whether it is about values) for the term theories,
/// whose scans the evaluated mark rests on, so that only a failed match of the left-hand side
/// can be `NotApplicable` there; `()` for the ceil and predicate scans, which never feed the
/// mark.
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
    Applied(T),
}

/// The diagnostics of the indeterminate equation attempts of the scans on one subject, held
/// until the caller knows whether the subject is kept.
///
/// A diagnostic emitted during an attempt (an undecided `requires` or obligation, an equation
/// passed over for its unbound result variables, or whatever simplifying its conditions
/// reported) is a claim about the subject's result. An indeterminate attempt does not use the
/// equation, so the subject is kept only if no other equation of the scan, or of a scan of
/// another theory on the same subject, rewrites it. The caller that sees the subject kept
/// commits the held diagnostics ([`IndeterminateAttempts::commit`]); a caller whose subject was
/// rewritten drops them, since the result they describe is not the one returned. Once committed,
/// they explain that subject, and the simplifier entry that returns the result keeps them only if
/// the result still holds it ([`diagnostic::retract_dropped`]).
#[derive(Default)]
pub(super) struct IndeterminateAttempts(Vec<Buffered>);

impl IndeterminateAttempts {
    /// The subject is kept at its node: record the held diagnostics, attempt by attempt in scan
    /// order, each explaining the subject, which is built only when there is one to record.
    pub(super) fn commit(self, subject: impl FnOnce() -> Subject) {
        if self.0.iter().all(Buffered::is_empty) {
            return;
        }
        let subject = subject();
        for attempt in self.0 {
            attempt.commit_kept(&subject);
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

/// Try the equations of one priority group in order until one applies.
///
/// Each attempt is speculative, so its diagnostics are buffered ([`diagnostic::buffer`]) and
/// follow its outcome. An applied attempt's are committed: its result is the subject's. An
/// indeterminate attempt's are held in `indeterminate`, for the caller to commit if the subject
/// is kept. An attempt that does not apply, its `requires` refuted or the equation not used,
/// says nothing about the subject, and its diagnostics are dropped. A failed attempt's are
/// committed, as the failure is what the scan returns.
#[deny(clippy::wildcard_enum_match_arm)]
pub(super) fn scan_group<R, T, N>(
    rules: &[Arc<R>],
    indeterminate_attempts: &mut IndeterminateAttempts,
    mut attempt: impl FnMut(&Arc<R>) -> SimplifyResult<EquationAttempt<T, N>>,
) -> SimplifyResult<GroupScan<T>> {
    let mut indeterminate = false;
    let mut not_cacheable = false;
    for rule in rules {
        let (outcome, diagnostics) = diagnostic::buffer(|| attempt(rule));
        let outcome = match outcome {
            Ok(outcome) => outcome,
            Err(unwind) => {
                diagnostics.commit();
                return Err(unwind);
            }
        };
        match outcome {
            EquationAttempt::Applied(result) => {
                diagnostics.commit();
                return Ok(GroupScan::Applied(result));
            }
            EquationAttempt::Indeterminate(_reason) => {
                indeterminate_attempts.0.push(diagnostics);
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

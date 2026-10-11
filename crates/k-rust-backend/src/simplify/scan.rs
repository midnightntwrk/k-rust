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
/// scan. The diagnostics of each indeterminate attempt are held in `indeterminate` (see
/// [`scan_group`]). The only mint of [`NoOfferedEquationMatched`]: it is
/// returned when every attempt of every offered group ended `NotApplicable`, which for a term
/// theory carries a [`MatchFailed`].
///
/// ```toml algorithm-site
/// id = "backend.simplify.term"
/// role = "part"
/// sites = ["scan_term_theory", "scan_alternatives", "scan_group", "scan_instances"]
/// ```
#[deny(clippy::wildcard_enum_match_arm)]
pub(super) fn scan_term_theory<K: TermTheory>(
    definition: &BackendDefinition,
    term: &Term,
    indeterminate: &mut IndeterminateAttempts,
    mut attempt: impl FnMut(
        &Arc<RewriteRule>,
    ) -> SimplifyResult<EquationAttempt<Simplification, MatchFailed>>,
) -> SimplifyResult<TheoryScan<K>> {
    let groups = applicable_groups(K::theory(definition), &term_index(term));
    let mut blocked = false;
    let mut not_cacheable = false;
    for rules in groups.values() {
        match scan_group(rules, indeterminate, |rule| {
            Ok(match attempt(rule)? {
                EquationAttempt::Applied(result) => {
                    EquationAttempt::Applied((result, Arc::clone(rule)))
                }
                EquationAttempt::NotApplicable(failed) => EquationAttempt::NotApplicable(failed),
                EquationAttempt::ContextDependent => EquationAttempt::ContextDependent,
                EquationAttempt::Unused => EquationAttempt::Unused,
                EquationAttempt::Indeterminate(reason) => EquationAttempt::Indeterminate(reason),
                EquationAttempt::Recurred => EquationAttempt::Recurred,
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
    /// left-hand side, or the right-hand side is a predicate or `\top` (a `\top` lemma is used
    /// only on an operand of a term-level conjunction). These are choices of when the
    /// evaluator uses an equation, not of what the definition means: the equation still holds,
    /// so the term may equal its right-hand side. Like `ContextDependent`, this lets
    /// lower-priority equations of the scan fire and keeps the term out of the evaluated cache.
    Unused,
    Indeterminate(ConditionIndeterminacy),
    /// The equation applied to the subject, an `Unspecified` application, in an attempt that
    /// failed: its outcome still needed a value being computed, so the attempt was undone and
    /// the subject is tried again without it (`simplify::UnspecifiedFrame`). The equation is not
    /// refuted: like `Indeterminate`, this keeps lower-priority groups from firing, while the
    /// other equations of its group are still tried.
    Recurred,
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

/// How alternatives tried in order combine when each is by itself enough to rewrite the subject:
/// the equations of one priority group ([`scan_group`]) and the instances of one equation
/// ([`scan_instances`]). The first alternative that applies gives the result. Otherwise an
/// undecided alternative (indeterminate or recurred) leaves the whole undecided, since it may
/// still apply, and the first such outcome is the whole's. Otherwise the whole is context
/// dependent if one alternative is, else unused if one is, and not applicable only when every
/// alternative is.
pub(super) enum Combined<T, N> {
    Applied(T),
    Indeterminate(ConditionIndeterminacy),
    Recurred,
    ContextDependent,
    Unused,
    /// Every alternative was `NotApplicable`: the evidence of the last one, none when there was
    /// no alternative.
    NotApplicable(Option<N>),
}

/// Try `alternatives` in order with `attempt` until one applies, and combine their outcomes
/// ([`Combined`]); also returns the diagnostics of the undecided attempts, in order.
///
/// Each attempt is speculative, so its diagnostics are buffered ([`diagnostic::buffer`]) and
/// follow its outcome. An applied attempt's are committed: its result is the subject's. An
/// undecided attempt's are returned, for the caller to commit where an undecided outcome is what
/// explains the subject. An attempt that does not apply, its `requires` refuted or the equation
/// not used, says nothing about the subject, and its diagnostics are dropped. A failed attempt's
/// are committed, as the failure is what the scan returns.
#[deny(clippy::wildcard_enum_match_arm)]
fn scan_alternatives<A, T, N>(
    alternatives: impl IntoIterator<Item = A>,
    mut attempt: impl FnMut(A) -> SimplifyResult<EquationAttempt<T, N>>,
) -> SimplifyResult<(Combined<T, N>, Vec<Buffered>)> {
    let mut undecided: Option<Combined<T, N>> = None;
    let mut held = Vec::new();
    let mut context_dependent = false;
    let mut unused = false;
    let mut not_applicable = None;
    for alternative in alternatives {
        let (outcome, diagnostics) = diagnostic::buffer(|| attempt(alternative));
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
                return Ok((Combined::Applied(result), held));
            }
            EquationAttempt::Indeterminate(reason) => {
                held.push(diagnostics);
                undecided.get_or_insert(Combined::Indeterminate(reason));
            }
            EquationAttempt::Recurred => {
                held.push(diagnostics);
                undecided.get_or_insert(Combined::Recurred);
            }
            EquationAttempt::ContextDependent => context_dependent = true,
            EquationAttempt::Unused => unused = true,
            EquationAttempt::NotApplicable(evidence) => not_applicable = Some(evidence),
        }
    }
    let combined = if let Some(undecided) = undecided {
        undecided
    } else if context_dependent {
        Combined::ContextDependent
    } else if unused {
        Combined::Unused
    } else {
        Combined::NotApplicable(not_applicable)
    };
    Ok((combined, held))
}

/// Try the equations of one priority group in order until one applies ([`scan_alternatives`]).
/// An undecided group blocks; one whose equations were context dependent or unused is not
/// cacheable. The diagnostics of the undecided attempts are held in `indeterminate_attempts`,
/// for the caller to commit if the subject is kept.
#[deny(clippy::wildcard_enum_match_arm)]
pub(super) fn scan_group<R, T, N>(
    rules: &[Arc<R>],
    indeterminate_attempts: &mut IndeterminateAttempts,
    attempt: impl FnMut(&Arc<R>) -> SimplifyResult<EquationAttempt<T, N>>,
) -> SimplifyResult<GroupScan<T>> {
    let (combined, undecided) = scan_alternatives(rules, attempt)?;
    indeterminate_attempts.0.extend(undecided);
    Ok(match combined {
        Combined::Applied(result) => GroupScan::Applied(result),
        Combined::Indeterminate(_) | Combined::Recurred => GroupScan::Blocked,
        Combined::ContextDependent | Combined::Unused => GroupScan::NotCacheable,
        Combined::NotApplicable(_evidence) => GroupScan::NotApplicable,
    })
}

/// Try the instances of one equation, one per matching of its left-hand side against the
/// subject, in the matcher's order, until one applies.
///
/// A left-hand side with a map or set pattern can match one subject in several ways, binding
/// `σ1, ..., σn`. Each instance `f(t) = rhs σi requires R σi` is by itself a consequence of the
/// equation, so the equation applies to `t` as soon as one instance does, and is passed over
/// only when every instance is. The instances therefore combine exactly as the equations of one
/// priority group do ([`scan_alternatives`]): the first instance that applies gives the result
/// (when several would apply with different results, the definition equates those results, and
/// the load-time check pairs the equation with itself unless its right-hand side and `ensures`
/// read only variables every matching binds alike); otherwise an undecided instance leaves the
/// equation undecided, so that a lower-priority group does not fire where this equation may
/// apply.
///
/// The undecided instances' diagnostics are committed to the enclosing collector only if the
/// equation ends undecided, as they explain that outcome. A single instance is attempted
/// directly.
#[deny(clippy::wildcard_enum_match_arm)]
pub(super) fn scan_instances<S, T, N>(
    mut instances: Vec<S>,
    mut attempt: impl FnMut(S) -> SimplifyResult<EquationAttempt<T, N>>,
) -> SimplifyResult<EquationAttempt<T, N>> {
    if instances.len() == 1 {
        return attempt(instances.pop().expect("one instance"));
    }
    let (combined, undecided) = scan_alternatives(instances, attempt)?;
    let commit_undecided = |outcome| {
        for diagnostics in undecided {
            diagnostics.commit();
        }
        outcome
    };
    Ok(match combined {
        Combined::Applied(result) => EquationAttempt::Applied(result),
        Combined::Indeterminate(reason) => commit_undecided(EquationAttempt::Indeterminate(reason)),
        Combined::Recurred => commit_undecided(EquationAttempt::Recurred),
        Combined::ContextDependent => EquationAttempt::ContextDependent,
        Combined::Unused => EquationAttempt::Unused,
        Combined::NotApplicable(evidence) => {
            EquationAttempt::NotApplicable(evidence.expect("an equation has at least one instance"))
        }
    })
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::{EquationAttempt, GroupScan, IndeterminateAttempts, scan_group, scan_instances};
    use crate::{diagnostic, simplify::ConditionIndeterminacy};

    type Outcome = EquationAttempt<&'static str, ()>;

    /// Attempt alternative `index` of `outcomes`: emit a diagnostic naming it and end as given.
    fn replay(outcomes: &[Outcome], index: usize) -> Outcome {
        diagnostic::emit_rule_condition_budget_exhausted(&format!("alternative-{index}"), 1);
        match &outcomes[index] {
            EquationAttempt::Applied(result) => EquationAttempt::Applied(*result),
            EquationAttempt::NotApplicable(()) => EquationAttempt::NotApplicable(()),
            EquationAttempt::Indeterminate(_) => {
                EquationAttempt::Indeterminate(ConditionIndeterminacy::NoSolver)
            }
            EquationAttempt::ContextDependent => EquationAttempt::ContextDependent,
            EquationAttempt::Unused => EquationAttempt::Unused,
            EquationAttempt::Recurred => EquationAttempt::Recurred,
        }
    }

    /// The alternatives whose diagnostics reached the collector shown as `shown`.
    fn reached(outcomes: &[Outcome], shown: &str) -> Vec<usize> {
        (0..outcomes.len())
            .filter(|index| shown.contains(&format!("\"alternative-{index}\"")))
            .collect()
    }

    /// The instances of one equation, ending as `outcomes` in order; returns the scan's outcome
    /// and the instances whose diagnostics reached the collector.
    fn scan(outcomes: &[Outcome]) -> (String, Vec<usize>) {
        let (outcome, diagnostics) = diagnostic::collect(|| {
            scan_instances((0..outcomes.len()).collect(), |instance| {
                Ok(replay(outcomes, instance))
            })
        });
        let outcome = match outcome.expect("no attempt stops") {
            EquationAttempt::Applied(result) => format!("applied {result}"),
            EquationAttempt::NotApplicable(()) => "not applicable".to_owned(),
            EquationAttempt::Indeterminate(_) => "indeterminate".to_owned(),
            EquationAttempt::ContextDependent => "context dependent".to_owned(),
            EquationAttempt::Unused => "unused".to_owned(),
            EquationAttempt::Recurred => "recurred".to_owned(),
        };
        (outcome, reached(outcomes, &format!("{diagnostics:?}")))
    }

    /// The equations of one priority group, ending as `outcomes` in order; returns the scan's
    /// outcome, the equations whose diagnostics reached the collector, and how many attempts it
    /// held for the caller.
    fn scan_equations(outcomes: &[Outcome]) -> (String, Vec<usize>, usize) {
        let rules = (0..outcomes.len()).map(Arc::new).collect::<Vec<_>>();
        let mut held = IndeterminateAttempts::default();
        let (outcome, diagnostics) = diagnostic::collect(|| {
            scan_group(&rules, &mut held, |rule| Ok(replay(outcomes, **rule)))
        });
        let outcome = match outcome.expect("no attempt stops") {
            GroupScan::Applied(result) => format!("applied {result}"),
            GroupScan::Blocked => "blocked".to_owned(),
            GroupScan::NotCacheable => "not cacheable".to_owned(),
            GroupScan::NotApplicable => "not applicable".to_owned(),
        };
        (
            outcome,
            reached(outcomes, &format!("{diagnostics:?}")),
            held.0.len(),
        )
    }

    /// Diagnostics follow the outcome they explain: an instance passed over (refuted, unused)
    /// explains nothing, an applied instance explains the result, and undecided instances explain
    /// an undecided equation, but not one that a later instance applies.
    #[test]
    fn only_the_instances_that_explain_the_outcome_report_their_diagnostics() {
        use EquationAttempt::{Applied, Indeterminate, NotApplicable, Unused};
        let undecided = || Indeterminate(ConditionIndeterminacy::NoSolver);

        assert_eq!(
            scan(&[NotApplicable(()), Unused, Applied("r")]),
            ("applied r".to_owned(), vec![2])
        );
        assert_eq!(
            scan(&[undecided(), NotApplicable(()), Applied("r")]),
            ("applied r".to_owned(), vec![2])
        );
        assert_eq!(
            scan(&[NotApplicable(()), undecided(), Unused, undecided()]),
            ("indeterminate".to_owned(), vec![1, 3])
        );
        assert_eq!(
            scan(&[NotApplicable(()), Unused]),
            ("unused".to_owned(), vec![])
        );
        assert_eq!(
            scan(&[
                NotApplicable(()),
                EquationAttempt::Recurred,
                Unused,
                undecided()
            ]),
            ("recurred".to_owned(), vec![1, 3])
        );
    }

    /// Diagnostics follow the outcome they explain, as for the instances of one equation: an
    /// equation passed over (refuted, unused) explains nothing, an applied one explains the
    /// result, and undecided ones are held for the caller, which commits them only if the
    /// subject is kept.
    #[test]
    fn only_the_equations_that_explain_the_outcome_report_their_diagnostics() {
        use EquationAttempt::{Applied, Indeterminate, NotApplicable, Unused};
        let undecided = || Indeterminate(ConditionIndeterminacy::NoSolver);

        assert_eq!(
            scan_equations(&[NotApplicable(()), Unused, Applied("r")]),
            ("applied r".to_owned(), vec![2], 0)
        );
        assert_eq!(
            scan_equations(&[undecided(), NotApplicable(()), Applied("r")]),
            ("applied r".to_owned(), vec![2], 1)
        );
        assert_eq!(
            scan_equations(&[NotApplicable(()), undecided(), Unused, undecided()]),
            ("blocked".to_owned(), vec![], 2)
        );
        assert_eq!(
            scan_equations(&[NotApplicable(()), Unused]),
            ("not cacheable".to_owned(), vec![], 0)
        );
        assert_eq!(
            scan_equations(&[NotApplicable(()), NotApplicable(())]),
            ("not applicable".to_owned(), vec![], 0)
        );
        assert_eq!(
            scan_equations(&[EquationAttempt::Recurred, Unused, undecided()]),
            ("blocked".to_owned(), vec![], 2)
        );
    }
}

//! Request-local diagnostics emitted by backend operations.

use std::cell::RefCell;

use crate::{
    builtin::UnsupportedHookReason,
    rule::Predicate,
    simplify::{BudgetSubject, ConditionIndeterminacy},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BackendDiagnostic {
    UndecidedCondition {
        rule_id: String,
        reason: ConditionIndeterminacy,
        predicates: Vec<Predicate>,
    },
    UndecidedPredicate {
        predicate: Predicate,
        reason: ConditionIndeterminacy,
    },
    SimplificationBudgetExhausted {
        limit: usize,
        subject: BudgetSubject,
    },
    /// The side conditions of an application attempt of the rule `rule_id` (its `requires`,
    /// the definedness obligations of its bindings, or its `ensures`) exhausted the budget
    /// `limit` while being simplified and were decided in their unsimplified form, so the rule
    /// may be left unapplied for lack of budget rather than because its condition is open.
    /// Always recorded in a collection right after the `SimplificationBudgetExhausted` with
    /// subject `Predicates` that it qualifies; in an execution path's list, which keeps each
    /// distinct diagnostic once, it follows that exhaustion but not necessarily directly.
    RuleConditionUnsimplified { rule_id: String, limit: usize },
    UnsupportedHookUnevaluated {
        hook: String,
        reason: UnsupportedHookReason,
    },
}

thread_local! {
    static SINK: RefCell<Option<Vec<BackendDiagnostic>>> = const { RefCell::new(None) };
}

/// Record a diagnostic when the current thread has an active collector.
pub fn emit(diagnostic: BackendDiagnostic) {
    SINK.with(|sink| {
        if let Some(diagnostics) = sink.borrow_mut().as_mut() {
            record(diagnostics, diagnostic);
        }
    });
}

/// Append `diagnostic` to a collection under its once-per-collection rule: an unevaluated hook
/// is reported once per hook, whatever the reason given at later calls; every other diagnostic
/// is appended as emitted.
fn record(diagnostics: &mut Vec<BackendDiagnostic>, diagnostic: BackendDiagnostic) {
    if let BackendDiagnostic::UnsupportedHookUnevaluated { hook, .. } = &diagnostic
        && diagnostics.iter().any(|existing| {
            matches!(
                existing,
                BackendDiagnostic::UnsupportedHookUnevaluated {
                    hook: existing_hook,
                    ..
                } if existing_hook == hook
            )
        })
    {
        return;
    }
    diagnostics.push(diagnostic);
}

/// Record that simplifying the side conditions of `rule_id` exhausted the budget `limit`: a
/// `SimplificationBudgetExhausted` over `Predicates` qualified by `RuleConditionUnsimplified`.
///
/// The simplifier re-attempts a rule each time it meets the same redex, so the pair is recorded
/// once per rule and limit in a collection; repeated attempts report the same fact.
pub(crate) fn emit_rule_condition_budget_exhausted(rule_id: &str, limit: usize) {
    SINK.with(|sink| {
        if let Some(diagnostics) = sink.borrow_mut().as_mut() {
            record_rule_condition_budget_exhausted(diagnostics, rule_id, limit);
        }
    });
}

fn record_rule_condition_budget_exhausted(
    diagnostics: &mut Vec<BackendDiagnostic>,
    rule_id: &str,
    limit: usize,
) {
    if diagnostics.iter().any(|existing| {
        matches!(
            existing,
            BackendDiagnostic::RuleConditionUnsimplified {
                rule_id: existing_rule,
                limit: existing_limit,
            } if existing_rule == rule_id && *existing_limit == limit
        )
    }) {
        return;
    }
    diagnostics.push(BackendDiagnostic::SimplificationBudgetExhausted {
        limit,
        subject: BudgetSubject::Predicates,
    });
    diagnostics.push(BackendDiagnostic::RuleConditionUnsimplified {
        rule_id: rule_id.to_owned(),
        limit,
    });
}

/// Append a finished collection to an enclosing one, applying the enclosing collection's rules
/// as if each diagnostic had been emitted into it directly.
///
/// A collection is only ever appended to by `record` and `record_rule_condition_budget_exhausted`,
/// so a `RuleConditionUnsimplified` directly follows the `SimplificationBudgetExhausted` over
/// `Predicates` with the same limit that it qualifies; the two are replayed as the pair they were
/// recorded as. Replaying in order reproduces the enclosing list direct emission would have built:
/// a diagnostic the inner rules dropped duplicates an earlier inner one, which the enclosing rules
/// meet first and drop it against in turn.
fn forward(enclosing: &mut Vec<BackendDiagnostic>, inner: &[BackendDiagnostic]) {
    let mut index = 0;
    while let Some(diagnostic) = inner.get(index) {
        index += 1;
        if let BackendDiagnostic::SimplificationBudgetExhausted {
            limit,
            subject: BudgetSubject::Predicates,
        } = diagnostic
            && let Some(BackendDiagnostic::RuleConditionUnsimplified {
                rule_id,
                limit: qualified_limit,
            }) = inner.get(index)
            && qualified_limit == limit
        {
            index += 1;
            record_rule_condition_budget_exhausted(enclosing, rule_id, *limit);
            continue;
        }
        record(enclosing, diagnostic.clone());
    }
}

/// Append `diagnostics` to the list of one execution path, keeping the first occurrence of each
/// diagnostic: a path records a fact once however many of its states report it, in the order the
/// path first met it.
pub(crate) fn extend_path(path: &mut Vec<BackendDiagnostic>, diagnostics: &[BackendDiagnostic]) {
    for diagnostic in diagnostics {
        if !path.contains(diagnostic) {
            path.push(diagnostic.clone());
        }
    }
}

/// Collect diagnostics emitted while `action` runs.
///
/// Collections nest: when `action` returns, the enclosing collector (if any) is restored and
/// receives the collected diagnostics under its own once-per-collection rules, so a caller
/// collecting around an operation sees every diagnostic whatever the operation collects inside.
pub fn collect<T>(action: impl FnOnce() -> T) -> (T, Vec<BackendDiagnostic>) {
    let previous = SINK.with(|sink| sink.replace(Some(Vec::new())));
    let restore = SinkGuard(previous);
    let result = action();
    let diagnostics = SINK.with(|sink| sink.replace(None).unwrap_or_default());
    drop(restore);
    SINK.with(|sink| {
        if let Some(enclosing) = sink.borrow_mut().as_mut() {
            forward(enclosing, &diagnostics);
        }
    });
    (result, diagnostics)
}

struct SinkGuard(Option<Vec<BackendDiagnostic>>);

impl Drop for SinkGuard {
    fn drop(&mut self) {
        SINK.with(|sink| {
            sink.replace(self.0.take());
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn term_exhausted(limit: usize) -> BackendDiagnostic {
        BackendDiagnostic::SimplificationBudgetExhausted {
            limit,
            subject: BudgetSubject::Term,
        }
    }

    fn predicates_exhausted(limit: usize) -> BackendDiagnostic {
        BackendDiagnostic::SimplificationBudgetExhausted {
            limit,
            subject: BudgetSubject::Predicates,
        }
    }

    fn rule_condition(rule_id: &str, limit: usize) -> BackendDiagnostic {
        BackendDiagnostic::RuleConditionUnsimplified {
            rule_id: rule_id.to_owned(),
            limit,
        }
    }

    fn hook(hook: &str, reason: UnsupportedHookReason) -> BackendDiagnostic {
        BackendDiagnostic::UnsupportedHookUnevaluated {
            hook: hook.to_owned(),
            reason,
        }
    }

    fn out_of_range() -> UnsupportedHookReason {
        UnsupportedHookReason::ArgumentOutOfRange {
            detail: "second call".to_owned(),
        }
    }

    /// The emissions every nesting below performs, in order: two batches, each of which a nested
    /// collection may capture.
    fn first_batch() {
        emit(hook("INT.pow", UnsupportedHookReason::NotImplemented));
        emit(term_exhausted(3));
        emit_rule_condition_budget_exhausted("r1", 3);
        emit(predicates_exhausted(3));
    }

    fn second_batch() {
        emit(hook("INT.pow", out_of_range()));
        emit(term_exhausted(3));
        emit_rule_condition_budget_exhausted("r1", 3);
        emit(predicates_exhausted(3));
        emit_rule_condition_budget_exhausted("r2", 3);
        emit(hook("INT.log2", UnsupportedHookReason::NotImplemented));
    }

    #[test]
    fn nested_collection_forwards_to_the_enclosing_collector_under_its_rules() {
        let ((), direct) = collect(|| {
            first_batch();
            second_batch();
        });
        let expected = vec![
            hook("INT.pow", UnsupportedHookReason::NotImplemented),
            term_exhausted(3),
            predicates_exhausted(3),
            rule_condition("r1", 3),
            predicates_exhausted(3),
            term_exhausted(3),
            predicates_exhausted(3),
            predicates_exhausted(3),
            rule_condition("r2", 3),
            hook("INT.log2", UnsupportedHookReason::NotImplemented),
        ];
        assert_eq!(direct, expected);

        let ((inner_first, inner_second), outer) = collect(|| {
            let ((), first) = collect(first_batch);
            let (second, _) = collect(|| collect(second_batch).1);
            (first, second)
        });
        assert_eq!(
            outer, expected,
            "the enclosing collector sees the direct list"
        );
        assert_eq!(
            inner_first,
            vec![
                hook("INT.pow", UnsupportedHookReason::NotImplemented),
                term_exhausted(3),
                predicates_exhausted(3),
                rule_condition("r1", 3),
                predicates_exhausted(3),
            ]
        );
        assert_eq!(
            inner_second,
            vec![
                hook("INT.pow", out_of_range()),
                term_exhausted(3),
                predicates_exhausted(3),
                rule_condition("r1", 3),
                predicates_exhausted(3),
                predicates_exhausted(3),
                rule_condition("r2", 3),
                hook("INT.log2", UnsupportedHookReason::NotImplemented),
            ],
            "an inner collection applies its rules to its own emissions only"
        );
    }

    #[test]
    fn a_collection_without_an_enclosing_collector_forwards_nothing() {
        let ((), inner) = collect(first_batch);
        assert_eq!(inner.len(), 5);
        emit(term_exhausted(1));
        let ((), after) = collect(|| {});
        assert!(after.is_empty(), "no collector outlives its collection");
    }

    #[test]
    fn a_path_records_each_diagnostic_once_in_first_occurrence_order() {
        let mut path = vec![term_exhausted(3)];
        extend_path(
            &mut path,
            &[
                predicates_exhausted(3),
                rule_condition("r1", 3),
                term_exhausted(3),
                predicates_exhausted(3),
                rule_condition("r2", 3),
            ],
        );
        extend_path(&mut path, &[term_exhausted(3), rule_condition("r1", 3)]);
        assert_eq!(
            path,
            vec![
                term_exhausted(3),
                predicates_exhausted(3),
                rule_condition("r1", 3),
                rule_condition("r2", 3),
            ]
        );
    }
}

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
    /// Always recorded right after the `SimplificationBudgetExhausted` with subject
    /// `Predicates` that it qualifies.
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
    });
}

/// Record that simplifying the side conditions of `rule_id` exhausted the budget `limit`: a
/// `SimplificationBudgetExhausted` over `Predicates` qualified by `RuleConditionUnsimplified`.
///
/// The simplifier re-attempts a rule each time it meets the same redex, so the pair is recorded
/// once per rule and limit in a collection; repeated attempts report the same fact.
pub(crate) fn emit_rule_condition_budget_exhausted(rule_id: &str, limit: usize) {
    SINK.with(|sink| {
        let mut sink = sink.borrow_mut();
        let Some(diagnostics) = sink.as_mut() else {
            return;
        };
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
    });
}

/// Collect diagnostics emitted while `action` runs, restoring any enclosing collector afterward.
pub fn collect<T>(action: impl FnOnce() -> T) -> (T, Vec<BackendDiagnostic>) {
    let previous = SINK.with(|sink| sink.replace(Some(Vec::new())));
    let restore = SinkGuard(previous);
    let result = action();
    let diagnostics = SINK.with(|sink| sink.replace(None).unwrap_or_default());
    drop(restore);
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

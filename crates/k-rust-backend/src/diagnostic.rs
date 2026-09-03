//! Request-local diagnostics emitted by backend operations.

use std::cell::RefCell;

use crate::{rule::Predicate, simplify::ConditionIndeterminacy};

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
}

thread_local! {
    static SINK: RefCell<Option<Vec<BackendDiagnostic>>> = const { RefCell::new(None) };
}

/// Record a diagnostic when the current thread has an active collector.
pub fn emit(diagnostic: BackendDiagnostic) {
    SINK.with(|sink| {
        if let Some(diagnostics) = sink.borrow_mut().as_mut() {
            diagnostics.push(diagnostic);
        }
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

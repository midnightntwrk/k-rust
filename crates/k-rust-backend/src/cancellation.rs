//! Cooperative cancellation for synchronous backend operations.

use std::{
    cell::RefCell,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

thread_local! {
    static ACTIVE_TOKEN: RefCell<Option<CancellationToken>> = const { RefCell::new(None) };
    static OPERATION_TOKENS: RefCell<Vec<CancellationToken>> = const { RefCell::new(Vec::new()) };
}

/// A cheaply clonable signal used to cancel one in-process backend request.
#[derive(Clone, Debug, Default)]
pub struct CancellationToken(Arc<AtomicBool>);

impl CancellationToken {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn cancel(&self) {
        self.0.store(true, Ordering::Release);
    }

    pub fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::Acquire)
    }

    /// Make this token visible to cooperative interruption points for the duration of `action`.
    pub fn scope<T>(&self, action: impl FnOnce() -> T) -> T {
        let previous = ACTIVE_TOKEN.with(|active| active.replace(Some(self.clone())));
        let _restore = ActiveTokenGuard(previous);
        action()
    }

    /// Add an operation-local signal without replacing an outer request cancellation token.
    pub fn scope_operation<T>(&self, action: impl FnOnce() -> T) -> T {
        OPERATION_TOKENS.with(|active| active.borrow_mut().push(self.clone()));
        let _restore = OperationTokenGuard;
        action()
    }
}

/// Return whether the operation active on this thread has been cancelled.
pub fn cancellation_requested() -> bool {
    let outer_cancelled = ACTIVE_TOKEN.with(|active| {
        active
            .borrow()
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled)
    });
    outer_cancelled
        || OPERATION_TOKENS
            .with(|active| active.borrow().iter().any(CancellationToken::is_cancelled))
}

struct ActiveTokenGuard(Option<CancellationToken>);

impl Drop for ActiveTokenGuard {
    fn drop(&mut self) {
        ACTIVE_TOKEN.with(|active| {
            active.replace(self.0.take());
        });
    }
}

struct OperationTokenGuard;

impl Drop for OperationTokenGuard {
    fn drop(&mut self) {
        OPERATION_TOKENS.with(|active| {
            active.borrow_mut().pop();
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scopes_and_restores_active_tokens() {
        let outer = CancellationToken::new();
        let inner = CancellationToken::new();
        outer.cancel();

        assert!(!cancellation_requested());
        outer.scope(|| {
            assert!(cancellation_requested());
            inner.scope(|| assert!(!cancellation_requested()));
            assert!(cancellation_requested());
        });
        assert!(!cancellation_requested());
    }

    #[test]
    fn cloned_tokens_signal_across_threads() {
        let token = CancellationToken::new();
        let signal = token.clone();
        std::thread::spawn(move || signal.cancel()).join().unwrap();

        assert!(token.is_cancelled());
    }

    #[test]
    fn operation_signal_composes_with_outer_cancellation_and_does_not_leak() {
        let outer = CancellationToken::new();
        let operation = CancellationToken::new();
        outer.scope(|| {
            operation.scope_operation(|| {
                assert!(!cancellation_requested());
                operation.cancel();
                assert!(cancellation_requested());
                assert!(!outer.is_cancelled());
            });
            assert!(!cancellation_requested());
            let next = CancellationToken::new();
            next.scope_operation(|| assert!(!cancellation_requested()));
            outer.cancel();
            next.scope_operation(|| assert!(cancellation_requested()));
        });
        assert!(!cancellation_requested());
    }
}

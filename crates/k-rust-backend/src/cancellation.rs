//! Cooperative cancellation for synchronous backend operations.
//!
//! The request token and its registry live in [`crate::stop`]; this module keeps the legacy
//! predicate until every interruption point polls `stop::check` (CBC-04-T11).

pub use crate::stop::CancellationToken;

/// Return whether the operation active on this thread has been cancelled: its request token is
/// cancelled, or the prelude of a solver it uses failed.
pub fn cancellation_requested() -> bool {
    crate::stop::legacy_cancellation_requested()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stop::{PreludeFailure, PreludeSignal, with_prelude_signal};

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
    fn prelude_signal_composes_with_outer_cancellation_and_does_not_leak() {
        let outer = CancellationToken::new();
        let operation = PreludeSignal::default();
        outer.scope(|| {
            with_prelude_signal(&operation, || {
                assert!(!cancellation_requested());
                operation.raise(PreludeFailure::Inconsistent);
                assert!(cancellation_requested());
                assert!(!outer.is_cancelled());
            });
            assert!(!cancellation_requested());
            let next = PreludeSignal::default();
            with_prelude_signal(&next, || assert!(!cancellation_requested()));
            outer.cancel();
            with_prelude_signal(&next, || assert!(cancellation_requested()));
        });
        assert!(!cancellation_requested());
    }
}

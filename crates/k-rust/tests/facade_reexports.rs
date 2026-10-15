//! A host compiles against `k_rust` alone: the cancellation surface is named through
//! `k_rust::backend`, and every backend type the facade's public signatures carry is named
//! through `k_rust::k_rust_backend`.
//!
//! This file imports nothing from `k_rust_backend` directly, so it fails to compile when one of
//! these paths goes away.

use k_rust::backend::{
    Backend, BackendError, BackendOptions, CancellationToken, PreludeFailure, SegmentRefused,
    StackLimit, StepTimeoutMode, StopCause, StopScope, VARIABLE_IDENTITY,
};
use k_rust::k_rust_backend::{definition::BackendDefinition, smt::SmtSolver};
use std::time::Duration;

const DEFINITION: &str = r#"[]
module TEST
  sort SortK{} []
  symbol value{}() : SortK{} [constructor{}()]
endmodule []"#;

/// A host's error type, as `Backend::with_solver` requires it, written with facade names only.
#[derive(Debug)]
enum HostError {
    Backend(String),
    Stopped(StopCause),
}

impl std::fmt::Display for HostError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Backend(message) => formatter.write_str(message),
            Self::Stopped(cause) => write!(formatter, "stopped: {}", cause_name(cause)),
        }
    }
}

impl From<BackendError> for HostError {
    fn from(error: BackendError) -> Self {
        Self::Backend(error.to_string())
    }
}

impl From<StopCause> for HostError {
    fn from(cause: StopCause) -> Self {
        Self::Stopped(cause)
    }
}

/// Every cause, with the payload types named through the facade.
fn cause_name(cause: &StopCause) -> &'static str {
    match cause {
        StopCause::Cancelled => "cancelled",
        StopCause::Deadline(StepTimeoutMode::Manual(_)) => "manual deadline",
        StopCause::Deadline(StepTimeoutMode::MovingAverage(_)) => "moving-average deadline",
        StopCause::StackExhausted(StackLimit::ThreadBudget(_)) => "thread budget",
        StopCause::StackExhausted(StackLimit::ProcessBudget(_)) => "process budget",
        StopCause::StackExhausted(StackLimit::MappingRefused(SegmentRefused { .. })) => {
            "mapping refused"
        }
        StopCause::SolverPrelude(PreludeFailure::Inconsistent) => "inconsistent prelude",
        StopCause::SolverPrelude(PreludeFailure::Unknown(_)) => "undecided prelude",
    }
}

fn main_module(definition: &BackendDefinition, _solver: &dyn SmtSolver) -> String {
    definition.main_module().to_string()
}

/// `k_rust::backend::StopCause` is the backend's own type, not a copy: a function over one
/// accepts the other.
fn accepts_backend_cause(cause: k_rust::k_rust_backend::stop::StopCause) -> StopCause {
    cause
}

#[test]
fn a_host_runs_an_operation_with_facade_names_only() {
    let mut backend = Backend::new(DEFINITION, "TEST", BackendOptions::default()).unwrap();
    let token = CancellationToken::new();
    let module = token
        .scope(|| {
            backend.with_solver(None, |definition, solver| {
                Ok::<_, HostError>(main_module(definition, solver))
            })
        })
        .unwrap_or_else(|error| panic!("{error}"));
    assert_eq!(module, "TEST");
}

#[test]
fn the_reexports_are_the_backend_items() {
    assert_eq!(VARIABLE_IDENTITY, 3);
    assert_eq!(
        VARIABLE_IDENTITY,
        k_rust::k_rust_backend::term::names::VARIABLE_IDENTITY
    );
    let cause = accepts_backend_cause(StopCause::Cancelled);
    assert_eq!(cause_name(&cause), "cancelled");
    assert_eq!(cause.scope(), StopScope::Request);
    let deadline = StopCause::Deadline(StepTimeoutMode::Manual(Duration::from_millis(5)));
    assert_eq!(cause_name(&deadline), "manual deadline");
    assert_eq!(deadline.scope(), StopScope::Step);
    let refused =
        StopCause::StackExhausted(StackLimit::MappingRefused(SegmentRefused { size: 1 << 20 }));
    assert_eq!(cause_name(&refused), "mapping refused");
    let error = HostError::from(cause);
    assert!(matches!(error, HostError::Stopped(StopCause::Cancelled)));
}

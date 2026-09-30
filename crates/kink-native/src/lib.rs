//! Fail-closed integration with the k-rust backend.
//!
//! - [`NativeValidator`] applies a kink-patch patch and compiles the mutant with k-rust.
//! - [`execution`] runs event-free and stepped, time-bounded executions through the k-rust facade.
//! - [`execution_difference`] records rewrite state sequences and difference proof outcomes.
//! - [`step_events`] declares and classifies events over the configurations of each step.
//! - [`observation`] retains branch-local execution states.
//! - [`bridge`] maps adapted executions to kink-pattern paths and collection evidence.
//! - [`feasibility`] decides solver-free leaf feasibility and payload relations with the
//!   backend's definition and unifier ([`feasibility::BackendRelations`]).
//!
pub mod bridge;
mod equivalence;
pub mod execution;
pub mod execution_difference;
pub mod feasibility;
pub mod observation;
pub mod report;
pub mod step_events;
#[cfg(test)]
#[path = "../../../testdata/k/support.rs"]
mod support;
mod validator;

pub use equivalence::equivalent_compilation;
pub use validator::{MutantRejection, NativeFailure, NativeValidator, ValidatedDefinition};

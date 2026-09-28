//! Fail-closed integration with the k-rust backend.
//!
//! - [`NativeValidator`] applies a kink-patch patch and compiles the mutant with k-rust.
//! - [`execution`] runs observed, time-bounded executions through the k-rust `execute` facade.
//! - [`execution_difference`] records rewrite state sequences and difference proof outcomes.
//! - [`observation`] installs source-position rule observations and adapts branch-local events;
//!   [`select_rules`] chooses those positions by label, attribute, term structure, or every rewrite rule.
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
mod selector;
#[cfg(test)]
#[path = "../../../testdata/k/support.rs"]
mod support;
mod validator;

pub use equivalence::equivalent_compilation;
pub use selector::{
    ClassificationFailure, RewriteRules, RuleSelection, RuleSelector, SelectionFailure,
    select_rules,
};
pub use validator::{
    IdentityError, ManifestFailure, MutantRejection, NativeFailure, NativeValidator, ObservedRule,
    ValidatedDefinition,
};

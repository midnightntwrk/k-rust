//! Fail-closed integration with the k-rust backend.
//!
//! - [`NativeValidator`] applies a kink-patch patch and compiles the mutant with k-rust.
//! - [`execution`] runs observed, time-bounded executions through the k-rust `execute` facade.
//! - [`observation`] installs exact-label rule observations and adapts branch-local events;
//!   [`select_rules`] chooses those rules by label, attribute, term structure or all of them.
//! - [`bridge`] maps adapted executions to kink-pattern paths and collection evidence.
//!
pub mod bridge;
pub mod execution;
pub mod observation;
mod selector;
mod validator;

pub use selector::{RuleSelection, RuleSelector, SelectionFailure, select_rules};
pub use validator::{
    IdentityError, ManifestFailure, MutantRejection, NativeFailure, NativeValidator, ObservedRule,
    ValidatedDefinition,
};

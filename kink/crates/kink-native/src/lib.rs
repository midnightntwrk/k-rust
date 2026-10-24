//! Fail-closed integration with the k-rust backend.
//!
//! - [`NativeValidator`] applies a kink-patch patch and compiles the mutant with k-rust.
//! - [`execution`] runs event-free and stepped, time-bounded executions through the k-rust facade.
//! - [`signature`] records the definition-independent structure shared by observation sides.
//! - [`step_events`] declares and classifies events over the configurations of each step.
//! - [`observation`] retains branch-local execution states.
//! - [`bridge`] maps adapted executions to kink-pattern paths and collection evidence.
//! - [`exclusion`] names the runs that are no evidence for any comparison (stack stops, load
//!   stack stops, contradicted claims, implementation-chosen hooks, allowance refusals).
//! - [`data`] reads each definition's full critical-pair check once ([`data::DataFacts`]) and
//!   says which ends of runs on it are data under it ([`data::data_ends`]): none while a finding
//!   no `assume_joined` name assumes is left.
//! - [`consistency`] refuses a mutant whose edit makes two equations of one function disagree
//!   (k-rust's critical-pair check on the claim-free mutant), reading what the edit changes from
//!   the compiled definitions, with kink-patch's source reading as a fail-closed cross-check.
//! - [`feasibility`] decides solver-free leaf feasibility and payload relations with the
//!   backend's definition and unifier ([`feasibility::BackendRelations`]).
//!
pub mod bridge;
pub mod census;
pub mod consistency;
pub mod coverage;
pub mod data;
mod equivalence;
pub mod exclusion;
pub mod execution;
pub mod feasibility;
pub mod observation;
pub mod report;
pub mod representation;
pub mod signature;
pub mod step_events;
#[cfg(test)]
#[path = "../../../testdata/k/support.rs"]
mod support;
mod validator;

pub use census::{
    CensusClass, CensusError, CensusFinding, CensusVerdict, DeclarationCensus, InertDeclaration,
    declaration_census,
};
pub use coverage::{
    Authorship, COVERAGE_DOMAIN, RuleAuthors, TestCoverage, coverage_digest, coverage_text,
};
pub use equivalence::equivalent_compilation;
pub use validator::{
    AHEAD_PER_WORKER, AheadChunk, KEPT_PER_WORKER, MutantRejection, NativeFailure, NativeValidator,
    ValidatedDefinition,
};

/// The k-rust kink builds against, named by the version of k-rust's package (build.rs reads it
/// from the in-repo `crates/k-rust/Cargo.toml`). kink is built inside k-rust's workspace against
/// the k-rust beside it, so a hard-coded commit would be false as soon as k-rust moved. The name
/// and the documents' `k_rust_revision` / `k_rust.revision` fields are kept. No store's soundness
/// rests on it: every store honoured without re-deriving its verdicts also keys on `kink_build`,
/// the SHA-256 of the executable, which changes with the linked k-rust (kink-campaign `identity`).
/// The k-rust commit kink's premises were last judged at is `[reference_pin]` of
/// upstream/k-rust.toml.
pub const K_RUST_REVISION: &str = env!("KINK_K_RUST_VERSION");

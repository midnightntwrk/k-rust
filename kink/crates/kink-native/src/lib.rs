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
//!   no `assume_joined` name assumes is left; otherwise those the terminal-value walk admits,
//!   instance-normal overload applications included where k-rust's `is_data` holds (fz26
//!   KINK-OVERLOAD-VALUE). The runner judges each compared end under both definitions.
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

/// The solver options of every backend kink builds, unless a corpus states its own resource
/// budget (kink-flow's `[budget] smt_resource_limit`, which replaces
/// [`SMT_RESOURCE_LIMIT`] only): k-rust's resource-bounded options, each Z3 attempt bounded by
/// Z3's resource units and by no clock. A run's verdict and every answer kink stores is then a
/// function of its query, these options and the Z3 build, never of the host's speed or load;
/// the time a run may take is bounded outside the solver (`ExecutionBudget::time`), and a run
/// that bound stops is never stored.
pub const BACKEND_OPTIONS: k_rust::backend::BackendOptions =
    k_rust::backend::BackendOptions::RESOURCE_BOUNDED;

/// The first attempt's Z3 resource units of [`BACKEND_OPTIONS`] (k-rust's
/// `DEFAULT_SMT_RESOURCE_LIMIT`, which states how it was calibrated).
pub const SMT_RESOURCE_LIMIT: std::num::NonZeroU32 = k_rust::backend::DEFAULT_SMT_RESOURCE_LIMIT;

/// [`BACKEND_OPTIONS`] with the first attempt bounded by `units` Z3 resource units.
#[must_use]
pub const fn backend_options(units: std::num::NonZeroU32) -> k_rust::backend::BackendOptions {
    k_rust::backend::BackendOptions {
        smt_resource_limit: Some(units),
        ..BACKEND_OPTIONS
    }
}

/// The solver an answer kink stores depends on, under the build's solver profile: `None` under
/// the no-Z3 profile, where no backend reads its solver options; under the Z3 profile
/// `{resource_limit, retries, z3: {version, library_sha256}}`, `options`' first attempt's units
/// (null in clock mode, whose answers no key can name) and retries, and the Z3 build that
/// counts the units (k-rust `z3_build`: two builds of one version can count them differently,
/// so the version string alone does not name the answer's solver; the digest is the library
/// file's, which names Z3 whatever kink is built around it). `library_sha256` is null when the
/// build cannot be named, and every such build shares that value, so a store keyed by it reads
/// and writes only when [`solver_named`] holds.
#[must_use]
pub fn solver_value(options: k_rust::backend::BackendOptions) -> Option<serde_json::Value> {
    if execution::SolverProfile::BUILD == execution::SolverProfile::NoZ3 {
        return None;
    }
    let build = k_rust::backend::z3_build();
    Some(serde_json::json!({
        "resource_limit": options.smt_resource_limit.map(std::num::NonZeroU32::get),
        "retries": options.smt_retry_limit,
        "z3": build.map(|build| serde_json::json!({
            "version": build.version,
            "library_sha256": build.library_sha256,
        })),
    }))
}

/// Why no answer kink stores can name its solver under the Z3 profile ([`solver_named`]).
pub const UNNAMED_Z3_BUILD: &str = "the Z3 build is unknown (the library file its code comes \
     from cannot be named): no stored answer could name the solver that decided it, so the caches \
     are neither read nor written";

/// Whether [`solver_value`] names the solver of an answer: always under the no-Z3 profile, where
/// no answer depends on one, and under the Z3 profile when the Z3 build is known (k-rust
/// `z3_build` named its library file). An unknown build (a shared library replaced or deleted
/// since it was mapped, a static link whose archive the build could not name) gives a key every
/// unknown build shares, so a store of answers is off then, with [`UNNAMED_Z3_BUILD`] as its
/// reason, as it is when kink's own build is unknown.
///
/// # Errors
///
/// [`UNNAMED_Z3_BUILD`] under the Z3 profile when the build cannot be named.
pub fn solver_named() -> Result<(), &'static str> {
    if execution::SolverProfile::BUILD == execution::SolverProfile::NoZ3 {
        return Ok(());
    }
    match k_rust::backend::z3_build() {
        Some(build) if build.library_sha256.is_some() => Ok(()),
        _ => Err(UNNAMED_Z3_BUILD),
    }
}

#[cfg(test)]
mod tests {
    /// The solver is named exactly when the key's value names the build: always without Z3, where
    /// there is no member, and under Z3 when the library's digest is known.
    #[test]
    fn the_solver_is_named_exactly_when_its_value_names_the_build() {
        let named = super::solver_named();
        match super::solver_value(super::BACKEND_OPTIONS) {
            None => assert_eq!(named, Ok(())),
            Some(value) => assert_eq!(
                named.is_ok(),
                value["z3"]["library_sha256"].is_string(),
                "{value}"
            ),
        }
        if named.is_err() {
            assert_eq!(named, Err(super::UNNAMED_Z3_BUILD));
        }
    }
}

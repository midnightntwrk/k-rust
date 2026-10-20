//! `krust fuzz` as a library: craft concrete input values for a given program under a given K
//! specification, such that an execution of that program reaches a stated target.
//!
//! A [`Campaign`] searches for values of the program's *holes* (literal spans of the unmodified
//! program text, configuration variables, or free variables of a KORE template) that make the
//! program reach a [`Target`]. Its product is a [`FuzzReport`]: a witness that a concrete re-run
//! confirmed, or a bounded "no witness found" that names the budget, the cases run, the coverage
//! reached and the outcome counts. "No witness found" is never a proof that no witness exists.
//!
//! The crate crafts inputs; it never generates programs. The program author writes the program
//! and marks its holes beside it, the crate chooses hole values, runs the program and reports.
//!
//! Design: `ARCHITECTURE.md` of the fz26 programme (sections cited as "ARCHITECTURE n.m" in the
//! rustdoc of each item).
//!
//! # Modules
//!
//! - [`spec`]: the campaign specification ([`CampaignSpec`] and its parts).
//! - [`holes`]: hole declarations and the overlay on the unmodified program.
//! - [`values`]: definition-independent hole values, their constraints and generators.
//! - [`exec`]: per-case execution, clean leaves, natural ends and outcome classes.
//! - [`target`]: targets and their judgement.
//! - [`report`]: the canonical JSON report.
//! - [`error`]: the errors [`Campaign::new`] reports.

// Phase-1 skeleton: some cross-module interfaces are written before the code that calls them.
// Integration round 1 removes this expectation once every one has a caller.
#![expect(
    dead_code,
    reason = "phase-1 interface stubs (FZ-01); removed at integration round 1"
)]

// The unit tests share the integration tests' fixture module (tests/support), declared once
// here as `crate::support`, so that crate-private code is tested against the real fixtures. The
// module names this crate `k_rust_fuzz`, as an integration test does.
#[cfg(test)]
extern crate self as k_rust_fuzz;
#[cfg(test)]
#[path = "../tests/support/mod.rs"]
mod support;

pub(crate) mod assemble;
mod engine;
pub mod error;
pub mod exec;
mod graph;
pub mod holes;
pub mod report;
pub mod spec;
pub mod target;
pub mod values;

pub use engine::Campaign;
pub use error::CampaignError;
pub use exec::OutcomeClass;
pub use holes::{HoleDecl, HoleLocation, SpanAddress};
pub use k_rust::backend::CancellationToken;
pub use report::FuzzReport;
pub use spec::{
    BackendRoute, Budget, CallerIdentity, CampaignSpec, CaseOptions, CompiledDefinition,
    Definitions, PathMode, ProgramInput, ProgramSource, ProposerConfig,
};
pub use target::{Target, TargetKind};
pub use values::{Constraints, Value};

/// The version of the engine's case sequence.
///
/// A campaign's report is a function of its definitions, program, holes, target, options,
/// budget, seed, the k-rust revision and this version (ARCHITECTURE 5.4, 9.3). It covers the
/// fuzz crate's proposer, schedule and generator code and the pinned versions of `proptest`,
/// `rand` and `rand_chacha`. Any change that can change the sequence of cases a fixed
/// specification produces bumps it; the golden determinism test fails when the sequence changes
/// without a bump. A cache key also needs the k-rust revision, which the caller supplies
/// ([`CallerIdentity`]).
pub const ENGINE_VERSION: u32 = 1;

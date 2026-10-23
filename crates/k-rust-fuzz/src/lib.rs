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
mod proposers;
pub mod report;
mod score;
mod source_names;
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
///
/// Version 2: map holes shrink by whole entries, which moves the shrunk witness of a map hole,
/// and the dictionary proposer's parameters join the case sequence's inputs.
/// The climb proposer (FZ-12) was added within version 2: no specification of an earlier build
/// could weigh it (`Campaign::new` refused it), and the sequence of every other specification is
/// unchanged, so it needed no bump; its parameters join the case sequence's inputs of a
/// climbing campaign. A climbing campaign's sequence also depends on the condition records the
/// k-rust revision reports. The corpus proposer (FZ-14) was added within version 2 on the same
/// grounds; its parameters join the case sequence's inputs of a campaign that weighs it.
///
/// Version 3: the climb and the corpus propose run-time literals from the comparisons of the
/// guards a case refuted (FZ-16), and their campaigns record the condition entries of the
/// dictionary's guard rules; the corpus also keeps a `miss` case that applied a rule a number of
/// times in a bucket no earlier `miss` case did (FZ-17, k-rust's applied counts). Both can move
/// the case sequence of a campaign that weighs the climb or the corpus: the run-time literals
/// act only for a rule target, and the counts move a sequence only where a case is kept for a
/// count alone. Blind, dictionary-only and solve-only campaigns keep theirs.
///
/// Version 4 (phase 5): an `Int` span hole whose position reads no probed negative integer back
/// as itself is generated from 0 (FZ-INTGEN), which moves the sequence of every campaign with
/// such a hole; and the classes the proposers read move with the phase's judgements: differential
/// ends as sets of final configurations under state sets with the one-path re-run (FZ-DIFFEND),
/// the every-`<k>` natural end of threaded configurations (FZ-UNSUPPORTED), and ends judged as
/// data (FZ-DATAEND).
pub const ENGINE_VERSION: u32 = 4;

#[cfg(test)]
mod release_tests {
    /// A release tag `vX.Y.Z` ships the dist packages of version X.Y.Z (dist-workspace.toml),
    /// and `krust fuzz` runs only a `krust-fuzz` built from its own k-rust sources: krust-fuzz
    /// ships in krust's releases only while this crate's version is k-rust's.
    #[test]
    fn version_is_k_rust_version() {
        let identity = k_rust::build_identity();
        let k_rust_version = identity.split('+').next().unwrap_or_default();
        assert_eq!(
            env!("CARGO_PKG_VERSION"),
            k_rust_version,
            "k-rust-fuzz's version must equal k-rust's (build identity {identity})"
        );
    }
}

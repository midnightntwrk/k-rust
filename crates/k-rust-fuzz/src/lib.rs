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
pub(crate) mod crash;
mod engine;
pub mod error;
pub mod exec;
pub mod filter;
mod findings;
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
pub use filter::{FilterRefusal, WitnessFilter};
pub use holes::{HoleDecl, HoleLocation, SpanAddress};
pub use k_rust::backend::CancellationToken;
pub use report::FuzzReport;
pub use spec::{
    BackendRoute, Budget, CallerIdentity, CampaignSpec, CaseOptions, CompiledDefinition,
    Definitions, PathMode, ProgramInput, ProgramSource, ProposerConfig,
};
pub use target::{Target, TargetKind};
pub use values::{Constraints, Value};

/// This build of k-rust-fuzz, which every report records as `identity.fuzz-revision`: the
/// package version, then `+src.` and the digest of the sources this crate and `krs-unparse` are
/// built from (the build script's `K_RUST_FUZZ_SOURCE_DIGEST`, by the rule of k-rust's
/// `build/source_digest.rs`), or the version and `k_rust::UNVERIFIED_BUILD` outside this
/// workspace's layout (FZ-REPLAY-WHOLE S4).
///
/// A report is computed by k-rust's runs and by this crate's code: its classes, judgements,
/// statements, warnings and summary lines. The k-rust revision names only the first, and
/// [`ENGINE_VERSION`] promises only the case sequence, so a fix of a classification or of a
/// statement that moves no golden campaign could change a report under an unchanged identity.
/// This revision names the rest: two builds whose report code differs, committed or not, record
/// different revisions. No caller can name another.
#[must_use]
pub fn build_identity() -> String {
    let digest = env!("K_RUST_FUZZ_SOURCE_DIGEST");
    if digest.is_empty() {
        format!("{}{}", env!("CARGO_PKG_VERSION"), k_rust::UNVERIFIED_BUILD)
    } else {
        format!("{}+src.{digest}", env!("CARGO_PKG_VERSION"))
    }
}

/// The version of the engine's case sequence.
///
/// A campaign's report is a function of its definitions, program, holes, target, options,
/// budget, seed, the k-rust revision, the k-rust-fuzz revision ([`build_identity`]) and this
/// version (ARCHITECTURE 5.4, 9.3). It covers the
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
///
/// Version 5 (phase 6): a campaign whose holes' domains are all finite runs each assignment
/// once, replacing a repeat by the next untried assignment of a seeded permutation, and ends
/// when all have run (FZ-POLISH N-T1); shrinking tries each hole's least value first and revisits
/// every hole, value trees included (N-T2); a campaign that reads data ends on a definition
/// whose full critical-pair check reports a finding not assumed joined runs no case
/// (not comparable at setup); and the data judgement's check reads an overlap over a sort with
/// no normal form like any other (FZ-EMPTYSORT), pairs each equation at an evaluated hook with the
/// hook's written meaning and refutes more overlaps (FZ-CONFLUENCE), which moves the classes the
/// proposers read.
///
/// Version 6 (phase 8): the data judgement's check refutes more overlaps (membership literals,
/// FZ-MEMBERSHIP; collection memberships, S2B-T2; the map rule, FZ-MAPKEY; literal bounds of
/// `INT.max` and `INT.min`, FZ-CONFLUENCE-F), adopts witness equations for pairs over sorts with
/// no normal form (FZ-EMPTYJOIN-WITNESS) with the claims read accordingly
/// (FZ-EMPTYJOIN-CLAIMS), splits a residual into the cases its equations distinguish
/// (FZ-CONFLUENCE-F), reads a leaf with a term-level `\and` of different sides conservatively
/// (FZ-ADOPT-AND) and widens `genuine` (S2B-T3), which moves the findings and the classes the
/// proposers read; a pattern target `at: any-state` now runs (FZ-ANYSTATE); and under
/// `comparable` a rule or pattern hit is also judged on the program's run of every path, and one
/// whose case ran one path or stopped at the target's rule takes one more run of every path,
/// counted in the case's work, which moves `Budget::Work` and shrinking, and refuses hits
/// (FZ-COMPARABLE-AQ). `query-confirmable` runs nothing more. A campaign with neither option keeps
/// its case sequence: its witness cases' comparable judgement is made after the search, outside
/// every case, and its run adds to `totals.work` alone.
///
/// Crash findings (FZ-CRASH, report version 8) came in within version 6: a crashed case keeps
/// its class, its confirmation and shrinking are charged to `totals.crash-work` alone, and the
/// campaign's backends are rebuilt after a panic with the requests the run made of them, so the
/// case sequence of every campaign is unchanged, except one whose solver does not start, which
/// now aborts at its first case (`solver-init`) where it ran every case as an error.
///
/// Version 7 (round 3, FZ-STATESET): all-paths rule targets, patterns `at: final` and the
/// program's run of every path that judges comparability run as k-rust state sets, so the
/// classes, work, coverage, condition records and applied counts the proposers read are those
/// of distinct states (verdict moves V1 to V7 of `docs/compatibility.md`, "Format versions"),
/// which moves `Budget::Work`, the corpus's and the climb's scores and the solve proposer's
/// budget, scaled from a blocked case's work.
///
/// Within version 7 (KRUST-ANYWHERE-HEAD, the same round-3 wave): a leaf's or reached state's
/// existence is k-rust's `ground_defined` (the definedness walk on the decided state) where it
/// was the stored `ceil_free` attribute, and an end's data judgement admits the instance-normal
/// applications of plain `anywhere` data heads (SIMPLE's stored `a[4]`). Cases on such programs
/// move from `unsupported` or `baseline-incomplete` (`not-ceil-free`, an end not data) to judged
/// classes, which the proposers read. Every case whose class was judged before keeps its class,
/// but an `at: any-state` hit can move to an earlier reached state (a state holding such an
/// application is now a clean reach), so its witness's `reaching.step` and
/// `reaching.configuration` may change.
///
/// Version 8 (round 4, FZ-ENGINE-R4): classes the proposers read move on inputs outside the
/// golden set. `covered` reads the committed transitions, so a step whose result was empty (a
/// rolled-back candidate, an undefined step) is no hit: such a case becomes `undefined` or
/// `miss`, and the campaign, which a hit would have ended, runs on. In a differential
/// campaign a mutant that refuses an input the baseline accepts (its grammar or its backend) is
/// `unsupported`, not `rejected`, which moves whether a campaign reaches the rejection cap; a
/// mutant whose initial state has no instance has the empty set of ends, so its cases move from
/// `rejected` to a removed end, `undefined` or `unsupported`; and an end naming a symbol or sort
/// the other definition does not declare is `unsupported` with its own reason. Every golden
/// campaign keeps its case sequence, so the fingerprints are re-pinned with the same digests.
///
/// Within version 8 (FZ-FRESH, the same wave): ends are compared without the content of their
/// `<generatedCounter>` cell (`k_rust::backend::counter_erased`), so a case whose ends differ
/// only there moves from a hit to `miss` (or another judged class); and a run through a rule
/// with two or more `!` variables carries k-rust's `fresh-association` mark, so its cases move
/// from judged classes to `baseline-incomplete` or `unsupported` as for any
/// implementation-chosen value. No golden campaign mints with such a rule or kills on the counter
/// alone, so the goldens keep their case sequences and digests.
pub const ENGINE_VERSION: u32 = 8;

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

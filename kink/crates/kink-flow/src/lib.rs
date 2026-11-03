//! The primary usage flow (flow package, README section 5): an LLM-written concrete
//! corpus for a K specification, described by one `FLOW.toml` corpus manifest.
//!
//! F-02 provides the manifest ([`manifest`]), admission of the specification and its
//! programs through kink-corpus's admission stages ([`admit`]) and the `check` command
//! ([`cli`]). F-03 adds the specification and program digests ([`digest`]) and the result
//! cache with the `results` command ([`results`]). F-04 adds the mutation list and its
//! resolution into one pinned patch per mutation ([`mutation`]). F-05 adds the kill search
//! and the `run` command ([`search`]). F-06 adds the survivor report to the run document and the
//! `report` command ([`report`]). F-14 adds the outcome cache: tier 1, the proved outcome of a
//! mutation on a program under an exact key ([`outcomes`]), and tier 2, killer hints that
//! survive specification edits ([`hints`], which replaces F-05's killer cache). F-12 runs each
//! program's baseline at most once per command; F-13 names the oracle slots of the report,
//! records timings and leaf censuses, orders the kill search cheapest killer first and lists
//! the rules no mutation targets. F-18 adds the per-input pattern checks: `PATTERNS.toml`, the
//! lowering of a K pattern and its evaluation by k-rust's search ([`pattern`]), and the `query`
//! command with its cache of definitive answers ([`query`]). fz26 P7-KINKFLOW T3a adds the
//! `fuzz` command: a k-rust-fuzz campaign on kink's own sides that looks for hole values of a
//! template that kill a mutation, printed as a `[[program]]` fragment ([`fuzz`]). CF-16 adds the
//! kill evidence: the first differing cell path of a kill's ends, both values as K text, and each
//! end's computation head and class ([`evidence`]). CF-18 adds the resolve-only check of a
//! mutation list, `check --mutations` ([`check`]), and CF-13 the mutations directory and anchors
//! by a suffix of a label's components ([`mutation`]). CF-02 reads the definition exclusions at
//! admission, prints why each holds with one formatter for every command ([`exclusion`]), and
//! makes `check` fail when a fact known before any mutant runs makes a verdict impossible: a
//! program that cannot be judged on the baseline, or a baseline with no data under
//! `[spec] assume_joined`, whose findings it names with what to do. CF-11 lets a case bind every
//! configuration variable by name, with no program text on a definition without `$PGM`, and
//! from typed inputs a front end's [`InputDecoder`] reads; it refuses a case whose initial
//! configuration has no value on the baseline ([`admit`]).

pub mod admit;
pub mod check;
pub mod cli;
pub mod digest;
pub mod evidence;
pub mod exclusion;
pub mod fuzz;
pub mod fuzz_filter;
pub mod hints;
pub mod manifest;
pub mod memo;
pub mod mutation;
pub mod outcomes;
pub mod pattern;
pub mod query;
pub mod report;
pub mod results;
pub mod search;

pub use admit::{
    AdmittedSpec, CaseInputs, FlowAdmission, InputDecoder, InputFiles, InputSession,
    ProgramAdmission, ProgramExclusion, ProgramInputs, admit, admit_spec,
};
pub use check::{
    CorpusCoverage, Finding, MutationCheck, MutationCheckRow, check_mutations, corpus_coverage,
};
pub use manifest::{Budget, Decoder, FlowManifest, ManifestError, Program, SpecSection};
pub use mutation::{
    EditAction, EditSpec, EditedRule, InvalidMutation, InvalidReason, LabelMatch, Mutation,
    MutationList, ResolvedEdit, ResolvedMutation, RuleText, addressed_rule, label_match, resolve,
    rule_texts,
};

/// The k-rust revision every kink-flow document names as `k_rust_revision`, and `--version`
/// prints: k-rust's build identity (`k_rust::build_identity`, its version and a digest of its
/// sources; GUIDE-USABILITY 5), so two builds of one k-rust version from different sources are
/// told apart, as the fuzz report's `identity.k-rust-revision` tells them. The semantics identity's
/// component `kink.k_rust_revision` and the cache keys keep the version
/// (`kink_native::K_RUST_REVISION`): a key already names the executable (`kink_build`).
#[must_use]
pub fn k_rust_revision() -> String {
    k_rust::build_identity()
}

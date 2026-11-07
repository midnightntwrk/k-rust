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
//! survived specification edits, since replaced by the killer record ([`lock`]: one recorded
//! killer per killed mutation, kept while it still kills, in a `verdicts.lock` the run reads and
//! rewrites). F-12 runs each
//! program's baseline at most once per command; F-13 names the oracle slots of the report,
//! records timings and leaf censuses and lists the rules no mutation targets. F-18 adds the per-input pattern checks: `PATTERNS.toml`, the
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
//!
//! CF-40 makes the manifest, the command layer and the reports a library both front ends use,
//! kink-flow's own command line and the krs front end (`krs kink <verb>`): one manifest schema
//! whose `[spec]` declares a K specification or a KRS package's emitted K ([`ManifestFile`],
//! [`SpecDecl`]), bound to the specification a command runs on ([`ManifestFile::bind`]); one
//! parser of every verb's options ([`FlowCommand::parse`]) and one way to run it
//! ([`dispatch`]), with what a front end adds ([`FrontEnd`]: how next steps spell its commands,
//! the mutations it refused before the engine, an annotation of the document); a visitor over
//! every rule a document names ([`visit_rules`]); and the deterministic rendering of a results or
//! run document ([`verdicts()`]). The engine does not change: a KRS corpus runs as a K corpus
//! over the K its front end emitted.

pub mod admit;
pub mod check;
pub mod cli;
pub mod digest;
pub mod evidence;
pub mod exclusion;
pub mod expect;
pub mod fuzz;
pub mod fuzz_filter;
pub mod lock;
pub mod manifest;
pub mod memo;
pub mod mutation;
pub mod names;
pub mod observed;
pub mod outcomes;
pub mod pattern;
pub mod query;
pub mod report;
pub mod results;
pub mod search;
pub mod verdicts;

pub use admit::{
    AdmittedSpec, BoundProgram, CaseInputs, FlowAdmission, InputDecoder, InputFiles, InputSession,
    ProgramAdmission, ProgramBinding, ProgramExclusion, ProgramInputs, admit, admit_spec,
};
pub use check::{
    CorpusCoverage, Finding, MutationCheck, MutationCheckRow, check_mutations, corpus_coverage,
};
pub use cli::{
    CommandFiles, CommandSpelling, FlowCommand, FrontEnd, KinkFlowSpelling, OutputFormat, Verb,
    dispatch, on_stack,
};
pub use evidence::{EndRenderer, Renderer};
pub use expect::{CheckedExpectation, ExpectationCheck, ExpectationVerdict};
pub use manifest::{
    Budget, Decoder, FlowManifest, KrsSpec, ManifestError, ManifestFile, Program, ResultSection,
    SpecDecl, SpecSection, StopSection,
};
pub use mutation::{
    EditAction, EditSpec, EditedRule, InvalidMutation, InvalidReason, LabelMatch, Mutation,
    MutationList, ResolvedEdit, ResolvedMutation, RuleText, addressed_rule, label_match, resolve,
    rule_texts,
};
pub use names::{RuleRef, visit_rules};
pub use observed::{ResultProjection, ResultRefusal, result_projection};
pub use verdicts::verdicts;

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

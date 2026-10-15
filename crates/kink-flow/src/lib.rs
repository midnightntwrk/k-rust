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
//! the rules no mutation targets.

pub mod admit;
pub mod cli;
pub mod digest;
pub mod hints;
pub mod manifest;
pub mod mutation;
pub mod outcomes;
pub mod report;
pub mod results;
pub mod search;

pub use admit::{AdmittedSpec, FlowAdmission, ProgramAdmission, ProgramInputs, admit, admit_spec};
pub use manifest::{Budget, FlowManifest, ManifestError, Program, SpecSection};
pub use mutation::{
    EditAction, EditSpec, EditedRule, InvalidMutation, InvalidReason, Mutation, MutationList,
    ResolvedMutation, RuleText, resolve, rule_texts,
};

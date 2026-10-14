//! The primary usage flow (flow package, README section 5): an LLM-written concrete
//! corpus for a K specification, described by one `FLOW.toml` corpus manifest.
//!
//! F-02 provides the manifest ([`manifest`]), admission of the specification and its
//! programs through kink-corpus's admission stages ([`admit`]) and the `check` command
//! ([`cli`]). F-03 adds the specification and program digests ([`digest`]) and the result
//! cache with the `results` command ([`results`]). F-04 adds the mutation list and its
//! resolution into one pinned patch per mutation ([`mutation`]). F-05 adds the kill search
//! with its killer cache and the `run` command ([`search`], [`killers`]).

pub mod admit;
pub mod cli;
pub mod digest;
pub mod killers;
pub mod manifest;
pub mod mutation;
pub mod results;
pub mod search;

pub use admit::{AdmittedSpec, FlowAdmission, ProgramAdmission, ProgramInputs, admit, admit_spec};
pub use manifest::{Budget, FlowManifest, ManifestError, Program, SpecSection};
pub use mutation::{
    EditAction, EditSpec, EditedRule, InvalidMutation, InvalidReason, Mutation, MutationList,
    ResolvedMutation, resolve,
};

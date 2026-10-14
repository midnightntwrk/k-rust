//! The primary usage flow (flow package, README section 5): an LLM-written concrete
//! corpus for a K specification, described by one `FLOW.toml` corpus manifest.
//!
//! F-02 provides the manifest ([`manifest`]), admission of the specification and its
//! programs through kink-corpus's admission stages ([`admit`]) and the `check` command
//! ([`cli`]). F-03 adds the specification and program digests ([`digest`]) and the result
//! cache with the `results` command ([`results`]).

pub mod admit;
pub mod cli;
pub mod digest;
pub mod manifest;
pub mod results;

pub use admit::{AdmittedSpec, FlowAdmission, ProgramAdmission, ProgramInputs, admit, admit_spec};
pub use manifest::{Budget, FlowManifest, ManifestError, Program, SpecSection};

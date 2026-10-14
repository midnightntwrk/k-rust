//! The primary usage flow (flow package, README section 5): an LLM-written concrete
//! corpus for a K specification, described by one `FLOW.toml` corpus manifest.
//!
//! F-02 provides the manifest ([`manifest`]), admission of the specification and its
//! programs through kink-corpus's admission stages ([`admit`]) and the `check` command
//! ([`cli`]).

pub mod admit;
pub mod cli;
pub mod manifest;

pub use admit::{AdmittedSpec, FlowAdmission, ProgramAdmission, admit};
pub use manifest::{Budget, FlowManifest, ManifestError, Program, SpecSection};

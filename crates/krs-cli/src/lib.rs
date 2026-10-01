//! Cargo-native orchestration for KRS definition compilation.
//!
//! A production command plans an explicit definition selection, generates and
//! executes a host collector, then sends its canonical descriptor protocol
//! through the shared semantic-theory and Definition-IR pipeline.
//! [`CollectorRequest`] plans a collector that calls a caller-named entry point;
//! production planning shares its package and facet selection.
//! Authored production packages do not implement a collector runtime.
//!
//! The command-line binary renders human-readable diagnostics on stderr by default.
//! `--message-format=json` selects schema-1 envelope lines for located diagnostics and prose lines for unlocated diagnostics and other failures.

mod cargo;
mod command;
mod diagnostic;
mod format;
mod generate;
mod metadata;
mod plan;
mod render;

pub use command::{
    Command, CommandError, CommandKind, CommandOutcome, CommandRequest, MessageFormat,
    execute_command, execute_command_measured, execute_command_reported,
};
pub use diagnostic::{
    DIAGNOSTIC_SCHEMA_VERSION, DiagnosticEnvelope, DiagnosticGeneratedRange, DiagnosticReports,
    DiagnosticSeverity, DiagnosticStage, UnlocatedDiagnostic, diagnostic_envelope,
    translate_k_frontend_diagnostic, translate_native_diagnostic,
};
pub use format::{FormatInput, discover_format_inputs};
pub use generate::{GeneratedCollector, GenerationError};
pub use krs_k_rust::Backend;
pub use metadata::{
    CargoMetadata, MetadataError, MetadataNode, MetadataPackage, MetadataResolve, MetadataTarget,
};
pub use plan::valid_identifier_segment;
pub use plan::{
    CollectorEntrypoint, CollectorPlan, CollectorRequest, CollectorRuntime, DefinitionRequest,
    FacetSelector, KrsCfg, PackageSelector, PlanningError, PlanningErrorKind, RegistrationMode,
    ResolvedFacet, ResolvedPackage,
};

pub use render::DiagnosticSources;

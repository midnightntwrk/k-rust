//! Cargo-native orchestration for KRS definition compilation.
//!
//! A production command plans an explicit definition selection, generates and
//! executes a host collector, then sends its canonical descriptor protocol
//! through the shared semantic-theory and Definition-IR pipeline.
//! [`CollectorRequest`] plans a collector that calls a caller-named entry point;
//! production planning shares its package and facet selection.
//! Authored production packages do not implement a collector runtime.

mod cargo;
mod command;
mod diagnostic;
mod format;
mod generate;
mod metadata;
mod plan;

pub use command::{
    Command, CommandError, CommandKind, CommandOutcome, CommandRequest, execute_command,
    execute_command_measured,
};
pub use diagnostic::{
    DIAGNOSTIC_SCHEMA_VERSION, DiagnosticEnvelope, DiagnosticGeneratedRange, DiagnosticSeverity,
    DiagnosticStage, diagnostic_envelope, translate_k_frontend_diagnostic,
    translate_native_diagnostic,
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

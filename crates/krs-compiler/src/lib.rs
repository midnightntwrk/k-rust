//! Deterministic collection and target-neutral semantic analysis for KRS.
//!
//! This crate owns the sole conversion from process-local
//! [`krs_ir::HostDescriptor`] values to a serializable
//! [`krs_ir::DescriptorBundle`]. Cargo orchestration remains in `krs-cli`, and
//! adapters consume only the stable bundle or later IRs.

mod collect;
mod emit;
mod error;
mod facade;
mod lowering;
mod overlap;
mod reference;
mod semantic;
mod sidecar;
#[cfg(feature = "test-support")]
pub mod testing;

pub use collect::{
    PackageContext, collect_host_descriptors, collect_host_descriptors_with_builtins,
    collect_host_descriptors_with_builtins_timed, run_collector,
};
pub use emit::{DEFINITION_ARTIFACT, EmitError, EmittedK, EmittedSpec, SPEC_ARTIFACT, emit_k};
pub use error::{AnalysisError, AnalysisErrorKind, CollectionError, CollectionErrorKind};
pub use lowering::{LoweredDefinition, LoweringError, lower_semantic_theory};
pub use reference::{
    ReferenceExpansionError, ReferenceSourceError, expand_package_reference_source,
    expand_reference_source,
};
pub use semantic::{
    DescriptorLoweringError, OpenSortAnalysis, analyze_open_sorts, lower_descriptor_bundle,
};
pub use sidecar::{
    GeneratedRange, MappedIdentity, SourceMap, SourceMapEntry, SourceMapNodeKind, SymbolMap,
    SymbolMapEntry,
};

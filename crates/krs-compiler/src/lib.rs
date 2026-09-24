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

pub use collect::{
    PackageContext, collect_host_descriptors, collect_host_descriptors_with_builtins,
};
pub use emit::{EmitError, EmittedK, emit_k};
pub use error::{AnalysisError, AnalysisErrorKind, CollectionError, CollectionErrorKind};
pub use lowering::{LoweredDefinition, LoweringError, lower_semantic_theory};
pub use reference::{ReferenceExpansionError, expand_reference_source};
pub use semantic::{
    DescriptorLoweringError, OpenSortAnalysis, analyze_open_sorts, lower_descriptor_bundle,
};
pub use sidecar::{
    GeneratedRange, MappedIdentity, SourceMap, SourceMapEntry, SourceMapNodeKind, SymbolMap,
    SymbolMapEntry,
};

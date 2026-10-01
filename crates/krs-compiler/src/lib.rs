//! Target-neutral semantic analysis, lowering, and K emission for KRS.
//!
//! Host descriptor collection belongs to `krs-collector`.
//! This crate consumes the stable descriptor bundle
//! and produces the Semantic IR, the Definition IR, and the emitted K.

mod emit;
mod error;
mod lowering;
mod overlap;
mod reference;
mod semantic;
mod sidecar;
#[cfg(feature = "test-support")]
pub mod testing;

pub use emit::{DEFINITION_ARTIFACT, EmitError, EmittedK, EmittedSpec, SPEC_ARTIFACT, emit_k};
pub use error::{AnalysisError, AnalysisErrorKind};
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

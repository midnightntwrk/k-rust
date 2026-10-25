//! Target-neutral semantic analysis, lowering, and K emission for KRS.
//!
//! Host descriptor collection belongs to `krs-collector`.
//! This crate consumes the stable descriptor bundle
//! and produces the Semantic IR, the Definition IR, and the emitted K.

pub mod artifacts;
pub mod capability;
mod console;
mod coverage;
mod emit;
mod equation_domain;
mod error;
mod int_facts;
mod lowering;
mod overlap;
pub mod partition;
mod reference;
mod semantic;
mod sidecar;
mod sort_tests;
mod spec_tokens;
#[cfg(feature = "test-support")]
pub mod testing;

pub use artifacts::*;
pub use coverage::coverage_warnings;
pub use emit::{
    DeclaredCellType, EmitError, EmittedK, EmittedSpec, declared_cell_types,
    definition_module_imports, definition_sentence_source, emit_k, smt_only_function_warnings,
    trusted_claim_warnings,
};
pub use error::{AnalysisError, AnalysisErrorKind};
pub use lowering::{CollisionNamespace, LoweredDefinition, LoweringError, lower_semantic_theory};
pub use reference::{
    ReferenceExpansionError, ReferenceSourceError, expand_package_reference_source,
    expand_reference_source,
};
pub use semantic::{
    DescriptorLoweringError, FreshProblem, ImplicitPresentCell, LexicalProblem, NondetGroupProblem,
    OpenSortAnalysis, OperatorProblem, RawKPolicy, analyze_open_sorts, lower_descriptor_bundle,
    raw_k_policy,
};
pub use sidecar::{
    GeneratedRange, MappedIdentity, SourceMap, SourceMapEntry, SourceMapNodeKind, SymbolMap,
    SymbolMapEntry,
};
pub use sort_tests::sort_test_warnings;

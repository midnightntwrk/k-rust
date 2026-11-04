//! Target-neutral semantic analysis, lowering, and K emission for KRS.
//!
//! Host descriptor collection belongs to `krs-collector`.
//! This crate consumes the stable descriptor bundle
//! and produces the Semantic IR, the Definition IR, and the emitted K.

pub mod artifacts;
pub mod capability;
mod console;
mod coverage;
mod edit_origin;
mod emit;
mod equation_domain;
mod error;
mod int_facts;
mod lowering;
mod mutant_theory;
mod overlap;
pub mod partition;
mod rederivation;
mod reference;
mod semantic;
mod sidecar;
mod sort_tests;
mod spec_tokens;
#[cfg(feature = "test-support")]
pub mod testing;
mod token_values;

pub use artifacts::*;
pub use coverage::coverage_warnings;
pub use edit_origin::{
    AuthoredNodeRef, EditContainer, EditJudgement, InsertedNodeRef, JudgeError, KEdit,
    MutationVerdict, OutsideChange, SentenceJudgement, SentenceVerdict, judge_edits,
};
pub use emit::{
    DeclaredCellType, EmitError, EmittedK, EmittedSpec, SentenceSource, SentenceSources,
    declared_cell_types, definition_module_imports, definition_sentence_source, emit_k,
    smt_only_function_warnings, trusted_claim_warnings,
};
pub use error::{AnalysisError, AnalysisErrorKind};
pub use lowering::{CollisionNamespace, LoweredDefinition, LoweringError, lower_semantic_theory};
pub use mutant_theory::{
    MutantTheory, TheoryChanges, TheoryCheckError, TheoryRefusal, rule_sentence_key,
};
pub use rederivation::{
    IndexedProduction, KLabelIndex, Rederivation, RederivationError, RederiveFailure, Rederived,
    Site,
};
pub use reference::{
    ExpandedFile, PackageExpansion, ReferenceExpansionError, ReferenceSourceError,
    expand_package_reference_source, expand_reference_source, expand_reference_source_naming,
};
pub use semantic::{
    DescriptorLoweringError, FreshProblem, ImplicitPresentCell, LexicalProblem, NondetGroupProblem,
    OpenSortAnalysis, OperatorProblem, RawKPolicy, RetainedLowering, analyze_open_sorts,
    guard_warnings, lower_descriptor_bundle, lower_descriptor_bundle_retained, raw_k_policy,
};
pub use sidecar::{
    GeneratedRange, MappedIdentity, SourceMap, SourceMapEntry, SourceMapNodeKind, SymbolMap,
    SymbolMapEntry,
};
pub use sort_tests::sort_test_warnings;

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
mod guard_families;
mod instance_keys;
mod int_facts;
mod k_reserved;
mod lowering;
mod mutant_theory;
mod never_cools;
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

/// How a message names a leaf cell's generated sort (`IrSortRef::LeafCell`): a Semantic leaf
/// cell is named by its cell id, which carries no name an author wrote.
pub(crate) const LEAF_CELL_SORT: &str = "the sort of a leaf cell";

/// How a message names a collection cell's generated instances sort
/// (`IrSortRef::CellCollection`), named by its cell id as a leaf's is.
pub(crate) const CELL_COLLECTION_SORT: &str = "the sort of a cell collection";

pub use artifacts::*;
pub use coverage::coverage_warnings;
pub use edit_origin::{
    AuthoredNodeRef, EditContainer, EditJudgement, InsertedNodeRef, JudgeError, KEdit,
    MutationVerdict, OutsideChange, SentenceJudgement, SentenceVerdict, judge_edits,
};
pub use emit::{
    DeclaredCellType, EmitError, EmittedK, EmittedPattern, EmittedPatternStep, EmittedSpec,
    PatternSource, PatternVariable, SentenceSource, SentenceSources, declared_cell_types,
    definition_module_imports, definition_sentence_source, emit_k, emit_patterns,
    smt_only_function_warnings, trusted_claim_warnings,
};
pub use error::{AnalysisError, AnalysisErrorKind};
pub use guard_families::{
    AtomKind, AtomOccurrence, FamilyKind, FamilySentence, Flip, FlipOperator, GuardAtom,
    GuardFamily, NotGenerated, NotGeneratedReason, guard_families,
};
pub use lowering::{CollisionNamespace, LoweredDefinition, LoweringError, lower_semantic_theory};
pub use mutant_theory::{
    MutantTheory, TheoryChanges, TheoryCheckError, TheoryRefusal, rule_sentence_key,
};
pub use never_cools::never_cooling_warnings;
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
    guard_warnings, lower_composed_bundle, lower_descriptor_bundle,
    lower_descriptor_bundle_retained, raw_k_policy,
};
pub use sidecar::{
    GeneratedRange, MappedIdentity, SourceMap, SourceMapEntry, SourceMapNodeKind, SymbolMap,
    SymbolMapEntry,
};
pub use sort_tests::sort_test_warnings;

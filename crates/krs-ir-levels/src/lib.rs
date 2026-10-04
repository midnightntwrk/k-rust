//! The Semantic IR and Definition IR: the two target-neutral IR levels between a
//! collected descriptor bundle and emitted K.
//!
//! [`SemanticTheory`] records KRS meaning after descriptor collection and name
//! resolution. [`DefinitionIr`] is the source-level K definition with generated
//! symbol and label names. Both share the level-generic shapes in [`ir_level`]
//! and one set of whole-program validators. [`k_surface`] holds the K-surface
//! facts that the `.k` printer and the k-rust adapter share.
//!
//! Identities, provenance, grammar and state shapes, and the one
//! [`krs_ir::SchemaVersion`] of every serialized contract come from `krs-ir`.
//! The author-facing facade and the front-end crates do not depend on this crate.

pub mod collection_operands;
pub mod definition;
mod display;
pub mod ir_level;
mod ir_validation;
pub mod k_surface;
pub mod semantic;
mod stable_text;

pub use collection_operands::{
    CollectionArityError, ListOperands, MapEntry, MapOperands, SetOperands,
};

pub use definition::{
    ConfigurationSentence, ContextAliasSentence, DefinitionApplicationRef, DefinitionClaim,
    DefinitionClaimBinder, DefinitionIr, DefinitionModule, DefinitionProductionAttribute,
    DefinitionRuleBody, DefinitionRuleCondition, DefinitionRulePriority, DefinitionSentence,
    DefinitionSimplification, DefinitionSimplificationPriority, DefinitionSortRef, DefinitionTerm,
    DefinitionTermKind, DefinitionValidationError, DefinitionVariable, LabelId, LabelIdentity,
    ProductionGroupIdentity, ProductionItem, ProductionSentence, RuleSentence, SubsortSentence,
    SymbolId, SymbolIdentity, SymbolKind, SyntaxSortSentence,
};
pub use ir_level::{
    DefinitionLevel, IrClaim, IrClaimBinder, IrContextAlias, IrLevel, IrRewrite, IrRuleBody,
    IrRuleCondition, IrRulePriority, IrSimplification, IrSimplificationPriority, IrSortRef,
    IrSubsort, IrTerm, IrTermKind, IrVariable, RuleBodyRef, SemanticLevel,
};
pub use semantic::{
    SemanticApplicationRef, SemanticClaim, SemanticClaimBinder, SemanticConfiguration,
    SemanticContextAlias, SemanticModule, SemanticProduction, SemanticProductionAttribute,
    SemanticProductionItem, SemanticRule, SemanticRuleBody, SemanticRuleCondition,
    SemanticRuleLabel, SemanticRulePriority, SemanticSimplification,
    SemanticSimplificationPriority, SemanticSort, SemanticSortRef, SemanticSubsort, SemanticTerm,
    SemanticTermKind, SemanticTheory, SemanticValidationError, SemanticVariable,
};

//! Stable contracts shared by KRS producers, collectors, and compilers.
//!
//! There are two deliberately separate descriptor layers:
//!
//! - [`host`] contains process-local Rust type keys and Cargo lookup hints. It
//!   is never serializable and may temporarily hold an absolute manifest path.
//! - [`bundle`] contains only final stable identities and deterministic data;
//!   host lookup paths cannot enter it through the descriptor types.
//!
//! A host collector is responsible for crossing that boundary. Neither this
//! crate nor serialized bundles depend on a Rust ABI, linker order, `k-rust`,
//! or the KRS command-line interface.

pub mod bundle;
pub mod bytes_token;
mod catalog;
pub mod coordinates;
pub mod definition;
pub mod descriptor_index;
mod detail_macros;
mod display;
mod error_detail;
pub mod generated;
pub mod grammar;
pub mod host;
pub mod identity;
pub mod ir;
pub mod ir_level;
mod ir_validation;
pub mod json;
pub mod k_surface;
pub mod measure;
pub mod provenance;
pub mod provenance_role;
pub mod refined;
pub mod semantic;
pub mod sorted;
pub use refined::{AtLeastTwo, AtLeastTwoError, NonEmpty};
pub mod stable_text;
pub mod stage;
#[cfg(test)]
mod stage_tests;
pub mod state;
#[cfg(any(test, feature = "test-support"))]
pub mod testing;
pub mod transport;
#[doc(hidden)]
pub mod wire;

pub use bundle::{
    ConfigurationSentenceKind, Constructor, ConstructorDescriptor, ConstructorField,
    ConstructorFieldDescriptor, Descriptor, DescriptorBundle, DescriptorDeclaration,
    DescriptorDeclarationError, DescriptorError, DescriptorNodeOrigin, DescriptorPayload,
    DescriptorProvenance, DescriptorProvenanceError, Payload, SentenceKind, SortDescriptor,
    SortPayload,
};
pub use catalog::{
    BuiltinOperationNotation, BuiltinOperationSpec, BuiltinSort, BuiltinSortSpec,
    HookOperationSpec, HookPointConstructor, HookPointSortSource, HookSignature,
    HookSortConstraint,
};
pub use coordinates::{
    ByteRange, CoordinateError, DisplayPath, DisplayPathError, LineIndex, LineIndexError, Position,
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
pub use descriptor_index::{DescriptorIndex, LookupError};
pub use error_detail::{
    Bn128PointSignature, IdentityComponent, IrField, IrIdentityKind, ProductionAttributeFamily,
    SemanticIdentityKind,
};
pub use generated::{GeneratedProductionIdError, GeneratedProductionKind, generated_production_id};
pub use grammar::{
    ApplicationRef, BuiltinOperation, FormatFragment, GrammarProductionItem,
    GrammarProductionItemKind, GrammarShapeError, GroupAssociativity, GroupAssociativitySentence,
    HookOperation, PrecedenceRelation, ProductionAttribute, ProductionContextAliasReference,
    ProductionFieldId, ProductionFieldReference, ProductionGroupId, ProductionResultSort,
    StrictnessKind,
};
pub use host::{
    AnchorPrecision, HostAuthoredAnchor, HostConstructorDescriptor, HostConstructorFieldDescriptor,
    HostDescriptor, HostDescriptorPayload, HostIdentityError, HostItemId, HostPackageKey,
    HostProvenance, HostProvenanceError, HostSortDescriptor, HostSourceAnchor, HostSourcePosition,
    HostTypeKey, HostTypeReference, ProvenanceKey,
};
pub use identity::{
    ExplicitSymbol, IdentityError, ItemKind, PackageId, RustVisibility, Sha256Digest, SourceFileId,
    StableItemId, lower_hex,
};
pub use ir::{IrIdentityError, ModuleId, NodeOrigin, SemanticId, SemanticIdKind, SourceMapKey};
pub use ir_level::{
    DefinitionLevel, IrClaim, IrClaimBinder, IrContextAlias, IrLevel, IrRewrite, IrRuleBody,
    IrRuleCondition, IrRulePriority, IrSimplification, IrSimplificationPriority, IrSortRef,
    IrSubsort, IrTerm, IrTermKind, IrVariable, RuleBodyRef, SemanticLevel,
};
pub use provenance::{
    OriginFrame, OriginStack, OriginStackError, RangedOriginKind, SourceRange, SourceRangeError,
    SourceRangeOverflow, TransformationOriginKind,
};
pub use provenance_role::{ProvenanceRole, RuleRole, RuleSide};
pub use semantic::{
    SemanticApplicationRef, SemanticClaim, SemanticClaimBinder, SemanticConfiguration,
    SemanticContextAlias, SemanticModule, SemanticProduction, SemanticProductionAttribute,
    SemanticProductionItem, SemanticRule, SemanticRuleBody, SemanticRuleCondition,
    SemanticRuleLabel, SemanticRulePriority, SemanticSimplification,
    SemanticSimplificationPriority, SemanticSort, SemanticSortRef, SemanticSubsort, SemanticTerm,
    SemanticTermKind, SemanticTheory, SemanticValidationError, SemanticVariable,
};
pub use stable_text::StableText;
pub use stage::{DescriptorStage, HostStage, RefMap, Stage, WireStage};
pub use state::{
    CellAttribute, CellCollectionType, CellColor, CellContentFrame, CellMultiplicity, CellPost,
    ConfigurationRoot, FixedCell, FixedCellClause, FixedCellContent, FixedCellPattern,
    FixedConfiguration, FixedConfigurationPattern, FixedConfigurationRewrite,
    FixedConfigurationVariable, FixedInitializerCell, FixedInitializerContent, ListOperation,
    MapOperation, SetOperation, StateShapeError, TermMapOperation,
};
pub use transport::configuration::{
    CellWrapper, DescriptorCellCollectionType, DescriptorCellColor, DescriptorCellDeclaration,
    DescriptorCellDeclarationReference, DescriptorCellField, DescriptorCellIdentity,
    DescriptorCellMultiplicity, DescriptorCellName, DescriptorCellReference, DescriptorCellType,
    DescriptorConfigurationDeclaration, DescriptorConfigurationInitializer,
    DescriptorConfigurationRoot, DescriptorConfigurationVariable, DescriptorFixedConfiguration,
    DescriptorInitializerCell, DescriptorInitializerStateTerm, DescriptorKSequenceNotation,
    FixedConfiguration as TransportFixedConfiguration, HostCellDeclaration,
    HostCellDeclarationReference, HostCellField, HostCellIdentity, HostCellReference,
    HostConfigurationDeclaration, HostConfigurationInitializer, HostConfigurationVariable,
    HostFixedConfiguration, HostInitializerCell, HostInitializerStateTerm, ProtocolCellContent,
    ProtocolCellDeclaration, ProtocolCellField, ProtocolConfigurationInitializer,
    ProtocolConfigurationVariable, ProtocolInitializerCell, ProtocolInitializerCellContent,
    ProtocolInitializerStateTerm, ProtocolInitializerTerm, ProtocolKSequence,
    ProtocolKSequenceItem, ProtocolMap, ProtocolMapBody, ProtocolMapItem, StageCellDeclaration,
    StageConfigurationInitializer, StateTransportError,
};
pub use transport::grammar::{
    Arguments, ArgumentsError, CellTermField, DescriptorApplicationHeadClass,
    DescriptorApplicationRef, DescriptorApplicationReference, DescriptorAssociativitySentence,
    DescriptorCellTermField, DescriptorContextAliasReference, DescriptorFieldReference,
    DescriptorFormatFragment, DescriptorGroupReference, DescriptorLexicalPrecedence,
    DescriptorLiteral, DescriptorPrecedenceChain, DescriptorProduction,
    DescriptorProductionAttribute, DescriptorProductionItem, DescriptorProductionOwner,
    DescriptorRuleCondition, DescriptorRuleLabel, DescriptorRulePriority, DescriptorSimplification,
    DescriptorSimplificationPriority, DescriptorSortRef, DescriptorSortReference, DescriptorTerm,
    DescriptorTermArgument, ENUM_VARIANT_DISAMBIGUATOR_PREFIX, GrammarDescriptor,
    GrammarTransportError, HostApplicationIdentity, HostApplicationReference,
    HostApplicationTarget, HostBuiltinRegistry, HostBuiltinRegistryError, HostCellTermField,
    HostContextAliasReference, HostDeclarationIdentity, HostEnumVariantKey,
    HostEnumVariantReference, HostEnumVariantReferenceError, HostGrammarDescriptor,
    HostListOperationRegistration, HostMapOperationRegistration, HostProduction,
    HostProductionAttribute, HostProductionItem, HostProductionOwner, HostRuleCondition,
    HostSetOperationRegistration, HostSortReference, HostStructuredRuleDescriptor, HostTerm,
    HostTermArgument, NamedTermArgument, Production,
    ProductionAttribute as TransportProductionAttribute, ProductionItem as TransportProductionItem,
    ProductionOwner, RuleCondition, StageGrammarDescriptor, StructuredRule,
    StructuredRuleDescriptor, Term, TermArgument, TermArgumentRef, enum_variant_disambiguator,
};
pub use transport::head_rule::{
    DescriptorHeadRule, DescriptorHeadRuleBinding, DescriptorHeadRuleExtra,
    DescriptorHeadRuleResult, HeadRule, HostHeadRule, HostHeadRuleBinding,
    HostHeadRuleCellReference, HostHeadRuleExtra, HostHeadRuleResult, ProtocolHeadRuleBinding,
    ProtocolHeadRuleExtra, ProtocolHeadRuleResult, ResolvedHeadRule,
};
pub use transport::rule::{
    Claim, ClaimBinder, ClaimModality, ConfigurationRule, ContextAlias, DescriptorClaim,
    DescriptorClaimBinder, DescriptorConfigurationReference, DescriptorConfigurationRule,
    DescriptorContextAlias, DescriptorRuleBinding, DescriptorRuleCells, HostClaim, HostClaimBinder,
    HostConfigurationReference, HostConfigurationRule, HostContextAlias, HostRuleBinding,
    HostRuleCells, ProtocolContextAliasBinding, ProtocolContextAliasBindingKind,
    ProtocolRuleBinding, ProtocolRuleBindingKind, ProtocolRuleCell, ProtocolRuleCells,
    ProtocolRuleFrame, ProtocolRuleKSequence, ProtocolRuleKSequenceItem, ProtocolRuleMap,
    ProtocolRuleMapBody, ProtocolRuleMapItem, ProtocolRuleStateTerm,
};

use serde::{Deserialize, Serialize};

/// The one version of every serialized KRS contract: descriptor bundles,
/// Semantic IR, and Definition IR.
///
/// Readers accept exactly [`SchemaVersion::CURRENT`]; there is no reader for
/// an older version. The value changes whenever a serialized shape or a closed
/// catalog it carries (builtin operations, hooks, sorts) changes. It must equal
/// `[schemas] krs_ir` in the repository's `Krs.lock`, which the gates read and a
/// `krs-ir` test checks against this constant.
/// Traceable serialized shapes are pinned by `crates/krs-ir/tests/schema/krs_ir-<version>.json`.
/// Other serialized shapes are pinned by `crates/krs-ir/tests/schema/krs_ir-<version>.samples.json`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(transparent)]
pub struct SchemaVersion(pub u32);

impl SchemaVersion {
    /// The only version this release reads and writes.
    pub const CURRENT: Self = Self(39);
}

impl Default for SchemaVersion {
    fn default() -> Self {
        Self::CURRENT
    }
}

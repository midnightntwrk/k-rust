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
pub mod coordinates;
pub mod definition;
mod display;
pub mod generated;
pub mod grammar;
pub mod host;
pub mod identity;
pub mod ir;
pub mod json;
pub mod measure;
pub mod provenance;
pub mod provenance_role;
pub mod semantic;
pub mod sorted;
pub mod stable_text;
pub mod state;
#[cfg(any(test, feature = "test-support"))]
pub mod testing;
pub mod transport;
#[doc(hidden)]
pub mod wire;

pub use bundle::{
    ConstructorDescriptor, ConstructorFieldDescriptor, Descriptor, DescriptorBundle,
    DescriptorDeclaration, DescriptorDeclarationError, DescriptorNodeOrigin, DescriptorPayload,
    DescriptorProvenance, DescriptorProvenanceError, SentenceKind, SortDescriptor,
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
    StableItemId,
};
pub use ir::{BuiltinSort, IrIdentityError, ModuleId, NodeOrigin, SemanticId, SourceMapKey};
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
pub use state::{
    CellAttribute, CellCollectionType, CellColor, CellContentFrame, CellMultiplicity, CellPost,
    ConfigurationRoot, FixedCell, FixedCellClause, FixedCellContent, FixedCellPattern,
    FixedConfiguration, FixedConfigurationPattern, FixedConfigurationRewrite,
    FixedConfigurationVariable, FixedInitializerCell, FixedInitializerContent, ListOperation,
    MapOperation, SetOperation, StateShapeError,
};
pub use transport::configuration::{
    CellWrapper, DescriptorCellColor, DescriptorCellDeclaration,
    DescriptorCellDeclarationReference, DescriptorCellField, DescriptorCellIdentity,
    DescriptorCellMultiplicity, DescriptorCellName, DescriptorCellReference, DescriptorCellType,
    DescriptorConfigurationDeclaration, DescriptorConfigurationInitializer,
    DescriptorConfigurationRoot, DescriptorConfigurationVariable, DescriptorFixedConfiguration,
    DescriptorInitializerCell, DescriptorInitializerStateTerm, DescriptorKSequenceNotation,
    HostCellDeclaration, HostCellDeclarationReference, HostCellField, HostCellIdentity,
    HostCellReference, HostConfigurationDeclaration, HostConfigurationInitializer,
    HostConfigurationVariable, HostFixedConfiguration, HostInitializerCell,
    HostInitializerStateTerm, ProtocolCellContent, ProtocolCellDeclaration, ProtocolCellField,
    ProtocolConfigurationInitializer, ProtocolConfigurationVariable, ProtocolInitializerCell,
    ProtocolInitializerCellContent, ProtocolInitializerStateTerm, ProtocolInitializerTerm,
    ProtocolKSequence, ProtocolKSequenceItem, ProtocolMap, ProtocolMapBody, ProtocolMapItem,
    StateTransportError,
};
pub use transport::grammar::{
    DescriptorApplicationHeadClass, DescriptorApplicationRef, DescriptorApplicationReference,
    DescriptorAssociativitySentence, DescriptorCellTermField, DescriptorContextAliasReference,
    DescriptorFieldReference, DescriptorFormatFragment, DescriptorGroupReference,
    DescriptorLexicalPrecedence, DescriptorLiteral, DescriptorPrecedenceChain,
    DescriptorProduction, DescriptorProductionAttribute, DescriptorProductionItem,
    DescriptorProductionOwner, DescriptorRuleCondition, DescriptorRuleLabel,
    DescriptorRulePriority, DescriptorSimplification, DescriptorSimplificationPriority,
    DescriptorSortRef, DescriptorSortReference, DescriptorTerm, DescriptorTermArgument,
    ENUM_VARIANT_DISAMBIGUATOR_PREFIX, GrammarDescriptor, GrammarTransportError,
    HostApplicationIdentity, HostApplicationReference, HostApplicationTarget,
    HostBuiltinOperationRegistration, HostBuiltinRegistry, HostBuiltinRegistryError,
    HostBuiltinSortRegistration, HostCellTermField, HostContextAliasReference,
    HostDeclarationIdentity, HostEnumVariantKey, HostEnumVariantReference,
    HostEnumVariantReferenceError, HostGrammarDescriptor, HostListOperationRegistration,
    HostMapOperationRegistration, HostProduction, HostProductionAttribute, HostProductionItem,
    HostProductionOwner, HostRuleCondition, HostSetOperationRegistration, HostSortReference,
    HostStructuredRuleDescriptor, HostTerm, HostTermArgument, StructuredRuleDescriptor,
    enum_variant_disambiguator,
};
pub use transport::head_rule::{
    DescriptorHeadRule, DescriptorHeadRuleBinding, DescriptorHeadRuleExtra,
    DescriptorHeadRuleResult, HostHeadRule, HostHeadRuleBinding, HostHeadRuleCellReference,
    HostHeadRuleExtra, HostHeadRuleResult, ProtocolHeadRuleBinding, ProtocolHeadRuleExtra,
    ProtocolHeadRuleResult,
};
pub use transport::rule::{
    ClaimModality, DescriptorClaim, DescriptorClaimBinder, DescriptorConfigurationReference,
    DescriptorConfigurationRule, DescriptorContextAlias, DescriptorRuleBinding,
    DescriptorRuleCells, HostClaim, HostClaimBinder, HostConfigurationReference,
    HostConfigurationRule, HostContextAlias, HostRuleBinding, HostRuleCells,
    ProtocolContextAliasBinding, ProtocolContextAliasBindingKind, ProtocolRuleBinding,
    ProtocolRuleBindingKind, ProtocolRuleCell, ProtocolRuleCells, ProtocolRuleFrame,
    ProtocolRuleKSequence, ProtocolRuleKSequenceItem, ProtocolRuleMap, ProtocolRuleMapBody,
    ProtocolRuleMapItem, ProtocolRuleStateTerm,
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
    pub const CURRENT: Self = Self(38);
}

impl Default for SchemaVersion {
    fn default() -> Self {
        Self::CURRENT
    }
}

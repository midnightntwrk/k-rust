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
pub mod definition;
pub mod generated;
pub mod grammar;
pub mod head_rule;
pub mod host;
pub mod identity;
pub mod ir;
pub mod protocol_v6;
pub mod protocol_v7;
pub mod provenance;
pub mod semantic;
pub mod state;

pub use bundle::{
    ConstructorDescriptor, ConstructorFieldDescriptor, Descriptor, DescriptorBundle,
    DescriptorDeclaration, DescriptorDeclarationError, DescriptorNodeOrigin, DescriptorPayload,
    DescriptorProvenance, DescriptorProvenanceError, SentenceKind, SortDescriptor,
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
pub use head_rule::{
    DescriptorHeadRule, DescriptorHeadRuleBinding, DescriptorHeadRuleExtra,
    DescriptorHeadRuleResult, HostHeadRule, HostHeadRuleBinding, HostHeadRuleCellReference,
    HostHeadRuleExtra, HostHeadRuleResult, ProtocolHeadRuleBinding, ProtocolHeadRuleExtra,
    ProtocolHeadRuleResult,
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
pub use ir::{
    BuiltinSort, IrIdentityError, IrSchemaVersion, ModuleId, NodeOrigin, SemanticId, SourceMapKey,
};
pub use protocol_v6::{
    DescriptorApplicationHeadClass, DescriptorApplicationRef, DescriptorApplicationReference,
    DescriptorAssociativitySentence, DescriptorCellTermField, DescriptorContextAliasReference,
    DescriptorFieldReference, DescriptorFormatFragment, DescriptorGroupReference,
    DescriptorLexicalPrecedence, DescriptorLiteral, DescriptorPrecedenceChain,
    DescriptorProduction, DescriptorProductionAttribute, DescriptorProductionItem,
    DescriptorProductionOwner, DescriptorRuleCondition, DescriptorRuleLabel,
    DescriptorRulePriority, DescriptorSimplification, DescriptorSimplificationPriority,
    DescriptorSortRef, DescriptorSortReference, DescriptorTerm, DescriptorTermArgument,
    ENUM_VARIANT_DISAMBIGUATOR_PREFIX, GrammarDescriptor, HostApplicationIdentity,
    HostApplicationReference, HostApplicationTarget, HostBuiltinOperationRegistration,
    HostBuiltinRegistry, HostBuiltinRegistryError, HostBuiltinSortRegistration, HostCellTermField,
    HostContextAliasReference, HostDeclarationIdentity, HostEnumVariantKey,
    HostEnumVariantReference, HostEnumVariantReferenceError, HostGrammarDescriptor,
    HostListOperationRegistration, HostMapOperationRegistration, HostProduction,
    HostProductionAttribute, HostProductionItem, HostProductionOwner, HostRuleCondition,
    HostSetOperationRegistration, HostSortReference, HostStructuredRuleDescriptor, HostTerm,
    HostTermArgument, ProtocolV6ShapeError, StructuredRuleDescriptor, enum_variant_disambiguator,
};
pub use protocol_v7::{
    CellWrapper, ClaimModality, DescriptorCellColor, DescriptorCellDeclaration,
    DescriptorCellDeclarationReference, DescriptorCellField, DescriptorCellIdentity,
    DescriptorCellMultiplicity, DescriptorCellName, DescriptorCellReference, DescriptorCellType,
    DescriptorClaim, DescriptorClaimBinder, DescriptorConfigurationDeclaration,
    DescriptorConfigurationInitializer, DescriptorConfigurationReference,
    DescriptorConfigurationRoot, DescriptorConfigurationRule, DescriptorConfigurationVariable,
    DescriptorContextAlias, DescriptorFixedConfiguration, DescriptorInitializerCell,
    DescriptorInitializerStateTerm, DescriptorKSequenceNotation, DescriptorRuleBinding,
    DescriptorRuleCells, HostCellDeclaration, HostCellDeclarationReference, HostCellField,
    HostCellIdentity, HostCellReference, HostClaim, HostClaimBinder, HostConfigurationDeclaration,
    HostConfigurationInitializer, HostConfigurationReference, HostConfigurationRule,
    HostConfigurationVariable, HostContextAlias, HostFixedConfiguration, HostInitializerCell,
    HostInitializerStateTerm, HostRuleBinding, HostRuleCells, ProtocolCellContent,
    ProtocolCellDeclaration, ProtocolCellField, ProtocolConfigurationInitializer,
    ProtocolConfigurationVariable, ProtocolContextAliasBinding, ProtocolContextAliasBindingKind,
    ProtocolInitializerCell, ProtocolInitializerCellContent, ProtocolInitializerStateTerm,
    ProtocolInitializerTerm, ProtocolKSequence, ProtocolKSequenceItem, ProtocolMap,
    ProtocolMapBody, ProtocolMapItem, ProtocolRuleBinding, ProtocolRuleBindingKind,
    ProtocolRuleCell, ProtocolRuleCells, ProtocolRuleFrame, ProtocolRuleKSequence,
    ProtocolRuleKSequenceItem, ProtocolRuleMap, ProtocolRuleMapBody, ProtocolRuleMapItem,
    ProtocolRuleStateTerm, ProtocolV7ShapeError,
};
pub use provenance::{
    OriginFrame, OriginStack, OriginStackError, RangedOriginKind, SourceRange, SourceRangeError,
    TransformationOriginKind,
};
pub use semantic::{
    SemanticApplicationRef, SemanticClaim, SemanticClaimBinder, SemanticConfiguration,
    SemanticContextAlias, SemanticModule, SemanticProduction, SemanticProductionAttribute,
    SemanticProductionItem, SemanticRule, SemanticRuleBody, SemanticRuleCondition,
    SemanticRuleLabel, SemanticRulePriority, SemanticSimplification,
    SemanticSimplificationPriority, SemanticSort, SemanticSortRef, SemanticSubsort, SemanticTerm,
    SemanticTermKind, SemanticTheory, SemanticValidationError, SemanticVariable,
};
pub use state::{
    CellAttribute, CellCollectionType, CellColor, CellContentFrame, CellMultiplicity, CellPost,
    ConfigurationRoot, FixedCell, FixedCellClause, FixedCellContent, FixedCellPattern,
    FixedConfiguration, FixedConfigurationPattern, FixedConfigurationRewrite,
    FixedConfigurationVariable, FixedInitializerCell, FixedInitializerContent, ListOperation,
    MapOperation, SetOperation, StateShapeError,
};

use serde::{Deserialize, Serialize};

/// Version of the collector-to-compiler descriptor protocol.
///
/// This version changes when serialized meaning or canonical encoding changes;
/// it is intentionally independent of the Cargo package version. Protocol v1
/// was the pre-anchor M0 draft whose origin frames required a range at every
/// transformation. Protocol v2 added honest metadata-only transformations but
/// did not carry explicit parser-keyed rule targets. Protocol v3 represented a
/// rule parameter with one synthetic binding and therefore could not preserve
/// zero- or multi-binding patterns. No compatibility reader is provided for
/// v1-v3. Protocol v4 preserved authored rule-binding preorder but discarded
/// every materialized parser-keyed range except a descriptor's primary origin
/// and had no configuration/initializer payload. No compatibility reader is
/// provided for v1-v4. Protocol v5 added one combined configuration descriptor
/// and a generic parser-keyed provenance table. Protocol v6 adds exact
/// host-only builtin registration, typed declared/builtin references,
/// structured after-the-fact grammar sentences, and structured rule terms.
/// Protocol v7 adds Map/Id builtin registration, owner-qualified nominal cell
/// declarations, complete fixed initializer forests, and simultaneous
/// whole-configuration rules with collision-free side-specific provenance.
/// Protocol v9 adds typed object-language Boolean conditions to ordinary and
/// whole-configuration rules.
/// Protocol v10 adds functional-production totality, explicit equation
/// priority metadata, and reversible static alias production/clause metadata,
/// and admits builtin result sorts on constructor declarations that are owned
/// by structured grammar productions.
/// Protocol v12 extends the closed builtin-operation catalog with exact
/// object-language Boolean conjunction. Protocol v13 adds exact Rust
/// declaration visibility and explicit stable-symbol metadata. Protocol v14
/// carries literal constructor-production rustdoc into target emission.
/// Protocol v15 adds alias-safe ordinary Map-operation application heads and
/// retains complete registered map-update terms in readable head rules.
/// Protocol v16 adds exact ordinary fixed-cell patterns and replacements to
/// readable head-rule transport. Protocol v17 adds K's builtin `Bytes` sort,
/// selected length and lookup operations, and exact byte-token transport.
/// Protocol v18 adds K's builtin associative `List` sort and selected unit,
/// item, concatenation, lookup, update, and size operations.
/// Protocol v19 adds K's builtin Euclidean integer-modulus operation.
/// Protocol v20 adds K's native modular-power, logarithm, shift, and bitwise
/// integer operations. Protocol v21 adds empty Bytes. Protocol v22 adds byte
/// update and right padding. Protocol v23 adds Map lookup/key membership and
/// Set terms. Protocol v24 adds repeated cells and readable head conditions.
/// Protocol v25 adds ordered fallback rules. Protocol v26 adds closed typed
/// production hooks. Protocol v27 adds raw SHA-256 and protocol v28 adds raw
/// RIPEMD-160 to the closed hook catalog. Protocol v29 adds ECDSA recovery and
/// protocol v30 adds declared-sort BN128 validity and addition hooks, and
/// protocol v31 adds declared-sort BN128 multiplication. Protocol v32 adds
/// BN128 G2 validity and pairing-product hooks. Protocol v33 adds K's native
/// contiguous List range and multi-element update operations. Protocol v34
/// adds half-open Bytes substring extraction. Protocol v35 adds native List
/// repetition through `LIST.make`.
/// Semantic and Definition IR schema versioning remains independent.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(transparent)]
pub struct ProtocolVersion(pub u32);

impl ProtocolVersion {
    /// The protocol emitted by this release.
    /// Protocol v22 adds byte update and right-padding operations.
    /// Protocol v26 adds closed typed production hooks.
    /// Protocol v27 adds raw SHA-256 to the hook catalog.
    /// Protocol v28 adds raw RIPEMD-160 to the hook catalog.
    /// Protocol v29 adds ECDSA recovery to the hook catalog.
    /// Protocol v30 adds declared-sort BN128 validity and addition hooks.
    /// Protocol v31 adds declared-sort BN128 multiplication.
    /// Protocol v32 adds BN128 G2 validity and pairing-product hooks.
    /// Protocol v33 adds builtin List range and multi-element update operations.
    /// Protocol v34 adds half-open Bytes substring extraction.
    /// Protocol v35 adds native List repetition through `LIST.make`.
    pub const CURRENT: Self = Self(35);
}

impl Default for ProtocolVersion {
    fn default() -> Self {
        Self::CURRENT
    }
}

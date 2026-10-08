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
//!
//! The Semantic IR and Definition IR, which the compiler lowers a bundle into,
//! live in the `krs-ir-levels` crate. The author-facing facade and the
//! front-end crates depend on this crate only.

pub mod bundle;
pub mod bytes_token;
mod catalog;
pub mod coordinates;
pub mod descriptor_index;
mod detail_macros;
mod display;
mod error_detail;
pub mod float_token;
pub mod generated;
pub mod grammar;
pub mod hook_registry;
pub mod host;
pub mod identity;
pub mod ir;
pub mod json;
pub mod measure;
pub mod provenance;
pub mod provenance_role;
pub mod refined;
pub mod sorted;
pub mod string_token;
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
    DescriptorProvenance, DescriptorProvenanceError, PackageSettings, Payload, SentenceKind,
    SortDescriptor, SortPayload,
};
pub use catalog::{
    BuiltinOperationNotation, BuiltinOperationSpec, BuiltinSort, BuiltinSortSpec,
    CollectionApplication, CollectionConcatenation, CollectionNotation, CollectionOperandSort,
    CollectionOperationSpec, CollectionResultSort, FacadeMarker, HookOperationSpec,
    HookPointConstructor, HookPointSortSource, HookSignature, HookSortConstraint, IntLiterals,
    OperationSort, RawKProfile,
};
pub use coordinates::{
    ByteRange, CoordinateError, DisplayPath, DisplayPathError, LineIndex, LineIndexError, Position,
};
pub use descriptor_index::{DescriptorIndex, LookupError};
pub use error_detail::{
    Bn128PointSignature, IdentityComponent, IrField, IrIdentityKind, ProductionAttributeFamily,
    SemanticIdentityKind,
};
pub use generated::{
    GeneratedProductionIdError, GeneratedProductionKind, TokenProductionContent,
    generated_production_id,
};
pub use grammar::{
    ApplicationRef, BuiltinOperation, FormatFragment, GeneratedOperation, GrammarProductionItem,
    GrammarProductionItemKind, GrammarShapeError, GroupAssociativity, GroupAssociativitySentence,
    HookOperation, LayoutSentence, LexicalSentence, PrecedenceRelation, ProductionAttribute,
    ProductionContextAliasReference, ProductionFieldId, ProductionFieldReference,
    ProductionGroupId, ProductionResultSort, RawSentence, RawSentenceKind, SmtFragment,
    StrictnessKind, is_smtlib_simple_symbol,
};
pub use host::{
    AnchorPrecision, HostAuthoredAnchor, HostConstructorDescriptor, HostConstructorFieldDescriptor,
    HostDescriptor, HostDescriptorPayload, HostIdentityError, HostItemId, HostPackageKey,
    HostProvenance, HostProvenanceError, HostProvenanceShapeError, HostRawAnchor,
    HostRawProvenance, HostSortDescriptor, HostSourceAnchor, HostSourcePosition, HostTypeKey,
    HostTypeReference, ProvenanceKey,
};
pub use identity::{
    ExplicitSymbol, IdentityError, ItemKind, PackageId, RustVisibility, Sha256Digest, SourceFileId,
    StableItemId, lower_hex,
};
pub use ir::{IrIdentityError, ModuleId, NodeOrigin, SemanticId, SemanticIdKind, SourceMapKey};
pub use provenance::{
    OriginFrame, OriginStack, OriginStackError, RangedOriginKind, SourceRange, SourceRangeError,
    SourceRangeOverflow, TransformationOriginKind,
};
pub use provenance_role::{ProvenanceRole, RuleRole, RuleSide};
pub use stable_text::StableText;
pub use stage::{DescriptorStage, HostStage, RefMap, Stage, WireStage};
pub use state::{
    CellAttribute, CellClauseKind, CellCollectionType, CellColor, CellContentFrame,
    CellMultiplicity, CellPost, CellStream, ConfigurationRoot, FixedCell, FixedCellClause,
    FixedCellContent, FixedCellPattern, FixedConfiguration, FixedConfigurationPattern,
    FixedConfigurationRewrite, FixedConfigurationVariable, FixedInitializerCell,
    FixedInitializerContent, ListOperation, MapOperation, SetOperation, StateShapeError,
    TermMapOperation,
};
pub use transport::configuration::{
    CellWrapper, DescriptorCellCollectionType, DescriptorCellColor, DescriptorCellDeclaration,
    DescriptorCellDeclarationReference, DescriptorCellExit, DescriptorCellField,
    DescriptorCellIdentity, DescriptorCellMultiplicity, DescriptorCellName,
    DescriptorCellReference, DescriptorCellStream, DescriptorCellType,
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
    DescriptorCellTermField, DescriptorColorEntry, DescriptorContextAliasReference,
    DescriptorFieldReference, DescriptorFormatFragment, DescriptorGroupReference,
    DescriptorLayoutRegex, DescriptorLexical, DescriptorLexicalPrecedence, DescriptorLiteral,
    DescriptorNondetGroup, DescriptorPrecedenceChain, DescriptorProduction,
    DescriptorProductionAttribute, DescriptorProductionItem, DescriptorProductionOwner,
    DescriptorRuleCondition, DescriptorRuleLabel, DescriptorRulePriority, DescriptorSimplification,
    DescriptorSimplificationPriority, DescriptorSmtFragment, DescriptorSortRef,
    DescriptorSortReference, DescriptorTerm, DescriptorTermArgument,
    ENUM_VARIANT_DISAMBIGUATOR_PREFIX, GrammarDescriptor, GrammarTransportError,
    HostApplicationIdentity, HostApplicationReference, HostApplicationTarget, HostBuiltinRegistry,
    HostBuiltinRegistryError, HostCellTermField, HostContextAliasReference,
    HostDeclarationIdentity, HostEnumVariantKey, HostEnumVariantReference,
    HostEnumVariantReferenceError, HostGrammarDescriptor, HostProduction, HostProductionAttribute,
    HostProductionItem, HostProductionOwner, HostRuleCondition, HostSortReference,
    HostStructuredRuleDescriptor, HostTerm, HostTermArgument, HostTypedBinding, NamedTermArgument,
    Production, ProductionAttribute as TransportProductionAttribute,
    ProductionItem as TransportProductionItem, ProductionOwner, RuleCondition, SortTestKind,
    StageGrammarDescriptor, StructuredRule, StructuredRuleDescriptor, Term, TermArgument,
    TermArgumentRef, enum_variant_disambiguator,
};
pub use transport::grammar::{DescriptorTypedBinding, ProtocolTypedBinding};
pub use transport::head_rule::{
    DescriptorHeadRule, DescriptorHeadRuleBinding, DescriptorHeadRuleExtra,
    DescriptorHeadRuleResult, HeadRule, HostHeadRule, HostHeadRuleBinding,
    HostHeadRuleCellReference, HostHeadRuleExtra, HostHeadRuleResult, ProtocolHeadRuleBinding,
    ProtocolHeadRuleExtra, ProtocolHeadRuleHead, ProtocolHeadRuleResult, ResolvedHeadRule,
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
/// The Semantic and Definition IR types live in `krs-ir-levels`, the only crate that sees
/// every serialized type, so it pins the shapes of both crates in one registry: traceable
/// shapes in `crates/krs-ir-levels/tests/schema/krs_ir-<version>.json` and the others in
/// `crates/krs-ir-levels/tests/schema/krs_ir-<version>.samples.json`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(transparent)]
pub struct SchemaVersion(pub u32);

impl SchemaVersion {
    /// The only version this release reads and writes.
    pub const CURRENT: Self = Self(48);
}

impl Default for SchemaVersion {
    fn default() -> Self {
        Self::CURRENT
    }
}

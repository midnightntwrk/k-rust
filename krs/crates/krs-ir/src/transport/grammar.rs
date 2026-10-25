//! Collector transport for typed object grammar and structured rule terms.
//!
//! These are transport types, not semantic IR. Nested nodes carry parser-owned
//! [`ProvenanceKey`] values which the compiler resolves through the enclosing
//! descriptor's provenance table. Rust references remain build-local in the
//! host forms and become declared-or-builtin identities before serialization.

mod term_validation;

use std::any::TypeId;
use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

use crate::Stage;
use serde::{Deserialize, Serialize};

use super::detail::{
    GrammarApplicationReason, GrammarProductionReason, GrammarTermReason, TransportField,
};
use super::keys::{KeyFailure, TermKeying, TermRefusal, WireKeys, collect_term_keys};
use super::rule::ValidationSide;
use crate::host::{HostItemId, HostTypeKey, HostTypeReference};
use crate::stage::{DescriptorStage, HostStage, protocol_shape, stage_shape};
use crate::{
    BuiltinOperation, BuiltinOperator, BuiltinSort, FormatFragment, GroupAssociativity,
    HookOperation, ItemKind, ListNotation, ListOperation, MlConnective, ProductionFieldId,
    ProductionGroupId, ProvenanceKey, ProvenanceRole, RawSentenceKind, SentenceKind, SetOperation,
    SmtFragment, StableItemId, StrictnessKind, TermMapOperation,
};

/// Versioned stable-ID disambiguator prefix for enum constructor variants.
///
/// A variant descriptor uses the variant identifier as `item_name` and
/// `enum:<owning-enum>` as its disambiguator. This distinguishes
/// `Boolean::False` from both a same-module `struct False` and
/// `OtherBoolean::False` without putting `::` into an identity component.
/// The emitted K symbol of a variant combines both: `lowerCamel(Enum)` +
/// `Variant` (`booleanFalse`).
pub const ENUM_VARIANT_DISAMBIGUATOR_PREFIX: &str = "enum:";

/// Derives the stable [`crate::HostItemId`] disambiguator for every descriptor
/// emitted from one `#[k::constructors]` enum.
///
/// The variant identifier itself remains the host item's `item_name`.
///
/// # Errors
///
/// Returns [`HostEnumVariantReferenceError::InvalidOwnerName`] if the enum name
/// is blank or contains a path/filesystem separator.
pub fn enum_variant_disambiguator(
    enum_name: &str,
) -> Result<String, HostEnumVariantReferenceError> {
    if enum_name.trim().is_empty() || enum_name.contains("::") || enum_name.contains(['/', '\\']) {
        return Err(HostEnumVariantReferenceError::InvalidOwnerName(
            enum_name.to_owned(),
        ));
    }
    Ok(format!("{ENUM_VARIANT_DISAMBIGUATOR_PREFIX}{enum_name}"))
}

/// A stable sort reference in collector output.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "sort_source",
    content = "sort",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum DescriptorSortRef {
    /// An authored sort declaration.
    Declared(StableItemId),
    /// A compiler-provided sort from the exact builtin catalog.
    Builtin(BuiltinSort),
    /// The generated sort of a nested `#[k::cell]` declaration, used only by
    /// whole-group rule binders (KF-016).
    Cell(StableItemId),
    /// A sort parameter of the enclosing parametric production, by its
    /// declared name (`S` of `struct Choose<S: ?Sized>`, KF-027). It occurs
    /// only inside that production's own signature.
    Parameter(String),
}

/// One stable sort reference paired with its exact parser-owned origin key.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorSortReference {
    /// Parser role and ordinal of the authored Rust path.
    pub key: ProvenanceKey,
    /// Resolved declared or builtin sort.
    pub sort: DescriptorSortRef,
}

/// A stable application reference in collector output.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "application_source",
    content = "application",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum DescriptorApplicationRef {
    /// An authored constructor production.
    Declared(StableItemId),
    /// A compiler-provided operation from the exact builtin catalog.
    Builtin(BuiltinOperation),
    /// A compiler-provided Map-theory term operation.
    Map(TermMapOperation),
    /// A compiler-provided List-theory term operation.
    List(ListOperation),
    /// A compiler-provided Set-theory term operation.
    Set(SetOperation),
    /// A matching-logic connective of `k::ml` (KF-039): a predicate, never an
    /// object term.
    Ml(MlConnective),
    /// A Rust operator (`a + b`), which denotes the builtin operation of the
    /// domain semantic analysis chooses from its operands' inferred sorts.
    Operator(BuiltinOperator),
    /// One level of bracket list notation (`[head, ..tail]`, `[]`, F6),
    /// which denotes the constructor of the cons list semantic analysis
    /// finds at the position's expected sort.
    ListNotation(ListNotation),
}

/// One stable application reference and its exact authored head location.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorApplicationReference {
    /// Parser role and ordinal of the application head.
    pub key: ProvenanceKey,
    /// Resolved declared or builtin operation.
    pub application: DescriptorApplicationRef,
}

/// A build-local sort reference. The collector resolves its `TypeId` against
/// both authored declarations and the explicit builtin registry.
#[derive(Clone, Debug)]
pub struct HostSortReference {
    /// Parser role and ordinal of the authored sort path.
    pub key: ProvenanceKey,
    /// Rust-resolved type path. Its spelling is diagnostic-only.
    pub target: HostTypeReference,
}

/// A build-local application head resolved through the same exact registry.
#[derive(Clone, Debug)]
pub struct HostApplicationReference {
    /// Parser role and ordinal of the authored application head.
    pub key: ProvenanceKey,
    /// Exact Rust-resolved nominal or enum-variant target.
    pub target: HostApplicationTarget,
}

/// A resolved build-local identity used to join application references to
/// declarations.
///
/// Enum variants are not Rust types. Their identity is therefore the pair of
/// the owning enum's `TypeId` and a distinct marker `TypeId` generated by
/// `#[k::constructors]` for that variant. Neither the enum nor variant spelling
/// participates in the join.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum HostApplicationIdentity {
    /// An ordinary nominal constructor or compiler-provided operation marker.
    Nominal(TypeId),
    /// One exact variant of one exact enum.
    EnumVariant {
        /// Rust identity of the enum which owns the variant.
        enum_type: TypeId,
        /// Rust identity of the generated per-variant marker.
        variant: TypeId,
    },
}

/// Build-local identity exposed by one declared Rust-backed item.
///
/// Sorts, configurations, and struct constructors use `Nominal`. A descriptor
/// emitted for an enum constructor variant uses `EnumVariant`; the owning enum
/// itself is not a constructor declaration.
#[derive(Clone, Copy, Debug)]
pub enum HostDeclarationIdentity {
    /// An ordinary nominal type declaration.
    Nominal(HostTypeKey),
    /// A generated enum-variant declaration key.
    EnumVariant(HostEnumVariantKey),
}

impl HostDeclarationIdentity {
    /// Resolves this declaration to the exact key used by the collector.
    #[must_use]
    pub fn resolve(self) -> HostApplicationIdentity {
        match self {
            Self::Nominal(target) => HostApplicationIdentity::Nominal(target.resolve()),
            Self::EnumVariant(target) => target.resolve(),
        }
    }
}

/// Exact generated declaration key for one Rust enum variant.
///
/// The two key functions are emitted by `#[k::constructors]`. The variant key
/// returns the `TypeId` of a private generated marker, not the discriminant or
/// the variant name.
#[derive(Clone, Copy, Debug)]
pub struct HostEnumVariantKey {
    enum_type: HostTypeKey,
    variant: HostTypeKey,
}

impl HostEnumVariantKey {
    /// Creates the exact owner/variant pair emitted by `#[k::constructors]`.
    #[must_use]
    pub const fn new(enum_type: HostTypeKey, variant: HostTypeKey) -> Self {
        Self { enum_type, variant }
    }

    /// Resolves both generated keys without consulting Rust path spelling.
    #[must_use]
    pub fn resolve(self) -> HostApplicationIdentity {
        HostApplicationIdentity::EnumVariant {
            enum_type: self.enum_type.resolve(),
            variant: self.variant.resolve(),
        }
    }
}

/// Host target for one structured application head.
#[derive(Clone, Debug)]
pub enum HostApplicationTarget {
    /// An ordinary nominal constructor or builtin operation marker.
    Nominal(HostTypeReference),
    /// An enum variant resolved as an exact owner/marker pair.
    EnumVariant(HostEnumVariantReference),
}

impl HostApplicationTarget {
    /// Resolves the exact build-local join key.
    #[must_use]
    pub fn resolve(&self) -> HostApplicationIdentity {
        match self {
            Self::Nominal(target) => HostApplicationIdentity::Nominal(target.key.resolve()),
            Self::EnumVariant(target) => target.resolve(),
        }
    }

    /// Returns the authored path retained only for diagnostics.
    #[must_use]
    pub fn authored_path(&self) -> &str {
        match self {
            Self::Nominal(target) => &target.authored_path,
            Self::EnumVariant(target) => target.authored_path(),
        }
    }
}

/// An alias-safe reference to one enum variant.
///
/// For a qualified application, the author-facing macro splits the path at its
/// final segment and rustc-resolves the prefix as the owning enum. Readable
/// rule heads may instead let rustc infer that enum from an unqualified
/// module-scope glob import. Both routes retain the generated owner and variant
/// keys. A type alias, `use Enum as Alias`, and module/re-export aliases of a
/// qualified owner preserve those two identities.
#[derive(Clone, Debug)]
pub struct HostEnumVariantReference {
    enum_type: HostTypeReference,
    variant: HostTypeKey,
    authored_path: String,
}

impl HostEnumVariantReference {
    /// Creates a qualified enum-variant reference.
    ///
    /// # Errors
    ///
    /// Returns [`HostEnumVariantReferenceError`] for an unqualified path such
    /// as a standalone `use Enum::Variant as V` alias, or when `enum_type` is
    /// not exactly the textual prefix of the full diagnostic path. Standalone
    /// variant aliases are deliberately rejected because they contain no owner
    /// path from which the macro can derive and rustc-check the generated
    /// associated key. Meaning is never recovered from the variant spelling.
    pub fn new(
        enum_type: HostTypeReference,
        variant: HostTypeKey,
        authored_path: impl Into<String>,
    ) -> Result<Self, HostEnumVariantReferenceError> {
        let authored_path = authored_path.into();
        let Some((owner, variant_name)) = authored_path.rsplit_once("::") else {
            return Err(HostEnumVariantReferenceError::UnqualifiedPath(
                authored_path,
            ));
        };
        if owner.trim() != enum_type.authored_path.trim() || variant_name.trim().is_empty() {
            return Err(HostEnumVariantReferenceError::OwnerPathMismatch {
                owner: enum_type.authored_path,
                application: authored_path,
            });
        }
        Ok(Self {
            enum_type,
            variant,
            authored_path,
        })
    }

    /// Resolves the enum owner and generated variant marker as one exact key.
    #[must_use]
    pub fn resolve(&self) -> HostApplicationIdentity {
        HostApplicationIdentity::EnumVariant {
            enum_type: self.enum_type.key.resolve(),
            variant: self.variant.resolve(),
        }
    }

    /// Returns the qualified authored path retained only for diagnostics.
    #[must_use]
    pub fn authored_path(&self) -> &str {
        &self.authored_path
    }

    /// Returns the rustc-resolved owning enum reference.
    #[must_use]
    pub const fn enum_type(&self) -> &HostTypeReference {
        &self.enum_type
    }
}

/// Invalid host enum-variant reference shape.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostEnumVariantReferenceError {
    /// An enum declaration name cannot form a stable disambiguator.
    InvalidOwnerName(String),
    /// The authored application path contains no owning-type prefix.
    UnqualifiedPath(String),
    /// The supplied owner spelling is not the prefix of the application path.
    OwnerPathMismatch {
        /// Supplied owning-type diagnostic path.
        owner: String,
        /// Complete application diagnostic path.
        application: String,
    },
}

impl fmt::Display for HostEnumVariantReferenceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidOwnerName(name) => {
                write!(formatter, "invalid enum constructor owner name `{name}`")
            }
            Self::UnqualifiedPath(path) => write!(
                formatter,
                "enum variant path `{path}` must retain its owning enum path; standalone variant aliases are unsupported"
            ),
            Self::OwnerPathMismatch { owner, application } => write!(
                formatter,
                "enum owner path `{owner}` is not the owner prefix of `{application}`"
            ),
        }
    }
}

impl Error for HostEnumVariantReferenceError {}

/// Complete host-only builtin catalog used for exact `TypeId` joins.
///
/// It is intentionally not serializable. A collector turns references into
/// [`DescriptorSortRef`] and [`DescriptorApplicationRef`] before emitting JSON.
/// Every field is ordered by its catalog's `ALL`, so the registry is complete by construction.
#[derive(Clone, Debug)]
pub struct HostBuiltinRegistry {
    /// Registered sort markers in [`BuiltinSort::ALL`] order.
    pub sorts: [HostTypeKey; BuiltinSort::ALL.len()],
    /// Registered operation markers in [`BuiltinOperation::ALL`] order.
    pub operations: [HostTypeKey; BuiltinOperation::ALL.len()],
    /// Registered ordinary Map operation markers in [`TermMapOperation::ALL`] order.
    pub map_operations: [HostTypeKey; TermMapOperation::ALL.len()],
    /// Registered List operation markers in [`ListOperation::ALL`] order.
    pub list_operations: [HostTypeKey; ListOperation::ALL.len()],
    /// Registered Set operation markers in [`SetOperation::ALL`] order.
    pub set_operations: [HostTypeKey; SetOperation::ALL.len()],
    /// Registered `k::ml` connective markers in [`MlConnective::ALL`] order (KF-039).
    pub ml_connectives: [HostTypeKey; MlConnective::ALL.len()],
    /// Registered operator markers in [`BuiltinOperator::ALL`] order.
    pub operators: [HostTypeKey; BuiltinOperator::ALL.len()],
    /// Registered list-notation markers in [`ListNotation::ALL`] order (F6).
    pub list_notation: [HostTypeKey; ListNotation::ALL.len()],
}

impl HostBuiltinRegistry {
    /// Validates that no Rust marker `TypeId` has two builtin meanings.
    ///
    /// # Errors
    ///
    /// Returns [`HostBuiltinRegistryError::ReusedRustType`] for a reused marker `TypeId`.
    /// Alias paths remain valid because aliases preserve the same `TypeId`; no authored spelling participates in this check.
    pub fn validate(&self) -> Result<(), HostBuiltinRegistryError> {
        let mut rust_ids = BTreeSet::new();
        for target in self
            .sorts
            .iter()
            .chain(&self.operations)
            .chain(&self.map_operations)
            .chain(&self.list_operations)
            .chain(&self.set_operations)
            .chain(&self.ml_connectives)
            .chain(&self.operators)
            .chain(&self.list_notation)
        {
            if !rust_ids.insert(target.resolve()) {
                return Err(HostBuiltinRegistryError::ReusedRustType);
            }
        }
        Ok(())
    }

    /// Resolves one build-local type as a builtin sort.
    #[must_use]
    pub fn resolve_sort(&self, target: TypeId) -> Option<BuiltinSort> {
        BuiltinSort::ALL
            .into_iter()
            .zip(&self.sorts)
            .find(|(_, key)| key.resolve() == target)
            .map(|(sort, _)| sort)
    }

    /// Resolves one build-local type as a builtin operation.
    #[must_use]
    pub fn resolve_operation(&self, target: TypeId) -> Option<BuiltinOperation> {
        BuiltinOperation::ALL
            .into_iter()
            .zip(&self.operations)
            .find(|(_, key)| key.resolve() == target)
            .map(|(operation, _)| operation)
    }

    /// Resolves one build-local type as an ordinary Map operation.
    #[must_use]
    pub fn resolve_map_operation(&self, target: TypeId) -> Option<TermMapOperation> {
        TermMapOperation::ALL
            .into_iter()
            .zip(&self.map_operations)
            .find(|(_, key)| key.resolve() == target)
            .map(|(operation, _)| operation)
    }

    /// Resolves one build-local type as a List operation.
    #[must_use]
    pub fn resolve_list_operation(&self, target: TypeId) -> Option<ListOperation> {
        ListOperation::ALL
            .into_iter()
            .zip(&self.list_operations)
            .find(|(_, key)| key.resolve() == target)
            .map(|(operation, _)| operation)
    }

    /// Resolves one build-local type as a Set operation.
    #[must_use]
    pub fn resolve_set_operation(&self, target: TypeId) -> Option<SetOperation> {
        SetOperation::ALL
            .into_iter()
            .zip(&self.set_operations)
            .find(|(_, key)| key.resolve() == target)
            .map(|(operation, _)| operation)
    }

    /// Resolves one build-local type as a `k::ml` connective (KF-039).
    #[must_use]
    pub fn resolve_ml_connective(&self, target: TypeId) -> Option<MlConnective> {
        MlConnective::ALL
            .into_iter()
            .zip(&self.ml_connectives)
            .find(|(_, key)| key.resolve() == target)
            .map(|(connective, _)| connective)
    }

    /// Resolves one build-local type as an operator.
    #[must_use]
    pub fn resolve_operator(&self, target: TypeId) -> Option<BuiltinOperator> {
        BuiltinOperator::ALL
            .into_iter()
            .zip(&self.operators)
            .find(|(_, key)| key.resolve() == target)
            .map(|(operator, _)| operator)
    }

    /// Resolves one build-local type as a list-notation marker (F6).
    #[must_use]
    pub fn resolve_list_notation(&self, target: TypeId) -> Option<ListNotation> {
        ListNotation::ALL
            .into_iter()
            .zip(&self.list_notation)
            .find(|(_, key)| key.resolve() == target)
            .map(|(notation, _)| notation)
    }
}

/// Invalid host builtin catalog.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostBuiltinRegistryError {
    /// One Rust marker type was assigned two meanings.
    ReusedRustType,
}

impl fmt::Display for HostBuiltinRegistryError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReusedRustType => {
                formatter.write_str("one Rust marker type has multiple builtin meanings")
            }
        }
    }
}

impl Error for HostBuiltinRegistryError {}

/// One field/group reference with its independently retained authored origin.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorFieldReference {
    /// Parser role and ordinal of the field name.
    pub key: ProvenanceKey,
    /// Stable production field identity.
    pub field: ProductionFieldId,
}

/// Stable typed reference to one authored context-alias declaration.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorContextAliasReference {
    /// Exact `using` occurrence provenance.
    pub key: ProvenanceKey,
    /// Resolved context-alias declaration identity.
    pub alias: StableItemId,
}

/// Host counterpart of [`DescriptorContextAliasReference`].
#[derive(Clone, Debug)]
pub struct HostContextAliasReference {
    /// Exact `using` occurrence provenance.
    pub key: ProvenanceKey,
    /// Build-local package/module/item identity.
    pub alias: HostItemId,
}

/// One production-group occurrence with exact provenance.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorGroupReference {
    /// Parser role and ordinal of this occurrence.
    pub key: ProvenanceKey,
    /// Stable group identity.
    pub group: ProductionGroupId,
}

/// One format fragment with exact parser provenance.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorFormatFragment {
    /// Parser role and ordinal of this fragment.
    pub key: ProvenanceKey,
    /// Typed format meaning.
    pub fragment: FormatFragment,
}

/// Optional token lexical precedence with its independently retained origin.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorLexicalPrecedence {
    /// Exact integer-literal provenance.
    pub key: ProvenanceKey,
    /// Pinned K lexical `prec` value.
    pub value: u32,
}

stage_shape! {
    /// Ordered grammar item in a structured production.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "DescriptorProductionItem",
        bound(
            serialize = "S::Sort: Serialize",
            deserialize = "S::Sort: Deserialize<'de>"
        ),
        tag = "item_kind", rename_all = "snake_case",
        deny_unknown_fields
    )]
    pub enum ProductionItem<S: Stage> {
        /// Literal concrete-syntax terminal.
        Terminal {
            /// Exact item provenance.
            key: ProvenanceKey => [keep],
            /// Nonempty terminal text.
            text: String => [keep],
        },
        /// Named nonterminal with a typed sort.
        NonTerminal {
            /// Exact ordered-item provenance.
            key: ProvenanceKey => [keep],
            /// Exact placeholder/name provenance.
            field_key: ProvenanceKey => [keep],
            /// Constructor field-declaration provenance, absent only for a compiler-owned bracket placeholder.
            #[serde(skip_serializing_if = "S::skip_none")]
            declaration_key: Option<ProvenanceKey> => [keep],
            /// Stable field identity.
            field: ProductionFieldId => [keep],
            /// Typed field sort and its Rust type-path provenance.
            sort: Box<S::Sort> => [box sort],
        },
        /// K-compatible regex terminal.
        RegexTerminal {
            /// Exact regex-literal provenance.
            key: ProvenanceKey => [keep],
            /// Optional negative lookbehind guard.
            #[serde(skip_serializing_if = "S::skip_none")]
            precede_regex: Option<String> => [keep],
            /// Nonempty central regex.
            regex: String => [keep],
            /// Optional negative lookahead guard.
            #[serde(skip_serializing_if = "S::skip_none")]
            follow_regex: Option<String> => [keep],
        },
    }
}

/// Descriptor-stage form of [`ProductionItem`].
pub type DescriptorProductionItem = ProductionItem<DescriptorStage>;

/// Host-stage form of [`ProductionItem`].
pub type HostProductionItem = ProductionItem<HostStage>;

stage_shape! {
    /// Classified production metadata transported without raw K attributes.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "DescriptorProductionAttribute",
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize, S::ContextAlias: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::ContextAlias: Deserialize<'de>"
        ),
        tag = "attribute_kind", rename_all = "snake_case",
        deny_unknown_fields
    )]
    pub enum ProductionAttribute<S: Stage> {
        /// Literal production documentation carried from Rust rustdoc.
        Documentation {
            /// Documentation-line provenance.
            key: ProvenanceKey => [keep],
            /// One normalized documentation line.
            text: String => [keep],
        },
        /// Marks a production as a K function.
        Function {
            /// Function-marker provenance.
            key: ProvenanceKey => [keep],
        },
        /// Marks a functional production as total.
        Total {
            /// Totality-marker provenance.
            key: ProvenanceKey => [keep],
        },
        /// Selects one closed backend hook identity.
        Hook {
            /// Hook-selector provenance.
            key: ProvenanceKey => [keep],
            /// Closed hook identity.
            operation: HookOperation => [keep],
        },
        /// Marks a constructor production as a reversible static alias.
        Alias {
            /// Alias-marker provenance.
            key: ProvenanceKey => [keep],
            /// Provenance of `recursive` (K's `alias-rec`), when written;
            /// omitted when absent in every stage, so plain aliases keep
            /// their encoding.
            #[serde(default, skip_serializing_if = "Option::is_none")]
            recursive: Option<ProvenanceKey> => [keep],
        },
        /// Regex token production and optional lexical precedence.
        Token {
            /// Token-attribute provenance.
            key: ProvenanceKey => [keep],
            /// Optional lexical priority.
            #[serde(skip_serializing_if = "S::skip_none")]
            lexical_precedence: Option<DescriptorLexicalPrecedence> => [keep],
        },
        /// Nominal precedence/associativity group membership.
        Group {
            /// Group identity and authored location.
            reference: DescriptorGroupReference => [keep],
        },
        /// Syntax-only bracket marker.
        Bracket {
            /// Bracket-attribute provenance.
            key: ProvenanceKey => [keep],
        },
        /// Typed parser preference.
        Avoid {
            /// Avoid-attribute provenance.
            key: ProvenanceKey => [keep],
        },
        /// Structured unparse format.
        Format {
            /// Format-attribute provenance.
            key: ProvenanceKey => [keep],
            /// Ordered typed fragments with independent origins.
            fragments: Vec<DescriptorFormatFragment> => [keep],
        },
        /// Strict or sequentially strict evaluation metadata.
        Strictness {
            /// Strictness-attribute provenance.
            key: ProvenanceKey => [keep],
            /// Strict or sequentially strict strategy.
            kind: StrictnessKind => [keep],
            /// Optional selected context-alias declaration.
            #[serde(skip_serializing_if = "S::skip_none")]
            using: Option<S::ContextAlias> => [option context_alias],
            /// Named fields in authored order.
            fields: Vec<DescriptorFieldReference> => [keep],
            /// Explicit result-predicate sort.
            result_sort: Box<S::Sort> => [box sort],
        },
        /// `internal`: usable in rules but not program syntax.
        Internal {
            /// Flag provenance.
            key: ProvenanceKey => [keep],
        },
        /// `program`: asserts that the production is program syntax.
        Program {
            /// Flag provenance.
            key: ProvenanceKey => [keep],
        },
        /// One colour for every printed terminal.
        Color {
            /// Colour-literal provenance.
            key: ProvenanceKey => [keep],
            /// Colour name.
            value: String => [keep],
        },
        /// One colour per printed terminal and per `%c`.
        Colors {
            /// Colour-list provenance.
            key: ProvenanceKey => [keep],
            /// Colour names with their own literal provenance, in source order.
            values: Vec<DescriptorColorEntry> => [keep],
        },
        /// Typed parser preference, the counterpart of `avoid`.
        Prefer {
            /// Prefer-attribute provenance.
            key: ProvenanceKey => [keep],
        },
        /// Membership in the overload family of the target production.
        Overload {
            /// Target constructor identity and the target path's location.
            target: S::Application => [application],
        },
        /// Memoization hint of a function production.
        Memo {
            /// Memo-flag provenance.
            key: ProvenanceKey => [keep],
        },
        /// The cons production of a `#[k::syntax_list]` enum (KF-020).
        ListCons {
            /// `#[k::syntax_list]` attribute provenance.
            key: ProvenanceKey => [keep],
            /// Separator-literal provenance.
            separator_key: ProvenanceKey => [keep],
            /// Separator terminal; empty for a list without separator.
            separator: String => [keep],
            /// `non_empty` flag provenance, present for K's `NeList`.
            non_empty: Option<ProvenanceKey> => [keep],
            /// The terminator variant of the same enum.
            terminator: S::Application => [application],
        },
        /// The terminator production of a `#[k::syntax_list]` enum (KF-020).
        ListTerminator {
            /// The cons variant of the same enum, keyed at the list attribute.
            cons: S::Application => [application],
        },
        /// The cons constructor of a `#[k::cons_list]` constructors enum
        /// (F6): bracket list notation at its sort denotes it and `empty`.
        /// It is notation only, so it reaches neither the semantic IR nor K.
        ConsList {
            /// `#[k::cons_list]` attribute provenance.
            key: ProvenanceKey => [keep],
            /// The empty constructor of the same enum, keyed at the attribute.
            empty: S::Application => [application],
        },
        /// Quoted K hook name, checked against the pinned hook registry only.
        RawHook {
            /// Hook-string provenance.
            key: ProvenanceKey => [keep],
            /// Hook namespace before the first `.`.
            namespace: String => [keep],
            /// Hook name after the first `.`.
            name: String => [keep],
        },
        /// Fresh-value generator of its result sort (`fresh_generator`, KF-022).
        FreshGenerator {
            /// Flag provenance.
            key: ProvenanceKey => [keep],
        },
        /// Uninterpreted SMT-LIB symbol of a function (`smtlib`, KF-044).
        Smtlib {
            /// Symbol-string provenance.
            key: ProvenanceKey => [keep],
            /// SMT-LIB simple symbol.
            symbol: String => [keep],
        },
        /// SMT-LIB template of a function (`smt_hook`, KF-044).
        SmtHook {
            /// Template-string provenance.
            key: ProvenanceKey => [keep],
            /// Template fragments; each field fragment keeps its placeholder provenance.
            template: Vec<DescriptorSmtFragment> => [keep],
        },
        /// A total function's intended coverage gap (`underspecified = ".."`).
        Underspecified {
            /// Reason-string provenance.
            key: ProvenanceKey => [keep],
            /// The stated reason, nonempty.
            reason: String => [keep],
        },
        /// Marks a constructor production as a one-way static desugar (K's `macro`).
        Desugar {
            /// Desugar-marker provenance.
            key: ProvenanceKey => [keep],
            /// Provenance of `recursive` (K's `macro-rec`), when written;
            /// omitted when absent in every stage.
            #[serde(default, skip_serializing_if = "Option::is_none")]
            recursive: Option<ProvenanceKey> => [keep],
        },
    }
}

/// One `smt_hook` template fragment; a field fragment carries its placeholder provenance.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorSmtFragment {
    /// Placeholder provenance, present exactly for a field fragment.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub key: Option<ProvenanceKey>,
    /// Typed fragment.
    pub fragment: SmtFragment,
}

/// One provenance-bearing entry of a production's `colors` list.
#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorColorEntry {
    /// Colour-literal provenance.
    pub key: ProvenanceKey,
    /// Colour name.
    pub value: String,
}

/// Descriptor-stage form of [`ProductionAttribute`].
pub type DescriptorProductionAttribute = ProductionAttribute<DescriptorStage>;

/// Host-stage form of [`ProductionAttribute`].
pub type HostProductionAttribute = ProductionAttribute<HostStage>;

stage_shape! {
    /// Ownership of a semantic production.
    /// Generated token/bracket identities are deliberately absent; the compiler derives them from the grammar descriptor.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "DescriptorProductionOwner",
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>"
        ),
        tag = "production_owner",
        rename_all = "snake_case",
        deny_unknown_fields
    )]
    pub enum ProductionOwner<S: Stage> {
        /// Grammar belonging to an authored constructor declaration.
        Constructor {
            /// Authored constructor identity and location.
            constructor: S::Application => [application],
        },
        /// Compiler-owned token production for an authored sort.
        TokenSort {
            /// Authored token sort and location.
            sort: S::Sort => [sort],
        },
        /// Compiler-owned bracket production attached to an authored sort.
        BracketSort {
            /// Authored bracket sort and location.
            sort: S::Sort => [sort],
        },
    }
}

/// Descriptor-stage form of [`ProductionOwner`].
pub type DescriptorProductionOwner = ProductionOwner<DescriptorStage>;

/// Host-stage form of [`ProductionOwner`].
pub type HostProductionOwner = ProductionOwner<HostStage>;

stage_shape! {
    /// One complete typed production extension.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "DescriptorProduction",
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize, S::ContextAlias: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::ContextAlias: Deserialize<'de>"
        ),
        deny_unknown_fields
    )]
    pub struct Production<S: Stage> {
        /// Production-level authored provenance.
        pub key: ProvenanceKey => [keep],
        /// Explicit syntax-template literal provenance.
        /// This is present for authored constructor templates and absent for default/token/bracket productions.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub template_key: Option<ProvenanceKey> => [keep],
        /// Declared or compiler-generated production ownership.
        pub owner: ProductionOwner<S> => [nested],
        /// Typed production result sort and its authored sort-path provenance.
        pub result_sort: S::Sort => [sort],
        /// Ordered classified grammar items.
        pub items: Vec<ProductionItem<S>> => [vec nested],
        /// Classified metadata only.
        pub attributes: Vec<ProductionAttribute<S>> => [vec nested],
        /// Sort parameters of a parametric production (`struct Choose<S: ?Sized>`,
        /// K's `syntax {S}`), in declaration order; each resolves to
        /// [`DescriptorSortRef::Parameter`] (KF-027). Empty for every other production.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        pub parameters: Vec<S::Sort> => [vec sort],
    }
    map_order: [key, template_key, owner, parameters, items, attributes, result_sort];
}

/// Descriptor-stage form of [`Production`].
pub type DescriptorProduction = Production<DescriptorStage>;

/// Host-stage form of [`Production`].
pub type HostProduction = Production<HostStage>;

/// One direct precedence edge with every group occurrence retained.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields, try_from = "DescriptorPrecedenceChainWire")]
pub struct DescriptorPrecedenceChain {
    /// Complete precedence-chain provenance.
    pub key: ProvenanceKey,
    /// Groups from tightest to loosest binding.
    /// The compiler expands adjacent pairs into target-neutral precedence edges.
    pub groups: crate::AtLeastTwo<DescriptorGroupReference>,
}

/// Plain wire shape of an ordered precedence chain.
#[doc(hidden)]
#[derive(Deserialize)]
#[serde(rename = "DescriptorPrecedenceChain", deny_unknown_fields)]
pub struct DescriptorPrecedenceChainWire {
    key: ProvenanceKey,
    groups: Vec<DescriptorGroupReference>,
}

impl DescriptorPrecedenceChain {
    /// Creates an ordered precedence chain with at least two groups.
    /// # Errors
    /// Returns the existing empty-collection or short-chain error.
    pub fn new(
        key: ProvenanceKey,
        groups: Vec<DescriptorGroupReference>,
    ) -> Result<Self, GrammarTransportError> {
        if groups.is_empty() {
            return Err(GrammarTransportError::EmptyCollection(
                TransportField::PrecedenceGroups,
            ));
        }
        let groups = groups.try_into().map_err(|_| {
            GrammarTransportError::InvalidProduction(GrammarProductionReason::ShortPrecedenceChain)
        })?;
        Ok(Self { key, groups })
    }
}

impl TryFrom<DescriptorPrecedenceChainWire> for DescriptorPrecedenceChain {
    type Error = GrammarTransportError;
    fn try_from(value: DescriptorPrecedenceChainWire) -> Result<Self, Self::Error> {
        Self::new(value.key, value.groups)
    }
}

/// One associativity sentence with every group occurrence retained.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorAssociativitySentence {
    /// Associativity-sentence provenance.
    pub key: ProvenanceKey,
    /// Left, right, or non-associative strategy.
    pub associativity: GroupAssociativity,
    /// Group occurrences in authored order.
    pub groups: Vec<DescriptorGroupReference>,
}

/// One `Name = r".."` entry of a `k::lexical!` block.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorLexical {
    /// Entry provenance (`lexical_declaration`).
    pub key: ProvenanceKey,
    /// Lexical name, referenced from regexes as `{Name}`.
    pub name: String,
    /// Regex-literal provenance (`lexical_regex`).
    pub regex_key: ProvenanceKey,
    /// Unescaped regex text.
    pub regex: String,
}

/// One regex of a `k::layout!` block.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorLayoutRegex {
    /// Regex-literal provenance (`layout_regex`).
    pub key: ProvenanceKey,
    /// Unescaped regex text.
    pub regex: String,
}

stage_shape! {
    /// Typed after-the-fact object-grammar sentence.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "GrammarDescriptor",
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize, S::ContextAlias: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::ContextAlias: Deserialize<'de>"
        ),
        tag = "grammar_kind",
        content = "grammar",
        rename_all = "snake_case",
        deny_unknown_fields
    )]
    pub enum StageGrammarDescriptor<S: Stage> {
        /// Constructor, token, or bracket production.
        Production(value: Production<S> => [nested]),
        /// Explicit direct subsort relation, including builtin endpoints.
        Subsort {
            /// Subsort-declaration provenance.
            key: ProvenanceKey => [keep],
            /// Smaller sort and authored path.
            subsort: S::Sort => [sort],
            /// Larger sort and authored path.
            supersort: S::Sort => [sort],
        },
        /// One macro declaration containing one or more precedence edges.
        Precedence {
            /// Complete macro-invocation provenance.
            key: ProvenanceKey => [keep],
            /// Direct partial-order edges.
            chains: Vec<DescriptorPrecedenceChain> => [keep],
        },
        /// One macro declaration containing one or more associativity sentences.
        Associativity {
            /// Complete macro-invocation provenance.
            key: ProvenanceKey => [keep],
            /// Typed associativity sentences.
            sentences: Vec<DescriptorAssociativitySentence> => [keep],
        },
        /// The stacked token productions of one `#[k::token]` carrier, in
        /// attribute order: one production per attribute, all on one sort.
        Tokens {
            /// One `regex` or `terminal` token production per attribute.
            productions: Vec<Production<S>> => [vec nested],
        },
        /// The named regex fragments of one `k::lexical!` block, in source order.
        Lexical {
            /// One entry per `Name = r".."`.
            lexicals: Vec<DescriptorLexical> => [keep],
        },
        /// The layout regexes of one `k::layout!` block, in source order.
        Layout {
            /// One entry per regex literal.
            regexes: Vec<DescriptorLayoutRegex> => [keep],
        },
        /// One `k::raw_k!` sentence: unchecked K text, opaque to KRS, placed
        /// in the package's semantics module.
        RawSentence {
            /// Text-literal provenance.
            key: ProvenanceKey => [keep],
            /// The sentence keyword the text starts with.
            kind: RawSentenceKind => [keep],
            /// The complete K sentence text.
            text: String => [keep],
            /// One-based line of the `raw_k!` invocation, for the emitted comment.
            line: u32 => [keep],
            /// One-based column of the `raw_k!` invocation.
            column: u32 => [keep],
        },
        /// One `#[k::spec_module]` inline module (KF-041): an author K proof
        /// module. Its Rust module path is the descriptor identity's module path.
        SpecModule {
            /// Module-name provenance (`spec_module_declaration`).
            key: ProvenanceKey => [keep],
            /// The authored `name = ".."`, when present.
            name: Option<DescriptorSpecModuleName> => [keep],
            /// The `imports = [..]` paths, in authored order.
            imports: Vec<DescriptorModuleImport> => [keep],
        },
    }
}

/// The `name = ".."` of a `#[k::spec_module]`.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorSpecModuleName {
    /// Literal provenance (`spec_module_name`).
    pub key: ProvenanceKey,
    /// The K module name.
    pub value: String,
}

/// One `imports = [..]` path of a `#[k::spec_module]`, resolved by the
/// semantic layer: `crate`, a dependency crate root, or another spec module.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorModuleImport {
    /// Path provenance (`spec_module_import`).
    pub key: ProvenanceKey,
    /// The authored Rust path, `::`-separated, with a leading `::` when authored.
    pub path: String,
}

/// Descriptor-stage form of [`StageGrammarDescriptor`].
pub type GrammarDescriptor = StageGrammarDescriptor<DescriptorStage>;

/// Host-stage form of [`StageGrammarDescriptor`].
pub type HostGrammarDescriptor = StageGrammarDescriptor<HostStage>;

/// Literal kinds admitted by the explicit Rust term grammar.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "literal_kind",
    content = "value",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum DescriptorLiteral {
    /// The canonical K `Int` token: `0` or an optionally negative decimal
    /// without leading zeros (`0|-?[1-9][0-9]*`), so `-0` and `007` are rejected.
    Int(String),
    /// Rust Boolean literal.
    Bool(bool),
    /// The value of a Rust string literal, a K `String` of code points in
    /// U+0000..=U+00FF; its token is [`crate::string_token::encode`] of it.
    String(String),
    /// The canonical K `Float` token of a Rust float literal or `f32::`/`f64::`
    /// constant ([`crate::float_token`]), such as `0.1f`, `-0.0`, or `NaN`.
    Float(String),
}

/// Rust syntax class of a term node which resolves semantically to an
/// application.
///
/// A unit constructor written as `Boolean::False` is a bare Rust path and has
/// `BareReference` provenance even though its target-neutral meaning is a
/// zero-argument constructor application. Calls, tuple constructors, and
/// record constructors use `Applied`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DescriptorApplicationHeadClass {
    /// Call, tuple, or record application syntax.
    Applied,
    /// Qualified bare path naming a unit constructor.
    BareReference,
}

stage_shape! {
    /// One argument of a structured application.
    /// Positional tuple/call syntax and named record syntax remain distinct so ordinary Rust field reordering never changes K argument meaning.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "DescriptorTermArgument",
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize, S::Nominal: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::Nominal: Deserialize<'de>"
        ),
        tag = "argument_kind", rename_all = "snake_case",
        deny_unknown_fields
    )]
    pub enum TermArgument<S: Stage> {
        /// Argument from tuple/call syntax, interpreted in source order.
        Positional {
            /// Structured argument value.
            value: Box<Term<S>> => [box nested],
        },
        /// Argument from record syntax, interpreted by field identity.
        Named {
            /// Exact authored record-field name provenance.
            key: ProvenanceKey => [keep],
            /// Stable constructor-field identity.
            field: ProductionFieldId => [keep],
            /// Structured field value.
            value: Box<Term<S>> => [box nested],
        },
    }
}

stage_shape! {
    /// One named argument with its field identity and provenance.
    #[derive(Clone, Debug)]
    pub struct NamedTermArgument<S: Stage> {
        /// Exact authored field provenance.
        pub key: ProvenanceKey => [keep],
        /// Stable constructor-field identity.
        pub field: ProductionFieldId => [keep],
        /// Structured field value.
        pub value: Box<Term<S>> => [box nested],
    }
}

stage_shape! {
    /// Homogeneous positional or named application arguments.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        try_from = "Vec<TermArgument<S>>", into = "Vec<TermArgument<S>>",
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize, S::Nominal: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::Nominal: Deserialize<'de>"
        )
    )]
    pub enum Arguments<S: Stage> {
        /// Ordered positional values.
        Positional(values: Vec<Box<Term<S>>> => [vec box nested]),
        /// Ordered named values.
        Named(values: crate::NonEmpty<NamedTermArgument<S>> => [nonempty nested]),
    }
}

impl<S: Stage> Default for Arguments<S> {
    fn default() -> Self {
        Self::Positional(Vec::new())
    }
}

impl<S: Stage> TryFrom<Vec<TermArgument<S>>> for Arguments<S> {
    type Error = ArgumentsError;
    fn try_from(values: Vec<TermArgument<S>>) -> Result<Self, Self::Error> {
        let mut positional = Vec::new();
        let mut named = Vec::new();
        for value in values {
            match value {
                TermArgument::Positional { value } => positional.push(value),
                TermArgument::Named { key, field, value } => {
                    named.push(NamedTermArgument { key, field, value });
                }
            }
            if !positional.is_empty() && !named.is_empty() {
                return Err(ArgumentsError::MixedForms);
            }
        }
        Ok(if named.is_empty() {
            Self::Positional(positional)
        } else {
            Self::named(named)
        })
    }
}

impl<S: Stage> From<Arguments<S>> for Vec<TermArgument<S>> {
    fn from(value: Arguments<S>) -> Self {
        match value {
            Arguments::Positional(values) => values
                .into_iter()
                .map(|value| TermArgument::Positional { value })
                .collect(),
            Arguments::Named(values) => values
                .into_iter()
                .map(
                    |NamedTermArgument { key, field, value }| TermArgument::Named {
                        key,
                        field,
                        value,
                    },
                )
                .collect(),
        }
    }
}

/// A borrowed argument in a homogeneous argument collection.
#[derive(Clone, Copy, Debug)]
pub enum TermArgumentRef<'a, S: Stage> {
    /// Ordered positional value.
    Positional {
        /// Structured argument value.
        value: &'a Term<S>,
    },
    /// Value with authored field metadata.
    Named {
        /// Authored field provenance.
        key: &'a ProvenanceKey,
        /// Stable field identity.
        field: &'a ProductionFieldId,
        /// Structured field value.
        value: &'a Term<S>,
    },
}

/// Borrowed iteration over homogeneous arguments.
pub enum ArgumentIter<'a, S: Stage> {
    /// Positional traversal.
    Positional(std::slice::Iter<'a, Box<Term<S>>>),
    /// Named traversal.
    Named(<&'a crate::NonEmpty<NamedTermArgument<S>> as IntoIterator>::IntoIter),
}

impl<'a, S: Stage> Iterator for ArgumentIter<'a, S> {
    type Item = TermArgumentRef<'a, S>;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Positional(values) => values
                .next()
                .map(|value| TermArgumentRef::Positional { value }),
            Self::Named(values) => values.next().map(|value| TermArgumentRef::Named {
                key: &value.key,
                field: &value.field,
                value: &value.value,
            }),
        }
    }
}

/// Homogeneous argument forms cannot be mixed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArgumentsError {
    /// Positional and named values occur in the same application.
    MixedForms,
}

impl fmt::Display for ArgumentsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("positional and named arguments are mixed")
    }
}

impl Error for ArgumentsError {}

impl<S: Stage> Arguments<S> {
    /// Creates named arguments, canonicalizing an empty list to positional form.
    #[must_use]
    pub fn named(values: Vec<NamedTermArgument<S>>) -> Self {
        let mut values = values.into_iter();
        match values.next() {
            Some(first) => Self::Named(crate::NonEmpty::new(first, values.collect())),
            None => Self::default(),
        }
    }

    /// Returns the number of authored arguments.
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            Self::Positional(values) => values.len(),
            Self::Named(values) => values.len(),
        }
    }
    /// Reports whether there are no authored arguments.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Reports whether the arguments have field identities.
    #[must_use]
    pub fn is_named(&self) -> bool {
        matches!(self, Self::Named(_))
    }
    /// Traverses arguments in source order.
    #[must_use]
    pub fn iter(&self) -> ArgumentIter<'_, S> {
        match self {
            Self::Positional(values) => ArgumentIter::Positional(values.iter()),
            Self::Named(values) => ArgumentIter::Named(values.into_iter()),
        }
    }
}

impl<'a, S: Stage> IntoIterator for &'a Arguments<S> {
    type Item = TermArgumentRef<'a, S>;
    type IntoIter = ArgumentIter<'a, S>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Descriptor-stage form of [`TermArgument`].
pub type DescriptorTermArgument = TermArgument<DescriptorStage>;

/// Host-stage form of [`TermArgument`].
pub type HostTermArgument = TermArgument<HostStage>;

stage_shape! {
    /// One named child of a compiler-owned complete cell term.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "DescriptorCellTermField",
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize, S::Nominal: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::Nominal: Deserialize<'de>"
        ),
        deny_unknown_fields
    )]
    pub struct CellTermField<S: Stage> {
        /// Exact authored child-field provenance.
        pub key: ProvenanceKey => [keep],
        /// Stable Rust field identity within the nominal cell declaration.
        pub field: ProductionFieldId => [keep],
        /// Structured child value, before the generated child-cell wrapper.
        pub value: Box<Term<S>> => [box nested],
    }
}

/// Descriptor-stage form of [`CellTermField`].
pub type DescriptorCellTermField = CellTermField<DescriptorStage>;

fn deserialize_or_bool_arguments<'de, T, D>(
    deserializer: D,
) -> Result<crate::AtLeastTwo<T>, D::Error>
where
    T: Deserialize<'de>,
    D: serde::Deserializer<'de>,
{
    crate::AtLeastTwo::try_from(Vec::<T>::deserialize(deserializer)?)
        .map_err(|_| serde::de::Error::custom("or_bool requires at least two operands"))
}

fn deserialize_or_alternatives<'de, D, T>(deserializer: D) -> Result<crate::AtLeastTwo<T>, D::Error>
where
    T: Deserialize<'de>,
    D: serde::Deserializer<'de>,
{
    crate::AtLeastTwo::try_from(Vec::<T>::deserialize(deserializer)?)
        .map_err(|_| serde::de::Error::custom("an or-pattern requires at least two alternatives"))
}

/// Host-stage form of [`CellTermField`].
pub type HostCellTermField = CellTermField<HostStage>;

stage_shape! {
    /// A fully structured rule term with stage-specific references.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "DescriptorTerm",
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize, S::Nominal: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::Nominal: Deserialize<'de>"
        ),
        tag = "term_kind", rename_all = "snake_case",
        deny_unknown_fields
    )]
    pub enum Term<S: Stage> {
        /// Bound variable reference.
        Variable {
            /// Exact bare-reference provenance.
            key: ProvenanceKey => [keep],
            /// Compact named-path provenance retained for source-map continuity.
            path_key: ProvenanceKey => [keep],
            /// Bound Rust identifier.
            name: String => [keep],
        },
        /// Declared constructor or builtin operation application.
        Application {
            /// Syntactic head class used to select exact parser provenance.
            head_class: DescriptorApplicationHeadClass => [keep],
            /// Typed application head and provenance.
            reference: S::Application => [application],
            /// Compact named-path provenance retained for source-map continuity.
            path_key: ProvenanceKey => [keep],
            /// Positional or named arguments.
            /// One application may not mix forms.
            arguments: Arguments<S> => [nested],
            /// Turbofish sort arguments of a parametric production head
            /// (`Choose::<Int> { .. }`), in parameter order (KF-027); empty
            /// when none was written.
            #[serde(default, skip_serializing_if = "Vec::is_empty")]
            instance: Vec<S::Sort> => [vec sort],
            /// The base of a record update `Ctor { f: e, ..t }` (F5), a
            /// variable: the record is the one matched as `t @ Ctor { .. }`
            /// with the listed fields replaced. Absent for every other
            /// application.
            #[serde(default, skip_serializing_if = "Option::is_none")]
            update: Option<Box<Term<S>>> => [option box nested],
            /// Whether a record pattern ends in `..`, `Ctor { f: p, .. }`:
            /// the fields it does not name are unconstrained, all of them
            /// for `Ctor { .. }`, whose arguments are empty.
            #[serde(default, skip_serializing_if = "std::ops::Not::not")]
            open: bool => [keep],
        },
        /// Exact Int/Bool literal.
        Literal {
            /// Exact literal provenance.
            key: ProvenanceKey => [keep],
            /// Typed literal payload.
            literal: DescriptorLiteral => [keep],
        },
        /// Anonymous subject-pattern wildcard.
        /// This is rejected on rule results.
        Wildcard {
            /// Exact authored underscore provenance.
            key: ProvenanceKey => [keep],
        },
        /// Compiler-owned domain token whose sort is intrinsic.
        BuiltinToken {
            /// Exact literal provenance.
            key: ProvenanceKey => [keep],
            /// Closed builtin token sort.
            sort: BuiltinSort => [keep],
            /// Complete validated payload.
            value: String => [keep],
        },
        /// One typed anonymous-variable occurrence.
        Anonymous {
            /// Complete occurrence provenance.
            key: ProvenanceKey => [keep],
            /// Exact authored sort occurrence.
            sort: S::Sort => [sort],
            /// Exact display-spelling provenance.
            spelling_key: ProvenanceKey => [keep],
            /// Display spelling retained for K/native anonymous handling.
            spelling: String => [keep],
        },
        /// Compiler-owned associative object-Bool disjunction.
        OrBool {
            /// Complete macro-shell provenance.
            key: ProvenanceKey => [keep],
            /// Ordered operands, at least two.
            #[serde(deserialize_with = "deserialize_or_bool_arguments")]
            arguments: crate::AtLeastTwo<Term<S>> => [at_least_two nested],
        },
        /// Complete nominal parent-cell term constructed by `fragment!`.
        Cell {
            /// Complete macro-shell provenance.
            key: ProvenanceKey => [keep],
            /// Compact named-path provenance of the cell's declaration path;
            /// a cell value's names its head's node and carries its key.
            path_key: ProvenanceKey => [keep],
            /// Exact nominal `#[k::cell]` declaration reference.
            declaration: S::Nominal => [nominal],
            /// Authored child values; semantic lowering validates completeness and order.
            fields: Vec<CellTermField<S>> => [vec nested],
            /// Whether a pattern ends in `..`: the children it does not name
            /// are unconstrained.
            #[serde(default, skip_serializing_if = "std::ops::Not::not")]
            open: bool => [keep],
            /// The base of a group update `Group { f: e, ..t }` (F5), a
            /// variable: the children it does not list are the matched
            /// group `t`'s.
            #[serde(default, skip_serializing_if = "Option::is_none")]
            update: Option<Box<Term<S>>> => [option box nested],
        },
        /// `k::lexeme!(Sort, "text")`: one token of a user token sort, never
        /// re-lexed.
        Lexeme {
            /// Exact text-literal provenance.
            key: ProvenanceKey => [keep],
            /// Exact authored token-sort occurrence.
            sort: S::Sort => [sort],
            /// Nonempty token text.
            text: String => [keep],
        },
        /// `k::is!(Sort, t)` or `k::project!(Sort, t)`: K's generated sort
        /// predicate `isSort(T)` or projection `{T}:>Sort`.
        SortTest {
            /// Complete macro-shell provenance.
            key: ProvenanceKey => [keep],
            /// Predicate or projection.
            kind: SortTestKind => [keep],
            /// Exact authored sort occurrence.
            sort: S::Sort => [sort],
            /// The tested or projected term.
            operand: Box<Term<S>> => [box nested],
        },
        /// `name @ pattern` in a left-hand side: K's `( PATTERN #as Name:Sort )`.
        As {
            /// Complete `name @ pattern` provenance.
            key: ProvenanceKey => [keep],
            /// Exact alias-identifier provenance.
            binding_key: ProvenanceKey => [keep],
            /// The alias, a rule binding.
            name: String => [keep],
            /// The aliased subpattern.
            pattern: Box<Term<S>> => [box nested],
        },
        /// `A | B | ..` in a left-hand side: K's `( A #Or B #Or .. )`.
        Or {
            /// Complete or-pattern provenance.
            key: ProvenanceKey => [keep],
            /// Ordered alternatives, at least two.
            #[serde(deserialize_with = "deserialize_or_alternatives")]
            alternatives: crate::AtLeastTwo<Term<S>> => [at_least_two nested],
        },
        /// `k::matches!(subject, pattern)` in a result or condition: K's
        /// `( PATTERN :=K SUBJECT )`, a Bool. The pattern's names are local
        /// binders, visible only inside it.
        Matches {
            /// Complete macro-shell provenance.
            key: ProvenanceKey => [keep],
            /// The tested term.
            subject: Box<Term<S>> => [box nested],
            /// The pattern, a left-hand-side-shaped term.
            pattern: Box<Term<S>> => [box nested],
        },
        /// One `let pattern = value;` statement of a term block and the rest
        /// of the block: K's `( #let PATTERN = VALUE #in BODY )`. The
        /// pattern's names are local binders, visible in the pattern and the
        /// body only.
        Let {
            /// The `let` statement's provenance.
            key: ProvenanceKey => [keep],
            /// The pattern, a left-hand-side-shaped term.
            pattern: Box<Term<S>> => [box nested],
            /// The exact authored sort of `let name: Sort = value;`.
            sort: Option<S::Sort> => [option sort],
            /// The matched term, outside the pattern's scope.
            value: Box<Term<S>> => [box nested],
            /// The rest of the block: the next `let`, or the result term.
            body: Box<Term<S>> => [box nested],
        },
        /// `|x: S| p`, the one argument of `ml::exists` (KF-039): K's
        /// `#Exists X:S . P`. The binder is local to the body (BIND-1).
        Closure {
            /// Complete closure provenance.
            key: ProvenanceKey => [keep],
            /// Exact binder-identifier provenance.
            binder_key: ProvenanceKey => [keep],
            /// The quantified binder.
            name: String => [keep],
            /// The binder's exact authored sort.
            sort: S::Sort => [sort],
            /// The quantified predicate.
            body: Box<Term<S>> => [box nested],
        },
        /// `k::rewrite!(from => to)` in the subject of a single-body rule
        /// (KF-011): K's local `( FROM => TO )`. The rest of the subject is
        /// the unchanged frame; `from` binds like the subject, `to` only uses
        /// its bindings.
        Rewrite {
            /// Complete macro-shell provenance.
            key: ProvenanceKey => [keep],
            /// The left side's provenance.
            from_key: ProvenanceKey => [keep],
            /// The right side's provenance.
            to_key: ProvenanceKey => [keep],
            /// The left side, a pattern.
            from: Box<Term<S>> => [box nested],
            /// The right side; `None` is `()`, K's `.K`, admitted only as a
            /// whole K-sequence item (the item is removed).
            #[serde(default, skip_serializing_if = "Option::is_none")]
            to: Option<Box<Term<S>>> => [option box nested],
        },
    }
    pre_map: term;
}

/// Which generated sort operation a [`Term::SortTest`] denotes.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SortTestKind {
    /// `k::is!`: K's total predicate `isSort(T)`.
    Predicate,
    /// `k::project!`: K's partial projection `{T}:>Sort`.
    Projection,
}

/// Descriptor-stage form of [`Term`].
pub type DescriptorTerm = Term<DescriptorStage>;

/// Host-stage form of [`Term`].
pub type HostTerm = Term<HostStage>;

/// Optional explicit K rule label and its authored literal provenance.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorRuleLabel {
    /// Exact authored label-literal provenance.
    pub key: ProvenanceKey,
    /// Exact emitted K rule-label spelling.
    pub name: String,
}

stage_shape! {
    /// One typed object-language Boolean rule condition and its complete payload provenance.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "DescriptorRuleCondition",
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize, S::Nominal: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::Nominal: Deserialize<'de>"
        ),
        deny_unknown_fields
    )]
    pub struct RuleCondition<S: Stage> {
        /// Complete `#[k::requires(...)]` payload provenance.
        pub key: ProvenanceKey => [keep],
        /// Structured object-language term whose inferred sort must be `Bool`.
        pub term: Term<S> => [nested],
    }
}

/// Descriptor-stage form of [`RuleCondition`].
pub type DescriptorRuleCondition = RuleCondition<DescriptorStage>;

/// Host-stage form of [`RuleCondition`].
pub type HostRuleCondition = RuleCondition<HostStage>;

/// One explicit K rule priority with exact authoring provenance.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorRulePriority {
    /// Priority-literal provenance.
    pub key: ProvenanceKey,
    /// Effective K rule priority.
    pub value: u32,
}

impl DescriptorRulePriority {
    /// The priority K gives an `owise` rule or equation.
    pub const OWISE: u32 = 200;
    /// The largest rule priority k-rust ranks.
    pub const MAX: u32 = 254;

    /// The provenance role this priority must carry on a sentence of `kind`,
    /// or `None` when the kind has no priority or the pair is invalid.
    ///
    /// A transition carries `owise` (value 200, [`ProvenanceRole::RuleOwise`])
    /// or `priority = N` ([`ProvenanceRole::RulePriority`], `N <= 254`); an
    /// equation carries `priority = N` ([`ProvenanceRole::EquationPriority`])
    /// or `owise` (value 200, [`ProvenanceRole::EquationOwise`]).
    #[must_use]
    pub fn role_for(&self, kind: SentenceKind) -> Option<ProvenanceRole> {
        let role = self.key.role();
        let valid = match kind {
            SentenceKind::Transition => {
                (role == ProvenanceRole::RuleOwise && self.value == Self::OWISE)
                    || (role == ProvenanceRole::RulePriority && self.value <= Self::MAX)
            }
            SentenceKind::Equation => {
                role == ProvenanceRole::EquationPriority
                    || (role == ProvenanceRole::EquationOwise && self.value == Self::OWISE)
            }
            _ => false,
        };
        (valid && self.key.ordinal() == 0).then_some(role)
    }
}

/// The `nondet = group` key of a transition: check-only, never emitted.
///
/// Rules of one group may overlap at one priority; the overlap check (F2)
/// skips their pairs and validates the group instead. Groups are scoped to
/// the package that declares the rules.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorNondetGroup {
    /// Group-identifier provenance.
    pub key: ProvenanceKey,
    /// Authored group identifier.
    pub name: String,
}

impl DescriptorNondetGroup {
    /// Whether the key is the one `nondet` anchor and the name a nonempty identifier.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.key.role() == ProvenanceRole::RuleNondetGroup
            && self.key.ordinal() == 0
            && self
                .name
                .chars()
                .next()
                .is_some_and(|first| first == '_' || first.is_alphabetic())
            && self
                .name
                .chars()
                .all(|character| character == '_' || character.is_alphanumeric())
    }
}

/// Optional simplification metadata, kept distinct from equation priority.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorSimplification {
    /// Marker provenance (the attributed function identifier).
    pub key: ProvenanceKey,
    /// Optional ordering hint and its exact literal provenance.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub priority: Option<DescriptorSimplificationPriority>,
    /// Optional `concrete`, `symbolic`, and `smt_lemma` keys (KF-043).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub restriction: Option<DescriptorMatchRestriction>,
}

/// Keys of an equation beyond its priority (KF-043).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorEquationAttributes {
    /// The equation's `concrete`, `symbolic`, and `smt_lemma` keys.
    pub restriction: DescriptorMatchRestriction,
}

/// `concrete`, `symbolic`, and `smt_lemma` keys of an equation or simplification (KF-043).
///
/// At least one key is present; absent keys are omitted.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorMatchRestriction {
    /// `concrete` (every binder) or `concrete(x, ..)`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub concrete: Option<DescriptorRestriction>,
    /// `symbolic` (every binder) or `symbolic(x, ..)`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub symbolic: Option<DescriptorRestriction>,
    /// Provenance of the bare `smt_lemma` flag.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub smt_lemma: Option<ProvenanceKey>,
}

/// One `concrete` or `symbolic` key: bare (no variables) or a list of left-hand binders.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorRestriction {
    /// Provenance of the key identifier.
    pub key: ProvenanceKey,
    /// Named binders in authored order; empty for the bare key.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub variables: Vec<DescriptorRestrictionVariable>,
}

/// One left-hand binder named by `concrete(..)` or `symbolic(..)`.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorRestrictionVariable {
    /// Exact identifier provenance.
    pub key: ProvenanceKey,
    /// The binder's Rust name.
    pub name: String,
}

/// `unbound_variables = [x, _]` of a desugar clause (KF-046): right-hand
/// names the left-hand side does not bind, K's `unboundVariables`.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorUnboundVariables {
    /// Provenance of the `unbound_variables` key identifier.
    pub key: ProvenanceKey,
    /// Listed names in authored order; `_` stands for every result wildcard.
    pub variables: Vec<DescriptorUnboundVariable>,
}

/// One name, or `_`, listed in `unbound_variables = [..]`.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorUnboundVariable {
    /// Exact identifier provenance.
    pub key: ProvenanceKey,
    /// The Rust name, or `_` for the result's wildcards.
    pub name: String,
}

impl DescriptorUnboundVariable {
    /// The entry that stands for every wildcard of the result.
    pub const WILDCARD: &str = "_";

    /// Whether this entry is `_`.
    #[must_use]
    pub fn is_wildcard(&self) -> bool {
        self.name == Self::WILDCARD
    }
}

impl DescriptorUnboundVariables {
    /// Whether `_` is listed, which admits wildcards in the result.
    #[must_use]
    pub fn lists_wildcard(&self) -> bool {
        self.variables
            .iter()
            .any(DescriptorUnboundVariable::is_wildcard)
    }

    /// The listed names other than `_`.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.variables
            .iter()
            .filter(|variable| !variable.is_wildcard())
            .map(|variable| variable.name.as_str())
    }

    /// Validates key roles and nonblank distinct entries that the subject
    /// does not bind.
    fn validate(
        &self,
        bindings: &BTreeSet<String>,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    ) -> Result<(), GrammarTransportError> {
        let invalid =
            || GrammarTransportError::InvalidTerm(GrammarTermReason::InvalidUnboundVariables);
        require_key(&self.key, provenance)?;
        if self.key.role() != ProvenanceRole::UnboundVariables
            || self.key.ordinal() != 0
            || self.variables.is_empty()
        {
            return Err(invalid());
        }
        let mut names = BTreeSet::new();
        for variable in &self.variables {
            require_key(&variable.key, provenance)?;
            if variable.key.role() != ProvenanceRole::UnboundVariable
                || variable.name.trim().is_empty()
                || bindings.contains(&variable.name)
                || !names.insert(variable.name.as_str())
            {
                return Err(invalid());
            }
        }
        Ok(())
    }

    fn collect_wire_keys(&self, keys: &mut WireKeys) -> Result<(), GrammarTransportError> {
        keys.define(&self.key, ProvenanceRole::UnboundVariables)?;
        for variable in &self.variables {
            keys.define(&variable.key, ProvenanceRole::UnboundVariable)?;
        }
        Ok(())
    }
}

impl DescriptorMatchRestriction {
    /// Whether no key is present.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.concrete.is_none() && self.symbolic.is_none() && self.smt_lemma.is_none()
    }

    /// Validates key roles: one key each, and nonblank distinct variable
    /// names per list.
    fn validate(
        &self,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    ) -> Result<(), GrammarTransportError> {
        let invalid =
            || GrammarTransportError::InvalidTerm(GrammarTermReason::InvalidMatchRestriction);
        if self.is_empty() {
            return Err(invalid());
        }
        for (restriction, role) in [
            (&self.concrete, ProvenanceRole::RestrictionConcrete),
            (&self.symbolic, ProvenanceRole::RestrictionSymbolic),
        ] {
            let Some(restriction) = restriction else {
                continue;
            };
            require_key(&restriction.key, provenance)?;
            if restriction.key.role() != role || restriction.key.ordinal() != 0 {
                return Err(invalid());
            }
            let mut names = BTreeSet::new();
            for variable in &restriction.variables {
                require_key(&variable.key, provenance)?;
                if variable.key.role() != ProvenanceRole::RestrictionVariable
                    || variable.name.trim().is_empty()
                    || !names.insert(variable.name.as_str())
                {
                    return Err(invalid());
                }
            }
        }
        if let Some(smt_lemma) = &self.smt_lemma {
            require_key(smt_lemma, provenance)?;
            if smt_lemma.role() != ProvenanceRole::SmtLemma || smt_lemma.ordinal() != 0 {
                return Err(invalid());
            }
        }
        Ok(())
    }

    fn collect_wire_keys(&self, keys: &mut WireKeys) -> Result<(), GrammarTransportError> {
        for (restriction, role) in [
            (&self.concrete, ProvenanceRole::RestrictionConcrete),
            (&self.symbolic, ProvenanceRole::RestrictionSymbolic),
        ] {
            let Some(restriction) = restriction else {
                continue;
            };
            keys.define(&restriction.key, role)?;
            for variable in &restriction.variables {
                keys.define(&variable.key, ProvenanceRole::RestrictionVariable)?;
            }
        }
        if let Some(smt_lemma) = &self.smt_lemma {
            keys.define(smt_lemma, ProvenanceRole::SmtLemma)?;
        }
        Ok(())
    }
}

/// One numeric simplification ordering hint.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorSimplificationPriority {
    /// Exact integer-literal provenance.
    pub key: ProvenanceKey,
    /// Authored hint.
    pub value: u32,
}

impl DescriptorRuleLabel {
    /// Whether this is a portable explicit K rule label.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        valid_rule_label_name(&self.name)
    }
}

protocol_shape! {
    /// One declared typed binder `name: Sort` of a term-shaped rule fn (KF-009).
    ///
    /// A term sentence declares no binders or every subject binder, in
    /// first-occurrence order (the binder-list contract); the declared sort is
    /// the binder's sort, possibly narrower than its occurrences need.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolTypedBinding<S => sort_map => U> {
        /// Exact `name: Sort` parameter provenance.
        pub key: ProvenanceKey => [keep],
        /// Binding name, one of the rule's subject bindings.
        pub name: String => [keep],
        /// Exact authored sort reference.
        pub sort: S => [sort_map],
    }
}

/// Host typed binder awaiting stable sort resolution.
pub type HostTypedBinding = ProtocolTypedBinding<HostSortReference>;
/// Stable typed binder.
pub type DescriptorTypedBinding = ProtocolTypedBinding<DescriptorSortReference>;

stage_shape! {
    /// Structured relational sentence.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "StructuredRuleDescriptor",
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize, S::Nominal: Serialize, S::Configuration: Serialize, S::Cell: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::Nominal: Deserialize<'de>, S::Configuration: Deserialize<'de>, S::Cell: Deserialize<'de>"
        ),
        deny_unknown_fields
    )]
    pub struct StructuredRule<S: Stage> {
        /// Explicit relational sentence meaning.
        pub sentence_kind: SentenceKind => [keep],
        /// Optional explicit emitted K label.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub label: Option<DescriptorRuleLabel> => [keep],
        /// Optional object-language Boolean applicability condition.
        #[serde(skip_serializing_if = "S::skip_none")]
        #[serde(default)]
        pub requires: Option<RuleCondition<S>> => [option nested],
        /// Optional explicit equation or ordered-fallback priority.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub priority: Option<DescriptorRulePriority> => [keep],
        /// Simplifier classification and optional hint.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub simplification: Option<DescriptorSimplification> => [keep],
        /// Optional check-only nondeterminism group of a transition.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub nondet: Option<DescriptorNondetGroup> => [keep],
        /// Provenance of the `anywhere` marker of a term-shaped transition.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub anywhere: Option<ProvenanceKey> => [keep],
        /// Complete subject-pattern provenance.
        pub pattern_key: ProvenanceKey => [keep],
        /// Declared typed binders in subject first-occurrence order; empty
        /// when the fn declares none and every binder sort is inferred.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        pub typed_bindings: Vec<ProtocolTypedBinding<S::Sort>> => [vec protocol sort],
        /// Complete result-expression provenance; absent exactly for a
        /// single-body rule (KF-011).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub result_key: Option<ProvenanceKey> => [keep],
        /// Exact authored subject sort.
        pub subject_sort: S::Sort => [sort],
        /// Exact authored result sort; absent exactly for a single-body rule.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub result_sort: Option<S::Sort> => [option sort],
        /// Bound names in deterministic pattern preorder.
        pub bindings: Vec<String> => [keep],
        /// Structured left pattern; in a single-body rule it contains the
        /// `k::rewrite!` islands that mark what changes.
        pub subject: Term<S> => [nested],
        /// Structured right result; absent exactly for a single-body rule.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub result: Option<Term<S>> => [option nested],
        /// Result-scoped existential binders of a transition (`#[k::exists]`).
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        pub existentials: Vec<crate::transport::rule::ClaimBinder<S>> => [vec nested],
        /// Optional object-Bool postcondition of a transition (`#[k::ensures]`).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub ensures: Option<RuleCondition<S>> => [option nested],
        /// Fresh binders of a transition (`#[k::fresh]`), K's `!X`: values the step draws from the generated counter.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        pub fresh: Vec<crate::transport::rule::ClaimBinder<S>> => [vec nested],
        /// Keys of an equation beyond its priority: `concrete`, `symbolic`, `smt_lemma` (KF-043).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub equation: Option<DescriptorEquationAttributes> => [keep],
        /// `unbound_variables = [..]` of a desugar clause (KF-046).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub unbound_variables: Option<DescriptorUnboundVariables> => [keep],
        /// The read-only configuration context of an equation (KF-025), K's
        /// `[[ .. ]]` cells.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub function_context: Option<crate::transport::rule::FunctionContext<S>> => [option nested],
        /// Whether the subject and result types are `ml::Predicate`: a
        /// predicate simplification between matching-logic predicates
        /// (KF-039), whose `subject_sort` and `result_sort` are Bool
        /// placeholders that semantic lowering ignores.
        #[serde(default, skip_serializing_if = "core::ops::Not::not")]
        pub predicate: bool => [keep],
        /// The `heat` or `cool` key of a transition (KF-014).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub evaluation: Option<crate::transport::rule::EvaluationStep<S>> => [option nested],
    }
}

/// The roles of the production's nodes that a constructor's descriptor
/// repeats from its grammar descriptor, whose wire alone denotes them: the
/// declaration and its field names and documentation, the syntax with its
/// template and format, the metadata, the tier membership and the
/// cons-list marker, the alias or desugar marker and its payload, and the
/// strictness. The constructor's wire denotes the rest itself: the
/// constructed sort, its sort parameters and element types, and each
/// field's sort with its element types.
///
/// The expander's ledger accepts these anchors of a constructor's descriptor
/// when the grammar descriptor's wire defines them; the transport, which
/// validates each descriptor alone, leaves them to the grammar descriptor's
/// closure.
pub const REPEATED_PRODUCTION_ROLES: [ProvenanceRole; 24] = [
    ProvenanceRole::ConstructorDeclaration,
    ProvenanceRole::ConstructorFieldDeclaration,
    ProvenanceRole::ConstructorDocumentation,
    ProvenanceRole::ConstructorSyntax,
    ProvenanceRole::ConstructorSyntaxItem,
    ProvenanceRole::ConstructorSyntaxFieldReference,
    ProvenanceRole::ConstructorFormat,
    ProvenanceRole::ConstructorFormatFragment,
    ProvenanceRole::ConstructorGroup,
    ProvenanceRole::ConstructorAvoid,
    ProvenanceRole::ConstructorPrefer,
    ProvenanceRole::ConstructorInternal,
    ProvenanceRole::ConstructorProgram,
    ProvenanceRole::ConstructorOverload,
    ProvenanceRole::ConstructorColor,
    ProvenanceRole::ConstructorColorsEntry,
    ProvenanceRole::ConsListDeclaration,
    ProvenanceRole::AliasProduction,
    ProvenanceRole::DesugarProduction,
    ProvenanceRole::StaticRecursive,
    ProvenanceRole::StrictnessDeclaration,
    ProvenanceRole::StrictnessContextAliasReference,
    ProvenanceRole::StrictnessFieldReference,
    ProvenanceRole::StrictnessResultSort,
];

/// The roles of a syntax list's attribute nodes, which a list variant's
/// constructor descriptor repeats beside [`REPEATED_PRODUCTION_ROLES`]: the
/// variant's constructor and grammar descriptors share the production's
/// anchors, and only the grammar descriptor's wire denotes these.
pub const REPEATED_LIST_ROLES: [ProvenanceRole; 3] = [
    ProvenanceRole::ListDeclaration,
    ProvenanceRole::ListSeparator,
    ProvenanceRole::ListNonEmpty,
];

/// Descriptor-stage form of [`StructuredRule`].
pub type StructuredRuleDescriptor = StructuredRule<DescriptorStage>;

/// Host-stage form of [`StructuredRule`].
pub type HostStructuredRuleDescriptor = StructuredRule<HostStage>;

/// Typed local grammar transport error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GrammarTransportError {
    /// A required textual value was blank.
    EmptyText(TransportField),
    /// A declared sort reference used the wrong stable namespace.
    SortReferenceKind(ItemKind),
    /// A declared application used the wrong stable namespace.
    ApplicationReferenceKind(ItemKind),
    /// A collection-valued grammar construct was empty.
    EmptyCollection(TransportField),
    /// A set-valued list repeated a value.
    DuplicateValue(TransportField),
    /// The enclosing descriptor used the wrong stable item namespace.
    DescriptorItemKind {
        /// Required stable namespace.
        expected: ItemKind,
        /// Actual stable namespace.
        actual: ItemKind,
    },
    /// A nested semantic key was absent from the descriptor provenance table.
    MissingProvenance(ProvenanceKey),
    /// A nested node's key field held a key of another role than the field
    /// requires.
    UnexpectedProvenance {
        /// The field's role.
        expected: ProvenanceRole,
        /// Supplied parser key.
        actual: ProvenanceKey,
    },
    /// The descriptor's primary key was another key than its payload's
    /// declaration.
    MismatchedProvenance {
        /// The payload's declaration key.
        expected: ProvenanceKey,
        /// Supplied parser key.
        actual: ProvenanceKey,
    },
    /// Two nested nodes defined one parser key: a key names one authored
    /// node, and every other field that names it is a reference.
    DuplicateProvenance(ProvenanceKey),
    /// The provenance table contained a parser key not represented by the
    /// complete typed payload.
    ExtraProvenance(ProvenanceKey),
    /// A rule binding was blank, repeated, absent from the subject, or used in
    /// the result without being bound by the subject.
    InvalidBinding(String),
    /// A literal payload was not in canonical protocol form.
    InvalidLiteral,
    /// A production did not satisfy its classified owner/attribute shape.
    InvalidProduction(GrammarProductionReason),
    /// A structured application mixed argument forms or repeated a field.
    InvalidApplication(GrammarApplicationReason),
    /// A structured term used a node in an invalid relational position.
    InvalidTerm(GrammarTermReason),
}

impl fmt::Display for GrammarTransportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyText(field) | Self::EmptyCollection(field) => {
                write!(formatter, "{field} must not be empty")
            }
            Self::SortReferenceKind(kind) => {
                write!(formatter, "declared sort reference has item kind {kind}")
            }
            Self::ApplicationReferenceKind(kind) => {
                write!(
                    formatter,
                    "declared application reference has item kind {kind}"
                )
            }
            Self::DuplicateValue(field) => write!(formatter, "{field} contains a duplicate"),
            Self::DescriptorItemKind { expected, actual } => write!(
                formatter,
                "descriptor item kind mismatch: expected {expected}, found {actual}"
            ),
            Self::MissingProvenance(key) => write!(
                formatter,
                "descriptor provenance lacks `{}#{}`",
                key.role(),
                key.ordinal()
            ),
            Self::UnexpectedProvenance { expected, actual } => write!(
                formatter,
                "expected a `{expected}` provenance key, found `{}#{}`",
                actual.role(),
                actual.ordinal()
            ),
            Self::MismatchedProvenance { expected, actual } => write!(
                formatter,
                "expected provenance key `{}#{}`, found `{}#{}`",
                expected.role(),
                expected.ordinal(),
                actual.role(),
                actual.ordinal()
            ),
            Self::DuplicateProvenance(key) => write!(
                formatter,
                "provenance `{}#{}` is defined by two nodes",
                key.role(),
                key.ordinal()
            ),
            Self::ExtraProvenance(key) => write!(
                formatter,
                "unexpected provenance entry `{}#{}`",
                key.role(),
                key.ordinal()
            ),
            Self::InvalidBinding(binding) => write!(formatter, "invalid rule binding {binding:?}"),
            Self::InvalidLiteral => formatter.write_str("literal is not in canonical form"),
            Self::InvalidProduction(detail) => write!(formatter, "invalid production: {detail}"),
            Self::InvalidApplication(detail) => {
                write!(formatter, "invalid application: {detail}")
            }
            Self::InvalidTerm(detail) => write!(formatter, "invalid term: {detail}"),
        }
    }
}

impl Error for GrammarTransportError {}

impl From<KeyFailure> for GrammarTransportError {
    fn from(failure: KeyFailure) -> Self {
        match failure {
            KeyFailure::Role { expected, actual } => {
                Self::UnexpectedProvenance { expected, actual }
            }
            KeyFailure::Mismatched { expected, actual } => {
                Self::MismatchedProvenance { expected, actual }
            }
            KeyFailure::Duplicate(key) => Self::DuplicateProvenance(key),
            KeyFailure::Missing(key) => Self::MissingProvenance(key),
            KeyFailure::Extra(key) => Self::ExtraProvenance(key),
        }
    }
}

impl From<TermRefusal> for GrammarTransportError {
    fn from(refusal: TermRefusal) -> Self {
        Self::InvalidTerm(match refusal {
            TermRefusal::Wildcard => GrammarTermReason::WildcardsAreAllowedOnlyInRuleSubjects,
            TermRefusal::BuiltinToken => GrammarTermReason::InvalidCompilerOwnedBuiltinToken,
            TermRefusal::PatternAs => GrammarTermReason::PatternAsOutsideLeftHandSide,
            TermRefusal::PatternOr => GrammarTermReason::PatternOrOutsideLeftHandSide,
            TermRefusal::Matches => GrammarTermReason::MatchesInPattern,
            TermRefusal::Let => GrammarTermReason::LetInPattern,
            TermRefusal::Closure => GrammarTermReason::ClosureInPattern,
            TermRefusal::RecordUpdateBase => GrammarTermReason::RecordUpdateBase,
        })
    }
}

impl DescriptorSortRef {
    /// Checks the stable namespace of a declared sort.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarTransportError::SortReferenceKind`] when a declared
    /// target is not a sort identity.
    pub fn validate(&self) -> Result<(), GrammarTransportError> {
        match self {
            Self::Declared(id) if id.item_kind() != ItemKind::Sort => {
                Err(GrammarTransportError::SortReferenceKind(id.item_kind()))
            }
            Self::Cell(id) if id.item_kind() != ItemKind::Cell => {
                Err(GrammarTransportError::SortReferenceKind(id.item_kind()))
            }
            Self::Parameter(name) if !is_sort_parameter_name(name) => {
                Err(GrammarTransportError::SortReferenceKind(ItemKind::Sort))
            }
            Self::Declared(_) | Self::Builtin(_) | Self::Cell(_) | Self::Parameter(_) => Ok(()),
        }
    }
}

/// Whether `name` is a Rust identifier usable as a sort parameter name.
fn is_sort_parameter_name(name: &str) -> bool {
    let mut characters = name.chars();
    characters
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
        && characters.all(|character| character.is_ascii_alphanumeric() || character == '_')
}

impl DescriptorApplicationRef {
    /// Checks the stable namespace of a declared application.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarTransportError::ApplicationReferenceKind`] when a
    /// declared target is not a constructor identity.
    pub fn validate(&self) -> Result<(), GrammarTransportError> {
        if let Self::Declared(id) = self
            && id.item_kind() != ItemKind::Constructor
        {
            return Err(GrammarTransportError::ApplicationReferenceKind(
                id.item_kind(),
            ));
        }
        Ok(())
    }

    /// Checks the stable namespace of a term's application head: a
    /// constructor, or a named constant, which the compiler substitutes
    /// before it reads the term.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarTransportError::ApplicationReferenceKind`] when a
    /// declared head is neither a constructor nor a constant.
    pub fn validate_term_head(&self) -> Result<(), GrammarTransportError> {
        match self {
            Self::Declared(id) if id.item_kind() == ItemKind::Constant => Ok(()),
            _ => self.validate(),
        }
    }
}

impl DescriptorLiteral {
    pub(super) fn validate(&self) -> Result<(), GrammarTransportError> {
        match self {
            Self::Int(value) if is_canonical_int(value) => Ok(()),
            Self::Bool(_) => Ok(()),
            Self::String(value) if crate::string_token::encode(value).is_ok() => Ok(()),
            Self::Float(token) if crate::float_token::validate(token).is_ok() => Ok(()),
            Self::Int(_) | Self::String(_) | Self::Float(_) => {
                Err(GrammarTransportError::InvalidLiteral)
            }
        }
    }
}

/// Whether `value` matches `0|-?[1-9][0-9]*`.
fn is_canonical_int(value: &str) -> bool {
    if value == "0" {
        return true;
    }
    let digits = value.strip_prefix('-').unwrap_or(value);
    digits
        .bytes()
        .next()
        .is_some_and(|first| first.is_ascii_digit() && first != b'0')
        && digits.bytes().all(|byte| byte.is_ascii_digit())
}

fn validate_collection_application_shape(
    head_class: DescriptorApplicationHeadClass,
    application: &DescriptorApplicationRef,
    arguments: &Arguments<DescriptorStage>,
) -> Result<(), GrammarTransportError> {
    let (arity, unapplied, invalid_arity, positional_only) = match application {
        DescriptorApplicationRef::Map(operation) => (
            operation.spec().arity(),
            GrammarApplicationReason::UnappliedMapOperation,
            GrammarApplicationReason::MapOperationHasInvalidArity,
            GrammarApplicationReason::MapOperationsAcceptPositionalArgumentsOnly,
        ),
        DescriptorApplicationRef::List(operation) => (
            operation.spec().arity(),
            GrammarApplicationReason::UnappliedListOperation,
            GrammarApplicationReason::ListOperationHasInvalidArity,
            GrammarApplicationReason::ListOperationsAcceptPositionalArgumentsOnly,
        ),
        DescriptorApplicationRef::Set(operation) => (
            operation.spec().arity(),
            GrammarApplicationReason::UnappliedSetOperation,
            GrammarApplicationReason::SetOperationHasInvalidArity,
            GrammarApplicationReason::SetOperationsAcceptPositionalArgumentsOnly,
        ),
        // A connective's operands are checked by semantic lowering, which
        // reports the connective's arity (KF-039).
        DescriptorApplicationRef::Declared(_)
        | DescriptorApplicationRef::Builtin(_)
        | DescriptorApplicationRef::Ml(_)
        | DescriptorApplicationRef::Operator(_)
        | DescriptorApplicationRef::ListNotation(_) => {
            return Ok(());
        }
    };
    if head_class != DescriptorApplicationHeadClass::Applied {
        return Err(GrammarTransportError::InvalidApplication(unapplied));
    }
    if arguments.len() != arity {
        return Err(GrammarTransportError::InvalidApplication(invalid_arity));
    }
    if arguments
        .iter()
        .any(|argument| !matches!(argument, TermArgumentRef::Positional { .. }))
    {
        return Err(GrammarTransportError::InvalidApplication(positional_only));
    }
    Ok(())
}

impl DescriptorTerm {
    /// Validates references, literals, names, and exact nested provenance.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarTransportError`] for an invalid reference/literal, an
    /// unbound name, or a missing parser-keyed origin.
    pub fn validate(
        &self,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
        bindings: &BTreeSet<String>,
        seen_variables: &mut BTreeSet<String>,
        allow_wildcards: bool,
    ) -> Result<(), GrammarTransportError> {
        super::validation::validate_term(
            self,
            &mut term_validation::GrammarTermValidation {
                provenance,
                bindings,
                seen_variables,
                allow_wildcards,
                in_matches_pattern: false,
                in_let_pattern: false,
                let_scopes: Vec::new(),
                allow_rewrite: false,
                in_rewrite_right: false,
            },
        )
    }

    /// Validates the subject of a single-body rule (KF-011): like a rule
    /// subject, and its `k::rewrite!` islands are admitted; their right
    /// sides use the subject's bindings without binding them.
    ///
    /// # Errors
    ///
    /// As [`Self::validate`], plus a nested rewrite or a `()` right side.
    pub fn validate_single_body_subject(
        &self,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
        bindings: &BTreeSet<String>,
        seen_variables: &mut BTreeSet<String>,
    ) -> Result<(), GrammarTransportError> {
        if super::validation::misplaced_empty_rewrite(self, false) {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::EmptyRewriteOutsideKSequence,
            ));
        }
        super::validation::validate_term(
            self,
            &mut term_validation::GrammarTermValidation {
                provenance,
                bindings,
                seen_variables,
                allow_wildcards: true,
                in_matches_pattern: false,
                in_let_pattern: false,
                let_scopes: Vec::new(),
                allow_rewrite: true,
                in_rewrite_right: false,
            },
        )
    }
}

impl StructuredRuleDescriptor {
    /// Validates the existentials of a transition and returns the names its
    /// result and ensures condition may reference.
    fn validate_existentials(
        &self,
        bindings: &BTreeSet<String>,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    ) -> Result<BTreeSet<String>, GrammarTransportError> {
        if (!self.existentials.is_empty() || self.ensures.is_some())
            && self.sentence_kind != SentenceKind::Transition
        {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::InvalidRuleExistential,
            ));
        }
        let mut right_bindings = bindings.clone();
        for binder in &self.existentials {
            require_key(&binder.declaration_key, provenance)?;
            require_key(&binder.name_key, provenance)?;
            require_key(&binder.sort.key, provenance)?;
            binder.sort.sort.validate()?;
            if binder.name.trim().is_empty() || !right_bindings.insert(binder.name.clone()) {
                return Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::InvalidRuleExistential,
                ));
            }
        }
        if !self.fresh.is_empty()
            && (self.sentence_kind != SentenceKind::Transition || self.anywhere.is_some())
        {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::InvalidRuleFresh,
            ));
        }
        for binder in &self.fresh {
            require_key(&binder.declaration_key, provenance)?;
            require_key(&binder.name_key, provenance)?;
            require_key(&binder.sort.key, provenance)?;
            binder.sort.sort.validate()?;
            if binder.name.trim().is_empty() || !right_bindings.insert(binder.name.clone()) {
                return Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::InvalidRuleFresh,
                ));
            }
        }
        Ok(right_bindings)
    }

    /// Validates the result against the names it may reference, including a
    /// desugar clause's `unbound_variables` (KF-046): each listed name is
    /// used by the result, and `_` admits result wildcards.
    fn validate_result(
        &self,
        bindings: &BTreeSet<String>,
        mut right_bindings: BTreeSet<String>,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    ) -> Result<(), GrammarTransportError> {
        let invalid =
            || GrammarTransportError::InvalidTerm(GrammarTermReason::InvalidUnboundVariables);
        let mut result_wildcards = false;
        if let Some(unbound) = &self.unbound_variables {
            if self.sentence_kind != SentenceKind::Desugar {
                return Err(invalid());
            }
            unbound.validate(bindings, provenance)?;
            right_bindings.extend(unbound.names().map(str::to_owned));
            result_wildcards = unbound.lists_wildcard();
        }
        let mut result_variables = BTreeSet::new();
        if let Some(result) = &self.result {
            result.validate(
                provenance,
                &right_bindings,
                &mut result_variables,
                result_wildcards,
            )?;
        }
        if let Some(unbound) = &self.unbound_variables
            && unbound.names().any(|name| !result_variables.contains(name))
        {
            return Err(invalid());
        }
        Ok(())
    }

    /// Validates the result keys and sort, or a single-body rule's lack of
    /// them (KF-011): a transition that is not an anywhere rule, whose
    /// subject holds a `k::rewrite!`, with no result binders, function
    /// context, or clause metadata. Returns whether the rule is single-body.
    fn validate_result_shape(
        &self,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    ) -> Result<bool, GrammarTransportError> {
        match (&self.result_key, &self.result_sort, &self.result) {
            (Some(result_key), Some(result_sort), Some(_)) => {
                require_key(&result_sort.key, provenance)?;
                require_key(result_key, provenance)?;
                result_sort.sort.validate()?;
                Ok(false)
            }
            (None, None, None)
                if self.sentence_kind == SentenceKind::Transition
                    && self.anywhere.is_none()
                    && self.existentials.is_empty()
                    && self.ensures.is_none()
                    && self.fresh.is_empty()
                    && self.unbound_variables.is_none()
                    && self.function_context.is_none()
                    && super::validation::contains_rewrite(&self.subject) =>
            {
                Ok(true)
            }
            // A context (KF-021) has no post-state; it may rewrite its hole
            // once, or not at all.
            (None, None, None)
                if self.sentence_kind == SentenceKind::Context
                    && self.evaluation.is_some()
                    && self.anywhere.is_none()
                    && self.existentials.is_empty()
                    && self.ensures.is_none()
                    && self.fresh.is_empty()
                    && self.unbound_variables.is_none()
                    && self.function_context.is_none()
                    && super::validation::count_rewrites(&self.subject) <= 1 =>
            {
                Ok(true)
            }
            _ => Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::SingleBodyRuleWithoutRewrite,
            )),
        }
    }

    /// Validates an equation's function context and returns the subject's
    /// bindings extended by the context's (KF-025).
    fn validate_function_context(
        &self,
        mut bindings: BTreeSet<String>,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    ) -> Result<BTreeSet<String>, GrammarTransportError> {
        let Some(context) = &self.function_context else {
            return Ok(bindings);
        };
        let invalid =
            || GrammarTransportError::InvalidTerm(GrammarTermReason::InvalidFunctionContext);
        if self.sentence_kind != SentenceKind::Equation
            || context.configuration.configuration.item_kind() != ItemKind::Configuration
            || !matches!(
                context.cells.remainder,
                crate::ProtocolRuleFrame::Anonymous { .. }
            )
        {
            return Err(invalid());
        }
        require_key(&context.key, provenance)?;
        require_key(&context.configuration.key, provenance)?;
        require_key(&context.cells.key, provenance)?;
        for binding in &context.bindings {
            if let crate::ProtocolRuleBindingKind::Term { sort } = &binding.kind {
                require_key(&sort.key, provenance)?;
                sort.sort.validate()?;
            }
            if binding.name.trim().is_empty()
                || matches!(
                    binding.kind,
                    crate::ProtocolRuleBindingKind::ConfigurationFrame
                )
                || !bindings.insert(binding.name.clone())
            {
                return Err(invalid());
            }
        }
        // The closure checks the context's cell keys against the anchors.
        Ok(bindings)
    }

    /// Validates the priority, nondet, and anywhere keys of a rule.
    fn validate_rule_keys(
        &self,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    ) -> Result<(), GrammarTransportError> {
        if let Some(priority) = &self.priority {
            require_key(&priority.key, provenance)?;
            if priority.role_for(self.sentence_kind).is_none() {
                return Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::InvalidPriorityKind,
                ));
            }
        }
        if let Some(nondet) = &self.nondet {
            require_key(&nondet.key, provenance)?;
            if self.sentence_kind != SentenceKind::Transition || !nondet.is_valid() {
                return Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::InvalidNondetGroup,
                ));
            }
        }
        if let Some(anywhere) = &self.anywhere {
            require_key(anywhere, provenance)?;
            if self.sentence_kind != SentenceKind::Transition
                || anywhere.role() != ProvenanceRole::RuleAnywhere
                || anywhere.ordinal() != 0
                || self.priority.is_some()
                || self.nondet.is_some()
            {
                return Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::InvalidAnywhereRule,
                ));
            }
        }
        if let Some(step) = &self.evaluation {
            require_key(&step.key, provenance)?;
            require_key(&step.hole_key, provenance)?;
            if let Some(sort) = &step.result {
                require_key(&sort.key, provenance)?;
                sort.sort.validate()?;
            }
            let allowed = if self.sentence_kind == SentenceKind::Context {
                step.kind == crate::EvaluationKind::Context
            } else {
                self.sentence_kind == SentenceKind::Transition
                    && step.kind != crate::EvaluationKind::Context
                    && self.priority.is_none()
                    && self.nondet.is_none()
                    && self.anywhere.is_none()
                    && self.fresh.is_empty()
            };
            if !allowed || !step.has_valid_roles(|sort| &sort.key) {
                return Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::InvalidEvaluationStep,
                ));
            }
        }
        Ok(())
    }

    /// Validates the declared binder list: none, or every subject binding in
    /// first-occurrence order, each with its parameter and sort keys.
    fn validate_typed_bindings(
        &self,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    ) -> Result<(), GrammarTransportError> {
        // With a function context the list is mandatory and also declares
        // the context's term binders, after the subject's (X5.1).
        let mut expected = self.bindings.iter().map(String::as_str).collect::<Vec<_>>();
        if let Some(context) = &self.function_context {
            if self.typed_bindings.is_empty() {
                return Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::InvalidFunctionContext,
                ));
            }
            expected.extend(context.term_binding_names());
        }
        if self.typed_bindings.is_empty() {
            return Ok(());
        }
        if self.typed_bindings.len() != expected.len() {
            return Err(GrammarTransportError::InvalidBinding(
                expected
                    .iter()
                    .find(|name| !self.typed_bindings.iter().any(|typed| typed.name == **name))
                    .or_else(|| expected.last())
                    .map(|name| (*name).to_owned())
                    .unwrap_or_default(),
            ));
        }
        for (binding, name) in self.typed_bindings.iter().zip(&expected) {
            if binding.name != *name {
                return Err(GrammarTransportError::InvalidBinding(binding.name.clone()));
            }
            require_key(&binding.key, provenance)?;
            require_key(&binding.sort.key, provenance)?;
            binding.sort.sort.validate()?;
        }
        Ok(())
    }

    /// Validates local rule shape and all parser-keyed nested nodes.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarTransportError`] for wrong ownership, typed references,
    /// bindings, terms, literals, or missing provenance.
    #[expect(
        clippy::too_many_lines,
        reason = "One validator checks every rule field, in order, against one provenance table."
    )]
    pub fn validate(
        &self,
        descriptor_kind: ItemKind,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    ) -> Result<(), GrammarTransportError> {
        let expected = self.sentence_kind.item_kind();
        if descriptor_kind != expected {
            return Err(GrammarTransportError::DescriptorItemKind {
                expected,
                actual: descriptor_kind,
            });
        }
        if let Some(label) = &self.label {
            require_key(&label.key, provenance)?;
            if !label.is_valid() {
                return Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::InvalidExplicitRuleLabel,
                ));
            }
        }
        if let Some(requires) = &self.requires {
            require_key(&requires.key, provenance)?;
            if matches!(
                self.sentence_kind,
                SentenceKind::Alias | SentenceKind::Desugar
            ) {
                return Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::StaticAliasRequires,
                ));
            }
        }
        self.validate_rule_keys(provenance)?;
        if let Some(equation) = &self.equation {
            if self.sentence_kind != SentenceKind::Equation {
                return Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::InvalidMatchRestriction,
                ));
            }
            equation.restriction.validate(provenance)?;
        }
        if let Some(simplification) = &self.simplification {
            require_key(&simplification.key, provenance)?;
            if self.sentence_kind != SentenceKind::Simplification {
                return Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::UnexpectedSimplificationMetadata,
                ));
            }
            if let Some(priority) = &simplification.priority {
                require_key(&priority.key, provenance)?;
            }
            if let Some(restriction) = &simplification.restriction {
                restriction.validate(provenance)?;
            }
        } else if self.sentence_kind == SentenceKind::Simplification {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::MissingSimplificationMetadata,
            ));
        }
        if self.predicate && self.sentence_kind != SentenceKind::Simplification {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::InvalidPredicateRule,
            ));
        }
        require_key(&self.subject_sort.key, provenance)?;
        require_key(&self.pattern_key, provenance)?;
        self.subject_sort.sort.validate()?;
        let single_body = self.validate_result_shape(provenance)?;
        let bindings = self.bindings.iter().cloned().collect::<BTreeSet<_>>();
        if bindings.len() != self.bindings.len()
            || self
                .bindings
                .iter()
                .any(|binding| binding.trim().is_empty())
        {
            return Err(GrammarTransportError::DuplicateValue(
                TransportField::RuleBindings,
            ));
        }
        self.validate_typed_bindings(provenance)?;
        let mut subject_variables = BTreeSet::new();
        if single_body {
            self.subject.validate_single_body_subject(
                provenance,
                &bindings,
                &mut subject_variables,
            )?;
        } else {
            self.subject
                .validate(provenance, &bindings, &mut subject_variables, true)?;
        }
        if subject_variables != bindings {
            let missing = bindings
                .difference(&subject_variables)
                .next()
                .cloned()
                .unwrap_or_default();
            return Err(GrammarTransportError::InvalidBinding(missing));
        }
        // The function context's bindings are visible to the result and
        // the requires condition, like the subject's (KF-025).
        let bindings = self.validate_function_context(bindings, provenance)?;
        let right_bindings = self.validate_existentials(&bindings, provenance)?;
        self.validate_result(&bindings, right_bindings.clone(), provenance)?;
        if let Some(requires) = &self.requires {
            let mut condition_variables = BTreeSet::new();
            requires
                .term
                .validate(provenance, &bindings, &mut condition_variables, false)?;
        }
        if let Some(ensures) = &self.ensures {
            require_key(&ensures.key, provenance)?;
            let mut condition_variables = BTreeSet::new();
            ensures
                .term
                .validate(provenance, &right_bindings, &mut condition_variables, false)?;
        }
        Ok(())
    }
}

impl GrammarDescriptor {
    pub(crate) fn expected_primary_key(&self) -> ProvenanceKey {
        match self {
            Self::Production(production) => match production.owner {
                DescriptorProductionOwner::Constructor { .. } => {
                    ProvenanceKey::new(ProvenanceRole::ConstructorDeclaration, 0)
                }
                DescriptorProductionOwner::TokenSort { .. } => {
                    ProvenanceKey::new(ProvenanceRole::TokenDeclaration, 0)
                }
                DescriptorProductionOwner::BracketSort { .. } => {
                    ProvenanceKey::new(ProvenanceRole::BracketDeclaration, 0)
                }
            },
            Self::Subsort { .. } => ProvenanceKey::new(ProvenanceRole::SubsortDeclaration, 0),
            Self::Precedence { .. } => ProvenanceKey::new(ProvenanceRole::PrecedenceDeclaration, 0),
            Self::Associativity { .. } => {
                ProvenanceKey::new(ProvenanceRole::AssociativityDeclaration, 0)
            }
            Self::Tokens { .. } => ProvenanceKey::new(ProvenanceRole::TokenDeclaration, 0),
            Self::Lexical { .. } => ProvenanceKey::new(ProvenanceRole::LexicalDeclaration, 0),
            Self::Layout { .. } => ProvenanceKey::new(ProvenanceRole::LayoutRegex, 0),
            Self::RawSentence { .. } => ProvenanceKey::new(ProvenanceRole::RawKDeclaration, 0),
            Self::SpecModule { .. } => ProvenanceKey::new(ProvenanceRole::SpecModuleDeclaration, 0),
        }
    }

    /// Validates local grammar shape and every nested provenance/reference.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarTransportError`] for wrong ownership, malformed
    /// productions/relations, typed references, or missing provenance.
    #[expect(
        clippy::too_many_lines,
        reason = "One validation arm per grammar descriptor variant."
    )]
    pub fn validate(
        &self,
        descriptor_kind: ItemKind,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    ) -> Result<(), GrammarTransportError> {
        if descriptor_kind != ItemKind::Grammar {
            return Err(GrammarTransportError::DescriptorItemKind {
                expected: ItemKind::Grammar,
                actual: descriptor_kind,
            });
        }
        match self {
            Self::Production(production) => {
                if matches!(
                    production.owner,
                    DescriptorProductionOwner::TokenSort { .. }
                ) {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::TokenOutsideCarrier,
                    ));
                }
                production.validate(provenance)
            }
            Self::Tokens { productions } => {
                let Some(first) = productions.first() else {
                    return Err(GrammarTransportError::EmptyCollection(
                        TransportField::ProductionItems,
                    ));
                };
                let DescriptorProductionOwner::TokenSort { sort } = &first.owner else {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::TokenCarrierOwner,
                    ));
                };
                for production in productions {
                    match &production.owner {
                        DescriptorProductionOwner::TokenSort { sort: owner }
                            if owner.sort == sort.sort
                                && production.result_sort.sort == sort.sort => {}
                        _ => {
                            return Err(GrammarTransportError::InvalidProduction(
                                GrammarProductionReason::TokenCarrierOwner,
                            ));
                        }
                    }
                    production.validate(provenance)?;
                }
                Ok(())
            }
            Self::Subsort {
                key,
                subsort,
                supersort,
            } => {
                require_key(key, provenance)?;
                validate_sort_reference(subsort, provenance)?;
                validate_sort_reference(supersort, provenance)
            }
            Self::Precedence { key, chains } => {
                require_key(key, provenance)?;
                if chains.is_empty() {
                    return Err(GrammarTransportError::EmptyCollection(
                        TransportField::PrecedenceChains,
                    ));
                }
                for chain in chains {
                    require_key(&chain.key, provenance)?;
                    validate_group_references(
                        &chain.groups,
                        provenance,
                        TransportField::PrecedenceGroups,
                    )?;
                }
                Ok(())
            }
            Self::Lexical { lexicals } => validate_lexicals(lexicals, provenance),
            Self::Layout { regexes } => validate_layout(regexes, provenance),
            Self::Associativity { key, sentences } => {
                require_key(key, provenance)?;
                if sentences.is_empty() {
                    return Err(GrammarTransportError::EmptyCollection(
                        TransportField::AssociativitySentences,
                    ));
                }
                for sentence in sentences {
                    require_key(&sentence.key, provenance)?;
                    validate_group_references(
                        &sentence.groups,
                        provenance,
                        TransportField::AssociativityGroups,
                    )?;
                }
                Ok(())
            }
            Self::RawSentence {
                key,
                text,
                line,
                column,
                ..
            } => {
                require_key(key, provenance)?;
                if text.trim().is_empty() || *line == 0 || *column == 0 {
                    return Err(GrammarTransportError::EmptyCollection(
                        TransportField::RawSentenceText,
                    ));
                }
                Ok(())
            }
            Self::SpecModule { key, name, imports } => {
                require_key(key, provenance)?;
                if let Some(name) = name {
                    require_key(&name.key, provenance)?;
                    if name.value.is_empty() {
                        return Err(GrammarTransportError::EmptyCollection(
                            TransportField::SpecModuleName,
                        ));
                    }
                }
                for import in imports {
                    require_key(&import.key, provenance)?;
                    if import.path.is_empty() {
                        return Err(GrammarTransportError::EmptyCollection(
                            TransportField::SpecModuleImport,
                        ));
                    }
                }
                Ok(())
            }
        }
    }
}

impl DescriptorProduction {
    #[expect(
        clippy::too_many_lines,
        reason = "One ordered pass checks all production shape and provenance invariants."
    )]
    fn validate(
        &self,
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    ) -> Result<(), GrammarTransportError> {
        require_key(&self.key, provenance)?;
        if let Some(template_key) = &self.template_key {
            require_key(template_key, provenance)?;
        }
        match &self.owner {
            DescriptorProductionOwner::Constructor { constructor } => {
                require_key(&constructor.key, provenance)?;
                constructor.application.validate()?;
            }
            DescriptorProductionOwner::TokenSort { sort } => {
                // A type-alias carrier adds token productions to an existing
                // sort, which may be builtin; semantic lowering decides which.
                validate_sort_reference(sort, provenance)?;
            }
            DescriptorProductionOwner::BracketSort { sort } => {
                validate_sort_reference(sort, provenance)?;
                if !matches!(sort.sort, DescriptorSortRef::Declared(_)) {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::TokenOrBracketOwnerKind,
                    ));
                }
            }
        }
        validate_sort_reference(&self.result_sort, provenance)?;
        if self.items.is_empty() {
            return Err(GrammarTransportError::EmptyCollection(
                TransportField::ProductionItems,
            ));
        }
        for item in &self.items {
            match item {
                DescriptorProductionItem::Terminal { key, text } => {
                    require_key(key, provenance)?;
                    if text.is_empty() {
                        return Err(GrammarTransportError::EmptyText(TransportField::Terminal));
                    }
                }
                DescriptorProductionItem::NonTerminal {
                    key,
                    field_key,
                    declaration_key,
                    sort,
                    ..
                } => {
                    require_key(key, provenance)?;
                    require_key(field_key, provenance)?;
                    if let Some(declaration_key) = declaration_key {
                        require_key(declaration_key, provenance)?;
                    }
                    validate_sort_reference(sort, provenance)?;
                }
                DescriptorProductionItem::RegexTerminal {
                    key,
                    precede_regex,
                    regex,
                    follow_regex,
                } => {
                    require_key(key, provenance)?;
                    if regex.is_empty()
                        || precede_regex.as_deref() == Some("")
                        || follow_regex.as_deref() == Some("")
                    {
                        return Err(GrammarTransportError::EmptyText(
                            TransportField::ProductionRegex,
                        ));
                    }
                }
            }
        }
        let mut families = BTreeSet::new();
        for attribute in &self.attributes {
            let family = match attribute {
                DescriptorProductionAttribute::Documentation { key, .. } => {
                    require_key(key, provenance)?;
                    continue;
                }
                DescriptorProductionAttribute::Function { key } => {
                    require_key(key, provenance)?;
                    "function"
                }
                DescriptorProductionAttribute::Total { key } => {
                    require_key(key, provenance)?;
                    "total"
                }
                DescriptorProductionAttribute::Hook { key, .. }
                | DescriptorProductionAttribute::RawHook { key, .. } => {
                    require_key(key, provenance)?;
                    "hook"
                }
                DescriptorProductionAttribute::Alias { key, recursive } => {
                    require_key(key, provenance)?;
                    if let Some(recursive) = recursive {
                        require_key(recursive, provenance)?;
                    }
                    "alias"
                }
                DescriptorProductionAttribute::Desugar { key, recursive } => {
                    require_key(key, provenance)?;
                    if let Some(recursive) = recursive {
                        require_key(recursive, provenance)?;
                    }
                    "desugar"
                }
                DescriptorProductionAttribute::Token {
                    key,
                    lexical_precedence,
                } => {
                    require_key(key, provenance)?;
                    if let Some(precedence) = lexical_precedence {
                        require_key(&precedence.key, provenance)?;
                    }
                    "token"
                }
                DescriptorProductionAttribute::Group { reference } => {
                    require_key(&reference.key, provenance)?;
                    "group"
                }
                DescriptorProductionAttribute::Bracket { key } => {
                    require_key(key, provenance)?;
                    "bracket"
                }
                DescriptorProductionAttribute::Avoid { key } => {
                    require_key(key, provenance)?;
                    "avoid"
                }
                DescriptorProductionAttribute::Format { key, fragments } => {
                    require_key(key, provenance)?;
                    if fragments.is_empty() {
                        return Err(GrammarTransportError::EmptyCollection(
                            TransportField::FormatFragments,
                        ));
                    }
                    for fragment in fragments {
                        require_key(&fragment.key, provenance)?;
                    }
                    "format"
                }
                DescriptorProductionAttribute::Strictness {
                    key,
                    fields,
                    result_sort,
                    ..
                } => {
                    require_key(key, provenance)?;
                    if fields.is_empty() {
                        return Err(GrammarTransportError::EmptyCollection(
                            TransportField::StrictnessFields,
                        ));
                    }
                    let mut names = BTreeSet::new();
                    for field in fields {
                        require_key(&field.key, provenance)?;
                        if !names.insert(field.field.clone()) {
                            return Err(GrammarTransportError::DuplicateValue(
                                TransportField::StrictnessFields,
                            ));
                        }
                    }
                    validate_sort_reference(result_sort, provenance)?;
                    "strictness"
                }
                DescriptorProductionAttribute::Internal { key } => {
                    require_key(key, provenance)?;
                    "internal"
                }
                DescriptorProductionAttribute::Program { key } => {
                    require_key(key, provenance)?;
                    "program"
                }
                DescriptorProductionAttribute::Color { key, value } => {
                    require_key(key, provenance)?;
                    if value.is_empty() {
                        return Err(GrammarTransportError::EmptyText(TransportField::Color));
                    }
                    "color"
                }
                DescriptorProductionAttribute::Colors { key, values } => {
                    require_key(key, provenance)?;
                    if values.is_empty() {
                        return Err(GrammarTransportError::EmptyCollection(
                            TransportField::Colors,
                        ));
                    }
                    for entry in values {
                        require_key(&entry.key, provenance)?;
                        if entry.value.is_empty() {
                            return Err(GrammarTransportError::EmptyText(TransportField::Color));
                        }
                    }
                    "color"
                }
                DescriptorProductionAttribute::Prefer { key } => {
                    require_key(key, provenance)?;
                    "prefer"
                }
                DescriptorProductionAttribute::Overload { target } => {
                    require_key(&target.key, provenance)?;
                    "overload"
                }
                DescriptorProductionAttribute::Memo { key } => {
                    require_key(key, provenance)?;
                    "memo"
                }
                DescriptorProductionAttribute::FreshGenerator { key } => {
                    require_key(key, provenance)?;
                    "fresh_generator"
                }
                DescriptorProductionAttribute::Smtlib { key, symbol } => {
                    require_key(key, provenance)?;
                    if !crate::is_smtlib_simple_symbol(symbol) {
                        return Err(GrammarTransportError::InvalidProduction(
                            GrammarProductionReason::InvalidSmtlibSymbol,
                        ));
                    }
                    "smt"
                }
                DescriptorProductionAttribute::SmtHook { key, template } => {
                    require_key(key, provenance)?;
                    self.validate_smt_template(template, provenance)?;
                    "smt"
                }
                DescriptorProductionAttribute::Underspecified { key, reason } => {
                    require_key(key, provenance)?;
                    if reason.trim().is_empty() {
                        return Err(GrammarTransportError::InvalidProduction(
                            GrammarProductionReason::EmptyUnderspecifiedReason,
                        ));
                    }
                    "underspecified"
                }
                DescriptorProductionAttribute::ListCons {
                    key,
                    separator_key,
                    non_empty,
                    terminator,
                    ..
                } => {
                    require_key(key, provenance)?;
                    require_key(separator_key, provenance)?;
                    if let Some(non_empty) = non_empty {
                        require_key(non_empty, provenance)?;
                    }
                    require_key(&terminator.key, provenance)?;
                    terminator.application.validate()?;
                    "list"
                }
                DescriptorProductionAttribute::ListTerminator { cons } => {
                    require_key(&cons.key, provenance)?;
                    cons.application.validate()?;
                    "list"
                }
                DescriptorProductionAttribute::ConsList { key, empty } => {
                    require_key(key, provenance)?;
                    require_key(&empty.key, provenance)?;
                    empty.application.validate()?;
                    "cons_list"
                }
            };
            if !families.insert(family) {
                return Err(GrammarTransportError::DuplicateValue(
                    TransportField::ProductionAttributeFamilies,
                ));
            }
        }
        if families.contains("total") && !families.contains("function") {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::TotalWithoutFunction,
            ));
        }
        if families.contains("hook")
            && !(families.contains("function") && families.contains("total"))
        {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::HookWithoutTotalFunction,
            ));
        }
        if families.contains("alias") && families.contains("desugar") {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::AliasDesugarMetadata,
            ));
        }
        if (families.contains("alias") || families.contains("desugar"))
            && families.contains("function")
        {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::AliasFunctionMetadata,
            ));
        }
        if families.contains("internal") && families.contains("program") {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::InternalProgramMetadata,
            ));
        }
        if families.contains("memo") && !families.contains("function") {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::MemoWithoutFunction,
            ));
        }
        if families.contains("fresh_generator") && !families.contains("function") {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::FreshGeneratorWithoutFunction,
            ));
        }
        if families.contains("underspecified") && !families.contains("total") {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::UnderspecifiedWithoutTotal,
            ));
        }
        if families.contains("smt") && !families.contains("function") {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::SmtWithoutFunction,
            ));
        }
        if families.contains("prefer") && families.contains("avoid") {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::PreferAvoidMetadata,
            ));
        }
        if families.contains("list")
            && (["function", "token", "bracket", "alias", "desugar", "hook"]
                .iter()
                .any(|family| families.contains(family))
                || !matches!(self.owner, DescriptorProductionOwner::Constructor { .. }))
        {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::ListMetadata,
            ));
        }
        let has_token = families.contains("token");
        let has_bracket = families.contains("bracket");
        match &self.owner {
            DescriptorProductionOwner::TokenSort { .. } => {
                if !has_token {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::TokenOwnerShape,
                    ));
                }
                match self.items.as_slice() {
                    [
                        DescriptorProductionItem::RegexTerminal {
                            precede_regex,
                            follow_regex,
                            ..
                        },
                    ] => {
                        if precede_regex.is_some() || follow_regex.is_some() {
                            return Err(GrammarTransportError::InvalidProduction(
                                GrammarProductionReason::NominalTokenRegexGuards,
                            ));
                        }
                        Ok(())
                    }
                    [DescriptorProductionItem::Terminal { .. }] => {
                        if self.attributes.iter().any(|attribute| {
                            matches!(
                                attribute,
                                DescriptorProductionAttribute::Token {
                                    lexical_precedence: Some(_),
                                    ..
                                }
                            )
                        }) {
                            return Err(GrammarTransportError::InvalidProduction(
                                GrammarProductionReason::TerminalTokenPrecedence,
                            ));
                        }
                        Ok(())
                    }
                    _ => Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::TokenRegexItemCount,
                    )),
                }
            }
            DescriptorProductionOwner::BracketSort { sort } => {
                if !has_bracket
                    || self
                        .items
                        .iter()
                        .filter(|item| matches!(item, DescriptorProductionItem::NonTerminal { .. }))
                        .count()
                        != 1
                {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::BracketOwnerShape,
                    ));
                }
                if self.result_sort.sort != sort.sort {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::BracketOwnerResultSortMismatch,
                    ));
                }
                for item in &self.items {
                    match item {
                        DescriptorProductionItem::RegexTerminal { .. } => {
                            return Err(GrammarTransportError::InvalidProduction(
                                GrammarProductionReason::BracketRegexItem,
                            ));
                        }
                        DescriptorProductionItem::NonTerminal {
                            field,
                            declaration_key,
                            sort: value_sort,
                            ..
                        } => {
                            if field.as_str() != "value" {
                                return Err(GrammarTransportError::InvalidProduction(
                                    GrammarProductionReason::BracketFieldName,
                                ));
                            }
                            if declaration_key.is_some() {
                                return Err(GrammarTransportError::InvalidProduction(
                                    GrammarProductionReason::BracketConstructorField,
                                ));
                            }
                            if value_sort.sort != sort.sort {
                                return Err(GrammarTransportError::InvalidProduction(
                                    GrammarProductionReason::BracketSortMismatch,
                                ));
                            }
                        }
                        DescriptorProductionItem::Terminal { .. } => {}
                    }
                }
                Ok(())
            }
            DescriptorProductionOwner::Constructor { .. } if has_token || has_bracket => {
                Err(GrammarTransportError::InvalidProduction(
                    GrammarProductionReason::ConstructorOwnerMetadata,
                ))
            }
            DescriptorProductionOwner::Constructor { .. }
                if families.contains("format") && self.template_key.is_none() =>
            {
                Err(GrammarTransportError::InvalidProduction(
                    GrammarProductionReason::FormatWithoutConstructorSyntax,
                ))
            }
            DescriptorProductionOwner::Constructor { .. } => Ok(()),
        }
    }
}

fn validate_lexicals(
    lexicals: &[DescriptorLexical],
    provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
) -> Result<(), GrammarTransportError> {
    if lexicals.is_empty() {
        return Err(GrammarTransportError::EmptyCollection(
            TransportField::LexicalEntries,
        ));
    }
    for lexical in lexicals {
        require_key(&lexical.key, provenance)?;
        require_key(&lexical.regex_key, provenance)?;
        if lexical.name.is_empty() {
            return Err(GrammarTransportError::EmptyCollection(
                TransportField::LexicalName,
            ));
        }
        if lexical.regex.is_empty() {
            return Err(GrammarTransportError::EmptyCollection(
                TransportField::ProductionRegex,
            ));
        }
    }
    Ok(())
}

fn validate_layout(
    regexes: &[DescriptorLayoutRegex],
    provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
) -> Result<(), GrammarTransportError> {
    if regexes.is_empty() {
        return Err(GrammarTransportError::EmptyCollection(
            TransportField::LayoutRegexes,
        ));
    }
    for regex in regexes {
        require_key(&regex.key, provenance)?;
        if regex.regex.is_empty() {
            return Err(GrammarTransportError::EmptyCollection(
                TransportField::ProductionRegex,
            ));
        }
    }
    Ok(())
}

impl GrammarDescriptor {
    /// The keys of the descriptor's wire nodes, each checked for its field's
    /// role and defined once.
    pub(crate) fn wire_keys(&self) -> Result<WireKeys, GrammarTransportError> {
        let mut keys = WireKeys::default();
        match self {
            Self::Production(production) => production.collect_wire_keys(&mut keys)?,
            Self::Tokens { productions } => {
                // The carrier's name is the owner and the result sort of every
                // production: the first production's owner defines it.
                for (index, production) in productions.iter().enumerate() {
                    production.collect_token_keys(&mut keys, index == 0)?;
                }
            }
            Self::Subsort {
                key,
                subsort,
                supersort,
            } => {
                keys.define(key, ProvenanceRole::SubsortDeclaration)?;
                keys.define(&subsort.key, ProvenanceRole::SubsortSubSort)?;
                keys.define(&supersort.key, ProvenanceRole::SubsortSuperSort)?;
            }
            Self::Precedence { key, chains } => {
                keys.define(key, ProvenanceRole::PrecedenceDeclaration)?;
                for chain in chains {
                    keys.define(&chain.key, ProvenanceRole::PrecedenceChain)?;
                    for group in &chain.groups {
                        keys.define(&group.key, ProvenanceRole::PrecedenceGroupReference)?;
                    }
                }
            }
            Self::Lexical { lexicals } => {
                for lexical in lexicals {
                    keys.define(&lexical.key, ProvenanceRole::LexicalDeclaration)?;
                    keys.define(&lexical.regex_key, ProvenanceRole::LexicalRegex)?;
                }
            }
            Self::Layout { regexes } => {
                for regex in regexes {
                    keys.define(&regex.key, ProvenanceRole::LayoutRegex)?;
                }
            }
            Self::Associativity { key, sentences } => {
                keys.define(key, ProvenanceRole::AssociativityDeclaration)?;
                for sentence in sentences {
                    keys.define(&sentence.key, ProvenanceRole::AssociativitySentence)?;
                    for group in &sentence.groups {
                        keys.define(&group.key, ProvenanceRole::AssociativityGroupReference)?;
                    }
                }
            }
            Self::RawSentence { key, .. } => {
                keys.define(key, ProvenanceRole::RawKDeclaration)?;
            }
            Self::SpecModule { key, name, imports } => {
                keys.define(key, ProvenanceRole::SpecModuleDeclaration)?;
                if let Some(name) = name {
                    keys.define(&name.key, ProvenanceRole::SpecModuleName)?;
                }
                for import in imports {
                    keys.define(&import.key, ProvenanceRole::SpecModuleImport)?;
                }
            }
        }
        Ok(keys)
    }
}

impl DescriptorProduction {
    /// Checks an `smt_hook` template: nonempty, adjacent text merged, and each
    /// field fragment keyed and naming a nonterminal field of this production.
    fn validate_smt_template(
        &self,
        template: &[DescriptorSmtFragment],
        provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    ) -> Result<(), GrammarTransportError> {
        let invalid = || {
            GrammarTransportError::InvalidProduction(GrammarProductionReason::InvalidSmtTemplate)
        };
        if template.is_empty() {
            return Err(invalid());
        }
        let mut previous_text = false;
        for fragment in template {
            match (&fragment.fragment, &fragment.key) {
                (SmtFragment::Text(text), None) => {
                    if text.is_empty() || previous_text {
                        return Err(invalid());
                    }
                    previous_text = true;
                }
                (SmtFragment::Field(field), Some(key)) => {
                    require_key(key, provenance)?;
                    let known = self.items.iter().any(|item| {
                        matches!(item, DescriptorProductionItem::NonTerminal { field: name, .. } if name == field)
                    });
                    if !known {
                        return Err(invalid());
                    }
                    previous_text = false;
                }
                _ => return Err(invalid()),
            }
        }
        Ok(())
    }

    /// Collects the keys of one production of a token carrier. The carrier's
    /// name keys its owner and result sort, which `defines_carrier` says
    /// whether this production defines; its `regex` or `terminal` literal
    /// keys the production, which its one item and its token metadata name.
    fn collect_token_keys(
        &self,
        keys: &mut WireKeys,
        defines_carrier: bool,
    ) -> Result<(), GrammarTransportError> {
        let DescriptorProductionOwner::TokenSort { sort } = &self.owner else {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::TokenCarrierOwner,
            ));
        };
        if defines_carrier {
            keys.define(&sort.key, ProvenanceRole::TokenDeclaration)?;
        } else {
            keys.refer(&sort.key, ProvenanceRole::TokenDeclaration)?;
        }
        keys.refer(&self.result_sort.key, ProvenanceRole::TokenDeclaration)?;
        if self.template_key.is_some() {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::TokenSyntaxTemplate,
            ));
        }
        let (content_role, key) = match self.items.as_slice() {
            [DescriptorProductionItem::RegexTerminal { key, .. }] => {
                (ProvenanceRole::TokenRegex, key)
            }
            [DescriptorProductionItem::Terminal { key, .. }] => {
                (ProvenanceRole::TokenTerminal, key)
            }
            _ => {
                return Err(GrammarTransportError::InvalidProduction(
                    GrammarProductionReason::TokenRegexItemCount,
                ));
            }
        };
        keys.define(&self.key, content_role)?;
        keys.refer(key, content_role)?;
        let [
            DescriptorProductionAttribute::Token {
                key,
                lexical_precedence,
            },
        ] = self.attributes.as_slice()
        else {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::TokenMetadataShape,
            ));
        };
        keys.refer(key, content_role)?;
        if let Some(precedence) = lexical_precedence {
            if content_role != ProvenanceRole::TokenRegex {
                return Err(GrammarTransportError::InvalidProduction(
                    GrammarProductionReason::TerminalTokenPrecedence,
                ));
            }
            keys.define(&precedence.key, ProvenanceRole::TokenLexicalPrecedence)?;
        }
        Ok(())
    }

    /// The sort parameters of a parametric constructor production, each a
    /// parameter reference keyed `sort_parameter` (KF-027).
    fn collect_parameter_keys(&self, keys: &mut WireKeys) -> Result<(), GrammarTransportError> {
        for parameter in &self.parameters {
            if !matches!(parameter.sort, DescriptorSortRef::Parameter(_)) {
                return Err(GrammarTransportError::SortReferenceKind(ItemKind::Sort));
            }
            keys.define(&parameter.key, ProvenanceRole::SortParameter)?;
        }
        Ok(())
    }

    /// The production's keys. Its key is its declaration's, which a
    /// constructor production's owner names; a bracket's sort is its owner,
    /// which its result and its value nonterminal name, as its `bracket`
    /// attribute names the production.
    fn collect_wire_keys(&self, keys: &mut WireKeys) -> Result<(), GrammarTransportError> {
        match &self.owner {
            DescriptorProductionOwner::Constructor { constructor } => {
                keys.define(&self.key, ProvenanceRole::ConstructorDeclaration)?;
                keys.refer(&constructor.key, ProvenanceRole::ConstructorDeclaration)?;
                keys.define(&self.result_sort.key, ProvenanceRole::ConstructorSort)?;
                if let Some(template_key) = &self.template_key {
                    keys.define(template_key, ProvenanceRole::ConstructorSyntax)?;
                }
                self.collect_parameter_keys(keys)?;
                self.collect_constructor_item_keys(keys)?;
                self.collect_constructor_attribute_keys(keys)
            }
            DescriptorProductionOwner::TokenSort { .. } => {
                Err(GrammarTransportError::InvalidProduction(
                    GrammarProductionReason::TokenOutsideCarrier,
                ))
            }
            DescriptorProductionOwner::BracketSort { sort } => {
                keys.define(&self.key, ProvenanceRole::BracketDeclaration)?;
                keys.define(&sort.key, ProvenanceRole::SortDeclaration)?;
                keys.refer(&self.result_sort.key, ProvenanceRole::SortDeclaration)?;
                if self.template_key.is_some() {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::BracketConstructorTemplate,
                    ));
                }
                for item in &self.items {
                    match item {
                        DescriptorProductionItem::Terminal { key, .. }
                        | DescriptorProductionItem::RegexTerminal { key, .. } => {
                            keys.define(key, ProvenanceRole::BracketSyntaxItem)?;
                        }
                        DescriptorProductionItem::NonTerminal {
                            key,
                            field_key,
                            declaration_key,
                            sort,
                            ..
                        } => {
                            if declaration_key.is_some() {
                                return Err(GrammarTransportError::InvalidProduction(
                                    GrammarProductionReason::BracketConstructorField,
                                ));
                            }
                            keys.define(key, ProvenanceRole::BracketSyntaxItem)?;
                            keys.define(field_key, ProvenanceRole::BracketValueReference)?;
                            keys.refer(&sort.key, ProvenanceRole::SortDeclaration)?;
                        }
                    }
                }
                let [DescriptorProductionAttribute::Bracket { key }] = self.attributes.as_slice()
                else {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::BracketMetadataShape,
                    ));
                };
                keys.refer(key, ProvenanceRole::BracketDeclaration)?;
                Ok(())
            }
        }
    }

    /// A syntactic list's terminals are generated: the cons separator is
    /// keyed at its literal and the terminator `.Sort` at the attribute.
    fn list_terminal_role(&self) -> Option<ProvenanceRole> {
        self.attributes
            .iter()
            .find_map(|attribute| match attribute {
                DescriptorProductionAttribute::ListCons { .. } => {
                    Some(ProvenanceRole::ListSeparator)
                }
                DescriptorProductionAttribute::ListTerminator { .. } => {
                    Some(ProvenanceRole::ListDeclaration)
                }
                _ => None,
            })
    }

    /// The keys of a constructor production's items. With a syntax template
    /// each item is a node of the template, and a nonterminal names the
    /// field's declaration; without one, the production reads as the
    /// declaration: its terminal names the declaration's key, and each
    /// nonterminal is its field's declaration, which its field and
    /// declaration keys name.
    fn collect_constructor_item_keys(
        &self,
        keys: &mut WireKeys,
    ) -> Result<(), GrammarTransportError> {
        let explicit = self.template_key.is_some();
        let list_terminal = self.list_terminal_role();
        for item in &self.items {
            match item {
                DescriptorProductionItem::Terminal { key, .. } => {
                    if let Some(role) = list_terminal {
                        keys.define(key, role)?;
                    } else if explicit {
                        keys.define(key, ProvenanceRole::ConstructorSyntaxItem)?;
                    } else {
                        keys.refer(key, ProvenanceRole::ConstructorDeclaration)?;
                    }
                }
                DescriptorProductionItem::NonTerminal {
                    key,
                    field_key,
                    declaration_key,
                    sort,
                    ..
                } => {
                    let Some(declaration_key) = declaration_key else {
                        return Err(GrammarTransportError::InvalidProduction(
                            GrammarProductionReason::MissingConstructorFieldKey,
                        ));
                    };
                    if explicit {
                        keys.define(key, ProvenanceRole::ConstructorSyntaxItem)?;
                        keys.define(field_key, ProvenanceRole::ConstructorSyntaxFieldReference)?;
                        keys.define(declaration_key, ProvenanceRole::ConstructorFieldDeclaration)?;
                    } else {
                        keys.define(key, ProvenanceRole::ConstructorFieldDeclaration)?;
                        keys.refer(field_key, ProvenanceRole::ConstructorFieldDeclaration)?;
                        keys.refer(declaration_key, ProvenanceRole::ConstructorFieldDeclaration)?;
                    }
                    keys.define(&sort.key, ProvenanceRole::ConstructorFieldSort)?;
                }
                DescriptorProductionItem::RegexTerminal { .. } => {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::ConstructorRegexItem,
                    ));
                }
            }
        }
        Ok(())
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Keeps the exhaustive constructor attribute key catalog in one match."
    )]
    fn collect_constructor_attribute_keys(
        &self,
        keys: &mut WireKeys,
    ) -> Result<(), GrammarTransportError> {
        for attribute in &self.attributes {
            match attribute {
                DescriptorProductionAttribute::Documentation { key, .. } => {
                    keys.define(key, ProvenanceRole::ConstructorDocumentation)?;
                }
                DescriptorProductionAttribute::Group { reference } => {
                    keys.define(&reference.key, ProvenanceRole::ConstructorGroup)?;
                }
                DescriptorProductionAttribute::Avoid { key } => {
                    keys.define(key, ProvenanceRole::ConstructorAvoid)?;
                }
                DescriptorProductionAttribute::Prefer { key } => {
                    keys.define(key, ProvenanceRole::ConstructorPrefer)?;
                }
                DescriptorProductionAttribute::Overload { target } => {
                    keys.define(&target.key, ProvenanceRole::ConstructorOverload)?;
                }
                DescriptorProductionAttribute::Format { key, fragments } => {
                    keys.define(key, ProvenanceRole::ConstructorFormat)?;
                    for fragment in fragments {
                        keys.define(&fragment.key, ProvenanceRole::ConstructorFormatFragment)?;
                    }
                }
                DescriptorProductionAttribute::Strictness {
                    key,
                    using,
                    fields,
                    result_sort,
                    ..
                } => {
                    keys.define(key, ProvenanceRole::StrictnessDeclaration)?;
                    if let Some(using) = using {
                        keys.define(&using.key, ProvenanceRole::StrictnessContextAliasReference)?;
                    }
                    for field in fields {
                        keys.define(&field.key, ProvenanceRole::StrictnessFieldReference)?;
                    }
                    keys.define(&result_sort.key, ProvenanceRole::StrictnessResultSort)?;
                }
                DescriptorProductionAttribute::Function { key } => {
                    // A total function's name, or a partial one's `partial`.
                    if key.role() == ProvenanceRole::FunctionDeclaration {
                        keys.define(key, ProvenanceRole::FunctionDeclaration)?;
                    } else {
                        keys.define(key, ProvenanceRole::FunctionPartial)?;
                    }
                }
                DescriptorProductionAttribute::Total { key } => {
                    keys.define(key, ProvenanceRole::FunctionTotal)?;
                }
                DescriptorProductionAttribute::Hook { key, .. }
                | DescriptorProductionAttribute::RawHook { key, .. } => {
                    keys.define(key, ProvenanceRole::FunctionHook)?;
                }
                DescriptorProductionAttribute::Memo { key } => {
                    keys.define(key, ProvenanceRole::FunctionMemo)?;
                }
                DescriptorProductionAttribute::FreshGenerator { key } => {
                    keys.define(key, ProvenanceRole::FunctionFreshGenerator)?;
                }
                DescriptorProductionAttribute::Smtlib { key, .. } => {
                    keys.define(key, ProvenanceRole::FunctionSmtlib)?;
                }
                DescriptorProductionAttribute::Underspecified { key, .. } => {
                    keys.define(key, ProvenanceRole::FunctionUnderspecified)?;
                }
                DescriptorProductionAttribute::SmtHook { key, template } => {
                    keys.define(key, ProvenanceRole::FunctionSmtHook)?;
                    for key in template.iter().filter_map(|fragment| fragment.key.as_ref()) {
                        keys.define(key, ProvenanceRole::SmtHookPlaceholder)?;
                    }
                }
                DescriptorProductionAttribute::ListCons {
                    key,
                    separator_key,
                    separator,
                    non_empty,
                    terminator,
                } => {
                    keys.define(key, ProvenanceRole::ListDeclaration)?;
                    // The separator's terminal item defines its key; a list
                    // without separator has no such item.
                    if separator.is_empty() {
                        keys.define(separator_key, ProvenanceRole::ListSeparator)?;
                    } else {
                        keys.refer(separator_key, ProvenanceRole::ListSeparator)?;
                    }
                    if let Some(non_empty) = non_empty {
                        keys.define(non_empty, ProvenanceRole::ListNonEmpty)?;
                    }
                    keys.refer(&terminator.key, ProvenanceRole::ListDeclaration)?;
                }
                DescriptorProductionAttribute::ListTerminator { cons } => {
                    // The terminator's `.Sort` terminal defines the key.
                    keys.refer(&cons.key, ProvenanceRole::ListDeclaration)?;
                }
                DescriptorProductionAttribute::ConsList { key, empty } => {
                    keys.define(key, ProvenanceRole::ConsListDeclaration)?;
                    keys.refer(&empty.key, ProvenanceRole::ConsListDeclaration)?;
                }
                DescriptorProductionAttribute::Alias { key, recursive } => {
                    keys.define(key, ProvenanceRole::AliasProduction)?;
                    if let Some(recursive) = recursive {
                        keys.define(recursive, ProvenanceRole::StaticRecursive)?;
                    }
                }
                DescriptorProductionAttribute::Desugar { key, recursive } => {
                    keys.define(key, ProvenanceRole::DesugarProduction)?;
                    if let Some(recursive) = recursive {
                        keys.define(recursive, ProvenanceRole::StaticRecursive)?;
                    }
                }
                DescriptorProductionAttribute::Internal { key } => {
                    keys.define(key, ProvenanceRole::ConstructorInternal)?;
                }
                DescriptorProductionAttribute::Program { key } => {
                    keys.define(key, ProvenanceRole::ConstructorProgram)?;
                }
                DescriptorProductionAttribute::Color { key, .. } => {
                    keys.define(key, ProvenanceRole::ConstructorColor)?;
                }
                DescriptorProductionAttribute::Colors { key, values } => {
                    keys.define(key, ProvenanceRole::ConstructorColor)?;
                    for entry in values {
                        keys.define(&entry.key, ProvenanceRole::ConstructorColorsEntry)?;
                    }
                }
                DescriptorProductionAttribute::Token { .. }
                | DescriptorProductionAttribute::Bracket { .. } => {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::ConstructorHasTokenOrBracketMetadata,
                    ));
                }
            }
        }
        Ok(())
    }
}

impl StructuredRuleDescriptor {
    pub(crate) const fn expected_primary_key() -> ProvenanceKey {
        ProvenanceKey::new(ProvenanceRole::RuleDeclaration, 0)
    }

    /// The provenance role of the `label` key: a context's (KF-021) or a
    /// rule's.
    fn label_role(&self) -> ProvenanceRole {
        if self.sentence_kind == SentenceKind::Context {
            ProvenanceRole::ContextLabel
        } else {
            ProvenanceRole::RuleLabel
        }
    }

    /// Defines the marker, hole, and result-sort keys of a heat or cool
    /// rule (KF-014).
    fn collect_evaluation_keys(&self, keys: &mut WireKeys) -> Result<(), GrammarTransportError> {
        if let Some(step) = &self.evaluation {
            keys.define(&step.key, step.kind.role())?;
            keys.define(&step.hole_key, step.kind.hole_role())?;
            if let Some(sort) = &step.result {
                keys.define(&sort.key, step.kind.result_role())?;
            }
        }
        Ok(())
    }

    /// The keys of the rule's wire nodes, with the kind's fixed declaration
    /// keys: the rule's, and an alias's or a desugar's clause.
    pub(crate) fn wire_keys(&self) -> Result<WireKeys, GrammarTransportError> {
        let mut keys = WireKeys::default();
        keys.fixed(ProvenanceRole::RuleDeclaration)?;
        if self.sentence_kind == SentenceKind::Alias {
            keys.fixed(ProvenanceRole::AliasClause)?;
        }
        if self.sentence_kind == SentenceKind::Desugar {
            keys.fixed(ProvenanceRole::DesugarClause)?;
        }
        if let Some(label) = &self.label {
            keys.define(&label.key, self.label_role())?;
        }
        if let Some(requires) = &self.requires {
            keys.define(&requires.key, ProvenanceRole::RuleRequires)?;
        }
        if let Some(priority) = &self.priority {
            let role = priority.role_for(self.sentence_kind).unwrap_or(
                if self.sentence_kind == SentenceKind::Transition {
                    ProvenanceRole::RuleOwise
                } else {
                    ProvenanceRole::EquationPriority
                },
            );
            keys.define(&priority.key, role)?;
        }
        if let Some(nondet) = &self.nondet {
            keys.define(&nondet.key, ProvenanceRole::RuleNondetGroup)?;
        }
        if let Some(anywhere) = &self.anywhere {
            keys.define(anywhere, ProvenanceRole::RuleAnywhere)?;
        }
        self.collect_evaluation_keys(&mut keys)?;
        if let Some(simplification) = &self.simplification {
            keys.define(&simplification.key, ProvenanceRole::SimplificationMarker)?;
            if let Some(priority) = &simplification.priority {
                keys.define(&priority.key, ProvenanceRole::SimplificationPriority)?;
            }
            if let Some(restriction) = &simplification.restriction {
                restriction.collect_wire_keys(&mut keys)?;
            }
        }
        if let Some(equation) = &self.equation {
            equation.restriction.collect_wire_keys(&mut keys)?;
        }
        if let Some(unbound) = &self.unbound_variables {
            unbound.collect_wire_keys(&mut keys)?;
        }
        keys.define(&self.pattern_key, ProvenanceRole::RulePattern)?;
        for binding in &self.typed_bindings {
            keys.define(&binding.key, ProvenanceRole::RuleBindingParameter)?;
            keys.define(&binding.sort.key, ProvenanceRole::RuleBindingType)?;
        }
        keys.define(&self.subject_sort.key, ProvenanceRole::RuleType)?;
        if let Some(result_sort) = &self.result_sort {
            keys.define(&result_sort.key, ProvenanceRole::RuleResultType)?;
        }
        if let Some(result_key) = &self.result_key {
            keys.define(result_key, ProvenanceRole::RuleResult)?;
        }
        self.subject
            .collect_wire_term_keys(&mut keys, ValidationSide::Left)?;
        if let Some(context) = &self.function_context {
            context.collect_keys(&mut keys)?;
        }
        if let Some(result_term) = &self.result {
            result_term.collect_wire_term_keys(&mut keys, ValidationSide::Right)?;
        }
        self.collect_condition_keys(&mut keys)?;
        Ok(keys)
    }

    /// The keys of a rule's requires condition, then of a transition's
    /// existentials and ensures condition.
    fn collect_condition_keys(&self, keys: &mut WireKeys) -> Result<(), GrammarTransportError> {
        if let Some(requires) = &self.requires {
            requires
                .term
                .collect_wire_term_keys(keys, ValidationSide::Requires)?;
        }
        for binder in &self.existentials {
            keys.define(
                &binder.declaration_key,
                ProvenanceRole::RuleExistentialBinder,
            )?;
            keys.define(&binder.name_key, ProvenanceRole::RuleExistentialBinderName)?;
            keys.define(&binder.sort.key, ProvenanceRole::RuleExistentialBinderSort)?;
        }
        for binder in &self.fresh {
            keys.define(&binder.declaration_key, ProvenanceRole::RuleFreshBinder)?;
            keys.define(&binder.name_key, ProvenanceRole::RuleFreshBinderName)?;
            keys.define(&binder.sort.key, ProvenanceRole::RuleFreshBinderSort)?;
        }
        if let Some(ensures) = &self.ensures {
            keys.define(&ensures.key, ProvenanceRole::RuleEnsures)?;
            ensures
                .term
                .collect_wire_term_keys(keys, ValidationSide::RuleEnsures)?;
        }
        Ok(())
    }
}

/// Whether `value` is a rule label spelling: an ASCII letter followed by ASCII letters, digits, `_`, or `-`.
///
/// Descriptor rule labels and Semantic IR rule labels (crate `krs-ir-levels`) accept exactly these spellings.
#[must_use]
pub fn valid_rule_label_name(value: &str) -> bool {
    value
        .bytes()
        .next()
        .is_some_and(|byte| byte.is_ascii_alphabetic())
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
}

impl DescriptorTerm {
    /// Collects the keys of a term on `side`, each checked for its node's
    /// role on that side.
    fn collect_wire_term_keys(
        &self,
        keys: &mut WireKeys,
        side: ValidationSide,
    ) -> Result<(), GrammarTransportError> {
        collect_term_keys(self, side, TermKeying::Grammar, keys)
    }
}

/// Collects a constant's keys: its type, its value expression, and its
/// value's nodes, which are keyed as the nodes of a rule result are.
pub(super) fn collect_constant_keys(
    constant: &super::constant::ConstantDescriptor,
    keys: &mut WireKeys,
) -> Result<(), GrammarTransportError> {
    keys.define(&constant.sort.key, ProvenanceRole::ConstantType)?;
    constant.sort.sort.validate()?;
    if let Some(reason) = configuration_term(&constant.value) {
        return Err(GrammarTransportError::InvalidTerm(reason));
    }
    keys.define(&constant.value_key, ProvenanceRole::ConstantValue)?;
    constant
        .value
        .collect_wire_term_keys(keys, ValidationSide::Right)
}

/// Why `term` is no grammar term, if it holds a node only configuration
/// rules hold: a claim term or a complete cell term. A structured rule's
/// terms are refused these by their validation; a constant's value has no
/// other check.
fn configuration_term(term: &DescriptorTerm) -> Option<GrammarTermReason> {
    match term {
        DescriptorTerm::Anonymous { .. } | DescriptorTerm::OrBool { .. } => {
            Some(GrammarTermReason::UnexpectedClaimTerm)
        }
        DescriptorTerm::Cell { .. } => {
            Some(GrammarTermReason::CompleteCellTermsRequireConfigurationRules)
        }
        _ => super::validation::term_children(term)
            .into_iter()
            .find_map(configuration_term),
    }
}

fn validate_sort_reference(
    reference: &DescriptorSortReference,
    provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
) -> Result<(), GrammarTransportError> {
    require_key(&reference.key, provenance)?;
    reference.sort.validate()
}

fn validate_group_references<'a>(
    references: impl IntoIterator<Item = &'a DescriptorGroupReference>,
    provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    field: TransportField,
) -> Result<(), GrammarTransportError> {
    let mut references = references.into_iter().peekable();
    if references.peek().is_none() {
        return Err(GrammarTransportError::EmptyCollection(field));
    }
    let mut groups = BTreeSet::new();
    for reference in references {
        require_key(&reference.key, provenance)?;
        if !groups.insert(reference.group.clone()) {
            return Err(GrammarTransportError::DuplicateValue(field));
        }
    }
    Ok(())
}

fn require_key(
    key: &ProvenanceKey,
    provenance: impl Fn(&ProvenanceKey) -> bool,
) -> Result<(), GrammarTransportError> {
    if provenance(key) {
        Ok(())
    } else {
        Err(GrammarTransportError::MissingProvenance(key.clone()))
    }
}

#[cfg(test)]
mod traversal_tests {
    use super::{
        CellTermField, DescriptorApplicationHeadClass, DescriptorLiteral, Production,
        ProductionAttribute, ProductionItem, ProductionOwner, RuleCondition,
        StageGrammarDescriptor, StructuredRule, Term, TermArgument,
    };
    use crate::stage::{WireStage, tests::CountingMap};
    use crate::wire::{
        WireApplicationReference, WireContextAliasReference, WireSortReference, WireTypeReference,
    };
    use crate::{
        BuiltinSort, DescriptorAssociativitySentence, DescriptorFieldReference,
        DescriptorFormatFragment, DescriptorGroupReference, DescriptorLexicalPrecedence,
        DescriptorPrecedenceChain, FormatFragment, GroupAssociativity, HookOperation,
        ProductionFieldId, ProductionGroupId, ProvenanceKey, ProvenanceRole, SentenceKind,
        StrictnessKind,
    };

    macro_rules! assert_traversal {
        ($shape:expr, [$($call:literal),* $(,)?], $failure:literal) => {{
            let shape = $shape;
            let original = serde_json::to_vec(&shape).unwrap();
            let mut map = CountingMap::default();
            let mapped = shape.clone().try_map_refs::<WireStage, _>(&mut map).unwrap();
            assert_eq!(serde_json::to_vec(&mapped).unwrap(), original);
            assert_eq!(map.calls, [$($call),*]);
            let mut failing = CountingMap {
                fail: Some($failure),
                ..CountingMap::default()
            };
            assert_eq!(
                shape.try_map_refs::<WireStage, _>(&mut failing).unwrap_err(),
                $failure,
            );
            let expected_calls = [$($call),*];
            let first_failure = expected_calls.iter().position(|call| *call == $failure).unwrap();
            assert_eq!(failing.calls, expected_calls[..=first_failure]);
        }};
    }

    fn key(ordinal: u32) -> ProvenanceKey {
        ProvenanceKey::new(ProvenanceRole::RuleLeftReference, ordinal)
    }

    fn field() -> ProductionFieldId {
        ProductionFieldId::new("value").unwrap()
    }

    fn nominal() -> WireTypeReference {
        WireTypeReference {
            slot: crate::wire::TypeSlot(3),
            authored_path: "State".to_owned(),
        }
    }

    fn sort() -> WireSortReference {
        WireSortReference {
            key: key(1),
            target: nominal(),
        }
    }

    fn application() -> WireApplicationReference {
        WireApplicationReference {
            key: key(2),
            target: crate::wire::TargetSlot(5),
            authored_path: "Add".to_owned(),
        }
    }

    fn anonymous() -> Term<WireStage> {
        Term::Anonymous {
            key: key(3),
            sort: sort(),
            spelling_key: key(13),
            spelling: "_".to_owned(),
        }
    }

    fn group() -> DescriptorGroupReference {
        DescriptorGroupReference {
            key: key(4),
            group: ProductionGroupId::new("arithmetic").unwrap(),
        }
    }

    fn nonterminal() -> ProductionItem<WireStage> {
        ProductionItem::NonTerminal {
            key: key(5),
            field_key: key(6),
            declaration_key: Some(key(7)),
            field: field(),
            sort: Box::new(sort()),
        }
    }

    fn strictness() -> ProductionAttribute<WireStage> {
        ProductionAttribute::Strictness {
            key: key(8),
            kind: StrictnessKind::SeqStrict,
            using: Some(WireContextAliasReference {
                key: key(9),
                slot: crate::wire::ItemSlot(7),
            }),
            fields: vec![DescriptorFieldReference {
                key: key(10),
                field: field(),
            }],
            result_sort: Box::new(sort()),
        }
    }

    fn production() -> Production<WireStage> {
        Production {
            parameters: Vec::new(),
            key: key(11),
            template_key: Some(key(12)),
            owner: ProductionOwner::Constructor {
                constructor: application(),
            },
            result_sort: sort(),
            items: vec![nonterminal()],
            attributes: vec![strictness()],
        }
    }

    #[test]
    fn term_traversal_covers_every_variant_and_stops_on_reference_error() {
        let term = Term::<WireStage>::OrBool {
            key: key(0),
            arguments: vec![
                Term::Variable {
                    key: key(1),
                    path_key: key(2),
                    name: "bound".to_owned(),
                },
                Term::Application {
                    instance: Vec::new(),
                    head_class: DescriptorApplicationHeadClass::Applied,
                    reference: application(),
                    path_key: key(3),
                    arguments: vec![TermArgument::Positional {
                        value: Box::new(anonymous()),
                    }]
                    .try_into()
                    .unwrap(),
                    update: None,
                    open: false,
                },
                Term::Literal {
                    key: key(4),
                    literal: DescriptorLiteral::Int("42".to_owned()),
                },
                Term::Wildcard { key: key(5) },
                Term::BuiltinToken {
                    key: key(6),
                    sort: BuiltinSort::Bytes,
                    value: "0xff".to_owned(),
                },
                anonymous(),
                Term::OrBool {
                    key: key(7),
                    arguments: vec![anonymous(), anonymous()].try_into().unwrap(),
                },
                Term::Cell {
                    key: key(8),
                    path_key: key(14),
                    declaration: nominal(),
                    fields: vec![CellTermField {
                        key: key(9),
                        field: field(),
                        value: Box::new(anonymous()),
                    }],
                    open: false,
                    update: None,
                },
            ]
            .try_into()
            .unwrap(),
        };
        assert_traversal!(
            term,
            [
                "application",
                "sort",
                "sort",
                "sort",
                "sort",
                "nominal",
                "sort"
            ],
            "nominal"
        );
    }

    #[test]
    fn term_arguments_map_positional_and_named_values() {
        let positional = TermArgument::<WireStage>::Positional {
            value: Box::new(anonymous()),
        };
        assert_traversal!(positional, ["sort"], "sort");
        let named = TermArgument::<WireStage>::Named {
            key: key(0),
            field: field(),
            value: Box::new(anonymous()),
        };
        assert_traversal!(named, ["sort"], "sort");
    }

    #[test]
    fn cell_term_field_maps_its_nested_value() {
        let field = CellTermField::<WireStage> {
            key: key(0),
            field: field(),
            value: Box::new(anonymous()),
        };
        assert_traversal!(field, ["sort"], "sort");
    }

    #[test]
    fn rule_condition_maps_its_term() {
        let condition = RuleCondition::<WireStage> {
            key: key(0),
            term: anonymous(),
        };
        assert_traversal!(condition, ["sort"], "sort");
    }

    #[test]
    fn structured_rule_maps_condition_sorts_and_both_terms() {
        let rule = StructuredRule::<WireStage> {
            sentence_kind: SentenceKind::Equation,
            label: None,
            requires: Some(RuleCondition {
                key: key(0),
                term: anonymous(),
            }),
            priority: None,
            nondet: None,
            anywhere: None,
            simplification: None,
            pattern_key: key(1),
            typed_bindings: vec![],
            result_key: Some(key(2)),
            subject_sort: sort(),
            result_sort: Some(sort()),
            bindings: vec!["bound".to_owned()],
            subject: anonymous(),
            result: Some(anonymous()),
            existentials: Vec::new(),
            ensures: None,
            fresh: Vec::new(),
            equation: None,
            unbound_variables: None,
            function_context: None,
            predicate: false,
            evaluation: None,
        };
        assert_traversal!(rule, ["sort", "sort", "sort", "sort", "sort"], "sort");
    }

    #[test]
    fn production_items_map_sorts_and_preserve_terminal_payloads() {
        assert_traversal!(nonterminal(), ["sort"], "sort");
        let items: [ProductionItem<WireStage>; 2] = [
            ProductionItem::Terminal {
                key: key(0),
                text: "token".to_owned(),
            },
            ProductionItem::RegexTerminal {
                key: key(1),
                precede_regex: Some("before".to_owned()),
                regex: "[a-z]+".to_owned(),
                follow_regex: None,
            },
        ];
        for item in items {
            let original = serde_json::to_vec(&item).unwrap();
            let mut map = CountingMap::default();
            let mapped = item.try_map_refs::<WireStage, _>(&mut map).unwrap();
            assert_eq!(serde_json::to_vec(&mapped).unwrap(), original);
            assert!(map.calls.is_empty());
        }
    }

    #[test]
    fn production_attributes_map_aliases_and_sorts_and_preserve_metadata() {
        assert_traversal!(strictness(), ["context_alias", "sort"], "context_alias");
        let attributes: [ProductionAttribute<WireStage>; 10] = [
            ProductionAttribute::Documentation {
                key: key(0),
                text: "Documentation".to_owned(),
            },
            ProductionAttribute::Function { key: key(1) },
            ProductionAttribute::Total { key: key(2) },
            ProductionAttribute::Hook {
                key: key(3),
                operation: HookOperation::KryptoSha256Raw,
            },
            ProductionAttribute::Alias {
                key: key(4),
                recursive: None,
            },
            ProductionAttribute::Token {
                key: key(5),
                lexical_precedence: Some(DescriptorLexicalPrecedence {
                    key: key(6),
                    value: 42,
                }),
            },
            ProductionAttribute::Group { reference: group() },
            ProductionAttribute::Bracket { key: key(7) },
            ProductionAttribute::Avoid { key: key(8) },
            ProductionAttribute::Format {
                key: key(9),
                fragments: vec![DescriptorFormatFragment {
                    key: key(10),
                    fragment: FormatFragment::Item(1),
                }],
            },
        ];
        for attribute in attributes {
            let original = serde_json::to_vec(&attribute).unwrap();
            let mut map = CountingMap::default();
            let mapped = attribute.try_map_refs::<WireStage, _>(&mut map).unwrap();
            assert_eq!(serde_json::to_vec(&mapped).unwrap(), original);
            assert!(map.calls.is_empty());
        }
        let ProductionAttribute::Strictness {
            key,
            kind,
            fields,
            result_sort,
            ..
        } = strictness()
        else {
            unreachable!();
        };
        let without_alias = ProductionAttribute::<WireStage>::Strictness {
            key,
            kind,
            using: None,
            fields,
            result_sort,
        };
        assert_traversal!(without_alias, ["sort"], "sort");
    }

    #[test]
    fn production_owners_map_every_reference_variant() {
        let constructor = ProductionOwner::<WireStage>::Constructor {
            constructor: application(),
        };
        assert_traversal!(constructor, ["application"], "application");
        let token = ProductionOwner::<WireStage>::TokenSort { sort: sort() };
        assert_traversal!(token, ["sort"], "sort");
        let bracket = ProductionOwner::<WireStage>::BracketSort { sort: sort() };
        assert_traversal!(bracket, ["sort"], "sort");
    }

    #[test]
    fn production_maps_owner_items_attributes_and_result() {
        assert_traversal!(
            production(),
            ["application", "sort", "context_alias", "sort", "sort"],
            "context_alias"
        );
    }

    #[test]
    fn grammar_descriptor_maps_references_and_preserves_group_sentences() {
        let production = StageGrammarDescriptor::<WireStage>::Production(production());
        assert_traversal!(
            production,
            ["application", "sort", "context_alias", "sort", "sort"],
            "context_alias"
        );
        let subsort = StageGrammarDescriptor::<WireStage>::Subsort {
            key: key(0),
            subsort: sort(),
            supersort: sort(),
        };
        assert_traversal!(subsort, ["sort", "sort"], "sort");
        let descriptors = [
            StageGrammarDescriptor::<WireStage>::Precedence {
                key: key(1),
                chains: vec![DescriptorPrecedenceChain {
                    key: key(2),
                    groups: crate::AtLeastTwo::new(group(), group(), Vec::new()),
                }],
            },
            StageGrammarDescriptor::Associativity {
                key: key(3),
                sentences: vec![DescriptorAssociativitySentence {
                    key: key(4),
                    associativity: GroupAssociativity::Left,
                    groups: vec![group()],
                }],
            },
        ];
        for descriptor in descriptors {
            let original = serde_json::to_vec(&descriptor).unwrap();
            let mut map = CountingMap::default();
            let mapped = descriptor.try_map_refs::<WireStage, _>(&mut map).unwrap();
            assert_eq!(serde_json::to_vec(&mapped).unwrap(), original);
            assert!(map.calls.is_empty());
        }
    }
}

#[cfg(test)]
mod literal_tests {
    use super::{DescriptorLiteral, GrammarTransportError};

    #[test]
    fn int_literals_are_canonical_signed_decimals() {
        for value in [
            "0",
            "7",
            "-1",
            "-1000",
            "1234567890123456789012345678901234567890",
        ] {
            assert_eq!(
                DescriptorLiteral::Int(value.into()).validate(),
                Ok(()),
                "{value}"
            );
        }
        for value in ["", "-", "-0", "007", "-01", "+1", "1_000", "--1", "1-"] {
            assert_eq!(
                DescriptorLiteral::Int(value.into()).validate(),
                Err(GrammarTransportError::InvalidLiteral),
                "{value}"
            );
        }
    }
}

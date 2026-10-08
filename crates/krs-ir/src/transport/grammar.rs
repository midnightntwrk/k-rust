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
use crate::host::{HostItemId, HostTypeKey, HostTypeReference};
use crate::stage::{DescriptorStage, HostStage, stage_shape};
use crate::{
    BuiltinOperation, BuiltinSort, FormatFragment, GroupAssociativity, HookOperation, ItemKind,
    ListOperation, ProductionFieldId, ProductionGroupId, ProvenanceKey, ProvenanceRole,
    SentenceKind, SetOperation, StableItemId, StrictnessKind, TermMapOperation,
};

/// Versioned stable-ID disambiguator prefix for enum constructor variants.
///
/// A variant descriptor uses the variant identifier as `item_name` (so the
/// emitted K label remains `true`, `false`, and so on) and
/// `enum:<owning-enum>` as its disambiguator. This distinguishes
/// `Boolean::False` from both a same-module `struct False` and
/// `OtherBoolean::False` without putting `::` into an identity component.
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
            serialize = "S::Sort: Serialize, S::ContextAlias: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::ContextAlias: Deserialize<'de>"
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
    }
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
    }
    map_order: [key, template_key, owner, items, attributes, result_sort];
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
    }
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
        /// One fresh typed anonymous-variable occurrence.
        Anonymous {
            /// Complete occurrence provenance.
            key: ProvenanceKey => [keep],
            /// Exact authored sort occurrence.
            sort: S::Sort => [sort],
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
            /// Exact nominal `#[k::cell]` declaration reference.
            declaration: S::Nominal => [nominal],
            /// Authored child values; semantic lowering validates completeness and order.
            fields: Vec<CellTermField<S>> => [vec nested],
        },
    }
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

stage_shape! {
    /// Structured relational sentence.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "StructuredRuleDescriptor",
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize, S::Nominal: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::Nominal: Deserialize<'de>"
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
        /// Complete result-expression provenance.
        pub result_key: ProvenanceKey => [keep],
        /// Exact authored subject sort.
        pub subject_sort: S::Sort => [sort],
        /// Exact authored result sort.
        pub result_sort: S::Sort => [sort],
        /// Bound names in deterministic pattern preorder.
        pub bindings: Vec<String> => [keep],
        /// Structured left pattern.
        pub subject: Term<S> => [nested],
        /// Structured right result.
        pub result: Term<S> => [nested],
    }
}

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
    /// A nested node used a parser key other than its exact required
    /// role/ordinal.
    UnexpectedProvenance {
        /// Required parser key.
        expected: ProvenanceKey,
        /// Supplied parser key.
        actual: ProvenanceKey,
    },
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
                "expected provenance `{}#{}`, found `{}#{}`",
                expected.role(),
                expected.ordinal(),
                actual.role(),
                actual.ordinal()
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

impl DescriptorSortRef {
    /// Checks the stable namespace of a declared sort.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarTransportError::SortReferenceKind`] when a declared
    /// target is not a sort identity.
    pub fn validate(&self) -> Result<(), GrammarTransportError> {
        if let Self::Declared(id) = self
            && id.item_kind() != ItemKind::Sort
        {
            return Err(GrammarTransportError::SortReferenceKind(id.item_kind()));
        }
        Ok(())
    }
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
}

impl DescriptorLiteral {
    pub(super) fn validate(&self) -> Result<(), GrammarTransportError> {
        match self {
            Self::Int(value) if is_canonical_int(value) => Ok(()),
            Self::Bool(_) => Ok(()),
            Self::String(value) if crate::string_token::encode(value).is_ok() => Ok(()),
            Self::Int(_) | Self::String(_) => Err(GrammarTransportError::InvalidLiteral),
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
        DescriptorApplicationRef::Declared(_) | DescriptorApplicationRef::Builtin(_) => {
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
            },
        )
    }
}

impl StructuredRuleDescriptor {
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
        Ok(())
    }

    /// Validates local rule shape and all parser-keyed nested nodes.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarTransportError`] for wrong ownership, typed references,
    /// bindings, terms, literals, or missing provenance.
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
            if self.sentence_kind == SentenceKind::Alias {
                return Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::StaticAliasRequires,
                ));
            }
        }
        self.validate_rule_keys(provenance)?;
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
        } else if self.sentence_kind == SentenceKind::Simplification {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::MissingSimplificationMetadata,
            ));
        }
        require_key(&self.subject_sort.key, provenance)?;
        require_key(&self.result_sort.key, provenance)?;
        require_key(&self.pattern_key, provenance)?;
        require_key(&self.result_key, provenance)?;
        self.subject_sort.sort.validate()?;
        self.result_sort.sort.validate()?;
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
        let mut subject_variables = BTreeSet::new();
        self.subject
            .validate(provenance, &bindings, &mut subject_variables, true)?;
        if subject_variables != bindings {
            let missing = bindings
                .difference(&subject_variables)
                .next()
                .cloned()
                .unwrap_or_default();
            return Err(GrammarTransportError::InvalidBinding(missing));
        }
        let mut result_variables = BTreeSet::new();
        self.result
            .validate(provenance, &bindings, &mut result_variables, false)?;
        if let Some(requires) = &self.requires {
            let mut condition_variables = BTreeSet::new();
            requires
                .term
                .validate(provenance, &bindings, &mut condition_variables, false)?;
        }
        Ok(())
    }
}

impl GrammarDescriptor {
    pub(crate) fn expected_primary_key(&self) -> ProvenanceKey {
        match self {
            Self::Production(production) => match production.owner {
                DescriptorProductionOwner::Constructor { .. } => {
                    canonical_key(ProvenanceRole::ConstructorDeclaration, 0)
                }
                DescriptorProductionOwner::TokenSort { .. } => {
                    canonical_key(ProvenanceRole::TokenDeclaration, 0)
                }
                DescriptorProductionOwner::BracketSort { .. } => {
                    canonical_key(ProvenanceRole::BracketDeclaration, 0)
                }
            },
            Self::Subsort { .. } => canonical_key(ProvenanceRole::SubsortDeclaration, 0),
            Self::Precedence { .. } => canonical_key(ProvenanceRole::PrecedenceDeclaration, 0),
            Self::Associativity { .. } => {
                canonical_key(ProvenanceRole::AssociativityDeclaration, 0)
            }
        }
    }

    /// Validates local grammar shape and every nested provenance/reference.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarTransportError`] for wrong ownership, malformed
    /// productions/relations, typed references, or missing provenance.
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
            Self::Production(production) => production.validate(provenance),
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
            DescriptorProductionOwner::TokenSort { sort }
            | DescriptorProductionOwner::BracketSort { sort } => {
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
                DescriptorProductionAttribute::Hook { key, .. } => {
                    require_key(key, provenance)?;
                    "hook"
                }
                DescriptorProductionAttribute::Alias { key } => {
                    require_key(key, provenance)?;
                    "alias"
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
        if families.contains("alias") && families.contains("function") {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::AliasFunctionMetadata,
            ));
        }
        if families.contains("internal") && families.contains("program") {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::InternalProgramMetadata,
            ));
        }
        if families.contains("prefer") && families.contains("avoid") {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::PreferAvoidMetadata,
            ));
        }
        let regex_count = self
            .items
            .iter()
            .filter(|item| matches!(item, DescriptorProductionItem::RegexTerminal { .. }))
            .count();
        let has_token = families.contains("token");
        let has_bracket = families.contains("bracket");
        match &self.owner {
            DescriptorProductionOwner::TokenSort { .. } => {
                if regex_count != 1 || !has_token {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::TokenOwnerShape,
                    ));
                }
                let [
                    DescriptorProductionItem::RegexTerminal {
                        precede_regex,
                        follow_regex,
                        ..
                    },
                ] = self.items.as_slice()
                else {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::TokenRegexItemCount,
                    ));
                };
                if precede_regex.is_some() || follow_regex.is_some() {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::NominalTokenRegexGuards,
                    ));
                }
                Ok(())
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

impl GrammarDescriptor {
    pub(crate) fn expected_provenance_keys(
        &self,
    ) -> Result<BTreeSet<ProvenanceKey>, GrammarTransportError> {
        let mut keys = BTreeSet::new();
        match self {
            Self::Production(production) => production.collect_expected_keys(&mut keys)?,
            Self::Subsort {
                key,
                subsort,
                supersort,
            } => {
                insert_exact(&mut keys, key, ProvenanceRole::SubsortDeclaration, 0)?;
                insert_exact(&mut keys, &subsort.key, ProvenanceRole::SubsortSubSort, 0)?;
                insert_exact(
                    &mut keys,
                    &supersort.key,
                    ProvenanceRole::SubsortSuperSort,
                    0,
                )?;
            }
            Self::Precedence { key, chains } => {
                insert_exact(&mut keys, key, ProvenanceRole::PrecedenceDeclaration, 0)?;
                let mut group_ordinal = 0_u32;
                for (chain_ordinal, chain) in chains.iter().enumerate() {
                    insert_exact(
                        &mut keys,
                        &chain.key,
                        ProvenanceRole::PrecedenceChain,
                        checked_index(chain_ordinal)?,
                    )?;
                    for group in &chain.groups {
                        insert_exact(
                            &mut keys,
                            &group.key,
                            ProvenanceRole::PrecedenceGroupReference,
                            group_ordinal,
                        )?;
                        group_ordinal = increment(group_ordinal)?;
                    }
                }
            }
            Self::Associativity { key, sentences } => {
                insert_exact(&mut keys, key, ProvenanceRole::AssociativityDeclaration, 0)?;
                let mut group_ordinal = 0_u32;
                for (sentence_ordinal, sentence) in sentences.iter().enumerate() {
                    insert_exact(
                        &mut keys,
                        &sentence.key,
                        ProvenanceRole::AssociativitySentence,
                        checked_index(sentence_ordinal)?,
                    )?;
                    for group in &sentence.groups {
                        insert_exact(
                            &mut keys,
                            &group.key,
                            ProvenanceRole::AssociativityGroupReference,
                            group_ordinal,
                        )?;
                        group_ordinal = increment(group_ordinal)?;
                    }
                }
            }
        }
        Ok(keys)
    }
}

impl DescriptorProduction {
    #[expect(
        clippy::too_many_lines,
        reason = "One ordered pass retains exact provenance ordinals for every production owner."
    )]
    fn collect_expected_keys(
        &self,
        keys: &mut BTreeSet<ProvenanceKey>,
    ) -> Result<(), GrammarTransportError> {
        match &self.owner {
            DescriptorProductionOwner::Constructor { constructor } => {
                insert_exact(keys, &self.key, ProvenanceRole::ConstructorDeclaration, 0)?;
                insert_exact(
                    keys,
                    &constructor.key,
                    ProvenanceRole::ConstructorDeclaration,
                    0,
                )?;
                insert_exact(
                    keys,
                    &self.result_sort.key,
                    ProvenanceRole::ConstructorSort,
                    0,
                )?;
                if let Some(template_key) = &self.template_key {
                    insert_exact(keys, template_key, ProvenanceRole::ConstructorSyntax, 0)?;
                }
                self.collect_constructor_item_keys(keys)?;
                self.collect_constructor_attribute_keys(keys)
            }
            DescriptorProductionOwner::TokenSort { sort } => {
                insert_exact(keys, &self.key, ProvenanceRole::TokenDeclaration, 0)?;
                insert_exact(keys, &sort.key, ProvenanceRole::TokenDeclaration, 0)?;
                insert_exact(
                    keys,
                    &self.result_sort.key,
                    ProvenanceRole::TokenDeclaration,
                    0,
                )?;
                if self.template_key.is_some() {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::TokenSyntaxTemplate,
                    ));
                }
                let [DescriptorProductionItem::RegexTerminal { key, .. }] = self.items.as_slice()
                else {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::TokenRegexItemCount,
                    ));
                };
                insert_exact(keys, key, ProvenanceRole::TokenRegex, 0)?;
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
                insert_exact(keys, key, ProvenanceRole::TokenRegex, 0)?;
                if let Some(precedence) = lexical_precedence {
                    insert_exact(
                        keys,
                        &precedence.key,
                        ProvenanceRole::TokenLexicalPrecedence,
                        0,
                    )?;
                }
                Ok(())
            }
            DescriptorProductionOwner::BracketSort { sort } => {
                insert_exact(keys, &self.key, ProvenanceRole::BracketDeclaration, 0)?;
                insert_exact(keys, &sort.key, ProvenanceRole::SortDeclaration, 0)?;
                insert_exact(
                    keys,
                    &self.result_sort.key,
                    ProvenanceRole::SortDeclaration,
                    0,
                )?;
                if self.template_key.is_some() {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::BracketConstructorTemplate,
                    ));
                }
                let mut field_ordinal = 0_u32;
                for (item_ordinal, item) in self.items.iter().enumerate() {
                    match item {
                        DescriptorProductionItem::Terminal { key, .. }
                        | DescriptorProductionItem::RegexTerminal { key, .. } => {
                            insert_exact(
                                keys,
                                key,
                                ProvenanceRole::BracketSyntaxItem,
                                checked_index(item_ordinal)?,
                            )?;
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
                            insert_exact(
                                keys,
                                key,
                                ProvenanceRole::BracketSyntaxItem,
                                checked_index(item_ordinal)?,
                            )?;
                            insert_exact(
                                keys,
                                field_key,
                                ProvenanceRole::BracketValueReference,
                                field_ordinal,
                            )?;
                            insert_exact(keys, &sort.key, ProvenanceRole::SortDeclaration, 0)?;
                            field_ordinal = increment(field_ordinal)?;
                        }
                    }
                }
                let [DescriptorProductionAttribute::Bracket { key }] = self.attributes.as_slice()
                else {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::BracketMetadataShape,
                    ));
                };
                insert_exact(keys, key, ProvenanceRole::BracketDeclaration, 0)
            }
        }
    }

    fn collect_constructor_item_keys(
        &self,
        keys: &mut BTreeSet<ProvenanceKey>,
    ) -> Result<(), GrammarTransportError> {
        let explicit = self.template_key.is_some();
        let mut occurrence_ordinal = 0_u32;
        let mut declaration_ordinals = BTreeSet::new();
        for (item_ordinal, item) in self.items.iter().enumerate() {
            match item {
                DescriptorProductionItem::Terminal { key, .. } => {
                    if explicit {
                        insert_exact(
                            keys,
                            key,
                            ProvenanceRole::ConstructorSyntaxItem,
                            checked_index(item_ordinal)?,
                        )?;
                    } else {
                        insert_exact(keys, key, ProvenanceRole::ConstructorDeclaration, 0)?;
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
                    let declaration_ordinal = declaration_key.ordinal();
                    if !declaration_ordinals.insert(declaration_ordinal) {
                        return Err(GrammarTransportError::InvalidProduction(
                            GrammarProductionReason::DuplicateConstructorFieldOrdinal,
                        ));
                    }
                    insert_exact(
                        keys,
                        declaration_key,
                        ProvenanceRole::ConstructorFieldDeclaration,
                        if explicit {
                            declaration_ordinal
                        } else {
                            occurrence_ordinal
                        },
                    )?;
                    insert_exact(
                        keys,
                        &sort.key,
                        ProvenanceRole::ConstructorFieldSort,
                        declaration_ordinal,
                    )?;
                    if explicit {
                        insert_exact(
                            keys,
                            key,
                            ProvenanceRole::ConstructorSyntaxItem,
                            checked_index(item_ordinal)?,
                        )?;
                        insert_exact(
                            keys,
                            field_key,
                            ProvenanceRole::ConstructorSyntaxFieldReference,
                            occurrence_ordinal,
                        )?;
                    } else {
                        insert_exact(
                            keys,
                            key,
                            ProvenanceRole::ConstructorFieldDeclaration,
                            occurrence_ordinal,
                        )?;
                        insert_exact(
                            keys,
                            field_key,
                            ProvenanceRole::ConstructorFieldDeclaration,
                            occurrence_ordinal,
                        )?;
                    }
                    occurrence_ordinal = increment(occurrence_ordinal)?;
                }
                DescriptorProductionItem::RegexTerminal { .. } => {
                    return Err(GrammarTransportError::InvalidProduction(
                        GrammarProductionReason::ConstructorRegexItem,
                    ));
                }
            }
        }
        if declaration_ordinals != (0..occurrence_ordinal).collect::<BTreeSet<_>>() {
            return Err(GrammarTransportError::InvalidProduction(
                GrammarProductionReason::SparseConstructorFieldOrdinals,
            ));
        }
        Ok(())
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Keeps the exhaustive constructor attribute key catalog in one match."
    )]
    fn collect_constructor_attribute_keys(
        &self,
        keys: &mut BTreeSet<ProvenanceKey>,
    ) -> Result<(), GrammarTransportError> {
        let mut documentation_ordinal = 0_u32;
        for attribute in &self.attributes {
            match attribute {
                DescriptorProductionAttribute::Documentation { key, .. } => {
                    insert_exact(
                        keys,
                        key,
                        ProvenanceRole::ConstructorDocumentation,
                        documentation_ordinal,
                    )?;
                    documentation_ordinal = increment(documentation_ordinal)?;
                }
                DescriptorProductionAttribute::Group { reference } => {
                    insert_exact(keys, &reference.key, ProvenanceRole::ConstructorGroup, 0)?;
                }
                DescriptorProductionAttribute::Avoid { key } => {
                    insert_exact(keys, key, ProvenanceRole::ConstructorAvoid, 0)?;
                }
                DescriptorProductionAttribute::Prefer { key } => {
                    insert_exact(keys, key, ProvenanceRole::ConstructorPrefer, 0)?;
                }
                DescriptorProductionAttribute::Format { key, fragments } => {
                    insert_exact(keys, key, ProvenanceRole::ConstructorFormat, 0)?;
                    for (ordinal, fragment) in fragments.iter().enumerate() {
                        insert_exact(
                            keys,
                            &fragment.key,
                            ProvenanceRole::ConstructorFormatFragment,
                            checked_index(ordinal)?,
                        )?;
                    }
                }
                DescriptorProductionAttribute::Strictness {
                    key,
                    using,
                    fields,
                    result_sort,
                    ..
                } => {
                    insert_exact(keys, key, ProvenanceRole::StrictnessDeclaration, 0)?;
                    if let Some(using) = using {
                        insert_exact(
                            keys,
                            &using.key,
                            ProvenanceRole::StrictnessContextAliasReference,
                            0,
                        )?;
                    }
                    for (ordinal, field) in fields.iter().enumerate() {
                        insert_exact(
                            keys,
                            &field.key,
                            ProvenanceRole::StrictnessFieldReference,
                            checked_index(ordinal)?,
                        )?;
                    }
                    insert_exact(
                        keys,
                        &result_sort.key,
                        ProvenanceRole::StrictnessResultSort,
                        0,
                    )?;
                }
                DescriptorProductionAttribute::Function { key } => {
                    if key.role() == ProvenanceRole::FunctionDeclaration {
                        insert_exact(keys, key, ProvenanceRole::FunctionDeclaration, 0)?;
                    } else {
                        insert_exact(keys, key, ProvenanceRole::FunctionPartial, 0)?;
                    }
                }
                DescriptorProductionAttribute::Total { key } => {
                    insert_exact(keys, key, ProvenanceRole::FunctionTotal, 0)?;
                }
                DescriptorProductionAttribute::Hook { key, .. } => {
                    insert_exact(keys, key, ProvenanceRole::FunctionHook, 0)?;
                }
                DescriptorProductionAttribute::Alias { key } => {
                    insert_exact(keys, key, ProvenanceRole::AliasProduction, 0)?;
                }
                DescriptorProductionAttribute::Internal { key } => {
                    insert_exact(keys, key, ProvenanceRole::ConstructorInternal, 0)?;
                }
                DescriptorProductionAttribute::Program { key } => {
                    insert_exact(keys, key, ProvenanceRole::ConstructorProgram, 0)?;
                }
                DescriptorProductionAttribute::Color { key, .. } => {
                    insert_exact(keys, key, ProvenanceRole::ConstructorColor, 0)?;
                }
                DescriptorProductionAttribute::Colors { key, values } => {
                    insert_exact(keys, key, ProvenanceRole::ConstructorColor, 0)?;
                    for (ordinal, entry) in values.iter().enumerate() {
                        insert_exact(
                            keys,
                            &entry.key,
                            ProvenanceRole::ConstructorColorsEntry,
                            checked_index(ordinal)?,
                        )?;
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
    pub(crate) fn expected_primary_key() -> ProvenanceKey {
        canonical_key(ProvenanceRole::RuleDeclaration, 0)
    }

    pub(crate) fn expected_provenance_keys(
        &self,
    ) -> Result<BTreeSet<ProvenanceKey>, GrammarTransportError> {
        let mut keys = BTreeSet::new();
        insert_canonical(&mut keys, ProvenanceRole::RuleDeclaration, 0);
        if self.sentence_kind == SentenceKind::Alias {
            insert_canonical(&mut keys, ProvenanceRole::AliasClause, 0);
        }
        if let Some(label) = &self.label {
            insert_exact(&mut keys, &label.key, ProvenanceRole::RuleLabel, 0)?;
        }
        if let Some(requires) = &self.requires {
            insert_exact(&mut keys, &requires.key, ProvenanceRole::RuleRequires, 0)?;
        }
        if let Some(priority) = &self.priority {
            let role = priority.role_for(self.sentence_kind).unwrap_or(
                if self.sentence_kind == SentenceKind::Transition {
                    ProvenanceRole::RuleOwise
                } else {
                    ProvenanceRole::EquationPriority
                },
            );
            insert_exact(&mut keys, &priority.key, role, 0)?;
        }
        if let Some(nondet) = &self.nondet {
            insert_exact(&mut keys, &nondet.key, ProvenanceRole::RuleNondetGroup, 0)?;
        }
        if let Some(anywhere) = &self.anywhere {
            insert_exact(&mut keys, anywhere, ProvenanceRole::RuleAnywhere, 0)?;
        }
        if let Some(simplification) = &self.simplification {
            insert_exact(
                &mut keys,
                &simplification.key,
                ProvenanceRole::SimplificationMarker,
                0,
            )?;
            if let Some(priority) = &simplification.priority {
                insert_exact(
                    &mut keys,
                    &priority.key,
                    ProvenanceRole::SimplificationPriority,
                    0,
                )?;
            }
        }
        insert_exact(&mut keys, &self.pattern_key, ProvenanceRole::RulePattern, 0)?;
        insert_exact(
            &mut keys,
            &self.subject_sort.key,
            ProvenanceRole::RuleType,
            0,
        )?;
        insert_exact(
            &mut keys,
            &self.result_sort.key,
            ProvenanceRole::RuleResultType,
            0,
        )?;
        insert_exact(&mut keys, &self.result_key, ProvenanceRole::RuleResult, 0)?;
        let mut subject = TermKeyCounters::default();
        self.subject
            .collect_expected_term_keys(&mut keys, TermSide::Left, &mut subject)?;
        let mut result = TermKeyCounters::default();
        self.result
            .collect_expected_term_keys(&mut keys, TermSide::Right, &mut result)?;
        if let Some(requires) = &self.requires {
            let mut condition = TermKeyCounters::default();
            requires.term.collect_expected_term_keys(
                &mut keys,
                TermSide::Requires,
                &mut condition,
            )?;
        }
        Ok(keys)
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

#[derive(Clone, Copy)]
enum TermSide {
    Left,
    Right,
    Requires,
}

impl TermSide {
    const fn path_role(self) -> ProvenanceRole {
        match self {
            Self::Left => ProvenanceRole::RuleLeftPath,
            Self::Right => ProvenanceRole::RuleRightPath,
            Self::Requires => ProvenanceRole::RuleRequiresPath,
        }
    }
    const fn application_role(self) -> ProvenanceRole {
        match self {
            Self::Left => ProvenanceRole::RuleLeftApplicationHead,
            Self::Right => ProvenanceRole::RuleRightApplicationHead,
            Self::Requires => ProvenanceRole::RuleRequiresApplicationHead,
        }
    }
    const fn reference_role(self) -> ProvenanceRole {
        match self {
            Self::Left => ProvenanceRole::RuleLeftReference,
            Self::Right => ProvenanceRole::RuleRightReference,
            Self::Requires => ProvenanceRole::RuleRequiresReference,
        }
    }
    const fn literal_role(self) -> ProvenanceRole {
        match self {
            Self::Left => ProvenanceRole::RuleLeftLiteral,
            Self::Right => ProvenanceRole::RuleRightLiteral,
            Self::Requires => ProvenanceRole::RuleRequiresLiteral,
        }
    }
    const fn record_field_role(self) -> ProvenanceRole {
        match self {
            Self::Left => ProvenanceRole::RuleLeftRecordFieldName,
            Self::Right => ProvenanceRole::RuleRightRecordFieldName,
            Self::Requires => ProvenanceRole::RuleRequiresRecordFieldName,
        }
    }
    const fn wildcard_role(self) -> Option<ProvenanceRole> {
        match self {
            Self::Left => Some(ProvenanceRole::RuleLeftWildcard),
            Self::Right | Self::Requires => None,
        }
    }
}

#[derive(Default)]
struct TermKeyCounters {
    path: u32,
    application: u32,
    reference: u32,
    literal: u32,
    record_field: u32,
    wildcard: u32,
}

impl DescriptorTerm {
    fn collect_expected_term_keys(
        &self,
        keys: &mut BTreeSet<ProvenanceKey>,
        side: TermSide,
        counters: &mut TermKeyCounters,
    ) -> Result<(), GrammarTransportError> {
        super::validation::validate_term(
            self,
            &mut term_validation::TermProvenanceValidation {
                keys,
                side,
                counters,
            },
        )
    }
}

fn insert_exact(
    keys: &mut BTreeSet<ProvenanceKey>,
    actual: &ProvenanceKey,
    role: ProvenanceRole,
    ordinal: u32,
) -> Result<(), GrammarTransportError> {
    let expected = canonical_key(role, ordinal);
    if actual != &expected {
        return Err(GrammarTransportError::UnexpectedProvenance {
            expected,
            actual: actual.clone(),
        });
    }
    keys.insert(actual.clone());
    Ok(())
}

fn insert_canonical(keys: &mut BTreeSet<ProvenanceKey>, role: ProvenanceRole, ordinal: u32) {
    keys.insert(canonical_key(role, ordinal));
}

fn canonical_key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal)
}

fn checked_index(index: usize) -> Result<u32, GrammarTransportError> {
    u32::try_from(index).map_err(|_| {
        GrammarTransportError::InvalidProduction(
            GrammarProductionReason::ProvenanceOrdinalExceedsU32,
        )
    })
}

fn increment(value: u32) -> Result<u32, GrammarTransportError> {
    value
        .checked_add(1)
        .ok_or(GrammarTransportError::InvalidProduction(
            GrammarProductionReason::ProvenanceOrdinalExceedsU32,
        ))
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
                    head_class: DescriptorApplicationHeadClass::Applied,
                    reference: application(),
                    path_key: key(3),
                    arguments: vec![TermArgument::Positional {
                        value: Box::new(anonymous()),
                    }]
                    .try_into()
                    .unwrap(),
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
                    declaration: nominal(),
                    fields: vec![CellTermField {
                        key: key(9),
                        field: field(),
                        value: Box::new(anonymous()),
                    }],
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
            result_key: key(2),
            subject_sort: sort(),
            result_sort: sort(),
            bindings: vec!["bound".to_owned()],
            subject: anonymous(),
            result: anonymous(),
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
            ProductionAttribute::Alias { key: key(4) },
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

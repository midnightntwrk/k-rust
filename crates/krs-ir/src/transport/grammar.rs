//! Collector transport for typed object grammar and structured rule terms.
//!
//! These are transport types, not semantic IR. Nested nodes carry parser-owned
//! [`ProvenanceKey`] values which the compiler resolves through the enclosing
//! descriptor's provenance table. Rust references remain build-local in the
//! host forms and become declared-or-builtin identities before serialization.

use std::any::TypeId;
use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

use serde::{Deserialize, Serialize};

use crate::host::{HostItemId, HostTypeKey, HostTypeReference};
use crate::{
    BuiltinOperation, BuiltinSort, FormatFragment, GroupAssociativity, HookOperation, ItemKind,
    ListOperation, MapOperation, ProductionFieldId, ProductionGroupId, ProvenanceKey,
    ProvenanceRole, SentenceKind, SetOperation, StableItemId, StrictnessKind,
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
    Map(MapOperation),
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

/// One builtin sort marker registered by the author-facing facade.
#[derive(Clone, Copy, Debug)]
pub struct HostBuiltinSortRegistration {
    /// Target-neutral builtin identity.
    pub sort: BuiltinSort,
    /// Function producing the marker type's build-local identity.
    pub target: HostTypeKey,
}

/// One builtin operation marker registered by the author-facing facade.
#[derive(Clone, Copy, Debug)]
pub struct HostBuiltinOperationRegistration {
    /// Target-neutral builtin identity.
    pub operation: BuiltinOperation,
    /// Function producing the marker type's build-local identity.
    pub target: HostTypeKey,
}

/// One ordinary Map operation marker registered by the author-facing facade.
#[derive(Clone, Copy, Debug)]
pub struct HostMapOperationRegistration {
    /// Target-neutral Map operation identity.
    pub operation: MapOperation,
    /// Function producing the marker type's build-local identity.
    pub target: HostTypeKey,
}

/// One ordinary List operation marker registered by the author-facing facade.
#[derive(Clone, Copy, Debug)]
pub struct HostListOperationRegistration {
    /// Target-neutral List operation identity.
    pub operation: ListOperation,
    /// Function producing the marker type's build-local identity.
    pub target: HostTypeKey,
}

/// One ordinary Set operation marker registered by the author-facing facade.
#[derive(Clone, Copy, Debug)]
pub struct HostSetOperationRegistration {
    /// Target-neutral Set operation identity.
    pub operation: SetOperation,
    /// Function producing the marker type's build-local identity.
    pub target: HostTypeKey,
}

/// Complete host-only builtin catalog used for exact `TypeId` joins.
///
/// It is intentionally not serializable. A collector turns references into
/// [`DescriptorSortRef`] and [`DescriptorApplicationRef`] before emitting JSON.
#[derive(Clone, Debug)]
pub struct HostBuiltinRegistry {
    /// Registered sort markers.
    pub sorts: Vec<HostBuiltinSortRegistration>,
    /// Registered operation markers.
    pub operations: Vec<HostBuiltinOperationRegistration>,
    /// Registered ordinary Map operation markers.
    pub map_operations: Vec<HostMapOperationRegistration>,
    /// Registered ordinary List operation markers.
    pub list_operations: Vec<HostListOperationRegistration>,
    /// Registered ordinary Set operation markers.
    pub set_operations: Vec<HostSetOperationRegistration>,
}

impl HostBuiltinRegistry {
    /// Validates completeness, uniqueness, and separation of the two catalogs.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing/duplicate identity or any reused Rust
    /// marker `TypeId`. Alias paths remain valid because aliases preserve the
    /// same `TypeId`; no authored spelling participates in this check.
    pub fn validate(&self) -> Result<(), HostBuiltinRegistryError> {
        let mut sort_ids = BTreeSet::new();
        let mut operation_ids = BTreeSet::new();
        let mut map_operation_ids = BTreeSet::new();
        let mut list_operation_ids = BTreeSet::new();
        let mut set_operation_ids = BTreeSet::new();
        let mut rust_ids = BTreeSet::new();
        for registration in &self.sorts {
            if !sort_ids.insert(registration.sort) {
                return Err(HostBuiltinRegistryError::DuplicateSort(registration.sort));
            }
            if !rust_ids.insert(registration.target.resolve()) {
                return Err(HostBuiltinRegistryError::ReusedRustType);
            }
        }
        for registration in &self.operations {
            if !operation_ids.insert(registration.operation) {
                return Err(HostBuiltinRegistryError::DuplicateOperation(
                    registration.operation,
                ));
            }
            if !rust_ids.insert(registration.target.resolve()) {
                return Err(HostBuiltinRegistryError::ReusedRustType);
            }
        }
        for registration in &self.map_operations {
            if !MapOperation::TERM_APPLICATIONS.contains(&registration.operation) {
                return Err(HostBuiltinRegistryError::UnsupportedMapOperation(
                    registration.operation,
                ));
            }
            if !map_operation_ids.insert(registration.operation) {
                return Err(HostBuiltinRegistryError::DuplicateMapOperation(
                    registration.operation,
                ));
            }
            if !rust_ids.insert(registration.target.resolve()) {
                return Err(HostBuiltinRegistryError::ReusedRustType);
            }
        }
        for registration in &self.list_operations {
            if !ListOperation::TERM_APPLICATIONS.contains(&registration.operation) {
                return Err(HostBuiltinRegistryError::UnsupportedListOperation(
                    registration.operation,
                ));
            }
            if !list_operation_ids.insert(registration.operation) {
                return Err(HostBuiltinRegistryError::DuplicateListOperation(
                    registration.operation,
                ));
            }
            if !rust_ids.insert(registration.target.resolve()) {
                return Err(HostBuiltinRegistryError::ReusedRustType);
            }
        }
        for registration in &self.set_operations {
            if !SetOperation::TERM_APPLICATIONS.contains(&registration.operation) {
                return Err(HostBuiltinRegistryError::UnsupportedSetOperation(
                    registration.operation,
                ));
            }
            if !set_operation_ids.insert(registration.operation) {
                return Err(HostBuiltinRegistryError::DuplicateSetOperation(
                    registration.operation,
                ));
            }
            if !rust_ids.insert(registration.target.resolve()) {
                return Err(HostBuiltinRegistryError::ReusedRustType);
            }
        }
        for sort in BuiltinSort::ALL {
            if !sort_ids.contains(&sort) {
                return Err(HostBuiltinRegistryError::MissingSort(sort));
            }
        }
        for operation in BuiltinOperation::ALL {
            if !operation_ids.contains(&operation) {
                return Err(HostBuiltinRegistryError::MissingOperation(operation));
            }
        }
        for operation in MapOperation::TERM_APPLICATIONS {
            if !map_operation_ids.contains(&operation) {
                return Err(HostBuiltinRegistryError::MissingMapOperation(operation));
            }
        }
        for operation in ListOperation::TERM_APPLICATIONS {
            if !list_operation_ids.contains(&operation) {
                return Err(HostBuiltinRegistryError::MissingListOperation(operation));
            }
        }
        for operation in SetOperation::TERM_APPLICATIONS {
            if !set_operation_ids.contains(&operation) {
                return Err(HostBuiltinRegistryError::MissingSetOperation(operation));
            }
        }
        Ok(())
    }

    /// Resolves one build-local type as a builtin sort.
    #[must_use]
    pub fn resolve_sort(&self, target: TypeId) -> Option<BuiltinSort> {
        self.sorts
            .iter()
            .find(|registration| registration.target.resolve() == target)
            .map(|registration| registration.sort)
    }

    /// Resolves one build-local type as a builtin operation.
    #[must_use]
    pub fn resolve_operation(&self, target: TypeId) -> Option<BuiltinOperation> {
        self.operations
            .iter()
            .find(|registration| registration.target.resolve() == target)
            .map(|registration| registration.operation)
    }

    /// Resolves one build-local type as an ordinary Map operation.
    #[must_use]
    pub fn resolve_map_operation(&self, target: TypeId) -> Option<MapOperation> {
        self.map_operations
            .iter()
            .find(|registration| registration.target.resolve() == target)
            .map(|registration| registration.operation)
    }

    /// Resolves one build-local type as an ordinary List operation.
    #[must_use]
    pub fn resolve_list_operation(&self, target: TypeId) -> Option<ListOperation> {
        self.list_operations
            .iter()
            .find(|registration| registration.target.resolve() == target)
            .map(|registration| registration.operation)
    }

    /// Resolves one build-local type as an ordinary Set operation.
    #[must_use]
    pub fn resolve_set_operation(&self, target: TypeId) -> Option<SetOperation> {
        self.set_operations
            .iter()
            .find(|registration| registration.target.resolve() == target)
            .map(|registration| registration.operation)
    }
}

/// Invalid host builtin catalog.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostBuiltinRegistryError {
    /// A builtin sort identity occurred more than once.
    DuplicateSort(BuiltinSort),
    /// A builtin operation identity occurred more than once.
    DuplicateOperation(BuiltinOperation),
    /// A required builtin sort was absent.
    MissingSort(BuiltinSort),
    /// A required builtin operation was absent.
    MissingOperation(BuiltinOperation),
    /// A Map operation identity occurred more than once.
    DuplicateMapOperation(MapOperation),
    /// A required ordinary Map operation was absent.
    MissingMapOperation(MapOperation),
    /// A structural-only Map operation was registered as an ordinary term head.
    UnsupportedMapOperation(MapOperation),
    /// A List operation identity occurred more than once.
    DuplicateListOperation(ListOperation),
    /// A required ordinary List operation was absent.
    MissingListOperation(ListOperation),
    /// A structural-only List operation was registered as an ordinary term head.
    UnsupportedListOperation(ListOperation),
    /// A Set operation identity occurred more than once.
    DuplicateSetOperation(SetOperation),
    /// A required ordinary Set operation was absent.
    MissingSetOperation(SetOperation),
    /// A structural-only Set operation was registered as an ordinary term head.
    UnsupportedSetOperation(SetOperation),
    /// One Rust marker type was assigned two meanings.
    ReusedRustType,
}

impl fmt::Display for HostBuiltinRegistryError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateSort(sort) => write!(formatter, "duplicate builtin sort {sort}"),
            Self::DuplicateOperation(operation) => {
                write!(formatter, "duplicate builtin operation {operation}")
            }
            Self::MissingSort(sort) => write!(formatter, "missing builtin sort {sort}"),
            Self::MissingOperation(operation) => {
                write!(formatter, "missing builtin operation {operation}")
            }
            Self::DuplicateMapOperation(operation) => {
                write!(formatter, "duplicate {operation}")
            }
            Self::MissingMapOperation(operation) => {
                write!(formatter, "missing {operation}")
            }
            Self::UnsupportedMapOperation(operation) => {
                write!(formatter, "{operation} is not an ordinary term application")
            }
            Self::DuplicateListOperation(operation) => {
                write!(formatter, "duplicate {operation}")
            }
            Self::MissingListOperation(operation) => {
                write!(formatter, "missing {operation}")
            }
            Self::UnsupportedListOperation(operation) => {
                write!(formatter, "{operation} is not an ordinary term application")
            }
            Self::DuplicateSetOperation(operation) => {
                write!(formatter, "duplicate {operation}")
            }
            Self::MissingSetOperation(operation) => {
                write!(formatter, "missing {operation}")
            }
            Self::UnsupportedSetOperation(operation) => {
                write!(formatter, "{operation} is not an ordinary term application")
            }
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

/// Ordered grammar item in a structured production.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "item_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum DescriptorProductionItem {
    /// Literal concrete-syntax terminal.
    Terminal {
        /// Exact item provenance.
        key: ProvenanceKey,
        /// Nonempty terminal text.
        text: String,
    },
    /// Named nonterminal with a typed sort.
    NonTerminal {
        /// Exact ordered-item provenance.
        key: ProvenanceKey,
        /// Exact placeholder/name provenance.
        field_key: ProvenanceKey,
        /// Constructor field-declaration provenance, absent only for a
        /// compiler-owned bracket placeholder.
        #[serde(skip_serializing_if = "Option::is_none")]
        declaration_key: Option<ProvenanceKey>,
        /// Stable field identity.
        field: ProductionFieldId,
        /// Typed field sort and its Rust type-path provenance.
        sort: Box<DescriptorSortReference>,
    },
    /// K-compatible regex terminal.
    RegexTerminal {
        /// Exact regex-literal provenance.
        key: ProvenanceKey,
        /// Optional negative lookbehind guard.
        #[serde(skip_serializing_if = "Option::is_none")]
        precede_regex: Option<String>,
        /// Nonempty central regex.
        regex: String,
        /// Optional negative lookahead guard.
        #[serde(skip_serializing_if = "Option::is_none")]
        follow_regex: Option<String>,
    },
}

/// Host counterpart of [`DescriptorProductionItem`].
#[derive(Clone, Debug)]
pub enum HostProductionItem {
    /// Literal terminal.
    Terminal {
        /// Exact item provenance.
        key: ProvenanceKey,
        /// Nonempty terminal text.
        text: String,
    },
    /// Named nonterminal awaiting exact sort resolution.
    NonTerminal {
        /// Exact ordered-item provenance.
        key: ProvenanceKey,
        /// Exact placeholder/name provenance.
        field_key: ProvenanceKey,
        /// Constructor field-declaration provenance, absent for brackets.
        declaration_key: Option<ProvenanceKey>,
        /// Stable field identity.
        field: ProductionFieldId,
        /// Build-local sort reference.
        sort: Box<HostSortReference>,
    },
    /// Regex terminal.
    RegexTerminal {
        /// Exact regex-literal provenance.
        key: ProvenanceKey,
        /// Optional negative lookbehind guard.
        precede_regex: Option<String>,
        /// Nonempty central regex.
        regex: String,
        /// Optional negative lookahead guard.
        follow_regex: Option<String>,
    },
}

/// Classified production metadata transported without raw K attributes.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "attribute_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum DescriptorProductionAttribute {
    /// Literal production documentation carried from Rust rustdoc.
    Documentation {
        /// Documentation-line provenance.
        key: ProvenanceKey,
        /// One normalized documentation line.
        text: String,
    },
    /// Marks a production as a K function.
    Function {
        /// Function-marker provenance.
        key: ProvenanceKey,
    },
    /// Marks a functional production as total.
    Total {
        /// Totality-marker provenance.
        key: ProvenanceKey,
    },
    /// Selects one closed backend hook identity.
    Hook {
        /// Hook-selector provenance.
        key: ProvenanceKey,
        /// Closed hook identity.
        operation: HookOperation,
    },
    /// Marks a constructor production as a reversible static alias.
    Alias {
        /// Alias-marker provenance.
        key: ProvenanceKey,
    },
    /// Regex token production and optional lexical precedence.
    Token {
        /// Token-attribute provenance.
        key: ProvenanceKey,
        /// Optional lexical priority.
        #[serde(skip_serializing_if = "Option::is_none")]
        lexical_precedence: Option<DescriptorLexicalPrecedence>,
    },
    /// Nominal precedence/associativity group membership.
    Group {
        /// Group identity and authored location.
        reference: DescriptorGroupReference,
    },
    /// Syntax-only bracket marker.
    Bracket {
        /// Bracket-attribute provenance.
        key: ProvenanceKey,
    },
    /// Typed parser preference.
    Avoid {
        /// Avoid-attribute provenance.
        key: ProvenanceKey,
    },
    /// Structured unparse format.
    Format {
        /// Format-attribute provenance.
        key: ProvenanceKey,
        /// Ordered typed fragments with independent origins.
        fragments: Vec<DescriptorFormatFragment>,
    },
    /// Strict or sequentially strict evaluation metadata.
    Strictness {
        /// Strictness-attribute provenance.
        key: ProvenanceKey,
        /// Strict or sequentially strict strategy.
        kind: StrictnessKind,
        /// Optional selected context-alias declaration.
        #[serde(skip_serializing_if = "Option::is_none")]
        using: Option<DescriptorContextAliasReference>,
        /// Named fields in authored order.
        fields: Vec<DescriptorFieldReference>,
        /// Explicit result-predicate sort.
        result_sort: Box<DescriptorSortReference>,
    },
}

/// Host counterpart of [`DescriptorProductionAttribute`].
#[derive(Clone, Debug)]
pub enum HostProductionAttribute {
    /// Literal production documentation carried from Rust rustdoc.
    Documentation {
        /// Documentation-line provenance.
        key: ProvenanceKey,
        /// One normalized documentation line.
        text: String,
    },
    /// Marks a production as a K function.
    Function {
        /// Function-marker provenance.
        key: ProvenanceKey,
    },
    /// Marks a functional production as total.
    Total {
        /// Totality-marker provenance.
        key: ProvenanceKey,
    },
    /// Selects one closed backend hook identity.
    Hook {
        /// Hook-selector provenance.
        key: ProvenanceKey,
        /// Closed hook identity.
        operation: HookOperation,
    },
    /// Marks a constructor production as a reversible static alias.
    Alias {
        /// Alias-marker provenance.
        key: ProvenanceKey,
    },
    /// Regex token production and optional lexical precedence.
    Token {
        /// Token-attribute provenance.
        key: ProvenanceKey,
        /// Optional lexical priority.
        lexical_precedence: Option<DescriptorLexicalPrecedence>,
    },
    /// Nominal production-group membership.
    Group {
        /// Group identity and authored location.
        reference: DescriptorGroupReference,
    },
    /// Syntax-only bracket marker.
    Bracket {
        /// Bracket-attribute provenance.
        key: ProvenanceKey,
    },
    /// Typed parser preference.
    Avoid {
        /// Avoid-attribute provenance.
        key: ProvenanceKey,
    },
    /// Structured unparse format.
    Format {
        /// Format-attribute provenance.
        key: ProvenanceKey,
        /// Ordered typed fragments.
        fragments: Vec<DescriptorFormatFragment>,
    },
    /// Strict or sequentially strict evaluation metadata.
    Strictness {
        /// Strictness-attribute provenance.
        key: ProvenanceKey,
        /// Evaluation strategy.
        kind: StrictnessKind,
        /// Optional selected context-alias declaration.
        using: Option<HostContextAliasReference>,
        /// Named fields in authored order.
        fields: Vec<DescriptorFieldReference>,
        /// Build-local result-predicate sort.
        result_sort: Box<HostSortReference>,
    },
}

/// Ownership of a semantic production. Generated token/bracket identities are
/// deliberately absent; the compiler derives them from the grammar descriptor.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "production_owner",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum DescriptorProductionOwner {
    /// Grammar belonging to an authored constructor declaration.
    Constructor {
        /// Authored constructor identity and location.
        constructor: DescriptorApplicationReference,
    },
    /// Compiler-owned token production for an authored sort.
    TokenSort {
        /// Authored token sort and location.
        sort: DescriptorSortReference,
    },
    /// Compiler-owned bracket production attached to an authored sort.
    BracketSort {
        /// Authored bracket sort and location.
        sort: DescriptorSortReference,
    },
}

/// Host counterpart of [`DescriptorProductionOwner`].
#[derive(Clone, Debug)]
pub enum HostProductionOwner {
    /// Grammar belonging to an authored constructor declaration.
    Constructor {
        /// Build-local constructor identity.
        constructor: HostApplicationReference,
    },
    /// Compiler-owned token production for an authored sort.
    TokenSort {
        /// Build-local token sort identity.
        sort: HostSortReference,
    },
    /// Compiler-owned bracket production attached to an authored sort.
    BracketSort {
        /// Build-local bracket sort identity.
        sort: HostSortReference,
    },
}

/// One complete typed production extension.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorProduction {
    /// Production-level authored provenance.
    pub key: ProvenanceKey,
    /// Explicit syntax-template literal provenance. This is present for
    /// authored constructor templates and absent for default/token/bracket
    /// productions.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub template_key: Option<ProvenanceKey>,
    /// Declared or compiler-generated production ownership.
    pub owner: DescriptorProductionOwner,
    /// Typed production result sort and its authored sort-path provenance.
    pub result_sort: DescriptorSortReference,
    /// Ordered classified grammar items.
    pub items: Vec<DescriptorProductionItem>,
    /// Classified metadata only.
    pub attributes: Vec<DescriptorProductionAttribute>,
}

/// Host counterpart of [`DescriptorProduction`].
#[derive(Clone, Debug)]
pub struct HostProduction {
    /// Production-level authored provenance.
    pub key: ProvenanceKey,
    /// Optional explicit constructor syntax-template provenance.
    pub template_key: Option<ProvenanceKey>,
    /// Declared or compiler-generated ownership.
    pub owner: HostProductionOwner,
    /// Build-local production result sort.
    pub result_sort: HostSortReference,
    /// Ordered classified grammar items.
    pub items: Vec<HostProductionItem>,
    /// Classified metadata only.
    pub attributes: Vec<HostProductionAttribute>,
}

/// One direct precedence edge with every group occurrence retained.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorPrecedenceChain {
    /// Complete precedence-chain provenance.
    pub key: ProvenanceKey,
    /// Groups from tightest to loosest binding. The compiler expands adjacent
    /// pairs into target-neutral precedence edges.
    pub groups: Vec<DescriptorGroupReference>,
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

/// Typed after-the-fact object-grammar sentence.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "grammar_kind",
    content = "grammar",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum GrammarDescriptor {
    /// Constructor, token, or bracket production.
    Production(DescriptorProduction),
    /// Explicit direct subsort relation, including builtin endpoints.
    Subsort {
        /// Subsort-declaration provenance.
        key: ProvenanceKey,
        /// Smaller sort and authored path.
        subsort: DescriptorSortReference,
        /// Larger sort and authored path.
        supersort: DescriptorSortReference,
    },
    /// One macro declaration containing one or more precedence edges.
    Precedence {
        /// Complete macro-invocation provenance.
        key: ProvenanceKey,
        /// Direct partial-order edges.
        chains: Vec<DescriptorPrecedenceChain>,
    },
    /// One macro declaration containing one or more associativity sentences.
    Associativity {
        /// Complete macro-invocation provenance.
        key: ProvenanceKey,
        /// Typed associativity sentences.
        sentences: Vec<DescriptorAssociativitySentence>,
    },
}

/// Host counterpart of [`GrammarDescriptor`].
#[derive(Clone, Debug)]
pub enum HostGrammarDescriptor {
    /// Constructor, token, or bracket production.
    Production(HostProduction),
    /// Explicit direct subsort relation.
    Subsort {
        /// Subsort-declaration provenance.
        key: ProvenanceKey,
        /// Build-local smaller sort.
        subsort: HostSortReference,
        /// Build-local larger sort.
        supersort: HostSortReference,
    },
    /// One macro declaration containing precedence edges.
    Precedence {
        /// Complete macro-invocation provenance.
        key: ProvenanceKey,
        /// Direct partial-order edges.
        chains: Vec<DescriptorPrecedenceChain>,
    },
    /// One macro declaration containing associativity sentences.
    Associativity {
        /// Complete macro-invocation provenance.
        key: ProvenanceKey,
        /// Typed associativity sentences.
        sentences: Vec<DescriptorAssociativitySentence>,
    },
}

/// Literal kinds admitted by the explicit Rust term grammar.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "literal_kind",
    content = "value",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum DescriptorLiteral {
    /// Canonical unsigned decimal digits. Negative values use builtin
    /// operations rather than smuggling a signed lexer token through Rust.
    Int(String),
    /// Rust Boolean literal.
    Bool(bool),
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

/// One argument of a structured application. Positional tuple/call syntax and
/// named record syntax remain distinct so ordinary Rust field reordering never
/// changes K argument meaning.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "argument_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum DescriptorTermArgument {
    /// Argument from tuple/call syntax, interpreted in source order.
    Positional {
        /// Structured argument value.
        value: Box<DescriptorTerm>,
    },
    /// Argument from record syntax, interpreted by field identity.
    Named {
        /// Exact authored record-field name provenance.
        key: ProvenanceKey,
        /// Stable constructor-field identity.
        field: ProductionFieldId,
        /// Structured field value.
        value: Box<DescriptorTerm>,
    },
}

/// Host counterpart of [`DescriptorTermArgument`].
#[derive(Clone, Debug)]
pub enum HostTermArgument {
    /// Argument from tuple/call syntax.
    Positional {
        /// Structured argument value.
        value: Box<HostTerm>,
    },
    /// Argument from record syntax.
    Named {
        /// Exact authored record-field name provenance.
        key: ProvenanceKey,
        /// Stable constructor-field identity.
        field: ProductionFieldId,
        /// Structured field value.
        value: Box<HostTerm>,
    },
}

/// One named child of a compiler-owned complete cell term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorCellTermField {
    /// Exact authored child-field provenance.
    pub key: ProvenanceKey,
    /// Stable Rust field identity within the nominal cell declaration.
    pub field: ProductionFieldId,
    /// Structured child value, before the generated child-cell wrapper.
    pub value: Box<DescriptorTerm>,
}

/// Host counterpart of [`DescriptorCellTermField`].
#[derive(Clone, Debug)]
pub struct HostCellTermField {
    /// Exact authored child-field provenance.
    pub key: ProvenanceKey,
    /// Stable Rust field identity within the nominal cell declaration.
    pub field: ProductionFieldId,
    /// Structured child value.
    pub value: Box<HostTerm>,
}

/// A fully structured rule term after stable reference resolution.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "term_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum DescriptorTerm {
    /// Bound variable reference.
    Variable {
        /// Exact bare-reference provenance.
        key: ProvenanceKey,
        /// Compact named-path provenance retained for source-map
        /// continuity.
        path_key: ProvenanceKey,
        /// Bound Rust identifier.
        name: String,
    },
    /// Declared constructor or builtin operation application.
    Application {
        /// Syntactic head class used to select exact parser provenance.
        head_class: DescriptorApplicationHeadClass,
        /// Typed application head and provenance.
        reference: DescriptorApplicationReference,
        /// Compact named-path provenance retained for source-map
        /// continuity.
        path_key: ProvenanceKey,
        /// Positional or named arguments. One application may not mix forms.
        arguments: Vec<DescriptorTermArgument>,
    },
    /// Exact Int/Bool literal.
    Literal {
        /// Exact literal provenance.
        key: ProvenanceKey,
        /// Typed literal payload.
        literal: DescriptorLiteral,
    },
    /// Anonymous subject-pattern wildcard. This is rejected on rule results.
    Wildcard {
        /// Exact authored underscore provenance.
        key: ProvenanceKey,
    },
    /// Compiler-owned domain token whose sort is intrinsic.
    BuiltinToken {
        /// Exact literal provenance.
        key: ProvenanceKey,
        /// Closed builtin token sort.
        sort: BuiltinSort,
        /// Complete validated payload.
        value: String,
    },
    /// One fresh typed anonymous-variable occurrence.
    Anonymous {
        /// Complete occurrence provenance.
        key: ProvenanceKey,
        /// Exact authored sort occurrence.
        sort: DescriptorSortReference,
        /// Display spelling retained for K/native anonymous handling.
        spelling: String,
    },
    /// Compiler-owned associative object-Bool disjunction.
    OrBool {
        /// Complete macro-shell provenance.
        key: ProvenanceKey,
        /// Ordered operands, at least two.
        arguments: Vec<DescriptorTerm>,
    },
    /// Complete nominal parent-cell term constructed by `fragment!`.
    Cell {
        /// Complete macro-shell provenance.
        key: ProvenanceKey,
        /// Stable `#[k::cell]` declaration identity.
        declaration: StableItemId,
        /// Authored child values; semantic lowering validates completeness and order.
        fields: Vec<DescriptorCellTermField>,
    },
}

/// Host term whose application heads still carry build-local Rust identities.
#[derive(Clone, Debug)]
pub enum HostTerm {
    /// Bound variable reference.
    Variable {
        /// Exact bare-reference provenance.
        key: ProvenanceKey,
        /// Compact named-path provenance.
        path_key: ProvenanceKey,
        /// Bound Rust identifier.
        name: String,
    },
    /// Declared constructor or builtin operation application.
    Application {
        /// Syntactic head class used to select exact parser provenance.
        head_class: DescriptorApplicationHeadClass,
        /// Build-local application head and provenance.
        reference: HostApplicationReference,
        /// Compact named-path provenance.
        path_key: ProvenanceKey,
        /// Positional or named arguments. One application may not mix forms.
        arguments: Vec<HostTermArgument>,
    },
    /// Exact Int/Bool literal.
    Literal {
        /// Exact literal provenance.
        key: ProvenanceKey,
        /// Typed literal payload.
        literal: DescriptorLiteral,
    },
    /// Anonymous subject-pattern wildcard. This is rejected on rule results.
    Wildcard {
        /// Exact authored underscore provenance.
        key: ProvenanceKey,
    },
    /// Host counterpart of a compiler-owned builtin token.
    BuiltinToken {
        /// Exact literal provenance.
        key: ProvenanceKey,
        /// Closed builtin token sort.
        sort: BuiltinSort,
        /// Complete validated payload.
        value: String,
    },
    /// Host counterpart of a typed fresh anonymous occurrence.
    Anonymous {
        /// Complete occurrence provenance.
        key: ProvenanceKey,
        /// Rust-resolved explicit sort.
        sort: HostSortReference,
        /// Exact display spelling.
        spelling: String,
    },
    /// Host counterpart of an associative object-Bool disjunction.
    OrBool {
        /// Complete macro-shell provenance.
        key: ProvenanceKey,
        /// Ordered operands, at least two.
        arguments: Vec<HostTerm>,
    },
    /// Host counterpart of a complete nominal parent-cell term.
    Cell {
        /// Complete macro-shell provenance.
        key: ProvenanceKey,
        /// Rust-resolved nominal `#[k::cell]` owner.
        declaration: HostTypeReference,
        /// Authored child values.
        fields: Vec<HostCellTermField>,
    },
}

/// Optional explicit K rule label and its authored literal provenance.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorRuleLabel {
    /// Exact authored label-literal provenance.
    pub key: ProvenanceKey,
    /// Exact emitted K rule-label spelling.
    pub name: String,
}

/// One typed object-language Boolean rule condition and its complete payload provenance.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorRuleCondition {
    /// Complete `#[k::requires(...)]` payload provenance.
    pub key: ProvenanceKey,
    /// Structured object-language term whose inferred sort must be `Bool`.
    pub term: DescriptorTerm,
}

/// Host counterpart of [`DescriptorRuleCondition`].
#[derive(Clone, Debug)]
pub struct HostRuleCondition {
    /// Complete `#[k::requires(...)]` payload provenance.
    pub key: ProvenanceKey,
    /// Build-local structured object-language condition term.
    pub term: HostTerm,
}

/// One explicit K rule priority with exact authoring provenance.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorRulePriority {
    /// Priority-literal provenance.
    pub key: ProvenanceKey,
    /// Effective K rule priority.
    pub value: u32,
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

/// Structured relational sentence.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StructuredRuleDescriptor {
    /// Transition, equation, or claim meaning.
    pub sentence_kind: SentenceKind,
    /// Optional explicit emitted K label.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<DescriptorRuleLabel>,
    /// Optional object-language Boolean applicability condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub requires: Option<DescriptorRuleCondition>,
    /// Optional explicit equation or ordered-fallback priority.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub priority: Option<DescriptorRulePriority>,
    /// Simplifier classification and optional hint.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub simplification: Option<DescriptorSimplification>,
    /// Complete subject-pattern provenance.
    pub pattern_key: ProvenanceKey,
    /// Complete result-expression provenance.
    pub result_key: ProvenanceKey,
    /// Exact authored subject sort.
    pub subject_sort: DescriptorSortReference,
    /// Exact authored result sort.
    pub result_sort: DescriptorSortReference,
    /// Bound names in deterministic pattern preorder.
    pub bindings: Vec<String>,
    /// Structured left pattern.
    pub subject: DescriptorTerm,
    /// Structured right result.
    pub result: DescriptorTerm,
}

/// Host counterpart of [`StructuredRuleDescriptor`].
#[derive(Clone, Debug)]
pub struct HostStructuredRuleDescriptor {
    /// Transition, equation, or claim meaning.
    pub sentence_kind: SentenceKind,
    /// Optional explicit emitted K label.
    pub label: Option<DescriptorRuleLabel>,
    /// Optional object-language Boolean applicability condition.
    pub requires: Option<HostRuleCondition>,
    /// Optional explicit equation or ordered-fallback priority.
    pub priority: Option<DescriptorRulePriority>,
    /// Simplifier classification and optional hint.
    pub simplification: Option<DescriptorSimplification>,
    /// Complete subject-pattern provenance.
    pub pattern_key: ProvenanceKey,
    /// Complete result-expression provenance.
    pub result_key: ProvenanceKey,
    /// Build-local subject sort.
    pub subject_sort: HostSortReference,
    /// Build-local result sort.
    pub result_sort: HostSortReference,
    /// Bound names in deterministic pattern preorder.
    pub bindings: Vec<String>,
    /// Structured left pattern.
    pub subject: HostTerm,
    /// Structured right result.
    pub result: HostTerm,
}

/// Typed local grammar transport error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GrammarTransportError {
    /// A required textual value was blank.
    EmptyText(&'static str),
    /// A declared sort reference used the wrong stable namespace.
    SortReferenceKind(ItemKind),
    /// A declared application used the wrong stable namespace.
    ApplicationReferenceKind(ItemKind),
    /// A collection-valued grammar construct was empty.
    EmptyCollection(&'static str),
    /// A set-valued list repeated a value.
    DuplicateValue(&'static str),
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
    InvalidProduction(&'static str),
    /// A structured application mixed argument forms or repeated a field.
    InvalidApplication(&'static str),
    /// A structured term used a node in an invalid relational position.
    InvalidTerm(&'static str),
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
        if let Self::Map(operation) = self
            && !MapOperation::TERM_APPLICATIONS.contains(operation)
        {
            return Err(GrammarTransportError::InvalidApplication(
                "structural-only Map operation used as an application head",
            ));
        }
        if let Self::List(operation) = self
            && !ListOperation::TERM_APPLICATIONS.contains(operation)
        {
            return Err(GrammarTransportError::InvalidApplication(
                "structural-only List operation used as an application head",
            ));
        }
        if let Self::Set(operation) = self
            && !SetOperation::TERM_APPLICATIONS.contains(operation)
        {
            return Err(GrammarTransportError::InvalidApplication(
                "structural-only Set operation used as an application head",
            ));
        }
        Ok(())
    }
}

impl DescriptorLiteral {
    fn validate(&self) -> Result<(), GrammarTransportError> {
        match self {
            Self::Int(value)
                if !value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit()) =>
            {
                Ok(())
            }
            Self::Bool(_) => Ok(()),
            Self::Int(_) => Err(GrammarTransportError::InvalidLiteral),
        }
    }
}

fn validate_map_application_shape(
    head_class: DescriptorApplicationHeadClass,
    application: &DescriptorApplicationRef,
    arguments: &[DescriptorTermArgument],
) -> Result<(), GrammarTransportError> {
    let DescriptorApplicationRef::Map(operation) = application else {
        return Ok(());
    };
    if head_class != DescriptorApplicationHeadClass::Applied {
        return Err(GrammarTransportError::InvalidApplication(
            "a Map operation must be an applied term head",
        ));
    }
    let expected = match operation {
        MapOperation::Update => 3,
        MapOperation::Get | MapOperation::InKeys => 2,
        MapOperation::Empty | MapOperation::Item => unreachable!("validated application catalog"),
    };
    if arguments.len() != expected {
        return Err(GrammarTransportError::InvalidApplication(
            "Map operation has invalid arity",
        ));
    }
    if arguments
        .iter()
        .any(|argument| !matches!(argument, DescriptorTermArgument::Positional { .. }))
    {
        return Err(GrammarTransportError::InvalidApplication(
            "Map operations accept positional arguments only",
        ));
    }
    Ok(())
}

fn validate_set_application_shape(
    head_class: DescriptorApplicationHeadClass,
    application: &DescriptorApplicationRef,
    arguments: &[DescriptorTermArgument],
) -> Result<(), GrammarTransportError> {
    let DescriptorApplicationRef::Set(operation) = application else {
        return Ok(());
    };
    if head_class != DescriptorApplicationHeadClass::Applied {
        return Err(GrammarTransportError::InvalidApplication(
            "a Set operation must be an applied term head",
        ));
    }
    let expected = match operation {
        SetOperation::Empty => 0,
        SetOperation::Item => 1,
        SetOperation::Concat | SetOperation::Union | SetOperation::Contains => 2,
    };
    if arguments.len() != expected {
        return Err(GrammarTransportError::InvalidApplication(
            "Set operation has invalid arity",
        ));
    }
    if arguments
        .iter()
        .any(|argument| !matches!(argument, DescriptorTermArgument::Positional { .. }))
    {
        return Err(GrammarTransportError::InvalidApplication(
            "Set operations accept positional arguments only",
        ));
    }
    Ok(())
}

fn validate_list_application_shape(
    head_class: DescriptorApplicationHeadClass,
    application: &DescriptorApplicationRef,
    arguments: &[DescriptorTermArgument],
) -> Result<(), GrammarTransportError> {
    let DescriptorApplicationRef::List(operation) = application else {
        return Ok(());
    };
    if head_class != DescriptorApplicationHeadClass::Applied {
        return Err(GrammarTransportError::InvalidApplication(
            "a List operation must be an applied term head",
        ));
    }
    let expected = match operation {
        ListOperation::Empty => 0,
        ListOperation::Item | ListOperation::Size => 1,
        ListOperation::Concat | ListOperation::Get | ListOperation::Make => 2,
        ListOperation::Update | ListOperation::Range | ListOperation::UpdateAll => 3,
    };
    if arguments.len() != expected {
        return Err(GrammarTransportError::InvalidApplication(
            "List operation has invalid arity",
        ));
    }
    if arguments
        .iter()
        .any(|argument| !matches!(argument, DescriptorTermArgument::Positional { .. }))
    {
        return Err(GrammarTransportError::InvalidApplication(
            "List operations accept positional arguments only",
        ));
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
        match self {
            Self::Variable {
                key,
                path_key,
                name,
            } => {
                require_key(key, provenance)?;
                require_key(path_key, provenance)?;
                if name.trim().is_empty() || !bindings.contains(name) {
                    return Err(GrammarTransportError::InvalidBinding(name.clone()));
                }
                seen_variables.insert(name.clone());
            }
            Self::Application {
                head_class,
                reference,
                path_key,
                arguments,
            } => {
                require_key(&reference.key, provenance)?;
                require_key(path_key, provenance)?;
                reference.application.validate()?;
                if *head_class == DescriptorApplicationHeadClass::BareReference
                    && !arguments.is_empty()
                {
                    return Err(GrammarTransportError::InvalidApplication(
                        "a bare-reference constructor must have no arguments",
                    ));
                }
                validate_map_application_shape(*head_class, &reference.application, arguments)?;
                validate_list_application_shape(*head_class, &reference.application, arguments)?;
                validate_set_application_shape(*head_class, &reference.application, arguments)?;
                let named = arguments.first().is_some_and(|argument| {
                    matches!(argument, DescriptorTermArgument::Named { .. })
                });
                let mut fields = BTreeSet::new();
                for argument in arguments {
                    match argument {
                        DescriptorTermArgument::Positional { value } if !named => {
                            value.validate(
                                provenance,
                                bindings,
                                seen_variables,
                                allow_wildcards,
                            )?;
                        }
                        DescriptorTermArgument::Named { key, field, value } if named => {
                            require_key(key, provenance)?;
                            if !fields.insert(field.clone()) {
                                return Err(GrammarTransportError::InvalidApplication(
                                    "named field occurs more than once",
                                ));
                            }
                            value.validate(
                                provenance,
                                bindings,
                                seen_variables,
                                allow_wildcards,
                            )?;
                        }
                        DescriptorTermArgument::Positional { .. }
                        | DescriptorTermArgument::Named { .. } => {
                            return Err(GrammarTransportError::InvalidApplication(
                                "positional and named arguments are mixed",
                            ));
                        }
                    }
                }
            }
            Self::Literal { key, literal } => {
                require_key(key, provenance)?;
                literal.validate()?;
            }
            Self::Wildcard { key } => {
                require_key(key, provenance)?;
                if !allow_wildcards {
                    return Err(GrammarTransportError::InvalidTerm(
                        "wildcards are allowed only in rule subjects",
                    ));
                }
            }
            Self::BuiltinToken { .. } | Self::Anonymous { .. } | Self::OrBool { .. } => {
                return Err(GrammarTransportError::InvalidTerm(
                    "claim-only term used outside a whole-configuration claim",
                ));
            }
            Self::Cell { .. } => {
                return Err(GrammarTransportError::InvalidTerm(
                    "complete cell terms require configuration rules",
                ));
            }
        }
        Ok(())
    }
}

impl StructuredRuleDescriptor {
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
        let expected = match self.sentence_kind {
            SentenceKind::Transition => ItemKind::Rule,
            SentenceKind::Equation => ItemKind::Equation,
            SentenceKind::Simplification => ItemKind::Simplification,
            SentenceKind::Alias => ItemKind::Alias,
            SentenceKind::Claim => ItemKind::Claim,
        };
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
                    "invalid explicit rule label",
                ));
            }
        }
        if let Some(requires) = &self.requires {
            require_key(&requires.key, provenance)?;
            if self.sentence_kind == SentenceKind::Alias {
                return Err(GrammarTransportError::InvalidTerm(
                    "static alias clauses cannot carry requires conditions",
                ));
            }
        }
        if let Some(priority) = &self.priority {
            require_key(&priority.key, provenance)?;
            let valid_equation = self.sentence_kind == SentenceKind::Equation
                && priority.key.role() == ProvenanceRole::EquationPriority;
            let valid_owise = self.sentence_kind == SentenceKind::Transition
                && priority.key.role() == ProvenanceRole::RuleOwise
                && priority.value == 200;
            if !(valid_equation || valid_owise) {
                return Err(GrammarTransportError::InvalidTerm(
                    "priority must be an equation priority or transition ordered fallback",
                ));
            }
        }
        if let Some(simplification) = &self.simplification {
            require_key(&simplification.key, provenance)?;
            if self.sentence_kind != SentenceKind::Simplification {
                return Err(GrammarTransportError::InvalidTerm(
                    "simplification metadata is supported only on simplifications",
                ));
            }
            if let Some(priority) = &simplification.priority {
                require_key(&priority.key, provenance)?;
            }
        } else if self.sentence_kind == SentenceKind::Simplification {
            return Err(GrammarTransportError::InvalidTerm(
                "simplification sentence lacks simplification metadata",
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
            return Err(GrammarTransportError::DuplicateValue("rule bindings"));
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
                    return Err(GrammarTransportError::EmptyCollection("precedence chains"));
                }
                for chain in chains {
                    require_key(&chain.key, provenance)?;
                    validate_group_references(&chain.groups, provenance, "precedence groups")?;
                    if chain.groups.len() < 2 {
                        return Err(GrammarTransportError::InvalidProduction(
                            "precedence chain requires at least two groups",
                        ));
                    }
                }
                Ok(())
            }
            Self::Associativity { key, sentences } => {
                require_key(key, provenance)?;
                if sentences.is_empty() {
                    return Err(GrammarTransportError::EmptyCollection(
                        "associativity sentences",
                    ));
                }
                for sentence in sentences {
                    require_key(&sentence.key, provenance)?;
                    validate_group_references(
                        &sentence.groups,
                        provenance,
                        "associativity groups",
                    )?;
                }
                Ok(())
            }
        }
    }
}

impl DescriptorProduction {
    #[allow(clippy::too_many_lines)]
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
                        "token and bracket owners must be authored sorts",
                    ));
                }
            }
        }
        validate_sort_reference(&self.result_sort, provenance)?;
        if self.items.is_empty() {
            return Err(GrammarTransportError::EmptyCollection("production items"));
        }
        for item in &self.items {
            match item {
                DescriptorProductionItem::Terminal { key, text } => {
                    require_key(key, provenance)?;
                    if text.is_empty() {
                        return Err(GrammarTransportError::EmptyText("terminal"));
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
                        return Err(GrammarTransportError::EmptyText("production regex"));
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
                        return Err(GrammarTransportError::EmptyCollection("format fragments"));
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
                        return Err(GrammarTransportError::EmptyCollection("strictness fields"));
                    }
                    let mut names = BTreeSet::new();
                    for field in fields {
                        require_key(&field.key, provenance)?;
                        if !names.insert(field.field.clone()) {
                            return Err(GrammarTransportError::DuplicateValue("strictness fields"));
                        }
                    }
                    validate_sort_reference(result_sort, provenance)?;
                    "strictness"
                }
            };
            if !families.insert(family) {
                return Err(GrammarTransportError::DuplicateValue(
                    "production attribute families",
                ));
            }
        }
        if families.contains("total") && !families.contains("function") {
            return Err(GrammarTransportError::InvalidProduction(
                "total metadata requires function metadata",
            ));
        }
        if families.contains("hook")
            && !(families.contains("function") && families.contains("total"))
        {
            return Err(GrammarTransportError::InvalidProduction(
                "hook metadata requires a total function production",
            ));
        }
        if families.contains("alias") && families.contains("function") {
            return Err(GrammarTransportError::InvalidProduction(
                "alias metadata cannot be combined with function metadata",
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
                        "token owner requires one regex item and token metadata",
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
                        "token production must contain exactly one regex item",
                    ));
                };
                if precede_regex.is_some() || follow_regex.is_some() {
                    return Err(GrammarTransportError::InvalidProduction(
                        "nominal token regex cannot carry precede/follow guards",
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
                        "bracket owner requires bracket metadata and one nonterminal",
                    ));
                }
                if self.result_sort.sort != sort.sort {
                    return Err(GrammarTransportError::InvalidProduction(
                        "bracket owner and result sorts must be identical",
                    ));
                }
                for item in &self.items {
                    match item {
                        DescriptorProductionItem::RegexTerminal { .. } => {
                            return Err(GrammarTransportError::InvalidProduction(
                                "bracket production cannot contain regex items",
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
                                    "bracket nonterminal field must be `value`",
                                ));
                            }
                            if declaration_key.is_some() {
                                return Err(GrammarTransportError::InvalidProduction(
                                    "bracket nonterminal cannot claim a constructor field",
                                ));
                            }
                            if value_sort.sort != sort.sort {
                                return Err(GrammarTransportError::InvalidProduction(
                                    "bracket owner, result, and value sorts must be identical",
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
                    "constructor owner cannot carry token or bracket metadata",
                ))
            }
            DescriptorProductionOwner::Constructor { .. }
                if families.contains("format") && self.template_key.is_none() =>
            {
                Err(GrammarTransportError::InvalidProduction(
                    "format metadata requires explicit constructor syntax",
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
    #[allow(clippy::too_many_lines)]
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
                        "token production cannot have a syntax-template key",
                    ));
                }
                let [DescriptorProductionItem::RegexTerminal { key, .. }] = self.items.as_slice()
                else {
                    return Err(GrammarTransportError::InvalidProduction(
                        "token production must contain exactly one regex item",
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
                        "token production must contain only token metadata",
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
                        "bracket production cannot have a constructor-template key",
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
                                    "bracket nonterminal cannot claim a constructor field",
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
                        "bracket production must contain only bracket metadata",
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
                            "constructor nonterminal lacks its field declaration key",
                        ));
                    };
                    let declaration_ordinal = declaration_key.ordinal();
                    if !declaration_ordinals.insert(declaration_ordinal) {
                        return Err(GrammarTransportError::InvalidProduction(
                            "constructor field declaration ordinals must be unique",
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
                        "constructor production cannot contain a regex item",
                    ));
                }
            }
        }
        if declaration_ordinals != (0..occurrence_ordinal).collect::<BTreeSet<_>>() {
            return Err(GrammarTransportError::InvalidProduction(
                "constructor field declaration ordinals must form a dense permutation",
            ));
        }
        Ok(())
    }

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
                DescriptorProductionAttribute::Token { .. }
                | DescriptorProductionAttribute::Bracket { .. } => {
                    return Err(GrammarTransportError::InvalidProduction(
                        "constructor has token or bracket metadata",
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
            let role = if self.sentence_kind == SentenceKind::Transition {
                ProvenanceRole::RuleOwise
            } else {
                ProvenanceRole::EquationPriority
            };
            insert_exact(&mut keys, &priority.key, role, 0)?;
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

pub(crate) fn valid_rule_label_name(value: &str) -> bool {
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
        match self {
            Self::Variable { key, path_key, .. } => {
                insert_exact(keys, path_key, side.path_role(), counters.path)?;
                counters.path = increment(counters.path)?;
                insert_exact(keys, key, side.reference_role(), counters.reference)?;
                counters.reference = increment(counters.reference)?;
            }
            Self::Application {
                head_class,
                reference,
                path_key,
                arguments,
            } => {
                insert_exact(keys, path_key, side.path_role(), counters.path)?;
                counters.path = increment(counters.path)?;
                match head_class {
                    DescriptorApplicationHeadClass::Applied => {
                        insert_exact(
                            keys,
                            &reference.key,
                            side.application_role(),
                            counters.application,
                        )?;
                        counters.application = increment(counters.application)?;
                    }
                    DescriptorApplicationHeadClass::BareReference => {
                        insert_exact(
                            keys,
                            &reference.key,
                            side.reference_role(),
                            counters.reference,
                        )?;
                        counters.reference = increment(counters.reference)?;
                    }
                }
                for argument in arguments {
                    match argument {
                        DescriptorTermArgument::Positional { value } => {
                            value.collect_expected_term_keys(keys, side, counters)?;
                        }
                        DescriptorTermArgument::Named { key, value, .. } => {
                            insert_exact(
                                keys,
                                key,
                                side.record_field_role(),
                                counters.record_field,
                            )?;
                            counters.record_field = increment(counters.record_field)?;
                            value.collect_expected_term_keys(keys, side, counters)?;
                        }
                    }
                }
            }
            Self::Literal { key, .. } => {
                insert_exact(keys, key, side.literal_role(), counters.literal)?;
                counters.literal = increment(counters.literal)?;
            }
            Self::Wildcard { key } => {
                let Some(role) = side.wildcard_role() else {
                    return Err(GrammarTransportError::InvalidTerm(
                        "wildcards are allowed only in rule subjects",
                    ));
                };
                insert_exact(keys, key, role, counters.wildcard)?;
                counters.wildcard = increment(counters.wildcard)?;
            }
            Self::BuiltinToken { .. } | Self::Anonymous { .. } | Self::OrBool { .. } => {
                return Err(GrammarTransportError::InvalidTerm(
                    "claim-only term used outside a whole-configuration claim",
                ));
            }
            Self::Cell { .. } => {
                return Err(GrammarTransportError::InvalidTerm(
                    "complete cell terms require configuration rules",
                ));
            }
        }
        Ok(())
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
    u32::try_from(index)
        .map_err(|_| GrammarTransportError::InvalidProduction("provenance ordinal exceeds u32"))
}

fn increment(value: u32) -> Result<u32, GrammarTransportError> {
    value
        .checked_add(1)
        .ok_or(GrammarTransportError::InvalidProduction(
            "provenance ordinal exceeds u32",
        ))
}

fn validate_sort_reference(
    reference: &DescriptorSortReference,
    provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
) -> Result<(), GrammarTransportError> {
    require_key(&reference.key, provenance)?;
    reference.sort.validate()
}

fn validate_group_references(
    references: &[DescriptorGroupReference],
    provenance: impl Fn(&ProvenanceKey) -> bool + Copy,
    field: &'static str,
) -> Result<(), GrammarTransportError> {
    if references.is_empty() {
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

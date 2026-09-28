//! Collector transport for fixed configurations.
//!
//! Nominal nested-cell declarations, complete fixed configurations, paired
//! initializers, and the structured K-sequence/map terms used by
//! initializers. Whole-configuration rules, claims, and context aliases are
//! in [`crate::transport::rule`].
use std::any::TypeId;
use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

use serde::{Deserialize, Serialize};

use crate::host::{HostTypeKey, HostTypeReference};
use crate::transport::grammar::{
    DescriptorApplicationHeadClass, DescriptorSortRef, DescriptorSortReference, DescriptorTerm,
    DescriptorTermArgument, HostSortReference, HostTerm, HostTermArgument,
};
use crate::{BuiltinSort, ItemKind, ProvenanceKey, StableItemId};

/// Stable owner-qualified identity of one fixed cell field.
///
/// `field` is the stable Rust field identifier. It is intentionally distinct
/// from the optionally overridden emitted K cell name.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorCellIdentity {
    /// Configuration or nominal nested-cell declaration owning the field.
    pub owner: StableItemId,
    /// Stable Rust field identifier.
    pub field: String,
}

/// Build-local owner/field-marker identity emitted by a configuration macro.
///
/// A generated marker `TypeId` gives each field nominal identity even when two
/// declarations use the same Rust field spelling. This type cannot serialize.
#[derive(Clone, Copy, Debug)]
pub struct HostCellIdentity {
    /// Rust identity of the configuration or nested cell declaration.
    pub owner: HostTypeKey,
    /// Rust identity of the generated per-field marker.
    pub field: HostTypeKey,
}

impl HostCellIdentity {
    /// Resolves the exact build-local owner/field pair.
    #[must_use]
    pub fn resolve(self) -> (TypeId, TypeId) {
        (self.owner.resolve(), self.field.resolve())
    }
}

/// One stable cell identity paired with its exact parser-owned field key.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorCellReference {
    /// Field occurrence provenance.
    pub key: ProvenanceKey,
    /// Exact owner-qualified cell identity.
    pub cell: DescriptorCellIdentity,
}

/// Host counterpart of [`DescriptorCellReference`].
#[derive(Clone, Debug)]
pub struct HostCellReference {
    /// Field occurrence provenance.
    pub key: ProvenanceKey,
    /// Exact build-local owner/field-marker pair.
    pub cell: HostCellIdentity,
}

/// Stable reference to a nominal `#[k::cell]` declaration.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorCellDeclarationReference {
    /// Authored nested-declaration type-path provenance.
    pub key: ProvenanceKey,
    /// Stable nominal nested-cell declaration.
    pub declaration: StableItemId,
}

/// Host counterpart of [`DescriptorCellDeclarationReference`].
#[derive(Clone, Debug)]
pub struct HostCellDeclarationReference {
    /// Authored nested-declaration type-path provenance.
    pub key: ProvenanceKey,
    /// Rust-resolved nominal nested declaration.
    pub declaration: HostTypeReference,
}

/// Semantic cell wrapper selected by checked Rust syntax.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CellWrapper {
    /// Ordinary fixed cell containing one term of its declared sort.
    Cell,
    /// Distinguished computation cell containing a K sequence.
    KCell,
}

/// Optional explicitly-authored emitted cell name.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorCellName {
    /// Exact string-literal provenance.
    pub key: ProvenanceKey,
    /// Nonempty emitted K cell name.
    pub value: String,
}

/// Optional classified cell color.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorCellColor {
    /// Exact string-literal provenance.
    pub key: ProvenanceKey,
    /// Nonempty target-neutral color value.
    pub value: String,
}

/// Optional classified repeated-cell multiplicity.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorCellMultiplicity {
    /// Exact string-literal provenance.
    pub key: ProvenanceKey,
    /// Exact supported K multiplicity spelling.
    pub value: String,
}

/// Optional classified repeated-cell collection type.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorCellType {
    /// Exact string-literal provenance.
    pub key: ProvenanceKey,
    /// Exact supported K collection type spelling.
    pub value: String,
}

/// Leaf or nominally nested content of one fixed cell declaration field.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "content_kind",
    rename_all = "snake_case",
    deny_unknown_fields,
    bound(
        serialize = "S: Serialize, N: Serialize",
        deserialize = "S: Deserialize<'de>, N: Deserialize<'de>"
    )
)]
pub enum ProtocolCellContent<S, N> {
    /// `Cell<T>` or `KCell<KSequence>` leaf.
    Leaf {
        /// Exact wrapper-path provenance.
        wrapper_key: ProvenanceKey,
        /// Typed wrapper meaning; path spelling is not semantic.
        wrapper: CellWrapper,
        /// Exact declared or builtin content sort.
        sort: S,
        /// Generic object-sort arguments retained for cell-pattern inference.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        arguments: Vec<S>,
    },
    /// Field whose type is another nominal `#[k::cell]` declaration.
    Nested {
        /// Typed reference to that declaration.
        declaration: N,
    },
}

/// One ordered fixed-cell declaration field.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolCellField<I, S, N> {
    /// Exact `configuration_field` provenance and nominal identity.
    pub reference: I,
    /// Stable Rust field name. This must agree with the stable identity.
    pub rust_field: String,
    /// Optional authored name override; absence emits `rust_field`.
    pub emitted_name: Option<DescriptorCellName>,
    /// Optional classified color.
    pub color: Option<DescriptorCellColor>,
    /// Optional repeated-cell multiplicity.
    pub multiplicity: Option<DescriptorCellMultiplicity>,
    /// Optional repeated-cell collection type.
    pub cell_type: Option<DescriptorCellType>,
    /// Typed leaf or nested content.
    pub content: ProtocolCellContent<S, N>,
}

/// Stable fixed-cell field.
pub type DescriptorCellField = ProtocolCellField<
    DescriptorCellReference,
    DescriptorSortReference,
    DescriptorCellDeclarationReference,
>;

/// Host-only fixed-cell field.
pub type HostCellField =
    ProtocolCellField<HostCellReference, HostSortReference, HostCellDeclarationReference>;

/// Ordered fields owned by one configuration or nominal nested-cell item.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolCellDeclaration<F> {
    /// Complete declaration-name provenance.
    pub key: ProvenanceKey,
    /// Nonempty fixed fields in authored order.
    pub fields: Vec<F>,
}

/// Stable field declaration used by a configuration descriptor.
pub type DescriptorConfigurationDeclaration = ProtocolCellDeclaration<DescriptorCellField>;

/// Stable nominal nested-cell declaration payload.
pub type DescriptorCellDeclaration = ProtocolCellDeclaration<DescriptorCellField>;

/// Host field declaration used by a configuration descriptor.
pub type HostConfigurationDeclaration = ProtocolCellDeclaration<HostCellField>;

/// Host nominal nested-cell declaration payload.
pub type HostCellDeclaration = ProtocolCellDeclaration<HostCellField>;

/// Generated-top or explicit authored root policy.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "root_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum DescriptorConfigurationRoot {
    /// Let the compiler provide the generated top cell.
    GeneratedTop,
    /// Emit one explicit user-visible root cell.
    Named {
        /// Exact root-name literal provenance.
        key: ProvenanceKey,
        /// Nonempty emitted root name.
        name: String,
    },
}

/// One ordered external configuration variable.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolConfigurationVariable<S> {
    /// Exact Rust binding provenance.
    pub binding_key: ProvenanceKey,
    /// Authored Rust binding name used by initializer terms.
    pub binding: String,
    /// Exact external-name literal provenance.
    pub external_name_key: ProvenanceKey,
    /// Nonempty external K variable name.
    pub external_name: String,
    /// Typed variable sort and exact type-path provenance.
    pub sort: S,
    /// Exact optional `main` marker provenance.
    pub main_key: Option<ProvenanceKey>,
}

/// Stable configuration-variable metadata.
pub type DescriptorConfigurationVariable = ProtocolConfigurationVariable<DescriptorSortReference>;

/// Host configuration-variable metadata.
pub type HostConfigurationVariable = ProtocolConfigurationVariable<HostSortReference>;

/// Surface notation retained for an exact K sequence.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DescriptorKSequenceNotation {
    /// Comma-delimited host notation, including empty `k![]`.
    Comma,
    /// Authored `~>` connective.
    Operator,
    /// Standalone explicit `.K`.
    DotK,
}

/// One ordinary structured term with its complete initializer-term anchor.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolInitializerTerm<T> {
    /// Exact complete-term provenance.
    pub key: ProvenanceKey,
    /// Structured term payload.
    pub term: T,
}

/// One K-sequence item and its structural item provenance.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolKSequenceItem<T> {
    /// Exact K-item provenance.
    pub key: ProvenanceKey,
    /// Structured item term and complete-term provenance.
    pub value: ProtocolInitializerTerm<T>,
}

/// Exact K sequence admitted by an initializer.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolKSequence<T> {
    /// Complete payload provenance. Empty `k![]` alone has no inner endpoint.
    pub payload_key: Option<ProvenanceKey>,
    /// Exact `.K` provenance for standalone dot notation.
    pub dot_k_key: Option<ProvenanceKey>,
    /// Preserved parser classification.
    pub notation: DescriptorKSequenceNotation,
    /// Ordered sequence prefix; initializer sequences have no frame.
    pub items: Vec<ProtocolKSequenceItem<T>>,
}

/// One exact map item.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolMapItem<T> {
    /// Exact key-expression provenance.
    pub key_key: ProvenanceKey,
    /// Structured key term.
    pub key: ProtocolInitializerTerm<T>,
    /// Exact value-expression provenance.
    pub value_key: ProvenanceKey,
    /// Structured value term.
    pub value: ProtocolInitializerTerm<T>,
}

/// Empty map, ordered exact items, or one functional update.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "map_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ProtocolMapBody<T> {
    /// `.Map` or empty `map![]`.
    Empty {
        /// Whether `.Map` was written explicitly.
        explicit_dot: bool,
    },
    /// Ordered exact map items. Initializers cannot contain a remainder.
    Items {
        /// Nonempty ordered key/value entries.
        items: Vec<ProtocolMapItem<T>>,
    },
    /// Functional update `(base, key, value)`.
    Update {
        /// Exact base-expression provenance.
        base_key: ProvenanceKey,
        /// Existing map term.
        base: ProtocolInitializerTerm<T>,
        /// Exact updated-key provenance.
        key_key: ProvenanceKey,
        /// Updated key term.
        key: ProtocolInitializerTerm<T>,
        /// Exact replacement-value provenance.
        value_key: ProvenanceKey,
        /// Replacement value term.
        value: ProtocolInitializerTerm<T>,
    },
}

/// Structured exact map admitted by an initializer.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolMap<T> {
    /// Complete payload provenance. Empty `map![]` alone has no inner endpoint.
    pub payload_key: Option<ProvenanceKey>,
    /// Typed map operation.
    pub body: ProtocolMapBody<T>,
}

/// Leaf state families admitted by a fixed initializer.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "state_term_kind",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum ProtocolInitializerStateTerm<T> {
    /// Ordinary structured term.
    Term(ProtocolInitializerTerm<T>),
    /// Exact computation sequence.
    KSequence(ProtocolKSequence<T>),
    /// Exact map term.
    Map(ProtocolMap<T>),
}

/// Stable initializer state term.
pub type DescriptorInitializerStateTerm = ProtocolInitializerStateTerm<DescriptorTerm>;

/// Host initializer state term.
pub type HostInitializerStateTerm = ProtocolInitializerStateTerm<HostTerm>;

/// Leaf or recursively nested initializer cell content.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "content_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ProtocolInitializerCellContent<I, N, T> {
    /// `Cell::new(...)` or `KCell::new(k![...])`.
    Leaf {
        /// Exact constructor-path provenance.
        constructor_key: ProvenanceKey,
        /// Typed wrapper meaning.
        wrapper: CellWrapper,
        /// Structured leaf state.
        value: T,
    },
    /// Complete nominal nested-cell struct literal.
    Nested {
        /// Exact constructor reference.
        declaration: N,
        /// Ordered nonempty child initializers.
        children: Vec<ProtocolInitializerCell<I, N, T>>,
    },
}

/// One node of a recursive initializer forest.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolInitializerCell<I, N, T> {
    /// Exact initializer-cell node provenance.
    pub key: ProvenanceKey,
    /// Exact field occurrence and owner-qualified identity.
    pub field: I,
    /// Leaf or nested content.
    pub content: ProtocolInitializerCellContent<I, N, T>,
}

/// Stable initializer cell.
pub type DescriptorInitializerCell = ProtocolInitializerCell<
    DescriptorCellReference,
    DescriptorCellDeclarationReference,
    DescriptorInitializerStateTerm,
>;

/// Host initializer cell.
pub type HostInitializerCell = ProtocolInitializerCell<
    HostCellReference,
    HostCellDeclarationReference,
    HostInitializerStateTerm,
>;

/// Complete paired initializer payload.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolConfigurationInitializer<O, V, C> {
    /// Exact associated-function declaration provenance.
    pub key: ProvenanceKey,
    /// Exact `Self` result-type provenance.
    pub owner_key: ProvenanceKey,
    /// Configuration owner identity. Host forms use a `HostTypeKey`.
    pub owner: O,
    /// Variables in parameter order.
    pub variables: Vec<V>,
    /// Complete declarative body provenance.
    pub body_key: ProvenanceKey,
    /// Complete ordered top-level initializer forest.
    pub cells: Vec<C>,
}

/// Stable paired initializer.
pub type DescriptorConfigurationInitializer = ProtocolConfigurationInitializer<
    StableItemId,
    DescriptorConfigurationVariable,
    DescriptorInitializerCell,
>;

/// Host paired initializer.
pub type HostConfigurationInitializer =
    ProtocolConfigurationInitializer<HostTypeKey, HostConfigurationVariable, HostInitializerCell>;

/// Complete stable non-rule configuration payload.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorFixedConfiguration {
    /// Generated or named top policy.
    pub root: DescriptorConfigurationRoot,
    /// Top-level declaration fields.
    pub declaration: DescriptorConfigurationDeclaration,
    /// Paired complete initializer.
    pub initializer: DescriptorConfigurationInitializer,
}

/// Host counterpart of [`DescriptorFixedConfiguration`].
#[derive(Clone, Debug)]
pub struct HostFixedConfiguration {
    /// Generated or named top policy.
    pub root: DescriptorConfigurationRoot,
    /// Top-level declaration fields.
    pub declaration: HostConfigurationDeclaration,
    /// Paired complete initializer.
    pub initializer: HostConfigurationInitializer,
}

/// Typed local configuration transport error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StateTransportError {
    /// A required textual value was blank or path-shaped.
    InvalidText(&'static str),
    /// A collection required by the fixed grammar was empty.
    EmptyCollection(&'static str),
    /// A set-valued list repeated a value.
    DuplicateValue(&'static str),
    /// A stable declaration or reference used the wrong namespace.
    ItemKind {
        /// Description of the value being checked.
        field: &'static str,
        /// Allowed namespace(s).
        expected: &'static str,
        /// Actual namespace.
        actual: ItemKind,
    },
    /// A cell identity did not belong to its containing declaration.
    CellOwnerMismatch,
    /// Stable Rust field spelling disagreed with cell identity.
    CellFieldMismatch,
    /// Initializer and declaration field trees disagreed.
    InitializerDeclarationMismatch,
    /// More than one configuration variable was marked main.
    MultipleMainVariables,
    /// A `KCell` or state family disagreed with its declaration.
    InvalidCellContent(&'static str),
    /// A structured initializer term was invalid.
    InvalidTerm(&'static str),
    /// A nested semantic key was absent from materialized provenance.
    MissingProvenance(ProvenanceKey),
    /// A node used a key other than its exact parser role/ordinal.
    UnexpectedProvenance {
        /// Required key.
        expected: ProvenanceKey,
        /// Supplied key.
        actual: ProvenanceKey,
    },
    /// Materialized provenance contained a key absent from the typed payload.
    ExtraProvenance(ProvenanceKey),
}

impl fmt::Display for StateTransportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidText(field) => write!(formatter, "invalid {field}"),
            Self::EmptyCollection(field) => write!(formatter, "{field} must not be empty"),
            Self::DuplicateValue(field) => write!(formatter, "{field} contains a duplicate"),
            Self::ItemKind {
                field,
                expected,
                actual,
            } => write!(
                formatter,
                "{field} item kind mismatch: expected {expected}, found {actual}"
            ),
            Self::CellOwnerMismatch => formatter.write_str("cell identity owner mismatch"),
            Self::CellFieldMismatch => {
                formatter.write_str("cell identity and Rust field name mismatch")
            }
            Self::InitializerDeclarationMismatch => {
                formatter.write_str("initializer cell tree disagrees with its declaration")
            }
            Self::MultipleMainVariables => {
                formatter.write_str("configuration has more than one main variable")
            }
            Self::InvalidCellContent(detail) => write!(formatter, "invalid cell content: {detail}"),
            Self::InvalidTerm(detail) => write!(formatter, "invalid initializer term: {detail}"),
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
        }
    }
}

impl Error for StateTransportError {}

impl DescriptorCellIdentity {
    /// Validates the stable owner namespace and Rust field component.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for a non-configuration/cell owner or
    /// an invalid stable Rust field name.
    pub fn validate(&self) -> Result<(), StateTransportError> {
        require_cell_owner_kind(&self.owner, "cell identity owner")?;
        validate_rust_field(&self.field)
    }
}

impl DescriptorCellDeclarationReference {
    fn validate(&self) -> Result<(), StateTransportError> {
        if self.declaration.item_kind() != ItemKind::Cell {
            return Err(StateTransportError::ItemKind {
                field: "nested cell declaration",
                expected: "Cell",
                actual: self.declaration.item_kind(),
            });
        }
        Ok(())
    }
}

impl ProtocolCellDeclaration<DescriptorCellField> {
    /// Validates stable field identity, content, and exact declaration keys.
    ///
    /// The owner may be a top-level configuration or a nominal nested cell.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for invalid ownership, duplicates,
    /// typed references, metadata, or parser roles/ordinals.
    pub fn validate(&self, owner: &StableItemId) -> Result<(), StateTransportError> {
        let mut ignored = BTreeSet::new();
        validate_descriptor_declaration(self, owner, &mut ignored)
    }

    /// Returns the complete exact provenance set for this declaration.
    ///
    /// # Errors
    ///
    /// Returns the same shape/key errors as [`Self::validate`].
    pub fn expected_provenance_keys(
        &self,
        owner: &StableItemId,
    ) -> Result<BTreeSet<ProvenanceKey>, StateTransportError> {
        let mut keys = BTreeSet::new();
        validate_descriptor_declaration(self, owner, &mut keys)?;
        Ok(keys)
    }

    /// Validates an exact, closed provenance table for a cell declaration.
    ///
    /// # Errors
    ///
    /// Returns an error for missing/extra keys or a primary key other than
    /// `configuration_declaration#0`.
    pub fn validate_complete_provenance(
        &self,
        owner: &StableItemId,
        primary: &ProvenanceKey,
        actual: &BTreeSet<ProvenanceKey>,
    ) -> Result<(), StateTransportError> {
        let expected = self.expected_provenance_keys(owner)?;
        validate_complete_set(primary, actual, &expected)
    }
}

impl ProtocolCellDeclaration<HostCellField> {
    /// Validates host owner/field-marker joins and exact declaration keys.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for mismatched identities, duplicate
    /// fields/names, malformed metadata, or wrong parser roles/ordinals.
    pub fn validate_host(&self, owner: HostTypeKey) -> Result<(), StateTransportError> {
        let mut keys = BTreeSet::new();
        validate_host_declaration(self, owner, &mut keys)
    }
}

impl DescriptorFixedConfiguration {
    /// Validates a complete stable declaration/initializer pairing.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for wrong ownership, declaration/tree
    /// disagreement, invalid terms/variables, or inexact parser keys.
    pub fn validate(&self, owner: &StableItemId) -> Result<(), StateTransportError> {
        let mut ignored = BTreeSet::new();
        self.validate_into(owner, &mut ignored)
    }

    /// Returns every and only parser key represented by this typed payload.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::validate`].
    pub fn expected_provenance_keys(
        &self,
        owner: &StableItemId,
    ) -> Result<BTreeSet<ProvenanceKey>, StateTransportError> {
        let mut keys = BTreeSet::new();
        self.validate_into(owner, &mut keys)?;
        Ok(keys)
    }

    /// Validates exact expected-versus-actual provenance and the primary key.
    ///
    /// # Errors
    ///
    /// Returns an error for payload shape, missing/extra keys, or a primary
    /// key other than `configuration_declaration#0`.
    pub fn validate_complete_provenance(
        &self,
        owner: &StableItemId,
        primary: &ProvenanceKey,
        actual: &BTreeSet<ProvenanceKey>,
    ) -> Result<(), StateTransportError> {
        let expected = self.expected_provenance_keys(owner)?;
        validate_complete_set(primary, actual, &expected)
    }

    fn validate_into(
        &self,
        owner: &StableItemId,
        keys: &mut BTreeSet<ProvenanceKey>,
    ) -> Result<(), StateTransportError> {
        if owner.item_kind() != ItemKind::Configuration {
            return Err(StateTransportError::ItemKind {
                field: "configuration descriptor",
                expected: "Configuration",
                actual: owner.item_kind(),
            });
        }
        validate_root(&self.root, keys)?;
        validate_descriptor_declaration(&self.declaration, owner, keys)?;
        validate_descriptor_initializer(&self.initializer, owner, &self.declaration, keys)
    }
}

impl HostFixedConfiguration {
    /// Validates a complete host declaration/initializer pairing without
    /// consulting path spelling.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for owner-key mismatches,
    /// declaration/tree disagreement, malformed terms/variables, or inexact
    /// parser roles/ordinals.
    pub fn validate(&self, owner: HostTypeKey) -> Result<(), StateTransportError> {
        let mut keys = BTreeSet::new();
        validate_root(&self.root, &mut keys)?;
        validate_host_declaration(&self.declaration, owner, &mut keys)?;
        validate_host_initializer(&self.initializer, owner, &self.declaration, &mut keys)
    }
}

fn validate_descriptor_declaration(
    declaration: &DescriptorConfigurationDeclaration,
    owner: &StableItemId,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    require_cell_owner_kind(owner, "cell declaration")?;
    insert_exact(keys, &declaration.key, "configuration_declaration", 0)?;
    if declaration.fields.is_empty() {
        return Err(StateTransportError::EmptyCollection("fixed cell fields"));
    }
    let mut rust_fields = BTreeSet::new();
    let mut emitted_names = BTreeSet::new();
    let mut identities = BTreeSet::new();
    let mut argument_ordinal = 0_u32;
    for (index, field) in declaration.fields.iter().enumerate() {
        let ordinal = checked_index(index)?;
        field.reference.cell.validate()?;
        if &field.reference.cell.owner != owner {
            return Err(StateTransportError::CellOwnerMismatch);
        }
        validate_rust_field(&field.rust_field)?;
        if field.reference.cell.field != field.rust_field {
            return Err(StateTransportError::CellFieldMismatch);
        }
        if !rust_fields.insert(field.rust_field.clone())
            || !identities.insert(field.reference.cell.clone())
        {
            return Err(StateTransportError::DuplicateValue("fixed cell fields"));
        }
        insert_exact(keys, &field.reference.key, "configuration_field", ordinal)?;
        let emitted = validate_cell_metadata(field, ordinal, keys)?;
        if !emitted_names.insert(emitted) {
            return Err(StateTransportError::DuplicateValue(
                "emitted sibling cell names",
            ));
        }
        match &field.content {
            ProtocolCellContent::Leaf {
                wrapper_key,
                wrapper,
                sort,
                arguments,
            } => {
                insert_exact(keys, wrapper_key, "configuration_cell_wrapper", ordinal)?;
                insert_exact(keys, &sort.key, "configuration_cell_content", ordinal)?;
                sort.sort
                    .validate()
                    .map_err(|_| StateTransportError::ItemKind {
                        field: "cell content sort",
                        expected: "Sort or builtin",
                        actual: match &sort.sort {
                            DescriptorSortRef::Declared(id) => id.item_kind(),
                            DescriptorSortRef::Builtin(_) => ItemKind::Sort,
                        },
                    })?;
                validate_k_cell_sort(*wrapper, &sort.sort)?;
                for argument in arguments {
                    insert_exact(
                        keys,
                        &argument.key,
                        "configuration_cell_content_argument",
                        argument_ordinal,
                    )?;
                    argument.sort.validate().map_err(|_| {
                        StateTransportError::InvalidTerm("invalid cell sort argument")
                    })?;
                    argument_ordinal = increment(argument_ordinal)?;
                }
            }
            ProtocolCellContent::Nested { declaration } => {
                insert_exact(
                    keys,
                    &declaration.key,
                    "configuration_cell_content",
                    ordinal,
                )?;
                declaration.validate()?;
            }
        }
    }
    Ok(())
}

fn validate_host_declaration(
    declaration: &HostConfigurationDeclaration,
    owner: HostTypeKey,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    insert_exact(keys, &declaration.key, "configuration_declaration", 0)?;
    if declaration.fields.is_empty() {
        return Err(StateTransportError::EmptyCollection("fixed cell fields"));
    }
    let mut rust_fields = BTreeSet::new();
    let mut emitted_names = BTreeSet::new();
    let mut identities = BTreeSet::new();
    let mut argument_ordinal = 0_u32;
    for (index, field) in declaration.fields.iter().enumerate() {
        let ordinal = checked_index(index)?;
        if field.reference.cell.owner.resolve() != owner.resolve() {
            return Err(StateTransportError::CellOwnerMismatch);
        }
        validate_rust_field(&field.rust_field)?;
        if !rust_fields.insert(field.rust_field.clone())
            || !identities.insert(field.reference.cell.resolve())
        {
            return Err(StateTransportError::DuplicateValue("fixed cell fields"));
        }
        insert_exact(keys, &field.reference.key, "configuration_field", ordinal)?;
        let emitted = validate_cell_metadata(field, ordinal, keys)?;
        if !emitted_names.insert(emitted) {
            return Err(StateTransportError::DuplicateValue(
                "emitted sibling cell names",
            ));
        }
        match &field.content {
            ProtocolCellContent::Leaf {
                wrapper_key,
                sort,
                arguments,
                ..
            } => {
                insert_exact(keys, wrapper_key, "configuration_cell_wrapper", ordinal)?;
                insert_exact(keys, &sort.key, "configuration_cell_content", ordinal)?;
                for argument in arguments {
                    insert_exact(
                        keys,
                        &argument.key,
                        "configuration_cell_content_argument",
                        argument_ordinal,
                    )?;
                    if argument.target.authored_path.trim().is_empty() {
                        return Err(StateTransportError::InvalidText(
                            "cell sort argument diagnostic path",
                        ));
                    }
                    argument_ordinal = increment(argument_ordinal)?;
                }
            }
            ProtocolCellContent::Nested { declaration } => {
                insert_exact(
                    keys,
                    &declaration.key,
                    "configuration_cell_content",
                    ordinal,
                )?;
                if declaration.declaration.authored_path.trim().is_empty() {
                    return Err(StateTransportError::InvalidText(
                        "nested cell diagnostic path",
                    ));
                }
            }
        }
    }
    Ok(())
}

fn validate_cell_metadata<I, S, N>(
    field: &ProtocolCellField<I, S, N>,
    ordinal: u32,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<String, StateTransportError> {
    let emitted = if let Some(name) = &field.emitted_name {
        validate_nonblank("emitted cell name", &name.value)?;
        insert_exact(keys, &name.key, "configuration_cell_name", ordinal)?;
        name.value.clone()
    } else {
        field.rust_field.clone()
    };
    if let Some(color) = &field.color {
        validate_nonblank("cell color", &color.value)?;
        insert_exact(keys, &color.key, "configuration_cell_color", ordinal)?;
    }
    if let Some(multiplicity) = &field.multiplicity {
        if multiplicity.value != "*" {
            return Err(StateTransportError::InvalidTerm(
                "unsupported cell multiplicity",
            ));
        }
        insert_exact(
            keys,
            &multiplicity.key,
            "configuration_cell_multiplicity",
            ordinal,
        )?;
    }
    if let Some(cell_type) = &field.cell_type {
        if field.multiplicity.is_none() {
            return Err(StateTransportError::InvalidTerm(
                "cell type requires repeated multiplicity",
            ));
        }
        if !matches!(cell_type.value.as_str(), "Bag" | "List" | "Map" | "Set") {
            return Err(StateTransportError::InvalidTerm(
                "unsupported repeated-cell collection type",
            ));
        }
        insert_exact(keys, &cell_type.key, "configuration_cell_type", ordinal)?;
    }
    Ok(emitted)
}

fn validate_root(
    root: &DescriptorConfigurationRoot,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if let DescriptorConfigurationRoot::Named { key, name } = root {
        validate_nonblank("configuration root name", name)?;
        insert_exact(keys, key, "configuration_root", 0)?;
    }
    Ok(())
}

fn validate_descriptor_initializer(
    initializer: &DescriptorConfigurationInitializer,
    owner: &StableItemId,
    declaration: &DescriptorConfigurationDeclaration,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if &initializer.owner != owner {
        return Err(StateTransportError::InitializerDeclarationMismatch);
    }
    insert_exact(keys, &initializer.key, "initializer_declaration", 0)?;
    insert_exact(keys, &initializer.owner_key, "initializer_result_type", 0)?;
    insert_exact(keys, &initializer.body_key, "initializer_body", 0)?;
    let bindings = validate_descriptor_variables(&initializer.variables, keys)?;
    let mut counters = InitializerCounters::default();
    validate_descriptor_initializer_cells(
        &initializer.cells,
        &declaration.fields,
        owner,
        &bindings,
        &mut counters,
        keys,
    )
}

fn validate_host_initializer(
    initializer: &HostConfigurationInitializer,
    owner: HostTypeKey,
    declaration: &HostConfigurationDeclaration,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if initializer.owner.resolve() != owner.resolve() {
        return Err(StateTransportError::InitializerDeclarationMismatch);
    }
    insert_exact(keys, &initializer.key, "initializer_declaration", 0)?;
    insert_exact(keys, &initializer.owner_key, "initializer_result_type", 0)?;
    insert_exact(keys, &initializer.body_key, "initializer_body", 0)?;
    let bindings = validate_host_variables(&initializer.variables, keys)?;
    let mut counters = InitializerCounters::default();
    validate_host_initializer_cells(
        &initializer.cells,
        &declaration.fields,
        owner,
        &bindings,
        &mut counters,
        keys,
    )
}

fn validate_descriptor_variables(
    variables: &[DescriptorConfigurationVariable],
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<BTreeSet<String>, StateTransportError> {
    let mut bindings = BTreeSet::new();
    let mut external_names = BTreeSet::new();
    let mut main_count = 0;
    for (index, variable) in variables.iter().enumerate() {
        let ordinal = checked_index(index)?;
        validate_rust_field(&variable.binding)?;
        validate_nonblank(
            "external configuration variable name",
            &variable.external_name,
        )?;
        if !bindings.insert(variable.binding.clone()) {
            return Err(StateTransportError::DuplicateValue(
                "configuration variable bindings",
            ));
        }
        if !external_names.insert(variable.external_name.clone()) {
            return Err(StateTransportError::DuplicateValue(
                "external configuration variable names",
            ));
        }
        insert_exact(
            keys,
            &variable.binding_key,
            "configuration_variable",
            ordinal,
        )?;
        insert_exact(
            keys,
            &variable.external_name_key,
            "configuration_variable_name",
            ordinal,
        )?;
        insert_exact(
            keys,
            &variable.sort.key,
            "configuration_variable_type",
            ordinal,
        )?;
        variable
            .sort
            .sort
            .validate()
            .map_err(|_| StateTransportError::InvalidCellContent("invalid variable sort"))?;
        if let Some(main_key) = &variable.main_key {
            main_count += 1;
            insert_exact(keys, main_key, "configuration_variable_main", ordinal)?;
        }
    }
    if main_count > 1 {
        return Err(StateTransportError::MultipleMainVariables);
    }
    Ok(bindings)
}

fn validate_host_variables(
    variables: &[HostConfigurationVariable],
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<BTreeSet<String>, StateTransportError> {
    let mut bindings = BTreeSet::new();
    let mut external_names = BTreeSet::new();
    let mut main_count = 0;
    for (index, variable) in variables.iter().enumerate() {
        let ordinal = checked_index(index)?;
        validate_rust_field(&variable.binding)?;
        validate_nonblank(
            "external configuration variable name",
            &variable.external_name,
        )?;
        if !bindings.insert(variable.binding.clone()) {
            return Err(StateTransportError::DuplicateValue(
                "configuration variable bindings",
            ));
        }
        if !external_names.insert(variable.external_name.clone()) {
            return Err(StateTransportError::DuplicateValue(
                "external configuration variable names",
            ));
        }
        insert_exact(
            keys,
            &variable.binding_key,
            "configuration_variable",
            ordinal,
        )?;
        insert_exact(
            keys,
            &variable.external_name_key,
            "configuration_variable_name",
            ordinal,
        )?;
        insert_exact(
            keys,
            &variable.sort.key,
            "configuration_variable_type",
            ordinal,
        )?;
        if let Some(main_key) = &variable.main_key {
            main_count += 1;
            insert_exact(keys, main_key, "configuration_variable_main", ordinal)?;
        }
    }
    if main_count > 1 {
        return Err(StateTransportError::MultipleMainVariables);
    }
    Ok(bindings)
}

#[derive(Default)]
struct InitializerCounters {
    cell: u32,
    constructor: u32,
    term: u32,
    term_path: u32,
    k_payload: u32,
    k_item: u32,
    k_tail: u32,
    map_payload: u32,
    map_key: u32,
    map_value: u32,
    map_update_base: u32,
}

fn validate_descriptor_initializer_cells(
    cells: &[DescriptorInitializerCell],
    declarations: &[DescriptorCellField],
    owner: &StableItemId,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if cells.is_empty() {
        return Err(StateTransportError::EmptyCollection(
            "initializer cell fields",
        ));
    }
    if cells.len() != declarations.len() {
        return Err(StateTransportError::InitializerDeclarationMismatch);
    }
    for (cell, declaration) in cells.iter().zip(declarations) {
        if cell.field.cell.owner != *owner
            || cell.field.cell != declaration.reference.cell
            || cell.field.cell.field != declaration.rust_field
        {
            return Err(StateTransportError::InitializerDeclarationMismatch);
        }
        validate_descriptor_initializer_cell(
            cell,
            Some(declaration),
            owner,
            bindings,
            counters,
            keys,
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_lines)] // Stable and host validation stay visibly isomorphic.
fn validate_descriptor_initializer_cell(
    cell: &DescriptorInitializerCell,
    declaration: Option<&DescriptorCellField>,
    owner: &StableItemId,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    cell.field.cell.validate()?;
    if &cell.field.cell.owner != owner {
        return Err(StateTransportError::CellOwnerMismatch);
    }
    insert_exact(keys, &cell.key, "initializer_cell", counters.cell)?;
    insert_exact(keys, &cell.field.key, "initializer_field", counters.cell)?;
    counters.cell = increment(counters.cell)?;
    match (&cell.content, declaration.map(|field| &field.content)) {
        (
            ProtocolInitializerCellContent::Leaf {
                constructor_key,
                wrapper,
                value,
            },
            Some(ProtocolCellContent::Leaf {
                wrapper: declared_wrapper,
                ..
            }),
        ) if wrapper == declared_wrapper => {
            insert_exact(
                keys,
                constructor_key,
                "initializer_cell_constructor",
                counters.constructor,
            )?;
            counters.constructor = increment(counters.constructor)?;
            validate_wrapper_state(*wrapper, value)?;
            validate_descriptor_state_term(value, bindings, counters, keys)
        }
        (
            ProtocolInitializerCellContent::Nested {
                declaration: nested,
                children,
            },
            Some(ProtocolCellContent::Nested {
                declaration: declared,
            }),
        ) if nested.declaration == declared.declaration => {
            if children.is_empty() {
                return Err(StateTransportError::EmptyCollection(
                    "nested initializer children",
                ));
            }
            nested.validate()?;
            insert_exact(
                keys,
                &nested.key,
                "initializer_nested_constructor",
                counters.constructor,
            )?;
            counters.constructor = increment(counters.constructor)?;
            validate_descriptor_nested_children(
                children,
                &nested.declaration,
                bindings,
                counters,
                keys,
            )
        }
        (
            ProtocolInitializerCellContent::Leaf {
                constructor_key,
                wrapper,
                value,
            },
            None,
        ) => {
            insert_exact(
                keys,
                constructor_key,
                "initializer_cell_constructor",
                counters.constructor,
            )?;
            counters.constructor = increment(counters.constructor)?;
            validate_wrapper_state(*wrapper, value)?;
            validate_descriptor_state_term(value, bindings, counters, keys)
        }
        (
            ProtocolInitializerCellContent::Nested {
                declaration: nested,
                children,
            },
            None,
        ) => {
            if children.is_empty() {
                return Err(StateTransportError::EmptyCollection(
                    "nested initializer children",
                ));
            }
            nested.validate()?;
            insert_exact(
                keys,
                &nested.key,
                "initializer_nested_constructor",
                counters.constructor,
            )?;
            counters.constructor = increment(counters.constructor)?;
            validate_descriptor_nested_children(
                children,
                &nested.declaration,
                bindings,
                counters,
                keys,
            )
        }
        _ => Err(StateTransportError::InitializerDeclarationMismatch),
    }
}

fn validate_descriptor_nested_children(
    children: &[DescriptorInitializerCell],
    owner: &StableItemId,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    let mut fields = BTreeSet::new();
    for child in children {
        if child.field.cell.owner != *owner || !fields.insert(child.field.cell.field.clone()) {
            return Err(StateTransportError::InitializerDeclarationMismatch);
        }
        validate_descriptor_initializer_cell(child, None, owner, bindings, counters, keys)?;
    }
    Ok(())
}

fn validate_host_initializer_cells(
    cells: &[HostInitializerCell],
    declarations: &[HostCellField],
    owner: HostTypeKey,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if cells.is_empty() {
        return Err(StateTransportError::EmptyCollection(
            "initializer cell fields",
        ));
    }
    if cells.len() != declarations.len() {
        return Err(StateTransportError::InitializerDeclarationMismatch);
    }
    for (cell, declaration) in cells.iter().zip(declarations) {
        if cell.field.cell.resolve() != declaration.reference.cell.resolve()
            || cell.field.cell.owner.resolve() != owner.resolve()
        {
            return Err(StateTransportError::InitializerDeclarationMismatch);
        }
        validate_host_initializer_cell(cell, Some(declaration), owner, bindings, counters, keys)?;
    }
    Ok(())
}

#[allow(clippy::too_many_lines)] // Stable and host validation stay visibly isomorphic.
fn validate_host_initializer_cell(
    cell: &HostInitializerCell,
    declaration: Option<&HostCellField>,
    owner: HostTypeKey,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if cell.field.cell.owner.resolve() != owner.resolve() {
        return Err(StateTransportError::CellOwnerMismatch);
    }
    insert_exact(keys, &cell.key, "initializer_cell", counters.cell)?;
    insert_exact(keys, &cell.field.key, "initializer_field", counters.cell)?;
    counters.cell = increment(counters.cell)?;
    match (&cell.content, declaration.map(|field| &field.content)) {
        (
            ProtocolInitializerCellContent::Leaf {
                constructor_key,
                wrapper,
                value,
            },
            Some(ProtocolCellContent::Leaf {
                wrapper: declared_wrapper,
                ..
            }),
        ) if wrapper == declared_wrapper => {
            insert_exact(
                keys,
                constructor_key,
                "initializer_cell_constructor",
                counters.constructor,
            )?;
            counters.constructor = increment(counters.constructor)?;
            validate_wrapper_state(*wrapper, value)?;
            validate_host_state_term(value, bindings, counters, keys)
        }
        (
            ProtocolInitializerCellContent::Nested {
                declaration: nested,
                children,
            },
            Some(ProtocolCellContent::Nested {
                declaration: declared,
            }),
        ) if nested.declaration.key.resolve() == declared.declaration.key.resolve() => {
            if children.is_empty() {
                return Err(StateTransportError::EmptyCollection(
                    "nested initializer children",
                ));
            }
            insert_exact(
                keys,
                &nested.key,
                "initializer_nested_constructor",
                counters.constructor,
            )?;
            counters.constructor = increment(counters.constructor)?;
            validate_host_nested_children(
                children,
                nested.declaration.key,
                bindings,
                counters,
                keys,
            )
        }
        (
            ProtocolInitializerCellContent::Leaf {
                constructor_key,
                wrapper,
                value,
            },
            None,
        ) => {
            insert_exact(
                keys,
                constructor_key,
                "initializer_cell_constructor",
                counters.constructor,
            )?;
            counters.constructor = increment(counters.constructor)?;
            validate_wrapper_state(*wrapper, value)?;
            validate_host_state_term(value, bindings, counters, keys)
        }
        (
            ProtocolInitializerCellContent::Nested {
                declaration: nested,
                children,
            },
            None,
        ) => {
            if children.is_empty() {
                return Err(StateTransportError::EmptyCollection(
                    "nested initializer children",
                ));
            }
            insert_exact(
                keys,
                &nested.key,
                "initializer_nested_constructor",
                counters.constructor,
            )?;
            counters.constructor = increment(counters.constructor)?;
            validate_host_nested_children(
                children,
                nested.declaration.key,
                bindings,
                counters,
                keys,
            )
        }
        _ => Err(StateTransportError::InitializerDeclarationMismatch),
    }
}

fn validate_host_nested_children(
    children: &[HostInitializerCell],
    owner: HostTypeKey,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    let mut fields = BTreeSet::new();
    for child in children {
        if child.field.cell.owner.resolve() != owner.resolve()
            || !fields.insert(child.field.cell.field.resolve())
        {
            return Err(StateTransportError::InitializerDeclarationMismatch);
        }
        validate_host_initializer_cell(child, None, owner, bindings, counters, keys)?;
    }
    Ok(())
}

fn validate_wrapper_state<T>(
    wrapper: CellWrapper,
    value: &ProtocolInitializerStateTerm<T>,
) -> Result<(), StateTransportError> {
    match (wrapper, value) {
        (CellWrapper::KCell, ProtocolInitializerStateTerm::KSequence(_))
        | (
            CellWrapper::Cell,
            ProtocolInitializerStateTerm::Term(_) | ProtocolInitializerStateTerm::Map(_),
        ) => Ok(()),
        _ => Err(StateTransportError::InvalidCellContent(
            "wrapper and initializer state family disagree",
        )),
    }
}

fn validate_descriptor_state_term(
    value: &DescriptorInitializerStateTerm,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    match value {
        ProtocolInitializerStateTerm::Term(term) => {
            validate_descriptor_initializer_term(term, bindings, counters, keys, None)
        }
        ProtocolInitializerStateTerm::KSequence(sequence) => {
            validate_k_sequence_shell(sequence, counters, keys)?;
            for item in &sequence.items {
                insert_exact(keys, &item.key, "k_sequence_item", counters.k_item)?;
                counters.k_item = increment(counters.k_item)?;
                validate_descriptor_initializer_term(
                    &item.value,
                    bindings,
                    counters,
                    keys,
                    Some(&item.key),
                )?;
            }
            Ok(())
        }
        ProtocolInitializerStateTerm::Map(map) => {
            validate_map_shell(map, counters, keys)?;
            match &map.body {
                ProtocolMapBody::Empty { .. } => Ok(()),
                ProtocolMapBody::Items { items } => {
                    for item in items {
                        insert_exact(keys, &item.key_key, "map_key", counters.map_key)?;
                        counters.map_key = increment(counters.map_key)?;
                        insert_exact(keys, &item.value_key, "map_value", counters.map_value)?;
                        counters.map_value = increment(counters.map_value)?;
                        validate_descriptor_initializer_term(
                            &item.key,
                            bindings,
                            counters,
                            keys,
                            Some(&item.key_key),
                        )?;
                        validate_descriptor_initializer_term(
                            &item.value,
                            bindings,
                            counters,
                            keys,
                            Some(&item.value_key),
                        )?;
                    }
                    Ok(())
                }
                ProtocolMapBody::Update {
                    base_key,
                    base,
                    key_key,
                    key,
                    value_key,
                    value,
                } => {
                    insert_exact(keys, base_key, "map_update_base", counters.map_update_base)?;
                    counters.map_update_base = increment(counters.map_update_base)?;
                    insert_exact(keys, key_key, "map_key", counters.map_key)?;
                    counters.map_key = increment(counters.map_key)?;
                    insert_exact(keys, value_key, "map_value", counters.map_value)?;
                    counters.map_value = increment(counters.map_value)?;
                    validate_descriptor_initializer_term(
                        base,
                        bindings,
                        counters,
                        keys,
                        Some(base_key),
                    )?;
                    validate_descriptor_initializer_term(
                        key,
                        bindings,
                        counters,
                        keys,
                        Some(key_key),
                    )?;
                    validate_descriptor_initializer_term(
                        value,
                        bindings,
                        counters,
                        keys,
                        Some(value_key),
                    )
                }
            }
        }
    }
}

fn validate_host_state_term(
    value: &HostInitializerStateTerm,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    match value {
        ProtocolInitializerStateTerm::Term(term) => {
            validate_host_initializer_term(term, bindings, counters, keys, None)
        }
        ProtocolInitializerStateTerm::KSequence(sequence) => {
            validate_k_sequence_shell(sequence, counters, keys)?;
            for item in &sequence.items {
                insert_exact(keys, &item.key, "k_sequence_item", counters.k_item)?;
                counters.k_item = increment(counters.k_item)?;
                validate_host_initializer_term(
                    &item.value,
                    bindings,
                    counters,
                    keys,
                    Some(&item.key),
                )?;
            }
            Ok(())
        }
        ProtocolInitializerStateTerm::Map(map) => {
            validate_map_shell(map, counters, keys)?;
            match &map.body {
                ProtocolMapBody::Empty { .. } => Ok(()),
                ProtocolMapBody::Items { items } => {
                    for item in items {
                        insert_exact(keys, &item.key_key, "map_key", counters.map_key)?;
                        counters.map_key = increment(counters.map_key)?;
                        insert_exact(keys, &item.value_key, "map_value", counters.map_value)?;
                        counters.map_value = increment(counters.map_value)?;
                        validate_host_initializer_term(
                            &item.key,
                            bindings,
                            counters,
                            keys,
                            Some(&item.key_key),
                        )?;
                        validate_host_initializer_term(
                            &item.value,
                            bindings,
                            counters,
                            keys,
                            Some(&item.value_key),
                        )?;
                    }
                    Ok(())
                }
                ProtocolMapBody::Update {
                    base_key,
                    base,
                    key_key,
                    key,
                    value_key,
                    value,
                } => {
                    insert_exact(keys, base_key, "map_update_base", counters.map_update_base)?;
                    counters.map_update_base = increment(counters.map_update_base)?;
                    insert_exact(keys, key_key, "map_key", counters.map_key)?;
                    counters.map_key = increment(counters.map_key)?;
                    insert_exact(keys, value_key, "map_value", counters.map_value)?;
                    counters.map_value = increment(counters.map_value)?;
                    validate_host_initializer_term(base, bindings, counters, keys, Some(base_key))?;
                    validate_host_initializer_term(key, bindings, counters, keys, Some(key_key))?;
                    validate_host_initializer_term(value, bindings, counters, keys, Some(value_key))
                }
            }
        }
    }
}

fn validate_k_sequence_shell<T>(
    sequence: &ProtocolKSequence<T>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if let Some(payload_key) = &sequence.payload_key {
        insert_exact(keys, payload_key, "k_sequence_payload", counters.k_payload)?;
        counters.k_payload = increment(counters.k_payload)?;
    }
    match sequence.notation {
        DescriptorKSequenceNotation::DotK => {
            if !sequence.items.is_empty() || sequence.payload_key.is_none() {
                return Err(StateTransportError::InvalidCellContent(
                    "standalone .K must be empty and have payload provenance",
                ));
            }
            let dot_key =
                sequence
                    .dot_k_key
                    .as_ref()
                    .ok_or(StateTransportError::InvalidCellContent(
                        ".K is missing exact provenance",
                    ))?;
            insert_exact(keys, dot_key, "k_sequence_tail", counters.k_tail)?;
            counters.k_tail = increment(counters.k_tail)?;
        }
        DescriptorKSequenceNotation::Comma | DescriptorKSequenceNotation::Operator => {
            if sequence.dot_k_key.is_some()
                || (!sequence.items.is_empty() && sequence.payload_key.is_none())
                || (sequence.notation == DescriptorKSequenceNotation::Operator
                    && sequence.items.len() < 2)
            {
                return Err(StateTransportError::InvalidCellContent(
                    "invalid exact K-sequence shell",
                ));
            }
        }
    }
    Ok(())
}

fn validate_map_shell<T>(
    map: &ProtocolMap<T>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if let Some(payload_key) = &map.payload_key {
        insert_exact(keys, payload_key, "map_payload", counters.map_payload)?;
        counters.map_payload = increment(counters.map_payload)?;
    }
    match &map.body {
        ProtocolMapBody::Empty { explicit_dot } => {
            if *explicit_dot != map.payload_key.is_some() {
                return Err(StateTransportError::InvalidCellContent(
                    "empty map payload provenance disagrees with notation",
                ));
            }
        }
        ProtocolMapBody::Items { items } => {
            if items.is_empty() || map.payload_key.is_none() {
                return Err(StateTransportError::InvalidCellContent(
                    "map item form requires a nonempty payload",
                ));
            }
        }
        ProtocolMapBody::Update { .. } if map.payload_key.is_none() => {
            return Err(StateTransportError::InvalidCellContent(
                "map update requires payload provenance",
            ));
        }
        ProtocolMapBody::Update { .. } => {}
    }
    Ok(())
}

fn validate_descriptor_initializer_term(
    term: &ProtocolInitializerTerm<DescriptorTerm>,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
    structural_key: Option<&ProvenanceKey>,
) -> Result<(), StateTransportError> {
    insert_exact(keys, &term.key, "initializer_term", counters.term)?;
    counters.term = increment(counters.term)?;
    validate_descriptor_term_node(
        &term.term,
        bindings,
        counters,
        keys,
        structural_key.unwrap_or(&term.key),
    )
}

fn validate_descriptor_term_node(
    term: &DescriptorTerm,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
    structural_key: &ProvenanceKey,
) -> Result<(), StateTransportError> {
    match term {
        DescriptorTerm::Variable {
            key,
            path_key,
            name,
        } => {
            if key != path_key || !bindings.contains(name) {
                return Err(StateTransportError::InvalidTerm(
                    "variable keys disagree or the binding is undeclared",
                ));
            }
            insert_exact(keys, key, "initializer_term_path", counters.term_path)?;
            counters.term_path = increment(counters.term_path)?;
            Ok(())
        }
        DescriptorTerm::Application {
            head_class,
            reference,
            path_key,
            arguments,
        } => {
            if &reference.key != path_key
                || (*head_class == DescriptorApplicationHeadClass::BareReference
                    && !arguments.is_empty())
            {
                return Err(StateTransportError::InvalidTerm(
                    "application path keys or head class are invalid",
                ));
            }
            reference
                .application
                .validate()
                .map_err(|_| StateTransportError::InvalidTerm("invalid application target"))?;
            insert_exact(
                keys,
                &reference.key,
                "initializer_term_path",
                counters.term_path,
            )?;
            counters.term_path = increment(counters.term_path)?;
            for argument in arguments {
                match argument {
                    DescriptorTermArgument::Positional { value } => validate_descriptor_term_node(
                        value,
                        bindings,
                        counters,
                        keys,
                        structural_key,
                    )?,
                    DescriptorTermArgument::Named { .. } => {
                        return Err(StateTransportError::InvalidTerm(
                            "initializer syntax has no exact record-field provenance",
                        ));
                    }
                }
            }
            Ok(())
        }
        DescriptorTerm::Literal { key, literal } => {
            if key != structural_key {
                return Err(StateTransportError::UnexpectedProvenance {
                    expected: structural_key.clone(),
                    actual: key.clone(),
                });
            }
            if matches!(literal, crate::DescriptorLiteral::Int(value) if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()))
            {
                return Err(StateTransportError::InvalidTerm(
                    "integer literal is not canonical unsigned decimal",
                ));
            }
            keys.insert(key.clone());
            Ok(())
        }
        DescriptorTerm::Wildcard { .. } => Err(StateTransportError::InvalidTerm(
            "wildcards are not allowed in initializers",
        )),
        DescriptorTerm::BuiltinToken { .. }
        | DescriptorTerm::Anonymous { .. }
        | DescriptorTerm::OrBool { .. } => Err(StateTransportError::InvalidTerm(
            "claim-only terms are not allowed in initializers",
        )),
        DescriptorTerm::Cell { .. } => Err(StateTransportError::InvalidTerm(
            "fragment! terms are not allowed in initializers",
        )),
    }
}

fn validate_host_initializer_term(
    term: &ProtocolInitializerTerm<HostTerm>,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
    structural_key: Option<&ProvenanceKey>,
) -> Result<(), StateTransportError> {
    insert_exact(keys, &term.key, "initializer_term", counters.term)?;
    counters.term = increment(counters.term)?;
    validate_host_term_node(
        &term.term,
        bindings,
        counters,
        keys,
        structural_key.unwrap_or(&term.key),
    )
}

fn validate_host_term_node(
    term: &HostTerm,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
    structural_key: &ProvenanceKey,
) -> Result<(), StateTransportError> {
    match term {
        HostTerm::Variable {
            key,
            path_key,
            name,
        } => {
            if key != path_key || !bindings.contains(name) {
                return Err(StateTransportError::InvalidTerm(
                    "variable keys disagree or the binding is undeclared",
                ));
            }
            insert_exact(keys, key, "initializer_term_path", counters.term_path)?;
            counters.term_path = increment(counters.term_path)?;
            Ok(())
        }
        HostTerm::Application {
            head_class,
            reference,
            path_key,
            arguments,
        } => {
            if &reference.key != path_key
                || (*head_class == DescriptorApplicationHeadClass::BareReference
                    && !arguments.is_empty())
            {
                return Err(StateTransportError::InvalidTerm(
                    "application path keys or head class are invalid",
                ));
            }
            insert_exact(
                keys,
                &reference.key,
                "initializer_term_path",
                counters.term_path,
            )?;
            counters.term_path = increment(counters.term_path)?;
            for argument in arguments {
                match argument {
                    HostTermArgument::Positional { value } => {
                        validate_host_term_node(value, bindings, counters, keys, structural_key)?;
                    }
                    HostTermArgument::Named { .. } => {
                        return Err(StateTransportError::InvalidTerm(
                            "initializer syntax has no exact record-field provenance",
                        ));
                    }
                }
            }
            Ok(())
        }
        HostTerm::Literal { key, literal } => {
            if key != structural_key {
                return Err(StateTransportError::UnexpectedProvenance {
                    expected: structural_key.clone(),
                    actual: key.clone(),
                });
            }
            if matches!(literal, crate::DescriptorLiteral::Int(value) if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()))
            {
                return Err(StateTransportError::InvalidTerm(
                    "integer literal is not canonical unsigned decimal",
                ));
            }
            keys.insert(key.clone());
            Ok(())
        }
        HostTerm::Wildcard { .. } => Err(StateTransportError::InvalidTerm(
            "wildcards are not allowed in initializers",
        )),
        HostTerm::BuiltinToken { .. } | HostTerm::Anonymous { .. } | HostTerm::OrBool { .. } => {
            Err(StateTransportError::InvalidTerm(
                "claim-only terms are not allowed in initializers",
            ))
        }
        HostTerm::Cell { .. } => Err(StateTransportError::InvalidTerm(
            "fragment! terms are not allowed in initializers",
        )),
    }
}

fn validate_k_cell_sort(
    wrapper: CellWrapper,
    sort: &DescriptorSortRef,
) -> Result<(), StateTransportError> {
    if wrapper == CellWrapper::KCell && sort != &DescriptorSortRef::Builtin(BuiltinSort::KSequence)
    {
        return Err(StateTransportError::InvalidCellContent(
            "KCell content sort must be builtin KSequence",
        ));
    }
    Ok(())
}

fn require_cell_owner_kind(
    owner: &StableItemId,
    field: &'static str,
) -> Result<(), StateTransportError> {
    if matches!(owner.item_kind(), ItemKind::Configuration | ItemKind::Cell) {
        Ok(())
    } else {
        Err(StateTransportError::ItemKind {
            field,
            expected: "Configuration or Cell",
            actual: owner.item_kind(),
        })
    }
}

fn validate_rust_field(value: &str) -> Result<(), StateTransportError> {
    if value.trim().is_empty() || value.contains("::") || value.contains(['/', '\\']) {
        Err(StateTransportError::InvalidText("Rust field identity"))
    } else {
        Ok(())
    }
}

fn validate_nonblank(field: &'static str, value: &str) -> Result<(), StateTransportError> {
    if value.trim().is_empty() {
        Err(StateTransportError::InvalidText(field))
    } else {
        Ok(())
    }
}

fn validate_complete_set(
    primary: &ProvenanceKey,
    actual: &BTreeSet<ProvenanceKey>,
    expected: &BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    let expected_primary = canonical_key("configuration_declaration", 0);
    if primary != &expected_primary {
        return Err(StateTransportError::UnexpectedProvenance {
            expected: expected_primary,
            actual: primary.clone(),
        });
    }
    if let Some(missing) = expected.difference(actual).next() {
        return Err(StateTransportError::MissingProvenance(missing.clone()));
    }
    if let Some(extra) = actual.difference(expected).next() {
        return Err(StateTransportError::ExtraProvenance(extra.clone()));
    }
    Ok(())
}

fn insert_exact(
    keys: &mut BTreeSet<ProvenanceKey>,
    actual: &ProvenanceKey,
    role: &'static str,
    ordinal: u32,
) -> Result<(), StateTransportError> {
    let expected = canonical_key(role, ordinal);
    if actual != &expected {
        return Err(StateTransportError::UnexpectedProvenance {
            expected,
            actual: actual.clone(),
        });
    }
    keys.insert(actual.clone());
    Ok(())
}

fn canonical_key(role: &'static str, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal).expect("protocol-owned provenance roles are valid")
}

fn checked_index(index: usize) -> Result<u32, StateTransportError> {
    u32::try_from(index)
        .map_err(|_| StateTransportError::InvalidCellContent("provenance ordinal exceeds u32"))
}

fn increment(value: u32) -> Result<u32, StateTransportError> {
    value
        .checked_add(1)
        .ok_or(StateTransportError::InvalidCellContent(
            "provenance ordinal exceeds u32",
        ))
}

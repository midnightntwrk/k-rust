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

use super::detail::{StateCellContentReason, StateTermReason, TransportField, TransportItemKind};
use crate::stage::{DescriptorStage, HostStage, Stage, protocol_shape, stage_shape};

use crate::host::{HostTypeKey, HostTypeReference};
use crate::transport::grammar::{
    CellTermField, DescriptorApplicationHeadClass, DescriptorSortRef, DescriptorSortReference,
    DescriptorTerm, HostSortReference, HostTerm, Term,
};
use crate::{
    BuiltinSort, DescriptorLiteral, ItemKind, ProductionFieldId, ProvenanceKey, ProvenanceRole,
    StableItemId,
};

use super::validation::{TermValidation, ValidationStage, validate_term};

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

/// Supported K collection spellings for repeated-cell declarations.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(try_from = "String", into = "String")]
pub enum DescriptorCellCollectionType {
    /// Commutative bag collection.
    Bag,
    /// Ordered list collection.
    List,
    /// Keyed map collection.
    Map,
    /// Commutative set collection.
    Set,
}

impl TryFrom<String> for DescriptorCellCollectionType {
    type Error = StateTransportError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        match value.as_str() {
            "Bag" => Ok(Self::Bag),
            "List" => Ok(Self::List),
            "Map" => Ok(Self::Map),
            "Set" => Ok(Self::Set),
            _ => Err(StateTransportError::InvalidTerm(
                StateTermReason::UnsupportedRepeatedCellCollection,
            )),
        }
    }
}

impl From<DescriptorCellCollectionType> for crate::CellCollectionType {
    fn from(value: DescriptorCellCollectionType) -> Self {
        match value {
            DescriptorCellCollectionType::Bag => Self::Bag,
            DescriptorCellCollectionType::List => Self::List,
            DescriptorCellCollectionType::Map => Self::Map,
            DescriptorCellCollectionType::Set => Self::Set,
        }
    }
}

impl From<DescriptorCellCollectionType> for String {
    fn from(value: DescriptorCellCollectionType) -> Self {
        crate::CellCollectionType::from(value).as_str().into()
    }
}

/// Optional classified repeated-cell collection type.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields, try_from = "DescriptorCellTypeWire")]
pub struct DescriptorCellType {
    /// Exact string-literal provenance.
    pub key: ProvenanceKey,
    /// Exact supported K collection type spelling.
    pub value: DescriptorCellCollectionType,
}

/// Plain string wire shape for the repeated-cell collection attribute.
#[doc(hidden)]
#[derive(Deserialize)]
#[serde(rename = "DescriptorCellType", deny_unknown_fields)]
pub struct DescriptorCellTypeWire {
    key: ProvenanceKey,
    value: String,
}

impl TryFrom<DescriptorCellTypeWire> for DescriptorCellType {
    type Error = StateTransportError;
    fn try_from(value: DescriptorCellTypeWire) -> Result<Self, Self::Error> {
        Ok(Self {
            key: value.key,
            value: value.value.try_into()?,
        })
    }
}

protocol_shape! {
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
    pub enum ProtocolCellContent<S => sort_map => S2, N => nominal_map => N2> {
        /// `Cell<T>` or `KCell<KSequence>` leaf.
        Leaf {
            /// Exact wrapper-path provenance.
            wrapper_key: ProvenanceKey => [keep],
            /// Typed wrapper meaning; path spelling is not semantic.
            wrapper: CellWrapper => [keep],
            /// Exact declared or builtin content sort.
            sort: S => [sort_map],
            /// Generic object-sort arguments retained for cell-pattern inference.
            #[serde(default, skip_serializing_if = "Vec::is_empty")]
            arguments: Vec<S> => [vec sort_map],
        },
        /// Field whose type is another nominal `#[k::cell]` declaration.
        Nested {
            /// Typed reference to that declaration.
            declaration: N => [nominal_map],
        },
    }
}

protocol_shape! {
    /// One ordered fixed-cell declaration field.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolCellField<I => cell_map => I2, S => sort_map => S2, N => nominal_map => N2> {
        /// Exact `configuration_field` provenance and nominal identity.
        pub reference: I => [cell_map],
        /// Stable Rust field name.
        /// This must agree with the stable identity.
        pub rust_field: String => [keep],
        /// Optional authored name override; absence emits `rust_field`.
        pub emitted_name: Option<DescriptorCellName> => [keep],
        /// Optional classified color.
        pub color: Option<DescriptorCellColor> => [keep],
        /// Optional repeated-cell multiplicity.
        pub multiplicity: Option<DescriptorCellMultiplicity> => [keep],
        /// Optional repeated-cell collection type.
        pub cell_type: Option<DescriptorCellType> => [keep],
        /// Typed leaf or nested content.
        pub content: ProtocolCellContent<S, N> => [nested sort_map nominal_map],
    }
    map_order: [content, reference, rust_field, emitted_name, color, multiplicity, cell_type];
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

protocol_shape! {
    /// Ordered fields owned by one configuration or nominal nested-cell item.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolCellDeclaration<F => field_map => F2> {
        /// Complete declaration-name provenance.
        pub key: ProvenanceKey => [keep],
        /// Nonempty fixed fields in authored order.
        pub fields: Vec<F> => [vec field_map],
    }
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

protocol_shape! {
    /// One ordered external configuration variable.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolConfigurationVariable<S => sort_map => S2> {
        /// Exact Rust binding provenance.
        pub binding_key: ProvenanceKey => [keep],
        /// Authored Rust binding name used by initializer terms.
        pub binding: String => [keep],
        /// Exact external-name literal provenance.
        pub external_name_key: ProvenanceKey => [keep],
        /// Nonempty external K variable name.
        pub external_name: String => [keep],
        /// Typed variable sort and exact type-path provenance.
        pub sort: S => [sort_map],
        /// Exact optional `main` marker provenance.
        pub main_key: Option<ProvenanceKey> => [keep],
    }
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

protocol_shape! {
    /// One ordinary structured term with its complete initializer-term anchor.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolInitializerTerm<T => term_map => T2> {
        /// Exact complete-term provenance.
        pub key: ProvenanceKey => [keep],
        /// Structured term payload.
        pub term: T => [term_map],
    }
}

protocol_shape! {
    /// One K-sequence item and its structural item provenance.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolKSequenceItem<T => term_map => T2> {
        /// Exact K-item provenance.
        pub key: ProvenanceKey => [keep],
        /// Structured item term and complete-term provenance.
        pub value: ProtocolInitializerTerm<T> => [nested term_map],
    }
}

protocol_shape! {
    /// Exact K sequence admitted by an initializer.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolKSequence<T => term_map => T2> {
        /// Complete payload provenance.
        /// Empty `k![]` alone has no inner endpoint.
        pub payload_key: Option<ProvenanceKey> => [keep],
        /// Exact `.K` provenance for standalone dot notation.
        pub dot_k_key: Option<ProvenanceKey> => [keep],
        /// Preserved parser classification.
        pub notation: DescriptorKSequenceNotation => [keep],
        /// Ordered sequence prefix; initializer sequences have no frame.
        pub items: Vec<ProtocolKSequenceItem<T>> => [vec nested term_map],
    }
}

protocol_shape! {
    /// One exact map item.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolMapItem<T => term_map => T2> {
        /// Exact key-expression provenance.
        pub key_key: ProvenanceKey => [keep],
        /// Structured key term.
        pub key: ProtocolInitializerTerm<T> => [nested term_map],
        /// Exact value-expression provenance.
        pub value_key: ProvenanceKey => [keep],
        /// Structured value term.
        pub value: ProtocolInitializerTerm<T> => [nested term_map],
    }
}

protocol_shape! {
    /// Empty map, ordered exact items, or one functional update.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(tag = "map_kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum ProtocolMapBody<T => term_map => T2> {
        /// `.Map` or empty `map![]`.
        Empty {
            /// Whether `.Map` was written explicitly.
            explicit_dot: bool => [keep],
        },
        /// Ordered exact map items.
        /// Initializers cannot contain a remainder.
        Items {
            /// Nonempty ordered key/value entries.
            items: Vec<ProtocolMapItem<T>> => [vec nested term_map],
        },
        /// Functional update `(base, key, value)`.
        Update {
            /// Exact base-expression provenance.
            base_key: ProvenanceKey => [keep],
            /// Existing map term.
            base: ProtocolInitializerTerm<T> => [nested term_map],
            /// Exact updated-key provenance.
            key_key: ProvenanceKey => [keep],
            /// Updated key term.
            key: ProtocolInitializerTerm<T> => [nested term_map],
            /// Exact replacement-value provenance.
            value_key: ProvenanceKey => [keep],
            /// Replacement value term.
            value: ProtocolInitializerTerm<T> => [nested term_map],
        },
    }
}

protocol_shape! {
    /// Structured exact map admitted by an initializer.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolMap<T => term_map => T2> {
        /// Complete payload provenance.
        /// Empty `map![]` alone has no inner endpoint.
        pub payload_key: Option<ProvenanceKey> => [keep],
        /// Typed map operation.
        pub body: ProtocolMapBody<T> => [nested term_map],
    }
}

protocol_shape! {
    /// Leaf state families admitted by a fixed initializer.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(
        tag = "state_term_kind",
        rename_all = "snake_case",
        deny_unknown_fields
    )]
    pub enum ProtocolInitializerStateTerm<T => term_map => T2> {
        /// Ordinary structured term.
        Term(value: ProtocolInitializerTerm<T> => [nested term_map]),
        /// Exact computation sequence.
        KSequence(value: ProtocolKSequence<T> => [nested term_map]),
        /// Exact map term.
        Map(value: ProtocolMap<T> => [nested term_map]),
    }
}

/// Stable initializer state term.
pub type DescriptorInitializerStateTerm = ProtocolInitializerStateTerm<DescriptorTerm>;

/// Host initializer state term.
pub type HostInitializerStateTerm = ProtocolInitializerStateTerm<HostTerm>;

protocol_shape! {
    /// Leaf or recursively nested initializer cell content.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(tag = "content_kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum ProtocolInitializerCellContent<I => cell_map => I2, N => nominal_map => N2, T => term_map => T2> {
        /// `Cell::new(...)` or `KCell::new(k![...])`.
        Leaf {
            /// Exact constructor-path provenance.
            constructor_key: ProvenanceKey => [keep],
            /// Typed wrapper meaning.
            wrapper: CellWrapper => [keep],
            /// Structured leaf state.
            value: T => [term_map],
        },
        /// Complete nominal nested-cell struct literal.
        Nested {
            /// Exact constructor reference.
            declaration: N => [nominal_map],
            /// Ordered nonempty child initializers.
            children: Vec<ProtocolInitializerCell<I, N, T>> => [vec nested cell_map nominal_map term_map],
        },
    }
}

protocol_shape! {
    /// One node of a recursive initializer forest.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolInitializerCell<I => cell_map => I2, N => nominal_map => N2, T => term_map => T2> {
        /// Exact initializer-cell node provenance.
        pub key: ProvenanceKey => [keep],
        /// Exact field occurrence and owner-qualified identity.
        pub field: I => [cell_map],
        /// Leaf or nested content.
        pub content: ProtocolInitializerCellContent<I, N, T> => [nested cell_map nominal_map term_map],
    }
    map_order: [content, key, field];
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

protocol_shape! {
    /// Complete paired initializer payload.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolConfigurationInitializer<O => owner_map => O2, V => variable_map => V2, C => cell_map => C2> {
        /// Exact associated-function declaration provenance.
        pub key: ProvenanceKey => [keep],
        /// Exact `Self` result-type provenance.
        pub owner_key: ProvenanceKey => [keep],
        /// Configuration owner identity.
        /// Host forms use a `HostTypeKey`.
        pub owner: O => [owner_map],
        /// Variables in parameter order.
        pub variables: Vec<V> => [vec variable_map],
        /// Complete declarative body provenance.
        pub body_key: ProvenanceKey => [keep],
        /// Complete ordered top-level initializer forest.
        pub cells: Vec<C> => [vec cell_map],
    }
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

stage_shape! {
    /// Complete non-rule configuration payload.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    #[serde(
        rename = "DescriptorFixedConfiguration",
        bound(
            serialize = "
                S::Sort: Serialize,
                S::Cell: Serialize,
                S::CellDeclaration: Serialize,
                S::InitializerOwner: Serialize,
                S::Application: Serialize,
                S::Nominal: Serialize
            ",
            deserialize = "
                S::Sort: Deserialize<'de>,
                S::Cell: Deserialize<'de>,
                S::CellDeclaration: Deserialize<'de>,
                S::InitializerOwner: Deserialize<'de>,
                S::Application: Deserialize<'de>,
                S::Nominal: Deserialize<'de>
            "
        )
    )]
    pub struct FixedConfiguration<S: Stage> {
        /// Generated or named top policy.
        pub root: DescriptorConfigurationRoot => [keep],
        /// Top-level declaration fields.
        pub declaration: StageCellDeclaration<S> => [with (map_declaration) S],
        /// Paired complete initializer.
        pub initializer: StageConfigurationInitializer<S> => [with (map_initializer) S],
    }
}

/// Stable descriptor-stage form of [`FixedConfiguration`].
pub type DescriptorFixedConfiguration = FixedConfiguration<DescriptorStage>;

/// Build-local host-stage form of [`FixedConfiguration`].
pub type HostFixedConfiguration = FixedConfiguration<HostStage>;

/// Typed local configuration transport error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StateTransportError {
    /// A required textual value was blank or path-shaped.
    InvalidText(TransportField),
    /// A collection required by the fixed grammar was empty.
    EmptyCollection(TransportField),
    /// A set-valued list repeated a value.
    DuplicateValue(TransportField),
    /// A stable declaration or reference used the wrong namespace.
    ItemKind {
        /// Description of the value being checked.
        field: TransportField,
        /// Allowed namespace(s).
        expected: TransportItemKind,
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
    InvalidCellContent(StateCellContentReason),
    /// A structured initializer term was invalid.
    InvalidTerm(StateTermReason),
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
        require_cell_owner_kind(&self.owner, TransportField::CellIdentityOwner)?;
        validate_rust_field(&self.field)
    }
}

impl DescriptorCellDeclarationReference {
    fn validate(&self) -> Result<(), StateTransportError> {
        if self.declaration.item_kind() != ItemKind::Cell {
            return Err(StateTransportError::ItemKind {
                field: TransportField::NestedCellDeclaration,
                expected: TransportItemKind::Cell,
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
        validate_declaration::<DescriptorStage>(self, owner, &mut ignored)
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
        validate_declaration::<DescriptorStage>(self, owner, &mut keys)?;
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
        validate_declaration::<HostStage>(self, &owner, &mut keys)
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
        validate_configuration::<DescriptorStage>(self, owner, keys)
    }
}

impl HostFixedConfiguration {
    /// Validates a complete host declaration/initializer pairing.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for owner-key mismatches,
    /// declaration/tree disagreement, malformed terms/variables, or inexact
    /// parser roles/ordinals.
    pub fn validate(&self, owner: HostTypeKey) -> Result<(), StateTransportError> {
        let mut keys = BTreeSet::new();
        validate_configuration::<HostStage>(self, &owner, &mut keys)
    }
}

type StageCellField<S> =
    ProtocolCellField<<S as Stage>::Cell, <S as Stage>::Sort, <S as Stage>::CellDeclaration>;
type StageInitializerCell<S> = ProtocolInitializerCell<
    <S as Stage>::Cell,
    <S as Stage>::CellDeclaration,
    ProtocolInitializerStateTerm<Term<S>>,
>;

trait ConfigurationValidationStage: ValidationStage {
    type CellIdentity: Ord;
    type FieldIdentity: Ord;

    /// Host owners have no stable kind; `DescriptorStage::validate_configuration_owner` must check the resolved Configuration kind.
    fn validate_configuration_owner(
        owner: &Self::InitializerOwner,
    ) -> Result<(), StateTransportError>;
    /// Host owners have no stable kind; `DescriptorStage::validate_declaration_owner` must check the resolved Configuration or Cell kind.
    fn validate_declaration_owner(
        owner: &Self::InitializerOwner,
    ) -> Result<(), StateTransportError>;
    /// Descriptor owners compare stable identities; host owners compare resolved Rust types.
    fn owners_match(left: &Self::InitializerOwner, right: &Self::InitializerOwner) -> bool;
    /// Both stages retain the occurrence key on their different cell reference representations.
    fn cell_key(reference: &Self::Cell) -> &ProvenanceKey;
    /// Host cell identities have no stable kind or field text; `DescriptorStage::validate_cell` must validate both after resolution.
    fn validate_cell(reference: &Self::Cell) -> Result<(), StateTransportError>;
    /// Descriptor cell owners compare stable identities; host cell owners compare resolved Rust types.
    fn cell_owned_by(reference: &Self::Cell, owner: &Self::InitializerOwner) -> bool;
    /// Descriptor cell identities use owner and field text; host identities use owner and marker types.
    fn cell_identity(reference: &Self::Cell) -> Self::CellIdentity;
    /// Descriptor sibling fields compare text; host sibling fields compare resolved marker types.
    fn field_identity(reference: &Self::Cell) -> Self::FieldIdentity;
    /// Host marker identities do not encode spelling; `DescriptorStage::validate_field_spelling` must check the resolved field against its Rust spelling.
    fn validate_field_spelling(
        reference: &Self::Cell,
        spelling: &str,
    ) -> Result<(), StateTransportError>;
    /// Host initializer joins compare owner and marker types; `DescriptorStage::initializer_field_matches` must also check the resolved field spelling.
    fn initializer_field_matches(
        reference: &Self::Cell,
        declaration: &StageCellField<Self>,
        owner: &Self::InitializerOwner,
    ) -> bool;
    /// Host leaf sorts have no stable kind; `DescriptorStage::validate_leaf_sort` must check the resolved kind and `KCell` content sort.
    fn validate_leaf_sort(
        wrapper: CellWrapper,
        sort: &Self::Sort,
    ) -> Result<(), StateTransportError>;
    /// Host arguments require a nonblank diagnostic path; `DescriptorStage::validate_sort_argument` must check the resolved sort kind.
    fn validate_sort_argument(sort: &Self::Sort) -> Result<(), StateTransportError>;
    /// Both stages retain the occurrence key on their different nested declaration representations.
    fn declaration_key(declaration: &Self::CellDeclaration) -> &ProvenanceKey;
    /// Host declarations require a nonblank diagnostic path; `DescriptorStage::validate_nested_declaration` must check the resolved Cell kind.
    fn validate_nested_declaration(
        declaration: &Self::CellDeclaration,
    ) -> Result<(), StateTransportError>;
    /// Host initializer targets have no stable kind; `DescriptorStage::validate_nested_initializer` must check the resolved Cell kind.
    fn validate_nested_initializer(
        declaration: &Self::CellDeclaration,
    ) -> Result<(), StateTransportError>;
    /// Descriptor nested targets compare stable identities; host nested targets compare resolved Rust types.
    fn nested_declarations_match(
        left: &Self::CellDeclaration,
        right: &Self::CellDeclaration,
    ) -> bool;
    /// Descriptor nested owners are stable identities; host nested owners are Rust type keys.
    fn nested_owner(declaration: &Self::CellDeclaration) -> Self::InitializerOwner;
}

impl ConfigurationValidationStage for DescriptorStage {
    type CellIdentity = DescriptorCellIdentity;
    type FieldIdentity = String;

    fn validate_configuration_owner(owner: &StableItemId) -> Result<(), StateTransportError> {
        if owner.item_kind() != ItemKind::Configuration {
            return Err(StateTransportError::ItemKind {
                field: TransportField::ConfigurationDescriptor,
                expected: TransportItemKind::Configuration,
                actual: owner.item_kind(),
            });
        }
        Ok(())
    }

    fn validate_declaration_owner(owner: &StableItemId) -> Result<(), StateTransportError> {
        require_cell_owner_kind(owner, TransportField::CellDeclaration)
    }

    fn owners_match(left: &StableItemId, right: &StableItemId) -> bool {
        left == right
    }

    fn cell_key(reference: &DescriptorCellReference) -> &ProvenanceKey {
        &reference.key
    }

    fn validate_cell(reference: &DescriptorCellReference) -> Result<(), StateTransportError> {
        reference.cell.validate()
    }

    fn cell_owned_by(reference: &DescriptorCellReference, owner: &StableItemId) -> bool {
        &reference.cell.owner == owner
    }

    fn cell_identity(reference: &DescriptorCellReference) -> DescriptorCellIdentity {
        reference.cell.clone()
    }

    fn field_identity(reference: &DescriptorCellReference) -> String {
        reference.cell.field.clone()
    }

    fn validate_field_spelling(
        reference: &DescriptorCellReference,
        spelling: &str,
    ) -> Result<(), StateTransportError> {
        if reference.cell.field == spelling {
            Ok(())
        } else {
            Err(StateTransportError::CellFieldMismatch)
        }
    }

    fn initializer_field_matches(
        reference: &DescriptorCellReference,
        declaration: &DescriptorCellField,
        owner: &StableItemId,
    ) -> bool {
        reference.cell.owner == *owner
            && reference.cell == declaration.reference.cell
            && reference.cell.field == declaration.rust_field
    }

    fn validate_leaf_sort(
        wrapper: CellWrapper,
        sort: &DescriptorSortReference,
    ) -> Result<(), StateTransportError> {
        sort.sort
            .validate()
            .map_err(|_| StateTransportError::ItemKind {
                field: TransportField::CellContentSort,
                expected: TransportItemKind::SortOrBuiltin,
                actual: match &sort.sort {
                    DescriptorSortRef::Declared(id) => id.item_kind(),
                    DescriptorSortRef::Builtin(_) => ItemKind::Sort,
                },
            })?;
        validate_k_cell_sort(wrapper, &sort.sort)
    }

    fn validate_sort_argument(sort: &DescriptorSortReference) -> Result<(), StateTransportError> {
        sort.sort
            .validate()
            .map_err(|_| StateTransportError::InvalidTerm(StateTermReason::InvalidCellSortArgument))
    }

    fn declaration_key(declaration: &DescriptorCellDeclarationReference) -> &ProvenanceKey {
        &declaration.key
    }

    fn validate_nested_declaration(
        declaration: &DescriptorCellDeclarationReference,
    ) -> Result<(), StateTransportError> {
        declaration.validate()
    }

    fn validate_nested_initializer(
        declaration: &DescriptorCellDeclarationReference,
    ) -> Result<(), StateTransportError> {
        declaration.validate()
    }

    fn nested_declarations_match(
        left: &DescriptorCellDeclarationReference,
        right: &DescriptorCellDeclarationReference,
    ) -> bool {
        left.declaration == right.declaration
    }

    fn nested_owner(declaration: &DescriptorCellDeclarationReference) -> StableItemId {
        declaration.declaration.clone()
    }
}

impl ConfigurationValidationStage for HostStage {
    type CellIdentity = (TypeId, TypeId);
    type FieldIdentity = TypeId;

    fn validate_configuration_owner(_: &HostTypeKey) -> Result<(), StateTransportError> {
        Ok(())
    }

    fn validate_declaration_owner(_: &HostTypeKey) -> Result<(), StateTransportError> {
        Ok(())
    }

    fn owners_match(left: &HostTypeKey, right: &HostTypeKey) -> bool {
        left.resolve() == right.resolve()
    }

    fn cell_key(reference: &HostCellReference) -> &ProvenanceKey {
        &reference.key
    }

    fn validate_cell(_: &HostCellReference) -> Result<(), StateTransportError> {
        Ok(())
    }

    fn cell_owned_by(reference: &HostCellReference, owner: &HostTypeKey) -> bool {
        reference.cell.owner.resolve() == owner.resolve()
    }

    fn cell_identity(reference: &HostCellReference) -> (TypeId, TypeId) {
        reference.cell.resolve()
    }

    fn field_identity(reference: &HostCellReference) -> TypeId {
        reference.cell.field.resolve()
    }

    fn validate_field_spelling(_: &HostCellReference, _: &str) -> Result<(), StateTransportError> {
        Ok(())
    }

    fn initializer_field_matches(
        reference: &HostCellReference,
        declaration: &HostCellField,
        owner: &HostTypeKey,
    ) -> bool {
        reference.cell.resolve() == declaration.reference.cell.resolve()
            && reference.cell.owner.resolve() == owner.resolve()
    }

    fn validate_leaf_sort(
        _: CellWrapper,
        _: &HostSortReference,
    ) -> Result<(), StateTransportError> {
        Ok(())
    }

    fn validate_sort_argument(sort: &HostSortReference) -> Result<(), StateTransportError> {
        if sort.target.authored_path.trim().is_empty() {
            Err(StateTransportError::InvalidText(
                TransportField::CellSortArgumentDiagnosticPath,
            ))
        } else {
            Ok(())
        }
    }

    fn declaration_key(declaration: &HostCellDeclarationReference) -> &ProvenanceKey {
        &declaration.key
    }

    fn validate_nested_declaration(
        declaration: &HostCellDeclarationReference,
    ) -> Result<(), StateTransportError> {
        if declaration.declaration.authored_path.trim().is_empty() {
            Err(StateTransportError::InvalidText(
                TransportField::NestedCellDiagnosticPath,
            ))
        } else {
            Ok(())
        }
    }

    fn validate_nested_initializer(
        _: &HostCellDeclarationReference,
    ) -> Result<(), StateTransportError> {
        Ok(())
    }

    fn nested_declarations_match(
        left: &HostCellDeclarationReference,
        right: &HostCellDeclarationReference,
    ) -> bool {
        left.declaration.key.resolve() == right.declaration.key.resolve()
    }

    fn nested_owner(declaration: &HostCellDeclarationReference) -> HostTypeKey {
        declaration.declaration.key
    }
}

fn validate_configuration<S: ConfigurationValidationStage>(
    configuration: &FixedConfiguration<S>,
    owner: &S::InitializerOwner,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    S::validate_configuration_owner(owner)?;
    validate_root(&configuration.root, keys)?;
    validate_declaration::<S>(&configuration.declaration, owner, keys)?;
    validate_initializer::<S>(
        &configuration.initializer,
        owner,
        &configuration.declaration,
        keys,
    )
}

fn validate_declaration<S: ConfigurationValidationStage>(
    declaration: &StageCellDeclaration<S>,
    owner: &S::InitializerOwner,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    S::validate_declaration_owner(owner)?;
    insert_exact(
        keys,
        &declaration.key,
        ProvenanceRole::ConfigurationDeclaration,
        0,
    )?;
    if declaration.fields.is_empty() {
        return Err(StateTransportError::EmptyCollection(
            TransportField::FixedCellFields,
        ));
    }
    let mut rust_fields = BTreeSet::new();
    let mut emitted_names = BTreeSet::new();
    let mut identities = BTreeSet::new();
    let mut argument_ordinal = 0_u32;
    for (index, field) in declaration.fields.iter().enumerate() {
        let ordinal = checked_index(index)?;
        S::validate_cell(&field.reference)?;
        if !S::cell_owned_by(&field.reference, owner) {
            return Err(StateTransportError::CellOwnerMismatch);
        }
        validate_rust_field(&field.rust_field)?;
        S::validate_field_spelling(&field.reference, &field.rust_field)?;
        if !rust_fields.insert(field.rust_field.clone())
            || !identities.insert(S::cell_identity(&field.reference))
        {
            return Err(StateTransportError::DuplicateValue(
                TransportField::FixedCellFields,
            ));
        }
        insert_exact(
            keys,
            S::cell_key(&field.reference),
            ProvenanceRole::ConfigurationField,
            ordinal,
        )?;
        let emitted = validate_cell_metadata(field, ordinal, keys)?;
        if !emitted_names.insert(emitted) {
            return Err(StateTransportError::DuplicateValue(
                TransportField::EmittedSiblingCellNames,
            ));
        }
        match &field.content {
            ProtocolCellContent::Leaf {
                wrapper_key,
                wrapper,
                sort,
                arguments,
            } => {
                insert_exact(
                    keys,
                    wrapper_key,
                    ProvenanceRole::ConfigurationCellWrapper,
                    ordinal,
                )?;
                insert_exact(
                    keys,
                    S::sort_key(sort),
                    ProvenanceRole::ConfigurationCellContent,
                    ordinal,
                )?;
                S::validate_leaf_sort(*wrapper, sort)?;
                for argument in arguments {
                    insert_exact(
                        keys,
                        S::sort_key(argument),
                        ProvenanceRole::ConfigurationCellContentArgument,
                        argument_ordinal,
                    )?;
                    S::validate_sort_argument(argument)?;
                    argument_ordinal = increment(argument_ordinal)?;
                }
            }
            ProtocolCellContent::Nested { declaration } => {
                insert_exact(
                    keys,
                    S::declaration_key(declaration),
                    ProvenanceRole::ConfigurationCellContent,
                    ordinal,
                )?;
                S::validate_nested_declaration(declaration)?;
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
        validate_nonblank(TransportField::EmittedCellName, &name.value)?;
        insert_exact(
            keys,
            &name.key,
            ProvenanceRole::ConfigurationCellName,
            ordinal,
        )?;
        name.value.clone()
    } else {
        field.rust_field.clone()
    };
    if let Some(color) = &field.color {
        validate_nonblank(TransportField::CellColor, &color.value)?;
        insert_exact(
            keys,
            &color.key,
            ProvenanceRole::ConfigurationCellColor,
            ordinal,
        )?;
    }
    if let Some(multiplicity) = &field.multiplicity {
        if multiplicity.value != "*" {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::UnsupportedCellMultiplicity,
            ));
        }
        insert_exact(
            keys,
            &multiplicity.key,
            ProvenanceRole::ConfigurationCellMultiplicity,
            ordinal,
        )?;
    }
    if let Some(cell_type) = &field.cell_type {
        if field.multiplicity.is_none() {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::CellTypeRequiresRepeatedMultiplicity,
            ));
        }
        insert_exact(
            keys,
            &cell_type.key,
            ProvenanceRole::ConfigurationCellType,
            ordinal,
        )?;
    }
    Ok(emitted)
}

fn validate_root(
    root: &DescriptorConfigurationRoot,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if let DescriptorConfigurationRoot::Named { key, name } = root {
        validate_nonblank(TransportField::ConfigurationRootName, name)?;
        insert_exact(keys, key, ProvenanceRole::ConfigurationRoot, 0)?;
    }
    Ok(())
}

fn validate_initializer<S: ConfigurationValidationStage>(
    initializer: &StageConfigurationInitializer<S>,
    owner: &S::InitializerOwner,
    declaration: &StageCellDeclaration<S>,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if !S::owners_match(&initializer.owner, owner) {
        return Err(StateTransportError::InitializerDeclarationMismatch);
    }
    insert_exact(
        keys,
        &initializer.key,
        ProvenanceRole::InitializerDeclaration,
        0,
    )?;
    insert_exact(
        keys,
        &initializer.owner_key,
        ProvenanceRole::InitializerResultType,
        0,
    )?;
    insert_exact(
        keys,
        &initializer.body_key,
        ProvenanceRole::InitializerBody,
        0,
    )?;
    let bindings = validate_variables::<S>(&initializer.variables, keys)?;
    let mut counters = InitializerCounters::default();
    validate_initializer_cells::<S>(
        &initializer.cells,
        &declaration.fields,
        owner,
        &bindings,
        &mut counters,
        keys,
    )
}

fn validate_variables<S: ConfigurationValidationStage>(
    variables: &[ProtocolConfigurationVariable<S::Sort>],
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<BTreeSet<String>, StateTransportError> {
    let mut bindings = BTreeSet::new();
    let mut external_names = BTreeSet::new();
    let mut main_count = 0;
    for (index, variable) in variables.iter().enumerate() {
        let ordinal = checked_index(index)?;
        validate_rust_field(&variable.binding)?;
        validate_nonblank(
            TransportField::ExternalConfigurationVariableName,
            &variable.external_name,
        )?;
        if !bindings.insert(variable.binding.clone()) {
            return Err(StateTransportError::DuplicateValue(
                TransportField::ConfigurationVariableBindings,
            ));
        }
        if !external_names.insert(variable.external_name.clone()) {
            return Err(StateTransportError::DuplicateValue(
                TransportField::ExternalConfigurationVariableNames,
            ));
        }
        insert_exact(
            keys,
            &variable.binding_key,
            ProvenanceRole::ConfigurationVariable,
            ordinal,
        )?;
        insert_exact(
            keys,
            &variable.external_name_key,
            ProvenanceRole::ConfigurationVariableName,
            ordinal,
        )?;
        insert_exact(
            keys,
            S::sort_key(&variable.sort),
            ProvenanceRole::ConfigurationVariableType,
            ordinal,
        )?;
        S::validate_sort(&variable.sort).map_err(|_| {
            StateTransportError::InvalidCellContent(StateCellContentReason::InvalidVariableSort)
        })?;
        if let Some(main_key) = &variable.main_key {
            main_count += 1;
            insert_exact(
                keys,
                main_key,
                ProvenanceRole::ConfigurationVariableMain,
                ordinal,
            )?;
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

fn validate_initializer_cells<S: ConfigurationValidationStage>(
    cells: &[StageInitializerCell<S>],
    declarations: &[StageCellField<S>],
    owner: &S::InitializerOwner,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if cells.is_empty() {
        return Err(StateTransportError::EmptyCollection(
            TransportField::InitializerCellFields,
        ));
    }
    if cells.len() != declarations.len() {
        return Err(StateTransportError::InitializerDeclarationMismatch);
    }
    for (cell, declaration) in cells.iter().zip(declarations) {
        if !S::initializer_field_matches(&cell.field, declaration, owner) {
            return Err(StateTransportError::InitializerDeclarationMismatch);
        }
        validate_initializer_cell::<S>(cell, Some(declaration), owner, bindings, counters, keys)?;
    }
    Ok(())
}

fn validate_initializer_cell<S: ConfigurationValidationStage>(
    cell: &StageInitializerCell<S>,
    declaration: Option<&StageCellField<S>>,
    owner: &S::InitializerOwner,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    S::validate_cell(&cell.field)?;
    if !S::cell_owned_by(&cell.field, owner) {
        return Err(StateTransportError::CellOwnerMismatch);
    }
    insert_exact(
        keys,
        &cell.key,
        ProvenanceRole::InitializerCell,
        counters.cell,
    )?;
    insert_exact(
        keys,
        S::cell_key(&cell.field),
        ProvenanceRole::InitializerField,
        counters.cell,
    )?;
    counters.cell = increment(counters.cell)?;
    match (&cell.content, declaration.map(|field| &field.content)) {
        (
            ProtocolInitializerCellContent::Leaf {
                constructor_key,
                wrapper,
                value,
            },
            declared,
        ) if declared.is_none()
            || matches!(declared, Some(ProtocolCellContent::Leaf { wrapper: declared_wrapper, .. }) if wrapper == declared_wrapper) =>
        {
            insert_exact(
                keys,
                constructor_key,
                ProvenanceRole::InitializerCellConstructor,
                counters.constructor,
            )?;
            counters.constructor = increment(counters.constructor)?;
            validate_wrapper_state(*wrapper, value)?;
            validate_state_term::<S>(value, bindings, counters, keys)
        }
        (
            ProtocolInitializerCellContent::Nested {
                declaration: nested,
                children,
            },
            declared,
        ) if declared.is_none()
            || matches!(declared, Some(ProtocolCellContent::Nested { declaration }) if S::nested_declarations_match(nested, declaration)) =>
        {
            if children.is_empty() {
                return Err(StateTransportError::EmptyCollection(
                    TransportField::NestedInitializerChildren,
                ));
            }
            S::validate_nested_initializer(nested)?;
            insert_exact(
                keys,
                S::declaration_key(nested),
                ProvenanceRole::InitializerNestedConstructor,
                counters.constructor,
            )?;
            counters.constructor = increment(counters.constructor)?;
            validate_nested_children::<S>(
                children,
                &S::nested_owner(nested),
                bindings,
                counters,
                keys,
            )
        }
        _ => Err(StateTransportError::InitializerDeclarationMismatch),
    }
}

fn validate_nested_children<S: ConfigurationValidationStage>(
    children: &[StageInitializerCell<S>],
    owner: &S::InitializerOwner,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    let mut fields = BTreeSet::new();
    for child in children {
        if !S::cell_owned_by(&child.field, owner) || !fields.insert(S::field_identity(&child.field))
        {
            return Err(StateTransportError::InitializerDeclarationMismatch);
        }
        validate_initializer_cell::<S>(child, None, owner, bindings, counters, keys)?;
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
            StateCellContentReason::WrapperAndInitializerStateFamilyDisagree,
        )),
    }
}

fn validate_state_term<S: ConfigurationValidationStage>(
    value: &ProtocolInitializerStateTerm<Term<S>>,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    match value {
        ProtocolInitializerStateTerm::Term(term) => {
            validate_initializer_term::<S>(term, bindings, counters, keys, None)
        }
        ProtocolInitializerStateTerm::KSequence(sequence) => {
            validate_k_sequence_shell(sequence, counters, keys)?;
            for item in &sequence.items {
                insert_exact(
                    keys,
                    &item.key,
                    ProvenanceRole::KSequenceItem,
                    counters.k_item,
                )?;
                counters.k_item = increment(counters.k_item)?;
                validate_initializer_term::<S>(
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
            validate_initializer_map::<S>(map, bindings, counters, keys)
        }
    }
}

fn validate_initializer_map<S: ConfigurationValidationStage>(
    map: &ProtocolMap<Term<S>>,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    validate_map_shell(map, counters, keys)?;
    match &map.body {
        ProtocolMapBody::Empty { .. } => Ok(()),
        ProtocolMapBody::Items { items } => {
            for item in items {
                insert_exact(
                    keys,
                    &item.key_key,
                    ProvenanceRole::MapKey,
                    counters.map_key,
                )?;
                counters.map_key = increment(counters.map_key)?;
                insert_exact(
                    keys,
                    &item.value_key,
                    ProvenanceRole::MapValue,
                    counters.map_value,
                )?;
                counters.map_value = increment(counters.map_value)?;
                validate_initializer_term::<S>(
                    &item.key,
                    bindings,
                    counters,
                    keys,
                    Some(&item.key_key),
                )?;
                validate_initializer_term::<S>(
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
            insert_exact(
                keys,
                base_key,
                ProvenanceRole::MapUpdateBase,
                counters.map_update_base,
            )?;
            counters.map_update_base = increment(counters.map_update_base)?;
            insert_exact(keys, key_key, ProvenanceRole::MapKey, counters.map_key)?;
            counters.map_key = increment(counters.map_key)?;
            insert_exact(
                keys,
                value_key,
                ProvenanceRole::MapValue,
                counters.map_value,
            )?;
            counters.map_value = increment(counters.map_value)?;
            validate_initializer_term::<S>(base, bindings, counters, keys, Some(base_key))?;
            validate_initializer_term::<S>(key, bindings, counters, keys, Some(key_key))?;
            validate_initializer_term::<S>(value, bindings, counters, keys, Some(value_key))
        }
    }
}

fn validate_k_sequence_shell<T>(
    sequence: &ProtocolKSequence<T>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if let Some(payload_key) = &sequence.payload_key {
        insert_exact(
            keys,
            payload_key,
            ProvenanceRole::KSequencePayload,
            counters.k_payload,
        )?;
        counters.k_payload = increment(counters.k_payload)?;
    }
    match sequence.notation {
        DescriptorKSequenceNotation::DotK => {
            if !sequence.items.is_empty() || sequence.payload_key.is_none() {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::InvalidStandaloneDotKPayload,
                ));
            }
            let dot_key =
                sequence
                    .dot_k_key
                    .as_ref()
                    .ok_or(StateTransportError::InvalidCellContent(
                        StateCellContentReason::DotKMissingProvenance,
                    ))?;
            insert_exact(
                keys,
                dot_key,
                ProvenanceRole::KSequenceTail,
                counters.k_tail,
            )?;
            counters.k_tail = increment(counters.k_tail)?;
        }
        DescriptorKSequenceNotation::Comma | DescriptorKSequenceNotation::Operator => {
            if sequence.dot_k_key.is_some()
                || (!sequence.items.is_empty() && sequence.payload_key.is_none())
                || (sequence.notation == DescriptorKSequenceNotation::Operator
                    && sequence.items.len() < 2)
            {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::InvalidExactKSequenceShell,
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
        insert_exact(
            keys,
            payload_key,
            ProvenanceRole::MapPayload,
            counters.map_payload,
        )?;
        counters.map_payload = increment(counters.map_payload)?;
    }
    match &map.body {
        ProtocolMapBody::Empty { explicit_dot } => {
            if *explicit_dot != map.payload_key.is_some() {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::EmptyMapPayloadProvenanceMismatch,
                ));
            }
        }
        ProtocolMapBody::Items { items } => {
            if items.is_empty() || map.payload_key.is_none() {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::EmptyMapItemPayload,
                ));
            }
        }
        ProtocolMapBody::Update { .. } if map.payload_key.is_none() => {
            return Err(StateTransportError::InvalidCellContent(
                StateCellContentReason::MapUpdateRequiresPayloadProvenance,
            ));
        }
        ProtocolMapBody::Update { .. } => {}
    }
    Ok(())
}

fn validate_initializer_term<S: ConfigurationValidationStage>(
    term: &ProtocolInitializerTerm<Term<S>>,
    bindings: &BTreeSet<String>,
    counters: &mut InitializerCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
    structural_key: Option<&ProvenanceKey>,
) -> Result<(), StateTransportError> {
    insert_exact(
        keys,
        &term.key,
        ProvenanceRole::InitializerTerm,
        counters.term,
    )?;
    counters.term = increment(counters.term)?;
    validate_term(
        &term.term,
        &mut InitializerTermValidation {
            bindings,
            counters,
            keys,
            structural_key: structural_key.unwrap_or(&term.key),
        },
    )
}

struct InitializerTermValidation<'a> {
    bindings: &'a BTreeSet<String>,
    counters: &'a mut InitializerCounters,
    keys: &'a mut BTreeSet<ProvenanceKey>,
    structural_key: &'a ProvenanceKey,
}

impl<S: ValidationStage> TermValidation<S> for InitializerTermValidation<'_> {
    type Error = StateTransportError;

    fn variable(
        &mut self,
        key: &ProvenanceKey,
        path_key: &ProvenanceKey,
        name: &str,
    ) -> Result<(), Self::Error> {
        if key != path_key || !self.bindings.contains(name) {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::VariableKeyOrBindingMismatch,
            ));
        }
        insert_exact(
            self.keys,
            key,
            ProvenanceRole::InitializerTermPath,
            self.counters.term_path,
        )?;
        self.counters.term_path = increment(self.counters.term_path)?;
        Ok(())
    }

    fn application(
        &mut self,
        head_class: DescriptorApplicationHeadClass,
        reference: &S::Application,
        path_key: &ProvenanceKey,
        arguments: &crate::Arguments<S>,
    ) -> Result<(), Self::Error> {
        if S::application_key(reference) != path_key
            || (head_class == DescriptorApplicationHeadClass::BareReference
                && !arguments.is_empty())
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::InvalidApplicationPathOrHeadClass,
            ));
        }
        S::validate_application(reference).map_err(|_| {
            StateTransportError::InvalidTerm(StateTermReason::InvalidApplicationTarget)
        })?;
        insert_exact(
            self.keys,
            S::application_key(reference),
            ProvenanceRole::InitializerTermPath,
            self.counters.term_path,
        )?;
        self.counters.term_path = increment(self.counters.term_path)?;
        Ok(())
    }

    fn literal(
        &mut self,
        key: &ProvenanceKey,
        literal: &DescriptorLiteral,
    ) -> Result<(), Self::Error> {
        if key != self.structural_key {
            return Err(StateTransportError::UnexpectedProvenance {
                expected: self.structural_key.clone(),
                actual: key.clone(),
            });
        }
        literal.validate().map_err(|_| {
            StateTransportError::InvalidTerm(StateTermReason::NonCanonicalIntegerLiteral)
        })?;
        self.keys.insert(key.clone());
        Ok(())
    }

    fn wildcard(&mut self, _: &ProvenanceKey) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::WildcardsAreNotAllowedInInitializers,
        ))
    }

    fn builtin_token(
        &mut self,
        _: &ProvenanceKey,
        _: BuiltinSort,
        _: &str,
    ) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerClaimTerm,
        ))
    }

    fn anonymous(&mut self, _: &ProvenanceKey, _: &S::Sort, _: &str) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerClaimTerm,
        ))
    }

    fn or_bool(
        &mut self,
        _: &ProvenanceKey,
        _: &crate::AtLeastTwo<Term<S>>,
    ) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerClaimTerm,
        ))
    }

    fn cell(
        &mut self,
        _: &ProvenanceKey,
        _: &S::Nominal,
        _: &[CellTermField<S>],
    ) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerFragment,
        ))
    }

    fn argument(
        &mut self,
        argument: crate::TermArgumentRef<'_, S>,
        _: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        match argument {
            crate::TermArgumentRef::Positional { .. } => Ok(()),
            crate::TermArgumentRef::Named { .. } => Err(StateTransportError::InvalidTerm(
                StateTermReason::InitializerRecordFieldProvenance,
            )),
        }
    }

    fn cell_field(
        &mut self,
        _: &CellTermField<S>,
        _: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerFragment,
        ))
    }
}

fn validate_k_cell_sort(
    wrapper: CellWrapper,
    sort: &DescriptorSortRef,
) -> Result<(), StateTransportError> {
    if wrapper == CellWrapper::KCell && sort != &DescriptorSortRef::Builtin(BuiltinSort::KSequence)
    {
        return Err(StateTransportError::InvalidCellContent(
            StateCellContentReason::KCellSortMismatch,
        ));
    }
    Ok(())
}

fn require_cell_owner_kind(
    owner: &StableItemId,
    field: TransportField,
) -> Result<(), StateTransportError> {
    if matches!(owner.item_kind(), ItemKind::Configuration | ItemKind::Cell) {
        Ok(())
    } else {
        Err(StateTransportError::ItemKind {
            field,
            expected: TransportItemKind::ConfigurationOrCell,
            actual: owner.item_kind(),
        })
    }
}

fn validate_rust_field(value: &str) -> Result<(), StateTransportError> {
    if value.trim().is_empty() || value.contains("::") || value.contains(['/', '\\']) {
        Err(StateTransportError::InvalidText(
            TransportField::RustFieldIdentity,
        ))
    } else {
        Ok(())
    }
}

fn validate_nonblank(field: TransportField, value: &str) -> Result<(), StateTransportError> {
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
    let expected_primary = canonical_key(ProvenanceRole::ConfigurationDeclaration, 0);
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
    role: ProvenanceRole,
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

fn canonical_key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal)
}

fn checked_index(index: usize) -> Result<u32, StateTransportError> {
    u32::try_from(index).map_err(|_| {
        StateTransportError::InvalidCellContent(StateCellContentReason::ProvenanceOrdinalExceedsU32)
    })
}

fn increment(value: u32) -> Result<u32, StateTransportError> {
    value
        .checked_add(1)
        .ok_or(StateTransportError::InvalidCellContent(
            StateCellContentReason::ProvenanceOrdinalExceedsU32,
        ))
}

/// Declaration fields expressed through one reference stage.
pub type StageCellDeclaration<S> = ProtocolCellDeclaration<
    ProtocolCellField<<S as Stage>::Cell, <S as Stage>::Sort, <S as Stage>::CellDeclaration>,
>;
/// Paired initializer expressed through one reference stage.
pub type StageConfigurationInitializer<S> = ProtocolConfigurationInitializer<
    <S as Stage>::InitializerOwner,
    ProtocolConfigurationVariable<<S as Stage>::Sort>,
    ProtocolInitializerCell<
        <S as Stage>::Cell,
        <S as Stage>::CellDeclaration,
        ProtocolInitializerStateTerm<crate::transport::grammar::Term<S>>,
    >,
>;

/// Maps every reference in a cell declaration through the generated protocol traversals.
/// # Errors
/// Returns the first reference-resolution error.
#[doc(hidden)]
pub fn map_declaration<S: Stage, To: Stage, M: crate::RefMap<S, To>>(
    value: StageCellDeclaration<S>,
    map: &mut M,
) -> Result<StageCellDeclaration<To>, M::Error> {
    value.try_map_refs(map, &mut |field, map| {
        field.try_map_refs(
            map,
            &mut |reference, map| map.cell(reference),
            &mut |reference, map| map.sort(reference),
            &mut |reference, map| map.cell_declaration(reference),
        )
    })
}

/// Maps every reference in a paired initializer through the generated protocol traversals.
/// # Errors
/// Returns the first reference-resolution error.
#[doc(hidden)]
pub fn map_initializer<S: Stage, To: Stage, M: crate::RefMap<S, To>>(
    value: StageConfigurationInitializer<S>,
    map: &mut M,
) -> Result<StageConfigurationInitializer<To>, M::Error> {
    value.try_map_refs(
        map,
        &mut |owner, map| map.initializer_owner(owner),
        &mut |variable, map| variable.try_map_refs(map, &mut |sort, map| map.sort(sort)),
        &mut |cell, map| {
            cell.try_map_refs(
                map,
                &mut |reference, map| map.cell(reference),
                &mut |reference, map| map.cell_declaration(reference),
                &mut |value, map| value.try_map_refs(map, &mut |term, map| term.try_map_refs(map)),
            )
        },
    )
}

#[cfg(test)]
#[path = "configuration_validation_tests.rs"]
mod validation_tests;

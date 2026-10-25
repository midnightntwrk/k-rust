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
use super::keys::{KeyFailure, TermRefusal, WireKeys};
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

/// Optional K console stream of a fixed cell (`stream = "stdin"` or `"stdout"`).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorCellStream {
    /// Exact string-literal provenance.
    pub key: ProvenanceKey,
    /// The standard stream the cell is connected to.
    pub value: crate::CellStream,
}

/// Optional bare `exit` flag of a fixed cell.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorCellExit {
    /// Exact flag-identifier provenance.
    pub key: ProvenanceKey,
}

/// Optional bare `initial` flag of an optional or collection cell (KF-023).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorCellInitial {
    /// Exact flag-identifier provenance.
    pub key: ProvenanceKey,
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
    /// One argument of a cell's collection content type: a sort, or a
    /// collection type with its own arguments (`Set<Int>` in
    /// `Map<Int, Set<Int>>`).
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(
        deny_unknown_fields,
        bound(serialize = "S: Serialize", deserialize = "S: Deserialize<'de>")
    )]
    pub struct ProtocolSortArgument<S => sort_map => S2> {
        /// The argument's sort.
        pub sort: S => [sort_map],
        /// The arguments of a collection argument, in order.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        pub arguments: Vec<ProtocolSortArgument<S>> => [vec nested sort_map],
    }
}

impl<S> ProtocolSortArgument<S> {
    /// Every argument and nested argument of `arguments`, in preorder: the
    /// order of their `configuration_cell_content_argument` ordinals.
    #[must_use]
    pub fn preorder(arguments: &[Self]) -> Vec<&Self> {
        let mut output = Vec::new();
        for argument in arguments {
            output.push(argument);
            output.extend(Self::preorder(&argument.arguments));
        }
        output
    }
}

/// Stable collection argument of a cell's content type.
pub type DescriptorSortArgument = ProtocolSortArgument<DescriptorSortReference>;

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
            /// The arguments of a collection content type (`Id` and `Value`
            /// of `Map<Id, Value>`), which semantic analysis checks every
            /// term written into or read from the cell against; empty for a
            /// bare collection.
            #[serde(default, skip_serializing_if = "Vec::is_empty")]
            arguments: Vec<ProtocolSortArgument<S>> => [vec nested sort_map],
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
        /// Optional console stream; absent for an ordinary cell.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub stream: Option<DescriptorCellStream> => [keep],
        /// Optional exit flag; absent for an ordinary cell.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub exit: Option<DescriptorCellExit> => [keep],
        /// Optional `initial` flag of an optional or collection cell (KF-023).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub initial: Option<DescriptorCellInitial> => [keep],
        /// Typed leaf or nested content.
        pub content: ProtocolCellContent<S, N> => [nested sort_map nominal_map],
    }
    map_order: [content, reference, rust_field, emitted_name, color, multiplicity, cell_type, stream, exit, initial];
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
        /// The element types of a collection-typed variable (`Value` of
        /// `xs: List<Value>`), nested ones kept; empty for a bare collection
        /// and for every other sort.
        #[serde(default = "Vec::new", skip_serializing_if = "Vec::is_empty")]
        pub arguments: Vec<ProtocolSortArgument<S>> => [vec nested sort_map],
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
        /// Complete payload provenance, at the invocation of an empty
        /// `k![]`.
        pub payload_key: ProvenanceKey => [keep],
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
        /// Complete payload provenance, at the invocation of an empty
        /// `map![]`.
        pub payload_key: ProvenanceKey => [keep],
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
    InitializerDeclarationMismatch {
        /// The initializer node that disagrees: a cell whose field is not the declaration's or
        /// repeats one written before it, the struct literal when it leaves a declared field
        /// out, or the initializer of another owner.
        at: ProvenanceKey,
    },
    /// More than one configuration variable was marked main.
    MultipleMainVariables,
    /// A `KCell` or state family disagreed with its declaration.
    InvalidCellContent(StateCellContentReason),
    /// A structured initializer term was invalid.
    InvalidTerm(StateTermReason),
    /// A nested semantic key was absent from materialized provenance.
    MissingProvenance(ProvenanceKey),
    /// A node's key field held a key of another role than the field
    /// requires.
    UnexpectedProvenance {
        /// The field's role.
        expected: ProvenanceRole,
        /// Supplied key.
        actual: ProvenanceKey,
    },
    /// A field that names one particular node held another key of its role:
    /// a descriptor's primary key, or the key an initializer literal shares
    /// with the node it stands in.
    MismatchedProvenance {
        /// The key the field must hold.
        expected: ProvenanceKey,
        /// Supplied key.
        actual: ProvenanceKey,
    },
    /// Two nodes defined one key: a key names one authored node, and every
    /// other field that names it is a reference.
    DuplicateProvenance(ProvenanceKey),
    /// Materialized provenance contained a key absent from the typed payload.
    ExtraProvenance(ProvenanceKey),
}

impl StateTransportError {
    /// The node the failure is about, when it names one that the provenance can locate.
    #[must_use]
    pub const fn at(&self) -> Option<&ProvenanceKey> {
        match self {
            Self::InitializerDeclarationMismatch { at: key }
            | Self::UnexpectedProvenance { actual: key, .. }
            | Self::MismatchedProvenance { actual: key, .. }
            | Self::DuplicateProvenance(key)
            | Self::ExtraProvenance(key) => Some(key),
            Self::InvalidText(_)
            | Self::EmptyCollection(_)
            | Self::DuplicateValue(_)
            | Self::ItemKind { .. }
            | Self::CellOwnerMismatch
            | Self::CellFieldMismatch
            | Self::MultipleMainVariables
            | Self::InvalidCellContent(_)
            | Self::InvalidTerm(_)
            // A key absent from the provenance locates nothing.
            | Self::MissingProvenance(_) => None,
        }
    }
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
            Self::InitializerDeclarationMismatch { .. } => {
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
        }
    }
}

impl Error for StateTransportError {}

impl From<KeyFailure> for StateTransportError {
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

impl From<TermRefusal> for StateTransportError {
    fn from(refusal: TermRefusal) -> Self {
        Self::InvalidTerm(match refusal {
            TermRefusal::Wildcard => StateTermReason::WildcardsAreAllowedOnlyInRuleSubjects,
            TermRefusal::BuiltinToken => StateTermReason::InvalidCompilerOwnedBuiltinToken,
            TermRefusal::PatternAs => StateTermReason::PatternAsOutsideLeftHandSide,
            TermRefusal::PatternOr => StateTermReason::PatternOrOutsideLeftHandSide,
            TermRefusal::Matches => StateTermReason::MatchesInPattern,
            TermRefusal::Let => StateTermReason::LetInPattern,
            TermRefusal::Closure => StateTermReason::ClosureInPattern,
            TermRefusal::RecordUpdateBase => StateTermReason::RecordUpdateBase,
        })
    }
}

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
    /// typed references, metadata, or keys of other roles than their nodes'.
    pub fn validate(&self, owner: &StableItemId) -> Result<(), StateTransportError> {
        self.wire_keys(owner).map(|_| ())
    }

    /// Returns the keys of this declaration's nodes, which are exactly the
    /// anchors of a well-formed declaration.
    ///
    /// # Errors
    ///
    /// Returns the same shape/key errors as [`Self::validate`].
    pub fn expected_provenance_keys(
        &self,
        owner: &StableItemId,
    ) -> Result<BTreeSet<ProvenanceKey>, StateTransportError> {
        Ok(self.wire_keys(owner)?.into_defined())
    }

    fn wire_keys(&self, owner: &StableItemId) -> Result<WireKeys, StateTransportError> {
        let mut keys = WireKeys::default();
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
        validate_complete_set(primary, actual, self.wire_keys(owner)?)
    }
}

impl ProtocolCellDeclaration<HostCellField> {
    /// Validates host owner/field-marker joins and exact declaration keys.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for mismatched identities, duplicate
    /// fields/names, malformed metadata, or keys of other roles than their
    /// nodes'.
    pub fn validate_host(&self, owner: HostTypeKey) -> Result<(), StateTransportError> {
        validate_declaration::<HostStage>(self, &owner, &mut WireKeys::default())
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
        self.wire_keys(owner).map(|_| ())
    }

    /// Returns every key of this payload's nodes, which are exactly the
    /// anchors of a well-formed configuration.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::validate`].
    pub fn expected_provenance_keys(
        &self,
        owner: &StableItemId,
    ) -> Result<BTreeSet<ProvenanceKey>, StateTransportError> {
        Ok(self.wire_keys(owner)?.into_defined())
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
        validate_complete_set(primary, actual, self.wire_keys(owner)?)
    }

    fn wire_keys(&self, owner: &StableItemId) -> Result<WireKeys, StateTransportError> {
        let mut keys = WireKeys::default();
        validate_configuration::<DescriptorStage>(self, owner, &mut keys)?;
        Ok(keys)
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
        validate_configuration::<HostStage>(self, &owner, &mut WireKeys::default())
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
        let invalid = |actual| StateTransportError::ItemKind {
            field: TransportField::CellContentSort,
            expected: TransportItemKind::SortOrBuiltin,
            actual,
        };
        match &sort.sort {
            DescriptorSortRef::Cell(id) => return Err(invalid(id.item_kind())),
            DescriptorSortRef::Parameter(_) => return Err(invalid(ItemKind::Sort)),
            DescriptorSortRef::Declared(id) => {
                sort.sort.validate().map_err(|_| invalid(id.item_kind()))?;
            }
            DescriptorSortRef::Builtin(_) => {
                sort.sort.validate().map_err(|_| invalid(ItemKind::Sort))?;
            }
        }
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
    keys: &mut WireKeys,
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
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    S::validate_declaration_owner(owner)?;
    keys.define(&declaration.key, ProvenanceRole::ConfigurationDeclaration)?;
    if declaration.fields.is_empty() {
        return Err(StateTransportError::EmptyCollection(
            TransportField::FixedCellFields,
        ));
    }
    let mut rust_fields = BTreeSet::new();
    let mut emitted_names = BTreeSet::new();
    let mut identities = BTreeSet::new();
    for field in &declaration.fields {
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
        keys.define(
            S::cell_key(&field.reference),
            ProvenanceRole::ConfigurationField,
        )?;
        let emitted = validate_cell_metadata(field, keys)?;
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
                keys.define(wrapper_key, ProvenanceRole::ConfigurationCellWrapper)?;
                keys.define(S::sort_key(sort), ProvenanceRole::ConfigurationCellContent)?;
                S::validate_leaf_sort(*wrapper, sort)?;
                for argument in ProtocolSortArgument::preorder(arguments) {
                    let argument = &argument.sort;
                    keys.define(
                        S::sort_key(argument),
                        ProvenanceRole::ConfigurationCellContentArgument,
                    )?;
                    S::validate_sort_argument(argument)?;
                }
            }
            ProtocolCellContent::Nested { declaration } => {
                keys.define(
                    S::declaration_key(declaration),
                    ProvenanceRole::ConfigurationCellContent,
                )?;
                S::validate_nested_declaration(declaration)?;
            }
        }
    }
    Ok(())
}

fn validate_cell_metadata<I, S, N>(
    field: &ProtocolCellField<I, S, N>,
    keys: &mut WireKeys,
) -> Result<String, StateTransportError> {
    let emitted = if let Some(name) = &field.emitted_name {
        validate_nonblank(TransportField::EmittedCellName, &name.value)?;
        keys.define(&name.key, ProvenanceRole::ConfigurationCellName)?;
        name.value.clone()
    } else {
        field.rust_field.clone()
    };
    if let Some(color) = &field.color {
        validate_nonblank(TransportField::CellColor, &color.value)?;
        keys.define(&color.key, ProvenanceRole::ConfigurationCellColor)?;
    }
    if let Some(multiplicity) = &field.multiplicity {
        if crate::CellMultiplicity::from_k(&multiplicity.value).is_none() {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::UnsupportedCellMultiplicity,
            ));
        }
        keys.define(
            &multiplicity.key,
            ProvenanceRole::ConfigurationCellMultiplicity,
        )?;
    }
    let star = field
        .multiplicity
        .as_ref()
        .is_some_and(|multiplicity| multiplicity.value == "*");
    if star && field.cell_type.is_none() {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::CellTypeRequiresRepeatedMultiplicity,
        ));
    }
    if let Some(cell_type) = &field.cell_type {
        if !star {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::CellTypeRequiresRepeatedMultiplicity,
            ));
        }
        keys.define(&cell_type.key, ProvenanceRole::ConfigurationCellType)?;
    }
    if let Some(stream) = &field.stream {
        keys.define(&stream.key, ProvenanceRole::ConfigurationCellStream)?;
    }
    if let Some(exit) = &field.exit {
        keys.define(&exit.key, ProvenanceRole::ConfigurationCellExit)?;
    }
    if let Some(initial) = &field.initial {
        if field.multiplicity.is_none() {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::InitialRequiresMultiplicity,
            ));
        }
        keys.define(&initial.key, ProvenanceRole::ConfigurationCellInitial)?;
    }
    Ok(emitted)
}

fn validate_root(
    root: &DescriptorConfigurationRoot,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    if let DescriptorConfigurationRoot::Named { key, name } = root {
        validate_nonblank(TransportField::ConfigurationRootName, name)?;
        keys.define(key, ProvenanceRole::ConfigurationRoot)?;
    }
    Ok(())
}

fn validate_initializer<S: ConfigurationValidationStage>(
    initializer: &StageConfigurationInitializer<S>,
    owner: &S::InitializerOwner,
    declaration: &StageCellDeclaration<S>,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    if !S::owners_match(&initializer.owner, owner) {
        return Err(StateTransportError::InitializerDeclarationMismatch {
            at: initializer.owner_key.clone(),
        });
    }
    keys.define(&initializer.key, ProvenanceRole::InitializerDeclaration)?;
    keys.define(
        &initializer.owner_key,
        ProvenanceRole::InitializerResultType,
    )?;
    keys.define(&initializer.body_key, ProvenanceRole::InitializerBody)?;
    let bindings = validate_variables::<S>(&initializer.variables, keys)?;
    validate_initializer_cells::<S>(
        &initializer.cells,
        &declaration.fields,
        owner,
        &initializer.body_key,
        &bindings,
        keys,
    )
}

fn validate_variables<S: ConfigurationValidationStage>(
    variables: &[ProtocolConfigurationVariable<S::Sort>],
    keys: &mut WireKeys,
) -> Result<BTreeSet<String>, StateTransportError> {
    let mut bindings = BTreeSet::new();
    let mut external_names = BTreeSet::new();
    let mut main_count = 0;
    for variable in variables {
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
        keys.define(&variable.binding_key, ProvenanceRole::ConfigurationVariable)?;
        keys.define(
            &variable.external_name_key,
            ProvenanceRole::ConfigurationVariableName,
        )?;
        keys.define(
            S::sort_key(&variable.sort),
            ProvenanceRole::ConfigurationVariableType,
        )?;
        S::validate_sort(&variable.sort).map_err(|_| {
            StateTransportError::InvalidCellContent(StateCellContentReason::InvalidVariableSort)
        })?;
        for argument in ProtocolSortArgument::preorder(&variable.arguments) {
            let argument = &argument.sort;
            keys.define(
                S::sort_key(argument),
                ProvenanceRole::ConfigurationVariableTypeArgument,
            )?;
            S::validate_sort_argument(argument)?;
        }
        if let Some(main_key) = &variable.main_key {
            main_count += 1;
            keys.define(main_key, ProvenanceRole::ConfigurationVariableMain)?;
        }
    }
    if main_count > 1 {
        return Err(StateTransportError::MultipleMainVariables);
    }
    Ok(bindings)
}

fn validate_initializer_cells<S: ConfigurationValidationStage>(
    cells: &[StageInitializerCell<S>],
    declarations: &[StageCellField<S>],
    owner: &S::InitializerOwner,
    body_key: &ProvenanceKey,
    bindings: &BTreeSet<String>,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    if cells.is_empty() {
        return Err(StateTransportError::EmptyCollection(
            TransportField::InitializerCellFields,
        ));
    }
    // The body is a struct literal, whose field order has no meaning: each cell is matched to
    // its declared field by identity, and every declared field is written exactly once.
    let mut written = vec![false; declarations.len()];
    for cell in cells {
        let Some(index) = declarations
            .iter()
            .position(|declaration| S::initializer_field_matches(&cell.field, declaration, owner))
        else {
            return Err(StateTransportError::InitializerDeclarationMismatch {
                at: cell.key.clone(),
            });
        };
        if std::mem::replace(&mut written[index], true) {
            return Err(StateTransportError::InitializerDeclarationMismatch {
                at: cell.key.clone(),
            });
        }
        validate_initializer_cell::<S>(cell, Some(&declarations[index]), owner, bindings, keys)?;
    }
    if written.contains(&false) {
        return Err(StateTransportError::InitializerDeclarationMismatch {
            at: body_key.clone(),
        });
    }
    Ok(())
}

fn validate_initializer_cell<S: ConfigurationValidationStage>(
    cell: &StageInitializerCell<S>,
    declaration: Option<&StageCellField<S>>,
    owner: &S::InitializerOwner,
    bindings: &BTreeSet<String>,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    S::validate_cell(&cell.field)?;
    if !S::cell_owned_by(&cell.field, owner) {
        return Err(StateTransportError::CellOwnerMismatch);
    }
    keys.define(&cell.key, ProvenanceRole::InitializerCell)?;
    keys.define(S::cell_key(&cell.field), ProvenanceRole::InitializerField)?;
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
            keys.define(constructor_key, ProvenanceRole::InitializerCellConstructor)?;
            validate_wrapper_state(*wrapper, value)?;
            validate_state_term::<S>(value, bindings, keys)
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
            keys.define(
                S::declaration_key(nested),
                ProvenanceRole::InitializerNestedConstructor,
            )?;
            validate_nested_children::<S>(children, &S::nested_owner(nested), bindings, keys)
        }
        _ => Err(StateTransportError::InitializerDeclarationMismatch {
            at: cell.key.clone(),
        }),
    }
}

fn validate_nested_children<S: ConfigurationValidationStage>(
    children: &[StageInitializerCell<S>],
    owner: &S::InitializerOwner,
    bindings: &BTreeSet<String>,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    let mut fields = BTreeSet::new();
    for child in children {
        if !S::cell_owned_by(&child.field, owner) || !fields.insert(S::field_identity(&child.field))
        {
            return Err(StateTransportError::InitializerDeclarationMismatch {
                at: child.key.clone(),
            });
        }
        validate_initializer_cell::<S>(child, None, owner, bindings, keys)?;
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
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    match value {
        ProtocolInitializerStateTerm::Term(term) => {
            validate_initializer_term::<S>(term, bindings, keys)
        }
        ProtocolInitializerStateTerm::KSequence(sequence) => {
            validate_k_sequence_shell(sequence, keys)?;
            for item in &sequence.items {
                keys.define(&item.key, ProvenanceRole::KSequenceItem)?;
                validate_initializer_term::<S>(&item.value, bindings, keys)?;
            }
            Ok(())
        }
        ProtocolInitializerStateTerm::Map(map) => {
            validate_initializer_map::<S>(map, bindings, keys)
        }
    }
}

fn validate_initializer_map<S: ConfigurationValidationStage>(
    map: &ProtocolMap<Term<S>>,
    bindings: &BTreeSet<String>,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    validate_map_shell(map, keys)?;
    match &map.body {
        ProtocolMapBody::Empty { .. } => Ok(()),
        ProtocolMapBody::Items { items } => {
            for item in items {
                keys.define(&item.key_key, ProvenanceRole::MapKey)?;
                keys.define(&item.value_key, ProvenanceRole::MapValue)?;
                validate_initializer_term::<S>(&item.key, bindings, keys)?;
                validate_initializer_term::<S>(&item.value, bindings, keys)?;
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
            keys.define(base_key, ProvenanceRole::MapUpdateBase)?;
            keys.define(key_key, ProvenanceRole::MapKey)?;
            keys.define(value_key, ProvenanceRole::MapValue)?;
            validate_initializer_term::<S>(base, bindings, keys)?;
            validate_initializer_term::<S>(key, bindings, keys)?;
            validate_initializer_term::<S>(value, bindings, keys)
        }
    }
}

fn validate_k_sequence_shell<T>(
    sequence: &ProtocolKSequence<T>,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    keys.define(&sequence.payload_key, ProvenanceRole::KSequencePayload)?;
    match sequence.notation {
        DescriptorKSequenceNotation::DotK => {
            if !sequence.items.is_empty() {
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
            keys.define(dot_key, ProvenanceRole::KSequenceTail)?;
        }
        DescriptorKSequenceNotation::Comma | DescriptorKSequenceNotation::Operator => {
            if sequence.dot_k_key.is_some()
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
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    keys.define(&map.payload_key, ProvenanceRole::MapPayload)?;
    if let ProtocolMapBody::Items { items } = &map.body
        && items.is_empty()
    {
        return Err(StateTransportError::InvalidCellContent(
            StateCellContentReason::EmptyMapItemPayload,
        ));
    }
    Ok(())
}

fn validate_initializer_term<S: ConfigurationValidationStage>(
    term: &ProtocolInitializerTerm<Term<S>>,
    bindings: &BTreeSet<String>,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    keys.define(&term.key, ProvenanceRole::InitializerTerm)?;
    validate_term(
        &term.term,
        &mut InitializerTermValidation { bindings, keys },
    )
}

struct InitializerTermValidation<'a> {
    bindings: &'a BTreeSet<String>,
    keys: &'a mut WireKeys,
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
        self.keys.define(key, ProvenanceRole::InitializerTermPath)?;
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
        self.keys.define(
            S::application_key(reference),
            ProvenanceRole::InitializerTermPath,
        )?;
        Ok(())
    }

    fn literal(
        &mut self,
        key: &ProvenanceKey,
        literal: &DescriptorLiteral,
    ) -> Result<(), Self::Error> {
        literal.validate().map_err(|_| {
            StateTransportError::InvalidTerm(StateTermReason::NonCanonicalIntegerLiteral)
        })?;
        self.keys
            .define(key, ProvenanceRole::InitializerTermLiteral)?;
        Ok(())
    }

    fn wildcard(&mut self, _: &ProvenanceKey) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::WildcardsAreNotAllowedInInitializers,
        ))
    }

    /// A builtin literal is one constant of its sort, an initializer term as any constant is.
    fn builtin_token(
        &mut self,
        key: &ProvenanceKey,
        sort: BuiltinSort,
        value: &str,
    ) -> Result<(), Self::Error> {
        let role = super::validation::builtin_token_literal_role(sort, value).ok_or(
            StateTransportError::InvalidTerm(StateTermReason::InvalidCompilerOwnedBuiltinToken),
        )?;
        self.keys.define(key, role)?;
        Ok(())
    }

    /// An unknown value has no place in the initial configuration a run starts from.
    fn anonymous(
        &mut self,
        _: &ProvenanceKey,
        _: &S::Sort,
        _: &ProvenanceKey,
        _: &str,
    ) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerClaimTerm,
        ))
    }

    /// A lexeme is one constant of its token sort.
    fn lexeme(
        &mut self,
        key: &ProvenanceKey,
        sort: &S::Sort,
        text: &str,
    ) -> Result<(), Self::Error> {
        if text.is_empty() {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::EmptyLexemeText,
            ));
        }
        S::validate_sort(sort)
            .map_err(|_| StateTransportError::InvalidTerm(StateTermReason::InvalidLexemeSort))?;
        self.keys
            .define(S::sort_key(sort), ProvenanceRole::LexemeSort)?;
        self.keys.define(key, ProvenanceRole::LexemeText)?;
        Ok(())
    }

    fn sort_test(
        &mut self,
        _: &ProvenanceKey,
        _: crate::SortTestKind,
        _: &S::Sort,
    ) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerSortTest,
        ))
    }

    fn application_instance(&mut self, _: &S::Sort) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerApplicationInstance,
        ))
    }

    fn pattern_as(
        &mut self,
        _: &ProvenanceKey,
        _: &ProvenanceKey,
        _: &str,
    ) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerPatternAs,
        ))
    }

    fn pattern_or(&mut self, _: &ProvenanceKey) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerPatternOr,
        ))
    }

    fn matches(&mut self, _: &ProvenanceKey) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerMatches,
        ))
    }

    fn matches_pattern(&mut self, _: bool) {}

    fn let_binding(&mut self, _: &ProvenanceKey, _: Option<&S::Sort>) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerLet,
        ))
    }

    fn let_pattern(&mut self, _: bool) {}

    fn closure(
        &mut self,
        _: &ProvenanceKey,
        _: &ProvenanceKey,
        _: &S::Sort,
    ) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerClosure,
        ))
    }

    fn let_body(&mut self, _: Option<&BTreeSet<String>>) {}

    fn rewrite(
        &mut self,
        _: &ProvenanceKey,
        _: &ProvenanceKey,
        _: &ProvenanceKey,
        _: bool,
    ) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::RewriteOutsideSingleBodyRule,
        ))
    }

    fn rewrite_right(&mut self, _: bool) {}

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
        _: &ProvenanceKey,
        _: &S::Nominal,
        _: &[CellTermField<S>],
        _: bool,
    ) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerFragment,
        ))
    }

    /// A record argument names its field; each name has its own provenance.
    fn argument(
        &mut self,
        argument: crate::TermArgumentRef<'_, S>,
        fields: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        match argument {
            crate::TermArgumentRef::Positional { .. } => Ok(()),
            crate::TermArgumentRef::Named { key, field, .. } => {
                if !fields.insert(field.clone()) {
                    return Err(StateTransportError::DuplicateValue(
                        TransportField::RuleApplicationRecordFields,
                    ));
                }
                self.keys
                    .define(key, ProvenanceRole::InitializerRecordFieldName)?;
                Ok(())
            }
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

    fn record_update(&mut self, _: &Term<S>) -> Result<(), Self::Error> {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InitializerRecordUpdate,
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

/// Closes a configuration's or a cell declaration's keys over its anchors;
/// its primary key is the declaration's.
fn validate_complete_set(
    primary: &ProvenanceKey,
    actual: &BTreeSet<ProvenanceKey>,
    keys: WireKeys,
) -> Result<(), StateTransportError> {
    let expected_primary = ProvenanceKey::new(ProvenanceRole::ConfigurationDeclaration, 0);
    if primary != &expected_primary {
        return Err(StateTransportError::MismatchedProvenance {
            expected: expected_primary,
            actual: primary.clone(),
        });
    }
    keys.close(actual)?;
    Ok(())
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

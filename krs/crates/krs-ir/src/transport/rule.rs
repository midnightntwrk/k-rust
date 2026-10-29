//! Collector transport for whole-configuration rules, claims, and context aliases.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use super::detail::{StateCellContentReason, StateTermReason, TransportField, TransportItemKind};
use super::keys::{KeyFailure, WireKeys};
use crate::stage::{DescriptorStage, HostStage, protocol_shape, stage_shape};

use super::validation::{TermValidation, ValidationStage, validate_term};
use crate::host::HostTypeReference;
use crate::transport::configuration::{
    CellWrapper, DescriptorCellReference, DescriptorKSequenceNotation, HostCellReference,
    StateTransportError,
};
use crate::transport::grammar::{
    CellTermField, DescriptorApplicationHeadClass, DescriptorRuleLabel, DescriptorSortRef,
    DescriptorSortReference, DescriptorTerm, HostSortReference, HostTerm, Term,
    valid_rule_label_name,
};
use crate::{
    ItemKind, ProductionFieldId, ProvenanceKey, ProvenanceRole, RuleRole, RuleSide, StableItemId,
};

/// Explicit reachability modality authored on a claim.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ClaimModality {
    /// K's default all-path claim.
    AllPaths,
    /// Explicit one-path reachability.
    OnePath,
}

stage_shape! {
    /// One typed claim binder with explicit scope kind retained by its containing list.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    #[serde(
        rename = "ClaimBinder",
        bound(
            serialize = "S::Sort: Serialize",
            deserialize = "S::Sort: Deserialize<'de>"
        )
    )]
    pub struct ClaimBinder<S: Stage> {
        /// Binder declaration provenance.
        pub declaration_key: ProvenanceKey => [keep],
        /// Binder-name provenance.
        pub name_key: ProvenanceKey => [keep],
        /// Authored Rust name.
        pub name: String => [keep],
        /// Exact sort reference and sort provenance.
        pub sort: S::Sort => [sort],
    }
}

/// Stable descriptor-stage form of [`ClaimBinder`].
pub type DescriptorClaimBinder = ClaimBinder<DescriptorStage>;

/// Build-local host-stage form of [`ClaimBinder`].
pub type HostClaimBinder = ClaimBinder<HostStage>;

/// Whether a transition is a heating or a cooling step (KF-014), or the
/// sentence is an evaluation context that K turns into both (KF-021).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EvaluationKind {
    /// `#[k::rule(heat, hole = x)]`, K's `[heat]`: moves the hole to the front of `k`.
    Heat,
    /// `#[k::rule(cool, hole = x)]`, K's `[cool]`: plugs a finished hole back.
    Cool,
    /// `#[k::context(hole = x)]`, K's `context`: where evaluation may happen.
    Context,
}

impl EvaluationKind {
    /// The provenance role of the `heat` or `cool` marker, or of a context's
    /// fn name.
    #[must_use]
    pub const fn role(self) -> ProvenanceRole {
        match self {
            Self::Heat => ProvenanceRole::RuleHeat,
            Self::Cool => ProvenanceRole::RuleCool,
            Self::Context => ProvenanceRole::ContextDeclaration,
        }
    }

    /// The provenance role of the binder named by `hole = x`.
    #[must_use]
    pub const fn hole_role(self) -> ProvenanceRole {
        match self {
            Self::Heat | Self::Cool => ProvenanceRole::RuleHole,
            Self::Context => ProvenanceRole::ContextHole,
        }
    }

    /// The provenance role of the sort path of `result = S`.
    #[must_use]
    pub const fn result_role(self) -> ProvenanceRole {
        match self {
            Self::Heat | Self::Cool => ProvenanceRole::RuleResultSort,
            Self::Context => ProvenanceRole::ContextResult,
        }
    }

    /// K's attribute spelling, `heat` or `cool`; a context is a sentence
    /// keyword, `context`.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Heat => "heat",
            Self::Cool => "cool",
            Self::Context => "context",
        }
    }
}

stage_shape! {
    /// The `heat` or `cool` key of a transition with its hole binder and
    /// optional result sort (KF-014).
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    #[serde(
        rename = "EvaluationStep",
        bound(
            serialize = "S::Sort: Serialize",
            deserialize = "S::Sort: Deserialize<'de>"
        )
    )]
    pub struct EvaluationStep<S: Stage> {
        /// Heating or cooling.
        pub kind: EvaluationKind => [keep],
        /// Provenance of the `heat` or `cool` marker.
        pub key: ProvenanceKey => [keep],
        /// Provenance of the binder named by `hole = x`.
        pub hole_key: ProvenanceKey => [keep],
        /// The authored hole binder name.
        pub hole: String => [keep],
        /// Optional `result = S`, K's `result(S)`; K's default is `KResult`.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub result: Option<S::Sort> => [option sort],
    }
}

/// Stable descriptor-stage form of [`EvaluationStep`].
pub type DescriptorEvaluationStep = EvaluationStep<DescriptorStage>;

/// Build-local host-stage form of [`EvaluationStep`].
pub type HostEvaluationStep = EvaluationStep<HostStage>;

impl<S: crate::Stage> EvaluationStep<S> {
    /// Checks the marker, hole, and result-sort roles; `result_key` reads
    /// the result sort's provenance key.
    pub(crate) fn has_valid_roles(&self, result_key: impl Fn(&S::Sort) -> &ProvenanceKey) -> bool {
        self.key.role() == self.kind.role()
            && self.key.ordinal() == 0
            && self.hole_key.role() == self.kind.hole_role()
            && self.hole_key.ordinal() == 0
            && !self.hole.is_empty()
            && self.result.as_ref().is_none_or(|sort| {
                let key = result_key(sort);
                key.role() == self.kind.result_role() && key.ordinal() == 0
            })
    }
}

stage_shape! {
    /// Claim-only metadata attached to one configuration rewrite.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    #[serde(
        rename = "DescriptorClaim",
        bound(
            serialize = "S::Sort: Serialize, S::Application: Serialize, S::Nominal: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Application: Deserialize<'de>, S::Nominal: Deserialize<'de>"
        )
    )]
    pub struct Claim<S: Stage> {
        /// Claim declaration provenance.
        pub declaration_key: ProvenanceKey => [keep],
        /// Exact modality provenance.
        pub modality_key: ProvenanceKey => [keep],
        /// Exactly one reachability modality.
        pub modality: ClaimModality => [keep],
        /// Optional circularity marker provenance.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub circularity_key: Option<ProvenanceKey> => [keep],
        /// Optional trusted marker provenance: the claim is assumed without proof.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub trusted_key: Option<ProvenanceKey> => [keep],
        /// Universally scoped ordinary term binders.
        pub universals: Vec<ClaimBinder<S>> => [vec nested],
        /// Existentials scoped to RHS and ensures.
        pub existentials: Vec<ClaimBinder<S>> => [vec nested],
        /// Optional object-Bool postcondition.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub ensures: Option<crate::transport::grammar::RuleCondition<S>> => [option nested],
        /// Complete `or_bool!` shell provenance occurrences.
        pub or_bool_keys: Vec<ProvenanceKey> => [keep],
    }
}

/// Stable descriptor-stage form of [`Claim`].
pub type DescriptorClaim = Claim<DescriptorStage>;

/// Build-local host-stage form of [`Claim`].
pub type HostClaim = Claim<HostStage>;

/// Stable configuration type reference in a whole-configuration rule.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorConfigurationReference {
    /// Exact subject/result Rust type-path provenance.
    pub key: ProvenanceKey,
    /// Stable configuration declaration identity.
    pub configuration: StableItemId,
}

/// Host counterpart of [`DescriptorConfigurationReference`].
#[derive(Clone, Debug)]
pub struct HostConfigurationReference {
    /// Exact subject/result Rust type-path provenance.
    pub key: ProvenanceKey,
    /// Rust-resolved configuration type.
    pub configuration: HostTypeReference,
}

protocol_shape! {
    /// Semantic family and, for ordinary terms, exact sort of one rule binding.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(tag = "binding_kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum ProtocolRuleBindingKind<S => sort_map => S2> {
        /// Ordinary term binding with an explicitly authored sort.
        Term {
            /// Exact authored sort reference.
            sort: S => [sort_map],
        },
        /// Named remainder of a K sequence.
        KSequenceFrame,
        /// Named remainder of a map.
        MapFrame,
        /// Named remainder of the complete fixed configuration.
        ConfigurationFrame,
        /// Named rest of a collection cell's instances (KF-023).
        InstancesFrame,
    }
}

protocol_shape! {
    /// One typed/kinded rule binding in subject first-occurrence preorder.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolRuleBinding<S => sort_map => S2> {
        /// Rust binding name used by subject and result terms or frames.
        pub name: String => [keep],
        /// Exact structural family and optional term sort.
        pub kind: ProtocolRuleBindingKind<S> => [nested sort_map],
    }
}

/// Stable typed configuration-rule binding.
pub type DescriptorRuleBinding = ProtocolRuleBinding<DescriptorSortReference>;

/// Host typed configuration-rule binding.
pub type HostRuleBinding = ProtocolRuleBinding<HostSortReference>;

/// Exact, anonymous, bound-pattern, or reused-expression associative frame.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "frame_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ProtocolRuleFrame {
    /// No content is omitted.
    Exact,
    /// Anonymous subject remainder (`..`).
    Anonymous {
        /// Exact remainder provenance.
        key: ProvenanceKey,
    },
    /// Subject remainder binding (`name @ ..`).
    Bind {
        /// Exact remainder provenance.
        key: ProvenanceKey,
        /// Introduced binding.
        binding: String,
    },
    /// Result remainder reuse (`..name`).
    Reuse {
        /// Exact remainder provenance.
        key: ProvenanceKey,
        /// Previously introduced subject binding.
        binding: String,
    },
}

protocol_shape! {
    /// One ordered K-sequence item in a configuration rule.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolRuleKSequenceItem<T => term_map => T2> {
        /// Exact structural item provenance.
        pub key: ProvenanceKey => [keep],
        /// Structured item term.
        pub value: T => [term_map],
    }
}

protocol_shape! {
    /// Structured K sequence with an exact or framed tail.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolRuleKSequence<T => term_map => T2> {
        /// Complete payload provenance. An empty sequence's is at its own
        /// delimiters: an empty `k![]`'s invocation, `KCell()`'s
        /// parentheses, or a readable instance child's `[]`.
        pub payload_key: ProvenanceKey => [keep],
        /// Exact standalone `.K` provenance.
        pub dot_k_key: Option<ProvenanceKey> => [keep],
        /// Preserved parser notation.
        pub notation: DescriptorKSequenceNotation => [keep],
        /// Ordered sequence prefix.
        pub items: Vec<ProtocolRuleKSequenceItem<T>> => [vec nested term_map],
        /// Exact or associative tail.
        pub tail: ProtocolRuleFrame => [keep],
    }
}

protocol_shape! {
    /// One ordered map item in a configuration rule.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolRuleMapItem<T => term_map => T2> {
        /// Exact key-expression provenance.
        pub key_key: ProvenanceKey => [keep],
        /// Structured map key.
        pub key: T => [term_map],
        /// Exact value-expression provenance.
        pub value_key: ProvenanceKey => [keep],
        /// Structured map value.
        pub value: T => [term_map],
    }
}

protocol_shape! {
    /// Empty, associative-item, or functional-update map rule term.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(tag = "map_kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum ProtocolRuleMapBody<T => term_map => T2> {
        /// `.Map` or empty `map![]`.
        Empty {
            /// Whether `.Map` was explicitly authored.
            explicit_dot: bool => [keep],
        },
        /// Ordered items and exact/framed remainder.
        Items {
            /// Ordered key/value items; may be empty when the frame is non-exact.
            items: Vec<ProtocolRuleMapItem<T>> => [vec nested term_map],
            /// Exact or associative remainder.
            remainder: ProtocolRuleFrame => [keep],
        },
        /// Functional result-side update.
        Update {
            /// Exact base-expression provenance.
            base_key: ProvenanceKey => [keep],
            /// Existing map term.
            base: T => [term_map],
            /// Exact updated-key provenance.
            key_key: ProvenanceKey => [keep],
            /// Updated key term.
            key: T => [term_map],
            /// Exact replacement-value provenance.
            value_key: ProvenanceKey => [keep],
            /// Replacement value term.
            value: T => [term_map],
        },
    }
}

protocol_shape! {
    /// Structured map occurrence in a configuration rule.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolRuleMap<T => term_map => T2> {
        /// Complete map payload provenance, at the invocation of an empty
        /// `map![]`.
        pub payload_key: ProvenanceKey => [keep],
        /// Classified map operation.
        pub body: ProtocolRuleMapBody<T> => [nested term_map],
    }
}

protocol_shape! {
    /// Leaf state families admitted by `cells!` entries.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(
        tag = "state_term_kind",
        rename_all = "snake_case",
        deny_unknown_fields
    )]
    pub enum ProtocolRuleStateTerm<T => term_map => T2> {
        /// Ordinary structured term.
        Term(value: T => [term_map]),
        /// Structured K sequence.
        KSequence(value: ProtocolRuleKSequence<T> => [nested term_map]),
        /// Structured map.
        Map(value: ProtocolRuleMap<T> => [nested term_map]),
        /// A whole nested (group) cell, written without a wrapper: a group
        /// binder, `_`, or a complete `k::fragment!` term (KF-016).
        Group(value: T => [term_map]),
        /// `Some(..)` of an optional (`?`) cell: the present cell's state
        /// (KF-023).
        Present {
            /// The state inside `Some(..)`.
            value: Box<ProtocolRuleStateTerm<T>> => [box nested term_map],
        },
        /// `None` of an optional (`?`) cell: the cell is absent (KF-023).
        Absent,
        /// The instances of a collection (`*`) cell (KF-023).
        Instances(value: ProtocolRuleInstances<T> => [nested term_map]),
    }
}

impl<T> ProtocolRuleStateTerm<T> {
    /// Every term of the state in traversal order: a term or group, the
    /// items of a K sequence, the terms of a map, the inside of `Some(..)`,
    /// and the children of collection instances.
    #[must_use]
    pub fn terms(&self) -> Vec<&T> {
        match self {
            Self::Term(term) | Self::Group(term) => vec![term],
            Self::KSequence(sequence) => sequence.items.iter().map(|item| &item.value).collect(),
            Self::Map(map) => match &map.body {
                ProtocolRuleMapBody::Empty { .. } => Vec::new(),
                ProtocolRuleMapBody::Items { items, .. } => items
                    .iter()
                    .flat_map(|item| [&item.key, &item.value])
                    .collect(),
                ProtocolRuleMapBody::Update {
                    base, key, value, ..
                } => vec![base, key, value],
            },
            Self::Present { value } => value.terms(),
            Self::Absent => Vec::new(),
            Self::Instances(instances) => instances
                .front
                .iter()
                .chain(&instances.back)
                .flat_map(|instance| &instance.fields)
                .flat_map(|field| field.value.terms())
                .collect(),
        }
    }
}

/// The delimiter of a collection-cell entry (KF-023, R8): braces for Set and
/// Map collections, brackets for List collections.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum InstanceDelimiter {
    /// `{ .. }`: some instances of a Set or Map collection.
    Brace,
    /// `[ .. ]`: the ends of a List collection.
    Bracket,
}

/// The rest of one collection instance record (KF-023).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "instance_rest", rename_all = "snake_case", deny_unknown_fields)]
pub enum ProtocolInstanceRest {
    /// No rest: the record names every child.
    Exact,
    /// `..`: in a pattern the other children are unconstrained; in a result
    /// they take their template defaults.
    Open,
    /// `..label` in a result: the matched instance `label`, updated.
    Update {
        /// The pattern instance label.
        label: String,
    },
}

protocol_shape! {
    /// One child cell named inside a collection instance record (KF-023).
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolRuleInstanceField<T => term_map => T2> {
        /// Exact child-field provenance.
        pub key: ProvenanceKey => [keep],
        /// The child's Rust field name in the instance's cell declaration.
        pub field: String => [keep],
        /// The child's state.
        pub value: ProtocolRuleStateTerm<T> => [nested term_map],
    }
}

protocol_shape! {
    /// One instance record of a collection-cell entry (KF-023).
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolRuleInstance<T => term_map => T2> {
        /// Exact instance-record provenance.
        pub key: ProvenanceKey => [keep],
        /// The authored pattern label (`me @ ..`); a label is not a binder.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub label: Option<String> => [keep],
        /// The named children in authored order.
        pub fields: Vec<ProtocolRuleInstanceField<T>> => [vec nested term_map],
        /// The record's rest.
        pub rest: ProtocolInstanceRest => [keep],
    }
}

protocol_shape! {
    /// The instances one collection-cell entry names (KF-023).
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolRuleInstances<T => term_map => T2> {
        /// Braces (Set, Map) or brackets (List).
        pub delimiter: InstanceDelimiter => [keep],
        /// The instances before the rest (every instance of a braced list).
        pub front: Vec<ProtocolRuleInstance<T>> => [vec nested term_map],
        /// The other instances: exact, `..`, `rest @ ..`, or `..rest`.
        pub rest: ProtocolRuleFrame => [keep],
        /// The instances after the rest of a bracketed list.
        #[serde(default = "Vec::new", skip_serializing_if = "Vec::is_empty")]
        pub back: Vec<ProtocolRuleInstance<T>> => [vec nested term_map],
    }
}

protocol_shape! {
    /// One selected fixed cell in a simultaneous configuration side.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolRuleCell<I => cell_map => I2, T => term_map => T2> {
        /// Exact selected-field provenance and owner-qualified identity.
        pub field: I => [cell_map],
        /// Exact `Cell`/`KCell` wrapper path provenance; absent exactly for a
        /// whole group-cell entry, which has no wrapper (KF-016).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub wrapper_key: Option<ProvenanceKey> => [keep],
        /// Typed wrapper meaning; absent exactly when `wrapper_key` is.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub wrapper: Option<CellWrapper> => [keep],
        /// Structured cell state.
        pub value: ProtocolRuleStateTerm<T> => [nested term_map],
    }
}

protocol_shape! {
    /// One complete `cells!` side of a simultaneous configuration rule.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolRuleCells<I => cell_map => I2, T => term_map => T2> {
        /// Complete `cells!` payload provenance.
        pub key: ProvenanceKey => [keep],
        /// Selected fixed cells in authored order.
        pub cells: Vec<ProtocolRuleCell<I, T>> => [vec nested cell_map term_map],
        /// Exact or framed remainder of the complete configuration.
        pub remainder: ProtocolRuleFrame => [keep],
    }
}

/// Stable selected-cell side.
pub type DescriptorRuleCells = ProtocolRuleCells<DescriptorCellReference, DescriptorTerm>;

/// Host selected-cell side.
pub type HostRuleCells = ProtocolRuleCells<HostCellReference, HostTerm>;

protocol_shape! {
    /// Semantic family of one binding in a one-sided context-alias pattern.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(tag = "binding_kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum ProtocolContextAliasBindingKind<S => sort_map => S2> {
        /// The distinguished ordinary term occurrence substituted for `HERE`.
        Here,
        /// An ordinary typed term binding other than `HERE`.
        Term {
            /// Exact authored sort reference.
            sort: S => [sort_map],
        },
        /// Named K-sequence tail.
        KSequenceFrame,
        /// Named map remainder.
        MapFrame,
        /// Named complete-configuration remainder.
        ConfigurationFrame,
    }
}

protocol_shape! {
    /// One binding in a one-sided context-alias pattern.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolContextAliasBinding<S => sort_map => S2> {
        /// Authored Rust binding name.
        pub name: String => [keep],
        /// Typed or structural binding family.
        pub kind: ProtocolContextAliasBindingKind<S> => [nested sort_map],
    }
}

stage_shape! {
    /// One-sided reusable configuration context template.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    #[serde(
        rename = "DescriptorContextAlias",
        bound(
            serialize = "
                S::Sort: Serialize,
                S::Configuration: Serialize,
                S::Cell: Serialize,
                S::Application: Serialize,
                S::Nominal: Serialize
            ",
            deserialize = "
                S::Sort: Deserialize<'de>,
                S::Configuration: Deserialize<'de>,
                S::Cell: Deserialize<'de>,
                S::Application: Deserialize<'de>,
                S::Nominal: Deserialize<'de>
            "
        )
    )]
    pub struct ContextAlias<S: Stage> {
        /// Declaration provenance.
        pub declaration_key: ProvenanceKey => [keep],
        /// Exact alias-name occurrence provenance.
        pub name_key: ProvenanceKey => [keep],
        /// Target-neutral authored alias identity.
        pub name: String => [keep],
        /// Exact `here` binder occurrence provenance.
        pub here_key: ProvenanceKey => [keep],
        /// Binding selected for native `HERE` substitution.
        pub here: String => [keep],
        /// Complete one-sided pattern provenance.
        pub pattern_key: ProvenanceKey => [keep],
        /// Exact fixed-configuration reference.
        pub configuration: S::Configuration => [configuration],
        /// Typed bindings in first-occurrence preorder.
        pub bindings: Vec<ProtocolContextAliasBinding<S::Sort>> => [vec protocol sort],
        /// Complete one-sided cells pattern.
        pub pattern: ProtocolRuleCells<S::Cell, crate::transport::grammar::Term<S>> => [protocol cell nested],
        /// Optional `result = S`, K's `result(S)` (KF-021).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub result: Option<S::Sort> => [option sort],
    }
}

/// Stable descriptor-stage form of [`ContextAlias`].
pub type DescriptorContextAlias = ContextAlias<DescriptorStage>;

stage_shape! {
    /// The read-only configuration context of an equation (KF-025): K's
    /// `[[ .. ]]` cells, a one-sided pattern framed by an anonymous remainder.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    #[serde(
        rename = "DescriptorFunctionContext",
        bound(
            serialize = "
                S::Sort: Serialize,
                S::Configuration: Serialize,
                S::Cell: Serialize,
                S::Application: Serialize,
                S::Nominal: Serialize
            ",
            deserialize = "
                S::Sort: Deserialize<'de>,
                S::Configuration: Deserialize<'de>,
                S::Cell: Deserialize<'de>,
                S::Application: Deserialize<'de>,
                S::Nominal: Deserialize<'de>
            "
        )
    )]
    pub struct FunctionContext<S: Stage> {
        /// Complete `k::cells! { .. }` parameter provenance.
        pub key: ProvenanceKey => [keep],
        /// Exact fixed-configuration reference.
        pub configuration: S::Configuration => [configuration],
        /// The context's bindings that the subject does not bind, in
        /// first-occurrence preorder; a term binding carries its declared sort.
        pub bindings: Vec<ProtocolRuleBinding<S::Sort>> => [vec protocol sort],
        /// Complete one-sided cells pattern.
        pub cells: ProtocolRuleCells<S::Cell, crate::transport::grammar::Term<S>> => [protocol cell nested],
    }
}

/// Stable descriptor-stage form of [`FunctionContext`].
pub type DescriptorFunctionContext = FunctionContext<DescriptorStage>;

impl DescriptorFunctionContext {
    /// The context's keys: the parameter and its configuration type define
    /// theirs, a term binding's sort names the sort its typed binding
    /// defines, and its cells are keyed as a rule's left side is.
    pub(crate) fn collect_keys(
        &self,
        keys: &mut WireKeys,
    ) -> Result<(), crate::GrammarTransportError> {
        keys.define(&self.key, ProvenanceRole::FunctionContext)?;
        keys.define(&self.configuration.key, ProvenanceRole::FunctionContextType)?;
        for binding in &self.bindings {
            if let ProtocolRuleBindingKind::Term { sort } = &binding.kind {
                keys.refer(&sort.key, ProvenanceRole::RuleBindingType)?;
            }
        }
        collect_pattern_keys::<DescriptorStage, _>(&self.cells, keys)
    }

    /// The names the context binds that the subject does not: every name
    /// the result and the requires condition may reference besides the
    /// subject's.
    #[must_use]
    pub fn binding_names(&self) -> BTreeSet<String> {
        self.bindings
            .iter()
            .map(|binding| binding.name.clone())
            .collect()
    }

    /// The context's term bindings in first-occurrence preorder.
    pub(crate) fn term_binding_names(&self) -> impl Iterator<Item = &str> {
        self.bindings.iter().filter_map(|binding| {
            matches!(binding.kind, ProtocolRuleBindingKind::Term { .. })
                .then_some(binding.name.as_str())
        })
    }
}

/// Build-local host-stage form of [`ContextAlias`].
pub type HostContextAlias = ContextAlias<HostStage>;

impl DescriptorContextAlias {
    /// Validates the frozen one-sided alias contract.
    ///
    /// # Errors
    ///
    /// Rejects wrong ownership, blank names, a missing/duplicate/wrong-kind
    /// `HERE` binding, or lost/mismatched structural frame bindings.
    pub fn validate(&self, descriptor_kind: ItemKind) -> Result<(), StateTransportError> {
        validate_context_alias(self, descriptor_kind)
    }

    /// Returns every parser-owned provenance key represented by this alias.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] when a key has another role than its
    /// field's, or two nodes define one key.
    pub fn expected_provenance_keys(&self) -> Result<BTreeSet<ProvenanceKey>, StateTransportError> {
        Ok(self.wire_keys()?.into_defined())
    }

    /// Validates shape plus exact closed provenance ownership.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for invalid shape or provenance.
    pub fn validate_complete_provenance(
        &self,
        descriptor_kind: ItemKind,
        primary: &ProvenanceKey,
        actual: &BTreeSet<ProvenanceKey>,
    ) -> Result<(), StateTransportError> {
        self.validate(descriptor_kind)?;
        if primary != &self.declaration_key {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::AliasPrimaryProvenanceMismatch,
            ));
        }
        self.wire_keys()?.close(actual)?;
        Ok(())
    }

    /// The alias's keys: its declaration, name, `here` binder, pattern and
    /// configuration type, its term bindings' sorts and its result sort
    /// define theirs, and its cells are keyed as a rule's left side is.
    fn wire_keys(&self) -> Result<WireKeys, StateTransportError> {
        let mut keys = WireKeys::default();
        keys.define(
            &self.declaration_key,
            ProvenanceRole::ContextAliasDeclaration,
        )?;
        keys.define(&self.name_key, ProvenanceRole::ContextAliasName)?;
        keys.define(&self.here_key, ProvenanceRole::ContextAliasHere)?;
        keys.define(&self.pattern_key, ProvenanceRole::RulePattern)?;
        keys.define(&self.configuration.key, ProvenanceRole::RuleType)?;
        for binding in &self.bindings {
            if let ProtocolContextAliasBindingKind::Term { sort } = &binding.kind {
                keys.define(&sort.key, ProvenanceRole::RuleBindingType)?;
            }
        }
        if let Some(result) = &self.result {
            keys.define(&result.key, ProvenanceRole::ContextAliasResult)?;
        }
        collect_pattern_keys::<DescriptorStage, StateTransportError>(&self.pattern, &mut keys)?;
        Ok(keys)
    }
}

impl HostContextAlias {
    /// Validates host ownership and the frozen `HERE` binding contract.
    ///
    /// # Errors
    ///
    /// Returns ownership, binding, and frame failures before stable reference resolution.
    pub fn validate(&self, descriptor_kind: ItemKind) -> Result<(), StateTransportError> {
        validate_context_alias(self, descriptor_kind)
    }
}

fn validate_context_alias<S: RuleValidationStage>(
    alias: &ContextAlias<S>,
    descriptor_kind: ItemKind,
) -> Result<(), StateTransportError> {
    if descriptor_kind != ItemKind::ContextAlias {
        return Err(StateTransportError::ItemKind {
            field: TransportField::ContextAliasDescriptor,
            expected: TransportItemKind::ContextAlias,
            actual: descriptor_kind,
        });
    }
    S::validate_configuration(&alias.configuration)?;
    if !valid_context_alias_name(&alias.name) || alias.here.trim().is_empty() {
        return Err(StateTransportError::InvalidText(
            TransportField::ContextAliasNameHere,
        ));
    }
    S::validate_alias_duplicates(&alias.bindings)?;
    let here = alias
        .bindings
        .iter()
        .filter(|binding| {
            binding.name == alias.here
                && matches!(binding.kind, ProtocolContextAliasBindingKind::Here)
        })
        .count();
    if here != 1 {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::AliasHereBindingCount,
        ));
    }
    S::validate_alias_here(&alias.pattern, &alias.here)?;
    validate_context_alias_frames(&alias.pattern, &alias.bindings)?;
    if let Some(result) = &alias.result {
        S::validate_binding_sort(result)?;
        let key = S::sort_key(result);
        if key.role() != ProvenanceRole::ContextAliasResult || key.ordinal() != 0 {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::InvalidEvaluationStep,
            ));
        }
    }
    Ok(())
}

#[expect(
    clippy::enum_variant_names,
    reason = "Each variant names the distinct frame family used by a context-alias binding."
)]
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum ContextAliasBindingUse {
    KSequenceFrame,
    MapFrame,
    ConfigurationFrame,
}

fn validate_context_alias_frames<I, T, S>(
    cells: &ProtocolRuleCells<I, T>,
    bindings: &[ProtocolContextAliasBinding<S>],
) -> Result<(), StateTransportError> {
    let names = bindings
        .iter()
        .map(|binding| binding.name.as_str())
        .collect::<BTreeSet<_>>();
    if names.len() != bindings.len() || names.iter().any(|name| name.trim().is_empty()) {
        return Err(StateTransportError::DuplicateValue(
            TransportField::ContextAliasBindings,
        ));
    }
    let structural = bindings
        .iter()
        .filter_map(|binding| {
            context_alias_binding_use(&binding.kind).map(|kind| (binding.name.clone(), kind))
        })
        .collect::<BTreeSet<_>>();
    let mut discovered = BTreeSet::new();
    for cell in &cells.cells {
        let mut value = &cell.value;
        while let ProtocolRuleStateTerm::Present { value: inner } = value {
            value = inner;
        }
        match value {
            ProtocolRuleStateTerm::Term(_) | ProtocolRuleStateTerm::Group(_) => {}
            ProtocolRuleStateTerm::KSequence(sequence) => validate_context_alias_frame(
                &sequence.tail,
                ContextAliasBindingUse::KSequenceFrame,
                &structural,
                &mut discovered,
            )?,
            ProtocolRuleStateTerm::Map(map) => {
                if let ProtocolRuleMapBody::Items { remainder, .. } = &map.body {
                    validate_context_alias_frame(
                        remainder,
                        ContextAliasBindingUse::MapFrame,
                        &structural,
                        &mut discovered,
                    )?;
                }
            }
            // A context alias is a one-sided pattern over fixed cells.
            ProtocolRuleStateTerm::Present { .. }
            | ProtocolRuleStateTerm::Absent
            | ProtocolRuleStateTerm::Instances(_) => {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::InvalidOptionalCellEntry,
                ));
            }
        }
    }
    validate_context_alias_frame(
        &cells.remainder,
        ContextAliasBindingUse::ConfigurationFrame,
        &structural,
        &mut discovered,
    )?;
    if discovered != structural {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::AliasBindingCatalogMismatch,
        ));
    }
    Ok(())
}

fn validate_context_alias_frame(
    frame: &ProtocolRuleFrame,
    expected: ContextAliasBindingUse,
    structural: &BTreeSet<(String, ContextAliasBindingUse)>,
    discovered: &mut BTreeSet<(String, ContextAliasBindingUse)>,
) -> Result<(), StateTransportError> {
    match frame {
        ProtocolRuleFrame::Exact | ProtocolRuleFrame::Anonymous { .. } => Ok(()),
        ProtocolRuleFrame::Bind { binding, .. } => {
            let occurrence = (binding.clone(), expected);
            if !structural.contains(&occurrence) || !discovered.insert(occurrence) {
                return Err(StateTransportError::InvalidTerm(
                    StateTermReason::AliasFrameBindingMismatch,
                ));
            }
            Ok(())
        }
        ProtocolRuleFrame::Reuse { .. } => Err(StateTransportError::InvalidTerm(
            StateTermReason::OneSidedAliasReusesResultFrame,
        )),
    }
}

fn context_alias_binding_use<S>(
    kind: &ProtocolContextAliasBindingKind<S>,
) -> Option<ContextAliasBindingUse> {
    match kind {
        ProtocolContextAliasBindingKind::Here | ProtocolContextAliasBindingKind::Term { .. } => {
            None
        }
        ProtocolContextAliasBindingKind::KSequenceFrame => {
            Some(ContextAliasBindingUse::KSequenceFrame)
        }
        ProtocolContextAliasBindingKind::MapFrame => Some(ContextAliasBindingUse::MapFrame),
        ProtocolContextAliasBindingKind::ConfigurationFrame => {
            Some(ContextAliasBindingUse::ConfigurationFrame)
        }
    }
}

fn valid_context_alias_name(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|first| first == '_' || first.is_ascii_alphabetic())
        && chars.all(|character| character == '_' || character.is_ascii_alphanumeric())
}

fn count_here_in_cells<I>(cells: &ProtocolRuleCells<I, DescriptorTerm>, here: &str) -> usize {
    cells
        .cells
        .iter()
        .map(|cell| count_here_in_state(&cell.value, here))
        .sum()
}

fn count_here_in_state(state: &ProtocolRuleStateTerm<DescriptorTerm>, here: &str) -> usize {
    match state {
        ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
            count_here_in_term(term, here)
        }
        ProtocolRuleStateTerm::Present { value } => count_here_in_state(value, here),
        ProtocolRuleStateTerm::Absent => 0,
        ProtocolRuleStateTerm::Instances(instances) => instances
            .front
            .iter()
            .chain(&instances.back)
            .flat_map(|instance| &instance.fields)
            .map(|field| count_here_in_state(&field.value, here))
            .sum(),
        ProtocolRuleStateTerm::KSequence(sequence) => sequence
            .items
            .iter()
            .map(|item| count_here_in_term(&item.value, here))
            .sum(),
        ProtocolRuleStateTerm::Map(map) => match &map.body {
            ProtocolRuleMapBody::Empty { .. } => 0,
            ProtocolRuleMapBody::Items { items, .. } => items
                .iter()
                .map(|item| {
                    count_here_in_term(&item.key, here) + count_here_in_term(&item.value, here)
                })
                .sum(),
            ProtocolRuleMapBody::Update {
                base, key, value, ..
            } => {
                count_here_in_term(base, here)
                    + count_here_in_term(key, here)
                    + count_here_in_term(value, here)
            }
        },
    }
}

fn count_here_in_term(term: &DescriptorTerm, here: &str) -> usize {
    match term {
        DescriptorTerm::Variable { name, .. } => usize::from(name == here),
        DescriptorTerm::Application { arguments, .. } => arguments
            .iter()
            .map(|argument| match argument {
                crate::TermArgumentRef::Positional { value }
                | crate::TermArgumentRef::Named { value, .. } => count_here_in_term(value, here),
            })
            .sum(),
        DescriptorTerm::Literal { .. }
        | DescriptorTerm::Wildcard { .. }
        | DescriptorTerm::BuiltinToken { .. }
        | DescriptorTerm::Anonymous { .. }
        | DescriptorTerm::Lexeme { .. } => 0,
        DescriptorTerm::OrBool { arguments, .. } => arguments
            .iter()
            .map(|argument| count_here_in_term(argument, here))
            .sum(),
        DescriptorTerm::Cell { fields, .. } => fields
            .iter()
            .map(|field| count_here_in_term(&field.value, here))
            .sum(),
        DescriptorTerm::SortTest { operand, .. } => count_here_in_term(operand, here),
        DescriptorTerm::As { name, pattern, .. } => {
            usize::from(name == here) + count_here_in_term(pattern, here)
        }
        DescriptorTerm::Or { alternatives, .. } => alternatives
            .iter()
            .map(|alternative| count_here_in_term(alternative, here))
            .sum(),
        DescriptorTerm::Matches {
            subject, pattern, ..
        } => count_here_in_term(subject, here) + count_here_in_term(pattern, here),
        DescriptorTerm::Rewrite { from, to, .. } => {
            count_here_in_term(from, here)
                + to.as_ref().map_or(0, |to| count_here_in_term(to, here))
        }
        DescriptorTerm::Let {
            pattern,
            value,
            body,
            ..
        } => {
            count_here_in_term(pattern, here)
                + count_here_in_term(value, here)
                + count_here_in_term(body, here)
        }
        DescriptorTerm::Closure { body, .. } => count_here_in_term(body, here),
    }
}

/// Collects the keys of a `cells!` payload on `side`, each of its role
/// there: the payload, each cell's field and wrapper, the structure of its
/// value ([`collect_state_keys`]), and the remainder. Each term the cells
/// hold goes to `term`.
fn collect_cells_keys<S: RuleValidationStage, E: From<KeyFailure>>(
    cells: &ProtocolRuleCells<S::Cell, Term<S>>,
    side: RuleSide,
    keys: &mut WireKeys,
    term: &mut impl FnMut(&Term<S>, &mut WireKeys) -> Result<(), E>,
) -> Result<(), E> {
    keys.define(&cells.key, RuleRole::CellsPayload.on_side(side))?;
    for cell in &cells.cells {
        collect_cell_keys::<S, E>(cell, side, keys, term)?;
    }
    if let Some(key) = frame_key(&cells.remainder) {
        keys.define(key, RuleRole::CellsRemainder.on_side(side))?;
    }
    Ok(())
}

/// Collects the keys of one cell of a `cells!` payload on `side`: its field,
/// its wrapper and the structure of its value; each term goes to `term`.
fn collect_cell_keys<S: RuleValidationStage, E: From<KeyFailure>>(
    cell: &ProtocolRuleCell<S::Cell, Term<S>>,
    side: RuleSide,
    keys: &mut WireKeys,
    term: &mut impl FnMut(&Term<S>, &mut WireKeys) -> Result<(), E>,
) -> Result<(), E> {
    keys.define(
        S::rule_cell_key(&cell.field),
        RuleRole::CellsField.on_side(side),
    )?;
    if let Some(wrapper_key) = &cell.wrapper_key {
        keys.define(wrapper_key, RuleRole::CellsWrapper.on_side(side))?;
    }
    collect_state_keys(&cell.value, side, keys, term)
}

/// Collects the keys of a one-sided `cells!` pattern's cell values, the
/// left side of an alias or a function context, whose nodes have no other
/// key walk.
fn collect_pattern_keys<S: RuleValidationStage, E>(
    cells: &ProtocolRuleCells<S::Cell, Term<S>>,
    keys: &mut WireKeys,
) -> Result<(), E>
where
    E: From<KeyFailure> + From<super::keys::TermRefusal>,
{
    collect_cells_keys::<S, E>(cells, RuleSide::Left, keys, &mut |term, keys| {
        super::keys::collect_term_keys(
            term,
            ValidationSide::Left,
            super::keys::TermKeying::CellValue,
            keys,
        )
    })
}

/// Collects the keys of a rule state's own nodes on `side`, each of its
/// role there: a K sequence's payload, `.K`, items and tail, a map's
/// payload, entries, update and remainder, and instances, their fields and
/// their rest. Each term the state holds goes to `term`, which collects its
/// keys as its rule's terms are keyed.
pub(super) fn collect_state_keys<T, E: From<KeyFailure>>(
    state: &ProtocolRuleStateTerm<T>,
    side: RuleSide,
    keys: &mut WireKeys,
    term: &mut impl FnMut(&T, &mut WireKeys) -> Result<(), E>,
) -> Result<(), E> {
    let define = |keys: &mut WireKeys, key: &ProvenanceKey, role: RuleRole| {
        keys.define(key, role.on_side(side))
    };
    match state {
        ProtocolRuleStateTerm::Term(value) | ProtocolRuleStateTerm::Group(value) => {
            term(value, keys)?;
        }
        ProtocolRuleStateTerm::Present { value } => collect_state_keys(value, side, keys, term)?,
        ProtocolRuleStateTerm::Absent => {}
        ProtocolRuleStateTerm::Instances(instances) => {
            for instance in instances.front.iter().chain(&instances.back) {
                define(keys, &instance.key, RuleRole::CellsInstance)?;
                for field in &instance.fields {
                    define(keys, &field.key, RuleRole::CellsInstanceField)?;
                    collect_state_keys(&field.value, side, keys, term)?;
                }
            }
            if let Some(key) = frame_key(&instances.rest) {
                define(keys, key, RuleRole::CellsInstancesRest)?;
            }
        }
        ProtocolRuleStateTerm::KSequence(sequence) => {
            define(keys, &sequence.payload_key, RuleRole::KSequencePayload)?;
            for key in sequence.dot_k_key.iter().chain(frame_key(&sequence.tail)) {
                define(keys, key, RuleRole::KSequenceTail)?;
            }
            for item in &sequence.items {
                define(keys, &item.key, RuleRole::KSequenceItem)?;
                term(&item.value, keys)?;
            }
        }
        ProtocolRuleStateTerm::Map(map) => {
            define(keys, &map.payload_key, RuleRole::MapPayload)?;
            match &map.body {
                ProtocolRuleMapBody::Empty { .. } => {}
                ProtocolRuleMapBody::Items { items, remainder } => {
                    for item in items {
                        define(keys, &item.key_key, RuleRole::MapKey)?;
                        define(keys, &item.value_key, RuleRole::MapValue)?;
                        term(&item.key, keys)?;
                        term(&item.value, keys)?;
                    }
                    if let Some(key) = frame_key(remainder) {
                        define(keys, key, RuleRole::MapRemainder)?;
                    }
                }
                ProtocolRuleMapBody::Update {
                    base_key,
                    base,
                    key_key,
                    key,
                    value_key,
                    value,
                } => {
                    define(keys, base_key, RuleRole::MapUpdateBase)?;
                    define(keys, key_key, RuleRole::MapKey)?;
                    define(keys, value_key, RuleRole::MapValue)?;
                    for value in [base, key, value] {
                        term(value, keys)?;
                    }
                }
            }
        }
    }
    Ok(())
}

pub(super) fn frame_key(frame: &ProtocolRuleFrame) -> Option<&ProvenanceKey> {
    match frame {
        ProtocolRuleFrame::Exact => None,
        ProtocolRuleFrame::Anonymous { key }
        | ProtocolRuleFrame::Bind { key, .. }
        | ProtocolRuleFrame::Reuse { key, .. } => Some(key),
    }
}

stage_shape! {
    /// Stable simultaneous configuration rewrite.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    #[serde(
        rename = "DescriptorConfigurationRule",
        bound(
            serialize = "
                S::Sort: Serialize,
                S::Configuration: Serialize,
                S::Cell: Serialize,
                S::Application: Serialize,
                S::Nominal: Serialize
            ",
            deserialize = "
                S::Sort: Deserialize<'de>,
                S::Configuration: Deserialize<'de>,
                S::Cell: Deserialize<'de>,
                S::Application: Deserialize<'de>,
                S::Nominal: Deserialize<'de>
            "
        )
    )]
    pub struct ConfigurationRule<S: Stage> {
        /// Explicit relational sentence meaning.
        pub sentence_kind: crate::ConfigurationSentenceKind => [keep],
        /// Optional explicit emitted K label.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub label: Option<DescriptorRuleLabel> => [keep],
        /// Optional priority transported from `#[k::rule(owise)]` or `#[k::rule(priority = N)]`.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub priority: Option<crate::DescriptorRulePriority> => [keep],
        /// Optional check-only nondeterminism group from `#[k::rule(nondet = group)]`.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub nondet: Option<crate::DescriptorNondetGroup> => [keep],
        /// Optional object-language Boolean applicability condition.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub requires: Option<crate::transport::grammar::RuleCondition<S>> => [option nested],
        /// Required claim-only metadata, present iff this is a claim.
        #[serde(skip_serializing_if = "S::skip_none")]
        pub claim: Option<Claim<S>> => [option nested],
        /// Complete subject-pattern provenance.
        pub pattern_key: ProvenanceKey => [keep],
        /// Exact subject configuration type.
        pub subject_configuration: S::Configuration => [configuration],
        /// Complete result-expression provenance; absent exactly for a
        /// single-body rule (KF-011).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub result_key: Option<ProvenanceKey> => [keep],
        /// Exact result configuration type; absent exactly for a single-body
        /// rule.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub result_configuration: Option<S::Configuration> => [option configuration],
        /// Typed subject bindings in first-occurrence structural preorder.
        pub bindings: Vec<ProtocolRuleBinding<S::Sort>> => [vec protocol sort],
        /// Complete left `cells!` pattern; in a single-body rule it contains
        /// the `k::rewrite!` islands that mark what changes.
        pub subject: ProtocolRuleCells<S::Cell, crate::transport::grammar::Term<S>> => [protocol cell nested],
        /// Complete right `cells!` expression; absent exactly for a
        /// single-body rule.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub result: Option<ProtocolRuleCells<S::Cell, crate::transport::grammar::Term<S>>> => [option protocol cell nested],
        /// Result-scoped existential binders of a transition (`#[k::exists]`); a claim keeps its own in [`Claim`].
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        pub existentials: Vec<ClaimBinder<S>> => [vec nested],
        /// Optional object-Bool postcondition of a transition (`#[k::ensures]`); a claim keeps its own in [`Claim`].
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub ensures: Option<crate::transport::grammar::RuleCondition<S>> => [option nested],
        /// Fresh binders of a transition (`#[k::fresh]`), K's `!X`.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        pub fresh: Vec<ClaimBinder<S>> => [vec nested],
        /// The `heat` or `cool` key of a transition (KF-014).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub evaluation: Option<EvaluationStep<S>> => [option nested],
    }
}

/// Stable descriptor-stage form of [`ConfigurationRule`].
pub type DescriptorConfigurationRule = ConfigurationRule<DescriptorStage>;

/// Build-local host-stage form of [`ConfigurationRule`].
pub type HostConfigurationRule = ConfigurationRule<HostStage>;

#[derive(Clone, Copy)]
pub(super) enum ValidationSide {
    Left,
    Right,
    Requires,
    Ensures,
    RuleEnsures,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RuleBindingUse {
    Term,
    KSequenceFrame,
    MapFrame,
    ConfigurationFrame,
    InstancesFrame,
}

impl From<RuleSide> for ValidationSide {
    fn from(side: RuleSide) -> Self {
        match side {
            RuleSide::Left => Self::Left,
            RuleSide::Right => Self::Right,
        }
    }
}

/// A term role whose provenance spelling depends on the rule clause.
#[derive(Clone, Copy)]
pub(super) enum TermRole {
    Path,
    ApplicationHead,
    Reference,
    Literal,
    RecordFieldName,
}

impl TermRole {
    pub(super) const fn on_side(self, side: ValidationSide) -> ProvenanceRole {
        match (side, self) {
            (ValidationSide::Left, Self::Path) => ProvenanceRole::RuleLeftPath,
            (ValidationSide::Left, Self::ApplicationHead) => {
                ProvenanceRole::RuleLeftApplicationHead
            }
            (ValidationSide::Left, Self::Reference) => ProvenanceRole::RuleLeftReference,
            (ValidationSide::Left, Self::Literal) => ProvenanceRole::RuleLeftLiteral,
            (ValidationSide::Left, Self::RecordFieldName) => {
                ProvenanceRole::RuleLeftRecordFieldName
            }
            (ValidationSide::Right, Self::Path) => ProvenanceRole::RuleRightPath,
            (ValidationSide::Right, Self::ApplicationHead) => {
                ProvenanceRole::RuleRightApplicationHead
            }
            (ValidationSide::Right, Self::Reference) => ProvenanceRole::RuleRightReference,
            (ValidationSide::Right, Self::Literal) => ProvenanceRole::RuleRightLiteral,
            (ValidationSide::Right, Self::RecordFieldName) => {
                ProvenanceRole::RuleRightRecordFieldName
            }
            (ValidationSide::Requires, Self::Path) => ProvenanceRole::RuleRequiresPath,
            (ValidationSide::Requires, Self::ApplicationHead) => {
                ProvenanceRole::RuleRequiresApplicationHead
            }
            (ValidationSide::Requires, Self::Reference) => ProvenanceRole::RuleRequiresReference,
            (ValidationSide::Requires, Self::Literal) => ProvenanceRole::RuleRequiresLiteral,
            (ValidationSide::Requires, Self::RecordFieldName) => {
                ProvenanceRole::RuleRequiresRecordFieldName
            }
            (ValidationSide::Ensures, Self::Path) => ProvenanceRole::ClaimEnsuresPath,
            (ValidationSide::Ensures, Self::ApplicationHead) => {
                ProvenanceRole::ClaimEnsuresApplicationHead
            }
            (ValidationSide::Ensures, Self::Reference) => ProvenanceRole::ClaimEnsuresReference,
            (ValidationSide::Ensures, Self::Literal) => ProvenanceRole::ClaimEnsuresLiteral,
            (ValidationSide::Ensures, Self::RecordFieldName) => {
                ProvenanceRole::ClaimEnsuresRecordFieldName
            }
            (ValidationSide::RuleEnsures, Self::Path) => ProvenanceRole::RuleEnsuresPath,
            (ValidationSide::RuleEnsures, Self::ApplicationHead) => {
                ProvenanceRole::RuleEnsuresApplicationHead
            }
            (ValidationSide::RuleEnsures, Self::Reference) => ProvenanceRole::RuleEnsuresReference,
            (ValidationSide::RuleEnsures, Self::Literal) => ProvenanceRole::RuleEnsuresLiteral,
            (ValidationSide::RuleEnsures, Self::RecordFieldName) => {
                ProvenanceRole::RuleEnsuresRecordFieldName
            }
        }
    }
}

/// Where a rule term walk stands, and how many `k::rewrite!` islands the
/// subject held.
#[derive(Default)]
#[expect(
    clippy::struct_excessive_bools,
    reason = "Each flag records one independent nesting context of the term walk."
)]
struct RuleWalk {
    /// Whether the validator is inside a `k::matches!` pattern.
    in_matches_pattern: bool,
    /// Whether the validator is inside a `let` pattern.
    in_let_pattern: bool,
    /// The `k::rewrite!` islands of the side (KF-011).
    rewrites: u32,
    /// Whether `k::rewrite!` is admitted: the subject of a single-body rule.
    allow_rewrite: bool,
    /// Whether the validator is inside the right side of a `k::rewrite!`.
    in_rewrite_right: bool,
    /// Whether the term being validated is a whole K-sequence item, whose
    /// root rewrite may remove it (`k::rewrite!(x => ())`).
    k_item_root: bool,
}

fn builtin_token_role(
    sort: crate::BuiltinSort,
    value: &str,
) -> Result<ProvenanceRole, StateTransportError> {
    super::validation::builtin_token_literal_role(sort, value).ok_or(
        StateTransportError::InvalidTerm(StateTermReason::InvalidCompilerOwnedBuiltinToken),
    )
}

trait RuleValidationStage: ValidationStage {
    /// Descriptor cells use stable owner/field identities; host cells use resolved type identities.
    type RuleCellIdentity: Ord;
    /// Configuration provenance is stored beside either a stable identity or a host reference.
    fn configuration_key(configuration: &Self::Configuration) -> &ProvenanceKey;
    /// Host configuration references have no stable kind; `DescriptorStage::validate_configuration` must check the resolved Configuration kind.
    fn validate_configuration(
        configuration: &Self::Configuration,
    ) -> Result<(), StateTransportError>;
    /// Descriptor configurations compare stable identities; host configurations compare resolved type identities.
    fn same_configuration(left: &Self::Configuration, right: &Self::Configuration) -> bool;
    /// Host selected cells have no stable owner kind; `DescriptorStage::validate_rule_cell` must check the resolved identity and Configuration or nominal Cell ownership.
    fn validate_rule_cell(
        cell: &Self::Cell,
        owner: &Self::Configuration,
    ) -> Result<(), StateTransportError>;
    /// Descriptor cells compare stable identities; host cells compare resolved owner/field identities.
    fn rule_cell_identity(cell: &Self::Cell) -> Self::RuleCellIdentity;
    /// Cell provenance accompanies either a stable identity or a host identity.
    fn rule_cell_key(cell: &Self::Cell) -> &ProvenanceKey;
    /// Host binding sorts have no stable kind; `DescriptorStage::validate_binding_sort` must check the resolved declared Sort kind.
    fn validate_binding_sort(sort: &Self::Sort) -> Result<(), StateTransportError>;
    /// Descriptor labels enter the rule key set; host labels are validated in an isolated set.
    fn define_rule_label(
        keys: &mut WireKeys,
        key: &ProvenanceKey,
        role: ProvenanceRole,
    ) -> Result<(), StateTransportError>;
    /// Descriptor rules other than claims fix their declaration key, which no
    /// wire field carries (a claim's is its claim's declaration key); host
    /// rules do not collect it.
    fn fix_rule_declaration(
        keys: &mut WireKeys,
        kind: crate::ConfigurationSentenceKind,
    ) -> Result<(), StateTransportError>;
    /// Descriptor aliases must retain their duplicate-binding error before HERE validation.
    /// Host aliases must retain HERE-binding errors before the duplicate catalog error from frame validation.
    /// These orders preserve each stage's existing first error for aliases with multiple faults.
    fn validate_alias_duplicates(
        bindings: &[ProtocolContextAliasBinding<Self::Sort>],
    ) -> Result<(), StateTransportError>;
    /// Host alias validation must retain its binding/frame-only acceptance contract; `DescriptorStage::validate_alias_here` must count exactly one HERE content occurrence after resolution and before collector output.
    fn validate_alias_here(
        cells: &ProtocolRuleCells<Self::Cell, Term<Self>>,
        here: &str,
    ) -> Result<(), StateTransportError>;
}

impl RuleValidationStage for DescriptorStage {
    type RuleCellIdentity = crate::DescriptorCellIdentity;

    fn configuration_key(configuration: &Self::Configuration) -> &ProvenanceKey {
        &configuration.key
    }

    fn validate_configuration(
        configuration: &Self::Configuration,
    ) -> Result<(), StateTransportError> {
        configuration.validate()
    }

    fn same_configuration(left: &Self::Configuration, right: &Self::Configuration) -> bool {
        left.configuration == right.configuration
    }

    fn validate_rule_cell(
        cell: &Self::Cell,
        owner: &Self::Configuration,
    ) -> Result<(), StateTransportError> {
        cell.cell.validate()?;
        if cell.cell.owner != owner.configuration && cell.cell.owner.item_kind() != ItemKind::Cell {
            return Err(StateTransportError::CellOwnerMismatch);
        }
        Ok(())
    }

    fn rule_cell_identity(cell: &Self::Cell) -> Self::RuleCellIdentity {
        cell.cell.clone()
    }

    fn rule_cell_key(cell: &Self::Cell) -> &ProvenanceKey {
        &cell.key
    }

    fn validate_binding_sort(sort: &Self::Sort) -> Result<(), StateTransportError> {
        if let DescriptorSortRef::Declared(sort) = &sort.sort
            && sort.item_kind() != ItemKind::Sort
        {
            return Err(StateTransportError::ItemKind {
                field: TransportField::RuleBindingSort,
                expected: TransportItemKind::Sort,
                actual: sort.item_kind(),
            });
        }
        Ok(())
    }

    fn define_rule_label(
        keys: &mut WireKeys,
        key: &ProvenanceKey,
        role: ProvenanceRole,
    ) -> Result<(), StateTransportError> {
        Ok(keys.define(key, role)?)
    }

    fn fix_rule_declaration(
        keys: &mut WireKeys,
        kind: crate::ConfigurationSentenceKind,
    ) -> Result<(), StateTransportError> {
        if kind != crate::ConfigurationSentenceKind::Claim {
            keys.fixed(ProvenanceRole::RuleDeclaration)?;
        }
        Ok(())
    }

    fn validate_alias_duplicates(
        bindings: &[ProtocolContextAliasBinding<Self::Sort>],
    ) -> Result<(), StateTransportError> {
        let mut names = BTreeSet::new();
        if bindings
            .iter()
            .any(|binding| !names.insert(binding.name.as_str()))
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::DuplicateAliasBinding,
            ));
        }
        Ok(())
    }

    fn validate_alias_here(
        cells: &ProtocolRuleCells<Self::Cell, Term<Self>>,
        here: &str,
    ) -> Result<(), StateTransportError> {
        if count_here_in_cells(cells, here) != 1 {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::AliasHereContentOccurrence,
            ));
        }
        Ok(())
    }
}

impl RuleValidationStage for HostStage {
    type RuleCellIdentity = (std::any::TypeId, std::any::TypeId);

    fn configuration_key(configuration: &Self::Configuration) -> &ProvenanceKey {
        &configuration.key
    }

    fn validate_configuration(_: &Self::Configuration) -> Result<(), StateTransportError> {
        Ok(())
    }

    fn same_configuration(left: &Self::Configuration, right: &Self::Configuration) -> bool {
        left.configuration.key.resolve() == right.configuration.key.resolve()
    }

    fn validate_rule_cell(
        _: &Self::Cell,
        _: &Self::Configuration,
    ) -> Result<(), StateTransportError> {
        Ok(())
    }

    fn rule_cell_identity(cell: &Self::Cell) -> Self::RuleCellIdentity {
        cell.cell.resolve()
    }

    fn rule_cell_key(cell: &Self::Cell) -> &ProvenanceKey {
        &cell.key
    }

    fn validate_binding_sort(_: &Self::Sort) -> Result<(), StateTransportError> {
        Ok(())
    }

    fn define_rule_label(
        _: &mut WireKeys,
        key: &ProvenanceKey,
        role: ProvenanceRole,
    ) -> Result<(), StateTransportError> {
        Ok(WireKeys::default().define(key, role)?)
    }

    fn fix_rule_declaration(
        _: &mut WireKeys,
        _: crate::ConfigurationSentenceKind,
    ) -> Result<(), StateTransportError> {
        Ok(())
    }

    fn validate_alias_duplicates(
        _: &[ProtocolContextAliasBinding<Self::Sort>],
    ) -> Result<(), StateTransportError> {
        Ok(())
    }

    fn validate_alias_here(
        _: &ProtocolRuleCells<Self::Cell, Term<Self>>,
        _: &str,
    ) -> Result<(), StateTransportError> {
        Ok(())
    }
}

impl DescriptorConfigurationReference {
    fn validate(&self) -> Result<(), StateTransportError> {
        if self.configuration.item_kind() != ItemKind::Configuration {
            return Err(StateTransportError::ItemKind {
                field: TransportField::ConfigurationRuleType,
                expected: TransportItemKind::Configuration,
                actual: self.configuration.item_kind(),
            });
        }
        Ok(())
    }
}

impl DescriptorConfigurationRule {
    /// Validates ownership, configuration/cell identities, frame bindings,
    /// structured terms, and side-specific parser key roles.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for any invalid rule shape.
    pub fn validate(&self, descriptor_kind: ItemKind) -> Result<(), StateTransportError> {
        self.wire_keys(descriptor_kind).map(|_| ())
    }

    /// Returns every key this rule's nodes carry, with its fixed declaration
    /// key.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::validate`].
    pub fn expected_provenance_keys(
        &self,
        descriptor_kind: ItemKind,
    ) -> Result<BTreeSet<ProvenanceKey>, StateTransportError> {
        Ok(self.wire_keys(descriptor_kind)?.into_defined())
    }

    /// Validates a closed provenance table and the rule or claim declaration primary key.
    ///
    /// # Errors
    ///
    /// Returns an error for rule shape, missing/extra keys, or wrong primary.
    pub fn validate_complete_provenance(
        &self,
        descriptor_kind: ItemKind,
        primary: &ProvenanceKey,
        actual: &BTreeSet<ProvenanceKey>,
    ) -> Result<(), StateTransportError> {
        let keys = self.wire_keys(descriptor_kind)?;
        let declaration = if self.sentence_kind == crate::ConfigurationSentenceKind::Claim {
            ProvenanceRole::ClaimDeclaration
        } else {
            ProvenanceRole::RuleDeclaration
        };
        let expected = ProvenanceKey::new(declaration, 0);
        if primary != &expected {
            return Err(StateTransportError::MismatchedProvenance {
                expected,
                actual: primary.clone(),
            });
        }
        keys.close(actual)?;
        Ok(())
    }

    fn wire_keys(&self, descriptor_kind: ItemKind) -> Result<WireKeys, StateTransportError> {
        let mut keys = WireKeys::default();
        validate_configuration_rule(self, descriptor_kind, &mut keys)?;
        Ok(keys)
    }
}

impl HostConfigurationRule {
    /// Validates host configuration equality, selected-cell uniqueness, and parser key roles.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for invalid ownership, frames, terms,
    /// or side-specific provenance roles.
    pub fn validate(&self, descriptor_kind: ItemKind) -> Result<(), StateTransportError> {
        validate_configuration_rule(self, descriptor_kind, &mut WireKeys::default())
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "Rule validation must preserve the ordered provenance pass."
)]
fn validate_configuration_rule<S: RuleValidationStage>(
    rule: &ConfigurationRule<S>,
    descriptor_kind: ItemKind,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    validate_sentence_kind(rule.sentence_kind, descriptor_kind)?;
    if rule.sentence_kind == crate::ConfigurationSentenceKind::Claim {
        if rule.claim.is_none() || rule.label.is_none() {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::MissingClaimMetadataOrLabel,
            ));
        }
    } else if rule.claim.is_some() {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::UnexpectedClaimMetadata,
        ));
    }
    if let Some(label) = &rule.label {
        let label_role = match rule.sentence_kind {
            crate::ConfigurationSentenceKind::Claim => ProvenanceRole::ClaimLabel,
            crate::ConfigurationSentenceKind::Context => ProvenanceRole::ContextLabel,
            _ => ProvenanceRole::RuleLabel,
        };
        S::define_rule_label(keys, &label.key, label_role)?;
        if !valid_rule_label_name(&label.name) {
            return Err(StateTransportError::InvalidText(TransportField::RuleLabel));
        }
    }
    if let Some(priority) = &rule.priority {
        let priority_role = priority
            .role_for(crate::SentenceKind::Transition)
            .unwrap_or(ProvenanceRole::RuleOwise);
        keys.define(&priority.key, priority_role)?;
        if rule.sentence_kind != crate::ConfigurationSentenceKind::Transition
            || priority.role_for(crate::SentenceKind::Transition).is_none()
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::ConfigurationRuleOrderedFallbackPriority,
            ));
        }
    }
    if let Some(nondet) = &rule.nondet {
        keys.define(&nondet.key, ProvenanceRole::RuleNondetGroup)?;
        if rule.sentence_kind != crate::ConfigurationSentenceKind::Transition || !nondet.is_valid()
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::InvalidNondetGroup,
            ));
        }
    }
    S::validate_configuration(&rule.subject_configuration)?;
    // A single-body rule (KF-011) has no result: its subject's `k::rewrite!`
    // islands mark what changes.
    let result = match (&rule.result_key, &rule.result_configuration, &rule.result) {
        (Some(result_key), Some(result_configuration), Some(result)) => {
            Some((result_key, result_configuration, result))
        }
        (None, None, None) => None,
        _ => {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::SingleBodyRuleWithoutRewrite,
            ));
        }
    };
    if let Some((_, result_configuration, _)) = result {
        S::validate_configuration(result_configuration)?;
        if !S::same_configuration(&rule.subject_configuration, result_configuration) {
            return Err(StateTransportError::InvalidCellContent(
                StateCellContentReason::RuleSubjectAndResultConfigurationsDiffer,
            ));
        }
    } else if !matches!(
        rule.sentence_kind,
        crate::ConfigurationSentenceKind::Transition | crate::ConfigurationSentenceKind::Context
    ) {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::RewriteOutsideSingleBodyRule,
        ));
    }
    // A context (KF-021) has no post-state and is not a single-body rule:
    // it may rewrite its hole once, or not at all.
    let context = rule.sentence_kind == crate::ConfigurationSentenceKind::Context;
    if context && (result.is_some() || rule.evaluation.is_none()) {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidEvaluationStep,
        ));
    }
    keys.define(&rule.pattern_key, ProvenanceRole::RulePattern)?;
    keys.define(
        S::configuration_key(&rule.subject_configuration),
        ProvenanceRole::RuleType,
    )?;
    if let Some((result_key, result_configuration, _)) = result {
        keys.define(result_key, ProvenanceRole::RuleResult)?;
        keys.define(
            S::configuration_key(result_configuration),
            ProvenanceRole::RuleResultType,
        )?;
    }
    S::fix_rule_declaration(keys, rule.sentence_kind)?;
    validate_rule_binding_catalog::<S>(&rule.bindings, keys)?;

    let mut discovered = Vec::new();
    let mut subject = RuleWalk {
        allow_rewrite: result.is_none(),
        ..RuleWalk::default()
    };
    validate_rule_cells::<S>(
        &rule.subject,
        &rule.subject_configuration,
        RuleSide::Left,
        &rule.bindings,
        &mut discovered,
        &mut subject,
        keys,
    )?;
    if !binding_names_match(&rule.bindings, &discovered) {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::BindingCatalogOrder,
        ));
    }
    if result.is_none() && subject.rewrites == 0 && !context {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::SingleBodyRuleWithoutRewrite,
        ));
    }
    if context && subject.rewrites > 1 {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidEvaluationStep,
        ));
    }
    let mut ignored = Vec::new();
    let mut right_bindings = rule.bindings.clone();
    if (!rule.existentials.is_empty() || rule.ensures.is_some())
        && rule.sentence_kind != crate::ConfigurationSentenceKind::Transition
    {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidRuleExistential,
        ));
    }
    if !rule.fresh.is_empty() && rule.sentence_kind != crate::ConfigurationSentenceKind::Transition
    {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidRuleFresh,
        ));
    }
    for binder in rule.existentials.iter().chain(&rule.fresh) {
        right_bindings.push(ProtocolRuleBinding {
            name: binder.name.clone(),
            kind: ProtocolRuleBindingKind::Term {
                sort: binder.sort.clone(),
            },
        });
    }
    if let Some(claim) = &rule.claim {
        for binder in &claim.existentials {
            right_bindings.push(ProtocolRuleBinding {
                name: binder.name.clone(),
                kind: ProtocolRuleBindingKind::Term {
                    sort: binder.sort.clone(),
                },
            });
        }
    }
    if let Some((_, result_configuration, result)) = result {
        validate_rule_cells::<S>(
            result,
            result_configuration,
            RuleSide::Right,
            &right_bindings,
            &mut ignored,
            &mut RuleWalk::default(),
            keys,
        )?;
    }
    if let Some(requires) = &rule.requires {
        keys.define(&requires.key, ProvenanceRole::RuleRequires)?;
        validate_rule_term::<S>(
            &requires.term,
            ValidationSide::Requires,
            &rule.bindings,
            &mut Vec::new(),
            &mut RuleWalk::default(),
            keys,
        )?;
    }
    if let Some(claim) = &rule.claim {
        validate_rule_claim::<S>(claim, &rule.bindings, &right_bindings, keys)?;
    }
    validate_rule_existentials::<S>(rule, &right_bindings, keys)?;
    if let Some(step) = &rule.evaluation {
        validate_rule_evaluation::<S>(
            step,
            if context {
                step.kind == EvaluationKind::Context
            } else {
                rule.sentence_kind == crate::ConfigurationSentenceKind::Transition
                    && step.kind != EvaluationKind::Context
                    && rule.priority.is_none()
                    && rule.nondet.is_none()
                    && rule.fresh.is_empty()
            },
            keys,
        )?;
    }
    Ok(())
}

/// Checks the `heat` or `cool` key of a transition (KF-014): it is allowed
/// only on a transition without priority, nondet group, or fresh binders.
/// Whether the hole is a left-side binder is a semantic check.
fn validate_rule_evaluation<S: RuleValidationStage>(
    step: &EvaluationStep<S>,
    allowed: bool,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    if !allowed || !step.has_valid_roles(|sort| S::sort_key(sort)) {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidEvaluationStep,
        ));
    }
    keys.define(&step.key, step.kind.role())?;
    keys.define(&step.hole_key, step.kind.hole_role())?;
    if let Some(sort) = &step.result {
        S::validate_binding_sort(sort)?;
        keys.define(S::sort_key(sort), step.kind.result_role())?;
    }
    Ok(())
}

/// Checks the result-scoped existentials, the fresh binders, and the ensures condition of a transition.
fn validate_rule_existentials<S: RuleValidationStage>(
    rule: &ConfigurationRule<S>,
    right_bindings: &[ProtocolRuleBinding<S::Sort>],
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    let mut names = BTreeSet::new();
    for binder in &rule.existentials {
        if binder.name.trim().is_empty()
            || !names.insert(binder.name.clone())
            || rule
                .bindings
                .iter()
                .any(|binding| binding.name == binder.name)
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::InvalidRuleExistential,
            ));
        }
        S::validate_binding_sort(&binder.sort)?;
        keys.define(
            &binder.declaration_key,
            ProvenanceRole::RuleExistentialBinder,
        )?;
        keys.define(&binder.name_key, ProvenanceRole::RuleExistentialBinderName)?;
        keys.define(
            S::sort_key(&binder.sort),
            ProvenanceRole::RuleExistentialBinderSort,
        )?;
    }
    for binder in &rule.fresh {
        if binder.name.trim().is_empty()
            || !names.insert(binder.name.clone())
            || rule
                .bindings
                .iter()
                .any(|binding| binding.name == binder.name)
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::InvalidRuleFresh,
            ));
        }
        S::validate_binding_sort(&binder.sort)?;
        keys.define(&binder.declaration_key, ProvenanceRole::RuleFreshBinder)?;
        keys.define(&binder.name_key, ProvenanceRole::RuleFreshBinderName)?;
        keys.define(
            S::sort_key(&binder.sort),
            ProvenanceRole::RuleFreshBinderSort,
        )?;
    }
    if let Some(ensures) = &rule.ensures {
        keys.define(&ensures.key, ProvenanceRole::RuleEnsures)?;
        validate_rule_term::<S>(
            &ensures.term,
            ValidationSide::RuleEnsures,
            right_bindings,
            &mut Vec::new(),
            &mut RuleWalk::default(),
            keys,
        )?;
    }
    Ok(())
}

fn validate_rule_claim<S: RuleValidationStage>(
    claim: &Claim<S>,
    left_bindings: &[ProtocolRuleBinding<S::Sort>],
    right_bindings: &[ProtocolRuleBinding<S::Sort>],
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    keys.define(&claim.declaration_key, ProvenanceRole::ClaimDeclaration)?;
    keys.define(&claim.modality_key, ProvenanceRole::ClaimModality)?;
    if let Some(key) = &claim.circularity_key {
        if claim.modality != ClaimModality::AllPaths {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::CircularityRequiresAnAllPathClaim,
            ));
        }
        keys.define(key, ProvenanceRole::ClaimCircularity)?;
    }
    if let Some(key) = &claim.trusted_key {
        if claim.circularity_key.is_some() {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::TrustedClaimWithCircularity,
            ));
        }
        keys.define(key, ProvenanceRole::ClaimTrusted)?;
    }
    validate_rule_claim_binders::<S>(
        &claim.universals,
        left_bindings,
        ProvenanceRole::ClaimUniversalBinder,
        keys,
    )?;
    validate_rule_claim_binders::<S>(
        &claim.existentials,
        right_bindings,
        ProvenanceRole::ClaimExistentialBinder,
        keys,
    )?;
    // Each `k::or_bool!` term defines its key; the claim lists them.
    for key in &claim.or_bool_keys {
        keys.refer(key, ProvenanceRole::ClaimOrBool)?;
    }
    if let Some(ensures) = &claim.ensures {
        keys.define(&ensures.key, ProvenanceRole::ClaimEnsures)?;
        validate_rule_term::<S>(
            &ensures.term,
            ValidationSide::Ensures,
            right_bindings,
            &mut Vec::new(),
            &mut RuleWalk::default(),
            keys,
        )?;
    }
    Ok(())
}

fn validate_rule_claim_binders<S: RuleValidationStage>(
    binders: &[ClaimBinder<S>],
    catalog: &[ProtocolRuleBinding<S::Sort>],
    declaration_role: ProvenanceRole,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    let mut names = BTreeSet::new();
    for binder in binders {
        if binder.name.trim().is_empty()
            || !names.insert(binder.name.clone())
            || !binding_has_kind(catalog, &binder.name, RuleBindingUse::Term)
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::InvalidClaimBinderCatalog,
            ));
        }
        keys.define(&binder.declaration_key, declaration_role)?;
        keys.define(&binder.name_key, ProvenanceRole::ClaimBinderName)?;
        keys.define(S::sort_key(&binder.sort), ProvenanceRole::ClaimBinderSort)?;
        S::validate_sort(&binder.sort).map_err(|_| {
            StateTransportError::InvalidTerm(StateTermReason::InvalidClaimBinderSort)
        })?;
    }
    Ok(())
}

fn validate_rule_cells<S: RuleValidationStage>(
    cells: &ProtocolRuleCells<S::Cell, Term<S>>,
    owner: &S::Configuration,
    side: RuleSide,
    bindings: &[ProtocolRuleBinding<S::Sort>],
    discovered: &mut Vec<String>,
    walk: &mut RuleWalk,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    keys.define(&cells.key, RuleRole::CellsPayload.on_side(side))?;
    let mut selected = BTreeSet::new();
    for cell in &cells.cells {
        S::validate_rule_cell(&cell.field, owner)?;
        if !selected.insert(S::rule_cell_identity(&cell.field)) {
            return Err(StateTransportError::DuplicateValue(
                TransportField::SelectedRuleCells,
            ));
        }
        // The value's structure is keyed here, which refuses a shell
        // without its payload key; its terms are keyed by its validation
        // below.
        collect_cell_keys::<S, StateTransportError>(cell, side, keys, &mut |_, _| Ok(()))?;
        validate_rule_wrapper(cell.wrapper, &cell.value)?;
        validate_rule_state::<S>(&cell.value, side, bindings, discovered, walk, keys)?;
    }
    if let Some(key) = frame_key(&cells.remainder) {
        keys.define(key, RuleRole::CellsRemainder.on_side(side))?;
    }
    validate_frame(
        &cells.remainder,
        side,
        bindings,
        RuleBindingUse::ConfigurationFrame,
        discovered,
    )
}

fn validate_rule_wrapper<T>(
    wrapper: Option<CellWrapper>,
    value: &ProtocolRuleStateTerm<T>,
) -> Result<(), StateTransportError> {
    match (wrapper, value) {
        (_, ProtocolRuleStateTerm::Present { value }) => {
            if matches!(
                **value,
                ProtocolRuleStateTerm::Present { .. }
                    | ProtocolRuleStateTerm::Absent
                    | ProtocolRuleStateTerm::Instances(_)
            ) {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::InvalidOptionalCellEntry,
                ));
            }
            validate_rule_wrapper(wrapper, value)
        }
        (Some(CellWrapper::KCell), ProtocolRuleStateTerm::KSequence(_))
        | (
            Some(CellWrapper::Cell),
            ProtocolRuleStateTerm::Term(_) | ProtocolRuleStateTerm::Map(_),
        )
        | (
            None,
            ProtocolRuleStateTerm::Group(_)
            | ProtocolRuleStateTerm::Absent
            | ProtocolRuleStateTerm::Instances(_),
        ) => Ok(()),
        _ => Err(StateTransportError::InvalidCellContent(
            StateCellContentReason::RuleWrapperAndStateFamilyDisagree,
        )),
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "State validation follows the three ordered protocol families."
)]
fn validate_rule_state<S: RuleValidationStage>(
    state: &ProtocolRuleStateTerm<Term<S>>,
    side: RuleSide,
    bindings: &[ProtocolRuleBinding<S::Sort>],
    discovered: &mut Vec<String>,
    walk: &mut RuleWalk,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    match state {
        ProtocolRuleStateTerm::Term(term) => {
            validate_rule_term::<S>(term, side.into(), bindings, discovered, walk, keys)
        }
        ProtocolRuleStateTerm::Present { value } => {
            validate_rule_state::<S>(value, side, bindings, discovered, walk, keys)
        }
        ProtocolRuleStateTerm::Absent => Ok(()),
        ProtocolRuleStateTerm::Instances(instances) => {
            validate_rule_instances::<S>(instances, side, bindings, discovered, walk, keys)
        }
        ProtocolRuleStateTerm::Group(term) => {
            if !matches!(
                term,
                Term::Variable { .. } | Term::Wildcard { .. } | Term::Cell { .. }
            ) {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::InvalidGroupCellEntry,
                ));
            }
            validate_rule_term::<S>(term, side.into(), bindings, discovered, walk, keys)
        }
        ProtocolRuleStateTerm::KSequence(sequence) => {
            validate_k_shell(sequence)?;
            for item in &sequence.items {
                walk.k_item_root = true;
                let validated = validate_rule_term::<S>(
                    &item.value,
                    side.into(),
                    bindings,
                    discovered,
                    walk,
                    keys,
                );
                walk.k_item_root = false;
                validated?;
            }
            if sequence.notation == DescriptorKSequenceNotation::DotK {
                Ok(())
            } else {
                validate_frame(
                    &sequence.tail,
                    side,
                    bindings,
                    RuleBindingUse::KSequenceFrame,
                    discovered,
                )
            }
        }
        ProtocolRuleStateTerm::Map(map) => {
            validate_map_shell(map, side)?;
            match &map.body {
                ProtocolRuleMapBody::Empty { .. } => Ok(()),
                ProtocolRuleMapBody::Items { items, remainder } => {
                    for item in items {
                        // A map rewrite changes a value; it never adds or
                        // removes an entry (KF-011).
                        if super::validation::contains_rewrite(&item.key) {
                            return Err(StateTransportError::InvalidTerm(
                                StateTermReason::RewriteOutsideSingleBodyRule,
                            ));
                        }
                        validate_rule_term::<S>(
                            &item.key,
                            side.into(),
                            bindings,
                            discovered,
                            walk,
                            keys,
                        )?;
                        validate_rule_term::<S>(
                            &item.value,
                            side.into(),
                            bindings,
                            discovered,
                            walk,
                            keys,
                        )?;
                    }
                    validate_frame(
                        remainder,
                        side,
                        bindings,
                        RuleBindingUse::MapFrame,
                        discovered,
                    )
                }
                ProtocolRuleMapBody::Update {
                    base, key, value, ..
                } => {
                    for term in [base, key, value] {
                        validate_rule_term::<S>(
                            term,
                            side.into(),
                            bindings,
                            discovered,
                            walk,
                            keys,
                        )?;
                    }
                    Ok(())
                }
            }
        }
    }
}

/// Validates a collection entry (KF-023): instance keys, child keys, labels
/// on the subject only, `..label` on the result only, children named once,
/// back instances only after the rest of a bracketed list, and the rest.
fn validate_rule_instances<S: RuleValidationStage>(
    instances: &ProtocolRuleInstances<Term<S>>,
    side: RuleSide,
    bindings: &[ProtocolRuleBinding<S::Sort>],
    discovered: &mut Vec<String>,
    walk: &mut RuleWalk,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    let invalid =
        || StateTransportError::InvalidCellContent(StateCellContentReason::InvalidInstanceEntry);
    if !instances.back.is_empty()
        && (instances.delimiter != InstanceDelimiter::Bracket
            || matches!(instances.rest, ProtocolRuleFrame::Exact))
    {
        return Err(invalid());
    }
    let validate_instance = |instance: &ProtocolRuleInstance<Term<S>>,
                             discovered: &mut Vec<String>,
                             walk: &mut RuleWalk,
                             keys: &mut WireKeys|
     -> Result<(), StateTransportError> {
        let rest_valid = match (&instance.rest, side) {
            (ProtocolInstanceRest::Update { label }, RuleSide::Right) => !label.is_empty(),
            (ProtocolInstanceRest::Update { .. }, RuleSide::Left) => false,
            (ProtocolInstanceRest::Exact | ProtocolInstanceRest::Open, _) => true,
        };
        if !rest_valid
            || (side == RuleSide::Right && instance.label.is_some())
            || instance.label.as_ref().is_some_and(String::is_empty)
        {
            return Err(invalid());
        }
        let mut names = BTreeSet::new();
        for field in &instance.fields {
            if field.field.is_empty() || !names.insert(field.field.as_str()) {
                return Err(invalid());
            }
            if matches!(
                field.value,
                ProtocolRuleStateTerm::Present { .. }
                    | ProtocolRuleStateTerm::Absent
                    | ProtocolRuleStateTerm::Instances(_)
            ) {
                return Err(invalid());
            }
            validate_rule_state::<S>(&field.value, side, bindings, discovered, walk, keys)?;
        }
        Ok(())
    };
    for instance in &instances.front {
        validate_instance(instance, discovered, walk, keys)?;
    }
    if !(side == RuleSide::Right && matches!(instances.rest, ProtocolRuleFrame::Anonymous { .. })) {
        validate_frame(
            &instances.rest,
            side,
            bindings,
            RuleBindingUse::InstancesFrame,
            discovered,
        )?;
    }
    for instance in &instances.back {
        validate_instance(instance, discovered, walk, keys)?;
    }
    Ok(())
}

fn validate_k_shell<T>(sequence: &ProtocolRuleKSequence<T>) -> Result<(), StateTransportError> {
    match sequence.notation {
        DescriptorKSequenceNotation::DotK => {
            if !sequence.items.is_empty() || !matches!(sequence.tail, ProtocolRuleFrame::Exact) {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::InvalidStandaloneDotKShell,
                ));
            }
            if sequence.dot_k_key.is_none() {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::DotKMissingProvenance,
                ));
            }
        }
        DescriptorKSequenceNotation::Comma | DescriptorKSequenceNotation::Operator => {
            if sequence.dot_k_key.is_some()
                || (sequence.notation == DescriptorKSequenceNotation::Operator
                    && sequence.items.len() < 2)
            {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::InvalidKSequenceShell,
                ));
            }
        }
    }
    Ok(())
}

fn validate_map_shell<T>(
    map: &ProtocolRuleMap<T>,
    side: RuleSide,
) -> Result<(), StateTransportError> {
    match &map.body {
        ProtocolRuleMapBody::Empty { .. } => {}
        ProtocolRuleMapBody::Items { items, remainder } => {
            if items.is_empty() && matches!(remainder, ProtocolRuleFrame::Exact) {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::MapItemsWithoutContent,
                ));
            }
        }
        ProtocolRuleMapBody::Update { .. } => {
            if matches!(side, RuleSide::Left) {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::MapUpdateOnLeftSide,
                ));
            }
        }
    }
    Ok(())
}

struct RuleTermValidation<'a, S: ValidationStage> {
    side: ValidationSide,
    bindings: &'a [ProtocolRuleBinding<S::Sort>],
    discovered: &'a mut Vec<String>,
    walk: &'a mut RuleWalk,
    keys: &'a mut WireKeys,
    /// The names bound by the enclosing `let` statements, innermost last.
    let_scopes: Vec<BTreeSet<String>>,
}

fn validate_rule_term<S: ValidationStage>(
    term: &Term<S>,
    side: ValidationSide,
    bindings: &[ProtocolRuleBinding<S::Sort>],
    discovered: &mut Vec<String>,
    walk: &mut RuleWalk,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    // `k::rewrite!(x => ())` removes a whole K-sequence item (KF-011).
    if super::validation::misplaced_empty_rewrite(term, walk.k_item_root) {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::EmptyRewriteOutsideKSequence,
        ));
    }
    validate_term(
        term,
        &mut RuleTermValidation {
            side,
            bindings,
            discovered,
            walk,
            keys,
            let_scopes: Vec::new(),
        },
    )
}

impl<S: ValidationStage> TermValidation<S> for RuleTermValidation<'_, S> {
    type Error = StateTransportError;

    fn variable(
        &mut self,
        key: &ProvenanceKey,
        path_key: &ProvenanceKey,
        name: &str,
    ) -> Result<(), Self::Error> {
        // A name in a `k::matches!` or `let` pattern, or bound by an
        // enclosing `let`, is a local binder (BIND-1), not a rule binding;
        // semantic lowering scopes it.
        let local = self.walk.in_matches_pattern
            || self.walk.in_let_pattern
            || self.let_scopes.iter().any(|scope| scope.contains(name));
        // A result or a condition sees every variable the left side binds,
        // the computation and map remainders included.
        let uses = !matches!(self.side, ValidationSide::Left);
        if !local
            && !binding_has_kind(self.bindings, name, RuleBindingUse::Term)
            && !(uses
                && (binding_has_kind(self.bindings, name, RuleBindingUse::KSequenceFrame)
                    || binding_has_kind(self.bindings, name, RuleBindingUse::MapFrame)))
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::RuleVariableBindingIsNotATerm,
            ));
        }
        validate_term_path_key(self.keys, path_key, key, self.side)?;
        self.keys
            .define(key, TermRole::Reference.on_side(self.side))?;
        // The right side of a `k::rewrite!` uses the subject's bindings; the
        // binding order is the left image's.
        if !local && !self.walk.in_rewrite_right {
            discover_binding(self.side, name, self.discovered);
        }
        Ok(())
    }

    fn application(
        &mut self,
        head_class: DescriptorApplicationHeadClass,
        reference: &S::Application,
        path_key: &ProvenanceKey,
        arguments: &crate::Arguments<S>,
    ) -> Result<(), Self::Error> {
        if head_class == DescriptorApplicationHeadClass::BareReference && !arguments.is_empty() {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::InvalidRuleApplicationKeysOrHeadClass,
            ));
        }
        let key = S::application_key(reference);
        validate_term_path_key(self.keys, path_key, key, self.side)?;
        S::validate_application(reference).map_err(|_| {
            StateTransportError::InvalidTerm(StateTermReason::InvalidApplicationTarget)
        })?;
        let role = match head_class {
            DescriptorApplicationHeadClass::Applied => TermRole::ApplicationHead,
            DescriptorApplicationHeadClass::BareReference => TermRole::Reference,
        };
        self.keys.define(key, role.on_side(self.side))?;
        Ok(())
    }

    fn literal(
        &mut self,
        key: &ProvenanceKey,
        literal: &crate::DescriptorLiteral,
    ) -> Result<(), Self::Error> {
        self.keys
            .define(key, TermRole::Literal.on_side(self.side))?;
        literal.validate().map_err(|_| {
            StateTransportError::InvalidTerm(StateTermReason::NonCanonicalIntegerLiteral)
        })
    }

    fn wildcard(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        if self.walk.in_let_pattern {
            self.keys.define(key, ProvenanceRole::LetWildcard)?;
            return Ok(());
        }
        if self.walk.in_matches_pattern {
            self.keys.define(key, ProvenanceRole::MatchesWildcard)?;
            return Ok(());
        }
        if !matches!(self.side, ValidationSide::Left) || self.walk.in_rewrite_right {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::WildcardsAreAllowedOnlyInRuleSubjects,
            ));
        }
        self.keys.define(key, ProvenanceRole::RuleLeftWildcard)?;
        Ok(())
    }

    fn builtin_token(
        &mut self,
        key: &ProvenanceKey,
        sort: crate::BuiltinSort,
        value: &str,
    ) -> Result<(), Self::Error> {
        self.keys.define(key, builtin_token_role(sort, value)?)?;
        Ok(())
    }

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

    fn pattern_as(
        &mut self,
        key: &ProvenanceKey,
        binding_key: &ProvenanceKey,
        name: &str,
    ) -> Result<(), Self::Error> {
        let local = self.walk.in_matches_pattern;
        if self.walk.in_let_pattern || (!local && !matches!(self.side, ValidationSide::Left)) {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::PatternAsOutsideLeftHandSide,
            ));
        }
        if !local && !binding_has_kind(self.bindings, name, RuleBindingUse::Term) {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::RuleVariableBindingIsNotATerm,
            ));
        }
        self.keys.define(key, ProvenanceRole::PatternAs)?;
        self.keys
            .define(binding_key, ProvenanceRole::PatternAsBinding)?;
        if !local {
            discover_binding(self.side, name, self.discovered);
        }
        Ok(())
    }

    fn matches(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        if matches!(self.side, ValidationSide::Left)
            || self.walk.in_matches_pattern
            || self.walk.in_let_pattern
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::MatchesInPattern,
            ));
        }
        self.keys.define(key, ProvenanceRole::Matches)?;
        Ok(())
    }

    fn matches_pattern(&mut self, inside: bool) {
        self.walk.in_matches_pattern = inside;
    }

    fn let_binding(
        &mut self,
        key: &ProvenanceKey,
        sort: Option<&S::Sort>,
    ) -> Result<(), Self::Error> {
        if matches!(self.side, ValidationSide::Left)
            || self.walk.in_matches_pattern
            || self.walk.in_let_pattern
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::LetInPattern,
            ));
        }
        if let Some(sort) = sort {
            S::validate_sort(sort).map_err(|_| {
                StateTransportError::InvalidTerm(StateTermReason::InvalidSortTestSort)
            })?;
            self.keys
                .define(S::sort_key(sort), ProvenanceRole::LetSort)?;
        }
        self.keys.define(key, ProvenanceRole::Let)?;
        Ok(())
    }

    fn let_pattern(&mut self, inside: bool) {
        self.walk.in_let_pattern = inside;
    }

    fn closure(
        &mut self,
        key: &ProvenanceKey,
        binder_key: &ProvenanceKey,
        sort: &S::Sort,
    ) -> Result<(), Self::Error> {
        if matches!(self.side, ValidationSide::Left)
            || self.walk.in_matches_pattern
            || self.walk.in_let_pattern
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::ClosureInPattern,
            ));
        }
        S::validate_sort(sort)
            .map_err(|_| StateTransportError::InvalidTerm(StateTermReason::InvalidSortTestSort))?;
        self.keys.define(key, ProvenanceRole::MlConnective)?;
        self.keys.define(binder_key, ProvenanceRole::MlBinder)?;
        self.keys
            .define(S::sort_key(sort), ProvenanceRole::MlBinderSort)?;
        Ok(())
    }

    fn let_body(&mut self, names: Option<&BTreeSet<String>>) {
        match names {
            Some(names) => self.let_scopes.push(names.clone()),
            None => {
                self.let_scopes.pop();
            }
        }
    }

    fn rewrite(
        &mut self,
        key: &ProvenanceKey,
        from_key: &ProvenanceKey,
        to_key: &ProvenanceKey,
        nested: bool,
    ) -> Result<(), Self::Error> {
        if !self.walk.allow_rewrite
            || !matches!(self.side, ValidationSide::Left)
            || self.walk.in_matches_pattern
            || self.walk.in_let_pattern
            || !self.let_scopes.is_empty()
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::RewriteOutsideSingleBodyRule,
            ));
        }
        if nested || self.walk.in_rewrite_right {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::NestedRewrite,
            ));
        }
        for (actual, role) in [
            (key, ProvenanceRole::RuleLocalRewrite),
            (from_key, ProvenanceRole::RuleLocalRewriteFrom),
            (to_key, ProvenanceRole::RuleLocalRewriteTo),
        ] {
            self.keys.define(actual, role)?;
        }
        self.walk.rewrites += 1;
        Ok(())
    }

    fn rewrite_right(&mut self, inside: bool) {
        self.walk.in_rewrite_right = inside;
    }

    fn pattern_or(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        if self.walk.in_let_pattern
            || (!matches!(self.side, ValidationSide::Left) && !self.walk.in_matches_pattern)
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::PatternOrOutsideLeftHandSide,
            ));
        }
        self.keys.define(key, ProvenanceRole::PatternOr)?;
        Ok(())
    }

    fn sort_test(
        &mut self,
        key: &ProvenanceKey,
        _: crate::SortTestKind,
        sort: &S::Sort,
    ) -> Result<(), Self::Error> {
        S::validate_sort(sort)
            .map_err(|_| StateTransportError::InvalidTerm(StateTermReason::InvalidSortTestSort))?;
        self.keys
            .define(S::sort_key(sort), ProvenanceRole::SortTestSort)?;
        self.keys.define(key, ProvenanceRole::SortTest)?;
        Ok(())
    }

    fn application_instance(&mut self, sort: &S::Sort) -> Result<(), Self::Error> {
        S::validate_sort(sort)
            .map_err(|_| StateTransportError::InvalidTerm(StateTermReason::InvalidSortTestSort))?;
        self.keys
            .define(S::sort_key(sort), ProvenanceRole::ApplicationInstance)?;
        Ok(())
    }

    fn anonymous(
        &mut self,
        key: &ProvenanceKey,
        sort: &S::Sort,
        spelling_key: &ProvenanceKey,
        spelling: &str,
    ) -> Result<(), Self::Error> {
        if !matches!(self.side, ValidationSide::Left) || !spelling.starts_with('_') {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::UnexpectedAnonymousOccurrence,
            ));
        }
        S::validate_sort(sort)
            .map_err(|_| StateTransportError::InvalidTerm(StateTermReason::InvalidAnonymousSort))?;
        self.keys.define(key, ProvenanceRole::ClaimAnonymous)?;
        self.keys
            .define(S::sort_key(sort), ProvenanceRole::ClaimAnonymousSort)?;
        self.keys
            .define(spelling_key, ProvenanceRole::ClaimAnonymousSpelling)?;
        Ok(())
    }

    fn or_bool(
        &mut self,
        key: &ProvenanceKey,
        _arguments: &crate::AtLeastTwo<Term<S>>,
    ) -> Result<(), Self::Error> {
        self.keys.define(key, ProvenanceRole::ClaimOrBool)?;
        Ok(())
    }

    fn cell(
        &mut self,
        key: &ProvenanceKey,
        path_key: &ProvenanceKey,
        declaration: &S::Nominal,
        fields: &[CellTermField<S>],
        partial: bool,
    ) -> Result<(), Self::Error> {
        S::validate_fragment(declaration, fields.is_empty() && !partial)?;
        // The fragment's path is keyed as an application's.
        validate_term_path_key(self.keys, path_key, key, self.side)?;
        self.keys
            .define(key, TermRole::ApplicationHead.on_side(self.side))?;
        Ok(())
    }

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
                    .define(key, TermRole::RecordFieldName.on_side(self.side))?;
                Ok(())
            }
        }
    }

    fn cell_field(
        &mut self,
        field: &CellTermField<S>,
        names: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        if !names.insert(field.field.clone()) {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::DuplicateFragmentChildField,
            ));
        }
        self.keys
            .define(&field.key, TermRole::RecordFieldName.on_side(self.side))?;
        Ok(())
    }

    fn record_update(&mut self, base: &Term<S>) -> Result<(), Self::Error> {
        match base {
            Term::Variable {
                key,
                path_key,
                name,
            } if !matches!(self.side, ValidationSide::Left) => self.variable(key, path_key, name),
            _ => Err(StateTransportError::InvalidTerm(
                StateTermReason::RecordUpdateBase,
            )),
        }
    }
}

/// The path role of a condition's terms, which key their paths; a cell
/// value's terms key none, and a path there names its head's node.
const fn condition_path_role(side: ValidationSide) -> Option<ProvenanceRole> {
    match side {
        ValidationSide::Requires | ValidationSide::Ensures | ValidationSide::RuleEnsures => {
            Some(TermRole::Path.on_side(side))
        }
        ValidationSide::Left | ValidationSide::Right => None,
    }
}

fn validate_term_path_key(
    keys: &mut WireKeys,
    path_key: &ProvenanceKey,
    semantic_key: &ProvenanceKey,
    side: ValidationSide,
) -> Result<(), StateTransportError> {
    if let Some(role) = condition_path_role(side) {
        keys.define(path_key, role)?;
    } else if path_key != semantic_key {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::RuleTermKeyMismatch,
        ));
    }
    Ok(())
}

fn validate_frame<S>(
    frame: &ProtocolRuleFrame,
    side: RuleSide,
    bindings: &[ProtocolRuleBinding<S>],
    binding_kind: RuleBindingUse,
    discovered: &mut Vec<String>,
) -> Result<(), StateTransportError> {
    match (side, frame) {
        (_, ProtocolRuleFrame::Exact) | (RuleSide::Left, ProtocolRuleFrame::Anonymous { .. }) => {
            Ok(())
        }
        (RuleSide::Left, ProtocolRuleFrame::Bind { binding, .. }) => {
            if !binding_has_kind(bindings, binding, binding_kind) {
                return Err(StateTransportError::InvalidTerm(
                    StateTermReason::SubjectFrameBindingKind,
                ));
            }
            discover_binding(side.into(), binding, discovered);
            Ok(())
        }
        (RuleSide::Right, ProtocolRuleFrame::Reuse { binding, .. }) => {
            // A result map's rest may also name a map the subject binds whole
            // (`map![k -> v, ..m]` over `Cell(m)`): the entries are written over it.
            let whole_map = binding_kind == RuleBindingUse::MapFrame
                && binding_has_kind(bindings, binding, RuleBindingUse::Term);
            if !whole_map && !binding_has_kind(bindings, binding, binding_kind) {
                return Err(StateTransportError::InvalidTerm(
                    StateTermReason::ResultFrameBindingKind,
                ));
            }
            Ok(())
        }
        (RuleSide::Left, ProtocolRuleFrame::Reuse { .. })
        | (RuleSide::Right, ProtocolRuleFrame::Anonymous { .. } | ProtocolRuleFrame::Bind { .. }) => {
            Err(StateTransportError::InvalidTerm(
                StateTermReason::FrameFormIsInvalidOnThisRuleSide,
            ))
        }
    }
}

fn discover_binding(side: ValidationSide, binding: &str, discovered: &mut Vec<String>) {
    if matches!(side, ValidationSide::Left)
        && !discovered.iter().any(|candidate| candidate == binding)
    {
        discovered.push(binding.to_owned());
    }
}

fn validate_binding_catalog_names<S>(
    bindings: &[ProtocolRuleBinding<S>],
) -> Result<(), StateTransportError> {
    let unique = bindings
        .iter()
        .map(|binding| &binding.name)
        .collect::<BTreeSet<_>>();
    if unique.len() != bindings.len()
        || bindings
            .iter()
            .any(|binding| binding.name.trim().is_empty())
    {
        Err(StateTransportError::DuplicateValue(
            TransportField::RuleBindings,
        ))
    } else {
        Ok(())
    }
}

fn validate_rule_binding_catalog<S: RuleValidationStage>(
    bindings: &[ProtocolRuleBinding<S::Sort>],
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    validate_binding_catalog_names(bindings)?;
    for binding in bindings {
        if let ProtocolRuleBindingKind::Term { sort } = &binding.kind {
            keys.define(S::sort_key(sort), ProvenanceRole::RuleBindingType)?;
            S::validate_binding_sort(sort)?;
        }
    }
    Ok(())
}

fn binding_kind<S>(kind: &ProtocolRuleBindingKind<S>) -> RuleBindingUse {
    match kind {
        ProtocolRuleBindingKind::Term { .. } => RuleBindingUse::Term,
        ProtocolRuleBindingKind::KSequenceFrame => RuleBindingUse::KSequenceFrame,
        ProtocolRuleBindingKind::MapFrame => RuleBindingUse::MapFrame,
        ProtocolRuleBindingKind::ConfigurationFrame => RuleBindingUse::ConfigurationFrame,
        ProtocolRuleBindingKind::InstancesFrame => RuleBindingUse::InstancesFrame,
    }
}

fn binding_has_kind<S>(
    bindings: &[ProtocolRuleBinding<S>],
    name: &str,
    expected: RuleBindingUse,
) -> bool {
    bindings
        .iter()
        .find(|binding| binding.name == name)
        .is_some_and(|binding| binding_kind(&binding.kind) == expected)
}

fn binding_names_match<S>(bindings: &[ProtocolRuleBinding<S>], discovered: &[String]) -> bool {
    bindings
        .iter()
        .map(|binding| binding.name.as_str())
        .eq(discovered.iter().map(String::as_str))
}

fn validate_sentence_kind(
    sentence_kind: crate::ConfigurationSentenceKind,
    actual: ItemKind,
) -> Result<(), StateTransportError> {
    let expected = sentence_kind.item_kind();
    if actual == expected {
        Ok(())
    } else {
        Err(StateTransportError::ItemKind {
            field: TransportField::ConfigurationRuleDescriptor,
            expected: match sentence_kind {
                crate::ConfigurationSentenceKind::Transition => TransportItemKind::Rule,
                crate::ConfigurationSentenceKind::Equation => TransportItemKind::Equation,
                crate::ConfigurationSentenceKind::Claim => TransportItemKind::Claim,
                crate::ConfigurationSentenceKind::Context => TransportItemKind::Context,
            },
            actual,
        })
    }
}

#[cfg(test)]
mod bytes_token_tests {
    use super::{StateTermReason, builtin_token_role};
    use crate::{BuiltinSort, ProvenanceRole, StateTransportError};
    use krs_test_support::assert_rejects;

    #[test]
    fn builtin_bytes_tokens_accept_only_the_canonical_codec() {
        let role = builtin_token_role(BuiltinSort::Bytes, r#"b"\x00\x7f\xff""#).unwrap();
        assert_eq!(role, ProvenanceRole::ClaimBytesToken);

        for malformed in [r#""\x00""#, r#"b"\x0""#, r#"b"\xAF""#, r#"b"\x+1""#] {
            assert_rejects!(
                builtin_token_role(BuiltinSort::Bytes, malformed),
                StateTransportError::InvalidTerm(StateTermReason::InvalidCompilerOwnedBuiltinToken)
            );
        }
    }
}

#[cfg(test)]
#[path = "rule_validation_tests.rs"]
mod validation_tests;

//! Collector transport for whole-configuration rules, claims, and context aliases.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use super::detail::{StateCellContentReason, StateTermReason, TransportField, TransportItemKind};
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
    ItemKind, ProductionFieldId, ProvenanceKey, ProvenanceRole, RuleRole, RuleSide, SentenceKind,
    StableItemId,
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
        /// Complete payload provenance.
        /// Empty `k![]` alone has no inner endpoint.
        pub payload_key: Option<ProvenanceKey> => [keep],
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
        /// Complete map payload provenance.
        /// Empty `map![]` has no inner endpoint.
        pub payload_key: Option<ProvenanceKey> => [keep],
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
    /// The context's parser-owned keys: the parameter, the configuration
    /// type, and every cell, frame, and term key.
    pub(crate) fn collect_keys(&self, keys: &mut BTreeSet<ProvenanceKey>) {
        keys.insert(self.key.clone());
        keys.insert(self.configuration.key.clone());
        keys.insert(self.cells.key.clone());
        for binding in &self.bindings {
            if let ProtocolRuleBindingKind::Term { sort } = &binding.kind {
                keys.insert(sort.key.clone());
            }
        }
        collect_cells_keys(&self.cells, keys);
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
    #[must_use]
    pub fn expected_provenance_keys(&self) -> BTreeSet<ProvenanceKey> {
        let mut keys = BTreeSet::from([
            self.declaration_key.clone(),
            self.name_key.clone(),
            self.here_key.clone(),
            self.pattern_key.clone(),
            self.configuration.key.clone(),
            self.pattern.key.clone(),
        ]);
        for binding in &self.bindings {
            if let ProtocolContextAliasBindingKind::Term { sort } = &binding.kind {
                keys.insert(sort.key.clone());
            }
        }
        collect_cells_keys(&self.pattern, &mut keys);
        keys
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
        let expected = self.expected_provenance_keys();
        if expected != *actual {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::AliasProvenanceNotClosed,
            ));
        }
        Ok(())
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
        match &cell.value {
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

fn collect_cells_keys<I>(
    cells: &ProtocolRuleCells<I, DescriptorTerm>,
    keys: &mut BTreeSet<ProvenanceKey>,
) where
    I: CellKeyAccess,
{
    if let Some(key) = frame_key(&cells.remainder) {
        keys.insert(key.clone());
    }
    for cell in &cells.cells {
        keys.insert(cell.field.cell_key().clone());
        keys.extend(cell.wrapper_key.iter().cloned());
        collect_state_keys(&cell.value, keys);
    }
}

trait CellKeyAccess {
    fn cell_key(&self) -> &ProvenanceKey;
}
impl CellKeyAccess for DescriptorCellReference {
    fn cell_key(&self) -> &ProvenanceKey {
        &self.key
    }
}

fn frame_key(frame: &ProtocolRuleFrame) -> Option<&ProvenanceKey> {
    match frame {
        ProtocolRuleFrame::Exact => None,
        ProtocolRuleFrame::Anonymous { key }
        | ProtocolRuleFrame::Bind { key, .. }
        | ProtocolRuleFrame::Reuse { key, .. } => Some(key),
    }
}

fn collect_state_keys(
    state: &ProtocolRuleStateTerm<DescriptorTerm>,
    keys: &mut BTreeSet<ProvenanceKey>,
) {
    match state {
        ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
            collect_term_keys(term, keys);
        }
        ProtocolRuleStateTerm::KSequence(sequence) => {
            keys.extend(sequence.payload_key.iter().cloned());
            keys.extend(sequence.dot_k_key.iter().cloned());
            if let Some(key) = frame_key(&sequence.tail) {
                keys.insert(key.clone());
            }
            for item in &sequence.items {
                keys.insert(item.key.clone());
                collect_term_keys(&item.value, keys);
            }
        }
        ProtocolRuleStateTerm::Map(map) => {
            keys.extend(map.payload_key.iter().cloned());
            match &map.body {
                ProtocolRuleMapBody::Empty { .. } => {}
                ProtocolRuleMapBody::Items { items, remainder } => {
                    if let Some(key) = frame_key(remainder) {
                        keys.insert(key.clone());
                    }
                    for item in items {
                        keys.insert(item.key_key.clone());
                        keys.insert(item.value_key.clone());
                        collect_term_keys(&item.key, keys);
                        collect_term_keys(&item.value, keys);
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
                    keys.extend([base_key.clone(), key_key.clone(), value_key.clone()]);
                    collect_term_keys(base, keys);
                    collect_term_keys(key, keys);
                    collect_term_keys(value, keys);
                }
            }
        }
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "Exhaustive key collection over the closed descriptor term sum."
)]
fn collect_term_keys(term: &DescriptorTerm, keys: &mut BTreeSet<ProvenanceKey>) {
    match term {
        DescriptorTerm::Variable { key, path_key, .. } => {
            keys.extend([key.clone(), path_key.clone()]);
        }
        DescriptorTerm::Application {
            reference,
            path_key,
            arguments,
            ..
        } => {
            keys.extend([reference.key.clone(), path_key.clone()]);
            for argument in arguments {
                match argument {
                    crate::TermArgumentRef::Positional { value } => collect_term_keys(value, keys),
                    crate::TermArgumentRef::Named { key, value, .. } => {
                        keys.insert(key.clone());
                        collect_term_keys(value, keys);
                    }
                }
            }
        }
        DescriptorTerm::Literal { key, .. }
        | DescriptorTerm::Wildcard { key }
        | DescriptorTerm::BuiltinToken { key, .. } => {
            keys.insert(key.clone());
        }
        DescriptorTerm::Anonymous { key, sort, .. } | DescriptorTerm::Lexeme { key, sort, .. } => {
            keys.extend([key.clone(), sort.key.clone()]);
        }
        DescriptorTerm::OrBool { key, arguments } => {
            keys.insert(key.clone());
            for argument in arguments.iter() {
                collect_term_keys(argument, keys);
            }
        }
        DescriptorTerm::Cell { key, fields, .. } => {
            keys.insert(key.clone());
            for field in fields {
                keys.insert(field.key.clone());
                collect_term_keys(&field.value, keys);
            }
        }
        DescriptorTerm::SortTest {
            key, sort, operand, ..
        } => {
            keys.extend([key.clone(), sort.key.clone()]);
            collect_term_keys(operand, keys);
        }
        DescriptorTerm::As {
            key,
            binding_key,
            pattern,
            ..
        } => {
            keys.extend([key.clone(), binding_key.clone()]);
            collect_term_keys(pattern, keys);
        }
        DescriptorTerm::Or { key, alternatives } => {
            keys.insert(key.clone());
            for alternative in alternatives.iter() {
                collect_term_keys(alternative, keys);
            }
        }
        DescriptorTerm::Matches {
            key,
            subject,
            pattern,
        } => {
            keys.insert(key.clone());
            collect_term_keys(subject, keys);
            collect_term_keys(pattern, keys);
        }
        DescriptorTerm::Rewrite {
            key,
            from_key,
            to_key,
            from,
            to,
        } => {
            keys.extend([key.clone(), from_key.clone(), to_key.clone()]);
            collect_term_keys(from, keys);
            if let Some(to) = to {
                collect_term_keys(to, keys);
            }
        }
        DescriptorTerm::Let {
            key,
            pattern,
            sort,
            value,
            body,
        } => {
            keys.insert(key.clone());
            if let Some(sort) = sort {
                keys.insert(sort.key.clone());
            }
            collect_term_keys(pattern, keys);
            collect_term_keys(value, keys);
            collect_term_keys(body, keys);
        }
        DescriptorTerm::Closure {
            key,
            binder_key,
            sort,
            body,
            ..
        } => {
            keys.extend([key.clone(), binder_key.clone(), sort.key.clone()]);
            collect_term_keys(body, keys);
        }
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
    }
}

/// Stable descriptor-stage form of [`ConfigurationRule`].
pub type DescriptorConfigurationRule = ConfigurationRule<DescriptorStage>;

/// Build-local host-stage form of [`ConfigurationRule`].
pub type HostConfigurationRule = ConfigurationRule<HostStage>;

#[derive(Clone, Copy)]
enum ValidationSide {
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
}

fn claim_checked_index(index: usize) -> Result<u32, StateTransportError> {
    u32::try_from(index)
        .map_err(|_| StateTransportError::InvalidTerm(StateTermReason::TooManyClaimNodes))
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
enum TermRole {
    Path,
    ApplicationHead,
    Reference,
    Literal,
    RecordFieldName,
}

impl TermRole {
    const fn on_side(self, side: ValidationSide) -> ProvenanceRole {
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

#[derive(Default)]
#[expect(
    clippy::struct_excessive_bools,
    reason = "Each flag records one independent nesting context of the term walk."
)]
struct RuleCounters {
    path: u32,
    cells_field: u32,
    cells_wrapper: u32,
    cells_remainder: u32,
    k_payload: u32,
    k_item: u32,
    k_tail: u32,
    map_payload: u32,
    map_key: u32,
    map_value: u32,
    map_remainder: u32,
    map_update_base: u32,
    application: u32,
    reference: u32,
    literal: u32,
    record_field: u32,
    wildcard: u32,
    id_token: u32,
    bytes_token: u32,
    anonymous: u32,
    lexeme: u32,
    sort_test: u32,
    application_instance: u32,
    pattern_as: u32,
    pattern_or: u32,
    matches: u32,
    matches_wildcard: u32,
    /// Whether the validator is inside a `k::matches!` pattern.
    in_matches_pattern: bool,
    let_binding: u32,
    let_wildcard: u32,
    /// Whether the validator is inside a `let` pattern.
    in_let_pattern: bool,
    /// `ml::exists` closure ordinals, side-neutral (KF-039).
    ml_binder: u32,
    /// `k::rewrite!` ordinals, side-neutral (KF-011).
    rewrite: u32,
    /// Whether `k::rewrite!` is admitted: the subject of a single-body rule.
    allow_rewrite: bool,
    /// Whether the validator is inside the right side of a `k::rewrite!`.
    in_rewrite_right: bool,
    /// Whether the term being validated is a whole K-sequence item, whose
    /// root rewrite may remove it (`k::rewrite!(x => ())`).
    k_item_root: bool,
}

impl RuleCounters {
    /// The counters of the next side: the side-neutral ordinals continue,
    /// the per-side ones restart.
    fn next_side(&self) -> Self {
        Self {
            id_token: self.id_token,
            bytes_token: self.bytes_token,
            anonymous: self.anonymous,
            lexeme: self.lexeme,
            sort_test: self.sort_test,
            application_instance: self.application_instance,
            pattern_as: self.pattern_as,
            pattern_or: self.pattern_or,
            matches: self.matches,
            matches_wildcard: self.matches_wildcard,
            let_binding: self.let_binding,
            let_wildcard: self.let_wildcard,
            ml_binder: self.ml_binder,
            rewrite: self.rewrite,
            ..Self::default()
        }
    }
}

fn builtin_token_role<'a>(
    sort: crate::BuiltinSort,
    value: &str,
    counters: &'a mut RuleCounters,
) -> Result<(ProvenanceRole, &'a mut u32), StateTransportError> {
    match sort {
        crate::BuiltinSort::Id
            if value.strip_prefix('$').is_some_and(|tail| {
                !tail.is_empty()
                    && tail
                        .chars()
                        .all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
            }) =>
        {
            Ok((ProvenanceRole::ClaimIdToken, &mut counters.id_token))
        }
        crate::BuiltinSort::Bytes if crate::bytes_token::decode(value).is_ok() => {
            Ok((ProvenanceRole::ClaimBytesToken, &mut counters.bytes_token))
        }
        _ => Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidCompilerOwnedBuiltinToken,
        )),
    }
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
    fn insert_rule_label(
        keys: &mut BTreeSet<ProvenanceKey>,
        key: &ProvenanceKey,
        role: ProvenanceRole,
    ) -> Result<(), StateTransportError>;
    /// Descriptor rules synthesize their declaration key; host rules do not collect it.
    fn insert_rule_declaration(keys: &mut BTreeSet<ProvenanceKey>, kind: SentenceKind);
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

    fn insert_rule_label(
        keys: &mut BTreeSet<ProvenanceKey>,
        key: &ProvenanceKey,
        role: ProvenanceRole,
    ) -> Result<(), StateTransportError> {
        insert_rule_exact(keys, key, role, 0)
    }

    fn insert_rule_declaration(keys: &mut BTreeSet<ProvenanceKey>, kind: SentenceKind) {
        keys.insert(ProvenanceKey::new(
            if kind == SentenceKind::Claim {
                ProvenanceRole::ClaimDeclaration
            } else {
                ProvenanceRole::RuleDeclaration
            },
            0,
        ));
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

    fn insert_rule_label(
        _: &mut BTreeSet<ProvenanceKey>,
        key: &ProvenanceKey,
        role: ProvenanceRole,
    ) -> Result<(), StateTransportError> {
        insert_rule_exact(&mut BTreeSet::new(), key, role, 0)
    }

    fn insert_rule_declaration(_: &mut BTreeSet<ProvenanceKey>, _: SentenceKind) {}

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
    /// structured terms, and exact side-specific parser keys.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for any invalid rule shape.
    pub fn validate(&self, descriptor_kind: ItemKind) -> Result<(), StateTransportError> {
        let mut keys = BTreeSet::new();
        self.validate_into(descriptor_kind, &mut keys)
    }

    /// Returns every and only parser key represented by this rule.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::validate`].
    pub fn expected_provenance_keys(
        &self,
        descriptor_kind: ItemKind,
    ) -> Result<BTreeSet<ProvenanceKey>, StateTransportError> {
        let mut keys = BTreeSet::new();
        self.validate_into(descriptor_kind, &mut keys)?;
        Ok(keys)
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
        let expected = self.expected_provenance_keys(descriptor_kind)?;
        validate_rule_complete_set(primary, actual, &expected)
    }

    fn validate_into(
        &self,
        descriptor_kind: ItemKind,
        keys: &mut BTreeSet<ProvenanceKey>,
    ) -> Result<(), StateTransportError> {
        validate_configuration_rule(self, descriptor_kind, keys)
    }
}

impl HostConfigurationRule {
    /// Validates host configuration equality, selected-cell uniqueness, and exact parser keys.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for invalid ownership, frames, terms,
    /// or side-specific provenance roles/ordinals.
    pub fn validate(&self, descriptor_kind: ItemKind) -> Result<(), StateTransportError> {
        validate_configuration_rule(self, descriptor_kind, &mut BTreeSet::new())
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "Rule validation must preserve the ordered provenance pass."
)]
fn validate_configuration_rule<S: RuleValidationStage>(
    rule: &ConfigurationRule<S>,
    descriptor_kind: ItemKind,
    keys: &mut BTreeSet<ProvenanceKey>,
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
        let label_role = if rule.sentence_kind == crate::ConfigurationSentenceKind::Claim {
            ProvenanceRole::ClaimLabel
        } else {
            ProvenanceRole::RuleLabel
        };
        S::insert_rule_label(keys, &label.key, label_role)?;
        if !valid_rule_label_name(&label.name) {
            return Err(StateTransportError::InvalidText(TransportField::RuleLabel));
        }
    }
    if let Some(priority) = &rule.priority {
        let priority_role = priority
            .role_for(crate::SentenceKind::Transition)
            .unwrap_or(ProvenanceRole::RuleOwise);
        insert_rule_exact(keys, &priority.key, priority_role, 0)?;
        if rule.sentence_kind != crate::ConfigurationSentenceKind::Transition
            || priority.role_for(crate::SentenceKind::Transition).is_none()
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::ConfigurationRuleOrderedFallbackPriority,
            ));
        }
    }
    if let Some(nondet) = &rule.nondet {
        insert_rule_exact(keys, &nondet.key, ProvenanceRole::RuleNondetGroup, 0)?;
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
    } else if rule.sentence_kind != crate::ConfigurationSentenceKind::Transition {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::RewriteOutsideSingleBodyRule,
        ));
    }
    insert_rule_exact(keys, &rule.pattern_key, ProvenanceRole::RulePattern, 0)?;
    insert_rule_exact(
        keys,
        S::configuration_key(&rule.subject_configuration),
        ProvenanceRole::RuleType,
        0,
    )?;
    if let Some((result_key, result_configuration, _)) = result {
        insert_rule_exact(keys, result_key, ProvenanceRole::RuleResult, 0)?;
        insert_rule_exact(
            keys,
            S::configuration_key(result_configuration),
            ProvenanceRole::RuleResultType,
            0,
        )?;
    }
    S::insert_rule_declaration(keys, rule.sentence_kind.into());
    validate_rule_binding_catalog::<S>(&rule.bindings, keys)?;

    let mut discovered = Vec::new();
    let mut left_counters = RuleCounters {
        allow_rewrite: result.is_none(),
        ..RuleCounters::default()
    };
    validate_rule_cells::<S>(
        &rule.subject,
        &rule.subject_configuration,
        RuleSide::Left,
        &rule.bindings,
        &mut discovered,
        &mut left_counters,
        keys,
    )?;
    if !binding_names_match(&rule.bindings, &discovered) {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::BindingCatalogOrder,
        ));
    }
    if result.is_none() && left_counters.rewrite == 0 {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::SingleBodyRuleWithoutRewrite,
        ));
    }
    let mut ignored = Vec::new();
    let mut right_counters = left_counters.next_side();
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
            &mut right_counters,
            keys,
        )?;
    }
    let mut claim_counters = right_counters.next_side();
    if let Some(requires) = &rule.requires {
        insert_rule_exact(keys, &requires.key, ProvenanceRole::RuleRequires, 0)?;
        validate_rule_term::<S>(
            &requires.term,
            ValidationSide::Requires,
            &rule.bindings,
            &mut Vec::new(),
            &mut claim_counters,
            keys,
        )?;
    }
    if let Some(claim) = &rule.claim {
        validate_rule_claim::<S>(
            claim,
            &rule.bindings,
            &right_bindings,
            keys,
            &claim_counters,
        )?;
    }
    validate_rule_existentials::<S>(rule, &right_bindings, keys, &claim_counters)?;
    Ok(())
}

/// Checks the result-scoped existentials, the fresh binders, and the ensures condition of a transition.
fn validate_rule_existentials<S: RuleValidationStage>(
    rule: &ConfigurationRule<S>,
    right_bindings: &[ProtocolRuleBinding<S::Sort>],
    keys: &mut BTreeSet<ProvenanceKey>,
    inherited: &RuleCounters,
) -> Result<(), StateTransportError> {
    let mut names = BTreeSet::new();
    for (index, binder) in rule.existentials.iter().enumerate() {
        let ordinal = claim_checked_index(index)?;
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
        insert_rule_exact(
            keys,
            &binder.declaration_key,
            ProvenanceRole::RuleExistentialBinder,
            ordinal,
        )?;
        insert_rule_exact(
            keys,
            &binder.name_key,
            ProvenanceRole::RuleExistentialBinderName,
            ordinal,
        )?;
        insert_rule_exact(
            keys,
            S::sort_key(&binder.sort),
            ProvenanceRole::RuleExistentialBinderSort,
            ordinal,
        )?;
    }
    for (index, binder) in rule.fresh.iter().enumerate() {
        let ordinal = claim_checked_index(index)?;
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
        insert_rule_exact(
            keys,
            &binder.declaration_key,
            ProvenanceRole::RuleFreshBinder,
            ordinal,
        )?;
        insert_rule_exact(
            keys,
            &binder.name_key,
            ProvenanceRole::RuleFreshBinderName,
            ordinal,
        )?;
        insert_rule_exact(
            keys,
            S::sort_key(&binder.sort),
            ProvenanceRole::RuleFreshBinderSort,
            ordinal,
        )?;
    }
    if let Some(ensures) = &rule.ensures {
        insert_rule_exact(keys, &ensures.key, ProvenanceRole::RuleEnsures, 0)?;
        let mut counters = inherited.next_side();
        validate_rule_term::<S>(
            &ensures.term,
            ValidationSide::RuleEnsures,
            right_bindings,
            &mut Vec::new(),
            &mut counters,
            keys,
        )?;
    }
    Ok(())
}

fn validate_rule_claim<S: RuleValidationStage>(
    claim: &Claim<S>,
    left_bindings: &[ProtocolRuleBinding<S::Sort>],
    right_bindings: &[ProtocolRuleBinding<S::Sort>],
    keys: &mut BTreeSet<ProvenanceKey>,
    inherited: &RuleCounters,
) -> Result<(), StateTransportError> {
    insert_rule_exact(
        keys,
        &claim.declaration_key,
        ProvenanceRole::ClaimDeclaration,
        0,
    )?;
    insert_rule_exact(keys, &claim.modality_key, ProvenanceRole::ClaimModality, 0)?;
    if let Some(key) = &claim.circularity_key {
        if claim.modality != ClaimModality::AllPaths {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::CircularityRequiresAnAllPathClaim,
            ));
        }
        insert_rule_exact(keys, key, ProvenanceRole::ClaimCircularity, 0)?;
    }
    if let Some(key) = &claim.trusted_key {
        if claim.circularity_key.is_some() {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::TrustedClaimWithCircularity,
            ));
        }
        insert_rule_exact(keys, key, ProvenanceRole::ClaimTrusted, 0)?;
    }
    validate_rule_claim_binders::<S>(
        &claim.universals,
        left_bindings,
        ProvenanceRole::ClaimUniversalBinder,
        0,
        keys,
    )?;
    validate_rule_claim_binders::<S>(
        &claim.existentials,
        right_bindings,
        ProvenanceRole::ClaimExistentialBinder,
        claim_checked_index(claim.universals.len())?,
        keys,
    )?;
    for (ordinal, key) in claim.or_bool_keys.iter().enumerate() {
        insert_rule_exact(
            keys,
            key,
            ProvenanceRole::ClaimOrBool,
            claim_checked_index(ordinal)?,
        )?;
    }
    if let Some(ensures) = &claim.ensures {
        insert_rule_exact(keys, &ensures.key, ProvenanceRole::ClaimEnsures, 0)?;
        let mut counters = inherited.next_side();
        validate_rule_term::<S>(
            &ensures.term,
            ValidationSide::Ensures,
            right_bindings,
            &mut Vec::new(),
            &mut counters,
            keys,
        )?;
    }
    Ok(())
}

fn validate_rule_claim_binders<S: RuleValidationStage>(
    binders: &[ClaimBinder<S>],
    catalog: &[ProtocolRuleBinding<S::Sort>],
    declaration_role: ProvenanceRole,
    binder_base: u32,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    let mut names = BTreeSet::new();
    for (index, binder) in binders.iter().enumerate() {
        let ordinal = claim_checked_index(index)?;
        if binder.name.trim().is_empty()
            || !names.insert(binder.name.clone())
            || !binding_has_kind(catalog, &binder.name, RuleBindingUse::Term)
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::InvalidClaimBinderCatalog,
            ));
        }
        insert_rule_exact(keys, &binder.declaration_key, declaration_role, ordinal)?;
        let binder_ordinal =
            binder_base
                .checked_add(ordinal)
                .ok_or(StateTransportError::InvalidTerm(
                    StateTermReason::TooManyClaimBinders,
                ))?;
        insert_rule_exact(
            keys,
            &binder.name_key,
            ProvenanceRole::ClaimBinderName,
            binder_ordinal,
        )?;
        insert_rule_exact(
            keys,
            S::sort_key(&binder.sort),
            ProvenanceRole::ClaimBinderSort,
            binder_ordinal,
        )?;
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
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    insert_state_exact(keys, &cells.key, side, RuleRole::CellsPayload, 0)?;
    let mut selected = BTreeSet::new();
    for cell in &cells.cells {
        S::validate_rule_cell(&cell.field, owner)?;
        if !selected.insert(S::rule_cell_identity(&cell.field)) {
            return Err(StateTransportError::DuplicateValue(
                TransportField::SelectedRuleCells,
            ));
        }
        insert_state_exact(
            keys,
            S::rule_cell_key(&cell.field),
            side,
            RuleRole::CellsField,
            counters.cells_field,
        )?;
        counters.cells_field = rule_increment(counters.cells_field)?;
        if let Some(wrapper_key) = &cell.wrapper_key {
            insert_state_exact(
                keys,
                wrapper_key,
                side,
                RuleRole::CellsWrapper,
                counters.cells_wrapper,
            )?;
            counters.cells_wrapper = rule_increment(counters.cells_wrapper)?;
        }
        validate_rule_wrapper(cell.wrapper, &cell.value)?;
        validate_rule_state::<S>(&cell.value, side, bindings, discovered, counters, keys)?;
    }
    validate_frame(
        &cells.remainder,
        side,
        RuleRole::CellsRemainder,
        bindings,
        RuleBindingUse::ConfigurationFrame,
        discovered,
        &mut counters.cells_remainder,
        keys,
    )
}

fn validate_rule_wrapper<T>(
    wrapper: Option<CellWrapper>,
    value: &ProtocolRuleStateTerm<T>,
) -> Result<(), StateTransportError> {
    match (wrapper, value) {
        (Some(CellWrapper::KCell), ProtocolRuleStateTerm::KSequence(_))
        | (
            Some(CellWrapper::Cell),
            ProtocolRuleStateTerm::Term(_) | ProtocolRuleStateTerm::Map(_),
        )
        | (None, ProtocolRuleStateTerm::Group(_)) => Ok(()),
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
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    match state {
        ProtocolRuleStateTerm::Term(term) => {
            validate_rule_term::<S>(term, side.into(), bindings, discovered, counters, keys)
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
            validate_rule_term::<S>(term, side.into(), bindings, discovered, counters, keys)
        }
        ProtocolRuleStateTerm::KSequence(sequence) => {
            validate_k_shell(sequence, side, counters, keys)?;
            for item in &sequence.items {
                insert_state_exact(
                    keys,
                    &item.key,
                    side,
                    RuleRole::KSequenceItem,
                    counters.k_item,
                )?;
                counters.k_item = rule_increment(counters.k_item)?;
                counters.k_item_root = true;
                let validated = validate_rule_term::<S>(
                    &item.value,
                    side.into(),
                    bindings,
                    discovered,
                    counters,
                    keys,
                );
                counters.k_item_root = false;
                validated?;
            }
            if sequence.notation == DescriptorKSequenceNotation::DotK {
                Ok(())
            } else {
                validate_frame(
                    &sequence.tail,
                    side,
                    RuleRole::KSequenceTail,
                    bindings,
                    RuleBindingUse::KSequenceFrame,
                    discovered,
                    &mut counters.k_tail,
                    keys,
                )
            }
        }
        ProtocolRuleStateTerm::Map(map) => {
            validate_map_shell(map, side, counters, keys)?;
            match &map.body {
                ProtocolRuleMapBody::Empty { .. } => Ok(()),
                ProtocolRuleMapBody::Items { items, remainder } => {
                    for item in items {
                        insert_state_exact(
                            keys,
                            &item.key_key,
                            side,
                            RuleRole::MapKey,
                            counters.map_key,
                        )?;
                        counters.map_key = rule_increment(counters.map_key)?;
                        insert_state_exact(
                            keys,
                            &item.value_key,
                            side,
                            RuleRole::MapValue,
                            counters.map_value,
                        )?;
                        counters.map_value = rule_increment(counters.map_value)?;
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
                            counters,
                            keys,
                        )?;
                        validate_rule_term::<S>(
                            &item.value,
                            side.into(),
                            bindings,
                            discovered,
                            counters,
                            keys,
                        )?;
                    }
                    validate_frame(
                        remainder,
                        side,
                        RuleRole::MapRemainder,
                        bindings,
                        RuleBindingUse::MapFrame,
                        discovered,
                        &mut counters.map_remainder,
                        keys,
                    )
                }
                ProtocolRuleMapBody::Update {
                    base_key,
                    base,
                    key_key,
                    key,
                    value_key,
                    value,
                } => {
                    insert_state_exact(
                        keys,
                        base_key,
                        side,
                        RuleRole::MapUpdateBase,
                        counters.map_update_base,
                    )?;
                    counters.map_update_base = rule_increment(counters.map_update_base)?;
                    insert_state_exact(keys, key_key, side, RuleRole::MapKey, counters.map_key)?;
                    counters.map_key = rule_increment(counters.map_key)?;
                    insert_state_exact(
                        keys,
                        value_key,
                        side,
                        RuleRole::MapValue,
                        counters.map_value,
                    )?;
                    counters.map_value = rule_increment(counters.map_value)?;
                    for term in [base, key, value] {
                        validate_rule_term::<S>(
                            term,
                            side.into(),
                            bindings,
                            discovered,
                            counters,
                            keys,
                        )?;
                    }
                    Ok(())
                }
            }
        }
    }
}

fn validate_k_shell<T>(
    sequence: &ProtocolRuleKSequence<T>,
    side: RuleSide,
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if let Some(payload) = &sequence.payload_key {
        insert_state_exact(
            keys,
            payload,
            side,
            RuleRole::KSequencePayload,
            counters.k_payload,
        )?;
        counters.k_payload = rule_increment(counters.k_payload)?;
    }
    match sequence.notation {
        DescriptorKSequenceNotation::DotK => {
            if !sequence.items.is_empty()
                || sequence.payload_key.is_none()
                || !matches!(sequence.tail, ProtocolRuleFrame::Exact)
            {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::InvalidStandaloneDotKShell,
                ));
            }
            let key =
                sequence
                    .dot_k_key
                    .as_ref()
                    .ok_or(StateTransportError::InvalidCellContent(
                        StateCellContentReason::DotKMissingProvenance,
                    ))?;
            insert_state_exact(keys, key, side, RuleRole::KSequenceTail, counters.k_tail)?;
            counters.k_tail = rule_increment(counters.k_tail)?;
        }
        DescriptorKSequenceNotation::Comma | DescriptorKSequenceNotation::Operator => {
            if sequence.dot_k_key.is_some()
                || (!sequence.items.is_empty() && sequence.payload_key.is_none())
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
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    if let Some(payload) = &map.payload_key {
        insert_state_exact(
            keys,
            payload,
            side,
            RuleRole::MapPayload,
            counters.map_payload,
        )?;
        counters.map_payload = rule_increment(counters.map_payload)?;
    }
    match &map.body {
        ProtocolRuleMapBody::Empty { explicit_dot } => {
            if *explicit_dot != map.payload_key.is_some() {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::EmptyMapProvenanceMismatch,
                ));
            }
        }
        ProtocolRuleMapBody::Items { items, remainder } => {
            if map.payload_key.is_none()
                || (items.is_empty() && matches!(remainder, ProtocolRuleFrame::Exact))
            {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::MapItemContentOrPayloadProvenance,
                ));
            }
        }
        ProtocolRuleMapBody::Update { .. } => {
            if matches!(side, RuleSide::Left) || map.payload_key.is_none() {
                return Err(StateTransportError::InvalidCellContent(
                    StateCellContentReason::MapUpdateSideOrPayloadProvenance,
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
    counters: &'a mut RuleCounters,
    keys: &'a mut BTreeSet<ProvenanceKey>,
    /// The names bound by the enclosing `let` statements, innermost last.
    let_scopes: Vec<BTreeSet<String>>,
}

fn validate_rule_term<S: ValidationStage>(
    term: &Term<S>,
    side: ValidationSide,
    bindings: &[ProtocolRuleBinding<S::Sort>],
    discovered: &mut Vec<String>,
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    // `k::rewrite!(x => ())` removes a whole K-sequence item (KF-011).
    if super::validation::misplaced_empty_rewrite(term, counters.k_item_root) {
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
            counters,
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
        let local = self.counters.in_matches_pattern
            || self.counters.in_let_pattern
            || self.let_scopes.iter().any(|scope| scope.contains(name));
        if !local && !binding_has_kind(self.bindings, name, RuleBindingUse::Term) {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::RuleVariableBindingIsNotATerm,
            ));
        }
        validate_term_path_key(self.keys, path_key, key, self.side, self.counters)?;
        insert_term_exact(
            self.keys,
            key,
            self.side,
            TermRole::Reference,
            self.counters.reference,
        )?;
        self.counters.reference = rule_increment(self.counters.reference)?;
        // The right side of a `k::rewrite!` uses the subject's bindings; the
        // binding order is the left image's.
        if !local && !self.counters.in_rewrite_right {
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
        validate_term_path_key(self.keys, path_key, key, self.side, self.counters)?;
        S::validate_application(reference).map_err(|_| {
            StateTransportError::InvalidTerm(StateTermReason::InvalidApplicationTarget)
        })?;
        let (role, counter) = match head_class {
            DescriptorApplicationHeadClass::Applied => {
                (TermRole::ApplicationHead, &mut self.counters.application)
            }
            DescriptorApplicationHeadClass::BareReference => {
                (TermRole::Reference, &mut self.counters.reference)
            }
        };
        insert_term_exact(self.keys, key, self.side, role, *counter)?;
        *counter = rule_increment(*counter)?;
        Ok(())
    }

    fn literal(
        &mut self,
        key: &ProvenanceKey,
        literal: &crate::DescriptorLiteral,
    ) -> Result<(), Self::Error> {
        insert_term_exact(
            self.keys,
            key,
            self.side,
            TermRole::Literal,
            self.counters.literal,
        )?;
        self.counters.literal = rule_increment(self.counters.literal)?;
        literal.validate().map_err(|_| {
            StateTransportError::InvalidTerm(StateTermReason::NonCanonicalIntegerLiteral)
        })
    }

    fn wildcard(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        if self.counters.in_let_pattern {
            insert_rule_exact(
                self.keys,
                key,
                ProvenanceRole::LetWildcard,
                self.counters.let_wildcard,
            )?;
            self.counters.let_wildcard = rule_increment(self.counters.let_wildcard)?;
            return Ok(());
        }
        if self.counters.in_matches_pattern {
            insert_rule_exact(
                self.keys,
                key,
                ProvenanceRole::MatchesWildcard,
                self.counters.matches_wildcard,
            )?;
            self.counters.matches_wildcard = rule_increment(self.counters.matches_wildcard)?;
            return Ok(());
        }
        if !matches!(self.side, ValidationSide::Left) || self.counters.in_rewrite_right {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::WildcardsAreAllowedOnlyInRuleSubjects,
            ));
        }
        insert_rule_exact(
            self.keys,
            key,
            ProvenanceRole::RuleLeftWildcard,
            self.counters.wildcard,
        )?;
        self.counters.wildcard = rule_increment(self.counters.wildcard)?;
        Ok(())
    }

    fn builtin_token(
        &mut self,
        key: &ProvenanceKey,
        sort: crate::BuiltinSort,
        value: &str,
    ) -> Result<(), Self::Error> {
        let (role, counter) = builtin_token_role(sort, value, self.counters)?;
        insert_rule_exact(self.keys, key, role, *counter)?;
        *counter = rule_increment(*counter)?;
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
        insert_rule_exact(
            self.keys,
            S::sort_key(sort),
            ProvenanceRole::LexemeSort,
            self.counters.lexeme,
        )?;
        insert_rule_exact(
            self.keys,
            key,
            ProvenanceRole::LexemeText,
            self.counters.lexeme,
        )?;
        self.counters.lexeme = rule_increment(self.counters.lexeme)?;
        Ok(())
    }

    fn pattern_as(
        &mut self,
        key: &ProvenanceKey,
        binding_key: &ProvenanceKey,
        name: &str,
    ) -> Result<(), Self::Error> {
        let local = self.counters.in_matches_pattern;
        if self.counters.in_let_pattern || (!local && !matches!(self.side, ValidationSide::Left)) {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::PatternAsOutsideLeftHandSide,
            ));
        }
        if !local && !binding_has_kind(self.bindings, name, RuleBindingUse::Term) {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::RuleVariableBindingIsNotATerm,
            ));
        }
        insert_rule_exact(
            self.keys,
            key,
            ProvenanceRole::PatternAs,
            self.counters.pattern_as,
        )?;
        insert_rule_exact(
            self.keys,
            binding_key,
            ProvenanceRole::PatternAsBinding,
            self.counters.pattern_as,
        )?;
        self.counters.pattern_as = rule_increment(self.counters.pattern_as)?;
        if !local {
            discover_binding(self.side, name, self.discovered);
        }
        Ok(())
    }

    fn matches(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        if matches!(self.side, ValidationSide::Left)
            || self.counters.in_matches_pattern
            || self.counters.in_let_pattern
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::MatchesInPattern,
            ));
        }
        insert_rule_exact(
            self.keys,
            key,
            ProvenanceRole::Matches,
            self.counters.matches,
        )?;
        self.counters.matches = rule_increment(self.counters.matches)?;
        Ok(())
    }

    fn matches_pattern(&mut self, inside: bool) {
        self.counters.in_matches_pattern = inside;
    }

    fn let_binding(
        &mut self,
        key: &ProvenanceKey,
        sort: Option<&S::Sort>,
    ) -> Result<(), Self::Error> {
        if matches!(self.side, ValidationSide::Left)
            || self.counters.in_matches_pattern
            || self.counters.in_let_pattern
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::LetInPattern,
            ));
        }
        if let Some(sort) = sort {
            S::validate_sort(sort).map_err(|_| {
                StateTransportError::InvalidTerm(StateTermReason::InvalidSortTestSort)
            })?;
            insert_rule_exact(
                self.keys,
                S::sort_key(sort),
                ProvenanceRole::LetSort,
                self.counters.let_binding,
            )?;
        }
        insert_rule_exact(
            self.keys,
            key,
            ProvenanceRole::Let,
            self.counters.let_binding,
        )?;
        self.counters.let_binding = rule_increment(self.counters.let_binding)?;
        Ok(())
    }

    fn let_pattern(&mut self, inside: bool) {
        self.counters.in_let_pattern = inside;
    }

    fn closure(
        &mut self,
        key: &ProvenanceKey,
        binder_key: &ProvenanceKey,
        sort: &S::Sort,
    ) -> Result<(), Self::Error> {
        if matches!(self.side, ValidationSide::Left)
            || self.counters.in_matches_pattern
            || self.counters.in_let_pattern
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::ClosureInPattern,
            ));
        }
        S::validate_sort(sort)
            .map_err(|_| StateTransportError::InvalidTerm(StateTermReason::InvalidSortTestSort))?;
        let ordinal = self.counters.ml_binder;
        insert_rule_exact(self.keys, key, ProvenanceRole::MlConnective, ordinal)?;
        insert_rule_exact(self.keys, binder_key, ProvenanceRole::MlBinder, ordinal)?;
        insert_rule_exact(
            self.keys,
            S::sort_key(sort),
            ProvenanceRole::MlBinderSort,
            ordinal,
        )?;
        self.counters.ml_binder = rule_increment(ordinal)?;
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
        if !self.counters.allow_rewrite
            || !matches!(self.side, ValidationSide::Left)
            || self.counters.in_matches_pattern
            || self.counters.in_let_pattern
            || !self.let_scopes.is_empty()
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::RewriteOutsideSingleBodyRule,
            ));
        }
        if nested || self.counters.in_rewrite_right {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::NestedRewrite,
            ));
        }
        for (actual, role) in [
            (key, ProvenanceRole::RuleLocalRewrite),
            (from_key, ProvenanceRole::RuleLocalRewriteFrom),
            (to_key, ProvenanceRole::RuleLocalRewriteTo),
        ] {
            insert_rule_exact(self.keys, actual, role, self.counters.rewrite)?;
        }
        self.counters.rewrite = rule_increment(self.counters.rewrite)?;
        Ok(())
    }

    fn rewrite_right(&mut self, inside: bool) {
        self.counters.in_rewrite_right = inside;
    }

    fn pattern_or(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        if self.counters.in_let_pattern
            || (!matches!(self.side, ValidationSide::Left) && !self.counters.in_matches_pattern)
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::PatternOrOutsideLeftHandSide,
            ));
        }
        insert_rule_exact(
            self.keys,
            key,
            ProvenanceRole::PatternOr,
            self.counters.pattern_or,
        )?;
        self.counters.pattern_or = rule_increment(self.counters.pattern_or)?;
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
        insert_rule_exact(
            self.keys,
            S::sort_key(sort),
            ProvenanceRole::SortTestSort,
            self.counters.sort_test,
        )?;
        insert_rule_exact(
            self.keys,
            key,
            ProvenanceRole::SortTest,
            self.counters.sort_test,
        )?;
        self.counters.sort_test = rule_increment(self.counters.sort_test)?;
        Ok(())
    }

    fn application_instance(&mut self, sort: &S::Sort) -> Result<(), Self::Error> {
        S::validate_sort(sort)
            .map_err(|_| StateTransportError::InvalidTerm(StateTermReason::InvalidSortTestSort))?;
        insert_rule_exact(
            self.keys,
            S::sort_key(sort),
            ProvenanceRole::ApplicationInstance,
            self.counters.application_instance,
        )?;
        self.counters.application_instance = rule_increment(self.counters.application_instance)?;
        Ok(())
    }

    fn anonymous(
        &mut self,
        key: &ProvenanceKey,
        sort: &S::Sort,
        spelling: &str,
    ) -> Result<(), Self::Error> {
        if !matches!(self.side, ValidationSide::Left) || !spelling.starts_with('_') {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::UnexpectedAnonymousOccurrence,
            ));
        }
        S::validate_sort(sort)
            .map_err(|_| StateTransportError::InvalidTerm(StateTermReason::InvalidAnonymousSort))?;
        insert_rule_exact(
            self.keys,
            key,
            ProvenanceRole::ClaimAnonymous,
            self.counters.anonymous,
        )?;
        insert_rule_exact(
            self.keys,
            S::sort_key(sort),
            ProvenanceRole::ClaimAnonymousSort,
            self.counters.anonymous,
        )?;
        insert_rule_exact(
            self.keys,
            &ProvenanceKey::new(
                ProvenanceRole::ClaimAnonymousSpelling,
                self.counters.anonymous,
            ),
            ProvenanceRole::ClaimAnonymousSpelling,
            self.counters.anonymous,
        )?;
        self.counters.anonymous = rule_increment(self.counters.anonymous)?;
        Ok(())
    }

    fn or_bool(
        &mut self,
        key: &ProvenanceKey,
        _arguments: &crate::AtLeastTwo<Term<S>>,
    ) -> Result<(), Self::Error> {
        self.keys.insert(key.clone());
        Ok(())
    }

    fn cell(
        &mut self,
        key: &ProvenanceKey,
        declaration: &S::Nominal,
        fields: &[CellTermField<S>],
    ) -> Result<(), Self::Error> {
        S::validate_fragment(declaration, fields.is_empty())?;
        insert_term_exact(
            self.keys,
            key,
            self.side,
            TermRole::ApplicationHead,
            self.counters.application,
        )?;
        self.counters.application = rule_increment(self.counters.application)?;
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
                insert_term_exact(
                    self.keys,
                    key,
                    self.side,
                    TermRole::RecordFieldName,
                    self.counters.record_field,
                )?;
                self.counters.record_field = rule_increment(self.counters.record_field)?;
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
        insert_term_exact(
            self.keys,
            &field.key,
            self.side,
            TermRole::RecordFieldName,
            self.counters.record_field,
        )?;
        self.counters.record_field = rule_increment(self.counters.record_field)?;
        Ok(())
    }
}

fn validate_term_path_key(
    keys: &mut BTreeSet<ProvenanceKey>,
    path_key: &ProvenanceKey,
    semantic_key: &ProvenanceKey,
    side: ValidationSide,
    counters: &mut RuleCounters,
) -> Result<(), StateTransportError> {
    if matches!(
        side,
        ValidationSide::Requires | ValidationSide::Ensures | ValidationSide::RuleEnsures
    ) {
        insert_term_exact(keys, path_key, side, TermRole::Path, counters.path)?;
        counters.path = rule_increment(counters.path)?;
    } else if path_key != semantic_key {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::RuleTermKeyMismatch,
        ));
    }
    Ok(())
}

#[expect(
    clippy::too_many_arguments,
    reason = "Frame validation requires its rule side, binding context, and provenance accumulators."
)]
fn validate_frame<S>(
    frame: &ProtocolRuleFrame,
    side: RuleSide,
    role_suffix: RuleRole,
    bindings: &[ProtocolRuleBinding<S>],
    binding_kind: RuleBindingUse,
    discovered: &mut Vec<String>,
    counter: &mut u32,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    match (side, frame) {
        (_, ProtocolRuleFrame::Exact) => Ok(()),
        (RuleSide::Left, ProtocolRuleFrame::Anonymous { key }) => {
            insert_state_exact(keys, key, side, role_suffix, *counter)?;
            *counter = rule_increment(*counter)?;
            Ok(())
        }
        (RuleSide::Left, ProtocolRuleFrame::Bind { key, binding }) => {
            if !binding_has_kind(bindings, binding, binding_kind) {
                return Err(StateTransportError::InvalidTerm(
                    StateTermReason::SubjectFrameBindingKind,
                ));
            }
            insert_state_exact(keys, key, side, role_suffix, *counter)?;
            *counter = rule_increment(*counter)?;
            discover_binding(side.into(), binding, discovered);
            Ok(())
        }
        (RuleSide::Right, ProtocolRuleFrame::Reuse { key, binding }) => {
            if !binding_has_kind(bindings, binding, binding_kind) {
                return Err(StateTransportError::InvalidTerm(
                    StateTermReason::ResultFrameBindingKind,
                ));
            }
            insert_state_exact(keys, key, side, role_suffix, *counter)?;
            *counter = rule_increment(*counter)?;
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
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    validate_binding_catalog_names(bindings)?;
    let mut term_ordinal = 0;
    for binding in bindings {
        if let ProtocolRuleBindingKind::Term { sort } = &binding.kind {
            insert_rule_exact(
                keys,
                S::sort_key(sort),
                ProvenanceRole::RuleBindingType,
                term_ordinal,
            )?;
            term_ordinal = rule_increment(term_ordinal)?;
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
            },
            actual,
        })
    }
}

fn validate_rule_complete_set(
    primary: &ProvenanceKey,
    actual: &BTreeSet<ProvenanceKey>,
    expected: &BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    let expected_primary =
        if expected.contains(&ProvenanceKey::new(ProvenanceRole::ClaimDeclaration, 0)) {
            ProvenanceKey::new(ProvenanceRole::ClaimDeclaration, 0)
        } else {
            ProvenanceKey::new(ProvenanceRole::RuleDeclaration, 0)
        };
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

fn insert_rule_exact(
    keys: &mut BTreeSet<ProvenanceKey>,
    actual: &ProvenanceKey,
    role: ProvenanceRole,
    ordinal: u32,
) -> Result<(), StateTransportError> {
    let expected = ProvenanceKey::new(role, ordinal);
    if actual != &expected {
        return Err(StateTransportError::UnexpectedProvenance {
            expected,
            actual: actual.clone(),
        });
    }
    keys.insert(actual.clone());
    Ok(())
}

fn insert_state_exact(
    keys: &mut BTreeSet<ProvenanceKey>,
    actual: &ProvenanceKey,
    side: RuleSide,
    role: RuleRole,
    ordinal: u32,
) -> Result<(), StateTransportError> {
    insert_rule_exact(keys, actual, role.on_side(side), ordinal)
}

fn insert_term_exact(
    keys: &mut BTreeSet<ProvenanceKey>,
    actual: &ProvenanceKey,
    side: ValidationSide,
    role: TermRole,
    ordinal: u32,
) -> Result<(), StateTransportError> {
    insert_rule_exact(keys, actual, role.on_side(side), ordinal)
}

fn rule_increment(value: u32) -> Result<u32, StateTransportError> {
    value.checked_add(1).ok_or(StateTransportError::InvalidTerm(
        StateTermReason::RuleProvenanceOrdinalExceedsU32,
    ))
}

#[cfg(test)]
mod bytes_token_tests {
    use super::{RuleCounters, StateTermReason, builtin_token_role};
    use crate::{BuiltinSort, ProvenanceRole, StateTransportError};
    use krs_test_support::assert_rejects;

    #[test]
    fn builtin_bytes_tokens_accept_only_the_canonical_codec() {
        let mut counters = RuleCounters::default();
        let (role, ordinal) =
            builtin_token_role(BuiltinSort::Bytes, r#"b"\x00\x7f\xff""#, &mut counters).unwrap();
        assert_eq!(role, ProvenanceRole::ClaimBytesToken);
        assert_eq!(*ordinal, 0);

        for malformed in [r#""\x00""#, r#"b"\x0""#, r#"b"\xAF""#, r#"b"\x+1""#] {
            assert_rejects!(
                builtin_token_role(BuiltinSort::Bytes, malformed, &mut counters),
                StateTransportError::InvalidTerm(StateTermReason::InvalidCompilerOwnedBuiltinToken)
            );
        }
    }
}

#[cfg(test)]
#[path = "rule_validation_tests.rs"]
mod validation_tests;

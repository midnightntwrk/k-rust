//! Collector transport for whole-configuration rules, claims, and context aliases.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::host::HostTypeReference;
use crate::transport::configuration::{
    CellWrapper, DescriptorCellReference, DescriptorKSequenceNotation, HostCellReference,
    StateTransportError,
};
use crate::transport::grammar::{
    DescriptorApplicationHeadClass, DescriptorRuleCondition, DescriptorRuleLabel,
    DescriptorSortRef, DescriptorSortReference, DescriptorTerm, DescriptorTermArgument,
    HostRuleCondition, HostSortReference, HostTerm, HostTermArgument, valid_rule_label_name,
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

/// One typed claim binder with explicit scope kind retained by its containing list.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorClaimBinder {
    /// Binder declaration provenance.
    pub declaration_key: ProvenanceKey,
    /// Binder-name provenance.
    pub name_key: ProvenanceKey,
    /// Authored Rust name.
    pub name: String,
    /// Exact resolved sort and sort provenance.
    pub sort: DescriptorSortReference,
}

/// Host counterpart of [`DescriptorClaimBinder`].
#[derive(Clone, Debug)]
pub struct HostClaimBinder {
    /// Binder declaration provenance.
    pub declaration_key: ProvenanceKey,
    /// Binder-name provenance.
    pub name_key: ProvenanceKey,
    /// Authored Rust name.
    pub name: String,
    /// Rust-resolved sort.
    pub sort: HostSortReference,
}

/// Stable claim-only metadata attached to one configuration rewrite.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorClaim {
    /// Claim declaration provenance.
    pub declaration_key: ProvenanceKey,
    /// Exact modality provenance.
    pub modality_key: ProvenanceKey,
    /// Exactly one reachability modality.
    pub modality: ClaimModality,
    /// Optional circularity marker provenance.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub circularity_key: Option<ProvenanceKey>,
    /// Universally scoped ordinary term binders.
    pub universals: Vec<DescriptorClaimBinder>,
    /// Existentials scoped to RHS and ensures.
    pub existentials: Vec<DescriptorClaimBinder>,
    /// Optional object-Bool postcondition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ensures: Option<DescriptorRuleCondition>,
    /// Complete `or_bool!` shell provenance occurrences.
    pub or_bool_keys: Vec<ProvenanceKey>,
}

/// Host counterpart of [`DescriptorClaim`].
#[derive(Clone, Debug)]
pub struct HostClaim {
    /// Claim declaration provenance.
    pub declaration_key: ProvenanceKey,
    /// Exact modality provenance.
    pub modality_key: ProvenanceKey,
    /// Exactly one reachability modality.
    pub modality: ClaimModality,
    /// Optional circularity marker provenance.
    pub circularity_key: Option<ProvenanceKey>,
    /// Universally scoped ordinary term binders.
    pub universals: Vec<HostClaimBinder>,
    /// Existentials scoped to RHS and ensures.
    pub existentials: Vec<HostClaimBinder>,
    /// Optional object-Bool postcondition.
    pub ensures: Option<HostRuleCondition>,
    /// Complete `or_bool!` shell provenance occurrences.
    pub or_bool_keys: Vec<ProvenanceKey>,
}

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

/// Semantic family and, for ordinary terms, exact sort of one rule binding.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "binding_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ProtocolRuleBindingKind<S> {
    /// Ordinary term binding with an explicitly authored sort.
    Term {
        /// Exact authored sort reference.
        sort: S,
    },
    /// Named remainder of a K sequence.
    KSequenceFrame,
    /// Named remainder of a map.
    MapFrame,
    /// Named remainder of the complete fixed configuration.
    ConfigurationFrame,
}

/// One typed/kinded rule binding in subject first-occurrence preorder.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolRuleBinding<S> {
    /// Rust binding name used by subject and result terms or frames.
    pub name: String,
    /// Exact structural family and optional term sort.
    pub kind: ProtocolRuleBindingKind<S>,
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

/// One ordered K-sequence item in a configuration rule.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolRuleKSequenceItem<T> {
    /// Exact structural item provenance.
    pub key: ProvenanceKey,
    /// Structured item term.
    pub value: T,
}

/// Structured K sequence with an exact or framed tail.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolRuleKSequence<T> {
    /// Complete payload provenance. Empty `k![]` alone has no inner endpoint.
    pub payload_key: Option<ProvenanceKey>,
    /// Exact standalone `.K` provenance.
    pub dot_k_key: Option<ProvenanceKey>,
    /// Preserved parser notation.
    pub notation: DescriptorKSequenceNotation,
    /// Ordered sequence prefix.
    pub items: Vec<ProtocolRuleKSequenceItem<T>>,
    /// Exact or associative tail.
    pub tail: ProtocolRuleFrame,
}

/// One ordered map item in a configuration rule.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolRuleMapItem<T> {
    /// Exact key-expression provenance.
    pub key_key: ProvenanceKey,
    /// Structured map key.
    pub key: T,
    /// Exact value-expression provenance.
    pub value_key: ProvenanceKey,
    /// Structured map value.
    pub value: T,
}

/// Empty, associative-item, or functional-update map rule term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "map_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ProtocolRuleMapBody<T> {
    /// `.Map` or empty `map![]`.
    Empty {
        /// Whether `.Map` was explicitly authored.
        explicit_dot: bool,
    },
    /// Ordered items and exact/framed remainder.
    Items {
        /// Ordered key/value items; may be empty when the frame is non-exact.
        items: Vec<ProtocolRuleMapItem<T>>,
        /// Exact or associative remainder.
        remainder: ProtocolRuleFrame,
    },
    /// Functional result-side update.
    Update {
        /// Exact base-expression provenance.
        base_key: ProvenanceKey,
        /// Existing map term.
        base: T,
        /// Exact updated-key provenance.
        key_key: ProvenanceKey,
        /// Updated key term.
        key: T,
        /// Exact replacement-value provenance.
        value_key: ProvenanceKey,
        /// Replacement value term.
        value: T,
    },
}

/// Structured map occurrence in a configuration rule.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolRuleMap<T> {
    /// Complete map payload provenance. Empty `map![]` has no inner endpoint.
    pub payload_key: Option<ProvenanceKey>,
    /// Classified map operation.
    pub body: ProtocolRuleMapBody<T>,
}

/// Leaf state families admitted by `cells!` entries.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "state_term_kind",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum ProtocolRuleStateTerm<T> {
    /// Ordinary structured term.
    Term(T),
    /// Structured K sequence.
    KSequence(ProtocolRuleKSequence<T>),
    /// Structured map.
    Map(ProtocolRuleMap<T>),
}

/// One selected fixed cell in a simultaneous configuration side.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolRuleCell<I, T> {
    /// Exact selected-field provenance and owner-qualified identity.
    pub field: I,
    /// Exact `Cell`/`KCell` wrapper path provenance.
    pub wrapper_key: ProvenanceKey,
    /// Typed wrapper meaning.
    pub wrapper: CellWrapper,
    /// Structured cell state.
    pub value: ProtocolRuleStateTerm<T>,
}

/// One complete `cells!` side of a simultaneous configuration rule.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolRuleCells<I, T> {
    /// Complete `cells!` payload provenance.
    pub key: ProvenanceKey,
    /// Selected fixed cells in authored order.
    pub cells: Vec<ProtocolRuleCell<I, T>>,
    /// Exact or framed remainder of the complete configuration.
    pub remainder: ProtocolRuleFrame,
}

/// Stable selected-cell side.
pub type DescriptorRuleCells = ProtocolRuleCells<DescriptorCellReference, DescriptorTerm>;

/// Host selected-cell side.
pub type HostRuleCells = ProtocolRuleCells<HostCellReference, HostTerm>;

/// Semantic family of one binding in a one-sided context-alias pattern.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "binding_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ProtocolContextAliasBindingKind<S> {
    /// The distinguished ordinary term occurrence substituted for `HERE`.
    Here,
    /// An ordinary typed term binding other than `HERE`.
    Term {
        /// Exact authored sort reference.
        sort: S,
    },
    /// Named K-sequence tail.
    KSequenceFrame,
    /// Named map remainder.
    MapFrame,
    /// Named complete-configuration remainder.
    ConfigurationFrame,
}

/// One binding in a one-sided context-alias pattern.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolContextAliasBinding<S> {
    /// Authored Rust binding name.
    pub name: String,
    /// Typed or structural binding family.
    pub kind: ProtocolContextAliasBindingKind<S>,
}

/// Stable one-sided reusable configuration context template.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorContextAlias {
    /// Declaration provenance.
    pub declaration_key: ProvenanceKey,
    /// Exact alias-name occurrence provenance.
    pub name_key: ProvenanceKey,
    /// Target-neutral authored alias identity.
    pub name: String,
    /// Exact `here` binder occurrence provenance.
    pub here_key: ProvenanceKey,
    /// Binding selected for native `HERE` substitution.
    pub here: String,
    /// Complete one-sided pattern provenance.
    pub pattern_key: ProvenanceKey,
    /// Exact fixed-configuration type.
    pub configuration: DescriptorConfigurationReference,
    /// Typed bindings in first-occurrence preorder.
    pub bindings: Vec<ProtocolContextAliasBinding<DescriptorSortReference>>,
    /// Complete one-sided cells pattern.
    pub pattern: DescriptorRuleCells,
}

/// Host counterpart of [`DescriptorContextAlias`].
#[derive(Clone, Debug)]
pub struct HostContextAlias {
    /// Declaration provenance.
    pub declaration_key: ProvenanceKey,
    /// Exact alias-name occurrence provenance.
    pub name_key: ProvenanceKey,
    /// Target-neutral authored alias identity.
    pub name: String,
    /// Exact `here` binder occurrence provenance.
    pub here_key: ProvenanceKey,
    /// Binding selected for native `HERE` substitution.
    pub here: String,
    /// Complete one-sided pattern provenance.
    pub pattern_key: ProvenanceKey,
    /// Rust-resolved fixed-configuration type.
    pub configuration: HostConfigurationReference,
    /// Typed bindings in first-occurrence preorder.
    pub bindings: Vec<ProtocolContextAliasBinding<HostSortReference>>,
    /// Complete one-sided cells pattern.
    pub pattern: HostRuleCells,
}

impl DescriptorContextAlias {
    /// Validates the frozen one-sided alias contract.
    ///
    /// # Errors
    ///
    /// Rejects wrong ownership, blank names, a missing/duplicate/wrong-kind
    /// `HERE` binding, or lost/mismatched structural frame bindings.
    pub fn validate(&self, descriptor_kind: ItemKind) -> Result<(), StateTransportError> {
        if descriptor_kind != ItemKind::ContextAlias {
            return Err(StateTransportError::ItemKind {
                field: "context alias descriptor",
                expected: "ContextAlias",
                actual: descriptor_kind,
            });
        }
        self.configuration.validate()?;
        if !valid_context_alias_name(&self.name) || self.here.trim().is_empty() {
            return Err(StateTransportError::InvalidText("context alias name/here"));
        }
        let mut names = BTreeSet::new();
        if self
            .bindings
            .iter()
            .any(|binding| !names.insert(binding.name.as_str()))
        {
            return Err(StateTransportError::InvalidTerm(
                "duplicate context-alias binding",
            ));
        }
        let here = self
            .bindings
            .iter()
            .filter(|binding| {
                binding.name == self.here
                    && matches!(binding.kind, ProtocolContextAliasBindingKind::Here)
            })
            .count();
        if here != 1 {
            return Err(StateTransportError::InvalidTerm(
                "context alias must select exactly one ordinary HERE binding",
            ));
        }
        if count_here_in_cells(&self.pattern, &self.here) != 1 {
            return Err(StateTransportError::InvalidTerm(
                "context alias HERE binding must occur exactly once in cell content",
            ));
        }
        validate_context_alias_frames(&self.pattern, &self.bindings)?;
        Ok(())
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
                "wrong context-alias primary provenance",
            ));
        }
        let expected = self.expected_provenance_keys();
        if expected != *actual {
            return Err(StateTransportError::InvalidTerm(
                "context-alias provenance is not closed",
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
    /// Returns the same local shape failures as [`DescriptorContextAlias::validate`].
    pub fn validate(&self, descriptor_kind: ItemKind) -> Result<(), StateTransportError> {
        if descriptor_kind != ItemKind::ContextAlias {
            return Err(StateTransportError::ItemKind {
                field: "context alias descriptor",
                expected: "ContextAlias",
                actual: descriptor_kind,
            });
        }
        if !valid_context_alias_name(&self.name) || self.here.trim().is_empty() {
            return Err(StateTransportError::InvalidText("context alias name/here"));
        }
        let here = self
            .bindings
            .iter()
            .filter(|binding| {
                binding.name == self.here
                    && matches!(binding.kind, ProtocolContextAliasBindingKind::Here)
            })
            .count();
        if here != 1 {
            return Err(StateTransportError::InvalidTerm(
                "context alias must select exactly one ordinary HERE binding",
            ));
        }
        validate_context_alias_frames(&self.pattern, &self.bindings)?;
        Ok(())
    }
}

#[allow(clippy::enum_variant_names)]
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
            "context-alias bindings",
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
            ProtocolRuleStateTerm::Term(_) => {}
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
            "context-alias structural binding catalog does not match its frames",
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
                    "context-alias frame binding has the wrong structural kind or occurrence",
                ));
            }
            Ok(())
        }
        ProtocolRuleFrame::Reuse { .. } => Err(StateTransportError::InvalidTerm(
            "a one-sided context alias cannot reuse a result frame",
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
        ProtocolRuleStateTerm::Term(term) => count_here_in_term(term, here),
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
                DescriptorTermArgument::Positional { value }
                | DescriptorTermArgument::Named { value, .. } => count_here_in_term(value, here),
            })
            .sum(),
        DescriptorTerm::Literal { .. }
        | DescriptorTerm::Wildcard { .. }
        | DescriptorTerm::BuiltinToken { .. }
        | DescriptorTerm::Anonymous { .. } => 0,
        DescriptorTerm::OrBool { arguments, .. } => arguments
            .iter()
            .map(|argument| count_here_in_term(argument, here))
            .sum(),
        DescriptorTerm::Cell { fields, .. } => fields
            .iter()
            .map(|field| count_here_in_term(&field.value, here))
            .sum(),
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
        keys.insert(cell.wrapper_key.clone());
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
        ProtocolRuleStateTerm::Term(term) => collect_term_keys(term, keys),
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
                    DescriptorTermArgument::Positional { value } => collect_term_keys(value, keys),
                    DescriptorTermArgument::Named { key, value, .. } => {
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
        DescriptorTerm::Anonymous { key, sort, .. } => {
            keys.extend([key.clone(), sort.key.clone()]);
        }
        DescriptorTerm::OrBool { key, arguments } => {
            keys.insert(key.clone());
            for argument in arguments {
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
    }
}

/// Stable simultaneous configuration rewrite.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorConfigurationRule {
    /// Transition, equation, or claim meaning.
    pub sentence_kind: SentenceKind,
    /// Optional explicit emitted K label.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<DescriptorRuleLabel>,
    /// Optional ordered-fallback priority transported from `#[k::rule(owise)]`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub priority: Option<crate::DescriptorRulePriority>,
    /// Optional object-language Boolean applicability condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub requires: Option<DescriptorRuleCondition>,
    /// Required claim-only metadata, present iff this is a claim.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub claim: Option<DescriptorClaim>,
    /// Complete subject-pattern provenance.
    pub pattern_key: ProvenanceKey,
    /// Exact subject configuration type.
    pub subject_configuration: DescriptorConfigurationReference,
    /// Complete result-expression provenance.
    pub result_key: ProvenanceKey,
    /// Exact result configuration type.
    pub result_configuration: DescriptorConfigurationReference,
    /// Typed subject bindings in first-occurrence structural preorder.
    pub bindings: Vec<DescriptorRuleBinding>,
    /// Complete left `cells!` pattern.
    pub subject: DescriptorRuleCells,
    /// Complete right `cells!` expression.
    pub result: DescriptorRuleCells,
}

/// Host counterpart of [`DescriptorConfigurationRule`].
#[derive(Clone, Debug)]
pub struct HostConfigurationRule {
    /// Transition, equation, or claim meaning.
    pub sentence_kind: SentenceKind,
    /// Optional explicit emitted K label.
    pub label: Option<DescriptorRuleLabel>,
    /// Optional ordered-fallback priority transported from `#[k::rule(owise)]`.
    pub priority: Option<crate::DescriptorRulePriority>,
    /// Optional object-language Boolean applicability condition.
    pub requires: Option<HostRuleCondition>,
    /// Required claim-only metadata, present iff this is a claim.
    pub claim: Option<HostClaim>,
    /// Complete subject-pattern provenance.
    pub pattern_key: ProvenanceKey,
    /// Rust-resolved subject configuration type.
    pub subject_configuration: HostConfigurationReference,
    /// Complete result-expression provenance.
    pub result_key: ProvenanceKey,
    /// Rust-resolved result configuration type.
    pub result_configuration: HostConfigurationReference,
    /// Typed subject bindings in first-occurrence structural preorder.
    pub bindings: Vec<HostRuleBinding>,
    /// Complete left `cells!` pattern.
    pub subject: HostRuleCells,
    /// Complete right `cells!` expression.
    pub result: HostRuleCells,
}

#[derive(Clone, Copy)]
enum ValidationSide {
    Left,
    Right,
    Requires,
    Ensures,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RuleBindingUse {
    Term,
    KSequenceFrame,
    MapFrame,
    ConfigurationFrame,
}

fn claim_checked_index(index: usize) -> Result<u32, StateTransportError> {
    u32::try_from(index).map_err(|_| StateTransportError::InvalidTerm("too many claim nodes"))
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
        }
    }
}

#[derive(Default)]
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
        crate::BuiltinSort::Bytes if valid_bytes_token(value) => {
            Ok((ProvenanceRole::ClaimBytesToken, &mut counters.bytes_token))
        }
        _ => Err(StateTransportError::InvalidTerm(
            "invalid compiler-owned builtin token",
        )),
    }
}

fn valid_bytes_token(value: &str) -> bool {
    let Some(body) = value
        .strip_prefix("b\"")
        .and_then(|value| value.strip_suffix('"'))
    else {
        return false;
    };
    let (chunks, remainder) = body.as_bytes().as_chunks::<4>();
    remainder.is_empty()
        && chunks.iter().all(|chunk| {
            chunk[0] == b'\\'
                && chunk[1] == b'x'
                && (chunk[2].is_ascii_digit() || (b'a'..=b'f').contains(&chunk[2]))
                && (chunk[3].is_ascii_digit() || (b'a'..=b'f').contains(&chunk[3]))
        })
}

impl DescriptorConfigurationReference {
    fn validate(&self) -> Result<(), StateTransportError> {
        if self.configuration.item_kind() != ItemKind::Configuration {
            return Err(StateTransportError::ItemKind {
                field: "configuration rule type",
                expected: "Configuration",
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

    /// Validates a closed provenance table and `rule_declaration#0` primary.
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

    #[allow(clippy::too_many_lines)] // Keeps stable claim validation in one ordered pass.
    fn validate_into(
        &self,
        descriptor_kind: ItemKind,
        keys: &mut BTreeSet<ProvenanceKey>,
    ) -> Result<(), StateTransportError> {
        validate_sentence_kind(self.sentence_kind, descriptor_kind)?;
        if self.sentence_kind == SentenceKind::Claim {
            if self.claim.is_none() || self.label.is_none() {
                return Err(StateTransportError::InvalidTerm(
                    "claims require typed metadata and an explicit label",
                ));
            }
        } else if self.claim.is_some() {
            return Err(StateTransportError::InvalidTerm(
                "claim metadata is valid only on claims",
            ));
        }
        if let Some(label) = &self.label {
            let role = if self.sentence_kind == SentenceKind::Claim {
                ProvenanceRole::ClaimLabel
            } else {
                ProvenanceRole::RuleLabel
            };
            insert_rule_exact(keys, &label.key, role, 0)?;
            if !valid_rule_label_name(&label.name) {
                return Err(StateTransportError::InvalidText("rule label"));
            }
        }
        if let Some(priority) = &self.priority {
            insert_rule_exact(keys, &priority.key, ProvenanceRole::RuleOwise, 0)?;
            if self.sentence_kind != SentenceKind::Transition || priority.value != 200 {
                return Err(StateTransportError::InvalidTerm(
                    "configuration-rule ordered fallback priority",
                ));
            }
        }
        self.subject_configuration.validate()?;
        self.result_configuration.validate()?;
        if self.subject_configuration.configuration != self.result_configuration.configuration {
            return Err(StateTransportError::InvalidCellContent(
                "rule subject and result configurations differ",
            ));
        }
        insert_rule_exact(keys, &self.pattern_key, ProvenanceRole::RulePattern, 0)?;
        insert_rule_exact(
            keys,
            &self.subject_configuration.key,
            ProvenanceRole::RuleType,
            0,
        )?;
        insert_rule_exact(keys, &self.result_key, ProvenanceRole::RuleResult, 0)?;
        insert_rule_exact(
            keys,
            &self.result_configuration.key,
            ProvenanceRole::RuleResultType,
            0,
        )?;
        keys.insert(ProvenanceKey::new(
            if self.sentence_kind == SentenceKind::Claim {
                ProvenanceRole::ClaimDeclaration
            } else {
                ProvenanceRole::RuleDeclaration
            },
            0,
        ));
        validate_descriptor_binding_catalog(&self.bindings, keys)?;

        let mut discovered = Vec::new();
        let mut left_counters = RuleCounters::default();
        validate_descriptor_cells(
            &self.subject,
            &self.subject_configuration.configuration,
            RuleSide::Left,
            &self.bindings,
            &mut discovered,
            &mut left_counters,
            keys,
        )?;
        if !binding_names_match(&self.bindings, &discovered) {
            return Err(StateTransportError::InvalidTerm(
                "binding catalog is not subject first-occurrence preorder",
            ));
        }
        let mut ignored = Vec::new();
        let mut right_counters = RuleCounters {
            id_token: left_counters.id_token,
            bytes_token: left_counters.bytes_token,
            anonymous: left_counters.anonymous,
            ..RuleCounters::default()
        };
        let mut right_bindings = self.bindings.clone();
        if let Some(claim) = &self.claim {
            for binder in &claim.existentials {
                right_bindings.push(ProtocolRuleBinding {
                    name: binder.name.clone(),
                    kind: ProtocolRuleBindingKind::Term {
                        sort: binder.sort.clone(),
                    },
                });
            }
        }
        validate_descriptor_cells(
            &self.result,
            &self.result_configuration.configuration,
            RuleSide::Right,
            &right_bindings,
            &mut ignored,
            &mut right_counters,
            keys,
        )?;
        let mut claim_counters = RuleCounters {
            id_token: right_counters.id_token,
            bytes_token: right_counters.bytes_token,
            anonymous: right_counters.anonymous,
            ..RuleCounters::default()
        };
        if let Some(requires) = &self.requires {
            insert_rule_exact(keys, &requires.key, ProvenanceRole::RuleRequires, 0)?;
            validate_descriptor_term(
                &requires.term,
                ValidationSide::Requires,
                &self.bindings,
                &mut Vec::new(),
                &mut claim_counters,
                keys,
            )?;
        }
        if let Some(claim) = &self.claim {
            validate_descriptor_claim(
                claim,
                &self.bindings,
                &right_bindings,
                keys,
                &claim_counters,
            )?;
        }
        Ok(())
    }
}

impl HostConfigurationRule {
    /// Validates the host-only rule using exact `TypeId` configuration/cell
    /// joins and the same parser-key contract as the stable form.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for invalid ownership, frames, terms,
    /// or side-specific provenance roles/ordinals.
    #[allow(clippy::too_many_lines)] // Mirrors stable claim validation at the host boundary.
    pub fn validate(&self, descriptor_kind: ItemKind) -> Result<(), StateTransportError> {
        validate_sentence_kind(self.sentence_kind, descriptor_kind)?;
        if self.sentence_kind == SentenceKind::Claim {
            if self.claim.is_none() || self.label.is_none() {
                return Err(StateTransportError::InvalidTerm(
                    "claims require typed metadata and an explicit label",
                ));
            }
        } else if self.claim.is_some() {
            return Err(StateTransportError::InvalidTerm(
                "claim metadata is valid only on claims",
            ));
        }
        let mut keys = BTreeSet::new();
        if let Some(label) = &self.label {
            let mut label_keys = BTreeSet::new();
            let role = if self.sentence_kind == SentenceKind::Claim {
                ProvenanceRole::ClaimLabel
            } else {
                ProvenanceRole::RuleLabel
            };
            insert_rule_exact(&mut label_keys, &label.key, role, 0)?;
            if !valid_rule_label_name(&label.name) {
                return Err(StateTransportError::InvalidText("rule label"));
            }
        }
        if let Some(priority) = &self.priority {
            insert_rule_exact(&mut keys, &priority.key, ProvenanceRole::RuleOwise, 0)?;
            if self.sentence_kind != SentenceKind::Transition || priority.value != 200 {
                return Err(StateTransportError::InvalidTerm(
                    "configuration-rule ordered fallback priority",
                ));
            }
        }
        if self.subject_configuration.configuration.key.resolve()
            != self.result_configuration.configuration.key.resolve()
        {
            return Err(StateTransportError::InvalidCellContent(
                "rule subject and result configurations differ",
            ));
        }
        insert_rule_exact(&mut keys, &self.pattern_key, ProvenanceRole::RulePattern, 0)?;
        insert_rule_exact(
            &mut keys,
            &self.subject_configuration.key,
            ProvenanceRole::RuleType,
            0,
        )?;
        insert_rule_exact(&mut keys, &self.result_key, ProvenanceRole::RuleResult, 0)?;
        insert_rule_exact(
            &mut keys,
            &self.result_configuration.key,
            ProvenanceRole::RuleResultType,
            0,
        )?;
        validate_host_binding_catalog(&self.bindings, &mut keys)?;
        let mut discovered = Vec::new();
        let mut left_counters = RuleCounters::default();
        validate_host_cells(
            &self.subject,
            self.subject_configuration.configuration.key,
            RuleSide::Left,
            &self.bindings,
            &mut discovered,
            &mut left_counters,
            &mut keys,
        )?;
        if !binding_names_match(&self.bindings, &discovered) {
            return Err(StateTransportError::InvalidTerm(
                "binding catalog is not subject first-occurrence preorder",
            ));
        }
        let mut ignored = Vec::new();
        let mut right_counters = RuleCounters {
            id_token: left_counters.id_token,
            bytes_token: left_counters.bytes_token,
            anonymous: left_counters.anonymous,
            ..RuleCounters::default()
        };
        let mut right_bindings = self.bindings.clone();
        if let Some(claim) = &self.claim {
            for binder in &claim.existentials {
                right_bindings.push(ProtocolRuleBinding {
                    name: binder.name.clone(),
                    kind: ProtocolRuleBindingKind::Term {
                        sort: binder.sort.clone(),
                    },
                });
            }
        }
        validate_host_cells(
            &self.result,
            self.result_configuration.configuration.key,
            RuleSide::Right,
            &right_bindings,
            &mut ignored,
            &mut right_counters,
            &mut keys,
        )?;
        let mut claim_counters = RuleCounters {
            id_token: right_counters.id_token,
            bytes_token: right_counters.bytes_token,
            anonymous: right_counters.anonymous,
            ..RuleCounters::default()
        };
        if let Some(requires) = &self.requires {
            insert_rule_exact(&mut keys, &requires.key, ProvenanceRole::RuleRequires, 0)?;
            validate_host_term(
                &requires.term,
                ValidationSide::Requires,
                &self.bindings,
                &mut Vec::new(),
                &mut claim_counters,
                &mut keys,
            )?;
        }
        if let Some(claim) = &self.claim {
            validate_host_claim(
                claim,
                &self.bindings,
                &right_bindings,
                &mut keys,
                &claim_counters,
            )?;
        }
        Ok(())
    }
}

fn validate_descriptor_claim(
    claim: &DescriptorClaim,
    left_bindings: &[DescriptorRuleBinding],
    right_bindings: &[DescriptorRuleBinding],
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
                "circularity requires an all-path claim",
            ));
        }
        insert_rule_exact(keys, key, ProvenanceRole::ClaimCircularity, 0)?;
    }
    validate_descriptor_claim_binders(
        &claim.universals,
        left_bindings,
        ProvenanceRole::ClaimUniversalBinder,
        0,
        keys,
    )?;
    validate_descriptor_claim_binders(
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
        let mut counters = RuleCounters {
            id_token: inherited.id_token,
            bytes_token: inherited.bytes_token,
            anonymous: inherited.anonymous,
            ..RuleCounters::default()
        };
        validate_descriptor_term(
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

fn validate_descriptor_claim_binders(
    binders: &[DescriptorClaimBinder],
    catalog: &[DescriptorRuleBinding],
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
                "invalid, duplicate, or uncatalogued claim binder",
            ));
        }
        insert_rule_exact(keys, &binder.declaration_key, declaration_role, ordinal)?;
        let binder_ordinal = binder_base
            .checked_add(ordinal)
            .ok_or(StateTransportError::InvalidTerm("too many claim binders"))?;
        insert_rule_exact(
            keys,
            &binder.name_key,
            ProvenanceRole::ClaimBinderName,
            binder_ordinal,
        )?;
        insert_rule_exact(
            keys,
            &binder.sort.key,
            ProvenanceRole::ClaimBinderSort,
            binder_ordinal,
        )?;
        binder
            .sort
            .sort
            .validate()
            .map_err(|_| StateTransportError::InvalidTerm("invalid claim binder sort"))?;
    }
    Ok(())
}

fn validate_host_claim(
    claim: &HostClaim,
    left_bindings: &[HostRuleBinding],
    right_bindings: &[HostRuleBinding],
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
                "circularity requires an all-path claim",
            ));
        }
        insert_rule_exact(keys, key, ProvenanceRole::ClaimCircularity, 0)?;
    }
    validate_host_claim_binders(
        &claim.universals,
        left_bindings,
        ProvenanceRole::ClaimUniversalBinder,
        0,
        keys,
    )?;
    validate_host_claim_binders(
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
        let mut counters = RuleCounters {
            id_token: inherited.id_token,
            bytes_token: inherited.bytes_token,
            anonymous: inherited.anonymous,
            ..RuleCounters::default()
        };
        validate_host_term(
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

fn validate_host_claim_binders(
    binders: &[HostClaimBinder],
    catalog: &[HostRuleBinding],
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
                "invalid, duplicate, or uncatalogued claim binder",
            ));
        }
        insert_rule_exact(keys, &binder.declaration_key, declaration_role, ordinal)?;
        let binder_ordinal = binder_base
            .checked_add(ordinal)
            .ok_or(StateTransportError::InvalidTerm("too many claim binders"))?;
        insert_rule_exact(
            keys,
            &binder.name_key,
            ProvenanceRole::ClaimBinderName,
            binder_ordinal,
        )?;
        insert_rule_exact(
            keys,
            &binder.sort.key,
            ProvenanceRole::ClaimBinderSort,
            binder_ordinal,
        )?;
    }
    Ok(())
}

fn validate_descriptor_cells(
    cells: &DescriptorRuleCells,
    owner: &StableItemId,
    side: RuleSide,
    bindings: &[DescriptorRuleBinding],
    discovered: &mut Vec<String>,
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    insert_state_exact(keys, &cells.key, side, RuleRole::CellsPayload, 0)?;
    let mut selected = BTreeSet::new();
    for cell in &cells.cells {
        cell.field.cell.validate()?;
        if &cell.field.cell.owner != owner && cell.field.cell.owner.item_kind() != ItemKind::Cell {
            return Err(StateTransportError::CellOwnerMismatch);
        }
        if !selected.insert(cell.field.cell.clone()) {
            return Err(StateTransportError::DuplicateValue("selected rule cells"));
        }
        insert_state_exact(
            keys,
            &cell.field.key,
            side,
            RuleRole::CellsField,
            counters.cells_field,
        )?;
        counters.cells_field = rule_increment(counters.cells_field)?;
        insert_state_exact(
            keys,
            &cell.wrapper_key,
            side,
            RuleRole::CellsWrapper,
            counters.cells_wrapper,
        )?;
        counters.cells_wrapper = rule_increment(counters.cells_wrapper)?;
        validate_rule_wrapper(cell.wrapper, &cell.value)?;
        validate_descriptor_state(&cell.value, side, bindings, discovered, counters, keys)?;
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

fn validate_host_cells(
    cells: &HostRuleCells,
    _owner: crate::HostTypeKey,
    side: RuleSide,
    bindings: &[HostRuleBinding],
    discovered: &mut Vec<String>,
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    insert_state_exact(keys, &cells.key, side, RuleRole::CellsPayload, 0)?;
    let mut selected = BTreeSet::new();
    for cell in &cells.cells {
        if !selected.insert(cell.field.cell.resolve()) {
            return Err(StateTransportError::DuplicateValue("selected rule cells"));
        }
        insert_state_exact(
            keys,
            &cell.field.key,
            side,
            RuleRole::CellsField,
            counters.cells_field,
        )?;
        counters.cells_field = rule_increment(counters.cells_field)?;
        insert_state_exact(
            keys,
            &cell.wrapper_key,
            side,
            RuleRole::CellsWrapper,
            counters.cells_wrapper,
        )?;
        counters.cells_wrapper = rule_increment(counters.cells_wrapper)?;
        validate_rule_wrapper(cell.wrapper, &cell.value)?;
        validate_host_state(&cell.value, side, bindings, discovered, counters, keys)?;
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
    wrapper: CellWrapper,
    value: &ProtocolRuleStateTerm<T>,
) -> Result<(), StateTransportError> {
    match (wrapper, value) {
        (CellWrapper::KCell, ProtocolRuleStateTerm::KSequence(_))
        | (CellWrapper::Cell, ProtocolRuleStateTerm::Term(_) | ProtocolRuleStateTerm::Map(_)) => {
            Ok(())
        }
        _ => Err(StateTransportError::InvalidCellContent(
            "rule wrapper and state family disagree",
        )),
    }
}

#[allow(clippy::too_many_lines)] // Mirrors the three frozen state families directly.
fn validate_descriptor_state(
    state: &ProtocolRuleStateTerm<DescriptorTerm>,
    side: RuleSide,
    bindings: &[DescriptorRuleBinding],
    discovered: &mut Vec<String>,
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    match state {
        ProtocolRuleStateTerm::Term(term) => {
            validate_descriptor_term(term, side.into(), bindings, discovered, counters, keys)
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
                validate_descriptor_term(
                    &item.value,
                    side.into(),
                    bindings,
                    discovered,
                    counters,
                    keys,
                )?;
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
                        validate_descriptor_term(
                            &item.key,
                            side.into(),
                            bindings,
                            discovered,
                            counters,
                            keys,
                        )?;
                        validate_descriptor_term(
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
                        validate_descriptor_term(
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

#[allow(clippy::too_many_lines)] // Mirrors stable validation at the host boundary.
fn validate_host_state(
    state: &ProtocolRuleStateTerm<HostTerm>,
    side: RuleSide,
    bindings: &[HostRuleBinding],
    discovered: &mut Vec<String>,
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    match state {
        ProtocolRuleStateTerm::Term(term) => {
            validate_host_term(term, side.into(), bindings, discovered, counters, keys)
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
                validate_host_term(
                    &item.value,
                    side.into(),
                    bindings,
                    discovered,
                    counters,
                    keys,
                )?;
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
                        validate_host_term(
                            &item.key,
                            side.into(),
                            bindings,
                            discovered,
                            counters,
                            keys,
                        )?;
                        validate_host_term(
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
                        validate_host_term(
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
                    "standalone .K has an invalid shell",
                ));
            }
            let key =
                sequence
                    .dot_k_key
                    .as_ref()
                    .ok_or(StateTransportError::InvalidCellContent(
                        ".K is missing exact provenance",
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
                    "invalid K-sequence shell",
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
                    "empty map provenance disagrees with notation",
                ));
            }
        }
        ProtocolRuleMapBody::Items { items, remainder } => {
            if map.payload_key.is_none()
                || (items.is_empty() && matches!(remainder, ProtocolRuleFrame::Exact))
            {
                return Err(StateTransportError::InvalidCellContent(
                    "map items require content or a frame and payload provenance",
                ));
            }
        }
        ProtocolRuleMapBody::Update { .. } => {
            if matches!(side, RuleSide::Left) || map.payload_key.is_none() {
                return Err(StateTransportError::InvalidCellContent(
                    "map updates are result-only and require payload provenance",
                ));
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_lines)] // Exhaustively mirrors the closed descriptor term protocol.
fn validate_descriptor_term(
    term: &DescriptorTerm,
    side: ValidationSide,
    bindings: &[DescriptorRuleBinding],
    discovered: &mut Vec<String>,
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    match term {
        DescriptorTerm::Variable {
            key,
            path_key,
            name,
        } => {
            if !binding_has_kind(bindings, name, RuleBindingUse::Term) {
                return Err(StateTransportError::InvalidTerm(
                    "rule variable binding is not a term",
                ));
            }
            validate_term_path_key(keys, path_key, key, side, counters)?;
            insert_term_exact(keys, key, side, TermRole::Reference, counters.reference)?;
            counters.reference = rule_increment(counters.reference)?;
            discover_binding(side, name, discovered);
            Ok(())
        }
        DescriptorTerm::Application {
            head_class,
            reference,
            path_key,
            arguments,
        } => {
            if *head_class == DescriptorApplicationHeadClass::BareReference && !arguments.is_empty()
            {
                return Err(StateTransportError::InvalidTerm(
                    "rule application keys or head class are invalid",
                ));
            }
            validate_term_path_key(keys, path_key, &reference.key, side, counters)?;
            reference
                .application
                .validate()
                .map_err(|_| StateTransportError::InvalidTerm("invalid application target"))?;
            match head_class {
                DescriptorApplicationHeadClass::Applied => {
                    insert_term_exact(
                        keys,
                        &reference.key,
                        side,
                        TermRole::ApplicationHead,
                        counters.application,
                    )?;
                    counters.application = rule_increment(counters.application)?;
                }
                DescriptorApplicationHeadClass::BareReference => {
                    insert_term_exact(
                        keys,
                        &reference.key,
                        side,
                        TermRole::Reference,
                        counters.reference,
                    )?;
                    counters.reference = rule_increment(counters.reference)?;
                }
            }
            validate_descriptor_arguments(arguments, side, bindings, discovered, counters, keys)
        }
        DescriptorTerm::Literal { key, literal } => {
            insert_term_exact(keys, key, side, TermRole::Literal, counters.literal)?;
            counters.literal = rule_increment(counters.literal)?;
            validate_literal(literal)
        }
        DescriptorTerm::Wildcard { key } => {
            if !matches!(side, ValidationSide::Left) {
                return Err(StateTransportError::InvalidTerm(
                    "wildcards are allowed only in rule subjects",
                ));
            }
            insert_rule_exact(
                keys,
                key,
                ProvenanceRole::RuleLeftWildcard,
                counters.wildcard,
            )?;
            counters.wildcard = rule_increment(counters.wildcard)?;
            Ok(())
        }
        DescriptorTerm::BuiltinToken { key, sort, value } => {
            let (role, counter) = builtin_token_role(*sort, value, counters)?;
            insert_rule_exact(keys, key, role, *counter)?;
            *counter = rule_increment(*counter)?;
            Ok(())
        }
        DescriptorTerm::Anonymous {
            key,
            sort,
            spelling,
        } => {
            if !matches!(side, ValidationSide::Left) || !spelling.starts_with('_') {
                return Err(StateTransportError::InvalidTerm(
                    "anonymous occurrences are claim-subject-only",
                ));
            }
            sort.sort
                .validate()
                .map_err(|_| StateTransportError::InvalidTerm("invalid anonymous sort"))?;
            insert_rule_exact(
                keys,
                key,
                ProvenanceRole::ClaimAnonymous,
                counters.anonymous,
            )?;
            insert_rule_exact(
                keys,
                &sort.key,
                ProvenanceRole::ClaimAnonymousSort,
                counters.anonymous,
            )?;
            insert_rule_exact(
                keys,
                &ProvenanceKey::new(ProvenanceRole::ClaimAnonymousSpelling, counters.anonymous),
                ProvenanceRole::ClaimAnonymousSpelling,
                counters.anonymous,
            )?;
            counters.anonymous = rule_increment(counters.anonymous)?;
            Ok(())
        }
        DescriptorTerm::OrBool { key, arguments } => {
            if arguments.len() < 2 {
                return Err(StateTransportError::InvalidTerm(
                    "or_bool requires at least two operands",
                ));
            }
            keys.insert(key.clone());
            for argument in arguments {
                validate_descriptor_term(argument, side, bindings, discovered, counters, keys)?;
            }
            Ok(())
        }
        DescriptorTerm::Cell {
            key,
            declaration,
            fields,
        } => {
            if declaration.item_kind() != ItemKind::Cell || fields.is_empty() {
                return Err(StateTransportError::InvalidTerm(
                    "fragment! requires a nonempty nominal cell declaration",
                ));
            }
            insert_term_exact(
                keys,
                key,
                side,
                TermRole::ApplicationHead,
                counters.application,
            )?;
            counters.application = rule_increment(counters.application)?;
            let mut names = BTreeSet::new();
            for field in fields {
                if !names.insert(field.field.clone()) {
                    return Err(StateTransportError::InvalidTerm(
                        "fragment! child field occurs more than once",
                    ));
                }
                insert_term_exact(
                    keys,
                    &field.key,
                    side,
                    TermRole::RecordFieldName,
                    counters.record_field,
                )?;
                counters.record_field = rule_increment(counters.record_field)?;
                validate_descriptor_term(&field.value, side, bindings, discovered, counters, keys)?;
            }
            Ok(())
        }
    }
}

fn validate_descriptor_arguments(
    arguments: &[DescriptorTermArgument],
    side: ValidationSide,
    bindings: &[DescriptorRuleBinding],
    discovered: &mut Vec<String>,
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    let named = arguments
        .first()
        .is_some_and(|argument| matches!(argument, DescriptorTermArgument::Named { .. }));
    let mut fields = BTreeSet::<ProductionFieldId>::new();
    for argument in arguments {
        match argument {
            DescriptorTermArgument::Positional { value } if !named => {
                validate_descriptor_term(value, side, bindings, discovered, counters, keys)?;
            }
            DescriptorTermArgument::Named { key, field, value } if named => {
                if !fields.insert(field.clone()) {
                    return Err(StateTransportError::DuplicateValue(
                        "rule application record fields",
                    ));
                }
                insert_term_exact(
                    keys,
                    key,
                    side,
                    TermRole::RecordFieldName,
                    counters.record_field,
                )?;
                counters.record_field = rule_increment(counters.record_field)?;
                validate_descriptor_term(value, side, bindings, discovered, counters, keys)?;
            }
            DescriptorTermArgument::Positional { .. } | DescriptorTermArgument::Named { .. } => {
                return Err(StateTransportError::InvalidTerm(
                    "positional and named rule arguments are mixed",
                ));
            }
        }
    }
    Ok(())
}

fn validate_term_path_key(
    keys: &mut BTreeSet<ProvenanceKey>,
    path_key: &ProvenanceKey,
    semantic_key: &ProvenanceKey,
    side: ValidationSide,
    counters: &mut RuleCounters,
) -> Result<(), StateTransportError> {
    if matches!(side, ValidationSide::Requires | ValidationSide::Ensures) {
        insert_term_exact(keys, path_key, side, TermRole::Path, counters.path)?;
        counters.path = rule_increment(counters.path)?;
    } else if path_key != semantic_key {
        return Err(StateTransportError::InvalidTerm(
            "configuration-rule term path and semantic keys disagree",
        ));
    }
    Ok(())
}

#[allow(clippy::too_many_lines)] // Exhaustively mirrors descriptor validation for host terms.
fn validate_host_term(
    term: &HostTerm,
    side: ValidationSide,
    bindings: &[HostRuleBinding],
    discovered: &mut Vec<String>,
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    match term {
        HostTerm::Variable {
            key,
            path_key,
            name,
        } => {
            if !binding_has_kind(bindings, name, RuleBindingUse::Term) {
                return Err(StateTransportError::InvalidTerm(
                    "rule variable binding is not a term",
                ));
            }
            validate_term_path_key(keys, path_key, key, side, counters)?;
            insert_term_exact(keys, key, side, TermRole::Reference, counters.reference)?;
            counters.reference = rule_increment(counters.reference)?;
            discover_binding(side, name, discovered);
            Ok(())
        }
        HostTerm::Application {
            head_class,
            reference,
            path_key,
            arguments,
        } => {
            if *head_class == DescriptorApplicationHeadClass::BareReference && !arguments.is_empty()
            {
                return Err(StateTransportError::InvalidTerm(
                    "rule application keys or head class are invalid",
                ));
            }
            validate_term_path_key(keys, path_key, &reference.key, side, counters)?;
            match head_class {
                DescriptorApplicationHeadClass::Applied => {
                    insert_term_exact(
                        keys,
                        &reference.key,
                        side,
                        TermRole::ApplicationHead,
                        counters.application,
                    )?;
                    counters.application = rule_increment(counters.application)?;
                }
                DescriptorApplicationHeadClass::BareReference => {
                    insert_term_exact(
                        keys,
                        &reference.key,
                        side,
                        TermRole::Reference,
                        counters.reference,
                    )?;
                    counters.reference = rule_increment(counters.reference)?;
                }
            }
            validate_host_arguments(arguments, side, bindings, discovered, counters, keys)
        }
        HostTerm::Literal { key, literal } => {
            insert_term_exact(keys, key, side, TermRole::Literal, counters.literal)?;
            counters.literal = rule_increment(counters.literal)?;
            validate_literal(literal)
        }
        HostTerm::Wildcard { key } => {
            if !matches!(side, ValidationSide::Left) {
                return Err(StateTransportError::InvalidTerm(
                    "wildcards are allowed only in rule subjects",
                ));
            }
            insert_rule_exact(
                keys,
                key,
                ProvenanceRole::RuleLeftWildcard,
                counters.wildcard,
            )?;
            counters.wildcard = rule_increment(counters.wildcard)?;
            Ok(())
        }
        HostTerm::BuiltinToken { key, sort, value } => {
            let (role, counter) = builtin_token_role(*sort, value, counters)?;
            insert_rule_exact(keys, key, role, *counter)?;
            *counter = rule_increment(*counter)?;
            Ok(())
        }
        HostTerm::Anonymous {
            key,
            sort,
            spelling,
        } => {
            if !matches!(side, ValidationSide::Left) || !spelling.starts_with('_') {
                return Err(StateTransportError::InvalidTerm(
                    "anonymous occurrences are claim-subject-only",
                ));
            }
            insert_rule_exact(
                keys,
                key,
                ProvenanceRole::ClaimAnonymous,
                counters.anonymous,
            )?;
            insert_rule_exact(
                keys,
                &sort.key,
                ProvenanceRole::ClaimAnonymousSort,
                counters.anonymous,
            )?;
            insert_rule_exact(
                keys,
                &ProvenanceKey::new(ProvenanceRole::ClaimAnonymousSpelling, counters.anonymous),
                ProvenanceRole::ClaimAnonymousSpelling,
                counters.anonymous,
            )?;
            counters.anonymous = rule_increment(counters.anonymous)?;
            Ok(())
        }
        HostTerm::OrBool { key, arguments } => {
            if arguments.len() < 2 {
                return Err(StateTransportError::InvalidTerm(
                    "or_bool requires at least two operands",
                ));
            }
            keys.insert(key.clone());
            for argument in arguments {
                validate_host_term(argument, side, bindings, discovered, counters, keys)?;
            }
            Ok(())
        }
        HostTerm::Cell { key, fields, .. } => {
            if fields.is_empty() {
                return Err(StateTransportError::InvalidTerm(
                    "fragment! requires at least one child field",
                ));
            }
            insert_term_exact(
                keys,
                key,
                side,
                TermRole::ApplicationHead,
                counters.application,
            )?;
            counters.application = rule_increment(counters.application)?;
            let mut names = BTreeSet::new();
            for field in fields {
                if !names.insert(field.field.clone()) {
                    return Err(StateTransportError::InvalidTerm(
                        "fragment! child field occurs more than once",
                    ));
                }
                insert_term_exact(
                    keys,
                    &field.key,
                    side,
                    TermRole::RecordFieldName,
                    counters.record_field,
                )?;
                counters.record_field = rule_increment(counters.record_field)?;
                validate_host_term(&field.value, side, bindings, discovered, counters, keys)?;
            }
            Ok(())
        }
    }
}

fn validate_host_arguments(
    arguments: &[HostTermArgument],
    side: ValidationSide,
    bindings: &[HostRuleBinding],
    discovered: &mut Vec<String>,
    counters: &mut RuleCounters,
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    let named = arguments
        .first()
        .is_some_and(|argument| matches!(argument, HostTermArgument::Named { .. }));
    let mut fields = BTreeSet::<ProductionFieldId>::new();
    for argument in arguments {
        match argument {
            HostTermArgument::Positional { value } if !named => {
                validate_host_term(value, side, bindings, discovered, counters, keys)?;
            }
            HostTermArgument::Named { key, field, value } if named => {
                if !fields.insert(field.clone()) {
                    return Err(StateTransportError::DuplicateValue(
                        "rule application record fields",
                    ));
                }
                insert_term_exact(
                    keys,
                    key,
                    side,
                    TermRole::RecordFieldName,
                    counters.record_field,
                )?;
                counters.record_field = rule_increment(counters.record_field)?;
                validate_host_term(value, side, bindings, discovered, counters, keys)?;
            }
            HostTermArgument::Positional { .. } | HostTermArgument::Named { .. } => {
                return Err(StateTransportError::InvalidTerm(
                    "positional and named rule arguments are mixed",
                ));
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
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
                    "subject frame binding has the wrong structural kind",
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
                    "result frame binding has the wrong structural kind",
                ));
            }
            insert_state_exact(keys, key, side, role_suffix, *counter)?;
            *counter = rule_increment(*counter)?;
            Ok(())
        }
        (RuleSide::Left, ProtocolRuleFrame::Reuse { .. })
        | (RuleSide::Right, ProtocolRuleFrame::Anonymous { .. } | ProtocolRuleFrame::Bind { .. }) => {
            Err(StateTransportError::InvalidTerm(
                "frame form is invalid on this rule side",
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

fn validate_literal(literal: &crate::DescriptorLiteral) -> Result<(), StateTransportError> {
    if matches!(literal, crate::DescriptorLiteral::Int(value) if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()))
    {
        Err(StateTransportError::InvalidTerm(
            "integer literal is not canonical unsigned decimal",
        ))
    } else {
        Ok(())
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
        Err(StateTransportError::DuplicateValue("rule bindings"))
    } else {
        Ok(())
    }
}

fn validate_descriptor_binding_catalog(
    bindings: &[DescriptorRuleBinding],
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    validate_binding_catalog_names(bindings)?;
    let mut term_ordinal = 0;
    for binding in bindings {
        if let ProtocolRuleBindingKind::Term { sort } = &binding.kind {
            insert_rule_exact(
                keys,
                &sort.key,
                ProvenanceRole::RuleBindingType,
                term_ordinal,
            )?;
            term_ordinal = rule_increment(term_ordinal)?;
            if let DescriptorSortRef::Declared(sort) = &sort.sort
                && sort.item_kind() != ItemKind::Sort
            {
                return Err(StateTransportError::ItemKind {
                    field: "rule binding sort",
                    expected: "Sort",
                    actual: sort.item_kind(),
                });
            }
        }
    }
    Ok(())
}

fn validate_host_binding_catalog(
    bindings: &[HostRuleBinding],
    keys: &mut BTreeSet<ProvenanceKey>,
) -> Result<(), StateTransportError> {
    validate_binding_catalog_names(bindings)?;
    let mut term_ordinal = 0;
    for binding in bindings {
        if let ProtocolRuleBindingKind::Term { sort } = &binding.kind {
            insert_rule_exact(
                keys,
                &sort.key,
                ProvenanceRole::RuleBindingType,
                term_ordinal,
            )?;
            term_ordinal = rule_increment(term_ordinal)?;
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
    sentence_kind: SentenceKind,
    actual: ItemKind,
) -> Result<(), StateTransportError> {
    if sentence_kind == SentenceKind::Alias {
        return Err(StateTransportError::InvalidTerm(
            "static aliases cannot have configuration rewrite bodies",
        ));
    }
    if sentence_kind == SentenceKind::Simplification {
        return Err(StateTransportError::InvalidTerm(
            "simplifications cannot have configuration rewrite bodies",
        ));
    }
    let expected = match sentence_kind {
        SentenceKind::Transition => ItemKind::Rule,
        SentenceKind::Equation => ItemKind::Equation,
        SentenceKind::Simplification => {
            unreachable!("configuration simplifications were rejected above")
        }
        SentenceKind::Alias => unreachable!("configuration aliases were rejected above"),
        SentenceKind::Claim => ItemKind::Claim,
    };
    if actual == expected {
        Ok(())
    } else {
        Err(StateTransportError::ItemKind {
            field: "configuration rule descriptor",
            expected: match sentence_kind {
                SentenceKind::Transition => "Rule",
                SentenceKind::Equation => "Equation",
                SentenceKind::Simplification => {
                    unreachable!("configuration simplifications were rejected above")
                }
                SentenceKind::Alias => unreachable!("configuration aliases were rejected above"),
                SentenceKind::Claim => "Claim",
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
        "rule provenance ordinal exceeds u32",
    ))
}

#[cfg(test)]
mod bytes_token_tests {
    use super::{RuleCounters, builtin_token_role};
    use crate::{BuiltinSort, ProvenanceRole, StateTransportError};

    #[test]
    fn bytes_tokens_accept_only_canonical_lower_hex_transport() {
        let mut counters = RuleCounters::default();
        let (role, ordinal) =
            builtin_token_role(BuiltinSort::Bytes, r#"b"\x00\x7f\xff""#, &mut counters).unwrap();
        assert_eq!(role, ProvenanceRole::ClaimBytesToken);
        assert_eq!(*ordinal, 0);

        for malformed in [
            r#""\x00""#,
            r#"b"00""#,
            r#"b"\x0""#,
            r#"b"\xGG""#,
            r#"b"\xAF""#,
            r#"b"\u{00}""#,
        ] {
            assert!(matches!(
                builtin_token_role(BuiltinSort::Bytes, malformed, &mut counters),
                Err(StateTransportError::InvalidTerm(
                    "invalid compiler-owned builtin token"
                ))
            ));
        }
    }
}

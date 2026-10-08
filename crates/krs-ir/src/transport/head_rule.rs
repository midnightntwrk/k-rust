//! Collector transport for readable rules completed at a computation-cell head.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use super::detail::{StateTermReason, TransportField, TransportItemKind};
use crate::stage::{protocol_shape, stage_shape};
use crate::transport::grammar::{RuleCondition, Term};

use crate::{
    DescriptorCellReference, DescriptorRuleLabel, DescriptorRulePriority, DescriptorSortReference,
    DescriptorStage, DescriptorTerm, HostSortReference, HostStage, HostTerm, ItemKind,
    ProvenanceKey, ProvenanceRole, SentenceKind, StateTransportError,
};

protocol_shape! {
    /// One readable binding with an optional explicit `where name: Sort` refinement.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolHeadRuleBinding<S => sort_map => U> {
        /// Binding name in first-introduction order.
        pub name: String => [keep],
        /// Authored sort refinement, if present.
        #[serde(skip_serializing_if = "Option::is_none")]
        pub refinement: Option<S> => [option sort_map],
    }
}

/// Host binding transported before stable sort resolution.
pub type HostHeadRuleBinding = ProtocolHeadRuleBinding<HostSortReference>;
/// Stable binding transported to semantic inference.
pub type DescriptorHeadRuleBinding = ProtocolHeadRuleBinding<DescriptorSortReference>;

/// A named extra-cell occurrence awaiting collector resolution.
#[derive(Clone, Debug)]
pub struct HostHeadRuleCellReference {
    /// Exact authored cell-name provenance.
    pub key: ProvenanceKey,
    /// Rust field name used by the readable rule.
    pub name: String,
}

protocol_shape! {
    /// Result of rewriting one computation-cell head.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(
        tag = "head_result_kind",
        content = "head_result",
        rename_all = "snake_case"
    )]
    pub enum ProtocolHeadRuleResult<T => term_map => U> {
        /// Replace the matched head with one ordinary term.
        Replace(value: T => [term_map]),
        /// Splice zero or more `k![...]` items before the preserved tail.
        Splice(values: Vec<T> => [vec term_map]),
        /// Erase the matched head and expose the preserved tail.
        Erase,
    }
}

protocol_shape! {
    /// The matched computation-cell head of a readable rule and its rewrite.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolHeadRuleHead<T => term_map => U> {
        /// One matched computation-cell head item.
        pub subject: T => [term_map],
        /// Replacement, splice, or erasure before the implicit preserved tail.
        pub result: ProtocolHeadRuleResult<T> => [nested term_map],
    }
    map_order: [result, subject];
}

/// Host head result.
pub type HostHeadRuleResult = ProtocolHeadRuleResult<HostTerm>;
/// Stable head result.
pub type DescriptorHeadRuleResult = ProtocolHeadRuleResult<DescriptorTerm>;

protocol_shape! {
    /// One explicit gradual extra-cell clause.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(tag = "extra_kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum ProtocolHeadRuleExtra<I => cell_map => J, T => term_map => U> {
        /// Failable preserved map-item match (`have cell[key -> let value]`).
        HaveMap {
            /// Selected map cell.
            cell: I => [cell_map],
            /// Required map key.
            key: T => [term_map],
            /// Value binding introduced by the item match.
            value_binding: String => [keep],
        },
        /// Simultaneous whole-map replacement by an ordinary update term.
        UpdateMap {
            /// Selected map cell.
            cell: I => [cell_map],
            /// Implicit binding for the complete pre-state map.
            base_binding: String => [keep],
            /// Complete registered `map::update(base, key, value)` application.
            update: T => [term_map],
        },
        /// Simultaneous exact rewrite of one ordinary fixed leaf cell.
        RewriteCell {
            /// Selected cell, anchored at the authored subject field.
            cell: I => [cell_map],
            /// Authored result-field provenance for the same cell.
            result_key: ProvenanceKey => [keep],
            /// Complete exact cell-content pattern.
            before: T => [term_map],
            /// Complete replacement cell content.
            after: T => [term_map],
        },
    }
}

/// Host gradual extra-cell clause.
pub type HostHeadRuleExtra = ProtocolHeadRuleExtra<HostHeadRuleCellReference, HostTerm>;
/// Stable gradual extra-cell clause.
pub type DescriptorHeadRuleExtra = ProtocolHeadRuleExtra<DescriptorCellReference, DescriptorTerm>;

stage_shape! {
    /// Authored descriptor for one readable computation-cell head rule.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "WireHeadRule",
        deny_unknown_fields,
        bound(
            serialize = "S::Sort: Serialize, S::Configuration: Serialize, S::HeadRuleCell: Serialize, Term<S>: Serialize, RuleCondition<S>: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Configuration: Deserialize<'de>, S::HeadRuleCell: Deserialize<'de>, Term<S>: Deserialize<'de>, RuleCondition<S>: Deserialize<'de>"
        )
    )]
    pub struct HeadRule<S: Stage> {
        /// Explicit sentence kind.
        pub sentence_kind: SentenceKind => [keep],
        /// Optional emitted K label.
        pub label: Option<DescriptorRuleLabel> => [keep],
        /// Optional priority transported from `#[k::rule(owise)]` or `#[k::rule(priority = N)]`.
        pub priority: Option<DescriptorRulePriority> => [keep],
        /// Optional check-only nondeterminism group from `#[k::rule(nondet = group)]`.
        pub nondet: Option<crate::DescriptorNondetGroup> => [keep],
        /// Complete authored head pattern.
        pub pattern_key: ProvenanceKey => [keep],
        /// Complete authored right-hand side.
        pub result_key: ProvenanceKey => [keep],
        /// Sort named by a `for Sort` rule-table header.
        pub head_sort: Option<S::Sort> => [option sort],
        /// Fixed configuration named by a `for Configuration` cell-record header.
        pub configuration: Option<S::Configuration> => [option configuration],
        /// Authored computation-cell field for a cell-record clause that matches one.
        pub computation_cell_name: Option<String> => [keep],
        /// Bindings and authored refinements in introduction order.
        pub bindings: Vec<ProtocolHeadRuleBinding<S::Sort>> => [vec protocol sort],
        /// The matched computation-cell head and its rewrite; absent only for a
        /// cell-record clause that leaves the computation cell out (KF-015).
        pub head: Option<ProtocolHeadRuleHead<Term<S>>> => [option protocol nested],
        /// Optional object-language Boolean side condition.
        pub requires: Option<RuleCondition<S>> => [option nested],
        /// Explicit non-computation-cell reads and writes.
        pub extras: Vec<ProtocolHeadRuleExtra<S::HeadRuleCell, Term<S>>> => [vec protocol head_rule_cell nested],
        /// Result-scoped existential binders (`#[k::exists]`).
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        pub existentials: Vec<crate::transport::rule::ClaimBinder<S>> => [vec nested],
        /// Optional object-Bool postcondition (`#[k::ensures]`).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub ensures: Option<RuleCondition<S>> => [option nested],
    }
    map_order: [extras, head, sentence_kind, label, priority, nondet, pattern_key, result_key, head_sort, configuration, computation_cell_name, bindings, requires, existentials, ensures];
}

/// Host descriptor emitted before configuration and cell selection.
pub type HostHeadRule = HeadRule<HostStage>;

stage_shape! {
    /// Collector-resolved head rule with a selected configuration and computation cell.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "DescriptorHeadRule",
        deny_unknown_fields,
        bound(
            serialize = "S::Sort: Serialize, S::Item: Serialize, S::Cell: Serialize, S::HeadRuleCell: Serialize, Term<S>: Serialize, RuleCondition<S>: Serialize",
            deserialize = "S::Sort: Deserialize<'de>, S::Item: Deserialize<'de>, S::Cell: Deserialize<'de>, S::HeadRuleCell: Deserialize<'de>, Term<S>: Deserialize<'de>, RuleCondition<S>: Deserialize<'de>"
        )
    )]
    pub struct ResolvedHeadRule<S: Stage> {
        /// Explicit sentence kind.
        pub sentence_kind: SentenceKind => [keep],
        /// Optional emitted K label.
        #[serde(skip_serializing_if = "Option::is_none")]
        pub label: Option<DescriptorRuleLabel> => [keep],
        /// Optional priority transported from `#[k::rule(owise)]` or `#[k::rule(priority = N)]`.
        #[serde(skip_serializing_if = "Option::is_none")]
        pub priority: Option<DescriptorRulePriority> => [keep],
        /// Optional check-only nondeterminism group from `#[k::rule(nondet = group)]`.
        #[serde(skip_serializing_if = "Option::is_none")]
        pub nondet: Option<crate::DescriptorNondetGroup> => [keep],
        /// Complete authored head pattern.
        pub pattern_key: ProvenanceKey => [keep],
        /// Complete authored right-hand side.
        pub result_key: ProvenanceKey => [keep],
        /// Sort named by a `for Sort` header, absent for a cell-record rule.
        #[serde(skip_serializing_if = "Option::is_none")]
        pub head_sort: Option<S::Sort> => [option sort],
        /// Unique fixed configuration selected by collection.
        pub configuration: S::Item => [item],
        /// Unique top-level `KCell<KSequence>` selected by collection, present
        /// exactly when the rule matches a computation-cell head.
        #[serde(skip_serializing_if = "Option::is_none")]
        pub computation_cell: Option<S::Cell> => [option cell],
        /// Bindings and authored refinements in introduction order.
        pub bindings: Vec<ProtocolHeadRuleBinding<S::Sort>> => [vec protocol sort],
        /// The matched computation-cell head and its rewrite; absent only for a
        /// cell-record clause that leaves the computation cell out (KF-015).
        #[serde(skip_serializing_if = "Option::is_none")]
        pub head: Option<ProtocolHeadRuleHead<Term<S>>> => [option protocol nested],
        /// Optional object-language Boolean side condition.
        #[serde(skip_serializing_if = "Option::is_none")]
        pub requires: Option<RuleCondition<S>> => [option nested],
        /// Explicit resolved non-computation-cell reads and writes.
        pub extras: Vec<ProtocolHeadRuleExtra<S::HeadRuleCell, Term<S>>> => [vec protocol head_rule_cell nested],
        /// Result-scoped existential binders (`#[k::exists]`).
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        pub existentials: Vec<crate::transport::rule::ClaimBinder<S>> => [vec nested],
        /// Optional object-Bool postcondition (`#[k::ensures]`).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub ensures: Option<RuleCondition<S>> => [option nested],
    }
    descriptor_from: HeadRule<DescriptorStage> {
        configuration: crate::StableItemId,
        computation_cell: Option<DescriptorCellReference>,
    }
}

/// Stable collector-resolved head rule.
pub type DescriptorHeadRule = ResolvedHeadRule<DescriptorStage>;

fn validate_nondet(
    kind: SentenceKind,
    nondet: Option<&crate::DescriptorNondetGroup>,
) -> Result<(), StateTransportError> {
    if let Some(nondet) = nondet
        && (kind != SentenceKind::Transition || !nondet.is_valid())
    {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidNondetGroup,
        ));
    }
    Ok(())
}

fn validate_owise_priority(
    kind: SentenceKind,
    priority: Option<&DescriptorRulePriority>,
) -> Result<(), StateTransportError> {
    if let Some(priority) = priority
        && (kind != SentenceKind::Transition || priority.role_for(kind).is_none())
    {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::HeadRuleOrderedFallbackPriority,
        ));
    }
    Ok(())
}

/// Existentials and ensures belong to transitions; each existential has the
/// transition roles and a fresh name, and the ensures key is `RuleEnsures#0`.
fn validate_existentials<S: crate::Stage>(
    kind: SentenceKind,
    bindings: &[ProtocolHeadRuleBinding<S::Sort>],
    existentials: &[crate::transport::rule::ClaimBinder<S>],
    ensures: Option<&RuleCondition<S>>,
) -> Result<(), StateTransportError> {
    if (!existentials.is_empty() || ensures.is_some()) && kind != SentenceKind::Transition {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidRuleExistential,
        ));
    }
    let mut names = BTreeSet::new();
    for (index, binder) in existentials.iter().enumerate() {
        let ordinal = u32::try_from(index).ok();
        if binder.name.is_empty()
            || !names.insert(binder.name.as_str())
            || bindings.iter().any(|binding| binding.name == binder.name)
            || binder.declaration_key.role() != ProvenanceRole::RuleExistentialBinder
            || binder.name_key.role() != ProvenanceRole::RuleExistentialBinderName
            || Some(binder.declaration_key.ordinal()) != ordinal
            || Some(binder.name_key.ordinal()) != ordinal
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::InvalidRuleExistential,
            ));
        }
    }
    if let Some(ensures) = ensures
        && (ensures.key.role() != ProvenanceRole::RuleEnsures || ensures.key.ordinal() != 0)
    {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidRuleExistential,
        ));
    }
    Ok(())
}

fn validate_bindings<S, I, T>(
    bindings: &[ProtocolHeadRuleBinding<S>],
    extras: &[ProtocolHeadRuleExtra<I, T>],
) -> Result<(), StateTransportError> {
    let names = bindings
        .iter()
        .map(|binding| binding.name.as_str())
        .collect::<BTreeSet<_>>();
    if names.len() != bindings.len() || names.iter().any(|name| name.is_empty()) {
        return Err(StateTransportError::DuplicateValue(
            TransportField::HeadRuleBindings,
        ));
    }
    for extra in extras {
        let introduced = match extra {
            ProtocolHeadRuleExtra::HaveMap { value_binding, .. } => value_binding,
            ProtocolHeadRuleExtra::UpdateMap { base_binding, .. } => base_binding,
            ProtocolHeadRuleExtra::RewriteCell { .. } => continue,
        };
        if !names.contains(introduced.as_str()) {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::UndeclaredHeadRuleExtraBinding,
            ));
        }
    }
    Ok(())
}

impl HostHeadRule {
    /// Validates host-only ownership and the closed binding/extra shape.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for a wrong relational item kind,
    /// malformed structural key, undeclared binding, or duplicate extra cell.
    pub fn validate(&self, item_kind: ItemKind) -> Result<(), StateTransportError> {
        let expected = self.sentence_kind.item_kind();
        if item_kind != expected {
            return Err(StateTransportError::ItemKind {
                field: TransportField::HeadAnchoredRuleDescriptor,
                expected: TransportItemKind::SentenceMatchingRelationalItem,
                actual: item_kind,
            });
        }
        validate_owise_priority(self.sentence_kind, self.priority.as_ref())?;
        validate_nondet(self.sentence_kind, self.nondet.as_ref())?;
        if self.pattern_key.role() != ProvenanceRole::RulePattern
            || self.pattern_key.ordinal() != 0
            || self.result_key.role() != ProvenanceRole::RuleResult
            || self.result_key.ordinal() != 0
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::HeadRuleStructuralProvenanceKey,
            ));
        }
        match (
            &self.head_sort,
            &self.configuration,
            &self.computation_cell_name,
        ) {
            (Some(sort), None, None)
                if sort.key.role() == ProvenanceRole::RuleType && sort.key.ordinal() == 0 => {}
            (None, Some(configuration), cell)
                if configuration.key.role() == ProvenanceRole::RuleType
                    && configuration.key.ordinal() == 0
                    && cell.as_ref().is_none_or(|cell| !cell.is_empty())
                    && cell.is_some() == self.head.is_some()
                    && (self.head.is_some() || !self.extras.is_empty()) => {}
            _ => {
                return Err(StateTransportError::InvalidTerm(
                    StateTermReason::HeadRuleHeaderOwnership,
                ));
            }
        }
        validate_bindings(&self.bindings, &self.extras)?;
        if let Some(requires) = &self.requires
            && (requires.key.role() != ProvenanceRole::RuleRequires || requires.key.ordinal() != 0)
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::HeadRuleRequiresProvenanceKey,
            ));
        }
        validate_existentials(
            self.sentence_kind,
            &self.bindings,
            &self.existentials,
            self.ensures.as_ref(),
        )?;
        let mut cells = BTreeSet::new();
        for extra in &self.extras {
            let cell = match extra {
                ProtocolHeadRuleExtra::HaveMap { cell, .. } => {
                    if cell.key.role() != ProvenanceRole::RuleLeftCellsField {
                        return Err(StateTransportError::InvalidTerm(
                            StateTermReason::MapReadCellProvenanceKey,
                        ));
                    }
                    cell
                }
                ProtocolHeadRuleExtra::UpdateMap { cell, .. } => {
                    if cell.key.role() != ProvenanceRole::RuleRightCellsField {
                        return Err(StateTransportError::InvalidTerm(
                            StateTermReason::MapUpdateCellProvenanceKey,
                        ));
                    }
                    cell
                }
                ProtocolHeadRuleExtra::RewriteCell {
                    cell, result_key, ..
                } => {
                    if cell.key.role() != ProvenanceRole::RuleLeftCellsField
                        || result_key.role() != ProvenanceRole::RuleRightCellsField
                    {
                        return Err(StateTransportError::InvalidTerm(
                            StateTermReason::OrdinaryCellRewriteProvenanceKey,
                        ));
                    }
                    cell
                }
            };
            if cell.name.is_empty() || !cells.insert(cell.name.as_str()) {
                return Err(StateTransportError::DuplicateValue(
                    TransportField::HeadRuleExtraCells,
                ));
            }
        }
        Ok(())
    }
}

impl DescriptorHeadRule {
    /// Validates stable ownership after configuration and cell resolution.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for a wrong relational item kind,
    /// invalid configuration ownership, undeclared binding, duplicate cell,
    /// or an extra that selects the computation cell.
    pub fn validate(&self, item_kind: ItemKind) -> Result<(), StateTransportError> {
        let expected = self.sentence_kind.item_kind();
        if item_kind != expected {
            return Err(StateTransportError::ItemKind {
                field: TransportField::HeadAnchoredRuleDescriptor,
                expected: TransportItemKind::SentenceMatchingRelationalItem,
                actual: item_kind,
            });
        }
        validate_owise_priority(self.sentence_kind, self.priority.as_ref())?;
        validate_nondet(self.sentence_kind, self.nondet.as_ref())?;
        if self.configuration.item_kind() != ItemKind::Configuration {
            return Err(StateTransportError::ItemKind {
                field: TransportField::HeadRuleConfiguration,
                expected: TransportItemKind::Configuration,
                actual: self.configuration.item_kind(),
            });
        }
        if self.computation_cell.is_some() != self.head.is_some()
            || (self.head.is_none() && self.extras.is_empty())
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::HeadRuleHeaderOwnership,
            ));
        }
        if let Some(computation) = &self.computation_cell
            && computation.cell.owner != self.configuration
        {
            return Err(StateTransportError::CellOwnerMismatch);
        }
        validate_bindings(&self.bindings, &self.extras)?;
        if let Some(requires) = &self.requires
            && (requires.key.role() != ProvenanceRole::RuleRequires || requires.key.ordinal() != 0)
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::HeadRuleRequiresProvenanceKey,
            ));
        }
        validate_existentials(
            self.sentence_kind,
            &self.bindings,
            &self.existentials,
            self.ensures.as_ref(),
        )?;
        let mut cells = BTreeSet::new();
        for extra in &self.extras {
            let cell = match extra {
                ProtocolHeadRuleExtra::HaveMap { cell, .. }
                | ProtocolHeadRuleExtra::UpdateMap { cell, .. }
                | ProtocolHeadRuleExtra::RewriteCell { cell, .. } => cell,
            };
            if cell.cell.owner != self.configuration
                && cell.cell.owner.item_kind() != ItemKind::Cell
            {
                return Err(StateTransportError::CellOwnerMismatch);
            }
            if self
                .computation_cell
                .as_ref()
                .is_some_and(|computation| cell.cell == computation.cell)
                || !cells.insert(cell.cell.clone())
            {
                return Err(StateTransportError::DuplicateValue(
                    TransportField::HeadRuleSelectedCells,
                ));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{
        DescriptorHeadRule, HeadRule, ProtocolHeadRuleBinding, ProtocolHeadRuleExtra,
        ProtocolHeadRuleHead, ProtocolHeadRuleResult,
    };
    use crate::stage::tests::CountingMap;
    use crate::wire::{
        WireConfigurationReference, WireHeadRuleCellReference, WireSortReference, WireTerm,
        WireTypeReference,
    };
    use crate::{
        BuiltinSort, DescriptorCellIdentity, DescriptorCellReference, DescriptorSortRef,
        DescriptorSortReference, DescriptorTerm, ItemKind, PackageId, ProvenanceKey,
        ProvenanceRole, SentenceKind, StableItemId, WireStage,
    };

    fn map_number(reference: u8, calls: &mut Vec<u8>) -> Result<u16, &'static str> {
        calls.push(reference);
        if reference == 9 {
            Err("unresolved reference")
        } else {
            Ok(u16::from(reference) + 10)
        }
    }

    #[test]
    fn binding_traversal_maps_optional_refinement_and_propagates_errors() {
        let mut calls = Vec::new();
        let mapped = ProtocolHeadRuleBinding {
            name: "value".to_owned(),
            refinement: Some(1),
        }
        .try_map_refs(&mut calls, &mut map_number)
        .unwrap();
        assert_eq!(mapped.name, "value");
        assert_eq!(mapped.refinement, Some(11));
        assert_eq!(calls, [1]);

        let absent = ProtocolHeadRuleBinding::<u8> {
            name: "other".to_owned(),
            refinement: None,
        }
        .try_map_refs(&mut calls, &mut map_number)
        .unwrap();
        assert_eq!(absent.refinement, None);
        assert_eq!(calls, [1]);

        let failure = ProtocolHeadRuleBinding {
            name: "invalid".to_owned(),
            refinement: Some(9),
        }
        .try_map_refs(&mut calls, &mut map_number);
        assert_eq!(failure, Err("unresolved reference"));
        assert_eq!(calls, [1, 9]);
    }

    #[test]
    fn head_result_traversal_maps_each_variant_and_stops_at_first_error() {
        let mut calls = Vec::new();
        let replace = ProtocolHeadRuleResult::Replace(1)
            .try_map_refs(&mut calls, &mut map_number)
            .unwrap();
        assert_eq!(replace, ProtocolHeadRuleResult::Replace(11));
        let splice = ProtocolHeadRuleResult::Splice(vec![2, 3])
            .try_map_refs(&mut calls, &mut map_number)
            .unwrap();
        assert_eq!(splice, ProtocolHeadRuleResult::Splice(vec![12, 13]));
        let erase = ProtocolHeadRuleResult::<u8>::Erase
            .try_map_refs(&mut calls, &mut map_number)
            .unwrap();
        assert_eq!(erase, ProtocolHeadRuleResult::Erase);
        assert_eq!(calls, [1, 2, 3]);
        let failure =
            ProtocolHeadRuleResult::Splice(vec![4, 9, 5]).try_map_refs(&mut calls, &mut map_number);
        assert_eq!(failure, Err("unresolved reference"));
        assert_eq!(calls, [1, 2, 3, 4, 9]);
    }

    #[test]
    fn head_extra_traversal_maps_every_reference_and_stops_at_first_error() {
        let result_key = ProvenanceKey::new(ProvenanceRole::RuleRightCellsField, 0);
        let mut calls = Vec::new();
        let have = ProtocolHeadRuleExtra::HaveMap {
            cell: 1,
            key: 2,
            value_binding: "value".to_owned(),
        }
        .try_map_refs(&mut calls, &mut map_number, &mut map_number)
        .unwrap();
        assert_eq!(
            have,
            ProtocolHeadRuleExtra::HaveMap {
                cell: 11,
                key: 12,
                value_binding: "value".to_owned(),
            }
        );
        let update = ProtocolHeadRuleExtra::UpdateMap {
            cell: 3,
            base_binding: "base".to_owned(),
            update: 4,
        }
        .try_map_refs(&mut calls, &mut map_number, &mut map_number)
        .unwrap();
        assert_eq!(
            update,
            ProtocolHeadRuleExtra::UpdateMap {
                cell: 13,
                base_binding: "base".to_owned(),
                update: 14,
            }
        );
        let rewrite = ProtocolHeadRuleExtra::RewriteCell {
            cell: 5,
            result_key: result_key.clone(),
            before: 6,
            after: 7,
        }
        .try_map_refs(&mut calls, &mut map_number, &mut map_number)
        .unwrap();
        assert_eq!(
            rewrite,
            ProtocolHeadRuleExtra::RewriteCell {
                cell: 15,
                result_key: result_key.clone(),
                before: 16,
                after: 17,
            }
        );
        assert_eq!(calls, [1, 2, 3, 4, 5, 6, 7]);
        let failure = ProtocolHeadRuleExtra::RewriteCell {
            cell: 8,
            result_key,
            before: 9,
            after: 1,
        }
        .try_map_refs(&mut calls, &mut map_number, &mut map_number);
        assert_eq!(failure, Err("unresolved reference"));
        assert_eq!(calls, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    fn wire_sort() -> WireSortReference {
        WireSortReference {
            key: ProvenanceKey::new(ProvenanceRole::RuleType, 0),
            target: WireTypeReference {
                slot: crate::wire::TypeSlot(1),
                authored_path: "Value".to_owned(),
            },
        }
    }

    fn wire_term() -> WireTerm {
        WireTerm::Anonymous {
            key: ProvenanceKey::new(ProvenanceRole::RulePattern, 0),
            sort: wire_sort(),
            spelling: "_".to_owned(),
        }
    }

    #[test]
    fn authored_head_rule_traversal_visits_each_reference_and_propagates_errors() {
        let key = ProvenanceKey::new(ProvenanceRole::RulePattern, 0);
        let rule = HeadRule::<WireStage> {
            sentence_kind: SentenceKind::Transition,
            label: None,
            priority: None,
            nondet: None,
            pattern_key: key.clone(),
            result_key: key.clone(),
            head_sort: Some(wire_sort()),
            configuration: Some(WireConfigurationReference {
                key: key.clone(),
                configuration: WireTypeReference {
                    slot: crate::wire::TypeSlot(2),
                    authored_path: "State".to_owned(),
                },
            }),
            computation_cell_name: Some("k".to_owned()),
            bindings: vec![ProtocolHeadRuleBinding {
                name: "value".to_owned(),
                refinement: Some(wire_sort()),
            }],
            head: Some(ProtocolHeadRuleHead {
                subject: wire_term(),
                result: ProtocolHeadRuleResult::Splice(vec![wire_term()]),
            }),
            requires: Some(crate::wire::WireRuleCondition {
                key: key.clone(),
                term: wire_term(),
            }),
            extras: vec![ProtocolHeadRuleExtra::RewriteCell {
                cell: WireHeadRuleCellReference {
                    key: key.clone(),
                    name: "value".to_owned(),
                },
                result_key: key,
                before: wire_term(),
                after: wire_term(),
            }],
            existentials: Vec::new(),
            ensures: None,
        };
        let original = serde_json::to_value(&rule).unwrap();
        let mut map = CountingMap::default();
        let mapped = rule.clone().try_map_refs(&mut map).unwrap();
        assert_eq!(serde_json::to_value(mapped).unwrap(), original);
        assert_eq!(
            map.calls,
            [
                "head_rule_cell",
                "sort",
                "sort",
                "sort",
                "sort",
                "sort",
                "configuration",
                "sort",
                "sort"
            ]
        );
        let mut failing = CountingMap {
            fail: Some("configuration"),
            ..CountingMap::default()
        };
        assert_eq!(
            rule.try_map_refs(&mut failing).unwrap_err(),
            "configuration"
        );
        assert_eq!(
            failing.calls,
            [
                "head_rule_cell",
                "sort",
                "sort",
                "sort",
                "sort",
                "sort",
                "configuration"
            ]
        );
    }

    fn descriptor_sort() -> DescriptorSortReference {
        DescriptorSortReference {
            key: ProvenanceKey::new(ProvenanceRole::RuleType, 0),
            sort: DescriptorSortRef::Builtin(BuiltinSort::Int),
        }
    }

    fn descriptor_term() -> DescriptorTerm {
        DescriptorTerm::Anonymous {
            key: ProvenanceKey::new(ProvenanceRole::RulePattern, 0),
            sort: descriptor_sort(),
            spelling: "_".to_owned(),
        }
    }

    #[test]
    fn resolved_head_rule_traversal_visits_selected_references_and_propagates_errors() {
        let key = ProvenanceKey::new(ProvenanceRole::RulePattern, 0);
        let package = PackageId::new("ORG-EXAMPLE", "test", "0.1.0", "workspace").unwrap();
        let configuration = StableItemId::new(
            package,
            ["configuration"],
            "State",
            ItemKind::Configuration,
            "",
        )
        .unwrap();
        let cell = DescriptorCellReference {
            key: key.clone(),
            cell: DescriptorCellIdentity {
                owner: configuration.clone(),
                field: "k".to_owned(),
            },
        };
        let rule = DescriptorHeadRule {
            sentence_kind: SentenceKind::Transition,
            label: None,
            priority: None,
            nondet: None,
            pattern_key: key.clone(),
            result_key: key.clone(),
            head_sort: Some(descriptor_sort()),
            configuration,
            computation_cell: Some(cell.clone()),
            bindings: vec![ProtocolHeadRuleBinding {
                name: "value".to_owned(),
                refinement: Some(descriptor_sort()),
            }],
            head: Some(ProtocolHeadRuleHead {
                subject: descriptor_term(),
                result: ProtocolHeadRuleResult::Replace(descriptor_term()),
            }),
            requires: Some(crate::DescriptorRuleCondition {
                key,
                term: descriptor_term(),
            }),
            extras: vec![ProtocolHeadRuleExtra::HaveMap {
                cell,
                key: descriptor_term(),
                value_binding: "value".to_owned(),
            }],
            existentials: Vec::new(),
            ensures: None,
        };
        let mut map = CountingMap::default();
        let mapped = rule.clone().try_map_refs(&mut map).unwrap();
        assert_eq!(mapped, rule);
        assert_eq!(
            map.calls,
            [
                "sort",
                "item",
                "cell",
                "sort",
                "sort",
                "sort",
                "sort",
                "head_rule_cell",
                "sort"
            ]
        );
        let mut failing = CountingMap {
            fail: Some("cell"),
            ..CountingMap::default()
        };
        assert_eq!(rule.try_map_refs(&mut failing).unwrap_err(), "cell");
        assert_eq!(failing.calls, ["sort", "item", "cell"]);
    }
}

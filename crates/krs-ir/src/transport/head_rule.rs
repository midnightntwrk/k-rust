//! Collector transport for readable rules completed at a computation-cell head.

use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

use crate::{
    DescriptorCellReference, DescriptorRuleCondition, DescriptorRuleLabel, DescriptorRulePriority,
    DescriptorSortReference, DescriptorTerm, HostConfigurationReference, HostRuleCondition,
    HostSortReference, HostTerm, ItemKind, ProvenanceKey, SentenceKind, StableItemId,
    StateTransportError,
};

/// One readable binding with an optional explicit `where name: Sort` refinement.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProtocolHeadRuleBinding<S> {
    /// Binding name in first-introduction order.
    pub name: String,
    /// Authored sort refinement, if present.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub refinement: Option<S>,
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

/// Result of rewriting one computation-cell head.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "head_result_kind",
    content = "head_result",
    rename_all = "snake_case"
)]
pub enum ProtocolHeadRuleResult<T> {
    /// Replace the matched head with one ordinary term.
    Replace(T),
    /// Splice zero or more `k![...]` items before the preserved tail.
    Splice(Vec<T>),
    /// Erase the matched head and expose the preserved tail.
    Erase,
}

/// Host head result.
pub type HostHeadRuleResult = ProtocolHeadRuleResult<HostTerm>;
/// Stable head result.
pub type DescriptorHeadRuleResult = ProtocolHeadRuleResult<DescriptorTerm>;

/// One explicit gradual extra-cell clause.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "extra_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ProtocolHeadRuleExtra<I, T> {
    /// Failable preserved map-item match (`have cell[key -> let value]`).
    HaveMap {
        /// Selected map cell.
        cell: I,
        /// Required map key.
        key: T,
        /// Value binding introduced by the item match.
        value_binding: String,
    },
    /// Simultaneous whole-map replacement by an ordinary update term.
    UpdateMap {
        /// Selected map cell.
        cell: I,
        /// Implicit binding for the complete pre-state map.
        base_binding: String,
        /// Complete registered `map::update(base, key, value)` application.
        update: T,
    },
    /// Simultaneous exact rewrite of one ordinary fixed leaf cell.
    RewriteCell {
        /// Selected cell, anchored at the authored subject field.
        cell: I,
        /// Authored result-field provenance for the same cell.
        result_key: ProvenanceKey,
        /// Complete exact cell-content pattern.
        before: T,
        /// Complete replacement cell content.
        after: T,
    },
}

/// Host gradual extra-cell clause.
pub type HostHeadRuleExtra = ProtocolHeadRuleExtra<HostHeadRuleCellReference, HostTerm>;
/// Stable gradual extra-cell clause.
pub type DescriptorHeadRuleExtra = ProtocolHeadRuleExtra<DescriptorCellReference, DescriptorTerm>;

/// Host descriptor emitted for one bare `rules! { for Sort; ... }` clause.
#[derive(Clone, Debug)]
pub struct HostHeadRule {
    /// Explicit sentence kind.
    pub sentence_kind: SentenceKind,
    /// Optional emitted K label.
    pub label: Option<DescriptorRuleLabel>,
    /// Optional ordered-fallback priority transported from `#[k::rule(owise)]`.
    pub priority: Option<DescriptorRulePriority>,
    /// Complete authored head pattern.
    pub pattern_key: ProvenanceKey,
    /// Complete authored right-hand side.
    pub result_key: ProvenanceKey,
    /// Sort named by a `for Sort` rule-table header.
    pub head_sort: Option<HostSortReference>,
    /// Fixed configuration named by a `for Configuration` cell-record header.
    pub configuration: Option<HostConfigurationReference>,
    /// Authored computation-cell field for a cell-record clause.
    pub computation_cell_name: Option<String>,
    /// Bindings and authored refinements in introduction order.
    pub bindings: Vec<HostHeadRuleBinding>,
    /// One matched computation-cell head item.
    pub subject: HostTerm,
    /// Replacement, splice, or erasure before the implicit preserved tail.
    pub result: HostHeadRuleResult,
    /// Optional object-language Boolean side condition.
    pub requires: Option<HostRuleCondition>,
    /// Explicit non-computation-cell reads and writes.
    pub extras: Vec<HostHeadRuleExtra>,
}

/// Stable collector-resolved head-anchored rule.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorHeadRule {
    /// Explicit sentence kind.
    pub sentence_kind: SentenceKind,
    /// Optional emitted K label.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<DescriptorRuleLabel>,
    /// Optional ordered-fallback priority transported from `#[k::rule(owise)]`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub priority: Option<DescriptorRulePriority>,
    /// Complete authored head pattern.
    pub pattern_key: ProvenanceKey,
    /// Complete authored right-hand side.
    pub result_key: ProvenanceKey,
    /// Sort named by a `for Sort` header, absent for a cell-record rule.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub head_sort: Option<DescriptorSortReference>,
    /// Unique fixed configuration selected by collection.
    pub configuration: StableItemId,
    /// Unique top-level `KCell<KSequence>` selected by collection.
    pub computation_cell: DescriptorCellReference,
    /// Bindings and authored refinements in introduction order.
    pub bindings: Vec<DescriptorHeadRuleBinding>,
    /// One matched computation-cell head item.
    pub subject: DescriptorTerm,
    /// Replacement, splice, or erasure before the implicit preserved tail.
    pub result: DescriptorHeadRuleResult,
    /// Optional object-language Boolean side condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub requires: Option<DescriptorRuleCondition>,
    /// Explicit resolved non-computation-cell reads and writes.
    pub extras: Vec<DescriptorHeadRuleExtra>,
}

fn sentence_item_kind(kind: SentenceKind) -> ItemKind {
    match kind {
        SentenceKind::Transition => ItemKind::Rule,
        SentenceKind::Equation => ItemKind::Equation,
        SentenceKind::Simplification => ItemKind::Simplification,
        SentenceKind::Alias => ItemKind::Alias,
        SentenceKind::Claim => ItemKind::Claim,
    }
}

fn validate_owise_priority(
    kind: SentenceKind,
    priority: Option<&DescriptorRulePriority>,
) -> Result<(), StateTransportError> {
    if let Some(priority) = priority
        && (kind != SentenceKind::Transition
            || priority.key.role() != "rule_owise"
            || priority.key.ordinal() != 0
            || priority.value != 200)
    {
        return Err(StateTransportError::InvalidTerm(
            "head-rule ordered fallback priority",
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
        return Err(StateTransportError::DuplicateValue("head-rule bindings"));
    }
    for extra in extras {
        let introduced = match extra {
            ProtocolHeadRuleExtra::HaveMap { value_binding, .. } => value_binding,
            ProtocolHeadRuleExtra::UpdateMap { base_binding, .. } => base_binding,
            ProtocolHeadRuleExtra::RewriteCell { .. } => continue,
        };
        if !names.contains(introduced.as_str()) {
            return Err(StateTransportError::InvalidTerm(
                "head-rule extra references an undeclared binding",
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
        let expected = sentence_item_kind(self.sentence_kind);
        if item_kind != expected {
            return Err(StateTransportError::ItemKind {
                field: "head-anchored rule descriptor",
                expected: "sentence-matching relational item",
                actual: item_kind,
            });
        }
        validate_owise_priority(self.sentence_kind, self.priority.as_ref())?;
        if self.pattern_key.role() != "rule_pattern"
            || self.pattern_key.ordinal() != 0
            || self.result_key.role() != "rule_result"
            || self.result_key.ordinal() != 0
        {
            return Err(StateTransportError::InvalidTerm(
                "head-rule structural provenance key",
            ));
        }
        match (
            &self.head_sort,
            &self.configuration,
            &self.computation_cell_name,
        ) {
            (Some(sort), None, None)
                if sort.key.role() == "rule_type" && sort.key.ordinal() == 0 => {}
            (None, Some(configuration), Some(cell))
                if configuration.key.role() == "rule_type"
                    && configuration.key.ordinal() == 0
                    && !cell.is_empty() => {}
            _ => {
                return Err(StateTransportError::InvalidTerm(
                    "head-rule header ownership",
                ));
            }
        }
        validate_bindings(&self.bindings, &self.extras)?;
        if let Some(requires) = &self.requires
            && (requires.key.role() != "rule_requires" || requires.key.ordinal() != 0)
        {
            return Err(StateTransportError::InvalidTerm(
                "head-rule requires provenance key",
            ));
        }
        let mut cells = BTreeSet::new();
        for extra in &self.extras {
            let cell = match extra {
                ProtocolHeadRuleExtra::HaveMap { cell, .. } => {
                    if cell.key.role() != "rule_left_cells_field" {
                        return Err(StateTransportError::InvalidTerm(
                            "map read cell provenance key",
                        ));
                    }
                    cell
                }
                ProtocolHeadRuleExtra::UpdateMap { cell, .. } => {
                    if cell.key.role() != "rule_right_cells_field" {
                        return Err(StateTransportError::InvalidTerm(
                            "map update cell provenance key",
                        ));
                    }
                    cell
                }
                ProtocolHeadRuleExtra::RewriteCell {
                    cell, result_key, ..
                } => {
                    if cell.key.role() != "rule_left_cells_field"
                        || result_key.role() != "rule_right_cells_field"
                    {
                        return Err(StateTransportError::InvalidTerm(
                            "ordinary cell rewrite provenance key",
                        ));
                    }
                    cell
                }
            };
            if cell.name.is_empty() || !cells.insert(cell.name.as_str()) {
                return Err(StateTransportError::DuplicateValue("head-rule extra cells"));
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
        let expected = sentence_item_kind(self.sentence_kind);
        if item_kind != expected {
            return Err(StateTransportError::ItemKind {
                field: "head-anchored rule descriptor",
                expected: "sentence-matching relational item",
                actual: item_kind,
            });
        }
        validate_owise_priority(self.sentence_kind, self.priority.as_ref())?;
        if self.configuration.item_kind() != ItemKind::Configuration {
            return Err(StateTransportError::ItemKind {
                field: "head-rule configuration",
                expected: "Configuration",
                actual: self.configuration.item_kind(),
            });
        }
        if self.computation_cell.cell.owner != self.configuration {
            return Err(StateTransportError::CellOwnerMismatch);
        }
        validate_bindings(&self.bindings, &self.extras)?;
        if let Some(requires) = &self.requires
            && (requires.key.role() != "rule_requires" || requires.key.ordinal() != 0)
        {
            return Err(StateTransportError::InvalidTerm(
                "head-rule requires provenance key",
            ));
        }
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
            if cell.cell == self.computation_cell.cell || !cells.insert(cell.cell.clone()) {
                return Err(StateTransportError::DuplicateValue(
                    "head-rule selected cells",
                ));
            }
        }
        Ok(())
    }
}

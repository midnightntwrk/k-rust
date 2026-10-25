//! Collector transport for readable rules completed at a computation-cell head.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use super::detail::{StateTermReason, TransportField, TransportItemKind};
use super::keys::{TermKeying, WireKeys};
use super::rule::{ClaimBinder, EvaluationStep, ValidationSide, collect_state_keys};
use super::validation::ValidationStage;
use crate::stage::{protocol_shape, stage_shape};
use crate::transport::grammar::{RuleCondition, Term};

use crate::{
    DescriptorCellReference, DescriptorRuleLabel, DescriptorRulePriority, DescriptorSortReference,
    DescriptorStage, DescriptorTerm, HostSortReference, HostStage, HostTerm, ItemKind,
    ProvenanceKey, ProvenanceRole, RuleSide, SentenceKind, Stage, StateTransportError,
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
        Splice(value: ProtocolHeadRuleSplice<T> => [nested term_map]),
        /// Erase the matched head and expose the preserved tail.
        Erase,
    }
}

protocol_shape! {
    /// The items a head result splices before the preserved tail,
    /// `k: [x, y, ..]`, with the keys of the sequence and of its items.
    ///
    /// The keys are those of the nodes the clause's sentence keyed. A
    /// splice the collector reads from a list cell written on the
    /// computation cell denotes a list value and its elements, which the
    /// sentence keyed as no sequence, so it carries none.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolHeadRuleSplice<T => term_map => U> {
        /// The spliced sequence's provenance, `rule_right_k_sequence_payload`.
        #[serde(default = "Option::default", skip_serializing_if = "Option::is_none")]
        pub payload_key: Option<ProvenanceKey> => [keep],
        /// The spliced items, front first.
        pub items: Vec<ProtocolHeadRuleSpliceItem<T>> => [vec nested term_map],
    }
}

protocol_shape! {
    /// One spliced item of a head result.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolHeadRuleSpliceItem<T => term_map => U> {
        /// The item's provenance, `rule_right_k_sequence_item`.
        #[serde(default = "Option::default", skip_serializing_if = "Option::is_none")]
        pub key: Option<ProvenanceKey> => [keep],
        /// The item's term.
        pub value: T => [term_map],
    }
}

impl<T> ProtocolHeadRuleSplice<T> {
    /// The spliced items' terms, front first.
    pub fn terms(&self) -> impl Iterator<Item = &T> {
        self.items.iter().map(|item| &item.value)
    }

    /// The spliced items' terms, front first, for rewriting.
    pub fn terms_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.items.iter_mut().map(|item| &mut item.value)
    }

    /// The spliced items' terms, front first, without their keys.
    #[must_use]
    pub fn into_terms(self) -> Vec<T> {
        self.items.into_iter().map(|item| item.value).collect()
    }
}

protocol_shape! {
    /// The matched computation-cell items of a readable rule and their
    /// rewrite: `[p1, .., pn, ..]` matches at least `n` items and keeps the
    /// rest, `[p1, .., pn]` (`exact`) matches exactly `n`.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolHeadRuleHead<T => term_map => U> {
        /// The matched items, front first; at least one unless `exact`.
        pub items: Vec<T> => [vec term_map],
        /// Whether the pattern and the result name the whole cell, with no
        /// preserved tail.
        #[serde(default, skip_serializing_if = "core::ops::Not::not")]
        pub exact: bool => [keep],
        /// Replacement, splice, or erasure of the matched items, before the
        /// preserved tail unless `exact`; absent when the result leaves the
        /// cell out, which only reads it.
        #[serde(default = "Option::default", skip_serializing_if = "Option::is_none")]
        pub result: Option<ProtocolHeadRuleResult<T>> => [option nested term_map],
    }
    map_order: [result, items, exact];
}

/// Host head result.
pub type HostHeadRuleResult = ProtocolHeadRuleResult<HostTerm>;
/// Stable head result.
pub type DescriptorHeadRuleResult = ProtocolHeadRuleResult<DescriptorTerm>;

protocol_shape! {
    /// One map entry a readable rule requires and binds the value of.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolHeadRuleMapEntry<T => term_map => U> {
        /// Exact key-expression provenance, `rule_left_map_key`.
        pub key_key: ProvenanceKey => [keep],
        /// Required map key.
        pub key: T => [term_map],
        /// Exact value-binder provenance, `rule_left_map_value`.
        pub value_key: ProvenanceKey => [keep],
        /// Value binding introduced by the item match.
        pub value_binding: String => [keep],
    }
}

protocol_shape! {
    /// The rest of one side of a list cell: a cons list's (F6) or K's
    /// builtin `List`'s.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(
        tag = "list_rest_kind",
        content = "list_rest",
        rename_all = "snake_case"
    )]
    pub enum ProtocolHeadRuleListRest<T => term_map => U> {
        /// No rest: the list ends after the elements (`[a, b]`).
        Exact,
        /// The anonymous `..`: one rest, the same on both sides of the rule,
        /// as the computation cell's.
        Shared,
        /// A named rest: the binder of `rest @ ..` in the pattern, the term
        /// of `..t` in the result.
        Term(value: T => [term_map]),
    }
}

protocol_shape! {
    /// One side of a list cell: a cons list's (F6) or K's builtin `List`'s.
    /// The elements before the rest, front first, the rest, and the
    /// elements after it, which only a builtin `List` has: a cons list is
    /// built from its front.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolHeadRuleList<T => term_map => U> {
        /// The elements before the rest, front first.
        pub items: Vec<T> => [vec term_map],
        /// What follows those elements.
        pub rest: ProtocolHeadRuleListRest<T> => [nested term_map],
        /// The elements after the rest, front first; empty when the rest is
        /// [`ProtocolHeadRuleListRest::Exact`].
        pub back: Vec<T> => [vec term_map],
    }
}

impl<T> ProtocolHeadRuleList<T> {
    /// The elements before the rest, a named rest's term, then the elements
    /// after it, in order.
    #[must_use]
    pub fn terms(&self) -> Vec<&T> {
        let rest = match &self.rest {
            ProtocolHeadRuleListRest::Term(rest) => Some(rest),
            ProtocolHeadRuleListRest::Exact | ProtocolHeadRuleListRest::Shared => None,
        };
        self.items.iter().chain(rest).chain(&self.back).collect()
    }

    /// The terms in [`Self::terms`] order, for rewriting.
    pub fn terms_mut(&mut self) -> Vec<&mut T> {
        let rest = match &mut self.rest {
            ProtocolHeadRuleListRest::Term(rest) => Some(rest),
            ProtocolHeadRuleListRest::Exact | ProtocolHeadRuleListRest::Shared => None,
        };
        self.items
            .iter_mut()
            .chain(rest)
            .chain(&mut self.back)
            .collect()
    }
}

protocol_shape! {
    /// One explicit gradual extra-cell clause.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(tag = "extra_kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum ProtocolHeadRuleExtra<I => cell_map => J, T => term_map => U> {
        /// Failable preserved match of one or more map entries
        /// (`have cell[key -> let value]`, `cell: { k1 -> v1, k2 -> v2, .. }`).
        /// The entries are distinct items of the map, so their keys differ.
        HaveMap {
            /// Selected map cell.
            cell: I => [cell_map],
            /// The matched entries, at least one, in authored order.
            entries: Vec<ProtocolHeadRuleMapEntry<T>> => [vec nested term_map],
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
        /// Exact match of one ordinary fixed cell, simultaneously rewritten
        /// when the result restates it and read only when the result leaves
        /// it out.
        RewriteCell {
            /// Selected cell, anchored at the authored subject field.
            cell: I => [cell_map],
            /// Authored result-field provenance for the same cell, absent
            /// when the result leaves the cell out (it is then read only).
            #[serde(default = "Option::default", skip_serializing_if = "Option::is_none")]
            result_key: Option<ProvenanceKey> => [keep],
            /// Complete exact cell-content pattern.
            before: T => [term_map],
            /// Complete replacement cell content, absent for a read.
            #[serde(default = "Option::default", skip_serializing_if = "Option::is_none")]
            after: Option<T> => [option term_map],
        },
        /// An optional (`?`) or collection (`*`) cell (KF-023): `Some(..)`,
        /// `None`, or an instance list, matched and possibly rewritten.
        RewriteState {
            /// Selected cell, anchored at the authored subject field.
            cell: I => [cell_map],
            /// Authored result-field provenance, absent when the result
            /// leaves the cell out (it is then read only).
            #[serde(default = "Option::default", skip_serializing_if = "Option::is_none")]
            result_key: Option<ProvenanceKey> => [keep],
            /// The matched state.
            before: crate::ProtocolRuleStateTerm<T> => [nested term_map],
            /// The rewritten state.
            #[serde(default = "Option::default", skip_serializing_if = "Option::is_none")]
            after: Option<crate::ProtocolRuleStateTerm<T>> => [option nested term_map],
        },
        /// A cell of a cons-list sort written in list notation (F6),
        /// `stack: [a, b, ..] => stack: [c, ..]`: matched, and rewritten
        /// when the result restates it. Semantic lowering builds the cell's
        /// constructor terms from the cell's declared sort.
        RewriteList {
            /// Selected cell, anchored at the authored subject field.
            cell: I => [cell_map],
            /// Authored result-field provenance, absent when the result
            /// leaves the cell out (it is then read only).
            #[serde(default = "Option::default", skip_serializing_if = "Option::is_none")]
            result_key: Option<ProvenanceKey> => [keep],
            /// The matched list.
            before: ProtocolHeadRuleList<T> => [nested term_map],
            /// The rewritten list.
            #[serde(default = "Option::default", skip_serializing_if = "Option::is_none")]
            after: Option<ProtocolHeadRuleList<T>> => [option nested term_map],
        },
    }
}

protocol_shape! {
    /// The List-collection reading of a readable record clause whose
    /// bracketed cell value reads both as the computation cell's
    /// `[head, ..]` and as a List collection's front instances (KF-023):
    /// `job: [Job { payload: p }, ..]`. The rule is carried in its
    /// computation-cell reading; the collector, which knows the cell's
    /// declared type, replaces the head by this extra when the cell is a
    /// collection. The instance children reuse the head record's terms and
    /// keys.
    #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct ProtocolHeadRuleBracketAlternative<S => sort_map => U, I => cell_map => J, T => term_map => V> {
        /// The clause's bindings in this reading, in introduction order:
        /// instance labels are not bindings.
        pub bindings: Vec<ProtocolHeadRuleBinding<S>> => [vec nested sort_map],
        /// The collection cell's state extra.
        pub extra: ProtocolHeadRuleExtra<I, T> => [nested cell_map term_map],
    }
}

/// Host gradual extra-cell clause.
pub type HostHeadRuleExtra = ProtocolHeadRuleExtra<HostHeadRuleCellReference, HostTerm>;
/// Host List-collection reading of an ambiguous bracketed cell value.
pub type HostHeadRuleBracketAlternative =
    ProtocolHeadRuleBracketAlternative<HostSortReference, HostHeadRuleCellReference, HostTerm>;
/// Host map entry of a map read.
pub type HostHeadRuleMapEntry = ProtocolHeadRuleMapEntry<HostTerm>;
/// Stable map entry of a map read.
pub type DescriptorHeadRuleMapEntry = ProtocolHeadRuleMapEntry<DescriptorTerm>;
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
        /// The result's type, `rule_result_type`: the header's sort or
        /// configuration types the result as it types the subject.
        pub result_type_key: ProvenanceKey => [keep],
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
        /// Fresh binders of a transition (`#[k::fresh]`), K's `!X`: values the step draws from the generated counter.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        pub fresh: Vec<crate::transport::rule::ClaimBinder<S>> => [vec nested],
        /// The `heat` or `cool` key of a transition (KF-014).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub evaluation: Option<crate::transport::rule::EvaluationStep<S>> => [option nested],
        /// The List-collection reading of a bracketed cell value that also
        /// reads as the computation cell's head (KF-023); the collector keeps
        /// one reading by the cell's declared type.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub bracket_alternative: Option<ProtocolHeadRuleBracketAlternative<S::Sort, S::HeadRuleCell, Term<S>>> => [option protocol sort head_rule_cell nested],
        /// The modality and flags of a readable claim (`k::claims!`, F7),
        /// present exactly for a claim; its existentials and ensures are the
        /// rule's own.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub claim: Option<HeadRuleClaim> => [keep],
    }
    map_order: [extras, head, sentence_kind, label, priority, nondet, pattern_key, result_key, head_sort, configuration, result_type_key, computation_cell_name, bindings, requires, existentials, ensures, fresh, evaluation, bracket_alternative, claim];
}

/// Host descriptor emitted before configuration and cell selection.
pub type HostHeadRule = HeadRule<HostStage>;

/// The claim metadata of a readable claim clause (`k::claims!`, F7): its
/// reachability modality and flags. A readable claim's binders are the
/// rule's inferred bindings and its existentials and ensures the rule's
/// own, so they are not repeated here.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HeadRuleClaim {
    /// Exact modality provenance.
    pub modality_key: ProvenanceKey,
    /// Exactly one reachability modality.
    pub modality: crate::ClaimModality,
    /// Optional circularity marker provenance.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub circularity_key: Option<ProvenanceKey>,
    /// Optional trusted marker provenance: the claim is assumed without proof.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trusted_key: Option<ProvenanceKey>,
}

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
        /// The result's type, `rule_result_type`: the header's sort or
        /// configuration types the result as it types the subject.
        pub result_type_key: ProvenanceKey => [keep],
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
        /// Fresh binders of a transition (`#[k::fresh]`), K's `!X`: values the step draws from the generated counter.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        pub fresh: Vec<crate::transport::rule::ClaimBinder<S>> => [vec nested],
        /// The `heat` or `cool` key of a transition (KF-014).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub evaluation: Option<crate::transport::rule::EvaluationStep<S>> => [option nested],
        /// The modality and flags of a readable claim (F7).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        pub claim: Option<HeadRuleClaim> => [keep],
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

/// A readable claim (F7) carries its modality and flags, a transition none;
/// a claim states whole configurations, so it is a cell-record clause, and
/// its keys have the claim roles.
fn validate_claim(
    kind: SentenceKind,
    claim: Option<&HeadRuleClaim>,
    term_table: bool,
) -> Result<(), StateTransportError> {
    let valid = match (kind, claim) {
        (SentenceKind::Transition, None) => true,
        (SentenceKind::Claim, Some(claim)) => {
            !term_table
                && claim.modality_key.role() == ProvenanceRole::ClaimModality
                && claim
                    .circularity_key
                    .as_ref()
                    .is_none_or(|key| key.role() == ProvenanceRole::ClaimCircularity)
                && claim
                    .trusted_key
                    .as_ref()
                    .is_none_or(|key| key.role() == ProvenanceRole::ClaimTrusted)
                && !(claim.modality == crate::ClaimModality::OnePath
                    && claim.circularity_key.is_some())
                && !(claim.circularity_key.is_some() && claim.trusted_key.is_some())
        }
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidReadableClaim,
        ))
    }
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

/// Existentials and ensures belong to transitions and readable claims; each
/// existential has the readable roles and a fresh name, and the ensures key
/// is `RuleEnsures#0`.
fn validate_existentials<S: crate::Stage>(
    kind: SentenceKind,
    bindings: &[ProtocolHeadRuleBinding<S::Sort>],
    existentials: &[crate::transport::rule::ClaimBinder<S>],
    ensures: Option<&RuleCondition<S>>,
) -> Result<(), StateTransportError> {
    if (!existentials.is_empty() || ensures.is_some())
        && !matches!(kind, SentenceKind::Transition | SentenceKind::Claim)
    {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidRuleExistential,
        ));
    }
    let mut names = BTreeSet::new();
    for binder in existentials {
        if binder.name.is_empty()
            || !names.insert(binder.name.as_str())
            || bindings.iter().any(|binding| binding.name == binder.name)
            || binder.declaration_key.role() != ProvenanceRole::RuleExistentialBinder
            || binder.name_key.role() != ProvenanceRole::RuleExistentialBinderName
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

/// A heat or cool key belongs to a transition without priority, nondet
/// group, or fresh binders (KF-014); whether its hole is a subject binding
/// is a semantic check with a source diagnostic.
fn validate_evaluation<S: crate::Stage>(
    kind: SentenceKind,
    priority: Option<&DescriptorRulePriority>,
    nondet: Option<&crate::DescriptorNondetGroup>,
    fresh: &[crate::transport::rule::ClaimBinder<S>],
    evaluation: Option<&crate::transport::rule::EvaluationStep<S>>,
    result_key: impl Fn(&S::Sort) -> &ProvenanceKey,
) -> Result<(), StateTransportError> {
    if let Some(step) = evaluation
        && (kind != SentenceKind::Transition
            || step.kind == crate::EvaluationKind::Context
            || priority.is_some()
            || nondet.is_some()
            || !fresh.is_empty()
            || !step.has_valid_roles(result_key))
    {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidEvaluationStep,
        ));
    }
    Ok(())
}

/// Fresh binders belong to transitions; each has the transition roles and a
/// name distinct from every subject binding and existential.
fn validate_fresh<S: crate::Stage>(
    kind: SentenceKind,
    bindings: &[ProtocolHeadRuleBinding<S::Sort>],
    existentials: &[crate::transport::rule::ClaimBinder<S>],
    fresh: &[crate::transport::rule::ClaimBinder<S>],
) -> Result<(), StateTransportError> {
    if !fresh.is_empty() && kind != SentenceKind::Transition {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::InvalidRuleFresh,
        ));
    }
    let mut names = BTreeSet::new();
    for binder in fresh {
        if binder.name.is_empty()
            || !names.insert(binder.name.as_str())
            || bindings.iter().any(|binding| binding.name == binder.name)
            || existentials
                .iter()
                .any(|existential| existential.name == binder.name)
            || binder.declaration_key.role() != ProvenanceRole::RuleFreshBinder
            || binder.name_key.role() != ProvenanceRole::RuleFreshBinderName
        {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::InvalidRuleFresh,
            ));
        }
    }
    Ok(())
}

/// A readable optional or collection extra pairs states of one family: `Some`
/// or `None` on both sides, or an instance list on both sides.
fn readable_state_extra<T>(
    before: &crate::ProtocolRuleStateTerm<T>,
    after: Option<&crate::ProtocolRuleStateTerm<T>>,
) -> bool {
    use crate::ProtocolRuleStateTerm as State;
    let optional = |state: &State<T>| matches!(state, State::Present { .. } | State::Absent);
    match (before, after) {
        (State::Instances(_), None | Some(State::Instances(_))) => true,
        (before, after) => optional(before) && after.is_none_or(optional),
    }
}

/// A list cell has a result key exactly when it is rewritten, its anonymous
/// `..` is one rest on both sides (a rewritten list keeps it exactly when
/// the matched one has it), and each side has elements after its rest only
/// when it has a rest.
fn list_extra<T>(
    result_key: Option<&ProvenanceKey>,
    before: &ProtocolHeadRuleList<T>,
    after: Option<&ProtocolHeadRuleList<T>>,
) -> bool {
    let shared =
        |list: &ProtocolHeadRuleList<T>| matches!(list.rest, ProtocolHeadRuleListRest::Shared);
    let back = |list: &ProtocolHeadRuleList<T>| {
        list.back.is_empty() || !matches!(list.rest, ProtocolHeadRuleListRest::Exact)
    };
    result_key.is_some() == after.is_some()
        && back(before)
        && after.is_none_or(|after| shared(before) == shared(after) && back(after))
}

/// Whether an extra that is a cons-list cell pairs its rests and its result
/// key ([`list_extra`]); every other extra does.
fn list_pairs<I, T>(extra: &ProtocolHeadRuleExtra<I, T>) -> bool {
    match extra {
        ProtocolHeadRuleExtra::RewriteList {
            result_key,
            before,
            after,
            ..
        } => list_extra(result_key.as_ref(), before, after.as_ref()),
        _ => true,
    }
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
            ProtocolHeadRuleExtra::HaveMap { entries, .. } => {
                if entries.is_empty() {
                    return Err(StateTransportError::InvalidTerm(
                        StateTermReason::EmptyMapRead,
                    ));
                }
                entries
                    .iter()
                    .map(|entry| entry.value_binding.as_str())
                    .collect()
            }
            ProtocolHeadRuleExtra::UpdateMap { base_binding, .. } => vec![base_binding.as_str()],
            ProtocolHeadRuleExtra::RewriteCell { .. }
            | ProtocolHeadRuleExtra::RewriteState { .. }
            | ProtocolHeadRuleExtra::RewriteList { .. } => continue,
        };
        if introduced.iter().any(|name| !names.contains(name)) {
            return Err(StateTransportError::InvalidTerm(
                StateTermReason::UndeclaredHeadRuleExtraBinding,
            ));
        }
    }
    Ok(())
}

/// An open computation-cell pattern matches at least one item (`[..]` is
/// rejected: it would match any computation); a `for Sort` table's head is
/// one item that the rule rewrites, never a whole cell or a read.
fn validate_head<T>(
    head: Option<&ProtocolHeadRuleHead<T>>,
    term_table: bool,
) -> Result<(), StateTransportError> {
    if let Some(head) = head
        && ((head.items.is_empty() && !head.exact)
            || (term_table && (head.items.len() != 1 || head.exact || head.result.is_none())))
    {
        return Err(StateTransportError::InvalidTerm(
            StateTermReason::HeadRuleComputationItems,
        ));
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
    #[expect(
        clippy::too_many_lines,
        reason = "The host head rule is checked in one ordered pass over its keys and binders."
    )]
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
        validate_claim(
            self.sentence_kind,
            self.claim.as_ref(),
            self.head_sort.is_some(),
        )?;
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
        validate_head(self.head.as_ref(), self.head_sort.is_some())?;
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
        validate_fresh(
            self.sentence_kind,
            &self.bindings,
            &self.existentials,
            &self.fresh,
        )?;
        validate_evaluation(
            self.sentence_kind,
            self.priority.as_ref(),
            self.nondet.as_ref(),
            &self.fresh,
            self.evaluation.as_ref(),
            |sort| &sort.key,
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
                    cell,
                    result_key,
                    after,
                    ..
                } => {
                    if cell.key.role() != ProvenanceRole::RuleLeftCellsField
                        || result_key
                            .as_ref()
                            .is_some_and(|key| key.role() != ProvenanceRole::RuleRightCellsField)
                        || result_key.is_some() != after.is_some()
                    {
                        return Err(StateTransportError::InvalidTerm(
                            StateTermReason::OrdinaryCellRewriteProvenanceKey,
                        ));
                    }
                    cell
                }
                ProtocolHeadRuleExtra::RewriteState {
                    cell,
                    result_key,
                    before,
                    after,
                } => {
                    if cell.key.role() != ProvenanceRole::RuleLeftCellsField
                        || result_key
                            .as_ref()
                            .is_some_and(|key| key.role() != ProvenanceRole::RuleRightCellsField)
                        || result_key.is_some() != after.is_some()
                        || !readable_state_extra(before, after.as_ref())
                    {
                        return Err(StateTransportError::InvalidTerm(
                            StateTermReason::InvalidReadableStateExtra,
                        ));
                    }
                    cell
                }
                ProtocolHeadRuleExtra::RewriteList {
                    cell,
                    result_key,
                    before,
                    after,
                } => {
                    if cell.key.role() != ProvenanceRole::RuleLeftCellsField
                        || result_key
                            .as_ref()
                            .is_some_and(|key| key.role() != ProvenanceRole::RuleRightCellsField)
                        || !list_extra(result_key.as_ref(), before, after.as_ref())
                    {
                        return Err(StateTransportError::InvalidTerm(
                            StateTermReason::InvalidListCell,
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
        if let Some(alternative) = &self.bracket_alternative {
            // The List reading replaces the reading of the same cell the
            // clause took: the head, when it names the computation cell, or
            // the cell's list elements.
            let ProtocolHeadRuleExtra::RewriteState {
                cell,
                result_key,
                before,
                after,
            } = &alternative.extra
            else {
                return Err(StateTransportError::InvalidTerm(
                    StateTermReason::InvalidReadableStateExtra,
                ));
            };
            let replaces_head = self.head.is_some()
                && self.computation_cell_name.as_deref() == Some(cell.name.as_str());
            let replaces_list = self.extras.iter().any(|extra| {
                matches!(
                    extra,
                    ProtocolHeadRuleExtra::RewriteList { cell: list, .. }
                        if list.name == cell.name
                )
            });
            if !(replaces_list || replaces_head && !cells.contains(cell.name.as_str()))
                || cell.key.role() != ProvenanceRole::RuleLeftCellsField
                || result_key
                    .as_ref()
                    .is_some_and(|key| key.role() != ProvenanceRole::RuleRightCellsField)
                || result_key.is_some() != after.is_some()
                || !matches!(before, crate::ProtocolRuleStateTerm::Instances(_))
                || !readable_state_extra(before, after.as_ref())
            {
                return Err(StateTransportError::InvalidTerm(
                    StateTermReason::InvalidReadableStateExtra,
                ));
            }
            validate_bindings(
                &alternative.bindings,
                &[] as &[ProtocolHeadRuleExtra<HostHeadRuleCellReference, HostTerm>],
            )?;
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
        validate_claim(
            self.sentence_kind,
            self.claim.as_ref(),
            self.head_sort.is_some(),
        )?;
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
        // The computation cell may sit inside a nested cell, such as the
        // `<k>` of each `<thread>` instance (KF-023).
        if let Some(computation) = &self.computation_cell
            && computation.cell.owner != self.configuration
            && computation.cell.owner.item_kind() != ItemKind::Cell
        {
            return Err(StateTransportError::CellOwnerMismatch);
        }
        validate_head(self.head.as_ref(), self.head_sort.is_some())?;
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
        validate_fresh(
            self.sentence_kind,
            &self.bindings,
            &self.existentials,
            &self.fresh,
        )?;
        validate_evaluation(
            self.sentence_kind,
            self.priority.as_ref(),
            self.nondet.as_ref(),
            &self.fresh,
            self.evaluation.as_ref(),
            |sort| &sort.key,
        )?;
        let mut cells = BTreeSet::new();
        for extra in &self.extras {
            let cell = match extra {
                ProtocolHeadRuleExtra::HaveMap { cell, .. }
                | ProtocolHeadRuleExtra::UpdateMap { cell, .. }
                | ProtocolHeadRuleExtra::RewriteCell { cell, .. }
                | ProtocolHeadRuleExtra::RewriteState { cell, .. }
                | ProtocolHeadRuleExtra::RewriteList { cell, .. } => cell,
            };
            if !list_pairs(extra) {
                return Err(StateTransportError::InvalidTerm(
                    StateTermReason::InvalidListCell,
                ));
            }
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

impl HostHeadRule {
    /// Checks that the clause's keys are exactly `anchors`, its descriptor's:
    /// each key field has its field's role and defines its key once, and the
    /// fixed declaration key is the rule clause's or the claim clause's.
    ///
    /// The check reads the clause as the expander built it. The collector
    /// then keeps one of a bracketed value's two readings, moves a cell's
    /// list to the computation cell's head or back, and keys the cells it so
    /// writes at the clause's pattern and result, so the resolved rule
    /// carries only some of these keys, and some under another role
    /// ([`DescriptorHeadRule::validate_anchored_provenance`]).
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for a key of another role than its
    /// field's, a key two nodes define, or keys that are not the anchors.
    pub fn validate_complete_provenance<'a>(
        &self,
        anchors: impl IntoIterator<Item = &'a ProvenanceKey>,
    ) -> Result<(), StateTransportError> {
        let mut keys = WireKeys::default();
        let clause = clause_keys!(self, false);
        clause.collect(&mut keys)?;
        if let Some(configuration) = &self.configuration {
            keys.define(&configuration.key, ProvenanceRole::RuleType)?;
        }
        if let Some(alternative) = &self.bracket_alternative {
            // The List reading's bindings are the clause's, and its instance
            // children the head's or the list's terms: it defines its cell
            // names and its instance structure only.
            for binding in &alternative.bindings {
                if let Some(refinement) = &binding.refinement {
                    keys.refer(&refinement.key, ProvenanceRole::RuleBindingType)?;
                }
            }
            clause.collect_extra(&alternative.extra, true, &mut keys)?;
        }
        Ok(keys.close(anchors)?)
    }
}

impl DescriptorHeadRule {
    /// Checks the part of the clause's closure that holds once the collector
    /// resolved it: each key field has its field's role and defines its key
    /// once, and every key is one of `anchors`, its descriptor's.
    ///
    /// The collector keeps one of a bracketed value's readings, so anchors
    /// of the other reading are left unconsumed; it keys the cells it
    /// writes, the computation cell and a list cell read from or as the
    /// head, at the clause's pattern and result, which such a cell refers
    /// to; and the header's configuration, now a stable identity, carries
    /// no key. So an anchor no key consumes is not checked.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for a key of another role than its
    /// field's, a key two nodes define, or a key no anchor holds.
    pub fn validate_anchored_provenance<'a>(
        &self,
        anchors: impl IntoIterator<Item = &'a ProvenanceKey>,
    ) -> Result<(), StateTransportError> {
        let mut keys = WireKeys::default();
        let clause = clause_keys!(self, true);
        clause.collect(&mut keys)?;
        if let Some(computation) = &self.computation_cell {
            clause.cell(
                &mut keys,
                &computation.key,
                ProvenanceRole::RuleLeftCellsField,
            )?;
        }
        Ok(keys.close_within(anchors)?)
    }
}

/// The key of a readable extra's cell reference, at either stage.
trait CellKey {
    fn cell_key(&self) -> &ProvenanceKey;
}

impl CellKey for HostHeadRuleCellReference {
    fn cell_key(&self) -> &ProvenanceKey {
        &self.key
    }
}

impl CellKey for DescriptorCellReference {
    fn cell_key(&self) -> &ProvenanceKey {
        &self.key
    }
}

/// The parts of a readable clause that carry keys, which the clause the
/// expander built and the rule the collector resolves share.
struct ClauseKeys<'a, S: Stage, I> {
    sentence_kind: SentenceKind,
    label: Option<&'a DescriptorRuleLabel>,
    priority: Option<&'a DescriptorRulePriority>,
    nondet: Option<&'a crate::DescriptorNondetGroup>,
    pattern_key: &'a ProvenanceKey,
    result_key: &'a ProvenanceKey,
    head_sort: Option<&'a S::Sort>,
    result_type_key: &'a ProvenanceKey,
    bindings: &'a [ProtocolHeadRuleBinding<S::Sort>],
    head: Option<&'a ProtocolHeadRuleHead<Term<S>>>,
    extras: &'a [ProtocolHeadRuleExtra<I, Term<S>>],
    requires: Option<&'a RuleCondition<S>>,
    existentials: &'a [ClaimBinder<S>],
    ensures: Option<&'a RuleCondition<S>>,
    fresh: &'a [ClaimBinder<S>],
    evaluation: Option<&'a EvaluationStep<S>>,
    claim: Option<&'a HeadRuleClaim>,
    /// Whether the collector resolved the clause, keying the cells it
    /// writes at the clause's pattern and result.
    resolved: bool,
}

/// Borrows the parts of a readable clause that carry keys, from either
/// form: both name them alike.
macro_rules! clause_keys {
    ($rule:expr, $resolved:expr) => {
        ClauseKeys {
            sentence_kind: $rule.sentence_kind,
            label: $rule.label.as_ref(),
            priority: $rule.priority.as_ref(),
            nondet: $rule.nondet.as_ref(),
            pattern_key: &$rule.pattern_key,
            result_key: &$rule.result_key,
            head_sort: $rule.head_sort.as_ref(),
            result_type_key: &$rule.result_type_key,
            bindings: &$rule.bindings,
            head: $rule.head.as_ref(),
            extras: &$rule.extras,
            requires: $rule.requires.as_ref(),
            existentials: &$rule.existentials,
            ensures: $rule.ensures.as_ref(),
            fresh: &$rule.fresh,
            evaluation: $rule.evaluation.as_ref(),
            claim: $rule.claim.as_ref(),
            resolved: $resolved,
        }
    };
}
use clause_keys;

impl<S: ValidationStage, I: CellKey> ClauseKeys<'_, S, I> {
    fn collect(&self, keys: &mut WireKeys) -> Result<(), StateTransportError> {
        let claim = self.claim.is_some();
        keys.fixed(if claim {
            ProvenanceRole::ClaimDeclaration
        } else {
            ProvenanceRole::RuleDeclaration
        })?;
        if let Some(label) = self.label {
            // A claim clause's name is its `#[k::claim(..)]`'s label.
            let role = if claim {
                ProvenanceRole::ClaimLabel
            } else {
                ProvenanceRole::RuleLabel
            };
            keys.define(&label.key, role)?;
        }
        if let Some(priority) = self.priority {
            let role = priority
                .role_for(self.sentence_kind)
                .unwrap_or(ProvenanceRole::RuleOwise);
            keys.define(&priority.key, role)?;
        }
        if let Some(nondet) = self.nondet {
            keys.define(&nondet.key, ProvenanceRole::RuleNondetGroup)?;
        }
        keys.define(self.pattern_key, ProvenanceRole::RulePattern)?;
        keys.define(self.result_key, ProvenanceRole::RuleResult)?;
        // The clause's header, a sort or a configuration, is the type of its
        // subject and of its result, two nodes with a key each.
        if let Some(sort) = self.head_sort {
            keys.define(S::sort_key(sort), ProvenanceRole::RuleType)?;
        }
        keys.define(self.result_type_key, ProvenanceRole::RuleResultType)?;
        for binding in self.bindings {
            if let Some(refinement) = &binding.refinement {
                keys.define(S::sort_key(refinement), ProvenanceRole::RuleBindingType)?;
            }
        }
        if let Some(head) = self.head {
            for item in &head.items {
                collect_term_keys(item, ValidationSide::Left, false, keys)?;
            }
            match &head.result {
                None | Some(ProtocolHeadRuleResult::Erase) => {}
                Some(ProtocolHeadRuleResult::Replace(term)) => {
                    collect_term_keys(term, ValidationSide::Right, false, keys)?;
                }
                // The splice denotes the result's sequence, and each of its
                // items an item of it; one the collector read from a list
                // cell denotes nodes the sentence did not key.
                Some(ProtocolHeadRuleResult::Splice(splice)) => {
                    if let Some(key) = &splice.payload_key {
                        keys.define(key, ProvenanceRole::RuleRightKSequencePayload)?;
                    }
                    for item in &splice.items {
                        if let Some(key) = &item.key {
                            keys.define(key, ProvenanceRole::RuleRightKSequenceItem)?;
                        }
                        collect_term_keys(&item.value, ValidationSide::Right, false, keys)?;
                    }
                }
            }
        }
        for extra in self.extras {
            self.collect_extra(extra, false, keys)?;
        }
        if let Some(requires) = self.requires {
            keys.define(&requires.key, ProvenanceRole::RuleRequires)?;
            collect_term_keys(&requires.term, ValidationSide::Requires, false, keys)?;
        }
        self.collect_postconditions(keys)
    }

    /// The keys of the clause's existentials, ensures condition, fresh
    /// binders, evaluation step and claim metadata.
    fn collect_postconditions(&self, keys: &mut WireKeys) -> Result<(), StateTransportError> {
        for binder in self.existentials {
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
        if let Some(ensures) = self.ensures {
            keys.define(&ensures.key, ProvenanceRole::RuleEnsures)?;
            collect_term_keys(&ensures.term, ValidationSide::RuleEnsures, false, keys)?;
        }
        for binder in self.fresh {
            keys.define(&binder.declaration_key, ProvenanceRole::RuleFreshBinder)?;
            keys.define(&binder.name_key, ProvenanceRole::RuleFreshBinderName)?;
            keys.define(
                S::sort_key(&binder.sort),
                ProvenanceRole::RuleFreshBinderSort,
            )?;
        }
        if let Some(step) = self.evaluation {
            keys.define(&step.key, step.kind.role())?;
            keys.define(&step.hole_key, step.kind.hole_role())?;
            if let Some(sort) = &step.result {
                keys.define(S::sort_key(sort), step.kind.result_role())?;
            }
        }
        if let Some(claim) = self.claim {
            keys.define(&claim.modality_key, ProvenanceRole::ClaimModality)?;
            if let Some(key) = &claim.circularity_key {
                keys.define(key, ProvenanceRole::ClaimCircularity)?;
            }
            if let Some(key) = &claim.trusted_key {
                keys.define(key, ProvenanceRole::ClaimTrusted)?;
            }
        }
        Ok(())
    }

    /// Records a cell's key, of `role`; in a resolved clause, a cell keyed
    /// at the clause's pattern or result names that node.
    fn cell(
        &self,
        keys: &mut WireKeys,
        key: &ProvenanceKey,
        role: ProvenanceRole,
    ) -> Result<(), StateTransportError> {
        if self.resolved && key == self.pattern_key {
            keys.refer(key, ProvenanceRole::RulePattern)?;
        } else if self.resolved && key == self.result_key {
            keys.refer(key, ProvenanceRole::RuleResult)?;
        } else {
            keys.define(key, role)?;
        }
        Ok(())
    }

    /// Collects the keys of a readable extra cell. `cloned_terms` marks the
    /// bracket alternative's extra, whose terms are other nodes' and refer.
    fn collect_extra(
        &self,
        extra: &ProtocolHeadRuleExtra<I, Term<S>>,
        cloned_terms: bool,
        keys: &mut WireKeys,
    ) -> Result<(), StateTransportError> {
        let left_cell = ProvenanceRole::RuleLeftCellsField;
        let right_cell = ProvenanceRole::RuleRightCellsField;
        match extra {
            ProtocolHeadRuleExtra::HaveMap { cell, entries } => {
                self.cell(keys, cell.cell_key(), left_cell)?;
                // An entry denotes its key expression and its value binder;
                // a clone's are another entry's.
                for entry in entries {
                    for (key, role) in [
                        (&entry.key_key, ProvenanceRole::RuleLeftMapKey),
                        (&entry.value_key, ProvenanceRole::RuleLeftMapValue),
                    ] {
                        if cloned_terms {
                            keys.refer(key, role)?;
                        } else {
                            keys.define(key, role)?;
                        }
                    }
                    collect_term_keys(&entry.key, ValidationSide::Left, cloned_terms, keys)?;
                }
            }
            ProtocolHeadRuleExtra::UpdateMap { cell, update, .. } => {
                self.cell(keys, cell.cell_key(), right_cell)?;
                collect_term_keys(update, ValidationSide::Right, cloned_terms, keys)?;
            }
            ProtocolHeadRuleExtra::RewriteCell {
                cell,
                result_key,
                before,
                after,
            } => {
                self.cell(keys, cell.cell_key(), left_cell)?;
                if let Some(result_key) = result_key {
                    self.cell(keys, result_key, right_cell)?;
                }
                collect_term_keys(before, ValidationSide::Left, cloned_terms, keys)?;
                if let Some(after) = after {
                    collect_term_keys(after, ValidationSide::Right, cloned_terms, keys)?;
                }
            }
            ProtocolHeadRuleExtra::RewriteState {
                cell,
                result_key,
                before,
                after,
            } => {
                self.cell(keys, cell.cell_key(), left_cell)?;
                if let Some(result_key) = result_key {
                    self.cell(keys, result_key, right_cell)?;
                }
                // The state's structure defines its keys; its terms define
                // theirs unless cloned.
                for (state, side) in [
                    (Some(before), RuleSide::Left),
                    (after.as_ref(), RuleSide::Right),
                ] {
                    if let Some(state) = state {
                        collect_state_keys(state, side, keys, &mut |term, keys| {
                            collect_term_keys(term, side.into(), cloned_terms, keys)
                        })?;
                    }
                }
            }
            ProtocolHeadRuleExtra::RewriteList {
                cell,
                result_key,
                before,
                after,
            } => {
                self.cell(keys, cell.cell_key(), left_cell)?;
                if let Some(result_key) = result_key {
                    self.cell(keys, result_key, right_cell)?;
                }
                for term in before.terms() {
                    collect_term_keys(term, ValidationSide::Left, cloned_terms, keys)?;
                }
                for term in after.iter().flat_map(ProtocolHeadRuleList::terms) {
                    collect_term_keys(term, ValidationSide::Right, cloned_terms, keys)?;
                }
            }
        }
        Ok(())
    }
}

/// Collects the keys of a readable term's nodes on `side`. The clause's
/// terms are keyed as a rule's are: a path and its head are two nodes, each
/// keyed. A `cloned` term repeats another wire term's nodes and refers to
/// their keys.
fn collect_term_keys<S: ValidationStage>(
    term: &Term<S>,
    side: ValidationSide,
    cloned: bool,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    let keying = if cloned {
        TermKeying::ReadableClone
    } else {
        TermKeying::Readable
    };
    super::keys::collect_term_keys(term, side, keying, keys)
}

#[cfg(test)]
mod tests {
    use super::{
        DescriptorHeadRule, HeadRule, ProtocolHeadRuleBinding, ProtocolHeadRuleExtra,
        ProtocolHeadRuleHead, ProtocolHeadRuleMapEntry, ProtocolHeadRuleResult,
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

    /// A splice of `values` whose keys traversal leaves alone.
    fn splice<T>(values: Vec<T>) -> super::ProtocolHeadRuleSplice<T> {
        super::ProtocolHeadRuleSplice {
            payload_key: None,
            items: values
                .into_iter()
                .map(|value| super::ProtocolHeadRuleSpliceItem { key: None, value })
                .collect(),
        }
    }

    fn map_key() -> ProvenanceKey {
        ProvenanceKey::new(ProvenanceRole::RuleLeftMapKey, 0)
    }

    fn map_value() -> ProvenanceKey {
        ProvenanceKey::new(ProvenanceRole::RuleLeftMapValue, 0)
    }

    fn host_sort(role: ProvenanceRole) -> crate::HostSortReference {
        crate::HostSortReference {
            key: ProvenanceKey::new(role, 0),
            target: crate::HostTypeReference {
                key: crate::HostTypeKey(std::any::TypeId::of::<()>),
                authored_path: "Value".to_owned(),
            },
        }
    }

    /// A `for Value` clause `x => [1, ..]`: its head is one variable, its
    /// result a splice of one literal.
    fn table_clause() -> HeadRule<crate::HostStage> {
        let key = ProvenanceKey::new;
        HeadRule {
            sentence_kind: SentenceKind::Transition,
            label: None,
            priority: None,
            nondet: None,
            pattern_key: key(ProvenanceRole::RulePattern, 0),
            result_key: key(ProvenanceRole::RuleResult, 0),
            head_sort: Some(host_sort(ProvenanceRole::RuleType)),
            configuration: None,
            result_type_key: key(ProvenanceRole::RuleResultType, 0),
            computation_cell_name: None,
            bindings: vec![ProtocolHeadRuleBinding {
                name: "x".to_owned(),
                refinement: None,
            }],
            head: Some(ProtocolHeadRuleHead {
                items: vec![crate::Term::Variable {
                    key: key(ProvenanceRole::RuleLeftReference, 0),
                    path_key: key(ProvenanceRole::RuleLeftPath, 0),
                    name: "x".to_owned(),
                }],
                exact: false,
                result: Some(ProtocolHeadRuleResult::Splice(
                    super::ProtocolHeadRuleSplice {
                        payload_key: Some(key(ProvenanceRole::RuleRightKSequencePayload, 0)),
                        items: vec![super::ProtocolHeadRuleSpliceItem {
                            key: Some(key(ProvenanceRole::RuleRightKSequenceItem, 0)),
                            value: crate::Term::Literal {
                                key: key(ProvenanceRole::RuleRightLiteral, 0),
                                literal: crate::DescriptorLiteral::Int("1".to_owned()),
                            },
                        }],
                    },
                )),
            }),
            requires: None,
            extras: Vec::new(),
            existentials: Vec::new(),
            ensures: None,
            fresh: Vec::new(),
            evaluation: None,
            bracket_alternative: None,
            claim: None,
        }
    }

    fn table_anchors() -> Vec<ProvenanceKey> {
        [
            ProvenanceRole::RuleDeclaration,
            ProvenanceRole::RulePattern,
            ProvenanceRole::RuleResult,
            ProvenanceRole::RuleType,
            ProvenanceRole::RuleResultType,
            ProvenanceRole::RuleLeftReference,
            ProvenanceRole::RuleLeftPath,
            ProvenanceRole::RuleRightKSequencePayload,
            ProvenanceRole::RuleRightKSequenceItem,
            ProvenanceRole::RuleRightLiteral,
        ]
        .map(|role| ProvenanceKey::new(role, 0))
        .to_vec()
    }

    /// A readable clause's keys are its anchors: each key field defines its
    /// node, the result type, the splice and its item included, and the
    /// clause's declaration is fixed.
    #[test]
    fn a_readable_clause_is_closed_over_its_anchors() {
        let rule = table_clause();
        let anchors = table_anchors();
        assert_eq!(rule.validate_complete_provenance(&anchors), Ok(()));

        // A node that no wire node denotes is left over.
        let mut extra = anchors.clone();
        extra.push(ProvenanceKey::new(ProvenanceRole::RuleLeftWildcard, 0));
        assert_eq!(
            rule.validate_complete_provenance(&extra),
            Err(crate::StateTransportError::ExtraProvenance(
                ProvenanceKey::new(ProvenanceRole::RuleLeftWildcard, 0)
            ))
        );

        // A spliced item whose key no anchor holds.
        let mut spliced = rule.clone();
        let Some(ProtocolHeadRuleResult::Splice(splice)) =
            spliced.head.as_mut().and_then(|head| head.result.as_mut())
        else {
            unreachable!()
        };
        splice.items.push(super::ProtocolHeadRuleSpliceItem {
            key: Some(ProvenanceKey::new(
                ProvenanceRole::RuleRightKSequenceItem,
                1,
            )),
            value: crate::Term::Literal {
                key: ProvenanceKey::new(ProvenanceRole::RuleRightLiteral, 1),
                literal: crate::DescriptorLiteral::Int("2".to_owned()),
            },
        });
        let mut with_literal = anchors.clone();
        with_literal.push(ProvenanceKey::new(ProvenanceRole::RuleRightLiteral, 1));
        assert_eq!(
            spliced.validate_complete_provenance(&with_literal),
            Err(crate::StateTransportError::MissingProvenance(
                ProvenanceKey::new(ProvenanceRole::RuleRightKSequenceItem, 1)
            ))
        );

        // A splice whose keys the clause does not carry leaves its anchors
        // unconsumed.
        let mut unkeyed = rule.clone();
        let Some(ProtocolHeadRuleResult::Splice(splice)) =
            unkeyed.head.as_mut().and_then(|head| head.result.as_mut())
        else {
            unreachable!()
        };
        splice.payload_key = None;
        assert_eq!(
            unkeyed.validate_complete_provenance(&anchors),
            Err(crate::StateTransportError::ExtraProvenance(
                ProvenanceKey::new(ProvenanceRole::RuleRightKSequencePayload, 0)
            ))
        );

        // The result type is a node of its own, with its own role.
        let mut retyped = rule.clone();
        retyped.result_type_key = ProvenanceKey::new(ProvenanceRole::RuleType, 0);
        assert_eq!(
            retyped.validate_complete_provenance(&anchors),
            Err(crate::StateTransportError::UnexpectedProvenance {
                expected: ProvenanceRole::RuleResultType,
                actual: ProvenanceKey::new(ProvenanceRole::RuleType, 0),
            })
        );

        // Two head items that carry one node's keys.
        let mut repeated = rule.clone();
        let head = repeated.head.as_mut().unwrap();
        head.items.push(head.items[0].clone());
        assert_eq!(
            repeated.validate_complete_provenance(&anchors),
            Err(crate::StateTransportError::DuplicateProvenance(
                ProvenanceKey::new(ProvenanceRole::RuleLeftPath, 0)
            ))
        );

        // A claim clause's declaration is the claim's.
        let mut claim = rule;
        claim.sentence_kind = SentenceKind::Claim;
        claim.claim = Some(super::HeadRuleClaim {
            modality_key: ProvenanceKey::new(ProvenanceRole::ClaimModality, 0),
            modality: crate::ClaimModality::OnePath,
            circularity_key: None,
            trusted_key: None,
        });
        let mut claim_anchors = anchors;
        claim_anchors[0] = ProvenanceKey::new(ProvenanceRole::ClaimDeclaration, 0);
        claim_anchors.push(ProvenanceKey::new(ProvenanceRole::ClaimModality, 0));
        assert_eq!(claim.validate_complete_provenance(&claim_anchors), Ok(()));
    }

    /// A cell-record clause `k: [x, ..] => [x, ..], env: e => e` as the
    /// collector resolves it: its computation cell is keyed at the pattern.
    fn resolved_clause() -> DescriptorHeadRule {
        let key = ProvenanceKey::new;
        let configuration = StableItemId::new(
            PackageId::new("ORG-EXAMPLE", "test", "0.1.0", "workspace").unwrap(),
            ["configuration"],
            "State",
            ItemKind::Configuration,
            "",
        )
        .unwrap();
        let cell = |key, field: &str| DescriptorCellReference {
            key,
            cell: DescriptorCellIdentity {
                owner: configuration.clone(),
                field: field.to_owned(),
            },
        };
        let variable = |reference, path| DescriptorTerm::Variable {
            key: key(reference, 0),
            path_key: key(path, 0),
            name: "x".to_owned(),
        };
        DescriptorHeadRule {
            sentence_kind: SentenceKind::Transition,
            label: None,
            priority: None,
            nondet: None,
            pattern_key: key(ProvenanceRole::RulePattern, 0),
            result_key: key(ProvenanceRole::RuleResult, 0),
            head_sort: None,
            configuration: configuration.clone(),
            result_type_key: key(ProvenanceRole::RuleResultType, 0),
            computation_cell: Some(cell(key(ProvenanceRole::RulePattern, 0), "k")),
            bindings: Vec::new(),
            head: Some(ProtocolHeadRuleHead {
                items: vec![variable(
                    ProvenanceRole::RuleLeftReference,
                    ProvenanceRole::RuleLeftPath,
                )],
                exact: false,
                result: Some(ProtocolHeadRuleResult::Replace(variable(
                    ProvenanceRole::RuleRightReference,
                    ProvenanceRole::RuleRightPath,
                ))),
            }),
            requires: None,
            extras: vec![ProtocolHeadRuleExtra::RewriteCell {
                cell: cell(key(ProvenanceRole::RuleLeftCellsField, 0), "env"),
                result_key: Some(key(ProvenanceRole::RuleRightCellsField, 0)),
                before: variable(
                    ProvenanceRole::RuleLeftReference,
                    ProvenanceRole::RuleLeftPath,
                ),
                after: Some(variable(
                    ProvenanceRole::RuleRightReference,
                    ProvenanceRole::RuleRightPath,
                )),
            }],
            existentials: Vec::new(),
            ensures: None,
            fresh: Vec::new(),
            evaluation: None,
            claim: None,
        }
    }

    /// The resolved clause keeps the part of closure that holds once the
    /// collector reshaped it: roles, one definition per key, every key
    /// anchored, and a cell keyed at the pattern or the result refers to it;
    /// anchors of a dropped reading are left over.
    #[test]
    fn a_resolved_clause_is_anchored_by_role() {
        let key = ProvenanceKey::new;
        let mut anchors = vec![
            key(ProvenanceRole::RuleDeclaration, 0),
            key(ProvenanceRole::RulePattern, 0),
            key(ProvenanceRole::RuleResult, 0),
            key(ProvenanceRole::RuleResultType, 0),
            key(ProvenanceRole::RuleLeftCellsField, 0),
            key(ProvenanceRole::RuleRightCellsField, 0),
        ];
        for ordinal in 0..2 {
            anchors.extend([
                key(ProvenanceRole::RuleLeftReference, ordinal),
                key(ProvenanceRole::RuleLeftPath, ordinal),
                key(ProvenanceRole::RuleRightReference, ordinal),
                key(ProvenanceRole::RuleRightPath, ordinal),
            ]);
        }
        let mut rule = resolved_clause();
        // The extra's terms are the second of each role.
        let ProtocolHeadRuleExtra::RewriteCell { before, after, .. } = &mut rule.extras[0] else {
            unreachable!()
        };
        for term in [before, after.as_mut().unwrap()] {
            let DescriptorTerm::Variable { key, path_key, .. } = term else {
                unreachable!()
            };
            *key = ProvenanceKey::new(key.role(), 1);
            *path_key = ProvenanceKey::new(path_key.role(), 1);
        }
        assert_eq!(rule.validate_anchored_provenance(&anchors), Ok(()));

        // An anchor of a reading the collector dropped is left over.
        let mut dropped = anchors.clone();
        dropped.push(key(ProvenanceRole::RuleLeftCellsField, 1));
        assert_eq!(rule.validate_anchored_provenance(&dropped), Ok(()));

        // A key no anchor holds.
        assert_eq!(
            rule.validate_anchored_provenance(&anchors[1..]),
            Err(crate::StateTransportError::MissingProvenance(key(
                ProvenanceRole::RuleDeclaration,
                0
            )))
        );

        // The cell and result keys swapped: each has the other's role.
        let mut swapped = rule.clone();
        let ProtocolHeadRuleExtra::RewriteCell {
            cell, result_key, ..
        } = &mut swapped.extras[0]
        else {
            unreachable!()
        };
        std::mem::swap(&mut cell.key, result_key.as_mut().unwrap());
        assert_eq!(
            swapped.validate_anchored_provenance(&anchors),
            Err(crate::StateTransportError::UnexpectedProvenance {
                expected: ProvenanceRole::RuleLeftCellsField,
                actual: key(ProvenanceRole::RuleRightCellsField, 0),
            })
        );

        // The extra's terms repeating the head's keys.
        let repeated = resolved_clause();
        assert_eq!(
            repeated.validate_anchored_provenance(&anchors),
            Err(crate::StateTransportError::DuplicateProvenance(key(
                ProvenanceRole::RuleLeftPath,
                0
            )))
        );
    }

    /// A readable state's shells define their payload keys, as every shell
    /// does: an instance child `[]` or `map![]` is accepted with its key
    /// anchored, and refused when no anchor holds it.
    #[test]
    fn a_readable_state_shell_has_its_payload_key() {
        use crate::{
            InstanceDelimiter, ProtocolInstanceRest, ProtocolRuleFrame, ProtocolRuleInstance,
            ProtocolRuleInstanceField, ProtocolRuleInstances, ProtocolRuleKSequence,
            ProtocolRuleMap, ProtocolRuleMapBody, ProtocolRuleStateTerm,
        };

        let key = ProvenanceKey::new;
        // `threads: [Thread { k: [] }]`, its child the given shell.
        let with_child = |child| {
            let mut rule = resolved_clause();
            let ProtocolHeadRuleExtra::RewriteCell { cell, .. } = rule.extras.remove(0) else {
                unreachable!()
            };
            rule.extras = vec![ProtocolHeadRuleExtra::RewriteState {
                cell,
                result_key: None,
                before: ProtocolRuleStateTerm::Instances(ProtocolRuleInstances {
                    delimiter: InstanceDelimiter::Bracket,
                    front: vec![ProtocolRuleInstance {
                        key: key(ProvenanceRole::RuleLeftCellsInstance, 0),
                        label: None,
                        fields: vec![ProtocolRuleInstanceField {
                            key: key(ProvenanceRole::RuleLeftCellsInstanceField, 0),
                            field: "k".to_owned(),
                            value: child,
                        }],
                        rest: ProtocolInstanceRest::Exact,
                    }],
                    rest: ProtocolRuleFrame::Exact,
                    back: Vec::new(),
                }),
                after: None,
            }];
            rule
        };
        let sequence = |payload_key| {
            ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
                payload_key,
                dot_k_key: None,
                notation: crate::DescriptorKSequenceNotation::Comma,
                items: Vec::new(),
                tail: ProtocolRuleFrame::Exact,
            })
        };
        let map = |payload_key| {
            ProtocolRuleStateTerm::Map(ProtocolRuleMap {
                payload_key,
                body: ProtocolRuleMapBody::Empty {
                    explicit_dot: false,
                },
            })
        };
        let mut anchors = vec![
            key(ProvenanceRole::RuleDeclaration, 0),
            key(ProvenanceRole::RulePattern, 0),
            key(ProvenanceRole::RuleResult, 0),
            key(ProvenanceRole::RuleResultType, 0),
            key(ProvenanceRole::RuleLeftReference, 0),
            key(ProvenanceRole::RuleLeftPath, 0),
            key(ProvenanceRole::RuleRightReference, 0),
            key(ProvenanceRole::RuleRightPath, 0),
            key(ProvenanceRole::RuleLeftCellsField, 0),
            key(ProvenanceRole::RuleLeftCellsInstance, 0),
            key(ProvenanceRole::RuleLeftCellsInstanceField, 0),
            key(ProvenanceRole::RuleLeftKSequencePayload, 0),
            key(ProvenanceRole::RuleLeftMapPayload, 0),
        ];
        let keyed = with_child(sequence(key(ProvenanceRole::RuleLeftKSequencePayload, 0)));
        assert_eq!(keyed.validate_anchored_provenance(&anchors), Ok(()));

        let keyed = with_child(map(key(ProvenanceRole::RuleLeftMapPayload, 0)));
        assert_eq!(keyed.validate_anchored_provenance(&anchors), Ok(()));

        // The key is defined by the shell: one no anchor holds is refused.
        anchors.pop();
        assert_eq!(
            keyed.validate_anchored_provenance(&anchors),
            Err(crate::StateTransportError::MissingProvenance(key(
                ProvenanceRole::RuleLeftMapPayload,
                0
            )))
        );
    }

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
        let spliced = ProtocolHeadRuleResult::Splice(splice(vec![2, 3]))
            .try_map_refs(&mut calls, &mut map_number)
            .unwrap();
        assert_eq!(
            spliced,
            ProtocolHeadRuleResult::Splice(splice(vec![12, 13]))
        );
        let erase = ProtocolHeadRuleResult::<u8>::Erase
            .try_map_refs(&mut calls, &mut map_number)
            .unwrap();
        assert_eq!(erase, ProtocolHeadRuleResult::Erase);
        assert_eq!(calls, [1, 2, 3]);
        let failure = ProtocolHeadRuleResult::Splice(splice(vec![4, 9, 5]))
            .try_map_refs(&mut calls, &mut map_number);
        assert_eq!(failure, Err("unresolved reference"));
        assert_eq!(calls, [1, 2, 3, 4, 9]);
    }

    #[test]
    fn map_reads_need_an_entry_and_declare_every_value_binding() {
        use crate::StateTransportError;
        use crate::transport::detail::StateTermReason;

        let bindings = ["x", "y"].map(|name| ProtocolHeadRuleBinding::<u8> {
            name: name.to_owned(),
            refinement: None,
        });
        let read = |names: &[&str]| ProtocolHeadRuleExtra::<u8, u8>::HaveMap {
            cell: 0,
            entries: names
                .iter()
                .map(|name| ProtocolHeadRuleMapEntry {
                    key_key: map_key(),
                    key: 0,
                    value_key: map_value(),
                    value_binding: (*name).to_owned(),
                })
                .collect(),
        };
        assert!(super::validate_bindings(&bindings, &[read(&["x", "y"])]).is_ok());
        assert!(matches!(
            super::validate_bindings(&bindings, &[read(&[])]),
            Err(StateTransportError::InvalidTerm(
                StateTermReason::EmptyMapRead
            ))
        ));
        assert!(matches!(
            super::validate_bindings(&bindings, &[read(&["x", "z"])]),
            Err(StateTransportError::InvalidTerm(
                StateTermReason::UndeclaredHeadRuleExtraBinding
            ))
        ));
    }

    #[test]
    fn head_extra_traversal_maps_every_reference_and_stops_at_first_error() {
        let result_key = ProvenanceKey::new(ProvenanceRole::RuleRightCellsField, 0);
        let mut calls = Vec::new();
        let have = ProtocolHeadRuleExtra::HaveMap {
            cell: 1,
            entries: vec![ProtocolHeadRuleMapEntry {
                key_key: map_key(),
                key: 2,
                value_key: map_value(),
                value_binding: "value".to_owned(),
            }],
        }
        .try_map_refs(&mut calls, &mut map_number, &mut map_number)
        .unwrap();
        assert_eq!(
            have,
            ProtocolHeadRuleExtra::HaveMap {
                cell: 11,
                entries: vec![ProtocolHeadRuleMapEntry {
                    key_key: map_key(),
                    key: 12,
                    value_key: map_value(),
                    value_binding: "value".to_owned(),
                }],
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
            result_key: Some(result_key.clone()),
            before: 6,
            after: Some(7),
        }
        .try_map_refs(&mut calls, &mut map_number, &mut map_number)
        .unwrap();
        assert_eq!(
            rewrite,
            ProtocolHeadRuleExtra::RewriteCell {
                cell: 15,
                result_key: Some(result_key.clone()),
                before: 16,
                after: Some(17),
            }
        );
        assert_eq!(calls, [1, 2, 3, 4, 5, 6, 7]);
        let failure = ProtocolHeadRuleExtra::RewriteCell {
            cell: 8,
            result_key: Some(result_key),
            before: 9,
            after: Some(1),
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
            spelling_key: ProvenanceKey::new(ProvenanceRole::ClaimAnonymousSpelling, 0),
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
            result_type_key: key.clone(),
            computation_cell_name: Some("k".to_owned()),
            bindings: vec![ProtocolHeadRuleBinding {
                name: "value".to_owned(),
                refinement: Some(wire_sort()),
            }],
            head: Some(ProtocolHeadRuleHead {
                items: vec![wire_term()],
                exact: false,
                result: Some(ProtocolHeadRuleResult::Splice(splice(vec![wire_term()]))),
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
                result_key: Some(key),
                before: wire_term(),
                after: Some(wire_term()),
            }],
            existentials: Vec::new(),
            ensures: None,
            fresh: Vec::new(),
            evaluation: None,
            bracket_alternative: None,
            claim: None,
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
            spelling_key: ProvenanceKey::new(ProvenanceRole::ClaimAnonymousSpelling, 0),
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
            result_type_key: key.clone(),
            computation_cell: Some(cell.clone()),
            bindings: vec![ProtocolHeadRuleBinding {
                name: "value".to_owned(),
                refinement: Some(descriptor_sort()),
            }],
            head: Some(ProtocolHeadRuleHead {
                items: vec![descriptor_term()],
                exact: false,
                result: Some(ProtocolHeadRuleResult::Replace(descriptor_term())),
            }),
            requires: Some(crate::DescriptorRuleCondition {
                key,
                term: descriptor_term(),
            }),
            extras: vec![ProtocolHeadRuleExtra::HaveMap {
                cell,
                entries: vec![ProtocolHeadRuleMapEntry {
                    key_key: map_key(),
                    key: descriptor_term(),
                    value_key: map_value(),
                    value_binding: "value".to_owned(),
                }],
            }],
            existentials: Vec::new(),
            ensures: None,
            fresh: Vec::new(),
            evaluation: None,
            claim: None,
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

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
        /// Required map key.
        pub key: T => [term_map],
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
    map_order: [extras, head, sentence_kind, label, priority, nondet, pattern_key, result_key, head_sort, configuration, computation_cell_name, bindings, requires, existentials, ensures, fresh, evaluation, bracket_alternative, claim];
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
    for (index, binder) in fresh.iter().enumerate() {
        let ordinal = u32::try_from(index).ok();
        if binder.name.is_empty()
            || !names.insert(binder.name.as_str())
            || bindings.iter().any(|binding| binding.name == binder.name)
            || existentials
                .iter()
                .any(|existential| existential.name == binder.name)
            || binder.declaration_key.role() != ProvenanceRole::RuleFreshBinder
            || binder.name_key.role() != ProvenanceRole::RuleFreshBinderName
            || Some(binder.declaration_key.ordinal()) != ordinal
            || Some(binder.name_key.ordinal()) != ordinal
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
                    key: 0,
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
                key: 2,
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
                    key: 12,
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
                items: vec![wire_term()],
                exact: false,
                result: Some(ProtocolHeadRuleResult::Splice(vec![wire_term()])),
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
                    key: descriptor_term(),
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

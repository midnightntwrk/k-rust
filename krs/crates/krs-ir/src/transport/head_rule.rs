//! Collector transport for readable rules completed at a computation-cell head.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use super::detail::{StateTermReason, TransportField, TransportItemKind};
use super::keys::WireKeys;
use super::rule::{TermRole, ValidationSide, frame_key};
use super::validation::{TermValidation, validate_term};
use crate::stage::{protocol_shape, stage_shape};
use crate::transport::grammar::{
    CellTermField, DescriptorApplicationHeadClass, HostApplicationReference, RuleCondition, Term,
};

use crate::{
    BuiltinSort, DescriptorCellReference, DescriptorLiteral, DescriptorRuleLabel,
    DescriptorRulePriority, DescriptorSortReference, DescriptorStage, DescriptorTerm,
    HostSortReference, HostStage, HostTerm, ItemKind, ProvenanceKey, ProvenanceRole, RuleRole,
    RuleSide, SentenceKind, StateTransportError,
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
pub type HostHeadRule = HeadRule<crate::HostStage>;

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
    /// each key field has its field's role and defines its key once, the
    /// fixed declaration key is the rule clause's or the claim clause's, and
    /// the nodes that carry no key of their own pair with the anchors of
    /// their roles.
    ///
    /// The check reads the clause as the expander built it. The collector
    /// then keeps one of a bracketed value's two readings, moves a cell's
    /// list to the computation cell's head or back, and keys the cells it so
    /// writes at the clause's pattern and result, so the resolved rule
    /// carries only some of these keys, and some under another role.
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
        self.collect_keys(&mut keys)?;
        Ok(keys.close(anchors)?)
    }

    fn collect_keys(&self, keys: &mut WireKeys) -> Result<(), StateTransportError> {
        let claim = self.claim.is_some();
        keys.fixed(if claim {
            ProvenanceRole::ClaimDeclaration
        } else {
            ProvenanceRole::RuleDeclaration
        })?;
        if let Some(label) = &self.label {
            // A claim clause's name is its `#[k::claim(..)]`'s label.
            let role = if claim {
                ProvenanceRole::ClaimLabel
            } else {
                ProvenanceRole::RuleLabel
            };
            keys.define(&label.key, role)?;
        }
        if let Some(priority) = &self.priority {
            let role = priority
                .role_for(self.sentence_kind)
                .unwrap_or(ProvenanceRole::RuleOwise);
            keys.define(&priority.key, role)?;
        }
        if let Some(nondet) = &self.nondet {
            keys.define(&nondet.key, ProvenanceRole::RuleNondetGroup)?;
        }
        keys.define(&self.pattern_key, ProvenanceRole::RulePattern)?;
        keys.define(&self.result_key, ProvenanceRole::RuleResult)?;
        // The clause's header, a sort or a configuration, is the type of its
        // subject and of its result: it denotes both nodes, and carries the
        // first's key only.
        if let Some(sort) = &self.head_sort {
            keys.define(&sort.key, ProvenanceRole::RuleType)?;
        }
        if let Some(configuration) = &self.configuration {
            keys.define(&configuration.key, ProvenanceRole::RuleType)?;
        }
        keys.implicit(ProvenanceRole::RuleResultType);
        for binding in &self.bindings {
            if let Some(refinement) = &binding.refinement {
                keys.define(&refinement.key, ProvenanceRole::RuleBindingType)?;
            }
        }
        if let Some(head) = &self.head {
            for item in &head.items {
                collect_term_keys(item, ValidationSide::Left, false, keys)?;
            }
            match &head.result {
                None | Some(ProtocolHeadRuleResult::Erase) => {}
                Some(ProtocolHeadRuleResult::Replace(term)) => {
                    collect_term_keys(term, ValidationSide::Right, false, keys)?;
                }
                // The splice denotes the result's sequence, and each of its
                // terms an item of it; neither carries the key.
                Some(ProtocolHeadRuleResult::Splice(items)) => {
                    keys.implicit(ProvenanceRole::RuleRightKSequencePayload);
                    for item in items {
                        keys.implicit(ProvenanceRole::RuleRightKSequenceItem);
                        collect_term_keys(item, ValidationSide::Right, false, keys)?;
                    }
                }
            }
        }
        for extra in &self.extras {
            collect_extra_keys(extra, false, keys)?;
        }
        if let Some(requires) = &self.requires {
            keys.define(&requires.key, ProvenanceRole::RuleRequires)?;
            collect_term_keys(&requires.term, ValidationSide::Requires, false, keys)?;
        }
        self.collect_postcondition_keys(keys)?;
        if let Some(alternative) = &self.bracket_alternative {
            // The List reading's bindings are the clause's, and its instance
            // children the head's or the list's terms: it defines its cell
            // names and its instance structure only.
            for binding in &alternative.bindings {
                if let Some(refinement) = &binding.refinement {
                    keys.refer(&refinement.key, ProvenanceRole::RuleBindingType)?;
                }
            }
            collect_extra_keys(&alternative.extra, true, keys)?;
        }
        Ok(())
    }

    /// The keys of the clause's existentials, ensures condition, fresh
    /// binders, evaluation step and claim metadata.
    fn collect_postcondition_keys(&self, keys: &mut WireKeys) -> Result<(), StateTransportError> {
        for binder in &self.existentials {
            keys.define(
                &binder.declaration_key,
                ProvenanceRole::RuleExistentialBinder,
            )?;
            keys.define(&binder.name_key, ProvenanceRole::RuleExistentialBinderName)?;
            keys.define(&binder.sort.key, ProvenanceRole::RuleExistentialBinderSort)?;
        }
        if let Some(ensures) = &self.ensures {
            keys.define(&ensures.key, ProvenanceRole::RuleEnsures)?;
            collect_term_keys(&ensures.term, ValidationSide::RuleEnsures, false, keys)?;
        }
        for binder in &self.fresh {
            keys.define(&binder.declaration_key, ProvenanceRole::RuleFreshBinder)?;
            keys.define(&binder.name_key, ProvenanceRole::RuleFreshBinderName)?;
            keys.define(&binder.sort.key, ProvenanceRole::RuleFreshBinderSort)?;
        }
        if let Some(step) = &self.evaluation {
            keys.define(&step.key, step.kind.role())?;
            keys.define(&step.hole_key, step.kind.hole_role())?;
            if let Some(sort) = &step.result {
                keys.define(&sort.key, step.kind.result_role())?;
            }
        }
        if let Some(claim) = &self.claim {
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
}

/// Collects the keys of a readable extra cell. `cloned_terms` marks the
/// bracket alternative's extra, whose terms are other nodes' and refer.
fn collect_extra_keys(
    extra: &HostHeadRuleExtra,
    cloned_terms: bool,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    let left_cell = ProvenanceRole::RuleLeftCellsField;
    let right_cell = ProvenanceRole::RuleRightCellsField;
    match extra {
        ProtocolHeadRuleExtra::HaveMap { cell, entries } => {
            keys.define(&cell.key, left_cell)?;
            // An entry denotes its key term's payload and its value binder,
            // and carries neither key.
            for entry in entries {
                keys.implicit(ProvenanceRole::RuleLeftMapKey);
                keys.implicit(ProvenanceRole::RuleLeftMapValue);
                collect_term_keys(&entry.key, ValidationSide::Left, cloned_terms, keys)?;
            }
        }
        ProtocolHeadRuleExtra::UpdateMap { cell, update, .. } => {
            keys.define(&cell.key, right_cell)?;
            collect_term_keys(update, ValidationSide::Right, cloned_terms, keys)?;
        }
        ProtocolHeadRuleExtra::RewriteCell {
            cell,
            result_key,
            before,
            after,
        } => {
            keys.define(&cell.key, left_cell)?;
            if let Some(result_key) = result_key {
                keys.define(result_key, right_cell)?;
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
            keys.define(&cell.key, left_cell)?;
            if let Some(result_key) = result_key {
                keys.define(result_key, right_cell)?;
            }
            collect_state_keys(before, RuleSide::Left, cloned_terms, keys)?;
            if let Some(after) = after {
                collect_state_keys(after, RuleSide::Right, cloned_terms, keys)?;
            }
        }
        ProtocolHeadRuleExtra::RewriteList {
            cell,
            result_key,
            before,
            after,
        } => {
            keys.define(&cell.key, left_cell)?;
            if let Some(result_key) = result_key {
                keys.define(result_key, right_cell)?;
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

/// Collects the keys of a readable cell state on `side`: its sequence,
/// instance and map structure defines its keys, and its terms define theirs
/// unless `cloned_terms`.
fn collect_state_keys(
    state: &crate::ProtocolRuleStateTerm<HostTerm>,
    side: RuleSide,
    cloned_terms: bool,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    use crate::ProtocolRuleStateTerm as State;
    match state {
        State::Term(term) | State::Group(term) => {
            collect_term_keys(term, side.into(), cloned_terms, keys)?;
        }
        State::Present { value } => collect_state_keys(value, side, cloned_terms, keys)?,
        State::Absent => {}
        State::Instances(instances) => {
            for instance in instances.front.iter().chain(&instances.back) {
                keys.define(&instance.key, RuleRole::CellsInstance.on_side(side))?;
                for field in &instance.fields {
                    keys.define(&field.key, RuleRole::CellsInstanceField.on_side(side))?;
                    collect_state_keys(&field.value, side, cloned_terms, keys)?;
                }
            }
            if let Some(key) = frame_key(&instances.rest) {
                keys.define(key, RuleRole::CellsInstancesRest.on_side(side))?;
            }
        }
        State::KSequence(sequence) => {
            if let Some(key) = &sequence.payload_key {
                keys.define(key, RuleRole::KSequencePayload.on_side(side))?;
            }
            for key in sequence.dot_k_key.iter().chain(frame_key(&sequence.tail)) {
                keys.define(key, RuleRole::KSequenceTail.on_side(side))?;
            }
            for item in &sequence.items {
                keys.define(&item.key, RuleRole::KSequenceItem.on_side(side))?;
                collect_term_keys(&item.value, side.into(), cloned_terms, keys)?;
            }
        }
        State::Map(map) => {
            if let Some(key) = &map.payload_key {
                keys.define(key, RuleRole::MapPayload.on_side(side))?;
            }
            match &map.body {
                crate::ProtocolRuleMapBody::Empty { .. } => {}
                crate::ProtocolRuleMapBody::Items { items, remainder } => {
                    for item in items {
                        keys.define(&item.key_key, RuleRole::MapKey.on_side(side))?;
                        keys.define(&item.value_key, RuleRole::MapValue.on_side(side))?;
                        collect_term_keys(&item.key, side.into(), cloned_terms, keys)?;
                        collect_term_keys(&item.value, side.into(), cloned_terms, keys)?;
                    }
                    if let Some(key) = frame_key(remainder) {
                        keys.define(key, RuleRole::MapRemainder.on_side(side))?;
                    }
                }
                crate::ProtocolRuleMapBody::Update {
                    base_key,
                    base,
                    key_key,
                    key,
                    value_key,
                    value,
                } => {
                    keys.define(base_key, RuleRole::MapUpdateBase.on_side(side))?;
                    keys.define(key_key, RuleRole::MapKey.on_side(side))?;
                    keys.define(value_key, RuleRole::MapValue.on_side(side))?;
                    for term in [base, key, value] {
                        collect_term_keys(term, side.into(), cloned_terms, keys)?;
                    }
                }
            }
        }
    }
    Ok(())
}

/// Collects the keys of a readable term's nodes on `side`. The clause's
/// terms are keyed as a rule's are: a path and its head are two nodes, each
/// keyed. A `cloned` term repeats another wire term's nodes and refers to
/// their keys.
fn collect_term_keys(
    term: &HostTerm,
    side: ValidationSide,
    cloned: bool,
    keys: &mut WireKeys,
) -> Result<(), StateTransportError> {
    validate_term(
        term,
        &mut ReadableTermKeys {
            keys,
            side,
            cloned,
            in_matches_pattern: false,
            in_let_pattern: false,
        },
    )
}

/// The term walk of [`collect_term_keys`]: it checks each node's key roles
/// only; a readable term's placement rules are the collector's and the
/// compiler's.
struct ReadableTermKeys<'a> {
    keys: &'a mut WireKeys,
    side: ValidationSide,
    cloned: bool,
    in_matches_pattern: bool,
    in_let_pattern: bool,
}

impl ReadableTermKeys<'_> {
    fn node(
        &mut self,
        key: &ProvenanceKey,
        role: ProvenanceRole,
    ) -> Result<(), StateTransportError> {
        if self.cloned {
            self.keys.refer(key, role)?;
        } else {
            self.keys.define(key, role)?;
        }
        Ok(())
    }

    /// A node that carries no key of its own: a clone repeats one another
    /// term carries.
    fn implicit(&mut self, role: ProvenanceRole) {
        if !self.cloned {
            self.keys.implicit(role);
        }
    }
}

impl TermValidation<HostStage> for ReadableTermKeys<'_> {
    type Error = StateTransportError;

    fn variable(
        &mut self,
        key: &ProvenanceKey,
        path_key: &ProvenanceKey,
        _: &str,
    ) -> Result<(), Self::Error> {
        self.node(path_key, TermRole::Path.on_side(self.side))?;
        self.node(key, TermRole::Reference.on_side(self.side))
    }

    fn application(
        &mut self,
        head_class: DescriptorApplicationHeadClass,
        reference: &HostApplicationReference,
        path_key: &ProvenanceKey,
        _: &crate::Arguments<HostStage>,
    ) -> Result<(), Self::Error> {
        self.node(path_key, TermRole::Path.on_side(self.side))?;
        let role = match head_class {
            DescriptorApplicationHeadClass::Applied => TermRole::ApplicationHead,
            DescriptorApplicationHeadClass::BareReference => TermRole::Reference,
        };
        self.node(&reference.key, role.on_side(self.side))
    }

    fn literal(&mut self, key: &ProvenanceKey, _: &DescriptorLiteral) -> Result<(), Self::Error> {
        self.node(key, TermRole::Literal.on_side(self.side))
    }

    fn wildcard(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        let role = if self.in_let_pattern {
            ProvenanceRole::LetWildcard
        } else if self.in_matches_pattern {
            ProvenanceRole::MatchesWildcard
        } else {
            match self.side {
                ValidationSide::Left => ProvenanceRole::RuleLeftWildcard,
                ValidationSide::Right => ProvenanceRole::RuleRightWildcard,
                ValidationSide::Requires
                | ValidationSide::Ensures
                | ValidationSide::RuleEnsures => {
                    return Err(StateTransportError::InvalidTerm(
                        StateTermReason::WildcardsAreAllowedOnlyInRuleSubjects,
                    ));
                }
            }
        };
        self.node(key, role)
    }

    fn builtin_token(
        &mut self,
        key: &ProvenanceKey,
        sort: BuiltinSort,
        value: &str,
    ) -> Result<(), Self::Error> {
        let role = super::validation::builtin_token_literal_role(sort, value).ok_or(
            StateTransportError::InvalidTerm(StateTermReason::InvalidCompilerOwnedBuiltinToken),
        )?;
        self.node(key, role)
    }

    fn anonymous(
        &mut self,
        key: &ProvenanceKey,
        sort: &HostSortReference,
        _: &str,
    ) -> Result<(), Self::Error> {
        self.node(key, ProvenanceRole::ClaimAnonymous)?;
        self.node(&sort.key, ProvenanceRole::ClaimAnonymousSort)?;
        // The constant's spelling is a node of its own, which the term
        // carries as text.
        self.implicit(ProvenanceRole::ClaimAnonymousSpelling);
        Ok(())
    }

    fn or_bool(
        &mut self,
        key: &ProvenanceKey,
        _: &crate::AtLeastTwo<HostTerm>,
    ) -> Result<(), Self::Error> {
        self.node(key, ProvenanceRole::ClaimOrBool)
    }

    fn lexeme(
        &mut self,
        key: &ProvenanceKey,
        sort: &HostSortReference,
        _: &str,
    ) -> Result<(), Self::Error> {
        self.node(&sort.key, ProvenanceRole::LexemeSort)?;
        self.node(key, ProvenanceRole::LexemeText)
    }

    fn cell(
        &mut self,
        key: &ProvenanceKey,
        _: &<HostStage as crate::Stage>::Nominal,
        _: &[CellTermField<HostStage>],
        _: bool,
    ) -> Result<(), Self::Error> {
        self.node(key, TermRole::ApplicationHead.on_side(self.side))?;
        // The fragment's cell path is denoted by its declaration reference,
        // which carries no key.
        self.implicit(TermRole::Path.on_side(self.side));
        Ok(())
    }

    fn sort_test(
        &mut self,
        key: &ProvenanceKey,
        _: crate::SortTestKind,
        sort: &HostSortReference,
    ) -> Result<(), Self::Error> {
        self.node(&sort.key, ProvenanceRole::SortTestSort)?;
        self.node(key, ProvenanceRole::SortTest)
    }

    fn application_instance(&mut self, sort: &HostSortReference) -> Result<(), Self::Error> {
        self.node(&sort.key, ProvenanceRole::ApplicationInstance)
    }

    fn pattern_as(
        &mut self,
        key: &ProvenanceKey,
        binding_key: &ProvenanceKey,
        _: &str,
    ) -> Result<(), Self::Error> {
        self.node(key, ProvenanceRole::PatternAs)?;
        self.node(binding_key, ProvenanceRole::PatternAsBinding)
    }

    fn pattern_or(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        self.node(key, ProvenanceRole::PatternOr)
    }

    fn matches(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        self.node(key, ProvenanceRole::Matches)
    }

    fn matches_pattern(&mut self, inside: bool) {
        self.in_matches_pattern = inside;
    }

    fn let_binding(
        &mut self,
        key: &ProvenanceKey,
        sort: Option<&HostSortReference>,
    ) -> Result<(), Self::Error> {
        if let Some(sort) = sort {
            self.node(&sort.key, ProvenanceRole::LetSort)?;
        }
        self.node(key, ProvenanceRole::Let)
    }

    fn let_pattern(&mut self, inside: bool) {
        self.in_let_pattern = inside;
    }

    fn closure(
        &mut self,
        key: &ProvenanceKey,
        binder_key: &ProvenanceKey,
        sort: &HostSortReference,
    ) -> Result<(), Self::Error> {
        self.node(key, ProvenanceRole::MlConnective)?;
        self.node(binder_key, ProvenanceRole::MlBinder)?;
        self.node(&sort.key, ProvenanceRole::MlBinderSort)
    }

    fn let_body(&mut self, _: Option<&BTreeSet<String>>) {}

    fn rewrite(
        &mut self,
        key: &ProvenanceKey,
        from_key: &ProvenanceKey,
        to_key: &ProvenanceKey,
        _: bool,
    ) -> Result<(), Self::Error> {
        self.node(key, ProvenanceRole::RuleLocalRewrite)?;
        self.node(from_key, ProvenanceRole::RuleLocalRewriteFrom)?;
        self.node(to_key, ProvenanceRole::RuleLocalRewriteTo)
    }

    fn rewrite_right(&mut self, _: bool) {}

    fn argument(
        &mut self,
        argument: crate::TermArgumentRef<'_, HostStage>,
        _: &mut BTreeSet<crate::ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        if let crate::TermArgumentRef::Named { key, .. } = argument {
            self.node(key, TermRole::RecordFieldName.on_side(self.side))?;
        }
        Ok(())
    }

    fn cell_field(
        &mut self,
        field: &CellTermField<HostStage>,
        _: &mut BTreeSet<crate::ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        self.node(&field.key, TermRole::RecordFieldName.on_side(self.side))
    }

    fn record_update(&mut self, base: &HostTerm) -> Result<(), Self::Error> {
        validate_term(base, self)
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
                result: Some(ProtocolHeadRuleResult::Splice(vec![crate::Term::Literal {
                    key: key(ProvenanceRole::RuleRightLiteral, 0),
                    literal: crate::DescriptorLiteral::Int("1".to_owned()),
                }])),
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
    /// node, the clause's declaration is fixed, and the result type, the
    /// splice and its item pair with their anchors though no field carries
    /// their keys.
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

        // A spliced item with no anchor of its own: the pairing runs out.
        let mut spliced = rule.clone();
        let Some(ProtocolHeadRuleResult::Splice(items)) =
            spliced.head.as_mut().and_then(|head| head.result.as_mut())
        else {
            unreachable!()
        };
        items.push(crate::Term::Literal {
            key: ProvenanceKey::new(ProvenanceRole::RuleRightLiteral, 1),
            literal: crate::DescriptorLiteral::Int("2".to_owned()),
        });
        let mut with_literal = anchors.clone();
        with_literal.push(ProvenanceKey::new(ProvenanceRole::RuleRightLiteral, 1));
        assert_eq!(
            spliced.validate_complete_provenance(&with_literal),
            Err(crate::StateTransportError::MissingProvenance(
                ProvenanceKey::new(ProvenanceRole::RuleRightKSequenceItem, 1)
            ))
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

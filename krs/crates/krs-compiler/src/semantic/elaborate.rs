//! A readable rule's `cells!` rule: the [`DescriptorConfigurationRule`] a readable rule
//! elaborates to once its binders' sorts are inferred, which is what the rule means. The pass
//! [`elaborate_readable_rules`] replaces each readable rule's descriptor by its elaboration's
//! before any descriptor-wide check reads a rule, so every later pass reads one form of a rule.
//!
//! The elaborated rule is built in memory and never serialized. Each key it needs and a readable
//! rule lacks is borrowed from the nearest authored readable node, so a diagnostic on it lands
//! on source the author wrote.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    CellWrapper, ConfigurationSentenceKind, Descriptor, DescriptorClaim, DescriptorClaimBinder,
    DescriptorConfigurationReference, DescriptorConfigurationRule, DescriptorHeadRule,
    DescriptorIndex, DescriptorKSequenceNotation, DescriptorNodeOrigin, DescriptorPayload,
    DescriptorRuleCells, DescriptorSortRef, DescriptorSortReference, DescriptorTerm,
    ProtocolCellContent, ProtocolHeadRuleExtra, ProtocolHeadRuleResult, ProtocolInstanceRest,
    ProtocolRuleBinding, ProtocolRuleBindingKind, ProtocolRuleFrame, ProtocolRuleInstances,
    ProtocolRuleKSequence, ProtocolRuleKSequenceItem, ProtocolRuleMap, ProtocolRuleMapBody,
    ProtocolRuleMapItem, ProtocolRuleStateTerm, ProvenanceKey, SentenceKind, StableItemId,
};
use krs_ir_levels::SemanticSortRef;

type DescriptorRuleCell = krs_ir::ProtocolRuleCell<krs_ir::DescriptorCellReference, DescriptorTerm>;
use krs_syntax::ProvenanceRole;

use super::catalog::ProductionSignature;
use super::error::DescriptorLoweringError;
use super::origin::{key_range, role_key};
use super::references::{declared_multiplicity, require_cell_field};

/// What a readable rule's elaboration records beside its descriptor, which the descriptor
/// cannot say: compiler-internal, never on the wire. An authored `cells!` rule has none.
#[derive(Debug, Default)]
pub(super) struct ReadableNotes {
    /// The keys of the rule's anonymous frames the readable author wrote no `..` for.
    pub(super) inserted_frames: BTreeSet<ProvenanceKey>,
}

/// A bundle's readable rules, each replaced by its elaboration ([`elaborate_readable_rules`]).
#[derive(Debug, Default)]
pub(super) struct ReadableRules {
    /// Each readable rule's elaborated descriptor (its id, a `ConfigurationRule` payload) and
    /// notes, or the refusal its inference, a readable-only check or its elaboration gives.
    rules: BTreeMap<StableItemId, Result<(Descriptor, ReadableNotes), DescriptorLoweringError>>,
}

impl ReadableRules {
    /// The descriptor every later pass reads for `descriptor`: its elaboration's, for a readable
    /// rule that elaborates, else `descriptor` itself.
    pub(super) fn descriptor<'a>(&'a self, descriptor: &'a Descriptor) -> &'a Descriptor {
        match self.rules.get(descriptor.id()) {
            Some(Ok((elaborated, _))) => elaborated,
            _ => descriptor,
        }
    }

    /// The notes of the rule `id` when it is an elaborated readable rule.
    pub(super) fn notes(&self, id: &StableItemId) -> Option<&ReadableNotes> {
        match self.rules.get(id) {
            Some(Ok((_, notes))) => Some(notes),
            _ => None,
        }
    }

    /// The refusal of the readable rule `id`, which stays a readable rule for lowering to
    /// report where the rule's sentence is lowered: a sentence's own resolution error.
    pub(super) fn refusal(&self, id: &StableItemId) -> Option<&DescriptorLoweringError> {
        match self.rules.get(id) {
            Some(Err(error)) => Some(error),
            _ => None,
        }
    }
}

/// Elaborates every readable rule of `descriptors`: its binders' sorts inferred and its
/// readable-only checks made ([`super::rules::infer_head_rule_sorts`]), then [`elaborate`]d.
/// Run once the declarations, the sort parents and the production catalog exist, before any
/// descriptor-wide check reads a rule.
pub(super) fn elaborate_readable_rules(
    descriptors: &[&Descriptor],
    declarations: &DescriptorIndex<'_>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> ReadableRules {
    let rules = descriptors
        .iter()
        .filter_map(|descriptor| {
            let DescriptorPayload::HeadRule(rule) = descriptor.payload() else {
                return None;
            };
            let elaborated = super::rules::infer_head_rule_sorts(
                descriptor,
                rule,
                declarations,
                sort_parents,
                catalog,
            )
            .and_then(|inferred| elaborate(descriptor, rule, &inferred, declarations, catalog))
            .and_then(|elaboration| match elaboration {
                Ok(Elaboration {
                    descriptor,
                    inserted_frames,
                    ..
                }) => Ok((descriptor, ReadableNotes { inserted_frames })),
                Err(Unelaborated(form)) => Err(DescriptorLoweringError::unsupported_shape(
                    "readable rule",
                    format!("{form} has no `cells!` rule"),
                )
                .within(
                    descriptor.id(),
                    key_range(descriptor, &rule.pattern_key).as_ref(),
                )),
            });
            Some((descriptor.id().clone(), elaborated))
        })
        .collect();
    ReadableRules { rules }
}

/// A readable form [`elaborate`] has no `cells!` rule for yet.
#[derive(Debug)]
pub(super) struct Unelaborated(&'static str);

/// The `cells!` rule `rule` means, its binders at the sorts `inferred` (inference's, before any
/// state is lowered): the rule `krs expand` prints for it (`reference.rs` `render_rule`), taken
/// in the long form of its record updates, whose hidden binders are declared at their fields'
/// declared sorts. It comes as a copy of `descriptor` whose payload is that rule and whose
/// provenance gives each node the elaboration adds a key of its own ([`NodeKeys`]).
pub(super) fn elaborate(
    descriptor: &Descriptor,
    rule: &DescriptorHeadRule,
    inferred: &BTreeMap<String, SemanticSortRef>,
    declarations: &DescriptorIndex<'_>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<Result<Elaboration, Unelaborated>, DescriptorLoweringError> {
    let (mut rule, hidden) =
        super::record_updates::head_rule_long_form_in(descriptor, rule, catalog, declarations)?;
    let closing = Closing {
        catalog,
        key: &rule.pattern_key.clone(),
    };
    closing.rule(&mut rule);
    let mut keys = NodeKeys::new(descriptor);
    keys.rule(&mut rule);
    let mut sorts = inferred.clone();
    for (id, sort) in hidden {
        // A parametric production's field has its instance's sort: the sort arguments the base's
        // pattern writes give it, and a pattern that writes none leaves it unknown.
        let sort = sort.map_err(|(field, key)| {
            DescriptorLoweringError::invalid_term(
                descriptor.id(),
                format!(
                    "the field `{}` of a parametric record takes the sort of its instance; write the field, or fix the instance with a turbofish",
                    field.as_str()
                ),
            )
            .within(descriptor.id(), key_range(descriptor, &key).as_ref())
        })?;
        sorts.insert(id.as_str().to_owned(), sort);
    }
    let elaborated = match (Elaborator {
        rule: &rule,
        declarations,
        sorts: &sorts,
    }
    .rule(&mut keys))
    {
        Ok(elaborated) => elaborated,
        Err(unelaborated) => return Ok(Err(unelaborated)),
    };
    let copy = descriptor
        .with_generated_nodes(
            DescriptorPayload::ConfigurationRule(Box::new(elaborated)),
            keys.origins,
        )
        .map_err(|error| {
            DescriptorLoweringError::unsupported_shape("elaborated rule", error.to_string())
        })?;
    Ok(Ok(Elaboration {
        descriptor: copy,
        inserted_frames: keys.inserted_frames,
    }))
}

/// What [`elaborate`] makes of a readable rule.
pub(super) struct Elaboration {
    /// The readable rule's descriptor with the elaborated rule as its payload.
    pub(super) descriptor: Descriptor,
    /// The keys of the rule's anonymous frames the readable author wrote no `..` for.
    pub(super) inserted_frames: BTreeSet<ProvenanceKey>,
}

struct Elaborator<'a> {
    rule: &'a DescriptorHeadRule,
    declarations: &'a DescriptorIndex<'a>,
    sorts: &'a BTreeMap<String, SemanticSortRef>,
}

type Elaborated<T> = Result<T, Unelaborated>;

/// The names the elaborated rule introduces beside the readable binders: the remainders a
/// collection entry's `..` and an instance's `k` tail stand for, named as the print names them,
/// each fresh against every name taken before it.
struct Names {
    reserved: BTreeSet<String>,
    /// Instance `k` tails named so far (`tail0`, `tail1`, ..), across the rule's entries.
    tails: usize,
    /// Sorted wildcards declared so far.
    wildcards: usize,
    /// The frames these names bind, and the sorted wildcards of a `for Sort` head, in the order
    /// named.
    frames: Vec<ProtocolRuleBinding<DescriptorSortReference>>,
}

impl Names {
    fn fresh(&mut self, base: &str) -> String {
        // One of `reserved.len() + 1` candidates is free.
        let name = (0..=self.reserved.len())
            .map(|ordinal| {
                if ordinal == 0 {
                    base.to_owned()
                } else {
                    format!("{base}{ordinal}")
                }
            })
            .find(|name| !self.reserved.contains(name))
            .expect("one of more names than the reserved ones is free");
        self.reserved.insert(name.clone());
        name
    }

    fn frame(
        &mut self,
        base: &str,
        kind: ProtocolRuleBindingKind<DescriptorSortReference>,
    ) -> String {
        let name = self.fresh(base);
        self.frames.push(ProtocolRuleBinding {
            name: name.clone(),
            kind,
        });
        name
    }

    /// A head `_` of a `for Sort` clause, which matches any one item of that sort: a wildcard
    /// declared at it. `cells!` source writes no sorted `_`, so the binding takes the reserved
    /// wildcard id a lowered `_` bears, unique among the rule's ids (the `cells!` lowering
    /// numbers its own wildcards past every declared one); how the print spells it is S6-2c's.
    fn sorted_wildcard(
        &mut self,
        key: &ProvenanceKey,
        sort: &DescriptorSortReference,
    ) -> DescriptorTerm {
        let name = krs_ir::SemanticId::wildcard(self.wildcards)
            .as_str()
            .to_owned();
        self.wildcards += 1;
        self.frames.push(ProtocolRuleBinding {
            name: name.clone(),
            kind: ProtocolRuleBindingKind::Term {
                sort: DescriptorSortReference {
                    key: key.clone(),
                    sort: sort.sort.clone(),
                },
            },
        });
        DescriptorTerm::Variable {
            key: key.clone(),
            path_key: key.clone(),
            name,
        }
    }
}

impl Elaborator<'_> {
    #[expect(
        clippy::too_many_lines,
        reason = "Each field of the `cells!` rule is set once, in the rule's order."
    )]
    fn rule(&self, keys: &mut NodeKeys<'_>) -> Elaborated<DescriptorConfigurationRule> {
        let rule = self.rule;
        let sentence_kind = match rule.sentence_kind {
            SentenceKind::Transition => ConfigurationSentenceKind::Transition,
            SentenceKind::Claim => ConfigurationSentenceKind::Claim,
            _ => return Err(Unelaborated("a sentence kind other than a rule or a claim")),
        };
        // What the rule is about: the configuration (or the group) the clause names, else, for
        // a `for Sort` table clause, its head sort.
        let subject_key = rule
            .configuration_key
            .clone()
            .or_else(|| rule.head_sort.as_ref().map(|sort| sort.key.clone()))
            .unwrap_or_else(|| rule.pattern_key.clone());
        let configuration = |key: ProvenanceKey| DescriptorConfigurationReference {
            key,
            configuration: rule.configuration.clone(),
            subject: rule.subject.clone(),
        };
        let mut bindings = Vec::new();
        let mut universals = Vec::new();
        for binding in &rule.bindings {
            let sort = self
                .sorts
                .get(&binding.name)
                .ok_or(Unelaborated("a binding inference gave no sort"))?;
            // A `where` sort is the binder's declaration; an inferred one is declared at the
            // binder's first occurrence in the subject, where a declaration it contradicts is
            // reported, else at the subject.
            let key = binding.refinement.as_ref().map_or_else(
                || {
                    first_in_subject(rule, &binding.name)
                        .unwrap_or(&rule.pattern_key)
                        .clone()
                },
                |refinement| refinement.key.clone(),
            );
            let sort = DescriptorSortReference {
                key,
                sort: descriptor_sort(sort),
            };
            // A claim quantifies every variable it has, and lists each at the node that
            // declares it: a binder the author wrote, or an update's hidden binder at the node
            // the long form writes for it.
            if rule.claim.is_some() {
                universals.push(DescriptorClaimBinder {
                    declaration_key: sort.key.clone(),
                    name_key: sort.key.clone(),
                    name: binding.name.clone(),
                    sort: sort.clone(),
                });
            }
            bindings.push(ProtocolRuleBinding {
                name: binding.name.clone(),
                kind: ProtocolRuleBindingKind::Term { sort },
            });
        }
        // The cells the rule leaves out, a configuration frame the subject binds and the
        // result keeps, under a name no binder has.
        let mut names = Names {
            reserved: rule
                .bindings
                .iter()
                .map(|binding| binding.name.as_str())
                .chain(
                    rule.existentials
                        .iter()
                        .chain(&rule.fresh)
                        .map(|binder| binder.name.as_str()),
                )
                .map(str::to_owned)
                .collect(),
            tails: 0,
            wildcards: 0,
            frames: Vec::new(),
        };
        let state = names.fresh("state");
        let (subject, result) = self.cells(&mut names, keys)?;
        bindings.append(&mut names.frames);
        bindings.push(ProtocolRuleBinding {
            name: state.clone(),
            kind: ProtocolRuleBindingKind::ConfigurationFrame,
        });
        let claim = rule.claim.as_ref().map(|claim| DescriptorClaim {
            declaration_key: role_key(ProvenanceRole::ClaimDeclaration, 0),
            modality_key: claim.modality_key.clone(),
            modality: claim.modality,
            circularity_key: claim.circularity_key.clone(),
            trusted_key: claim.trusted_key.clone(),
            universals,
            existentials: rule.existentials.clone(),
            ensures: rule.ensures.clone(),
            or_bool_keys: Vec::new(),
        });
        let transition = |value| if claim.is_some() { None } else { value };
        Ok(DescriptorConfigurationRule {
            sentence_kind,
            label: rule.label.clone(),
            priority: rule.priority.clone(),
            nondet: rule.nondet.clone(),
            skipped_operand: rule.skipped_operand.clone(),
            requires: rule.requires.clone(),
            pattern_key: rule.pattern_key.clone(),
            subject_configuration: configuration(subject_key),
            result_key: Some(rule.result_key.clone()),
            result_configuration: Some(configuration(rule.result_type_key.clone())),
            bindings,
            subject: DescriptorRuleCells {
                key: rule.pattern_key.clone(),
                cells: subject,
                remainder: ProtocolRuleFrame::Bind {
                    key: rule.pattern_key.clone(),
                    binding: state.clone(),
                },
            },
            result: Some(DescriptorRuleCells {
                key: rule.result_key.clone(),
                cells: result,
                remainder: ProtocolRuleFrame::Reuse {
                    key: rule.result_key.clone(),
                    binding: state,
                },
            }),
            existentials: if claim.is_some() {
                Vec::new()
            } else {
                rule.existentials.clone()
            },
            ensures: transition(rule.ensures.clone()),
            fresh: rule.fresh.clone(),
            evaluation: rule.evaluation.clone(),
            claim,
        })
    }

    /// The subject's and the result's cells: the computation cell's head first, then each
    /// extra in the order written.
    fn cells(
        &self,
        names: &mut Names,
        keys: &mut NodeKeys<'_>,
    ) -> Elaborated<(Vec<DescriptorRuleCell>, Vec<DescriptorRuleCell>)> {
        let rule = self.rule;
        let mut subject = Vec::new();
        let mut result = Vec::new();
        if let (Some(head), Some(computation)) = (&rule.head, &rule.computation_cell) {
            // The readable lowering locates the computation clause at the rule's pattern,
            // whether or not the clause names the computation cell (a table clause does not).
            let key = rule.pattern_key.clone();
            let field = krs_ir::DescriptorCellReference {
                key: key.clone(),
                cell: computation.cell.clone(),
            };
            let tail = |key: &ProvenanceKey| {
                if head.exact {
                    ProtocolRuleFrame::Exact
                } else {
                    ProtocolRuleFrame::Anonymous {
                        key: head.tail_key.clone().unwrap_or_else(|| key.clone()),
                    }
                }
            };
            let sequence =
                |payload_key: ProvenanceKey,
                 tail_key: &ProvenanceKey,
                 items: Vec<&DescriptorTerm>| DescriptorRuleCell {
                    field: field.clone(),
                    wrapper_key: Some(key.clone()),
                    wrapper: Some(CellWrapper::KCell),
                    value: ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
                        tail: tail(tail_key),
                        payload_key,
                        dot_k_key: None,
                        notation: DescriptorKSequenceNotation::Comma,
                        items: items
                            .into_iter()
                            .map(|term| ProtocolRuleKSequenceItem {
                                key: super::collection_types::term_key(term).clone(),
                                value: term.clone(),
                            })
                            .collect(),
                    }),
                };
            // The matched sequence is the subject's `k: [..]` entry, where a mistake about the
            // sequence as a whole (its items' common sort) is told; a `for Sort` clause names
            // no cell, and its sequence is the clause's pattern. The result's is the result
            // expression.
            let mut subject_key = computation
                .key
                .clone()
                .unwrap_or_else(|| rule.pattern_key.clone());
            keys.key("k-sequence", &mut subject_key);
            let items = head
                .items
                .iter()
                .map(|item| match (item, &rule.head_sort) {
                    (DescriptorTerm::Wildcard { key }, Some(sort)) => {
                        names.sorted_wildcard(key, sort)
                    }
                    _ => item.clone(),
                })
                .collect::<Vec<_>>();
            if !head.exact && head.tail_key.is_none() {
                // A block-form clause leaves the rest of the computation unwritten: its frame
                // is the language's, at the clause.
                keys.inserted_frames.insert(rule.pattern_key.clone());
            }
            subject.push(sequence(
                subject_key,
                &rule.pattern_key,
                items.iter().collect(),
            ));
            if let Some(after) = &head.result {
                let items = match after {
                    ProtocolHeadRuleResult::Replace(term) => vec![term],
                    ProtocolHeadRuleResult::Splice(splice) => splice.terms().collect(),
                    ProtocolHeadRuleResult::Erase => Vec::new(),
                };
                result.push(sequence(rule.result_key.clone(), &rule.result_key, items));
            }
        }
        for (ordinal, extra) in rule.extras.iter().enumerate() {
            let (before, after) = self.extra(extra, ordinal, names, keys)?;
            subject.push(before);
            result.extend(after);
        }
        Ok((subject, result))
    }

    #[expect(
        clippy::too_many_lines,
        reason = "One arm per readable extra, each its `cells!` entries."
    )]
    fn extra(
        &self,
        extra: &ProtocolHeadRuleExtra<krs_ir::DescriptorCellReference, DescriptorTerm>,
        ordinal: usize,
        names: &mut Names,
        keys: &mut NodeKeys<'_>,
    ) -> Elaborated<(DescriptorRuleCell, Option<DescriptorRuleCell>)> {
        let cell = |field: &krs_ir::DescriptorCellReference, value| -> Elaborated<_> {
            let declared = require_cell_field(&field.cell, self.declarations)
                .map_err(|_| Unelaborated("a cell the declarations lack"))?;
            // A leaf's content is wrapped in its cell; a group, an absent cell and an instance
            // list are written without one.
            let wrapped = !matches!(declared.content, ProtocolCellContent::Nested { .. })
                && !matches!(value, ProtocolRuleStateTerm::Absent);
            Ok(DescriptorRuleCell {
                field: field.clone(),
                wrapper_key: wrapped.then(|| field.key.clone()),
                wrapper: wrapped.then_some(CellWrapper::Cell),
                value,
            })
        };
        // A leaf's term is its cell's content; a group's is the group.
        let content = |field: &krs_ir::DescriptorCellReference, term: &DescriptorTerm| {
            let declared = require_cell_field(&field.cell, self.declarations)
                .map_err(|_| Unelaborated("a cell the declarations lack"))?;
            let value = if matches!(declared.content, ProtocolCellContent::Nested { .. }) {
                ProtocolRuleStateTerm::Group(term.clone())
            } else {
                ProtocolRuleStateTerm::Term(term.clone())
            };
            // A value written on an optional cell matches or writes the cell present.
            Ok(
                if declared_multiplicity(declared, self.declarations)
                    == krs_ir::cell_kind::Multiplicity::Optional
                {
                    ProtocolRuleStateTerm::Present {
                        value: Box::new(value),
                    }
                } else {
                    value
                },
            )
        };
        match extra {
            ProtocolHeadRuleExtra::RewriteCell {
                cell: field,
                before,
                after,
                ..
            } => Ok((
                cell(field, content(field, before)?)?,
                after
                    .as_ref()
                    .map(|after| cell(field, content(field, after)?))
                    .transpose()?,
            )),
            ProtocolHeadRuleExtra::HaveMap {
                cell: field,
                entries,
                rest_key,
            } => {
                let items = entries
                    .iter()
                    .map(|entry| ProtocolRuleMapItem {
                        key_key: entry.key_key.clone(),
                        key: entry.key.clone(),
                        value_key: entry.value_key.clone(),
                        value: keys.variable(&entry.value_key, &entry.value_binding),
                    })
                    .collect();
                // A read leaves the other entries as they are; a block-form `have` read, which
                // writes no `..`, by the language's frame at the read.
                if rest_key.is_none() {
                    keys.inserted_frames.insert(field.key.clone());
                }
                let value = ProtocolRuleStateTerm::Map(ProtocolRuleMap {
                    payload_key: field.key.clone(),
                    body: ProtocolRuleMapBody::Items {
                        items,
                        remainder: ProtocolRuleFrame::Anonymous {
                            key: rest_key.clone().unwrap_or_else(|| field.key.clone()),
                        },
                    },
                });
                Ok((cell(field, value)?, None))
            }
            ProtocolHeadRuleExtra::UpdateMap {
                cell: field,
                base_binding,
                update,
            } => Ok((
                cell(
                    field,
                    ProtocolRuleStateTerm::Term(keys.variable(&field.key, base_binding)),
                )?,
                Some(cell(field, ProtocolRuleStateTerm::Term(update.clone()))?),
            )),
            ProtocolHeadRuleExtra::RewriteState {
                cell: field,
                before: ProtocolRuleStateTerm::Instances(before),
                after,
                ..
            } => {
                let after = match after {
                    None => None,
                    Some(ProtocolRuleStateTerm::Instances(after)) => Some(after),
                    Some(_) => return Err(Unelaborated("an instance list rewritten to no list")),
                };
                let (before, after) = instances(before, after, ordinal, names)?;
                Ok((
                    cell(field, ProtocolRuleStateTerm::Instances(before))?,
                    after
                        .map(|after| cell(field, ProtocolRuleStateTerm::Instances(after)))
                        .transpose()?,
                ))
            }
            ProtocolHeadRuleExtra::RewriteState {
                cell: field,
                before,
                after,
                ..
            } => {
                // `Some(..)` and `None` stay as written, so the `cells!` lowering judges them
                // against the cell's multiplicity as it judges an authored entry.
                let state = |state: &ProtocolRuleStateTerm<DescriptorTerm>| match state {
                    ProtocolRuleStateTerm::Absent => Ok(ProtocolRuleStateTerm::Absent),
                    ProtocolRuleStateTerm::Present { value } => match &**value {
                        ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
                            let declared = require_cell_field(&field.cell, self.declarations)
                                .map_err(|_| Unelaborated("a cell the declarations lack"))?;
                            Ok(ProtocolRuleStateTerm::Present {
                                value: Box::new(
                                    if matches!(
                                        declared.content,
                                        ProtocolCellContent::Nested { .. }
                                    ) {
                                        ProtocolRuleStateTerm::Group(term.clone())
                                    } else {
                                        ProtocolRuleStateTerm::Term(term.clone())
                                    },
                                ),
                            })
                        }
                        _ => Err(Unelaborated("a present state holding no term")),
                    },
                    _ => Err(Unelaborated("a cell state other than an optional cell's")),
                };
                Ok((
                    cell(field, state(before)?)?,
                    after
                        .as_ref()
                        .map(|after| cell(field, state(after)?))
                        .transpose()?,
                ))
            }
            ProtocolHeadRuleExtra::RewriteList {
                cell: field,
                before,
                after,
                ..
            } => Ok((
                cell(field, content(field, &list_notation(field, before, keys))?)?,
                after
                    .as_ref()
                    .map(|after| cell(field, content(field, &list_notation(field, after, keys))?))
                    .transpose()?,
            )),
        }
    }
}

/// Where `name` first occurs in `rule`'s subject, in the order the subject is written: the
/// computation's head, then each extra's subject side. A binder occurs as a variable (its own
/// node), as `name @ ..` (its name), or as a map entry's value (the value).
fn first_in_subject<'r>(rule: &'r DescriptorHeadRule, name: &str) -> Option<&'r ProvenanceKey> {
    let terms =
        |terms: Vec<&'r DescriptorTerm>| terms.into_iter().find_map(|term| first_in(term, name));
    if let Some(key) = rule
        .head
        .as_ref()
        .and_then(|head| terms(head.items.iter().collect()))
    {
        return Some(key);
    }
    rule.extras.iter().find_map(|extra| match extra {
        ProtocolHeadRuleExtra::RewriteCell { before, .. } => first_in(before, name),
        ProtocolHeadRuleExtra::HaveMap { entries, .. } => entries.iter().find_map(|entry| {
            first_in(&entry.key, name)
                .or_else(|| (entry.value_binding == name).then_some(&entry.value_key))
        }),
        ProtocolHeadRuleExtra::UpdateMap {
            cell, base_binding, ..
        } => (base_binding == name).then_some(&cell.key),
        ProtocolHeadRuleExtra::RewriteState { before, .. } => terms(before.terms()),
        ProtocolHeadRuleExtra::RewriteList { before, .. } => terms(before.terms()),
    })
}

/// Where `name` first occurs in `term`, in preorder.
fn first_in<'t>(term: &'t DescriptorTerm, name: &str) -> Option<&'t ProvenanceKey> {
    let children: Vec<&DescriptorTerm> = match term {
        DescriptorTerm::Variable {
            key, name: found, ..
        } => return (found == name).then_some(key),
        DescriptorTerm::As {
            binding_key,
            name: found,
            pattern,
            ..
        } => {
            if found == name {
                return Some(binding_key);
            }
            vec![pattern]
        }
        DescriptorTerm::Application {
            arguments, update, ..
        } => match arguments {
            krs_ir::Arguments::Positional(values) => {
                values.iter().map(|value| &**value).collect::<Vec<_>>()
            }
            krs_ir::Arguments::Named(values) => values.iter().map(|value| &*value.value).collect(),
        }
        .into_iter()
        .chain(update.as_deref())
        .collect(),
        DescriptorTerm::Cell { fields, update, .. } => fields
            .iter()
            .map(|field| &*field.value)
            .chain(update.as_deref())
            .collect(),
        DescriptorTerm::OrBool { arguments, .. } => arguments.iter().collect(),
        DescriptorTerm::Or { alternatives, .. } => alternatives.iter().collect(),
        DescriptorTerm::SortTest { operand, .. } => vec![operand],
        DescriptorTerm::Matches {
            subject, pattern, ..
        } => vec![subject, pattern],
        DescriptorTerm::Let {
            pattern,
            value,
            body,
            ..
        } => vec![pattern, value, body],
        DescriptorTerm::Closure { body, .. } => vec![body],
        DescriptorTerm::Rewrite { from, to, .. } => {
            std::iter::once(&**from).chain(to.as_deref()).collect()
        }
        DescriptorTerm::Literal { .. }
        | DescriptorTerm::Wildcard { .. }
        | DescriptorTerm::KeptRest { .. }
        | DescriptorTerm::BuiltinToken { .. }
        | DescriptorTerm::Anonymous { .. }
        | DescriptorTerm::Lexeme { .. } => Vec::new(),
    };
    children.into_iter().find_map(|child| first_in(child, name))
}

/// A readable collection entry as `cells!` writes it: the other instances, `..` on both sides, are
/// one instances frame the subject binds (`instances<ordinal> @ ..`) and the result keeps
/// (`..instances<ordinal>`); an instance's open `k` is a sequence frame its pattern binds
/// (`tail<n> @ ..`), which the result instance updating it (`..label`) keeps. Every other part
/// of an instance is written as the readable entry writes it.
fn instances(
    before: &ProtocolRuleInstances<DescriptorTerm>,
    after: Option<&ProtocolRuleInstances<DescriptorTerm>>,
    ordinal: usize,
    names: &mut Names,
) -> Elaborated<(
    ProtocolRuleInstances<DescriptorTerm>,
    Option<ProtocolRuleInstances<DescriptorTerm>>,
)> {
    let rest = (!matches!(before.rest, ProtocolRuleFrame::Exact)).then(|| {
        names.frame(
            &format!("instances{ordinal}"),
            ProtocolRuleBindingKind::InstancesFrame,
        )
    });
    // Each labelled subject instance's `k` tail, which the result instance updating it reuses.
    let mut tails = BTreeMap::new();
    let mut side = |instances: &ProtocolRuleInstances<DescriptorTerm>,
                    pattern: bool,
                    tails: &mut BTreeMap<String, String>|
     -> Elaborated<ProtocolRuleInstances<DescriptorTerm>> {
        let mut instance = |instance: &krs_ir::ProtocolRuleInstance<DescriptorTerm>| {
            let reused = match &instance.rest {
                ProtocolInstanceRest::Update { label } => tails.get(label).cloned(),
                _ => None,
            };
            let mut instance = instance.clone();
            for field in &mut instance.fields {
                let ProtocolRuleStateTerm::KSequence(sequence) = &mut field.value else {
                    continue;
                };
                sequence.notation = DescriptorKSequenceNotation::Comma;
                let key = match &sequence.tail {
                    ProtocolRuleFrame::Exact => continue,
                    ProtocolRuleFrame::Anonymous { key }
                    | ProtocolRuleFrame::Bind { key, .. }
                    | ProtocolRuleFrame::Reuse { key, .. } => key.clone(),
                };
                sequence.tail = if pattern {
                    let tail = names.frame(
                        &format!("tail{}", names.tails),
                        ProtocolRuleBindingKind::KSequenceFrame,
                    );
                    names.tails += 1;
                    if let Some(label) = &instance.label {
                        tails.insert(label.clone(), tail.clone());
                    }
                    ProtocolRuleFrame::Bind { key, binding: tail }
                } else {
                    let tail = reused.clone().ok_or(Unelaborated(
                        "an open instance `k` no updated instance keeps",
                    ))?;
                    ProtocolRuleFrame::Reuse { key, binding: tail }
                };
            }
            Ok(instance)
        };
        let front = instances
            .front
            .iter()
            .map(&mut instance)
            .collect::<Elaborated<Vec<_>>>()?;
        let back = instances
            .back
            .iter()
            .map(&mut instance)
            .collect::<Elaborated<Vec<_>>>()?;
        let rest = match (&instances.rest, &rest) {
            (ProtocolRuleFrame::Exact, _) => ProtocolRuleFrame::Exact,
            (
                ProtocolRuleFrame::Anonymous { key }
                | ProtocolRuleFrame::Bind { key, .. }
                | ProtocolRuleFrame::Reuse { key, .. },
                Some(rest),
            ) => {
                let binding = rest.clone();
                if pattern {
                    ProtocolRuleFrame::Bind {
                        key: key.clone(),
                        binding,
                    }
                } else {
                    ProtocolRuleFrame::Reuse {
                        key: key.clone(),
                        binding,
                    }
                }
            }
            // `..` on the result side only: the readable lowering refuses it, as cells! does.
            (open, None) => open.clone(),
        };
        Ok(ProtocolRuleInstances {
            delimiter: instances.delimiter,
            front,
            rest,
            back,
        })
    };
    let before = side(before, true, &mut tails)?;
    let after = after
        .map(|after| side(after, false, &mut tails))
        .transpose()?;
    Ok((before, after))
}

/// One side of a readable list cell as the `cells!` term its brackets are: the list-notation
/// levels `cells!` writes (`[a, b, ..r, z]` is `Cons(a, Cons(b, Snoc(r, z)))`), which the `cells!`
/// lowering types at the cell's list, a cons list's constructors or the builtin `List`. An
/// anonymous `..` is the list's unnamed rest ([`DescriptorTerm::KeptRest`]), the one rest the
/// subject matches and the result keeps; exact brackets end in the empty list. Each level is
/// located at the cell entry, where the readable lowering locates the terms it builds.
fn list_notation(
    field: &krs_ir::DescriptorCellReference,
    list: &krs_ir::ProtocolHeadRuleList<DescriptorTerm>,
    keys: &mut NodeKeys<'_>,
) -> DescriptorTerm {
    let level = |keys: &mut NodeKeys<'_>, notation, arguments: Vec<DescriptorTerm>| {
        let mut key = field.key.clone();
        let mut path_key = field.key.clone();
        keys.key("application", &mut key);
        keys.key("application-path", &mut path_key);
        DescriptorTerm::Application {
            head_class: krs_ir::DescriptorApplicationHeadClass::Applied,
            reference: krs_ir::DescriptorApplicationReference {
                key,
                application: krs_ir::DescriptorApplicationRef::ListNotation(notation),
            },
            path_key,
            arguments: krs_ir::Arguments::Positional(arguments.into_iter().map(Box::new).collect()),
            instance: Vec::new(),
            update: None,
            open: false,
        }
    };
    let rest = match &list.rest {
        krs_ir::ProtocolHeadRuleListRest::Exact => {
            level(keys, krs_ir::ListNotation::Empty, Vec::new())
        }
        krs_ir::ProtocolHeadRuleListRest::Shared(key) => {
            let mut key = key.clone().unwrap_or_else(|| field.key.clone());
            keys.key("kept-rest", &mut key);
            DescriptorTerm::KeptRest { key }
        }
        krs_ir::ProtocolHeadRuleListRest::Term(rest) => rest.clone(),
    };
    let back = list.back.iter().fold(rest, |list, item| {
        level(keys, krs_ir::ListNotation::Snoc, vec![list, item.clone()])
    });
    list.items.iter().rev().fold(back, |list, item| {
        level(keys, krs_ir::ListNotation::Cons, vec![item.clone(), list])
    })
}

/// Visits each term of `rule` in the order written: the head's items, its result, each extra's
/// subject side then its result side, then the conditions; `pattern` says whether the term
/// matches.
fn each_term(rule: &mut DescriptorHeadRule, visit: &mut impl FnMut(&mut DescriptorTerm, bool)) {
    if let Some(head) = &mut rule.head {
        for item in &mut head.items {
            visit(item, true);
        }
        match &mut head.result {
            Some(ProtocolHeadRuleResult::Replace(term)) => visit(term, false),
            Some(ProtocolHeadRuleResult::Splice(splice)) => {
                for term in splice.terms_mut() {
                    visit(term, false);
                }
            }
            Some(ProtocolHeadRuleResult::Erase) | None => {}
        }
    }
    for extra in &mut rule.extras {
        match extra {
            ProtocolHeadRuleExtra::HaveMap { entries, .. } => {
                for entry in entries {
                    visit(&mut entry.key, true);
                }
            }
            ProtocolHeadRuleExtra::UpdateMap { update, .. } => visit(update, false),
            ProtocolHeadRuleExtra::RewriteCell { before, after, .. } => {
                visit(before, true);
                if let Some(after) = after {
                    visit(after, false);
                }
            }
            ProtocolHeadRuleExtra::RewriteState { before, after, .. } => {
                state_terms(before, &mut |term| visit(term, true));
                if let Some(after) = after {
                    state_terms(after, &mut |term| visit(term, false));
                }
            }
            ProtocolHeadRuleExtra::RewriteList { before, after, .. } => {
                for term in before.terms_mut() {
                    visit(term, true);
                }
                for term in after
                    .iter_mut()
                    .flat_map(krs_ir::ProtocolHeadRuleList::terms_mut)
                {
                    visit(term, false);
                }
            }
        }
    }
    for condition in rule.requires.iter_mut().chain(&mut rule.ensures) {
        visit(&mut condition.term, false);
    }
}

/// Visits each term of a cell state.
fn state_terms(
    state: &mut ProtocolRuleStateTerm<DescriptorTerm>,
    visit: &mut impl FnMut(&mut DescriptorTerm),
) {
    match state {
        ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => visit(term),
        ProtocolRuleStateTerm::Present { value } => state_terms(value, visit),
        ProtocolRuleStateTerm::KSequence(sequence) => {
            for item in &mut sequence.items {
                visit(&mut item.value);
            }
        }
        ProtocolRuleStateTerm::Instances(instances) => {
            for instance in instances.front.iter_mut().chain(&mut instances.back) {
                for field in &mut instance.fields {
                    state_terms(&mut field.value, visit);
                }
            }
        }
        ProtocolRuleStateTerm::Map(_) | ProtocolRuleStateTerm::Absent => {}
    }
}

/// Closes a rule's constructor records, as the print writes them: a constructor applied to named
/// fields is applied to every field in declaration order, and in a pattern each field the record
/// leaves out (`Ctor { a, .. }`, `Ctor { .. }`) is `_`, which matches it whatever it holds. A
/// `cells!` term names a constructor's arguments by position, so an open constructor record is
/// no `cells!` term. A group record stays open: `cells!` writes `G { a, .. }`.
struct Closing<'a> {
    catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    /// Where a field a pattern leaves out is located: the rule's pattern, as the readable
    /// lowering locates such a field's wildcard.
    key: &'a ProvenanceKey,
}

impl Closing<'_> {
    fn rule(&self, rule: &mut DescriptorHeadRule) {
        each_term(rule, &mut |term, pattern| {
            let open = std::mem::replace(
                term,
                DescriptorTerm::Wildcard {
                    key: self.key.clone(),
                },
            );
            *term = self.term(open, pattern);
        });
    }

    /// `term` with its constructor records closed; `pattern` says whether it matches.
    #[expect(
        clippy::too_many_lines,
        reason = "One arm per term form, each rebuilding it around its closed subterms."
    )]
    fn term(&self, term: DescriptorTerm, pattern: bool) -> DescriptorTerm {
        let nested = |term: Box<DescriptorTerm>, pattern| Box::new(self.term(*term, pattern));
        match term {
            DescriptorTerm::Application {
                head_class,
                reference,
                path_key,
                arguments,
                instance,
                update,
                open,
            } => {
                let update = update.map(|update| nested(update, false));
                let arguments = match arguments {
                    krs_ir::Arguments::Positional(values) => krs_ir::Arguments::Positional(
                        values
                            .into_iter()
                            .map(|value| nested(value, pattern))
                            .collect(),
                    ),
                    krs_ir::Arguments::Named(values) => krs_ir::Arguments::Named(
                        values
                            .try_map(|argument| {
                                Ok::<_, std::convert::Infallible>(krs_ir::NamedTermArgument {
                                    value: nested(argument.value, pattern),
                                    ..argument
                                })
                            })
                            .unwrap_or_else(|never| match never {}),
                    ),
                };
                let fields = match &reference.application {
                    krs_ir::DescriptorApplicationRef::Declared(id) if update.is_none() => {
                        self.catalog.get(id).map(|signature| &signature.fields)
                    }
                    _ => None,
                };
                let named = matches!(arguments, krs_ir::Arguments::Named(_));
                let (arguments, open) = match fields {
                    Some(fields) if named || (open && pattern) => {
                        // Only a record is open, and its arguments are named: one that names no
                        // field (`Ctor { .. }`) has none, which is no named list.
                        // `krs-syntax` reads a positional application closed, and the long form
                        // writes a constructor's arguments named.
                        debug_assert!(
                            named
                                || matches!(&arguments, krs_ir::Arguments::Positional(values) if values.is_empty()),
                            "an open application with positional arguments"
                        );
                        let mut supplied = match &arguments {
                            krs_ir::Arguments::Named(values) => values
                                .iter()
                                .map(|argument| (argument.field.clone(), argument.value.clone()))
                                .collect::<BTreeMap<_, _>>(),
                            krs_ir::Arguments::Positional(_) => BTreeMap::new(),
                        };
                        let closed = fields
                            .iter()
                            .map(|(field, _)| {
                                supplied.remove(field).or_else(|| {
                                    pattern.then(|| {
                                        Box::new(DescriptorTerm::Wildcard {
                                            key: self.key.clone(),
                                        })
                                    })
                                })
                            })
                            .collect::<Option<Vec<_>>>();
                        // A record expression that leaves a field out, or names one the
                        // constructor lacks, stays as written: both lowerings refuse it.
                        match closed {
                            Some(closed) if supplied.is_empty() => {
                                (krs_ir::Arguments::Positional(closed), false)
                            }
                            _ => (arguments, open),
                        }
                    }
                    _ => (arguments, open),
                };
                DescriptorTerm::Application {
                    head_class,
                    reference,
                    path_key,
                    arguments,
                    instance,
                    update,
                    open,
                }
            }
            DescriptorTerm::OrBool { key, arguments } => DescriptorTerm::OrBool {
                key,
                arguments: arguments
                    .try_map(|term| Ok::<_, std::convert::Infallible>(self.term(term, pattern)))
                    .unwrap_or_else(|never| match never {}),
            },
            DescriptorTerm::Or { key, alternatives } => DescriptorTerm::Or {
                key,
                alternatives: alternatives
                    .try_map(|term| Ok::<_, std::convert::Infallible>(self.term(term, pattern)))
                    .unwrap_or_else(|never| match never {}),
            },
            DescriptorTerm::Cell {
                key,
                path_key,
                declaration,
                fields,
                open,
                update,
            } => DescriptorTerm::Cell {
                key,
                path_key,
                declaration,
                fields: fields
                    .into_iter()
                    .map(|field| krs_ir::CellTermField {
                        value: nested(field.value, pattern),
                        ..field
                    })
                    .collect(),
                open,
                update: update.map(|update| nested(update, false)),
            },
            DescriptorTerm::SortTest {
                key,
                kind,
                sort,
                operand,
            } => DescriptorTerm::SortTest {
                key,
                kind,
                sort,
                operand: nested(operand, pattern),
            },
            DescriptorTerm::As {
                key,
                binding_key,
                name,
                pattern: inner,
            } => DescriptorTerm::As {
                key,
                binding_key,
                name,
                pattern: nested(inner, pattern),
            },
            DescriptorTerm::Matches {
                key,
                subject,
                pattern: inner,
            } => DescriptorTerm::Matches {
                key,
                subject: nested(subject, pattern),
                pattern: nested(inner, true),
            },
            DescriptorTerm::Let {
                key,
                pattern: inner,
                sort,
                value,
                body,
            } => DescriptorTerm::Let {
                key,
                pattern: nested(inner, true),
                sort,
                value: nested(value, pattern),
                body: nested(body, pattern),
            },
            DescriptorTerm::Closure {
                key,
                binder_key,
                name,
                sort,
                body,
            } => DescriptorTerm::Closure {
                key,
                binder_key,
                name,
                sort,
                body: nested(body, pattern),
            },
            DescriptorTerm::Rewrite {
                key,
                from_key,
                to_key,
                from,
                to,
            } => DescriptorTerm::Rewrite {
                key,
                from_key,
                to_key,
                from: nested(from, pattern),
                to: to.map(|to| nested(to, false)),
            },
            term @ (DescriptorTerm::Variable { .. }
            | DescriptorTerm::Literal { .. }
            | DescriptorTerm::Wildcard { .. }
            | DescriptorTerm::KeptRest { .. }
            | DescriptorTerm::BuiltinToken { .. }
            | DescriptorTerm::Anonymous { .. }
            | DescriptorTerm::Lexeme { .. }) => term,
        }
    }
}

/// Gives each node of an elaborated rule a provenance key of its own. The long form and
/// [`Closing`] write each node they add (a field an update keeps, a field a pattern leaves out, a
/// rebuilt group's children) at the key of the authored node it stands at, so several nodes of one
/// kind can share a key; a `cells!` rule has one key per node, as its print would when parsed. The
/// first node of a kind at a key keeps the key, so every authored node keeps its own; each later
/// one gets the next ordinal of the key's role past every key the descriptor holds (the parser
/// numbers a role's occurrences from zero), with the origin of the node it stands at, so a
/// diagnostic on it reports that node's range.
struct NodeKeys<'a> {
    descriptor: &'a Descriptor,
    /// Each (kind of node, key) given so far.
    taken: BTreeSet<(&'static str, ProvenanceKey)>,
    /// The next free ordinal of each role a key has been made for.
    next: BTreeMap<ProvenanceRole, u32>,
    /// The origin of each key made.
    origins: Vec<DescriptorNodeOrigin>,
    /// The keys of the anonymous frames the readable author wrote no `..` for, which the
    /// `cells!` lowering marks inserted
    /// ([`super::configuration_rules::lower_configuration_rule_with_inserted_frames`]).
    inserted_frames: BTreeSet<ProvenanceKey>,
}

impl<'a> NodeKeys<'a> {
    fn new(descriptor: &'a Descriptor) -> Self {
        Self {
            descriptor,
            taken: BTreeSet::new(),
            next: BTreeMap::new(),
            origins: Vec::new(),
            inserted_frames: BTreeSet::new(),
        }
    }

    /// Keys the nodes of `rule`'s terms, in the order written.
    fn rule(&mut self, rule: &mut DescriptorHeadRule) {
        each_term(rule, &mut |term, _| self.term(term));
    }

    /// A variable term naming `name`, which the elaboration writes at the node `key` names.
    fn variable(&mut self, key: &ProvenanceKey, name: &str) -> DescriptorTerm {
        let mut term = DescriptorTerm::Variable {
            key: key.clone(),
            path_key: key.clone(),
            name: name.to_owned(),
        };
        self.term(&mut term);
        term
    }

    /// `key`, a key of a node of kind `node`, or a fresh key located where `key` is when a node of
    /// that kind already has it.
    fn key(&mut self, node: &'static str, key: &mut ProvenanceKey) {
        if self.taken.insert((node, key.clone())) {
            return;
        }
        // A key the descriptor does not hold is refused where the lowering looks it up.
        let Some(origin) = self.descriptor.provenance().origin_for(key) else {
            return;
        };
        let role = key.role();
        let provenance = self.descriptor.provenance();
        let ordinal = self.next.entry(role).or_insert_with(|| {
            provenance
                .origins()
                .iter()
                .filter(|node| node.key.role() == role)
                .map(|node| node.key.ordinal() + 1)
                .max()
                .unwrap_or(0)
        });
        let fresh = ProvenanceKey::new(role, *ordinal);
        *ordinal += 1;
        self.origins
            .push(DescriptorNodeOrigin::new(fresh.clone(), origin.clone()));
        self.taken.insert((node, fresh.clone()));
        *key = fresh;
    }

    fn term(&mut self, term: &mut DescriptorTerm) {
        match term {
            DescriptorTerm::Variable { key, path_key, .. } => {
                self.key("variable", key);
                self.key("variable-path", path_key);
            }
            DescriptorTerm::Application {
                reference,
                path_key,
                arguments,
                update,
                ..
            } => {
                self.key("application", &mut reference.key);
                self.key("application-path", path_key);
                match arguments {
                    krs_ir::Arguments::Positional(values) => {
                        for value in values {
                            self.term(value);
                        }
                    }
                    krs_ir::Arguments::Named(values) => {
                        for argument in values.iter_mut() {
                            self.key("argument", &mut argument.key);
                            self.term(&mut argument.value);
                        }
                    }
                }
                if let Some(update) = update {
                    self.term(update);
                }
            }
            DescriptorTerm::Wildcard { key } => self.key("wildcard", key),
            DescriptorTerm::KeptRest { key } => self.key("kept-rest", key),
            DescriptorTerm::Cell {
                key,
                path_key,
                fields,
                update,
                ..
            } => {
                self.key("cell", key);
                self.key("cell-path", path_key);
                for field in fields {
                    self.key("cell-field", &mut field.key);
                    self.term(&mut field.value);
                }
                if let Some(update) = update {
                    self.term(update);
                }
            }
            DescriptorTerm::As {
                key,
                binding_key,
                pattern,
                ..
            } => {
                self.key("as", key);
                // The name an alias binds is a variable as a variable term is: one node names
                // one binder.
                self.key("variable", binding_key);
                self.term(pattern);
            }
            DescriptorTerm::OrBool { arguments, .. } => {
                for argument in arguments.iter_mut() {
                    self.term(argument);
                }
            }
            DescriptorTerm::Or { alternatives, .. } => {
                for alternative in alternatives.iter_mut() {
                    self.term(alternative);
                }
            }
            DescriptorTerm::SortTest { operand, .. } => self.term(operand),
            DescriptorTerm::Matches {
                subject, pattern, ..
            } => {
                self.term(subject);
                self.term(pattern);
            }
            DescriptorTerm::Let {
                pattern,
                value,
                body,
                ..
            } => {
                self.term(pattern);
                self.term(value);
                self.term(body);
            }
            DescriptorTerm::Closure { body, .. } => self.term(body),
            DescriptorTerm::Rewrite { from, to, .. } => {
                self.term(from);
                if let Some(to) = to {
                    self.term(to);
                }
            }
            // No pass adds one of these: each is the authored node.
            DescriptorTerm::Literal { .. }
            | DescriptorTerm::BuiltinToken { .. }
            | DescriptorTerm::Anonymous { .. }
            | DescriptorTerm::Lexeme { .. } => {}
        }
    }
}

fn descriptor_sort(sort: &SemanticSortRef) -> DescriptorSortRef {
    match sort {
        SemanticSortRef::Declared(id) => DescriptorSortRef::Declared(id.clone()),
        SemanticSortRef::Builtin(sort) => DescriptorSortRef::Builtin(*sort),
        SemanticSortRef::Cell(id) => DescriptorSortRef::Cell(id.clone()),
        SemanticSortRef::Parameter(name) => DescriptorSortRef::Parameter(name.as_str().to_owned()),
    }
}

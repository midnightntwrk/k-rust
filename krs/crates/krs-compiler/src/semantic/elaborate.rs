//! A readable rule's `cells!` rule (S6 phase 2): the [`DescriptorConfigurationRule`] a readable
//! rule elaborates to once its binders' sorts are inferred, and the shadow check that lowers it
//! beside the readable lowering and refuses the rule where the two disagree.
//!
//! The elaborated rule is built in memory and never serialized. Each key it needs and a readable
//! rule lacks is borrowed from the nearest authored readable node, so a diagnostic on it lands
//! on source the author wrote.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

use krs_ir::{
    CellWrapper, ConfigurationSentenceKind, Descriptor, DescriptorClaim, DescriptorClaimBinder,
    DescriptorConfigurationReference, DescriptorConfigurationRule, DescriptorHeadRule,
    DescriptorIndex, DescriptorKSequenceNotation, DescriptorRuleCells, DescriptorSortRef,
    DescriptorSortReference, DescriptorTerm, ProtocolCellContent, ProtocolHeadRuleExtra,
    ProtocolHeadRuleResult, ProtocolRuleBinding, ProtocolRuleBindingKind, ProtocolRuleFrame,
    ProtocolRuleKSequence, ProtocolRuleKSequenceItem, ProtocolRuleMap, ProtocolRuleMapBody,
    ProtocolRuleMapItem, ProtocolRuleStateTerm, ProvenanceKey, SentenceKind, StableItemId,
};
use krs_ir_levels::{SemanticRule, SemanticSortRef};

type DescriptorRuleCell = krs_ir::ProtocolRuleCell<krs_ir::DescriptorCellReference, DescriptorTerm>;
use krs_syntax::ProvenanceRole;
use serde_json::Value;

use super::catalog::ProductionSignature;
use super::error::DescriptorLoweringError;
use super::origin::{key_range, role_key};
use super::references::{declared_multiplicity, require_cell_field};

/// What `KRS_READABLE_SHADOW` asks of every readable rule: `1` lowers it both ways and compares
/// the two meanings; `2` also compares where each node is located.
///
/// Scaffolding for S6-2a: S6-2b lowers readable rules through [`elaborate`] and removes the
/// switch with the readable lowering, so it has no documentation page.
#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum Shadow {
    Meaning,
    Located,
}

pub(super) fn shadow() -> Option<Shadow> {
    static SHADOW: OnceLock<Option<Shadow>> = OnceLock::new();
    *SHADOW.get_or_init(|| match std::env::var("KRS_READABLE_SHADOW").as_deref() {
        Ok("1") => Some(Shadow::Meaning),
        Ok("2") => Some(Shadow::Located),
        _ => None,
    })
}

/// A readable form [`elaborate`] has no `cells!` rule for yet.
#[derive(Debug)]
pub(super) struct Unelaborated(&'static str);

/// The `cells!` rule `rule` means, its binders at the sorts `readable` (its readable lowering)
/// inferred: the rule `krs expand` prints for it (`reference.rs` `render_rule`), taken in the
/// long form of its record updates.
pub(super) fn elaborate(
    descriptor: &Descriptor,
    rule: &DescriptorHeadRule,
    readable: &SemanticRule,
    declarations: &DescriptorIndex<'_>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<Result<DescriptorConfigurationRule, Unelaborated>, DescriptorLoweringError> {
    let rule =
        super::record_updates::head_rule_long_form_in(descriptor, rule, catalog, declarations)?;
    let sorts = readable
        .variables()
        .iter()
        .map(|variable| (variable.id().as_str().to_owned(), variable.sort().clone()))
        .collect::<BTreeMap<_, _>>();
    Ok(Elaborator {
        rule: &rule,
        declarations,
        sorts: &sorts,
    }
    .rule())
}

struct Elaborator<'a> {
    rule: &'a DescriptorHeadRule,
    declarations: &'a DescriptorIndex<'a>,
    sorts: &'a BTreeMap<String, SemanticSortRef>,
}

type Elaborated<T> = Result<T, Unelaborated>;

impl Elaborator<'_> {
    #[expect(
        clippy::too_many_lines,
        reason = "Each field of the `cells!` rule is set once, in the rule's order."
    )]
    fn rule(&self) -> Elaborated<DescriptorConfigurationRule> {
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
            let sort = self.sorts.get(&binding.name).ok_or(Unelaborated(
                "a binding the readable lowering declared no variable for",
            ))?;
            // A `where` sort is the binder's declaration; an inferred one is declared where the
            // rule's subject is written, the nearest node holding its first occurrence.
            let key = binding.refinement.as_ref().map_or_else(
                || rule.pattern_key.clone(),
                |refinement| refinement.key.clone(),
            );
            let sort = DescriptorSortReference {
                key,
                sort: descriptor_sort(sort),
            };
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
        let reserved = rule
            .bindings
            .iter()
            .map(|binding| binding.name.as_str())
            .chain(
                rule.existentials
                    .iter()
                    .chain(&rule.fresh)
                    .map(|binder| binder.name.as_str()),
            )
            .collect::<BTreeSet<_>>();
        let state = (0..=reserved.len())
            .map(|n| {
                if n == 0 {
                    "state".to_owned()
                } else {
                    format!("state{n}")
                }
            })
            .find(|name| !reserved.contains(name.as_str()))
            .expect("one of more names than the reserved ones is free");
        bindings.push(ProtocolRuleBinding {
            name: state.clone(),
            kind: ProtocolRuleBindingKind::ConfigurationFrame,
        });
        let (subject, result) = self.cells()?;
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
    fn cells(&self) -> Elaborated<(Vec<DescriptorRuleCell>, Vec<DescriptorRuleCell>)> {
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
                |payload_key: ProvenanceKey, items: Vec<&DescriptorTerm>| DescriptorRuleCell {
                    field: field.clone(),
                    wrapper_key: Some(key.clone()),
                    wrapper: Some(CellWrapper::KCell),
                    value: ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
                        tail: tail(&payload_key),
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
            // The readable lowering locates the computation's subject at the pattern and its
            // result at the result expression.
            subject.push(sequence(
                rule.pattern_key.clone(),
                head.items.iter().collect(),
            ));
            if let Some(after) = &head.result {
                let items = match after {
                    ProtocolHeadRuleResult::Replace(term) => vec![term],
                    ProtocolHeadRuleResult::Splice(splice) => splice.terms().collect(),
                    ProtocolHeadRuleResult::Erase => Vec::new(),
                };
                result.push(sequence(rule.result_key.clone(), items));
            }
        }
        for extra in &rule.extras {
            let (before, after) = self.extra(extra)?;
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
    ) -> Elaborated<(DescriptorRuleCell, Option<DescriptorRuleCell>)> {
        let cell = |field: &krs_ir::DescriptorCellReference, value| -> Elaborated<_> {
            let declared = require_cell_field(&field.cell, self.declarations)
                .map_err(|_| Unelaborated("a cell the declarations lack"))?;
            let group = matches!(declared.content, ProtocolCellContent::Nested { .. });
            Ok(DescriptorRuleCell {
                field: field.clone(),
                wrapper_key: (!group).then(|| field.key.clone()),
                wrapper: (!group).then_some(CellWrapper::Cell),
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
                        value: DescriptorTerm::Variable {
                            key: entry.value_key.clone(),
                            path_key: entry.value_key.clone(),
                            name: entry.value_binding.clone(),
                        },
                    })
                    .collect();
                // A read leaves the other entries as they are.
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
                    ProtocolRuleStateTerm::Term(DescriptorTerm::Variable {
                        key: field.key.clone(),
                        path_key: field.key.clone(),
                        name: base_binding.clone(),
                    }),
                )?,
                Some(cell(field, ProtocolRuleStateTerm::Term(update.clone()))?),
            )),
            ProtocolHeadRuleExtra::RewriteState {
                cell: field,
                before,
                after,
                ..
            } => {
                let state = |state: &ProtocolRuleStateTerm<DescriptorTerm>| match state {
                    ProtocolRuleStateTerm::Absent => Ok(ProtocolRuleStateTerm::Absent),
                    ProtocolRuleStateTerm::Present { value } => match &**value {
                        ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
                            content(field, term)
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
            ProtocolHeadRuleExtra::RewriteList { .. } => Err(Unelaborated("list notation")),
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

/// Lowers `rule`'s elaboration through the `cells!` lowering and refuses the rule where it
/// differs from `readable`, the readable lowering of the same rule.
pub(super) fn shadow_check(
    shadow: Shadow,
    descriptor: &Descriptor,
    rule: &DescriptorHeadRule,
    readable: &SemanticRule,
    declarations: &DescriptorIndex<'_>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<(), DescriptorLoweringError> {
    let disagreement = |detail: String| DescriptorLoweringError::ParserReferenceDisagreement {
        id: Box::new(descriptor.id().clone()),
        detail: format!(
            "readable shadow: the rule at `{}#{}` {detail}",
            rule.pattern_key.role().as_str(),
            rule.pattern_key.ordinal()
        ),
        range: key_range(descriptor, &rule.pattern_key).map(Box::new),
    };
    let elaborated = match elaborate(descriptor, rule, readable, declarations, catalog)? {
        Ok(elaborated) => elaborated,
        Err(Unelaborated(form)) => return Err(disagreement(format!("has no elaboration: {form}"))),
    };
    let cells = super::configuration_rules::lower_configuration_rule_descriptor(
        descriptor,
        &elaborated,
        declarations,
        sort_parents,
        catalog,
    )
    .map_err(|error| {
        disagreement(format!(
            "is accepted by the readable lowering and refused by the `cells!` one: {error}"
        ))
    })?;
    let readable = normalized(readable, false, shadow);
    let cells = normalized(&cells, true, shadow);
    match first_difference(&readable, &cells, "rule") {
        None => Ok(()),
        Some((path, left, right)) => Err(disagreement(format!(
            "lowers differently at `{path}`: readable {left}, `cells!` {right}"
        ))),
    }
}

/// `rule` as data, with what carries no meaning made comparable:
/// - each origin: it says where a node was written, which no sentence's meaning reads. Under
///   [`Shadow::Located`] only its route label is cleared (the label of its semantic
///   transformation frame and the source-map key hashed from it, `origin.rs`
///   `semantic_origin_from_stack`), and the authored source each node is located at is compared;
/// - the order of the declared variables, a set of declarations by name: no term refers to a
///   variable by position;
/// - a `cells!` claim's universals, once each is checked to be a variable of the same sort: a
///   claim's variables are universally quantified whether or not it lists them, and the list
///   records only where each is declared.
fn normalized(rule: &SemanticRule, cells: bool, shadow: Shadow) -> Value {
    let mut value = json(rule);
    unlabelled(&mut value, shadow);
    if let Some(Value::Array(variables)) = value.get_mut("variables") {
        variables.sort_by_key(Value::to_string);
    }
    if cells
        && let Some(claim) = rule.claim()
        && !claim.universals().is_empty()
    {
        let declared = rule
            .variables()
            .iter()
            .map(|variable| (variable.id(), variable.sort()))
            .collect::<BTreeSet<_>>();
        if claim
            .universals()
            .iter()
            .all(|binder| declared.contains(&(binder.id(), binder.sort())))
            && let Some(Value::Array(universals)) = value
                .get_mut("claim")
                .and_then(|claim| claim.get_mut("universals"))
        {
            universals.clear();
        }
    }
    value
}

/// Clears every origin `value` holds, or under [`Shadow::Located`] its route label.
fn unlabelled(value: &mut Value, shadow: Shadow) {
    match value {
        Value::Array(items) => items.iter_mut().for_each(|item| unlabelled(item, shadow)),
        Value::Object(fields) => {
            if fields.len() == 2
                && matches!(fields.get("key"), Some(Value::String(_)))
                && let Some(Value::Array(frames)) = fields.get_mut("origin")
            {
                if shadow == Shadow::Located {
                    frames.iter_mut().for_each(clear_transformation_labels);
                } else {
                    frames.clear();
                }
                fields.insert("key".to_owned(), Value::Null);
                return;
            }
            fields
                .values_mut()
                .for_each(|field| unlabelled(field, shadow));
        }
        _ => {}
    }
}

fn clear_transformation_labels(frame: &mut Value) {
    if let Value::Object(fields) = frame {
        if fields.contains_key("kind") && fields.contains_key("label") {
            fields.insert("label".to_owned(), Value::Null);
        }
        fields.values_mut().for_each(clear_transformation_labels);
    }
}

fn json(value: &impl serde::Serialize) -> Value {
    serde_json::to_value(value).expect("semantic IR serializes")
}

/// The first path at which `left` and `right` differ, with each side's value there.
fn first_difference(left: &Value, right: &Value, path: &str) -> Option<(String, String, String)> {
    let shown = |value: Option<&Value>| {
        value.map_or_else(
            || "nothing".to_owned(),
            |value| {
                let text = value.to_string();
                if text.len() > 400 {
                    format!("{}..", &text[..400])
                } else {
                    text
                }
            },
        )
    };
    match (left, right) {
        (Value::Object(left), Value::Object(right)) => {
            let keys = left.keys().chain(right.keys()).collect::<BTreeSet<_>>();
            keys.into_iter()
                .find_map(|key| match (left.get(key), right.get(key)) {
                    (Some(l), Some(r)) => first_difference(l, r, &format!("{path}.{key}")),
                    (l, r) => Some((format!("{path}.{key}"), shown(l), shown(r))),
                })
        }
        (Value::Array(l), Value::Array(r)) if l.len() == r.len() => l
            .iter()
            .zip(r)
            .enumerate()
            .find_map(|(n, (l, r))| first_difference(l, r, &format!("{path}[{n}]"))),
        (l, r) if l == r => None,
        (l, r) => Some((path.to_owned(), shown(Some(l)), shown(Some(r)))),
    }
}

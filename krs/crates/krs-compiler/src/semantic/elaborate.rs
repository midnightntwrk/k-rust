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
    ProtocolHeadRuleResult, ProtocolInstanceRest, ProtocolRuleBinding, ProtocolRuleBindingKind,
    ProtocolRuleFrame, ProtocolRuleInstances, ProtocolRuleKSequence, ProtocolRuleKSequenceItem,
    ProtocolRuleMap, ProtocolRuleMapBody, ProtocolRuleMapItem, ProtocolRuleStateTerm,
    ProvenanceKey, SentenceKind, StableItemId,
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

/// The `cells!` rule `rule` means, its binders at the sorts `inferred` (inference's, before any
/// state is lowered): the rule `krs expand` prints for it (`reference.rs` `render_rule`), taken
/// in the long form of its record updates, whose hidden binders are declared at their fields'
/// declared sorts.
pub(super) fn elaborate(
    descriptor: &Descriptor,
    rule: &DescriptorHeadRule,
    inferred: &BTreeMap<String, SemanticSortRef>,
    declarations: &DescriptorIndex<'_>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<Result<DescriptorConfigurationRule, Unelaborated>, DescriptorLoweringError> {
    let (mut rule, hidden) =
        super::record_updates::head_rule_long_form_in(descriptor, rule, catalog, declarations)?;
    let closing = Closing {
        catalog,
        key: &rule.pattern_key.clone(),
    };
    closing.rule(&mut rule);
    let mut sorts = inferred.clone();
    for (id, sort) in hidden {
        // A parametric production's field has its instance's sort, which only the lowering of
        // the occurrence fixes.
        let Some(sort) = sort else {
            return Ok(Err(Unelaborated(
                "a hidden binder of a parametric production's field",
            )));
        };
        sorts.insert(id.as_str().to_owned(), sort);
    }
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

/// The names the elaborated rule introduces beside the readable binders: the remainders a
/// collection entry's `..` and an instance's `k` tail stand for, named as the print names them,
/// each fresh against every name taken before it.
struct Names {
    reserved: BTreeSet<String>,
    /// Instance `k` tails named so far (`tail0`, `tail1`, ..), across the rule's entries.
    tails: usize,
    /// The frames these names bind, in the order named.
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
}

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
            frames: Vec::new(),
        };
        let state = names.fresh("state");
        let (subject, result) = self.cells(&mut names)?;
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
        for (ordinal, extra) in rule.extras.iter().enumerate() {
            let (before, after) = self.extra(extra, ordinal, names)?;
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
            ProtocolHeadRuleExtra::RewriteList {
                cell: field,
                before,
                after,
                ..
            } => Ok((
                cell(field, content(field, &list_notation(field, before))?)?,
                after
                    .as_ref()
                    .map(|after| cell(field, content(field, &list_notation(field, after))?))
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
) -> DescriptorTerm {
    let level = |notation, arguments: Vec<DescriptorTerm>| DescriptorTerm::Application {
        head_class: krs_ir::DescriptorApplicationHeadClass::Applied,
        reference: krs_ir::DescriptorApplicationReference {
            key: field.key.clone(),
            application: krs_ir::DescriptorApplicationRef::ListNotation(notation),
        },
        path_key: field.key.clone(),
        arguments: krs_ir::Arguments::Positional(arguments.into_iter().map(Box::new).collect()),
        instance: Vec::new(),
        update: None,
        open: false,
    };
    let rest = match &list.rest {
        krs_ir::ProtocolHeadRuleListRest::Exact => level(krs_ir::ListNotation::Empty, Vec::new()),
        krs_ir::ProtocolHeadRuleListRest::Shared(key) => DescriptorTerm::KeptRest {
            key: key.clone().unwrap_or_else(|| field.key.clone()),
        },
        krs_ir::ProtocolHeadRuleListRest::Term(rest) => rest.clone(),
    };
    let back = list.back.iter().fold(rest, |list, item| {
        level(krs_ir::ListNotation::Snoc, vec![list, item.clone()])
    });
    list.items.iter().rev().fold(back, |list, item| {
        level(krs_ir::ListNotation::Cons, vec![item.clone(), list])
    })
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
        let close = |term: &mut DescriptorTerm, pattern: bool| {
            let open = std::mem::replace(
                term,
                DescriptorTerm::Wildcard {
                    key: self.key.clone(),
                },
            );
            *term = self.term(open, pattern);
        };
        if let Some(head) = &mut rule.head {
            for item in &mut head.items {
                close(item, true);
            }
            match &mut head.result {
                Some(ProtocolHeadRuleResult::Replace(term)) => close(term, false),
                Some(ProtocolHeadRuleResult::Splice(splice)) => {
                    for term in splice.terms_mut() {
                        close(term, false);
                    }
                }
                Some(ProtocolHeadRuleResult::Erase) | None => {}
            }
        }
        let state = |state: &mut ProtocolRuleStateTerm<DescriptorTerm>, pattern: bool| {
            Self::state(state, &mut |term| close(term, pattern));
        };
        for extra in &mut rule.extras {
            match extra {
                ProtocolHeadRuleExtra::HaveMap { entries, .. } => {
                    for entry in entries {
                        close(&mut entry.key, true);
                    }
                }
                ProtocolHeadRuleExtra::UpdateMap { update, .. } => close(update, false),
                ProtocolHeadRuleExtra::RewriteCell { before, after, .. } => {
                    close(before, true);
                    if let Some(after) = after {
                        close(after, false);
                    }
                }
                ProtocolHeadRuleExtra::RewriteState { before, after, .. } => {
                    state(before, true);
                    if let Some(after) = after {
                        state(after, false);
                    }
                }
                ProtocolHeadRuleExtra::RewriteList { before, after, .. } => {
                    for term in before.terms_mut() {
                        close(term, true);
                    }
                    for term in after
                        .iter_mut()
                        .flat_map(krs_ir::ProtocolHeadRuleList::terms_mut)
                    {
                        close(term, false);
                    }
                }
            }
        }
        for condition in rule.requires.iter_mut().chain(&mut rule.ensures) {
            close(&mut condition.term, false);
        }
    }

    fn state(
        state: &mut ProtocolRuleStateTerm<DescriptorTerm>,
        close: &mut impl FnMut(&mut DescriptorTerm),
    ) {
        match state {
            ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => close(term),
            ProtocolRuleStateTerm::Present { value } => Self::state(value, close),
            ProtocolRuleStateTerm::KSequence(sequence) => {
                for item in &mut sequence.items {
                    close(&mut item.value);
                }
            }
            ProtocolRuleStateTerm::Instances(instances) => {
                for instance in instances.front.iter_mut().chain(&mut instances.back) {
                    for field in &mut instance.fields {
                        Self::state(&mut field.value, close);
                    }
                }
            }
            ProtocolRuleStateTerm::Map(_) | ProtocolRuleStateTerm::Absent => {}
        }
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
#[expect(
    clippy::too_many_arguments,
    reason = "Scaffolding: the readable lowering's inputs and both of its outputs."
)]
pub(super) fn shadow_check(
    shadow: Shadow,
    descriptor: &Descriptor,
    rule: &DescriptorHeadRule,
    readable: &SemanticRule,
    inferred: &BTreeMap<String, SemanticSortRef>,
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
    let elaborated = match elaborate(descriptor, rule, inferred, declarations, catalog)? {
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
        dump(
            descriptor,
            rule,
            &elaborated,
            &normalized(readable, false, shadow),
            &Value::String(error.to_string()),
        );
        disagreement(format!(
            "is accepted by the readable lowering and refused by the `cells!` one: {error}"
        ))
    })?;
    let mut readable = normalized(readable, false, shadow);
    let mut cells = normalized(&cells, true, shadow);
    for (route, value) in [("readable", &mut readable), ("`cells!`", &mut cells)] {
        canonical_wildcards(value).map_err(|wildcard| {
            disagreement(format!(
                "lowers with the wildcard `{wildcard}` occurring other than once on the {route} route"
            ))
        })?;
        if let Some(Value::Array(variables)) = value.get_mut("variables") {
            variables.sort_by_key(Value::to_string);
        }
    }
    let difference = first_difference(&readable, &cells, "rule");
    if difference.is_some() {
        dump(descriptor, rule, &elaborated, &readable, &cells);
    }
    match difference {
        None => Ok(()),
        Some((path, left, right)) => Err(disagreement(format!(
            "lowers differently at `{path}`: readable {left}, `cells!` {right}"
        ))),
    }
}

/// Under `KRS_READABLE_SHADOW_DUMP=<directory>`, writes a disagreeing rule's elaboration and both
/// compared lowerings there, one file each, named by the item and the rule's pattern key.
fn dump(
    descriptor: &Descriptor,
    rule: &DescriptorHeadRule,
    elaborated: &DescriptorConfigurationRule,
    readable: &Value,
    cells: &Value,
) {
    let Some(directory) = std::env::var_os("KRS_READABLE_SHADOW_DUMP") else {
        return;
    };
    let stem = format!(
        "{}-{}{}",
        descriptor.id(),
        rule.pattern_key.role().as_str(),
        rule.pattern_key.ordinal()
    )
    .replace(|c: char| !c.is_ascii_alphanumeric() && c != '-', "_");
    let directory = std::path::Path::new(&directory);
    let pretty = |value: &Value| serde_json::to_string_pretty(value).unwrap_or_default();
    // Best effort: a dump that cannot be written leaves the disagreement itself reported.
    let _ = std::fs::create_dir_all(directory);
    let _ = std::fs::write(
        directory.join(format!("{stem}.elaborated.txt")),
        format!("{elaborated:#?}"),
    );
    let _ = std::fs::write(
        directory.join(format!("{stem}.readable.json")),
        pretty(readable),
    );
    let _ = std::fs::write(directory.join(format!("{stem}.cells.json")), pretty(cells));
}

/// `rule` as data, with what carries no meaning made comparable:
/// - each origin: it says where a node was written, which no sentence's meaning reads. Under
///   [`Shadow::Located`] only its route label is cleared (the label of its semantic
///   transformation frame and the source-map key hashed from it, `origin.rs`
///   `semantic_origin_from_stack`), and the authored source each node is located at is compared;
/// - the order of the declared variables, a set of declarations by name: no term refers to a
///   variable by position (sorted by [`shadow_check`], after [`canonical_wildcards`]);
/// - a `cells!` claim's universals, once each is checked to be a variable of the same sort: a
///   claim's variables are universally quantified whether or not it lists them, and the list
///   records only where each is declared.
fn normalized(rule: &SemanticRule, cells: bool, shadow: Shadow) -> Value {
    let mut value = json(rule);
    unlabelled(&mut value, shadow);
    unread_frames(&mut value);
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

/// Drops the name of each K-sequence tail or map remainder frame of `rule` (its JSON) that no other
/// node reads, and its declaration. A clause's frame is one node standing for the content its
/// pattern leaves out and its result keeps; a name only that frame bears binds nothing a term or
/// a condition refers to, so the frame matches and keeps the same content named or not (K's
/// `<k> A => B ... </k>` and `<k> A ~> T => B ~> T </k>`). The routes differ there: the print
/// names an instance's open `k` (`tail0 @ ..`, `..tail0`), the readable entry leaves it unnamed.
fn unread_frames(rule: &mut Value) {
    fn frames(value: &Value, found: &mut Vec<String>) {
        match value {
            Value::Array(items) => items.iter().for_each(|item| frames(item, found)),
            Value::Object(fields) => {
                if let (Some(Value::String(kind)), Some(Value::String(binding))) =
                    (fields.get("frame_kind"), fields.get("binding"))
                    && matches!(kind.as_str(), "k_sequence_tail" | "map_remainder")
                {
                    found.push(binding.clone());
                }
                fields.values().for_each(|field| frames(field, found));
            }
            _ => {}
        }
    }
    fn count(value: &Value, name: &str) -> usize {
        match value {
            Value::String(text) => usize::from(text == name),
            Value::Array(items) => items.iter().map(|item| count(item, name)).sum(),
            Value::Object(fields) => fields.values().map(|field| count(field, name)).sum(),
            _ => 0,
        }
    }
    fn unname(value: &mut Value, name: &str) {
        match value {
            Value::Array(items) => items.iter_mut().for_each(|item| unname(item, name)),
            Value::Object(fields) => {
                if fields.get("frame_kind").is_some()
                    && fields.get("binding").and_then(Value::as_str) == Some(name)
                {
                    fields.remove("binding");
                }
                fields.values_mut().for_each(|field| unname(field, name));
            }
            _ => {}
        }
    }
    let Value::Object(fields) = rule else {
        return;
    };
    let mut found = Vec::new();
    frames(&Value::Object(fields.clone()), &mut found);
    for name in found {
        let reads = fields
            .iter()
            .filter(|(field, _)| *field != "variables")
            .map(|(_, value)| count(value, &name))
            .sum::<usize>();
        if reads != 1 {
            continue;
        }
        for (field, value) in fields.iter_mut() {
            if field != "variables" {
                unname(value, &name);
            }
        }
        if let Some(Value::Array(variables)) = fields.get_mut("variables") {
            variables.retain(|variable| variable.get("id").and_then(Value::as_str) != Some(&name));
        }
    }
}

/// Renames the wildcards of `rule` (its JSON) `__krs_wildcard_0`, `_1`, .. in the order they
/// first occur, outside the declared variables. A wildcard is a variable that occurs exactly
/// once: it binds nothing any other node refers to, so which ordinal it bears says nothing, and
/// the routes number them in the order each lowers its terms. Renaming them in a fixed order is
/// an alpha-renaming that makes the two comparable. A wildcard that occurs other than once binds
/// something; it is returned, and the rule is not renamed.
fn canonical_wildcards(rule: &mut Value) -> Result<(), String> {
    fn wildcard(text: &str) -> bool {
        text.strip_prefix("__krs_wildcard_").is_some_and(|ordinal| {
            !ordinal.is_empty() && ordinal.bytes().all(|b| b.is_ascii_digit())
        })
    }
    fn occurrences<'a>(value: &'a Value, found: &mut Vec<&'a str>) {
        match value {
            Value::String(text) if wildcard(text) => found.push(text),
            Value::Array(items) => items.iter().for_each(|item| occurrences(item, found)),
            Value::Object(fields) => fields.values().for_each(|field| occurrences(field, found)),
            _ => {}
        }
    }
    fn rename(value: &mut Value, names: &BTreeMap<String, String>) {
        match value {
            Value::String(text) => {
                if let Some(name) = names.get(text.as_str()) {
                    text.clone_from(name);
                }
            }
            Value::Array(items) => items.iter_mut().for_each(|item| rename(item, names)),
            Value::Object(fields) => fields.values_mut().for_each(|field| rename(field, names)),
            _ => {}
        }
    }
    let Value::Object(fields) = &*rule else {
        return Ok(());
    };
    let mut found = Vec::new();
    for (name, field) in fields {
        if name != "variables" {
            occurrences(field, &mut found);
        }
    }
    let mut declared = Vec::new();
    if let Some(variables) = fields.get("variables") {
        occurrences(variables, &mut declared);
    }
    let mut counts = BTreeMap::<&str, usize>::new();
    for name in found.iter().chain(&declared) {
        counts.entry(name).or_default();
    }
    for name in &found {
        *counts.entry(name).or_default() += 1;
    }
    if let Some((name, _)) = counts.iter().find(|(_, count)| **count != 1) {
        return Err((*name).to_owned());
    }
    let mut names = BTreeMap::new();
    for name in found {
        let next = format!("__krs_wildcard_{}", names.len());
        names.entry(name.to_owned()).or_insert(next);
    }
    rename(rule, &names);
    Ok(())
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

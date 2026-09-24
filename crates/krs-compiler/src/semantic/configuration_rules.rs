use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    BuiltinSort, CellContentFrame, CellPost, Descriptor, DescriptorPayload, DescriptorTerm,
    FixedCellClause, FixedCellPattern, FixedConfigurationPattern, FixedConfigurationRewrite,
    ItemKind, MapOperation, ProtocolCellContent, ProtocolContextAliasBindingKind,
    ProtocolRuleBindingKind, ProtocolRuleFrame, ProtocolRuleMapBody, ProtocolRuleStateTerm,
    ProvenanceKey, SemanticContextAlias, SemanticId, SemanticRule, SemanticRuleCondition,
    SemanticRulePriority, SemanticSortRef, SemanticTerm, SemanticVariable, StableItemId,
};
use krs_syntax::ProvenanceRole;

use super::catalog::{ProductionSignature, common_sequence_item_sort, semantic_sort_ref};
use super::error::DescriptorLoweringError;
use super::infer::{StructuredTermBuilder, initial_binding_constraints};
use super::origin::{generated_semantic_id, role_key, semantic_cell_id, semantic_origin};
use super::references::{require_cell_field, require_descriptor};
use super::rules::{collect_declared_leaf_identities, framework_k_item_sort, lower_rule_label};

#[allow(clippy::too_many_arguments)]
fn lower_rule_descriptor_term(
    descriptor: &Descriptor,
    term: &DescriptorTerm,
    expected_sort: Option<&SemanticSortRef>,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
    subject: bool,
    wildcard_ordinal: &mut usize,
    variables: &mut Vec<SemanticVariable>,
) -> Result<SemanticTerm, DescriptorLoweringError> {
    let binding_names = binding_sorts.keys().cloned().collect::<BTreeSet<_>>();
    let mut builder = StructuredTermBuilder {
        descriptor,
        catalog,
        declarations: Some(declarations),
        k_item_sort: Some(framework_k_item_sort(declarations)?),
        sort_parents,
        binding_names: &binding_names,
        pattern_key: None,
        binding_sorts: BTreeMap::new(),
        binding_constraints: initial_binding_constraints(binding_sorts),
        wildcard_offset: *wildcard_ordinal,
        wildcards: Vec::new(),
    };
    builder.infer(term, expected_sort, subject)?;
    builder.resolve_binding_sorts()?;
    let lowered = builder.lower(term, expected_sort, subject)?;
    *wildcard_ordinal += builder.wildcards.len();
    variables.append(&mut builder.wildcards);
    Ok(lowered)
}

#[allow(clippy::too_many_lines)]
pub(super) fn lower_configuration_rule_descriptor(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorConfigurationRule,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticRule, DescriptorLoweringError> {
    let configuration_descriptor = require_descriptor(
        &rule.subject_configuration.configuration,
        ItemKind::Configuration,
        declarations,
    )?;
    let DescriptorPayload::FixedConfiguration(configuration) = &configuration_descriptor.payload
    else {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "configuration rule",
            detail: "configuration rules require a fixed configuration".into(),
        });
    };

    let mut binding_sorts = BTreeMap::new();
    let mut variables = Vec::new();
    for binding in &rule.bindings {
        let sort = match &binding.kind {
            ProtocolRuleBindingKind::Term { sort } => semantic_sort_ref(&sort.sort),
            ProtocolRuleBindingKind::KSequenceFrame => SemanticSortRef::k_sequence(),
            ProtocolRuleBindingKind::MapFrame => SemanticSortRef::map(),
            ProtocolRuleBindingKind::ConfigurationFrame => continue,
        };
        if matches!(binding.kind, ProtocolRuleBindingKind::Term { .. }) {
            binding_sorts.insert(binding.name.clone(), sort.clone());
        }
        variables.push(SemanticVariable::new(
            SemanticId::new(binding.name.clone())?,
            sort,
        ));
    }
    let mut result_binding_sorts = binding_sorts.clone();
    if let Some(claim) = &rule.claim {
        for binder in &claim.existentials {
            let sort = semantic_sort_ref(&binder.sort.sort);
            result_binding_sorts.insert(binder.name.clone(), sort.clone());
            variables.push(SemanticVariable::new(
                SemanticId::new(binder.name.clone())?,
                sort,
            ));
        }
    }

    let subject_cells = rule
        .subject
        .cells
        .iter()
        .map(|cell| (&cell.field.cell, cell))
        .collect::<BTreeMap<_, _>>();
    let result_cells = rule
        .result
        .cells
        .iter()
        .map(|cell| (&cell.field.cell, cell))
        .collect::<BTreeMap<_, _>>();
    if result_cells
        .keys()
        .any(|identity| !subject_cells.contains_key(identity))
    {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "configuration rule",
            detail: "the result selects a fixed cell absent from the subject".into(),
        });
    }
    validate_frame_pair(
        descriptor,
        &rule.subject.remainder,
        &rule.result.remainder,
        "configuration remainder",
    )?;

    let mut clauses = Vec::with_capacity(rule.subject.cells.len());
    let mut wildcard_ordinal = 0;
    for subject in &rule.subject.cells {
        let declared = require_cell_field(&subject.field.cell, declarations)?;
        let ProtocolCellContent::Leaf { wrapper, sort, .. } = &declared.content else {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "configuration rule cell",
                detail: "rules over nominal parent cells are not represented by fixed-cell clauses"
                    .into(),
            });
        };
        let result = result_cells.get(&subject.field.cell).copied();
        if subject.wrapper != *wrapper || result.is_some_and(|result| result.wrapper != *wrapper) {
            return Err(DescriptorLoweringError::ParserReferenceDisagreement {
                id: Box::new(subject.field.cell.owner.clone()),
                detail: format!(
                    "rule wrapper disagrees with declared cell {:?}",
                    subject.field.cell.field
                ),
            });
        }
        let declared_sort = semantic_sort_ref(&sort.sort);
        let before = lower_rule_state_term(
            descriptor,
            &subject.value,
            &declared_sort,
            &subject.field.key,
            declarations,
            sort_parents,
            catalog,
            &binding_sorts,
            true,
            &mut wildcard_ordinal,
            &mut variables,
        )?;
        let subject_frame = rule_state_frame(&subject.value);
        let frame = lower_subject_cell_frame(descriptor, &subject.value)?;
        let post = if let Some(result) = result {
            let after = lower_rule_state_term(
                descriptor,
                &result.value,
                &declared_sort,
                &result.field.key,
                declarations,
                sort_parents,
                catalog,
                &result_binding_sorts,
                false,
                &mut wildcard_ordinal,
                &mut variables,
            )?;
            let result_frame = rule_state_frame(&result.value);
            validate_state_frame_pair(
                descriptor,
                subject_frame,
                result_frame,
                "cell content frame",
            )?;
            if semantic_terms_equivalent(&before, &after) {
                CellPost::Preserve
            } else {
                CellPost::Replace { term: after }
            }
        } else {
            CellPost::Preserve
        };
        clauses.push(FixedCellClause::new(
            semantic_origin(descriptor, subject.field.key.clone(), "rule-cell-clause")?,
            semantic_cell_id(&subject.field.cell)?,
            before,
            post,
            frame,
        ));
    }

    let selected = subject_cells
        .keys()
        .copied()
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut all_leaves = Vec::new();
    collect_declared_leaf_identities(
        &configuration.declaration,
        declarations,
        &mut BTreeSet::new(),
        &mut all_leaves,
    )?;
    let omitted_siblings = all_leaves
        .into_iter()
        .filter(|identity| !selected.contains(identity))
        .map(|identity| semantic_cell_id(&identity))
        .collect::<Result<Vec<_>, _>>()?;
    if matches!(rule.subject.remainder, ProtocolRuleFrame::Exact) && !omitted_siblings.is_empty() {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "configuration rule remainder",
            detail: "an exact subject must select every fixed leaf cell".into(),
        });
    }

    let body = FixedConfigurationRewrite::new(
        semantic_origin(
            descriptor,
            rule.pattern_key.clone(),
            "configuration-rewrite",
        )?,
        generated_semantic_id(
            "configuration",
            &rule.subject_configuration.configuration,
            None,
        )?,
        clauses,
        omitted_siblings,
    )?;
    let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
    let requires = rule
        .requires
        .as_ref()
        .map(|condition| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRuleCondition::new(
                semantic_origin(descriptor, condition.key.clone(), "rule-requires")?,
                lower_rule_descriptor_term(
                    descriptor,
                    &condition.term,
                    Some(&bool_sort),
                    declarations,
                    sort_parents,
                    catalog,
                    &binding_sorts,
                    false,
                    &mut wildcard_ordinal,
                    &mut variables,
                )?,
            ))
        })
        .transpose()?;
    let priority = rule
        .priority
        .as_ref()
        .map(|priority| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRulePriority::new(
                semantic_origin(descriptor, priority.key.clone(), "rule-owise")?,
                priority.value,
            ))
        })
        .transpose()?;
    let claim = rule
        .claim
        .as_ref()
        .map(|claim| -> Result<_, DescriptorLoweringError> {
            let universals = claim
                .universals
                .iter()
                .map(|binder| {
                    Ok(krs_ir::SemanticClaimBinder::new(
                        semantic_origin(
                            descriptor,
                            binder.declaration_key.clone(),
                            "claim-universal-binder",
                        )?,
                        semantic_origin(descriptor, binder.name_key.clone(), "claim-binder-name")?,
                        SemanticId::new(binder.name.clone())?,
                        semantic_origin(descriptor, binder.sort.key.clone(), "claim-binder-sort")?,
                        semantic_sort_ref(&binder.sort.sort),
                    ))
                })
                .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
            let existentials = claim
                .existentials
                .iter()
                .map(|binder| {
                    Ok(krs_ir::SemanticClaimBinder::new(
                        semantic_origin(
                            descriptor,
                            binder.declaration_key.clone(),
                            "claim-existential-binder",
                        )?,
                        semantic_origin(descriptor, binder.name_key.clone(), "claim-binder-name")?,
                        SemanticId::new(binder.name.clone())?,
                        semantic_origin(descriptor, binder.sort.key.clone(), "claim-binder-sort")?,
                        semantic_sort_ref(&binder.sort.sort),
                    ))
                })
                .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
            let ensures = claim
                .ensures
                .as_ref()
                .map(|condition| -> Result<_, DescriptorLoweringError> {
                    Ok(SemanticRuleCondition::new(
                        semantic_origin(descriptor, condition.key.clone(), "claim-ensures")?,
                        lower_rule_descriptor_term(
                            descriptor,
                            &condition.term,
                            Some(&bool_sort),
                            declarations,
                            sort_parents,
                            catalog,
                            &result_binding_sorts,
                            false,
                            &mut wildcard_ordinal,
                            &mut variables,
                        )?,
                    ))
                })
                .transpose()?;
            Ok(krs_ir::SemanticClaim::new(
                semantic_origin(descriptor, claim.modality_key.clone(), "claim-modality")?,
                claim.modality,
                claim
                    .circularity_key
                    .as_ref()
                    .map(|key| semantic_origin(descriptor, key.clone(), "claim-circularity"))
                    .transpose()?,
                universals,
                existentials,
                ensures,
            ))
        })
        .transpose()?;
    Ok(SemanticRule::new_configuration(
        semantic_origin(
            descriptor,
            role_key(
                if rule.sentence_kind == krs_ir::SentenceKind::Claim {
                    ProvenanceRole::ClaimDeclaration
                } else {
                    ProvenanceRole::RuleDeclaration
                },
                0,
            )?,
            "configuration-rule",
        )?,
        descriptor.id.clone(),
        rule.sentence_kind,
        variables,
        body,
    )?
    .with_label(lower_rule_label(descriptor, rule.label.as_ref())?)
    .with_priority(priority)?
    .with_requires(requires)?
    .with_claim(claim))
}

#[allow(clippy::too_many_lines)]
pub(super) fn lower_context_alias_descriptor(
    descriptor: &Descriptor,
    alias: &krs_ir::DescriptorContextAlias,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticContextAlias, DescriptorLoweringError> {
    let configuration_descriptor = require_descriptor(
        &alias.configuration.configuration,
        ItemKind::Configuration,
        declarations,
    )?;
    let DescriptorPayload::FixedConfiguration(configuration) = &configuration_descriptor.payload
    else {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "context alias",
            detail: "context aliases require a fixed configuration".into(),
        });
    };
    let k_items = declarations
        .keys()
        .filter(|id| id.item_kind() == ItemKind::Sort && id.item_name() == "KItem")
        .collect::<Vec<_>>();
    let [k_item] = k_items.as_slice() else {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "context alias",
            detail: "context aliases require exactly one declared KItem sort".into(),
        });
    };
    let mut binding_sorts = BTreeMap::new();
    let mut variables = Vec::new();
    for binding in &alias.bindings {
        let sort = match &binding.kind {
            ProtocolContextAliasBindingKind::Here => SemanticSortRef::Declared((**k_item).clone()),
            ProtocolContextAliasBindingKind::Term { sort } => semantic_sort_ref(&sort.sort),
            ProtocolContextAliasBindingKind::KSequenceFrame => SemanticSortRef::k_sequence(),
            ProtocolContextAliasBindingKind::MapFrame => SemanticSortRef::map(),
            ProtocolContextAliasBindingKind::ConfigurationFrame => continue,
        };
        if matches!(
            binding.kind,
            ProtocolContextAliasBindingKind::Here | ProtocolContextAliasBindingKind::Term { .. }
        ) {
            binding_sorts.insert(binding.name.clone(), sort.clone());
        }
        variables.push(SemanticVariable::new(
            SemanticId::new(binding.name.clone())?,
            sort,
        ));
    }
    let mut cells = Vec::with_capacity(alias.pattern.cells.len());
    let mut wildcard_ordinal = 0;
    for pattern in &alias.pattern.cells {
        let declared = require_cell_field(&pattern.field.cell, declarations)?;
        let ProtocolCellContent::Leaf { wrapper, sort, .. } = &declared.content else {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "context alias cell",
                detail: "context aliases select leaf cells only".into(),
            });
        };
        if pattern.wrapper != *wrapper {
            return Err(DescriptorLoweringError::ParserReferenceDisagreement {
                id: Box::new(pattern.field.cell.owner.clone()),
                detail: "context-alias wrapper disagrees with its cell declaration".into(),
            });
        }
        let term = lower_rule_state_term(
            descriptor,
            &pattern.value,
            &semantic_sort_ref(&sort.sort),
            &pattern.field.key,
            declarations,
            sort_parents,
            catalog,
            &binding_sorts,
            true,
            &mut wildcard_ordinal,
            &mut variables,
        )?;
        cells.push(FixedCellPattern::new(
            semantic_origin(descriptor, pattern.field.key.clone(), "context-alias-cell")?,
            semantic_cell_id(&pattern.field.cell)?,
            term,
            lower_subject_cell_frame(descriptor, &pattern.value)?,
        ));
    }
    let selected = alias
        .pattern
        .cells
        .iter()
        .map(|cell| cell.field.cell.clone())
        .collect::<BTreeSet<_>>();
    let mut all_leaves = Vec::new();
    collect_declared_leaf_identities(
        &configuration.declaration,
        declarations,
        &mut BTreeSet::new(),
        &mut all_leaves,
    )?;
    let omitted_siblings = all_leaves
        .into_iter()
        .filter(|identity| !selected.contains(identity))
        .map(|identity| semantic_cell_id(&identity))
        .collect::<Result<Vec<_>, _>>()?;
    if matches!(alias.pattern.remainder, ProtocolRuleFrame::Exact) && !omitted_siblings.is_empty() {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "context alias remainder",
            detail: "an exact pattern must select every fixed leaf cell".into(),
        });
    }
    let body = FixedConfigurationPattern::new(
        semantic_origin(
            descriptor,
            alias.pattern_key.clone(),
            "context-alias-pattern",
        )?,
        generated_semantic_id("configuration", &alias.configuration.configuration, None)?,
        cells,
        omitted_siblings,
    )?;
    Ok(SemanticContextAlias::new(
        semantic_origin(descriptor, alias.declaration_key.clone(), "context-alias")?,
        descriptor.id.clone(),
        semantic_origin(descriptor, alias.name_key.clone(), "context-alias-name")?,
        alias.name.clone(),
        semantic_origin(descriptor, alias.here_key.clone(), "context-alias-here")?,
        SemanticId::new(alias.here.clone())?,
        variables,
        body,
    ))
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::too_many_lines)]
fn lower_rule_state_term(
    descriptor: &Descriptor,
    state: &ProtocolRuleStateTerm<DescriptorTerm>,
    declared_sort: &SemanticSortRef,
    fallback_key: &ProvenanceKey,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
    subject: bool,
    wildcard_ordinal: &mut usize,
    variables: &mut Vec<SemanticVariable>,
) -> Result<SemanticTerm, DescriptorLoweringError> {
    match state {
        ProtocolRuleStateTerm::Term(term) => lower_rule_descriptor_term(
            descriptor,
            term,
            Some(declared_sort),
            declarations,
            sort_parents,
            catalog,
            binding_sorts,
            subject,
            wildcard_ordinal,
            variables,
        ),
        ProtocolRuleStateTerm::KSequence(sequence) => {
            if *declared_sort != SemanticSortRef::k_sequence() {
                return Err(DescriptorLoweringError::InvalidTerm {
                    id: Box::new(descriptor.id.clone()),
                    detail: "K sequence occurs in a non-KSequence rule cell".into(),
                });
            }
            let items = sequence
                .items
                .iter()
                .map(|item| {
                    lower_rule_descriptor_term(
                        descriptor,
                        &item.value,
                        None,
                        declarations,
                        sort_parents,
                        catalog,
                        binding_sorts,
                        subject,
                        wildcard_ordinal,
                        variables,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let item_sort = common_sequence_item_sort(descriptor, &items, sort_parents)?;
            let key = sequence
                .payload_key
                .as_ref()
                .or(sequence.dot_k_key.as_ref())
                .unwrap_or(fallback_key);
            Ok(SemanticTerm::k_sequence(
                semantic_origin(descriptor, key.clone(), "rule-k-sequence")?,
                item_sort,
                items,
            ))
        }
        ProtocolRuleStateTerm::Map(map) => {
            if *declared_sort != SemanticSortRef::map() {
                return Err(DescriptorLoweringError::InvalidTerm {
                    id: Box::new(descriptor.id.clone()),
                    detail: "map occurs in a non-Map rule cell".into(),
                });
            }
            let key = map.payload_key.as_ref().unwrap_or(fallback_key);
            let (operation, arguments) = match &map.body {
                ProtocolRuleMapBody::Empty { .. } => (MapOperation::Empty, Vec::new()),
                ProtocolRuleMapBody::Items { items, .. } => {
                    let mut arguments = Vec::with_capacity(items.len() * 2);
                    for item in items {
                        arguments.push(lower_rule_descriptor_term(
                            descriptor,
                            &item.key,
                            None,
                            declarations,
                            sort_parents,
                            catalog,
                            binding_sorts,
                            subject,
                            wildcard_ordinal,
                            variables,
                        )?);
                        arguments.push(lower_rule_descriptor_term(
                            descriptor,
                            &item.value,
                            None,
                            declarations,
                            sort_parents,
                            catalog,
                            binding_sorts,
                            subject,
                            wildcard_ordinal,
                            variables,
                        )?);
                    }
                    (MapOperation::Item, arguments)
                }
                ProtocolRuleMapBody::Update {
                    base, key, value, ..
                } => (
                    MapOperation::Update,
                    vec![
                        lower_rule_descriptor_term(
                            descriptor,
                            base,
                            Some(&SemanticSortRef::map()),
                            declarations,
                            sort_parents,
                            catalog,
                            binding_sorts,
                            subject,
                            wildcard_ordinal,
                            variables,
                        )?,
                        lower_rule_descriptor_term(
                            descriptor,
                            key,
                            None,
                            declarations,
                            sort_parents,
                            catalog,
                            binding_sorts,
                            subject,
                            wildcard_ordinal,
                            variables,
                        )?,
                        lower_rule_descriptor_term(
                            descriptor,
                            value,
                            None,
                            declarations,
                            sort_parents,
                            catalog,
                            binding_sorts,
                            subject,
                            wildcard_ordinal,
                            variables,
                        )?,
                    ],
                ),
            };
            Ok(SemanticTerm::map(
                semantic_origin(descriptor, key.clone(), "rule-map")?,
                operation,
                arguments,
            ))
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AssociativeStateFamily {
    KSequence,
    Map,
}

#[derive(Clone, Copy, Debug)]
enum RuleStateFrame<'a> {
    // Exactness is independent of surface notation: an ordinary whole-Map
    // term, `.Map`, exact map items, and a functional update all omit no
    // content. The declared cell sort validates their semantic family.
    Exact,
    Framed {
        family: AssociativeStateFamily,
        frame: &'a ProtocolRuleFrame,
    },
}

fn associative_state_frame(
    family: AssociativeStateFamily,
    frame: &ProtocolRuleFrame,
) -> RuleStateFrame<'_> {
    if matches!(frame, ProtocolRuleFrame::Exact) {
        RuleStateFrame::Exact
    } else {
        RuleStateFrame::Framed { family, frame }
    }
}

fn rule_state_frame(state: &ProtocolRuleStateTerm<DescriptorTerm>) -> RuleStateFrame<'_> {
    match state {
        ProtocolRuleStateTerm::Term(_) => RuleStateFrame::Exact,
        ProtocolRuleStateTerm::KSequence(sequence) => {
            associative_state_frame(AssociativeStateFamily::KSequence, &sequence.tail)
        }
        ProtocolRuleStateTerm::Map(map) => match &map.body {
            ProtocolRuleMapBody::Items { remainder, .. } => {
                associative_state_frame(AssociativeStateFamily::Map, remainder)
            }
            ProtocolRuleMapBody::Empty { .. } | ProtocolRuleMapBody::Update { .. } => {
                RuleStateFrame::Exact
            }
        },
    }
}

fn lower_subject_cell_frame(
    descriptor: &Descriptor,
    state: &ProtocolRuleStateTerm<DescriptorTerm>,
) -> Result<CellContentFrame, DescriptorLoweringError> {
    match rule_state_frame(state) {
        RuleStateFrame::Exact => Ok(CellContentFrame::Exact),
        RuleStateFrame::Framed {
            family: AssociativeStateFamily::KSequence,
            frame: ProtocolRuleFrame::Anonymous { key },
        } => Ok(CellContentFrame::KSequenceTail {
            origin: semantic_origin(descriptor, key.clone(), "rule-k-frame")?,
            binding: None,
        }),
        RuleStateFrame::Framed {
            family: AssociativeStateFamily::KSequence,
            frame: ProtocolRuleFrame::Bind { key, binding },
        } => Ok(CellContentFrame::KSequenceTail {
            origin: semantic_origin(descriptor, key.clone(), "rule-k-frame")?,
            binding: Some(SemanticId::new(binding.clone())?),
        }),
        RuleStateFrame::Framed {
            family: AssociativeStateFamily::Map,
            frame: ProtocolRuleFrame::Anonymous { key },
        } => Ok(CellContentFrame::MapRemainder {
            origin: semantic_origin(descriptor, key.clone(), "rule-map-frame")?,
            binding: None,
        }),
        RuleStateFrame::Framed {
            family: AssociativeStateFamily::Map,
            frame: ProtocolRuleFrame::Bind { key, binding },
        } => Ok(CellContentFrame::MapRemainder {
            origin: semantic_origin(descriptor, key.clone(), "rule-map-frame")?,
            binding: Some(SemanticId::new(binding.clone())?),
        }),
        RuleStateFrame::Framed {
            frame: ProtocolRuleFrame::Reuse { .. },
            ..
        } => Err(DescriptorLoweringError::UnsupportedShape {
            node: "subject cell frame",
            detail: "a subject frame cannot reuse a result binding".into(),
        }),
        RuleStateFrame::Framed {
            frame: ProtocolRuleFrame::Exact,
            ..
        } => unreachable!("exact associative frames are normalized"),
    }
}

fn state_frames_compatible(subject: RuleStateFrame<'_>, result: RuleStateFrame<'_>) -> bool {
    match (subject, result) {
        (
            RuleStateFrame::Exact
            | RuleStateFrame::Framed {
                frame: ProtocolRuleFrame::Anonymous { .. },
                ..
            },
            RuleStateFrame::Exact,
        ) => true,
        (
            RuleStateFrame::Framed {
                family: subject_family,
                frame:
                    ProtocolRuleFrame::Bind {
                        binding: subject, ..
                    },
            },
            RuleStateFrame::Framed {
                family: result_family,
                frame:
                    ProtocolRuleFrame::Reuse {
                        binding: result, ..
                    },
            },
        ) => subject_family == result_family && subject == result,
        _ => false,
    }
}

fn validate_state_frame_pair(
    descriptor: &Descriptor,
    subject: RuleStateFrame<'_>,
    result: RuleStateFrame<'_>,
    node: &'static str,
) -> Result<(), DescriptorLoweringError> {
    if state_frames_compatible(subject, result) {
        Ok(())
    } else {
        Err(DescriptorLoweringError::UnsupportedShape {
            node,
            detail: format!(
                "rule {:?} uses incompatible subject/result associative state families or frames",
                descriptor.id
            ),
        })
    }
}

fn validate_frame_pair(
    descriptor: &Descriptor,
    subject: &ProtocolRuleFrame,
    result: &ProtocolRuleFrame,
    node: &'static str,
) -> Result<(), DescriptorLoweringError> {
    let supported = match (subject, result) {
        (
            ProtocolRuleFrame::Exact | ProtocolRuleFrame::Anonymous { .. },
            ProtocolRuleFrame::Exact,
        ) => true,
        (
            ProtocolRuleFrame::Bind {
                binding: subject, ..
            },
            ProtocolRuleFrame::Reuse {
                binding: result, ..
            },
        ) => subject == result,
        _ => false,
    };
    if supported {
        Ok(())
    } else {
        Err(DescriptorLoweringError::UnsupportedShape {
            node,
            detail: format!(
                "rule {:?} uses incompatible subject/result frames",
                descriptor.id
            ),
        })
    }
}

fn semantic_terms_equivalent(left: &SemanticTerm, right: &SemanticTerm) -> bool {
    if left.sort() != right.sort() {
        return false;
    }
    match (left.kind(), right.kind()) {
        (
            krs_ir::SemanticTermKind::Variable { variable: left },
            krs_ir::SemanticTermKind::Variable { variable: right },
        ) => left == right,
        (
            krs_ir::SemanticTermKind::Application {
                application: left_application,
                arguments: left_arguments,
            },
            krs_ir::SemanticTermKind::Application {
                application: right_application,
                arguments: right_arguments,
            },
        ) => {
            left_application == right_application
                && semantic_term_slices_equivalent(left_arguments, right_arguments)
        }
        (
            krs_ir::SemanticTermKind::Token { value: left },
            krs_ir::SemanticTermKind::Token { value: right },
        ) => left == right,
        (
            krs_ir::SemanticTermKind::KSequence {
                item_sort: left_sort,
                items: left_items,
            },
            krs_ir::SemanticTermKind::KSequence {
                item_sort: right_sort,
                items: right_items,
            },
        ) => left_sort == right_sort && semantic_term_slices_equivalent(left_items, right_items),
        (
            krs_ir::SemanticTermKind::Map {
                operation: left_operation,
                arguments: left_arguments,
            },
            krs_ir::SemanticTermKind::Map {
                operation: right_operation,
                arguments: right_arguments,
            },
        ) => {
            left_operation == right_operation
                && semantic_term_slices_equivalent(left_arguments, right_arguments)
        }
        (
            krs_ir::SemanticTermKind::List {
                operation: left_operation,
                arguments: left_arguments,
            },
            krs_ir::SemanticTermKind::List {
                operation: right_operation,
                arguments: right_arguments,
            },
        ) => {
            left_operation == right_operation
                && semantic_term_slices_equivalent(left_arguments, right_arguments)
        }
        (
            krs_ir::SemanticTermKind::Set {
                operation: left_operation,
                arguments: left_arguments,
            },
            krs_ir::SemanticTermKind::Set {
                operation: right_operation,
                arguments: right_arguments,
            },
        ) => {
            left_operation == right_operation
                && semantic_term_slices_equivalent(left_arguments, right_arguments)
        }
        (
            krs_ir::SemanticTermKind::Rewrite {
                from: left_from,
                to: left_to,
            },
            krs_ir::SemanticTermKind::Rewrite {
                from: right_from,
                to: right_to,
            },
        ) => {
            semantic_terms_equivalent(left_from, right_from)
                && semantic_terms_equivalent(left_to, right_to)
        }
        _ => false,
    }
}

fn semantic_term_slices_equivalent(left: &[SemanticTerm], right: &[SemanticTerm]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| semantic_terms_equivalent(left, right))
}

#[cfg(test)]
mod state_frame_tests {
    use super::*;

    fn key(role: &str) -> ProvenanceKey {
        ProvenanceKey::new(role, 0).unwrap()
    }

    fn variable(role: &str) -> DescriptorTerm {
        DescriptorTerm::Variable {
            key: key(role),
            path_key: key(role),
            name: "M".into(),
        }
    }

    fn map(body: ProtocolRuleMapBody<DescriptorTerm>) -> ProtocolRuleStateTerm<DescriptorTerm> {
        ProtocolRuleStateTerm::Map(krs_ir::ProtocolRuleMap {
            payload_key: Some(key("map_payload")),
            body,
        })
    }

    fn exact_map_items() -> ProtocolRuleStateTerm<DescriptorTerm> {
        map(ProtocolRuleMapBody::Items {
            items: vec![krs_ir::ProtocolRuleMapItem {
                key_key: key("map_key"),
                key: variable("key_reference"),
                value_key: key("map_value"),
                value: variable("value_reference"),
            }],
            remainder: ProtocolRuleFrame::Exact,
        })
    }

    #[test]
    fn all_exact_map_forms_share_one_associative_family() {
        let empty = map(ProtocolRuleMapBody::Empty { explicit_dot: true });
        let items = exact_map_items();
        let update = map(ProtocolRuleMapBody::Update {
            base_key: key("map_update_base"),
            base: variable("base_reference"),
            key_key: key("map_update_key"),
            key: variable("update_key_reference"),
            value_key: key("map_update_value"),
            value: variable("update_value_reference"),
        });
        let whole_map_term = ProtocolRuleStateTerm::Term(variable("whole_map_reference"));

        assert!(state_frames_compatible(
            rule_state_frame(&empty),
            rule_state_frame(&items)
        ));
        assert!(state_frames_compatible(
            rule_state_frame(&items),
            rule_state_frame(&empty)
        ));
        assert!(state_frames_compatible(
            rule_state_frame(&items),
            rule_state_frame(&update)
        ));
        assert!(state_frames_compatible(
            rule_state_frame(&whole_map_term),
            rule_state_frame(&update)
        ));
    }

    #[test]
    fn exact_forms_do_not_admit_a_frame_and_framed_families_remain_typed() {
        let empty = map(ProtocolRuleMapBody::Empty { explicit_dot: true });
        let framed_k = ProtocolRuleStateTerm::KSequence(krs_ir::ProtocolRuleKSequence {
            payload_key: Some(key("k_payload")),
            dot_k_key: None,
            notation: krs_ir::DescriptorKSequenceNotation::Comma,
            items: Vec::new(),
            tail: ProtocolRuleFrame::Bind {
                key: key("k_remainder"),
                binding: "REST".into(),
            },
        });
        let framed_map = map(ProtocolRuleMapBody::Items {
            items: vec![krs_ir::ProtocolRuleMapItem {
                key_key: key("map_key"),
                key: variable("key_reference"),
                value_key: key("map_value"),
                value: variable("value_reference"),
            }],
            remainder: ProtocolRuleFrame::Reuse {
                key: key("map_remainder"),
                binding: "REST".into(),
            },
        });

        assert!(!state_frames_compatible(
            rule_state_frame(&empty),
            rule_state_frame(&framed_map)
        ));
        assert!(!state_frames_compatible(
            rule_state_frame(&framed_k),
            rule_state_frame(&framed_map)
        ));
    }
}

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    BuiltinSort, CellContentFrame, CellPost, Descriptor, DescriptorCellDeclaration,
    DescriptorCellIdentity, DescriptorPayload, DescriptorRuleLabel, DescriptorSortRef,
    FixedCellClause, FixedConfigurationRewrite, ItemKind, MapOperation, ProtocolCellContent,
    SemanticId, SemanticRule, SemanticRuleCondition, SemanticRuleLabel, SemanticRulePriority,
    SemanticSimplification, SemanticSimplificationPriority, SemanticSortRef, SemanticTerm,
    SemanticVariable, StableItemId, StructuredRuleDescriptor,
};
use krs_syntax::ProvenanceRole;

use super::catalog::{ProductionSignature, common_sequence_item_sort, semantic_sort_ref};
use super::error::DescriptorLoweringError;
use super::infer::{StructuredTermBuilder, initial_binding_constraints};
use super::origin::{
    generated_semantic_id, role_key, semantic_cell_id, semantic_origin,
    semantic_origin_from_primary,
};
use super::references::{require_cell_field, require_descriptor};

pub(super) fn framework_k_item_sort(
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<SemanticSortRef, DescriptorLoweringError> {
    let mut matches = declarations.keys().filter(|id| {
        id.item_kind() == ItemKind::Sort
            && id.item_name() == "KItem"
            && id.package().k_namespace() == "KRS-FRAMEWORK"
            && id.package().cargo_name() == "krs"
            && id.package().cargo_source() == "framework"
    });
    let first = matches
        .next()
        .ok_or_else(|| DescriptorLoweringError::UnsupportedShape {
            node: "complete cell term",
            detail: "fragment! requires the selected framework KItem sort".into(),
        })?;
    if matches.next().is_some() {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "complete cell term",
            detail: "fragment! found more than one selected framework KItem sort".into(),
        });
    }
    Ok(SemanticSortRef::Declared(first.clone()))
}

#[allow(clippy::too_many_lines)]
pub(super) fn lower_head_rule_descriptor(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticRule, DescriptorLoweringError> {
    if rule.sentence_kind != krs_ir::SentenceKind::Transition {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule",
            detail: "readable head completion currently supports transition rules only".into(),
        });
    }
    let configuration_descriptor =
        require_descriptor(&rule.configuration, ItemKind::Configuration, declarations)?;
    let DescriptorPayload::FixedConfiguration(configuration) = &configuration_descriptor.payload
    else {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule",
            detail: "head completion requires a fixed configuration".into(),
        });
    };
    let computation = require_cell_field(&rule.computation_cell.cell, declarations)?;
    let ProtocolCellContent::Leaf { wrapper, sort, .. } = &computation.content else {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule",
            detail: "resolved computation cell is not a fixed leaf".into(),
        });
    };
    if *wrapper != krs_ir::CellWrapper::KCell
        || sort.sort != DescriptorSortRef::Builtin(BuiltinSort::KSequence)
    {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule",
            detail: "resolved computation cell is not KCell<KSequence>".into(),
        });
    }

    let binding_names = rule
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<BTreeSet<_>>();
    if binding_names.len() != rule.bindings.len() {
        return Err(DescriptorLoweringError::InvalidTerm {
            id: Box::new(descriptor.id.clone()),
            detail: "head-anchored rule has duplicate bindings".into(),
        });
    }
    let mut binding_sorts = BTreeMap::new();
    for binding in &rule.bindings {
        if let Some(refinement) = &binding.refinement {
            binding_sorts.insert(binding.name.clone(), semantic_sort_ref(&refinement.sort));
        }
    }
    let mut map_argument_sorts = BTreeMap::new();
    let mut cell_sorts = BTreeMap::new();
    for extra in &rule.extras {
        let cell = match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, .. }
            | krs_ir::ProtocolHeadRuleExtra::UpdateMap { cell, .. }
            | krs_ir::ProtocolHeadRuleExtra::RewriteCell { cell, .. } => cell,
        };
        let declared = require_cell_field(&cell.cell, declarations)?;
        let ProtocolCellContent::Leaf {
            sort, arguments, ..
        } = &declared.content
        else {
            continue;
        };
        cell_sorts.insert(cell.cell.clone(), semantic_sort_ref(&sort.sort));
        if sort.sort == DescriptorSortRef::Builtin(BuiltinSort::Map)
            && let [key, value] = arguments.as_slice()
        {
            map_argument_sorts.insert(
                cell.cell.clone(),
                (semantic_sort_ref(&key.sort), semantic_sort_ref(&value.sort)),
            );
        }
        if let krs_ir::ProtocolHeadRuleExtra::HaveMap { value_binding, .. } = extra
            && let Some((_, value_sort)) = map_argument_sorts.get(&cell.cell)
        {
            binding_sorts
                .entry(value_binding.clone())
                .or_insert_with(|| value_sort.clone());
        }
        if let krs_ir::ProtocolHeadRuleExtra::UpdateMap { base_binding, .. } = extra {
            let cell_sort = cell_sorts.get(&cell.cell).ok_or_else(|| {
                DescriptorLoweringError::UnsupportedShape {
                    node: "head-anchored rule extra",
                    detail: format!("updated cell {:?} is not a fixed leaf", cell.cell.field),
                }
            })?;
            match binding_sorts.get(base_binding) {
                Some(sort) if sort != cell_sort => {
                    return Err(DescriptorLoweringError::InvalidTerm {
                        id: Box::new(descriptor.id.clone()),
                        detail: format!(
                            "updated-cell binding {base_binding:?} has a refinement other than {cell_sort:?}"
                        ),
                    });
                }
                Some(_) => {}
                None => {
                    binding_sorts.insert(base_binding.clone(), cell_sort.clone());
                }
            }
        }
    }
    let binding_constraints = initial_binding_constraints(&binding_sorts);
    let mut builder = StructuredTermBuilder {
        descriptor,
        catalog,
        declarations: Some(declarations),
        k_item_sort: Some(framework_k_item_sort(declarations)?),
        sort_parents,
        binding_names: &binding_names,
        pattern_key: Some(&rule.pattern_key),
        binding_sorts: BTreeMap::new(),
        binding_constraints,
        wildcard_offset: 0,
        wildcards: Vec::new(),
    };
    let head_sort = rule
        .head_sort
        .as_ref()
        .map(|sort| semantic_sort_ref(&sort.sort));
    builder.infer(&rule.subject, head_sort.as_ref(), true)?;
    match &rule.result {
        krs_ir::ProtocolHeadRuleResult::Replace(term) => {
            builder.infer(term, head_sort.as_ref(), false)?;
        }
        krs_ir::ProtocolHeadRuleResult::Splice(items) => {
            for term in items {
                builder.infer(term, head_sort.as_ref(), false)?;
            }
        }
        krs_ir::ProtocolHeadRuleResult::Erase => {}
    }
    for extra in &rule.extras {
        match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, key, .. } => {
                let expected = map_argument_sorts
                    .get(&cell.cell)
                    .map(|(key_sort, _)| key_sort);
                builder.infer(key, expected, true)?;
            }
            krs_ir::ProtocolHeadRuleExtra::UpdateMap {
                cell,
                base_binding,
                update,
            } => {
                let expected = cell_sorts.get(&cell.cell).ok_or_else(|| {
                    DescriptorLoweringError::UnsupportedShape {
                        node: "head-anchored rule extra",
                        detail: format!("updated cell {:?} is not a fixed leaf", cell.cell.field),
                    }
                })?;
                builder.infer_collection_update(
                    update,
                    base_binding,
                    expected,
                    map_argument_sorts.get(&cell.cell),
                )?;
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                cell,
                before,
                after,
                ..
            } => {
                let expected = cell_sorts.get(&cell.cell).ok_or_else(|| {
                    DescriptorLoweringError::UnsupportedShape {
                        node: "head-anchored rule extra",
                        detail: format!("ordinary cell {:?} is not a fixed leaf", cell.cell.field),
                    }
                })?;
                builder.infer(before, Some(expected), true)?;
                builder.infer(after, Some(expected), false)?;
            }
        }
    }
    let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
    if let Some(requires) = &rule.requires {
        builder.infer(&requires.term, Some(&bool_sort), false)?;
    }
    builder.resolve_binding_sorts()?;
    for binding in &rule.bindings {
        if !builder.binding_sorts.contains_key(&binding.name) {
            return Err(DescriptorLoweringError::InvalidTerm {
                id: Box::new(descriptor.id.clone()),
                detail: format!("binding {:?} has no inferred semantic sort", binding.name),
            });
        }
    }

    let subject_head = builder.lower(&rule.subject, head_sort.as_ref(), true)?;
    let subject_item_sort = subject_head.sort().clone();
    let before_k = SemanticTerm::k_sequence(
        semantic_origin(descriptor, rule.pattern_key.clone(), "completed-k-subject")?,
        subject_item_sort,
        vec![subject_head],
    );
    let result_items = match &rule.result {
        krs_ir::ProtocolHeadRuleResult::Replace(term) => {
            vec![builder.lower(term, head_sort.as_ref(), false)?]
        }
        krs_ir::ProtocolHeadRuleResult::Splice(items) => items
            .iter()
            .map(|term| builder.lower(term, head_sort.as_ref(), false))
            .collect::<Result<Vec<_>, _>>()?,
        krs_ir::ProtocolHeadRuleResult::Erase => Vec::new(),
    };
    let result_item_sort = common_sequence_item_sort(descriptor, &result_items, sort_parents)?;
    let after_k = SemanticTerm::k_sequence(
        semantic_origin(descriptor, rule.result_key.clone(), "completed-k-result")?,
        result_item_sort,
        result_items,
    );
    let mut clauses = vec![FixedCellClause::new(
        semantic_origin(descriptor, rule.pattern_key.clone(), "completed-k-clause")?,
        semantic_cell_id(&rule.computation_cell.cell)?,
        before_k,
        CellPost::Replace { term: after_k },
        CellContentFrame::KSequenceTail {
            origin: semantic_origin(descriptor, rule.pattern_key.clone(), "implicit-k-tail")?,
            binding: None,
        },
    )];
    let mut selected = BTreeSet::from([rule.computation_cell.cell.clone()]);
    for extra in &rule.extras {
        let cell_reference = match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, .. }
            | krs_ir::ProtocolHeadRuleExtra::UpdateMap { cell, .. }
            | krs_ir::ProtocolHeadRuleExtra::RewriteCell { cell, .. } => cell,
        };
        if !selected.insert(cell_reference.cell.clone()) {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "head-anchored rule",
                detail: format!(
                    "cell {:?} is mentioned more than once",
                    cell_reference.cell.field
                ),
            });
        }
        let declared = require_cell_field(&cell_reference.cell, declarations)?;
        let ProtocolCellContent::Leaf { wrapper, sort, .. } = &declared.content else {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "head-anchored rule extra",
                detail: "extra cell is not a fixed leaf".into(),
            });
        };
        match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap {
                cell,
                key,
                value_binding,
            } => {
                if *wrapper != krs_ir::CellWrapper::Cell
                    || sort.sort != DescriptorSortRef::Builtin(BuiltinSort::Map)
                {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "head-anchored rule extra",
                        detail: format!(
                            "extra cell {:?} is not a Map cell",
                            cell_reference.cell.field
                        ),
                    });
                }
                let key = builder.lower(key, None, true)?;
                let value_sort = builder
                    .binding_sorts
                    .get(value_binding)
                    .cloned()
                    .ok_or_else(|| DescriptorLoweringError::InvalidTerm {
                        id: Box::new(descriptor.id.clone()),
                        detail: format!("map value binding {value_binding:?} has no inferred sort"),
                    })?;
                let value = SemanticTerm::variable(
                    semantic_origin(descriptor, cell.key.clone(), "map-binding-value")?,
                    value_sort,
                    SemanticId::new(value_binding.clone())?,
                );
                clauses.push(FixedCellClause::new(
                    semantic_origin(descriptor, cell.key.clone(), "completed-map-read")?,
                    semantic_cell_id(&cell.cell)?,
                    SemanticTerm::map(
                        semantic_origin(descriptor, cell.key.clone(), "completed-map-item")?,
                        MapOperation::Item,
                        vec![key, value],
                    ),
                    CellPost::Preserve,
                    CellContentFrame::MapRemainder {
                        origin: semantic_origin(
                            descriptor,
                            cell.key.clone(),
                            "implicit-map-remainder",
                        )?,
                        binding: None,
                    },
                ));
            }
            krs_ir::ProtocolHeadRuleExtra::UpdateMap {
                cell,
                base_binding,
                update,
            } => {
                if *wrapper != krs_ir::CellWrapper::Cell
                    || !matches!(
                        sort.sort,
                        DescriptorSortRef::Builtin(BuiltinSort::Map | BuiltinSort::List)
                    )
                {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "head-anchored rule extra",
                        detail: format!(
                            "updated cell {:?} is not a Map or List cell",
                            cell_reference.cell.field
                        ),
                    });
                }
                let expected = semantic_sort_ref(&sort.sort);
                let (before_role, write_role) =
                    if sort.sort == DescriptorSortRef::Builtin(BuiltinSort::Map) {
                        ("map-update-before", "completed-map-write")
                    } else {
                        ("list-update-before", "completed-list-write")
                    };
                let before = SemanticTerm::variable(
                    semantic_origin(descriptor, cell.key.clone(), before_role)?,
                    expected.clone(),
                    SemanticId::new(base_binding.clone())?,
                );
                let after = builder.lower(update, Some(&expected), false)?;
                clauses.push(FixedCellClause::new(
                    semantic_origin(descriptor, cell.key.clone(), write_role)?,
                    semantic_cell_id(&cell.cell)?,
                    before,
                    CellPost::Replace { term: after },
                    CellContentFrame::Exact,
                ));
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                cell,
                result_key,
                before,
                after,
            } => {
                if *wrapper != krs_ir::CellWrapper::Cell {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "head-anchored rule extra",
                        detail: format!(
                            "ordinary cell {:?} does not use the Cell wrapper",
                            cell_reference.cell.field
                        ),
                    });
                }
                let expected = semantic_sort_ref(&sort.sort);
                let before = builder.lower(before, Some(&expected), true)?;
                let after = builder.lower(after, Some(&expected), false)?;
                clauses.push(FixedCellClause::new(
                    semantic_origin(descriptor, cell.key.clone(), "completed-cell-rewrite")?,
                    semantic_cell_id(&cell.cell)?,
                    before,
                    CellPost::Replace { term: after },
                    CellContentFrame::Exact,
                ));
                let _ = semantic_origin(
                    descriptor,
                    result_key.clone(),
                    "completed-cell-rewrite-result",
                )?;
            }
        }
    }
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
    let body = FixedConfigurationRewrite::new(
        semantic_origin(
            descriptor,
            rule.pattern_key.clone(),
            "completed-configuration-rewrite",
        )?,
        generated_semantic_id("configuration", &rule.configuration, None)?,
        clauses,
        omitted_siblings,
    )?;
    let requires = rule
        .requires
        .as_ref()
        .map(|condition| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRuleCondition::new(
                semantic_origin(descriptor, condition.key.clone(), "rule-requires")?,
                builder.lower(&condition.term, Some(&bool_sort), false)?,
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
    let mut variables = rule
        .bindings
        .iter()
        .map(|binding| {
            Ok(SemanticVariable::new(
                SemanticId::new(binding.name.clone())?,
                builder
                    .binding_sorts
                    .get(&binding.name)
                    .cloned()
                    .expect("all binding sorts were inferred"),
            ))
        })
        .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
    variables.append(&mut builder.wildcards);
    Ok(SemanticRule::new_configuration(
        semantic_origin(
            descriptor,
            role_key(ProvenanceRole::RuleDeclaration, 0)?,
            "head-anchored-rule",
        )?,
        descriptor.id.clone(),
        rule.sentence_kind,
        variables,
        body,
    )?
    .with_label(lower_rule_label(descriptor, rule.label.as_ref())?)
    .with_priority(priority)?
    .with_requires(requires)?)
}

pub(super) fn collect_declared_leaf_identities(
    declaration: &DescriptorCellDeclaration,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    visiting: &mut BTreeSet<StableItemId>,
    leaves: &mut Vec<DescriptorCellIdentity>,
) -> Result<(), DescriptorLoweringError> {
    for field in &declaration.fields {
        match &field.content {
            ProtocolCellContent::Leaf { .. } => leaves.push(field.reference.cell.clone()),
            ProtocolCellContent::Nested { declaration } => {
                if !visiting.insert(declaration.declaration.clone()) {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "nested cell declaration",
                        detail: "cyclic nominal cell declaration".into(),
                    });
                }
                let descriptor =
                    require_descriptor(&declaration.declaration, ItemKind::Cell, declarations)?;
                let DescriptorPayload::Cell(nested) = &descriptor.payload else {
                    unreachable!("kind-checked descriptor has a cell payload")
                };
                collect_declared_leaf_identities(nested, declarations, visiting, leaves)?;
                visiting.remove(&declaration.declaration);
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_lines)] // One closed pass performs inference, lowering, and metadata.
pub(super) fn lower_structured_rule_descriptor(
    descriptor: &Descriptor,
    rule: &StructuredRuleDescriptor,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticRule, DescriptorLoweringError> {
    let binding_names = rule.bindings.iter().cloned().collect::<BTreeSet<_>>();
    let mut builder = StructuredTermBuilder {
        descriptor,
        catalog,
        declarations: None,
        k_item_sort: None,
        sort_parents,
        binding_names: &binding_names,
        pattern_key: Some(&rule.pattern_key),
        binding_sorts: BTreeMap::new(),
        binding_constraints: BTreeMap::new(),
        wildcard_offset: 0,
        wildcards: Vec::new(),
    };
    let subject_sort = semantic_sort_ref(&rule.subject_sort.sort);
    let result_sort = semantic_sort_ref(&rule.result_sort.sort);
    let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
    builder.infer(&rule.subject, Some(&subject_sort), true)?;
    if let Some(requires) = &rule.requires {
        builder.infer(&requires.term, Some(&bool_sort), false)?;
    }
    builder.infer(&rule.result, Some(&result_sort), false)?;
    builder.resolve_binding_sorts()?;
    let subject = builder.lower(&rule.subject, Some(&subject_sort), true)?;
    let result = builder.lower(&rule.result, Some(&result_sort), false)?;
    let requires = rule
        .requires
        .as_ref()
        .map(|condition| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRuleCondition::new(
                semantic_origin(descriptor, condition.key.clone(), "rule-requires")?,
                builder.lower(&condition.term, Some(&bool_sort), false)?,
            ))
        })
        .transpose()?;
    let priority = rule
        .priority
        .as_ref()
        .map(|priority| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRulePriority::new(
                semantic_origin(
                    descriptor,
                    priority.key.clone(),
                    if rule.sentence_kind == krs_ir::SentenceKind::Transition {
                        "rule-owise"
                    } else {
                        "equation-priority"
                    },
                )?,
                priority.value,
            ))
        })
        .transpose()?;
    let simplification = rule
        .simplification
        .as_ref()
        .map(|simplification| -> Result<_, DescriptorLoweringError> {
            let priority = simplification
                .priority
                .as_ref()
                .map(|priority| -> Result<_, DescriptorLoweringError> {
                    Ok(SemanticSimplificationPriority::new(
                        semantic_origin(
                            descriptor,
                            priority.key.clone(),
                            "simplification-priority",
                        )?,
                        priority.value,
                    ))
                })
                .transpose()?;
            Ok(SemanticSimplification::new(
                semantic_origin(descriptor, simplification.key.clone(), "simplification")?,
                priority,
            ))
        })
        .transpose()?;
    let mut variables = Vec::new();
    for binding in &rule.bindings {
        let sort = builder.binding_sorts.get(binding).cloned().ok_or_else(|| {
            DescriptorLoweringError::InvalidTerm {
                id: Box::new(descriptor.id.clone()),
                detail: format!("binding {binding:?} has no inferred subject sort"),
            }
        })?;
        variables.push(SemanticVariable::new(
            SemanticId::new(binding.clone())?,
            sort,
        ));
    }
    variables.extend(builder.wildcards);
    let rewrite = SemanticTerm::rewrite(
        semantic_origin_from_primary(descriptor, "rule-rewrite")?,
        result_sort,
        subject,
        result,
    )?;
    let rule_origin_role = if rule.sentence_kind == krs_ir::SentenceKind::Alias {
        ProvenanceRole::AliasClause
    } else {
        ProvenanceRole::RuleDeclaration
    };
    Ok(SemanticRule::new(
        semantic_origin(descriptor, role_key(rule_origin_role, 0)?, "rule")?,
        descriptor.id.clone(),
        rule.sentence_kind,
        variables,
        rewrite,
    )?
    .with_label(lower_rule_label(descriptor, rule.label.as_ref())?)
    .with_priority(priority)?
    .with_simplification(simplification)
    .with_requires(requires)?)
}

pub(super) fn lower_rule_label(
    descriptor: &Descriptor,
    label: Option<&DescriptorRuleLabel>,
) -> Result<Option<SemanticRuleLabel>, DescriptorLoweringError> {
    label
        .map(|label| {
            Ok(SemanticRuleLabel::new(
                semantic_origin(descriptor, label.key.clone(), "rule-label")?,
                label.name.clone(),
            )?)
        })
        .transpose()
}

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    BuiltinSort, CellContentFrame, CellPost, Descriptor, DescriptorCellDeclaration,
    DescriptorCellIdentity, DescriptorCellReference, DescriptorFixedConfiguration,
    DescriptorHeadRuleExtra, DescriptorIndex, DescriptorRuleCondition, DescriptorRuleLabel,
    DescriptorRulePriority, DescriptorSimplification, DescriptorSortRef, DescriptorSortReference,
    DescriptorTerm, FixedCellClause, FixedConfigurationRewrite, ItemKind, ProtocolCellContent,
    ProvenanceKey, SemanticId, StableItemId, StructuredRuleDescriptor,
};
use krs_ir_levels::{
    MapOperands, SemanticRule, SemanticRuleCondition, SemanticRuleLabel, SemanticRulePriority,
    SemanticSimplification, SemanticSimplificationPriority, SemanticSortRef, SemanticTerm,
    SemanticVariable,
};
use krs_syntax::ProvenanceRole;

use super::catalog::{ProductionSignature, common_sequence_item_sort, semantic_sort_ref};
use super::error::DescriptorLoweringError;
use super::infer::{StructuredTermBuilder, initial_binding_constraints};
use super::origin::{
    generated_semantic_id, role_key, semantic_cell_id, semantic_origin,
    semantic_origin_from_primary,
};
use super::references::require_cell_field;

pub(super) fn framework_k_item_sort(
    declarations: &DescriptorIndex<'_>,
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

/// Resolves `configuration` to its fixed-configuration payload.
pub(super) fn require_fixed_configuration<'a>(
    configuration: &StableItemId,
    declarations: &'a DescriptorIndex<'_>,
    node: &'static str,
    detail: &'static str,
) -> Result<&'a DescriptorFixedConfiguration, DescriptorLoweringError> {
    declarations
        .configuration(configuration)
        .map_err(|error| match error {
            krs_ir::LookupError::WrongKind { ref id, .. }
                if id.item_kind() == ItemKind::Configuration =>
            {
                DescriptorLoweringError::UnsupportedShape {
                    node,
                    detail: detail.into(),
                }
            }
            other => other.into(),
        })
}

/// Returns the semantic identities of every fixed leaf cell of `declaration`
/// that `selected` does not name, in declaration order.
pub(super) fn omitted_leaf_cells(
    declaration: &DescriptorCellDeclaration,
    declarations: &DescriptorIndex<'_>,
    selected: &BTreeSet<DescriptorCellIdentity>,
) -> Result<Vec<SemanticId>, DescriptorLoweringError> {
    let mut all_leaves = Vec::new();
    collect_declared_leaf_identities(
        declaration,
        declarations,
        &mut BTreeSet::new(),
        &mut all_leaves,
    )?;
    all_leaves
        .into_iter()
        .filter(|identity| !selected.contains(identity))
        .map(|identity| semantic_cell_id(&identity))
        .collect()
}

/// Lowers an optional rule priority with the given origin role.
pub(super) fn lower_rule_priority(
    descriptor: &Descriptor,
    priority: Option<&DescriptorRulePriority>,
    role: &str,
) -> Result<Option<SemanticRulePriority>, DescriptorLoweringError> {
    priority
        .map(|priority| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRulePriority::new(
                semantic_origin(descriptor, priority.key.clone(), role)?,
                priority.value,
            ))
        })
        .transpose()
}

/// Lowers an optional Boolean `requires` condition through an inferred builder.
fn lower_rule_requires(
    builder: &mut StructuredTermBuilder<'_>,
    requires: Option<&DescriptorRuleCondition>,
) -> Result<Option<SemanticRuleCondition>, DescriptorLoweringError> {
    let descriptor = builder.descriptor;
    let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
    requires
        .map(|condition| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRuleCondition::new(
                semantic_origin(descriptor, condition.key.clone(), "rule-requires")?,
                builder.lower(&condition.term, Some(&bool_sort), false)?,
            ))
        })
        .transpose()
}

/// Binding names and the sorts known before head-rule inference: authored
/// refinements, sorts implied by selected cells, and each extra cell's sort.
struct HeadRuleSeeds {
    binding_names: BTreeSet<String>,
    binding_sorts: BTreeMap<String, SemanticSortRef>,
    map_argument_sorts: BTreeMap<DescriptorCellIdentity, (SemanticSortRef, SemanticSortRef)>,
    cell_sorts: BTreeMap<DescriptorCellIdentity, SemanticSortRef>,
}

fn head_rule_extra_cell(extra: &DescriptorHeadRuleExtra) -> &DescriptorCellReference {
    match extra {
        krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, .. }
        | krs_ir::ProtocolHeadRuleExtra::UpdateMap { cell, .. }
        | krs_ir::ProtocolHeadRuleExtra::RewriteCell { cell, .. } => cell,
    }
}

pub(super) fn lower_head_rule_descriptor(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &DescriptorIndex<'_>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticRule, DescriptorLoweringError> {
    let configuration = head_rule_configuration(rule, declarations)?;
    let seeds = seed_head_rule_sorts(descriptor, rule, declarations)?;
    let binding_constraints = initial_binding_constraints(&seeds.binding_sorts);
    let mut builder = StructuredTermBuilder {
        descriptor,
        catalog,
        declarations: Some(declarations),
        k_item_sort: Some(framework_k_item_sort(declarations)?),
        sort_parents,
        binding_names: &seeds.binding_names,
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
    infer_head_rule(&mut builder, rule, head_sort.as_ref(), &seeds)?;

    let mut clauses = vec![lower_head_rule_computation_clause(
        &mut builder,
        rule,
        head_sort.as_ref(),
        sort_parents,
    )?];
    let mut selected = BTreeSet::from([rule.computation_cell.cell.clone()]);
    for extra in &rule.extras {
        clauses.push(lower_head_rule_extra(
            &mut builder,
            extra,
            declarations,
            &mut selected,
        )?);
    }
    let omitted_siblings = omitted_leaf_cells(&configuration.declaration, declarations, &selected)?;
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
    let requires = lower_rule_requires(&mut builder, rule.requires.as_ref())?;
    let priority = lower_rule_priority(descriptor, rule.priority.as_ref(), "rule-owise")?;
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
            role_key(ProvenanceRole::RuleDeclaration, 0),
            "head-anchored-rule",
        )?,
        descriptor.id().clone(),
        rule.sentence_kind,
        variables,
        body,
    )?
    .with_label(lower_rule_label(descriptor, rule.label.as_ref())?)
    .with_priority(priority)?
    .with_requires(requires)?)
}

/// Checks the head rule's sentence kind and computation cell and returns its
/// fixed configuration.
fn head_rule_configuration<'a>(
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &'a DescriptorIndex<'_>,
) -> Result<&'a DescriptorFixedConfiguration, DescriptorLoweringError> {
    if rule.sentence_kind != krs_ir::SentenceKind::Transition {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule",
            detail: "readable head completion currently supports transition rules only".into(),
        });
    }
    let configuration = require_fixed_configuration(
        &rule.configuration,
        declarations,
        "head-anchored rule",
        "head completion requires a fixed configuration",
    )?;
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
    Ok(configuration)
}

fn seed_head_rule_sorts(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &DescriptorIndex<'_>,
) -> Result<HeadRuleSeeds, DescriptorLoweringError> {
    let binding_names = rule
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<BTreeSet<_>>();
    if binding_names.len() != rule.bindings.len() {
        return Err(DescriptorLoweringError::InvalidTerm {
            id: Box::new(descriptor.id().clone()),
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
        let cell = head_rule_extra_cell(extra);
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
                        id: Box::new(descriptor.id().clone()),
                        detail: format!(
                            "updated-cell binding {base_binding:?} has a refinement other than {cell_sort}"
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
    Ok(HeadRuleSeeds {
        binding_names,
        binding_sorts,
        map_argument_sorts,
        cell_sorts,
    })
}

/// Infers every term of the head rule and checks that each binding has a sort.
fn infer_head_rule(
    builder: &mut StructuredTermBuilder<'_>,
    rule: &krs_ir::DescriptorHeadRule,
    head_sort: Option<&SemanticSortRef>,
    seeds: &HeadRuleSeeds,
) -> Result<(), DescriptorLoweringError> {
    builder.infer(&rule.subject, head_sort, true)?;
    match &rule.result {
        krs_ir::ProtocolHeadRuleResult::Replace(term) => {
            builder.infer(term, head_sort, false)?;
        }
        krs_ir::ProtocolHeadRuleResult::Splice(items) => {
            for term in items {
                builder.infer(term, head_sort, false)?;
            }
        }
        krs_ir::ProtocolHeadRuleResult::Erase => {}
    }
    for extra in &rule.extras {
        match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, key, .. } => {
                let expected = seeds
                    .map_argument_sorts
                    .get(&cell.cell)
                    .map(|(key_sort, _)| key_sort);
                builder.infer(key, expected, true)?;
            }
            krs_ir::ProtocolHeadRuleExtra::UpdateMap {
                cell,
                base_binding,
                update,
            } => {
                let expected = seeds.cell_sorts.get(&cell.cell).ok_or_else(|| {
                    DescriptorLoweringError::UnsupportedShape {
                        node: "head-anchored rule extra",
                        detail: format!("updated cell {:?} is not a fixed leaf", cell.cell.field),
                    }
                })?;
                builder.infer_collection_update(
                    update,
                    base_binding,
                    expected,
                    seeds.map_argument_sorts.get(&cell.cell),
                )?;
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                cell,
                before,
                after,
                ..
            } => {
                let expected = seeds.cell_sorts.get(&cell.cell).ok_or_else(|| {
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
                id: Box::new(builder.descriptor.id().clone()),
                detail: format!("binding {:?} has no inferred semantic sort", binding.name),
            });
        }
    }
    Ok(())
}

/// Lowers the matched head and its result into the computation-cell clause,
/// which preserves the implicit K-sequence tail.
fn lower_head_rule_computation_clause(
    builder: &mut StructuredTermBuilder<'_>,
    rule: &krs_ir::DescriptorHeadRule,
    head_sort: Option<&SemanticSortRef>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<FixedCellClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = builder.descriptor;
    let subject_head = builder.lower(&rule.subject, head_sort, true)?;
    let subject_item_sort = subject_head.sort().clone();
    let before_k = SemanticTerm::k_sequence(
        semantic_origin(descriptor, rule.pattern_key.clone(), "completed-k-subject")?,
        subject_item_sort,
        vec![subject_head],
    );
    let result_items = match &rule.result {
        krs_ir::ProtocolHeadRuleResult::Replace(term) => {
            vec![builder.lower(term, head_sort, false)?]
        }
        krs_ir::ProtocolHeadRuleResult::Splice(items) => items
            .iter()
            .map(|term| builder.lower(term, head_sort, false))
            .collect::<Result<Vec<_>, _>>()?,
        krs_ir::ProtocolHeadRuleResult::Erase => Vec::new(),
    };
    let result_item_sort = common_sequence_item_sort(descriptor, &result_items, sort_parents)?;
    let after_k = SemanticTerm::k_sequence(
        semantic_origin(descriptor, rule.result_key.clone(), "completed-k-result")?,
        result_item_sort,
        result_items,
    );
    Ok(FixedCellClause::new(
        semantic_origin(descriptor, rule.pattern_key.clone(), "completed-k-clause")?,
        semantic_cell_id(&rule.computation_cell.cell)?,
        before_k,
        CellPost::Replace { term: after_k },
        CellContentFrame::KSequenceTail {
            origin: semantic_origin(descriptor, rule.pattern_key.clone(), "implicit-k-tail")?,
            binding: None,
        },
    ))
}

/// Lowers one extra-cell read or write after checking that the cell is
/// selected once and has the leaf shape the extra requires.
fn lower_head_rule_extra(
    builder: &mut StructuredTermBuilder<'_>,
    extra: &DescriptorHeadRuleExtra,
    declarations: &DescriptorIndex<'_>,
    selected: &mut BTreeSet<DescriptorCellIdentity>,
) -> Result<FixedCellClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let cell_reference = head_rule_extra_cell(extra);
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
        } => lower_head_rule_map_read(builder, cell, key, value_binding, *wrapper, sort),
        krs_ir::ProtocolHeadRuleExtra::UpdateMap {
            cell,
            base_binding,
            update,
        } => lower_head_rule_collection_write(builder, cell, base_binding, update, *wrapper, sort),
        krs_ir::ProtocolHeadRuleExtra::RewriteCell {
            cell,
            result_key,
            before,
            after,
        } => lower_head_rule_cell_rewrite(builder, cell, result_key, before, after, *wrapper, sort),
    }
}

fn lower_head_rule_map_read(
    builder: &mut StructuredTermBuilder<'_>,
    cell: &DescriptorCellReference,
    key: &DescriptorTerm,
    value_binding: &str,
    wrapper: krs_ir::CellWrapper,
    sort: &DescriptorSortReference,
) -> Result<FixedCellClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = builder.descriptor;
    if wrapper != krs_ir::CellWrapper::Cell
        || sort.sort != DescriptorSortRef::Builtin(BuiltinSort::Map)
    {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule extra",
            detail: format!("extra cell {:?} is not a Map cell", cell.cell.field),
        });
    }
    let key = builder.lower(key, None, true)?;
    let value_sort = builder
        .binding_sorts
        .get(value_binding)
        .cloned()
        .ok_or_else(|| DescriptorLoweringError::InvalidTerm {
            id: Box::new(descriptor.id().clone()),
            detail: format!("map value binding {value_binding:?} has no inferred sort"),
        })?;
    let value = SemanticTerm::variable(
        semantic_origin(descriptor, cell.key.clone(), "map-binding-value")?,
        value_sort,
        SemanticId::new(value_binding.to_owned())?,
    );
    Ok(FixedCellClause::new(
        semantic_origin(descriptor, cell.key.clone(), "completed-map-read")?,
        semantic_cell_id(&cell.cell)?,
        SemanticTerm::map(
            semantic_origin(descriptor, cell.key.clone(), "completed-map-item")?,
            MapOperands::entry(key, value),
        ),
        CellPost::Preserve,
        CellContentFrame::MapRemainder {
            origin: semantic_origin(descriptor, cell.key.clone(), "implicit-map-remainder")?,
            binding: None,
        },
    ))
}

fn lower_head_rule_collection_write(
    builder: &mut StructuredTermBuilder<'_>,
    cell: &DescriptorCellReference,
    base_binding: &str,
    update: &DescriptorTerm,
    wrapper: krs_ir::CellWrapper,
    sort: &DescriptorSortReference,
) -> Result<FixedCellClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = builder.descriptor;
    if wrapper != krs_ir::CellWrapper::Cell
        || !matches!(
            sort.sort,
            DescriptorSortRef::Builtin(BuiltinSort::Map | BuiltinSort::List)
        )
    {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule extra",
            detail: format!(
                "updated cell {:?} is not a Map or List cell",
                cell.cell.field
            ),
        });
    }
    let expected = semantic_sort_ref(&sort.sort);
    let (before_role, write_role) = if sort.sort == DescriptorSortRef::Builtin(BuiltinSort::Map) {
        ("map-update-before", "completed-map-write")
    } else {
        ("list-update-before", "completed-list-write")
    };
    let before = SemanticTerm::variable(
        semantic_origin(descriptor, cell.key.clone(), before_role)?,
        expected.clone(),
        SemanticId::new(base_binding.to_owned())?,
    );
    let after = builder.lower(update, Some(&expected), false)?;
    Ok(FixedCellClause::new(
        semantic_origin(descriptor, cell.key.clone(), write_role)?,
        semantic_cell_id(&cell.cell)?,
        before,
        CellPost::Replace { term: after },
        CellContentFrame::Exact,
    ))
}

fn lower_head_rule_cell_rewrite(
    builder: &mut StructuredTermBuilder<'_>,
    cell: &DescriptorCellReference,
    result_key: &ProvenanceKey,
    before: &DescriptorTerm,
    after: &DescriptorTerm,
    wrapper: krs_ir::CellWrapper,
    sort: &DescriptorSortReference,
) -> Result<FixedCellClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = builder.descriptor;
    if wrapper != krs_ir::CellWrapper::Cell {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule extra",
            detail: format!(
                "ordinary cell {:?} does not use the Cell wrapper",
                cell.cell.field
            ),
        });
    }
    let expected = semantic_sort_ref(&sort.sort);
    let before = builder.lower(before, Some(&expected), true)?;
    let after = builder.lower(after, Some(&expected), false)?;
    let clause = FixedCellClause::new(
        semantic_origin(descriptor, cell.key.clone(), "completed-cell-rewrite")?,
        semantic_cell_id(&cell.cell)?,
        before,
        CellPost::Replace { term: after },
        CellContentFrame::Exact,
    );
    let _ = semantic_origin(
        descriptor,
        result_key.clone(),
        "completed-cell-rewrite-result",
    )?;
    Ok(clause)
}

fn collect_declared_leaf_identities(
    declaration: &DescriptorCellDeclaration,
    declarations: &DescriptorIndex<'_>,
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
                let nested = declarations.cell(&declaration.declaration)?;
                collect_declared_leaf_identities(nested, declarations, visiting, leaves)?;
                visiting.remove(&declaration.declaration);
            }
        }
    }
    Ok(())
}

pub(super) fn lower_structured_rule_descriptor(
    descriptor: &Descriptor,
    rule: &StructuredRuleDescriptor,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
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
    let requires = lower_rule_requires(&mut builder, rule.requires.as_ref())?;
    let priority = lower_rule_priority(
        descriptor,
        rule.priority.as_ref(),
        if rule.sentence_kind == krs_ir::SentenceKind::Transition {
            "rule-owise"
        } else {
            "equation-priority"
        },
    )?;
    let simplification = lower_rule_simplification(descriptor, rule.simplification.as_ref())?;
    let mut variables = Vec::new();
    for binding in &rule.bindings {
        let sort = builder.binding_sorts.get(binding).cloned().ok_or_else(|| {
            DescriptorLoweringError::InvalidTerm {
                id: Box::new(descriptor.id().clone()),
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
        semantic_origin(descriptor, role_key(rule_origin_role, 0), "rule")?,
        descriptor.id().clone(),
        rule.sentence_kind,
        variables,
        rewrite,
    )?
    .with_label(lower_rule_label(descriptor, rule.label.as_ref())?)
    .with_priority(priority)?
    .with_simplification(simplification)
    .with_requires(requires)?)
}

fn lower_rule_simplification(
    descriptor: &Descriptor,
    simplification: Option<&DescriptorSimplification>,
) -> Result<Option<SemanticSimplification>, DescriptorLoweringError> {
    simplification
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
        .transpose()
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

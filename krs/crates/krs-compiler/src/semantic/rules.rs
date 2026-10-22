use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    BuiltinSort, CellContentFrame, CellPost, ConfigurationClause, Descriptor,
    DescriptorCellDeclaration, DescriptorCellIdentity, DescriptorCellReference,
    DescriptorFixedConfiguration, DescriptorHeadRuleExtra, DescriptorIndex,
    DescriptorRuleCondition, DescriptorRuleLabel, DescriptorRulePriority, DescriptorSimplification,
    DescriptorSortRef, DescriptorSortReference, DescriptorTerm, FixedCellClause,
    FixedConfigurationRewrite, ItemKind, ProtocolCellContent, ProvenanceKey, SemanticId,
    StableItemId, StructuredRuleDescriptor,
};
use krs_ir_levels::{
    MapEntry, MapOperands, SemanticCondition, SemanticNondetGroup, SemanticRule, SemanticRuleLabel,
    SemanticRulePriority, SemanticSimplification, SemanticSimplificationPriority, SemanticSortRef,
    SemanticTerm, SemanticVariable,
};
use krs_syntax::ProvenanceRole;

use super::catalog::{ProductionSignature, common_sequence_item_sort, semantic_sort_ref};
use super::configuration::{check_stdin_reads, stdin_cells};
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
/// that `selected` does not name, in declaration order. A selected nested
/// (group) cell covers every leaf below it (KF-016).
pub(super) fn omitted_leaf_cells(
    declaration: &DescriptorCellDeclaration,
    declarations: &DescriptorIndex<'_>,
    selected: &BTreeSet<DescriptorCellIdentity>,
) -> Result<Vec<SemanticId>, DescriptorLoweringError> {
    let mut all_leaves = Vec::new();
    collect_declared_leaf_identities(
        declaration,
        declarations,
        selected,
        &mut BTreeSet::new(),
        &mut all_leaves,
    )?;
    all_leaves
        .into_iter()
        .filter(|identity| !selected.contains(identity))
        .map(|identity| semantic_cell_id(&identity))
        .collect()
}

/// Rejects a rule that selects a nested (group) cell together with one of
/// the cells below it (KF-016): the group clause already names that cell.
pub(super) fn check_group_descendants(
    descriptor: &Descriptor,
    pattern_key: &ProvenanceKey,
    declaration: &DescriptorCellDeclaration,
    declarations: &DescriptorIndex<'_>,
    selected: &BTreeSet<DescriptorCellIdentity>,
) -> Result<(), DescriptorLoweringError> {
    fn below(
        declaration: &DescriptorCellDeclaration,
        declarations: &DescriptorIndex<'_>,
        depth: usize,
        output: &mut Vec<DescriptorCellIdentity>,
    ) -> Result<(), DescriptorLoweringError> {
        if depth > 64 {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "nested cell declaration",
                detail: "cyclic nominal cell declaration".into(),
            });
        }
        for field in &declaration.fields {
            output.push(field.reference.cell.clone());
            if let ProtocolCellContent::Nested { declaration } = &field.content {
                below(
                    declarations.cell(&declaration.declaration)?,
                    declarations,
                    depth + 1,
                    output,
                )?;
            }
        }
        Ok(())
    }
    fn first_conflict(
        declaration: &DescriptorCellDeclaration,
        declarations: &DescriptorIndex<'_>,
        selected: &BTreeSet<DescriptorCellIdentity>,
        depth: usize,
    ) -> Result<Option<(String, String)>, DescriptorLoweringError> {
        if depth > 64 {
            return Ok(None);
        }
        for field in &declaration.fields {
            let ProtocolCellContent::Nested { declaration } = &field.content else {
                continue;
            };
            let nested = declarations.cell(&declaration.declaration)?;
            if selected.contains(&field.reference.cell) {
                let mut descendants = Vec::new();
                below(nested, declarations, 0, &mut descendants)?;
                if let Some(descendant) = descendants.iter().find(|cell| selected.contains(cell)) {
                    return Ok(Some((field.rust_field.clone(), descendant.field.clone())));
                }
            }
            if let Some(conflict) = first_conflict(nested, declarations, selected, depth + 1)? {
                return Ok(Some(conflict));
            }
        }
        Ok(None)
    }
    let Some((group, descendant)) = first_conflict(declaration, declarations, selected, 0)? else {
        return Ok(());
    };
    Err(DescriptorLoweringError::GroupAndDescendant {
        rule: Box::new(descriptor.id().clone()),
        group,
        descendant,
        range: semantic_origin(descriptor, pattern_key.clone(), "group-descendant-pattern")?
            .origin()
            .exact_authored_range()
            .map(Box::new),
    })
}

/// Lowers an optional rule priority; its origin label names the authored key.
///
/// `owise` lowers to priority 200 on transitions and equations alike, and
/// `priority = N` to N, so both routes emit the same `priority(N)` attribute.
pub(super) fn lower_rule_priority(
    descriptor: &Descriptor,
    priority: Option<&DescriptorRulePriority>,
) -> Result<Option<SemanticRulePriority>, DescriptorLoweringError> {
    priority
        .map(|priority| -> Result<_, DescriptorLoweringError> {
            let role = match priority.key.role() {
                ProvenanceRole::RuleOwise => "rule-owise",
                ProvenanceRole::RulePriority => "rule-priority",
                ProvenanceRole::EquationOwise => "equation-owise",
                _ => "equation-priority",
            };
            Ok(SemanticRulePriority::new(
                semantic_origin(descriptor, priority.key.clone(), role)?,
                priority.value,
            ))
        })
        .transpose()
}

/// Lowers the optional check-only `nondet = group` key of a transition.
pub(super) fn lower_nondet_group(
    descriptor: &Descriptor,
    nondet: Option<&krs_ir::DescriptorNondetGroup>,
) -> Result<Option<SemanticNondetGroup>, DescriptorLoweringError> {
    nondet
        .map(|group| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticNondetGroup::new(
                semantic_origin(descriptor, group.key.clone(), "rule-nondet-group")?,
                group.name.clone(),
            ))
        })
        .transpose()
}

/// Lowers an optional `requires` condition through an inferred builder: an
/// object Bool, or a matching-logic predicate (KF-039).
fn lower_rule_requires(
    builder: &mut StructuredTermBuilder<'_>,
    requires: Option<&DescriptorRuleCondition>,
) -> Result<Option<SemanticCondition>, DescriptorLoweringError> {
    requires
        .map(|condition| super::ml::lower_condition(builder, condition, "rule-requires"))
        .transpose()
}

/// Infers a sentence's `requires` and `ensures` conditions, rejecting a
/// matching-logic predicate where the sentence kind admits none (KF-039).
pub(super) fn infer_rule_conditions(
    builder: &mut StructuredTermBuilder<'_>,
    kind: krs_ir::SentenceKind,
    requires: Option<&DescriptorRuleCondition>,
    ensures: Option<&DescriptorRuleCondition>,
) -> Result<(), DescriptorLoweringError> {
    if let Some(requires) = requires {
        super::ml::check_condition_placement(builder, kind, requires, false)?;
        super::ml::infer_condition(builder, requires)?;
    }
    if let Some(ensures) = ensures {
        super::ml::check_condition_placement(builder, kind, ensures, true)?;
        super::ml::infer_condition(builder, ensures)?;
    }
    Ok(())
}

/// Binding names and the sorts known before head-rule inference: authored
/// refinements, sorts implied by selected cells, and each extra cell's sort.
struct HeadRuleSeeds {
    binding_names: BTreeSet<String>,
    binding_sorts: BTreeMap<String, SemanticSortRef>,
    map_argument_sorts: BTreeMap<DescriptorCellIdentity, (SemanticSortRef, SemanticSortRef)>,
    cell_sorts: BTreeMap<DescriptorCellIdentity, SemanticSortRef>,
}

/// Every term of a head rule: its matched items and result, its cells'
/// patterns and results, and its conditions.
pub(super) fn head_rule_terms(rule: &krs_ir::DescriptorHeadRule) -> Vec<&DescriptorTerm> {
    let mut terms = Vec::new();
    if let Some(head) = &rule.head {
        terms.extend(&head.items);
        match &head.result {
            Some(krs_ir::ProtocolHeadRuleResult::Replace(term)) => terms.push(term),
            Some(krs_ir::ProtocolHeadRuleResult::Splice(items)) => terms.extend(items),
            Some(krs_ir::ProtocolHeadRuleResult::Erase) | None => {}
        }
    }
    for extra in &rule.extras {
        match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap { entries, .. } => {
                terms.extend(entries.iter().map(|entry| &entry.key));
            }
            krs_ir::ProtocolHeadRuleExtra::UpdateMap { update, .. } => terms.push(update),
            krs_ir::ProtocolHeadRuleExtra::RewriteCell { before, after, .. } => {
                terms.push(before);
                terms.extend(after);
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteState { before, after, .. } => {
                terms.extend(before.terms());
                terms.extend(after.iter().flat_map(krs_ir::ProtocolRuleStateTerm::terms));
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteList { before, after, .. } => {
                terms.extend(before.terms());
                terms.extend(after.iter().flat_map(krs_ir::ProtocolHeadRuleList::terms));
            }
        }
    }
    terms.extend(rule.requires.iter().map(|condition| &condition.term));
    terms.extend(rule.ensures.iter().map(|condition| &condition.term));
    terms
}

fn head_rule_extra_cell(extra: &DescriptorHeadRuleExtra) -> &DescriptorCellReference {
    match extra {
        krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, .. }
        | krs_ir::ProtocolHeadRuleExtra::UpdateMap { cell, .. }
        | krs_ir::ProtocolHeadRuleExtra::RewriteCell { cell, .. }
        | krs_ir::ProtocolHeadRuleExtra::RewriteState { cell, .. }
        | krs_ir::ProtocolHeadRuleExtra::RewriteList { cell, .. } => cell,
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "The completed rewrite, its conditions, and its binders are lowered in one ordered pass."
)]
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
    // Existentials are declared at their authored sort and are referenced
    // only by written terms and the ensures condition.
    let binding_names = seeds
        .binding_names
        .iter()
        .cloned()
        .chain(
            rule.existentials
                .iter()
                .chain(&rule.fresh)
                .map(|binder| binder.name.clone()),
        )
        .collect::<BTreeSet<_>>();
    let mut builder = StructuredTermBuilder {
        descriptor,
        catalog,
        declarations: Some(declarations),
        k_item_sort: Some(framework_k_item_sort(declarations)?),
        sort_parents,
        binding_names: &binding_names,
        pattern_key: Some(&rule.pattern_key),
        binding_sorts: rule
            .existentials
            .iter()
            .chain(&rule.fresh)
            .map(|binder| (binder.name.clone(), semantic_sort_ref(&binder.sort.sort)))
            .collect(),
        binding_constraints,
        wildcard_offset: 0,
        wildcards: Vec::new(),
        result_wildcards: false,
        locals: super::infer::LocalBinders::default(),
        head_pending: false,
        operators: super::operators::OperatorInference::default(),
        declared_binders: BTreeMap::new(),
        subject_keys: BTreeMap::new(),
        record_updates: super::record_updates::RecordUpdateState::default(),
    };
    builder.record_updates.updates = super::record_updates::RecordUpdates::scan(
        descriptor,
        &head_rule_terms(rule),
        catalog,
        Some(declarations),
    )?;
    let head_sort = rule
        .head_sort
        .as_ref()
        .map(|sort| semantic_sort_ref(&sort.sort));
    infer_head_rule(&mut builder, rule, head_sort.as_ref(), &seeds)?;

    let mut clauses = Vec::new();
    let mut selected = BTreeSet::new();
    if let (Some(head), Some(computation)) = (&rule.head, &rule.computation_cell) {
        clauses.push(ConfigurationClause::Fixed(
            lower_head_rule_computation_clause(
                &mut builder,
                rule,
                head,
                computation,
                head_sort.as_ref(),
                sort_parents,
            )?,
        ));
        selected.insert(computation.cell.clone());
    }
    for extra in &rule.extras {
        clauses.push(lower_head_rule_extra(
            &mut builder,
            extra,
            declarations,
            configuration,
            &mut selected,
        )?);
    }
    // Every cell record is checked, since one may now only read `k`; a
    // `for Sort` table's clause is a K term rule and is not. A claim is no
    // step of execution, so neither check applies to it: it may state that
    // a configuration reaches itself.
    if rule.head_sort.is_none() && rule.claim.is_none() {
        check_framed_computation_rule(descriptor, rule, &clauses, &seeds.cell_sorts)?;
    }
    super::cell_states::check_implicit_and_explicit_instances(
        descriptor,
        &rule.pattern_key,
        declarations,
        &clauses,
        &rule
            .extras
            .iter()
            .map(|extra| {
                (
                    head_rule_extra_cell(extra).clone(),
                    matches!(
                        extra,
                        krs_ir::ProtocolHeadRuleExtra::RewriteState {
                            before: krs_ir::ProtocolRuleStateTerm::Instances(_),
                            ..
                        }
                    ),
                )
            })
            .collect::<Vec<_>>(),
    )?;
    check_group_descendants(
        descriptor,
        &rule.pattern_key,
        &configuration.declaration,
        declarations,
        &selected,
    )?;
    let omitted_siblings = omitted_leaf_cells(&configuration.declaration, declarations, &selected)?;
    // A claim keeps its stream cells as ordinary List cells: `prove` performs no console I/O.
    if rule.sentence_kind != krs_ir::SentenceKind::Claim {
        let stdin = stdin_cells(&configuration.declaration, declarations)?;
        check_stdin_reads(&clauses, &stdin)?;
    }
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
    let (existentials, ensures) =
        lower_rule_existentials(&mut builder, &rule.existentials, rule.ensures.as_ref())?;
    let fresh = lower_rule_fresh(descriptor, &rule.fresh)?;
    let priority = lower_rule_priority(descriptor, rule.priority.as_ref())?;
    // An alias used only as a record update's base is matched without
    // `#as`, so it names no variable (F5).
    let mut variables = rule
        .bindings
        .iter()
        .map(|binding| &binding.name)
        .filter(|name| !builder.record_updates.updates.is_dropped(name))
        .chain(
            rule.existentials
                .iter()
                .chain(&rule.fresh)
                .map(|binder| &binder.name),
        )
        .map(|name| {
            Ok(SemanticVariable::new(
                SemanticId::new(name.clone())?,
                builder
                    .binding_sorts
                    .get(name)
                    .cloned()
                    .expect("all binding sorts were inferred"),
            ))
        })
        .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
    variables.append(&mut builder.wildcards);
    // A readable claim's declaration has the claim role (F7).
    let declaration = if rule.claim.is_some() {
        ProvenanceRole::ClaimDeclaration
    } else {
        ProvenanceRole::RuleDeclaration
    };
    let claim = rule
        .claim
        .as_ref()
        .map(|claim| lower_head_rule_claim(descriptor, claim))
        .transpose()?;
    Ok(SemanticRule::new_configuration(
        semantic_origin(descriptor, role_key(declaration, 0), "head-anchored-rule")?,
        descriptor.id().clone(),
        rule.sentence_kind,
        variables,
        body,
    )?
    .with_claim(claim)
    .with_label(lower_rule_label(descriptor, rule.label.as_ref())?)
    .with_priority(priority)?
    .with_nondet_group(lower_nondet_group(descriptor, rule.nondet.as_ref())?)
    .with_existentials(existentials)
    .with_ensures(ensures)
    .with_fresh(fresh)
    .with_evaluation(lower_rule_evaluation(descriptor, rule.evaluation.as_ref())?)
    .with_requires(requires)?)
}

/// Lowers a readable claim's modality and flags (F7). Its binders are the
/// rule's inferred variables, so it declares no universal binder.
fn lower_head_rule_claim(
    descriptor: &Descriptor,
    claim: &krs_ir::HeadRuleClaim,
) -> Result<krs_ir_levels::SemanticClaim, DescriptorLoweringError> {
    let flag = |key: Option<&ProvenanceKey>, role| {
        key.map(|key| semantic_origin(descriptor, key.clone(), role))
            .transpose()
    };
    Ok(krs_ir_levels::SemanticClaim::new(
        semantic_origin(descriptor, claim.modality_key.clone(), "claim-modality")?,
        claim.modality,
        flag(claim.circularity_key.as_ref(), "claim-circularity")?,
        Vec::new(),
    )
    .with_trusted_origin(flag(claim.trusted_key.as_ref(), "claim-trusted")?))
}

/// Lowers the `heat` or `cool` key of a transition (KF-014); the hole is
/// the rule binder of that name.
pub(super) fn lower_rule_evaluation(
    descriptor: &Descriptor,
    step: Option<&krs_ir::DescriptorEvaluationStep>,
) -> Result<Option<krs_ir_levels::SemanticEvaluationStep>, DescriptorLoweringError> {
    let Some(step) = step else {
        return Ok(None);
    };
    let result = step
        .result
        .as_ref()
        .map(|sort| {
            Ok::<_, DescriptorLoweringError>(krs_ir_levels::IrEvaluationResult::new(
                semantic_origin(descriptor, sort.key.clone(), "rule-result-sort")?,
                semantic_sort_ref(&sort.sort),
            ))
        })
        .transpose()?;
    Ok(Some(krs_ir_levels::SemanticEvaluationStep::new(
        semantic_origin(descriptor, step.key.clone(), "rule-evaluation")?,
        step.kind,
        semantic_origin(descriptor, step.hole_key.clone(), "rule-hole")?,
        SemanticId::new(step.hole.clone())?,
        result,
    )))
}

/// Lowers a transition's fresh binders (`#[k::fresh]`, KF-022).
pub(super) fn lower_rule_fresh(
    descriptor: &Descriptor,
    fresh: &[krs_ir::DescriptorClaimBinder],
) -> Result<Vec<krs_ir_levels::SemanticScopedBinder>, DescriptorLoweringError> {
    fresh
        .iter()
        .map(|binder| {
            Ok(krs_ir_levels::SemanticScopedBinder::new(
                semantic_origin(
                    descriptor,
                    binder.declaration_key.clone(),
                    "rule-fresh-binder",
                )?,
                semantic_origin(descriptor, binder.name_key.clone(), "claim-binder-name")?,
                SemanticId::new(binder.name.clone())?,
                semantic_origin(descriptor, binder.sort.key.clone(), "claim-binder-sort")?,
                semantic_sort_ref(&binder.sort.sort),
            ))
        })
        .collect()
}

/// Lowers a transition's existential binders and its ensures condition.
fn lower_rule_existentials(
    builder: &mut StructuredTermBuilder<'_>,
    existentials: &[krs_ir::DescriptorClaimBinder],
    ensures: Option<&DescriptorRuleCondition>,
) -> Result<
    (
        Vec<krs_ir_levels::SemanticScopedBinder>,
        Option<SemanticCondition>,
    ),
    DescriptorLoweringError,
> {
    let descriptor = builder.descriptor;
    let ensures = ensures
        .map(|condition| super::ml::lower_condition(builder, condition, "rule-ensures"))
        .transpose()?;
    let existentials = existentials
        .iter()
        .map(|binder| {
            Ok(krs_ir_levels::SemanticScopedBinder::new(
                semantic_origin(
                    descriptor,
                    binder.declaration_key.clone(),
                    "rule-existential-binder",
                )?,
                semantic_origin(descriptor, binder.name_key.clone(), "claim-binder-name")?,
                SemanticId::new(binder.name.clone())?,
                semantic_origin(descriptor, binder.sort.key.clone(), "claim-binder-sort")?,
                semantic_sort_ref(&binder.sort.sort),
            ))
        })
        .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
    Ok((existentials, ensures))
}

/// Rejects the readable machine rules that can never be what the author
/// meant: one that changes no cell, and one without the computation cell
/// (KF-015) that is enabled in every configuration, so execution never
/// terminates. A rule whose computation-cell pattern matches at least one
/// item, or the whole cell, constrains the state.
fn check_framed_computation_rule(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorHeadRule,
    clauses: &[ConfigurationClause<SemanticId, SemanticTerm>],
    cell_sorts: &BTreeMap<DescriptorCellIdentity, SemanticSortRef>,
) -> Result<(), DescriptorLoweringError> {
    let range = || -> Result<Option<Box<krs_ir::SourceRange>>, DescriptorLoweringError> {
        Ok(
            semantic_origin(descriptor, rule.pattern_key.clone(), "framed-rule-pattern")?
                .origin()
                .exact_authored_range()
                .map(Box::new),
        )
    };
    // An optional or collection clause (KF-023) changes something unless it
    // only reads; its parts say so.
    let unchanged = clauses
        .iter()
        .flat_map(ConfigurationClause::parts)
        .all(|part| match part {
            krs_ir::ClausePart::Matched { before, after, .. } => match after {
                krs_ir::PartPost::Preserve => true,
                krs_ir::PartPost::Local | krs_ir::PartPost::Removed => false,
                krs_ir::PartPost::Replace(term) => same_term(before, term),
            },
            krs_ir::ClausePart::Written { .. } => false,
        });
    if unchanged {
        return Err(DescriptorLoweringError::RuleChangesNoCell {
            rule: Box::new(descriptor.id().clone()),
            range: range()?,
        });
    }
    let unconstrained = rule.head.is_none()
        && rule.requires.is_none()
        && rule.extras.iter().zip(clauses).all(|(extra, clause)| {
            clause.as_fixed().is_some_and(|clause| {
                matches!(
                    clause.before().kind(),
                    krs_ir_levels::SemanticTermKind::Variable { .. }
                ) && cell_sorts
                    .get(&head_rule_extra_cell(extra).cell)
                    .is_some_and(|sort| sort == clause.before().sort())
            })
        });
    if unconstrained {
        return Err(DescriptorLoweringError::AlwaysEnabledRule {
            rule: Box::new(descriptor.id().clone()),
            range: range()?,
        });
    }
    Ok(())
}

/// Whether `result` restates the items of the k sequence `before`; the item
/// sort is an annotation of the sequence, not part of its items.
fn same_items(before: &SemanticTerm, result: &[SemanticTerm]) -> bool {
    matches!(before.kind(), krs_ir_levels::SemanticTermKind::KSequence { items, .. }
        if items.len() == result.len()
            && items.iter().zip(result).all(|(item, restated)| same_term(item, restated)))
}

/// Whether two semantic terms are the same term, ignoring their origins.
fn same_term(left: &SemanticTerm, right: &SemanticTerm) -> bool {
    use krs_ir_levels::SemanticTermKind as Kind;
    let all = |left: &[SemanticTerm], right: &[SemanticTerm]| {
        left.len() == right.len() && left.iter().zip(right).all(|(l, r)| same_term(l, r))
    };
    let all_iter = |left: Vec<&SemanticTerm>, right: Vec<&SemanticTerm>| {
        left.len() == right.len() && left.iter().zip(&right).all(|(l, r)| same_term(l, r))
    };
    if left.sort() != right.sort() {
        return false;
    }
    match (left.kind(), right.kind()) {
        (Kind::Variable { variable: l }, Kind::Variable { variable: r }) => l == r,
        (
            Kind::Application {
                application: l,
                arguments: la,
                instance: li,
                ..
            },
            Kind::Application {
                application: r,
                arguments: ra,
                instance: ri,
                ..
            },
        ) => l == r && li == ri && all(la, ra),
        (Kind::Token { value: l }, Kind::Token { value: r }) => l == r,
        (
            Kind::KSequence {
                item_sort: l,
                items: li,
            },
            Kind::KSequence {
                item_sort: r,
                items: ri,
            },
        ) => l == r && all(li, ri),
        (Kind::Map(l), Kind::Map(r)) => {
            l.operation() == r.operation()
                && all_iter(l.operands().collect(), r.operands().collect())
        }
        (Kind::List(l), Kind::List(r)) => {
            l.operation() == r.operation()
                && all_iter(l.operands().collect(), r.operands().collect())
        }
        (Kind::Set(l), Kind::Set(r)) => {
            l.operation() == r.operation()
                && all_iter(l.operands().collect(), r.operands().collect())
        }
        (
            Kind::Cell {
                cell: l,
                children: lc,
            },
            Kind::Cell {
                cell: r,
                children: rc,
            },
        ) => l == r && all(lc, rc),
        (Kind::Rewrite { from: lf, to: lt }, Kind::Rewrite { from: rf, to: rt }) => {
            same_term(lf, rf) && same_term(lt, rt)
        }
        _ => false,
    }
}

/// Checks the head rule's sentence kind and computation cell and returns its
/// fixed configuration.
fn head_rule_configuration<'a>(
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &'a DescriptorIndex<'_>,
) -> Result<&'a DescriptorFixedConfiguration, DescriptorLoweringError> {
    if !matches!(
        rule.sentence_kind,
        krs_ir::SentenceKind::Transition | krs_ir::SentenceKind::Claim
    ) {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule",
            detail: "readable head completion supports transitions and claims only".into(),
        });
    }
    let configuration = require_fixed_configuration(
        &rule.configuration,
        declarations,
        "head-anchored rule",
        "head completion requires a fixed configuration",
    )?;
    let Some(computation) = &rule.computation_cell else {
        if rule.head.is_some() {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "head-anchored rule",
                detail: "a rule that matches a computation-cell head has no computation cell"
                    .into(),
            });
        }
        return Ok(configuration);
    };
    let computation = require_cell_field(&computation.cell, declarations)?;
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
        return Err(DescriptorLoweringError::invalid_term(
            descriptor.id(),
            "head-anchored rule has duplicate bindings",
        ));
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
            if let ProtocolCellContent::Nested { declaration } = &declared.content {
                cell_sorts.insert(
                    cell.cell.clone(),
                    SemanticSortRef::Cell(declaration.declaration.clone()),
                );
            }
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
        if let krs_ir::ProtocolHeadRuleExtra::HaveMap { entries, .. } = extra
            && let Some((_, value_sort)) = map_argument_sorts.get(&cell.cell)
        {
            for entry in entries {
                binding_sorts
                    .entry(entry.value_binding.clone())
                    .or_insert_with(|| value_sort.clone());
            }
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
                    return Err(DescriptorLoweringError::invalid_term(
                        descriptor.id(),
                        format!(
                            "updated-cell binding {base_binding:?} has a refinement other than {cell_sort}"
                        ),
                    ));
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
#[expect(
    clippy::too_many_lines,
    reason = "One inference pass visits the head, every extra, and the conditions in order."
)]
fn infer_head_rule(
    builder: &mut StructuredTermBuilder<'_>,
    rule: &krs_ir::DescriptorHeadRule,
    head_sort: Option<&SemanticSortRef>,
    seeds: &HeadRuleSeeds,
) -> Result<(), DescriptorLoweringError> {
    builder.infer_sentence(|builder| {
        if let Some(head) = &rule.head {
            for item in &head.items {
                let k_item = builder.k_item_sort.clone();
                builder.infer(item, head_item_sort(item, head_sort, k_item.as_ref()), true)?;
            }
            match &head.result {
                Some(krs_ir::ProtocolHeadRuleResult::Replace(term)) => {
                    builder.infer(term, head_sort, false)?;
                }
                Some(krs_ir::ProtocolHeadRuleResult::Splice(items)) => {
                    for term in items {
                        builder.infer(term, head_sort, false)?;
                    }
                }
                Some(krs_ir::ProtocolHeadRuleResult::Erase) | None => {}
            }
        }
        for extra in &rule.extras {
            match extra {
                krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, entries } => {
                    let expected = seeds
                        .map_argument_sorts
                        .get(&cell.cell)
                        .map(|(key_sort, _)| key_sort);
                    for entry in entries {
                        builder.infer(&entry.key, expected, true)?;
                    }
                }
                krs_ir::ProtocolHeadRuleExtra::UpdateMap {
                    cell,
                    base_binding,
                    update,
                } => {
                    let expected = seeds.cell_sorts.get(&cell.cell).ok_or_else(|| {
                        DescriptorLoweringError::UnsupportedShape {
                            node: "head-anchored rule extra",
                            detail: format!(
                                "updated cell {:?} is not a fixed leaf",
                                cell.cell.field
                            ),
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
                            detail: format!(
                                "ordinary cell {:?} is not a fixed leaf",
                                cell.cell.field
                            ),
                        }
                    })?;
                    builder.infer(before, Some(expected), true)?;
                    if let Some(after) = after {
                        builder.infer(after, Some(expected), false)?;
                    }
                }
                krs_ir::ProtocolHeadRuleExtra::RewriteState {
                    cell,
                    before,
                    after,
                    ..
                } => {
                    let declarations = builder
                        .declarations
                        .expect("head rules lower with declarations");
                    let field = require_cell_field(&cell.cell, declarations)?;
                    infer_readable_state(builder, declarations, field, before, true)?;
                    if let Some(after) = after {
                        infer_readable_state(builder, declarations, field, after, false)?;
                    }
                }
                krs_ir::ProtocolHeadRuleExtra::RewriteList {
                    cell,
                    before,
                    after,
                    ..
                } => {
                    let sort = seeds.cell_sorts.get(&cell.cell);
                    let list = builder.list_cell(cell, sort)?;
                    let sort = sort.expect("a cons-list cell is a leaf of its sort");
                    builder.infer_list(before, sort, &list, true)?;
                    if let Some(after) = after {
                        builder.infer_list(after, sort, &list, false)?;
                    }
                }
            }
        }
        infer_rule_conditions(
            builder,
            rule.sentence_kind,
            rule.requires.as_ref(),
            rule.ensures.as_ref(),
        )
    })?;
    default_item_binders(builder, rule, head_sort);
    builder.resolve_binding_sorts()?;
    for binding in &rule.bindings {
        if !builder.binding_sorts.contains_key(&binding.name) {
            return Err(DescriptorLoweringError::invalid_term(
                builder.descriptor.id(),
                format!("binding {:?} has no inferred semantic sort", binding.name),
            ));
        }
    }
    Ok(())
}

/// Gives an item binder of a record that nothing else constrains its default
/// sort: it is any one item, a `KItem`.
fn default_item_binders(
    builder: &mut StructuredTermBuilder<'_>,
    rule: &krs_ir::DescriptorHeadRule,
    head_sort: Option<&SemanticSortRef>,
) {
    if head_sort.is_none()
        && let (Some(head), Some(k_item)) = (&rule.head, builder.k_item_sort.clone())
    {
        for item in &head.items {
            if let DescriptorTerm::Variable { name, .. } = item
                && !builder.binding_sorts.contains_key(name)
                && builder
                    .binding_constraints
                    .get(name)
                    .is_none_or(BTreeSet::is_empty)
            {
                builder
                    .binding_constraints
                    .entry(name.clone())
                    .or_default()
                    .insert(k_item.clone());
            }
        }
    }
}

/// The expected sort of one matched computation item: a `for Sort` table's
/// head has the table's sort; in a record, `_` is any one item, a `KItem`,
/// and every other item has the sort it states or infers.
fn head_item_sort<'a>(
    item: &DescriptorTerm,
    head_sort: Option<&'a SemanticSortRef>,
    k_item: Option<&'a SemanticSortRef>,
) -> Option<&'a SemanticSortRef> {
    match (head_sort, item) {
        (None, DescriptorTerm::Wildcard { .. }) => k_item,
        _ => head_sort,
    }
}

/// Lowers the matched items and their result into the computation-cell
/// clause: an open pattern preserves the implicit K-sequence tail, an exact
/// one names the whole cell, and a result that leaves the cell out only
/// reads it.
fn lower_head_rule_computation_clause(
    builder: &mut StructuredTermBuilder<'_>,
    rule: &krs_ir::DescriptorHeadRule,
    head: &krs_ir::ProtocolHeadRuleHead<DescriptorTerm>,
    computation: &DescriptorCellReference,
    head_sort: Option<&SemanticSortRef>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<FixedCellClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = builder.descriptor;
    let mut subject_items = Vec::with_capacity(head.items.len());
    for (index, item) in head.items.iter().enumerate() {
        // Only the first item is the sentence's head (KF-027).
        builder.head_pending = index == 0;
        let k_item = builder.k_item_sort.clone();
        subject_items.push(builder.lower(
            item,
            head_item_sort(item, head_sort, k_item.as_ref()),
            true,
        )?);
    }
    builder.head_pending = false;
    let subject_item_sort = match subject_items.as_slice() {
        [item] => item.sort().clone(),
        items => common_sequence_item_sort(descriptor, items, sort_parents, false)?,
    };
    let before_k = SemanticTerm::k_sequence(
        semantic_origin(descriptor, rule.pattern_key.clone(), "completed-k-subject")?,
        subject_item_sort,
        subject_items,
    );
    let post = match &head.result {
        None => CellPost::Preserve,
        Some(result) => {
            let result_items = match result {
                krs_ir::ProtocolHeadRuleResult::Replace(term) => {
                    vec![builder.lower(term, head_sort, false)?]
                }
                krs_ir::ProtocolHeadRuleResult::Splice(items) => items
                    .iter()
                    .map(|term| builder.lower(term, head_sort, false))
                    .collect::<Result<Vec<_>, _>>()?,
                krs_ir::ProtocolHeadRuleResult::Erase => Vec::new(),
            };
            let result_item_sort =
                common_sequence_item_sort(descriptor, &result_items, sort_parents, true)?;
            // A result that restates the matched items unchanged only reads
            // them, as a restated cell does.
            if same_items(&before_k, &result_items) {
                CellPost::Preserve
            } else {
                CellPost::Replace {
                    term: SemanticTerm::k_sequence(
                        semantic_origin(descriptor, rule.result_key.clone(), "completed-k-result")?,
                        result_item_sort,
                        result_items,
                    ),
                }
            }
        }
    };
    let frame = if head.exact {
        CellContentFrame::Exact
    } else {
        CellContentFrame::KSequenceTail {
            origin: semantic_origin(descriptor, rule.pattern_key.clone(), "implicit-k-tail")?,
            binding: None,
        }
    };
    Ok(FixedCellClause::new(
        semantic_origin(descriptor, rule.pattern_key.clone(), "completed-k-clause")?,
        semantic_cell_id(&computation.cell)?,
        before_k,
        post,
        frame,
    ))
}

/// Infers the terms of a readable optional or collection state (KF-023) at
/// its cell's sort, an instance child's at the child's sort.
fn infer_readable_state(
    builder: &mut StructuredTermBuilder<'_>,
    declarations: &DescriptorIndex<'_>,
    field: &krs_ir::DescriptorCellField,
    state: &krs_ir::ProtocolRuleStateTerm<DescriptorTerm>,
    subject: bool,
) -> Result<(), DescriptorLoweringError> {
    use krs_ir::ProtocolRuleStateTerm as State;
    let sort = match &field.content {
        ProtocolCellContent::Leaf { sort, .. } => semantic_sort_ref(&sort.sort),
        ProtocolCellContent::Nested { declaration } => {
            SemanticSortRef::Cell(declaration.declaration.clone())
        }
    };
    match state {
        State::Present { value } => {
            infer_readable_state(builder, declarations, field, value, subject)?;
        }
        State::Absent | State::Map(_) => {}
        State::Term(term) | State::Group(term) => builder.infer(term, Some(&sort), subject)?,
        State::KSequence(sequence) => {
            for item in &sequence.items {
                builder.infer(&item.value, None, subject)?;
            }
        }
        State::Instances(instances) => {
            let ProtocolCellContent::Nested { declaration } = &field.content else {
                return Ok(());
            };
            let children = &declarations.cell(&declaration.declaration)?.fields;
            for instance in instances.front.iter().chain(&instances.back) {
                for child in &instance.fields {
                    if let Some(declared) = children
                        .iter()
                        .find(|candidate| candidate.rust_field == child.field)
                    {
                        infer_readable_state(
                            builder,
                            declarations,
                            declared,
                            &child.value,
                            subject,
                        )?;
                    }
                }
            }
        }
    }
    Ok(())
}

/// [`super::cell_states::StateLowering`] for readable records: the terms
/// were inferred with the whole rule and are lowered by its builder.
struct HeadStateLowering<'a, 'b> {
    builder: &'a mut StructuredTermBuilder<'b>,
}

impl super::cell_states::StateLowering for HeadStateLowering<'_, '_> {
    fn descriptor(&self) -> &Descriptor {
        self.builder.descriptor
    }

    fn lower_state(
        &mut self,
        state: &krs_ir::ProtocolRuleStateTerm<DescriptorTerm>,
        sort: &SemanticSortRef,
        fallback_key: &ProvenanceKey,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        use krs_ir::ProtocolRuleStateTerm as State;
        let descriptor = self.builder.descriptor;
        match state {
            State::Term(term) | State::Group(term) => self.builder.lower(term, Some(sort), subject),
            State::KSequence(sequence) => {
                if *sort != SemanticSortRef::k_sequence() {
                    return Err(DescriptorLoweringError::invalid_term(
                        descriptor.id(),
                        "a `[..]` sequence occurs in a cell that is not the computation cell",
                    ));
                }
                let items = sequence
                    .items
                    .iter()
                    .map(|item| self.builder.lower(&item.value, None, subject))
                    .collect::<Result<Vec<_>, _>>()?;
                let item_sort = common_sequence_item_sort(
                    descriptor,
                    &items,
                    self.builder.sort_parents,
                    !subject,
                )?;
                let key = sequence.payload_key.as_ref().unwrap_or(fallback_key);
                Ok(SemanticTerm::k_sequence(
                    semantic_origin(descriptor, key.clone(), "readable-k-sequence")?,
                    item_sort,
                    items,
                ))
            }
            State::Map(_) | State::Present { .. } | State::Absent | State::Instances(_) => {
                Err(DescriptorLoweringError::invalid_term(
                    descriptor.id(),
                    "a readable cell state holds terms and `[..]` sequences",
                ))
            }
        }
    }

    fn same(&self, left: &SemanticTerm, right: &SemanticTerm) -> bool {
        same_term(left, right)
    }
}

/// Lowers one extra-cell read or write after checking that the cell is
/// selected once and has the leaf shape the extra requires.
fn lower_head_rule_extra(
    builder: &mut StructuredTermBuilder<'_>,
    extra: &DescriptorHeadRuleExtra,
    declarations: &DescriptorIndex<'_>,
    configuration: &DescriptorFixedConfiguration,
    selected: &mut BTreeSet<DescriptorCellIdentity>,
) -> Result<ConfigurationClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
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
    if let krs_ir::ProtocolHeadRuleExtra::RewriteState {
        cell,
        result_key,
        before,
        after,
    } = extra
    {
        let mut lowering = HeadStateLowering { builder };
        return match (before, after) {
            (krs_ir::ProtocolRuleStateTerm::Instances(before), after) => {
                let after = match after {
                    None => None,
                    Some(krs_ir::ProtocolRuleStateTerm::Instances(after)) => Some(after),
                    Some(_) => unreachable!("transport pairs instance lists"),
                };
                super::cell_states::lower_instances_clause(
                    &mut lowering,
                    declarations,
                    configuration,
                    cell,
                    before,
                    after,
                    result_key.as_ref(),
                )
            }
            (before, after) => super::cell_states::lower_optional_clause(
                &mut lowering,
                declarations,
                cell,
                before,
                after.as_ref(),
                result_key.as_ref(),
            ),
        };
    }
    lower_head_rule_fixed_extra(builder, extra, declarations).map(ConfigurationClause::Fixed)
}

fn lower_head_rule_fixed_extra(
    builder: &mut StructuredTermBuilder<'_>,
    extra: &DescriptorHeadRuleExtra,
    declarations: &DescriptorIndex<'_>,
) -> Result<FixedCellClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let cell_reference = head_rule_extra_cell(extra);
    let declared = require_cell_field(&cell_reference.cell, declarations)?;
    let ProtocolCellContent::Leaf { wrapper, sort, .. } = &declared.content else {
        let (
            ProtocolCellContent::Nested { declaration },
            krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                cell,
                result_key,
                before,
                after,
            },
        ) = (&declared.content, extra)
        else {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "head-anchored rule extra",
                detail: "a nested cell entry is a binder, `_`, or fragment!, not a map pattern"
                    .into(),
            });
        };
        return lower_head_rule_group_rewrite(
            builder,
            cell,
            result_key.as_ref(),
            before,
            after.as_ref(),
            &declaration.declaration,
        );
    };
    match extra {
        krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, entries } => {
            lower_head_rule_map_read(builder, cell, entries, *wrapper, sort)
        }
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
        } => lower_head_rule_cell_rewrite(
            builder,
            cell,
            result_key.as_ref(),
            before,
            after.as_ref(),
            *wrapper,
            sort,
        ),
        krs_ir::ProtocolHeadRuleExtra::RewriteList {
            cell,
            result_key,
            before,
            after,
        } => lower_head_rule_list_rewrite(
            builder,
            cell,
            result_key.as_ref(),
            before,
            after.as_ref(),
            sort,
        ),
        krs_ir::ProtocolHeadRuleExtra::RewriteState { .. } => {
            unreachable!("optional and collection extras are lowered by cell_states")
        }
    }
}

/// Lowers a read of entries `k1 -> v1, ..., kn -> vn` of a Map cell to the
/// preserved cell pattern `K1 |-> V1 ... Kn |-> Vn _`. Its items are distinct
/// entries of the map, so it matches only where the keys are pairwise
/// different and each is present.
fn lower_head_rule_map_read(
    builder: &mut StructuredTermBuilder<'_>,
    cell: &DescriptorCellReference,
    entries: &[krs_ir::DescriptorHeadRuleMapEntry],
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
    let mut items = Vec::with_capacity(entries.len());
    for (index, entry) in entries.iter().enumerate() {
        let key = builder.lower(&entry.key, None, true)?;
        let value_binding = &entry.value_binding;
        let value_sort = builder
            .binding_sorts
            .get(value_binding)
            .cloned()
            .ok_or_else(|| {
                DescriptorLoweringError::invalid_term(
                    descriptor.id(),
                    format!("map value binding {value_binding:?} has no inferred sort"),
                )
            })?;
        // Each value variable has its own origin; the first keeps the
        // spelling of a one-entry read.
        let role = match index {
            0 => "map-binding-value".to_owned(),
            index => format!("map-binding-value-{index}"),
        };
        let value = SemanticTerm::variable(
            semantic_origin(descriptor, cell.key.clone(), &role)?,
            value_sort,
            SemanticId::new(value_binding.clone())?,
        );
        items.push(MapEntry { key, value });
    }
    let items = MapOperands::items(items).map_err(|error| {
        DescriptorLoweringError::invalid_term(descriptor.id(), error.to_string())
    })?;
    Ok(FixedCellClause::new(
        semantic_origin(descriptor, cell.key.clone(), "completed-map-read")?,
        semantic_cell_id(&cell.cell)?,
        SemanticTerm::map(
            semantic_origin(descriptor, cell.key.clone(), "completed-map-item")?,
            items,
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

/// Lowers an ordinary leaf cell entry of a readable record. The cell is read
/// only when the result leaves it out or restates its pattern unchanged, and
/// rewritten otherwise.
fn lower_head_rule_cell_rewrite(
    builder: &mut StructuredTermBuilder<'_>,
    cell: &DescriptorCellReference,
    result_key: Option<&ProvenanceKey>,
    before: &DescriptorTerm,
    after: Option<&DescriptorTerm>,
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
    let post = lower_restated_post(builder, &before, after, &expected)?;
    let clause = FixedCellClause::new(
        semantic_origin(descriptor, cell.key.clone(), "completed-cell-rewrite")?,
        semantic_cell_id(&cell.cell)?,
        before,
        post,
        CellContentFrame::Exact,
    );
    if let Some(result_key) = result_key {
        let _ = semantic_origin(
            descriptor,
            result_key.clone(),
            "completed-cell-rewrite-result",
        )?;
    }
    Ok(clause)
}

/// Lowers a readable record's list cell (F6), `stack: [a, b, ..] => stack:
/// [c, ..]`, to the cell rewrite of the constructor terms it denotes; an
/// anonymous `..` is one rest variable on both sides.
fn lower_head_rule_list_rewrite(
    builder: &mut StructuredTermBuilder<'_>,
    cell: &DescriptorCellReference,
    result_key: Option<&ProvenanceKey>,
    before: &krs_ir::ProtocolHeadRuleList<DescriptorTerm>,
    after: Option<&krs_ir::ProtocolHeadRuleList<DescriptorTerm>>,
    sort: &DescriptorSortReference,
) -> Result<FixedCellClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = builder.descriptor;
    let expected = semantic_sort_ref(&sort.sort);
    let list = builder.list_cell(cell, Some(&expected))?;
    let before = builder.lower_list(before, &expected, &list, cell, "before", true)?;
    let post = match after {
        None => CellPost::Preserve,
        Some(after) => {
            let after = builder.lower_list(after, &expected, &list, cell, "after", false)?;
            if same_term(&before, &after) {
                CellPost::Preserve
            } else {
                CellPost::Replace { term: after }
            }
        }
    };
    if let Some(result_key) = result_key {
        let _ = semantic_origin(
            descriptor,
            result_key.clone(),
            "completed-cell-rewrite-result",
        )?;
    }
    Ok(FixedCellClause::new(
        semantic_origin(descriptor, cell.key.clone(), "completed-cell-rewrite")?,
        semantic_cell_id(&cell.cell)?,
        before,
        post,
        CellContentFrame::Exact,
    ))
}

/// The post-state of a readable record's cell entry: unchanged when the
/// result leaves the cell out or restates the same term, which denote the
/// same rule, and replaced otherwise.
fn lower_restated_post(
    builder: &mut StructuredTermBuilder<'_>,
    before: &SemanticTerm,
    after: Option<&DescriptorTerm>,
    expected: &SemanticSortRef,
) -> Result<CellPost<SemanticTerm>, DescriptorLoweringError> {
    let Some(after) = after else {
        return Ok(CellPost::Preserve);
    };
    let after = builder.lower(after, Some(expected), false)?;
    Ok(if same_term(before, &after) {
        CellPost::Preserve
    } else {
        CellPost::Replace { term: after }
    })
}

/// Lowers a whole nested (group) cell entry of a readable record, such as
/// `frame: f`, into a whole-cell clause of the group's generated cell sort
/// (KF-016). An entry left out of the result or restated unchanged is
/// preserved.
fn lower_head_rule_group_rewrite(
    builder: &mut StructuredTermBuilder<'_>,
    cell: &DescriptorCellReference,
    result_key: Option<&ProvenanceKey>,
    before: &DescriptorTerm,
    after: Option<&DescriptorTerm>,
    declaration: &StableItemId,
) -> Result<FixedCellClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = builder.descriptor;
    let expected = SemanticSortRef::Cell(declaration.clone());
    let before = builder.lower(before, Some(&expected), true)?;
    let post = lower_restated_post(builder, &before, after, &expected)?;
    let clause = FixedCellClause::whole(
        semantic_origin(descriptor, cell.key.clone(), "completed-group-rewrite")?,
        semantic_cell_id(&cell.cell)?,
        before,
        post,
    );
    if let Some(result_key) = result_key {
        let _ = semantic_origin(
            descriptor,
            result_key.clone(),
            "completed-group-rewrite-result",
        )?;
    }
    Ok(clause)
}

fn collect_declared_leaf_identities(
    declaration: &DescriptorCellDeclaration,
    declarations: &DescriptorIndex<'_>,
    selected: &BTreeSet<DescriptorCellIdentity>,
    visiting: &mut BTreeSet<StableItemId>,
    leaves: &mut Vec<DescriptorCellIdentity>,
) -> Result<(), DescriptorLoweringError> {
    for field in &declaration.fields {
        match &field.content {
            ProtocolCellContent::Leaf { .. } => leaves.push(field.reference.cell.clone()),
            ProtocolCellContent::Nested { .. } if selected.contains(&field.reference.cell) => {}
            ProtocolCellContent::Nested { declaration } => {
                if !visiting.insert(declaration.declaration.clone()) {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "nested cell declaration",
                        detail: "cyclic nominal cell declaration".into(),
                    });
                }
                let nested = declarations.cell(&declaration.declaration)?;
                collect_declared_leaf_identities(nested, declarations, selected, visiting, leaves)?;
                visiting.remove(&declaration.declaration);
            }
        }
    }
    Ok(())
}

#[expect(
    clippy::too_many_lines,
    reason = "The rewrite, its conditions, its function context, and its existential and fresh binders are lowered in one ordered pass."
)]
pub(super) fn lower_structured_rule_descriptor(
    descriptor: &Descriptor,
    rule: &StructuredRuleDescriptor,
    declarations: &DescriptorIndex<'_>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticRule, DescriptorLoweringError> {
    // A function context's bindings are visible to the result and requires
    // like the subject's (KF-025); its frames have their family's sort and its
    // term binders their declared sort.
    let context_frames = rule
        .function_context
        .iter()
        .flat_map(|context| &context.bindings)
        .filter_map(|binding| {
            let sort = match &binding.kind {
                krs_ir::ProtocolRuleBindingKind::KSequenceFrame => SemanticSortRef::k_sequence(),
                krs_ir::ProtocolRuleBindingKind::MapFrame => SemanticSortRef::map(),
                krs_ir::ProtocolRuleBindingKind::Term { .. }
                | krs_ir::ProtocolRuleBindingKind::ConfigurationFrame
                | krs_ir::ProtocolRuleBindingKind::InstancesFrame => return None,
            };
            Some((binding.name.clone(), sort))
        })
        .collect::<BTreeMap<_, _>>();
    let context_names = rule
        .function_context
        .iter()
        .flat_map(|context| &context.bindings)
        .map(|binding| &binding.name)
        .cloned()
        .collect::<Vec<_>>();
    // Existentials are declared at their authored sort and are visible only
    // to the result and the ensures condition (transport checks the scope).
    // A desugar clause's `unbound_variables` names occur only in the result,
    // and their sorts are inferred from those occurrences (KF-046).
    let unbound_names = rule
        .unbound_variables
        .iter()
        .flat_map(krs_ir::DescriptorUnboundVariables::names)
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let binding_names = rule
        .bindings
        .iter()
        .chain(&context_names)
        .chain(
            rule.existentials
                .iter()
                .chain(&rule.fresh)
                .map(|binder| &binder.name),
        )
        .chain(&unbound_names)
        .cloned()
        .collect::<BTreeSet<_>>();
    let existential_sorts = rule
        .existentials
        .iter()
        .chain(&rule.fresh)
        .map(|binder| (binder.name.clone(), semantic_sort_ref(&binder.sort.sort)))
        .chain(context_frames)
        .collect::<BTreeMap<_, _>>();
    let declared_binders = rule
        .typed_bindings
        .iter()
        .map(|binding| {
            (
                binding.name.clone(),
                (
                    semantic_sort_ref(&binding.sort.sort),
                    binding.sort.key.clone(),
                ),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut builder = StructuredTermBuilder {
        descriptor,
        catalog,
        declarations: None,
        k_item_sort: None,
        sort_parents,
        binding_names: &binding_names,
        pattern_key: Some(&rule.pattern_key),
        binding_sorts: declared_binders
            .iter()
            .map(|(name, (sort, _))| (name.clone(), sort.clone()))
            .chain(existential_sorts)
            .collect(),
        binding_constraints: BTreeMap::new(),
        wildcard_offset: 0,
        wildcards: Vec::new(),
        result_wildcards: rule
            .unbound_variables
            .as_ref()
            .is_some_and(krs_ir::DescriptorUnboundVariables::lists_wildcard),
        locals: super::infer::LocalBinders::default(),
        head_pending: false,
        operators: super::operators::OperatorInference::default(),
        declared_binders,
        subject_keys: BTreeMap::new(),
        record_updates: super::record_updates::RecordUpdateState::default(),
    };
    if rule.predicate {
        return lower_predicate_rule(descriptor, rule, builder, &binding_names_in_order(rule));
    }
    builder.record_updates.updates = super::record_updates::RecordUpdates::scan(
        descriptor,
        &std::iter::once(&rule.subject)
            .chain(&rule.result)
            .chain(rule.requires.iter().map(|condition| &condition.term))
            .chain(rule.ensures.iter().map(|condition| &condition.term))
            .collect::<Vec<_>>(),
        catalog,
        Some(declarations),
    )?;
    let subject_sort = semantic_sort_ref(&rule.subject_sort.sort);
    // A single-body rule (KF-011) has no result: its subject's rewrites
    // say what changes, and the rule's sort is the subject's.
    let result_sort = rule.result_sort.as_ref().map_or_else(
        || subject_sort.clone(),
        |sort| semantic_sort_ref(&sort.sort),
    );
    builder.infer_sentence(|builder| {
        builder.infer(&rule.subject, Some(&subject_sort), true)?;
        infer_rule_conditions(builder, rule.sentence_kind, rule.requires.as_ref(), None)?;
        if let Some(result) = &rule.result {
            builder.infer(result, Some(&result_sort), false)?;
        }
        infer_rule_conditions(builder, rule.sentence_kind, None, rule.ensures.as_ref())
    })?;
    builder.resolve_binding_sorts()?;
    // The subject's root is the sentence's head, whose parametric instance
    // its turbofish fixes (KF-027).
    builder.head_pending = true;
    let subject = builder.lower(&rule.subject, Some(&subject_sort), true)?;
    let function_context = rule
        .function_context
        .as_ref()
        .map(|context| {
            super::configuration_rules::lower_function_context(
                descriptor,
                context,
                super::configuration_rules::StateRuleTables {
                    declarations,
                    sort_parents,
                    catalog,
                },
                &builder.binding_sorts,
                builder.wildcards.len(),
            )
        })
        .transpose()?;
    let (function_context, context_wildcards) = function_context.unzip();
    let result = rule
        .result
        .as_ref()
        .map(|result| builder.lower(result, Some(&result_sort), false))
        .transpose()?;
    let requires = lower_rule_requires(&mut builder, rule.requires.as_ref())?;
    let (existentials, ensures) =
        lower_rule_existentials(&mut builder, &rule.existentials, rule.ensures.as_ref())?;
    let fresh = lower_rule_fresh(descriptor, &rule.fresh)?;
    let priority = lower_rule_priority(descriptor, rule.priority.as_ref())?;
    let simplification = lower_rule_simplification(descriptor, rule.simplification.as_ref())?;
    let restriction = super::restriction::lower_rule_restriction(descriptor, rule)?;
    let unbound_variables = lower_unbound_variables(descriptor, rule)?;
    let mut variables = Vec::new();
    for binding in rule
        .bindings
        .iter()
        .filter(|name| !builder.record_updates.updates.is_dropped(name))
        .chain(&context_names)
        .chain(
            rule.existentials
                .iter()
                .chain(&rule.fresh)
                .map(|binder| &binder.name),
        )
        .chain(&unbound_names)
    {
        let sort = builder.binding_sorts.get(binding).cloned().ok_or_else(|| {
            DescriptorLoweringError::invalid_term(
                descriptor.id(),
                format!("binding {binding:?} has no inferred subject sort"),
            )
        })?;
        variables.push(SemanticVariable::new(
            SemanticId::new(binding.clone())?,
            sort,
        ));
    }
    variables.extend(builder.wildcards);
    variables.extend(context_wildcards.into_iter().flatten());
    // A single-body rule's body is its subject, whose rewrites sit below the
    // root (KF-011); the rule body reads it through its images.
    let rewrite = match result {
        Some(result) => SemanticTerm::rewrite(
            semantic_origin_from_primary(descriptor, "rule-rewrite")?,
            result_sort,
            subject,
            result,
        )?,
        None => subject,
    };
    let rule_origin_role = match rule.sentence_kind {
        krs_ir::SentenceKind::Alias => ProvenanceRole::AliasClause,
        krs_ir::SentenceKind::Desugar => ProvenanceRole::DesugarClause,
        _ => ProvenanceRole::RuleDeclaration,
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
    .with_nondet_group(lower_nondet_group(descriptor, rule.nondet.as_ref())?)
    .with_anywhere(
        rule.anywhere
            .as_ref()
            .map(|key| semantic_origin(descriptor, key.clone(), "rule-anywhere"))
            .transpose()?,
    )
    .with_simplification(simplification)
    .with_restriction(restriction)
    .with_unbound_variables(unbound_variables)
    .with_function_context(function_context)
    .with_existentials(existentials)
    .with_ensures(ensures)
    .with_fresh(fresh)
    .with_evaluation(lower_rule_evaluation(descriptor, rule.evaluation.as_ref())?)
    .with_requires(requires)?)
}

/// The subject's bindings in first-occurrence order, which a predicate
/// simplification declares as its variables (KF-039).
fn binding_names_in_order(rule: &StructuredRuleDescriptor) -> Vec<String> {
    rule.bindings.clone()
}

/// Lowers a predicate simplification (KF-039): one matching-logic
/// predicate, rooted at `ml::equals` or `ml::ceil`, rewritten to another.
/// Its sort is the backend's to solve, so the descriptor's Bool sorts are
/// placeholders and are ignored.
fn lower_predicate_rule(
    descriptor: &Descriptor,
    rule: &StructuredRuleDescriptor,
    mut builder: StructuredTermBuilder<'_>,
    bindings: &[String],
) -> Result<SemanticRule, DescriptorLoweringError> {
    let lhs_connective = super::ml::root_connective(&rule.subject);
    if !matches!(
        lhs_connective,
        Some(krs_ir::MlConnective::Equals | krs_ir::MlConnective::Ceil)
    ) {
        let reason = match lhs_connective {
            Some(_) => {
                "the left side of a predicate simplification must be rooted at ml::equals or ml::ceil: K's simplifier rewrites an equality or a definedness condition, nothing else"
            }
            None => {
                "the left side of a predicate simplification must be a predicate rooted at ml::equals or ml::ceil; this is an object term (an object Bool enters matching logic only as `ml::equals(true, <term>)`)"
            }
        };
        return Err(builder.invalid_ml(&rule.pattern_key, reason.to_owned()));
    }
    // A single-body rule (KF-011) has no result, so it is never a
    // predicate simplification.
    let Some(result) = rule.result.as_ref() else {
        return Err(builder.invalid_ml(
            &rule.pattern_key,
            "a predicate simplification states its ml::Predicate result; a single-body rule (`k::rewrite!`) rewrites object terms".to_owned(),
        ));
    };
    builder.infer_sentence(|builder| {
        builder.infer_predicate(&rule.subject, true)?;
        infer_rule_conditions(builder, rule.sentence_kind, rule.requires.as_ref(), None)?;
        builder.infer_predicate(result, false)
    })?;
    builder.resolve_binding_sorts()?;
    let lhs = builder.lower_predicate(&rule.subject, true)?;
    let rhs = builder.lower_predicate(result, false)?;
    let requires = lower_rule_requires(&mut builder, rule.requires.as_ref())?;
    let simplification = lower_rule_simplification(descriptor, rule.simplification.as_ref())?;
    let restriction = super::restriction::lower_rule_restriction(descriptor, rule)?;
    let mut variables = Vec::new();
    for binding in bindings {
        let sort = builder.binding_sorts.get(binding).cloned().ok_or_else(|| {
            DescriptorLoweringError::invalid_term(
                descriptor.id(),
                format!("binding {binding:?} has no inferred subject sort"),
            )
        })?;
        variables.push(SemanticVariable::new(
            SemanticId::new(binding.clone())?,
            sort,
        ));
    }
    variables.extend(builder.wildcards);
    let body = krs_ir_levels::IrPredicateRewrite::new(
        semantic_origin_from_primary(descriptor, "rule-predicate-rewrite")?,
        lhs,
        rhs,
    );
    Ok(SemanticRule::new_predicate(
        semantic_origin(
            descriptor,
            role_key(ProvenanceRole::RuleDeclaration, 0),
            "rule",
        )?,
        descriptor.id().clone(),
        variables,
        body,
    )
    .with_label(lower_rule_label(descriptor, rule.label.as_ref())?)
    .with_simplification(simplification)
    .with_restriction(restriction)
    .with_requires(requires)?)
}

/// Lowers `unbound_variables = [..]` of a desugar clause (KF-046); `_` has
/// no identity and stands for every wildcard of the result.
fn lower_unbound_variables(
    descriptor: &Descriptor,
    rule: &StructuredRuleDescriptor,
) -> Result<Option<krs_ir_levels::IrUnboundVariables>, DescriptorLoweringError> {
    let Some(unbound) = &rule.unbound_variables else {
        return Ok(None);
    };
    let origin = semantic_origin(descriptor, unbound.key.clone(), "unbound-variables")?;
    let variables = unbound
        .variables
        .iter()
        .map(|variable| -> Result<_, DescriptorLoweringError> {
            let origin = semantic_origin(descriptor, variable.key.clone(), "unbound-variable")?;
            let id = if variable.is_wildcard() {
                None
            } else {
                Some(SemanticId::new(variable.name.clone())?)
            };
            Ok(krs_ir_levels::IrUnboundVariable::new(origin, id))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Some(krs_ir_levels::IrUnboundVariables::new(
        origin, variables,
    )))
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

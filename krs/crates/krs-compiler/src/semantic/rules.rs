use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    CellContentFrame, CellPost, ConfigurationClause, Descriptor, DescriptorCellDeclaration,
    DescriptorCellIdentity, DescriptorCellReference, DescriptorFixedConfiguration,
    DescriptorHeadRuleExtra, DescriptorIndex, DescriptorRuleCondition, DescriptorRuleLabel,
    DescriptorRulePriority, DescriptorSimplification, DescriptorTerm, FixedCellClause,
    FixedConfigurationRewrite, InsertedNode, ItemKind, ProtocolCellContent, ProvenanceKey,
    SemanticId, StableItemId, StructuredRuleDescriptor,
};
use krs_ir_levels::{
    SemanticCondition, SemanticNondetGroup, SemanticRule, SemanticRuleLabel, SemanticRulePriority,
    SemanticSimplification, SemanticSimplificationPriority, SemanticSortRef, SemanticTerm,
    SemanticVariable,
};
use krs_syntax::ProvenanceRole;

use super::catalog::{ProductionSignature, semantic_is_subsort, semantic_sort_ref};
use super::cell_states::{RecordOf, foreign_record, record_children};
use super::collection_types::{CollectionTyping, Root, SortType, Walker, selected_cell_type};
use super::error::DescriptorLoweringError;
use super::infer::{CollectionUse, StructuredTermBuilder, initial_binding_constraints};
use super::origin::{
    generated_semantic_id, inserted_origin, key_range, role_key, semantic_cell_id, semantic_origin,
    semantic_origin_from_primary,
};
use super::references::{declared_kind, declared_multiplicity, require_cell_field};
use krs_ir::cell_kind::{Multiplicity, Notation, Order};

/// The framework `KItem` sort, which every descriptor bundle carries (both
/// facade entry points always include the framework descriptors), so a
/// failure here is a malformed bundle, not an authoring error.
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
    let first = matches.next().ok_or_else(|| {
        DescriptorLoweringError::unsupported_shape(
            "framework sort",
            "the descriptor bundle has no framework KItem sort, which every definition has",
        )
    })?;
    if matches.next().is_some() {
        return Err(DescriptorLoweringError::unsupported_shape(
            "framework sort",
            "the descriptor bundle has more than one framework KItem sort",
        ));
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
                DescriptorLoweringError::unsupported_shape(node, detail)
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
/// A collection's instance list is such a clause too: its instances and its
/// rest are every instance, so they name each cell inside them, and a cell
/// of an instance named beside the list is named twice.
///
/// `selected` maps each cell the lowered subject names to the key of its
/// entry (a cell the result overwrites, to the result's entry). The
/// refusal is about the cell named twice, so it stands at that cell's entry,
/// as the collector's refusal of a result collection inside a named group
/// does; where the entry has no exact range, at the rule's subject.
pub(super) fn check_group_descendants(
    descriptor: &Descriptor,
    pattern_key: &ProvenanceKey,
    declaration: &DescriptorCellDeclaration,
    declarations: &DescriptorIndex<'_>,
    selected: &BTreeMap<DescriptorCellIdentity, ProvenanceKey>,
) -> Result<(), DescriptorLoweringError> {
    fn below(
        declaration: &DescriptorCellDeclaration,
        declarations: &DescriptorIndex<'_>,
        depth: usize,
        output: &mut Vec<DescriptorCellIdentity>,
    ) -> Result<(), DescriptorLoweringError> {
        if depth > 64 {
            return Err(DescriptorLoweringError::unsupported_shape(
                "nested cell declaration",
                "cyclic nominal cell declaration",
            ));
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
        selected: &BTreeMap<DescriptorCellIdentity, ProvenanceKey>,
        depth: usize,
    ) -> Result<Option<(String, DescriptorCellIdentity)>, DescriptorLoweringError> {
        if depth > 64 {
            return Ok(None);
        }
        for field in &declaration.fields {
            let ProtocolCellContent::Nested { declaration } = &field.content else {
                continue;
            };
            let nested = declarations.cell(&declaration.declaration)?;
            if selected.contains_key(&field.reference.cell) {
                let mut descendants = Vec::new();
                below(nested, declarations, 0, &mut descendants)?;
                if let Some(descendant) =
                    descendants.into_iter().find(|cell| selected.contains_key(cell))
                {
                    return Ok(Some((field.rust_field.clone(), descendant)));
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
    let at = |key: &ProvenanceKey| -> Result<_, DescriptorLoweringError> {
        Ok(
            semantic_origin(descriptor, key.clone(), "group-descendant-pattern")?
                .origin()
                .exact_authored_range()
                .map(Box::new),
        )
    };
    let range = match selected.get(&descendant).map(at).transpose()?.flatten() {
        Some(range) => Some(range),
        None => at(pattern_key)?,
    };
    Err(DescriptorLoweringError::GroupAndDescendant {
        rule: Box::new(descriptor.id().clone()),
        group,
        descendant: descendant.field,
        range,
    })
}

/// Lowers an optional rule priority; its origin label names the authored key.
///
/// `owise` lowers to an `owise` priority (value 200) on transitions and
/// equations alike, which every emitter states as `owise` itself;
/// `priority = N` lowers to a written N, never `owise`, even when N is 200.
pub(super) fn lower_rule_priority(
    descriptor: &Descriptor,
    priority: Option<&DescriptorRulePriority>,
) -> Result<Option<SemanticRulePriority>, DescriptorLoweringError> {
    priority
        .map(|priority| -> Result<_, DescriptorLoweringError> {
            let (label, owise) = match priority.key.role() {
                ProvenanceRole::RuleOwise => (SemanticRulePriority::RULE_OWISE_ORIGIN, true),
                ProvenanceRole::RulePriority => ("rule-priority", false),
                ProvenanceRole::EquationOwise => {
                    (SemanticRulePriority::EQUATION_OWISE_ORIGIN, true)
                }
                _ => ("equation-priority", false),
            };
            let origin = semantic_origin(descriptor, priority.key.clone(), label)?;
            Ok(if owise {
                SemanticRulePriority::owise(origin)
            } else {
                SemanticRulePriority::written(origin, priority.value)
            })
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
    cell_sorts: BTreeMap<DescriptorCellIdentity, SemanticSortRef>,
}

/// The element types of a readable rule's typed cells: each cell entry's
/// pattern and result at the cell's type, every other term at no type.
#[expect(
    clippy::too_many_lines,
    reason = "One root per cell entry kind of a readable record."
)]
fn head_rule_typing(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &DescriptorIndex<'_>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<CollectionTyping, DescriptorLoweringError> {
    let mut walker = Walker::new(descriptor, Some(declarations), catalog, sort_parents);
    walker.existentials(&rule.existentials, rule.claim.is_some());
    walker.checked_binders(rule.fresh.iter().map(|binder| binder.name.as_str()));
    let mut roots = Vec::new();
    let untyped = |term, subject| Root::Term {
        term,
        ty: None,
        subject,
    };
    if let Some(head) = &rule.head {
        roots.extend(head.items.iter().map(|item| untyped(item, true)));
        match &head.result {
            Some(krs_ir::ProtocolHeadRuleResult::Replace(term)) => roots.push(untyped(term, false)),
            Some(krs_ir::ProtocolHeadRuleResult::Splice(splice)) => {
                roots.extend(splice.terms().map(|item| untyped(item, false)));
            }
            Some(krs_ir::ProtocolHeadRuleResult::Erase) | None => {}
        }
    }
    for extra in &rule.extras {
        match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, entries, .. } => {
                let ty = selected_cell_type(&walker, cell, declarations)?;
                for entry in entries {
                    roots.push(Root::MapEntry {
                        key: &entry.key,
                        value: &entry.value_binding,
                        cell_key: &cell.key,
                        ty: ty.clone(),
                    });
                }
            }
            krs_ir::ProtocolHeadRuleExtra::UpdateMap {
                cell,
                base_binding,
                update,
            } => {
                let ty = selected_cell_type(&walker, cell, declarations)?;
                roots.push(Root::Binder {
                    name: base_binding,
                    ty: ty.clone(),
                });
                roots.push(Root::Term {
                    term: update,
                    ty,
                    subject: false,
                });
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                cell,
                before,
                after,
                ..
            } => {
                let ty = selected_cell_type(&walker, cell, declarations)?;
                roots.push(Root::Term {
                    term: before,
                    ty: ty.clone(),
                    subject: true,
                });
                if let Some(after) = after {
                    roots.push(Root::Term {
                        term: after,
                        ty,
                        subject: false,
                    });
                }
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteState {
                cell,
                before,
                after,
                ..
            } => {
                let field = require_cell_field(&cell.cell, declarations)?;
                walker.state_roots(before, field, true, &mut roots)?;
                if let Some(after) = after {
                    walker.state_roots(after, field, false, &mut roots)?;
                }
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteList {
                cell,
                before,
                after,
                ..
            } => {
                // A typed `List<T>` cell's elements are its elements and a
                // named rest its whole content.
                let ty = selected_cell_type(&walker, cell, declarations)?;
                for (list, subject) in
                    std::iter::once((before, true)).chain(after.iter().map(|after| (after, false)))
                {
                    for item in list.items.iter().chain(&list.back) {
                        roots.push(Root::Element {
                            term: item,
                            ty: ty.clone(),
                            subject,
                        });
                    }
                    if let krs_ir::ProtocolHeadRuleListRest::Term(rest) = &list.rest {
                        roots.push(Root::Term {
                            term: rest,
                            ty: ty.clone(),
                            subject,
                        });
                    }
                }
            }
        }
    }
    roots.extend(
        rule.requires
            .iter()
            .chain(&rule.ensures)
            .map(|condition| untyped(&condition.term, false)),
    );
    walker.run(&roots)
}

/// The element types of an equation or term rule: its function context's
/// cells at their types; its subject as a pattern, whose arguments bind at
/// their parameters' types; its result at the type of the subject's head,
/// which a typed function's equations must produce; and its other terms at
/// no type.
fn structured_rule_typing(
    descriptor: &Descriptor,
    rule: &StructuredRuleDescriptor,
    declarations: &DescriptorIndex<'_>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<CollectionTyping, DescriptorLoweringError> {
    let mut walker = Walker::new(descriptor, Some(declarations), catalog, sort_parents);
    // A term rule is a transition or an equation; claims are `cells!` rules.
    walker.existentials(&rule.existentials, false);
    walker.checked_binders(rule.fresh.iter().map(|binder| binder.name.as_str()));
    let mut roots = Vec::new();
    for cell in rule
        .function_context
        .iter()
        .flat_map(|context| &context.cells.cells)
    {
        let field = require_cell_field(&cell.field.cell, declarations)?;
        walker.state_roots(&cell.value, field, true, &mut roots)?;
    }
    let untyped = |term, subject| Root::Term {
        term,
        ty: None,
        subject,
    };
    roots.push(untyped(&rule.subject, true));
    let result_type = walker.result_type(&rule.subject);
    roots.extend(rule.result.iter().map(|result| Root::Term {
        term: result,
        ty: result_type.clone(),
        subject: false,
    }));
    roots.extend(
        rule.requires
            .iter()
            .chain(&rule.ensures)
            .map(|condition| untyped(&condition.term, false)),
    );
    walker.run(&roots)
}

/// Every term of a head rule: its matched items and result, its cells'
/// patterns and results, and its conditions.
pub(super) fn head_rule_terms(rule: &krs_ir::DescriptorHeadRule) -> Vec<&DescriptorTerm> {
    let mut terms = Vec::new();
    if let Some(head) = &rule.head {
        terms.extend(&head.items);
        match &head.result {
            Some(krs_ir::ProtocolHeadRuleResult::Replace(term)) => terms.push(term),
            Some(krs_ir::ProtocolHeadRuleResult::Splice(splice)) => terms.extend(splice.terms()),
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

/// A readable rule's front, before it means its elaborated `cells!` rule
/// ([`super::elaborate`]): the sort inference gives each binder (`where`
/// binders, existentials and fresh binders at their declared sorts), once the
/// rule passes the checks only readable notation can fail
/// ([`check_readable_notation`]).
pub(super) fn infer_head_rule_sorts(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &DescriptorIndex<'_>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<BTreeMap<String, SemanticSortRef>, DescriptorLoweringError> {
    head_rule_configuration(rule, declarations)?;
    let seeds = seed_head_rule_sorts(descriptor, rule, declarations, sort_parents)?;
    let typing = head_rule_typing(descriptor, rule, declarations, catalog, sort_parents)?;
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
    // A `where` sort is the binder's declaration, as an existential's is:
    // the binder has exactly that sort, and every occurrence must admit it.
    let mut declared_binders =
        super::infer::declared_existentials(rule.existentials.iter().chain(&rule.fresh));
    declared_binders.extend(rule.bindings.iter().filter_map(|binding| {
        binding.refinement.as_ref().map(|refinement| {
            (
                binding.name.clone(),
                (semantic_sort_ref(&refinement.sort), refinement.key.clone()),
            )
        })
    }));
    let mut builder = StructuredTermBuilder {
        descriptor,
        readable: true,
        catalog,
        declarations,
        k_item_sort: framework_k_item_sort(declarations)?,
        sort_parents,
        binding_names: &binding_names,
        pattern_key: Some(&rule.pattern_key),
        binding_sorts: declared_binders
            .iter()
            .map(|(name, (sort, _))| (name.clone(), sort.clone()))
            .collect(),
        binding_constraints,
        constraint_sites: BTreeMap::new(),
        wildcard_offset: 0,
        wildcards: Vec::new(),
        result_wildcards: false,
        locals: super::infer::LocalBinders::default(),
        in_key: false,
        // The guards of the Set collection instances the pattern looks up.
        instance_guards: Some(super::set_instances::InstanceGuards::after(0)),
        head_pending: false,
        head_place: super::infer::HeadPlace::Sentence,
        operators: super::operators::OperatorInference::default(),
        declared_binders,
        configuration_variables: BTreeMap::new(),
        subject_keys: BTreeMap::new(),
        record_updates: super::record_updates::RecordUpdateState::default(),
        collections: CollectionUse::new(&typing),
    };
    builder.record_updates.updates = super::record_updates::RecordUpdates::scan(
        descriptor,
        &head_rule_terms(rule),
        catalog,
        declarations,
        rule.sentence_kind != krs_ir::SentenceKind::Claim,
    )?;
    let head_sort = rule
        .head_sort
        .as_ref()
        .map(|sort| semantic_sort_ref(&sort.sort));
    infer_head_rule(&mut builder, rule, head_sort.as_ref(), &seeds)?;
    check_readable_notation(descriptor, rule, declarations)?;
    super::function_patterns::check_readable_patterns(descriptor, rule, catalog, declarations)?;
    Ok(builder.binding_sorts)
}

/// The checks a readable rule can fail and its `cells!` rule cannot state, made before it is
/// elaborated: an extra names the computation cell or another extra's cell (a `cells!` rule
/// writes each cell once, as a field of its cells), map notation reads a cell that holds no Map,
/// an update writes a cell that holds no Map or List, and a plain rewrite names the
/// computation cell (whose readable form is the head). Each error that names no narrower node
/// is located at the extra's cell entry.
fn check_readable_notation(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    let mut selected = BTreeSet::new();
    if let (Some(_), Some(computation)) = (&rule.head, &rule.computation_cell) {
        selected.insert(computation.cell.clone());
    }
    for extra in &rule.extras {
        check_readable_extra(descriptor, extra, declarations, &mut selected).map_err(|error| {
            error.within(
                descriptor.id(),
                key_range(descriptor, &head_rule_extra_cell(extra).key).as_ref(),
            )
        })?;
    }
    Ok(())
}

fn check_readable_extra(
    descriptor: &Descriptor,
    extra: &DescriptorHeadRuleExtra,
    declarations: &DescriptorIndex<'_>,
    selected: &mut BTreeSet<DescriptorCellIdentity>,
) -> Result<(), DescriptorLoweringError> {
    let cell = head_rule_extra_cell(extra);
    if !selected.insert(cell.cell.clone()) {
        return Err(DescriptorLoweringError::unsupported_shape(
            "head-anchored rule",
            format!("cell {:?} is mentioned more than once", cell.cell.field),
        ));
    }
    if matches!(extra, krs_ir::ProtocolHeadRuleExtra::RewriteState { .. }) {
        return Ok(());
    }
    let declared = require_cell_field(&cell.cell, declarations)?;
    let kind = declared_kind(declared, declarations);
    if kind.group().is_some() || matches!(declared.content, ProtocolCellContent::Nested { .. }) {
        return match (&declared.content, extra) {
            (
                ProtocolCellContent::Nested { .. },
                krs_ir::ProtocolHeadRuleExtra::RewriteCell { .. },
            ) => Ok(()),
            _ => Err(DescriptorLoweringError::invalid_term(
                descriptor.id(),
                format!(
                    "map notation `{{ k -> v, .. }}` reads a Map cell, and `{}` is a nested cell group",
                    cell.cell.field
                ),
            )),
        };
    }
    match extra {
        krs_ir::ProtocolHeadRuleExtra::HaveMap { .. } if kind.leaf() != Some(Notation::Map) => {
            Err(DescriptorLoweringError::invalid_term(
                descriptor.id(),
                format!(
                    "map notation `{{ k -> v, .. }}` reads a Map cell, and `{}` does not hold a Map",
                    cell.cell.field
                ),
            ))
        }
        krs_ir::ProtocolHeadRuleExtra::UpdateMap { .. }
            if !matches!(kind.leaf(), Some(Notation::Map | Notation::List)) =>
        {
            Err(DescriptorLoweringError::unsupported_shape(
                "head-anchored rule extra",
                format!(
                    "updated cell {:?} is not a Map or List cell",
                    cell.cell.field
                ),
            ))
        }
        krs_ir::ProtocolHeadRuleExtra::RewriteCell { .. } => {
            if let Some(wrapper @ krs_ir::CellWrapper::KCell) =
                super::cell_states::content_wrapper(&kind)
            {
                return Err(DescriptorLoweringError::cell_wrapper(
                    Some(&cell.cell.field),
                    Some(wrapper),
                    None,
                ));
            }
            Ok(())
        }
        _ => Ok(()),
    }
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

/// Rejects a step of execution that can never be what its author meant, on
/// either route. One that changes no cell (KF-015) is legal K, but once
/// enabled it applies again to the configuration it leaves, forever, and
/// changes nothing. One that is `unconstrained` (the caller's judgement:
/// every cell pattern matches every content and nothing guards it) is
/// enabled in every configuration, so execution never terminates. A claim is
/// no step, and its callers do not ask: it may state that a configuration
/// reaches itself.
pub(super) fn check_step_effect(
    descriptor: &Descriptor,
    pattern_key: &ProvenanceKey,
    clauses: &[ConfigurationClause<SemanticId, SemanticTerm>],
    unconstrained: bool,
) -> Result<(), DescriptorLoweringError> {
    if changes_no_cell(clauses) {
        return Err(DescriptorLoweringError::RuleChangesNoCell {
            rule: Box::new(descriptor.id().clone()),
            range: step_range(descriptor, pattern_key)?,
        });
    }
    if unconstrained {
        return Err(DescriptorLoweringError::AlwaysEnabledRule {
            rule: Box::new(descriptor.id().clone()),
            range: step_range(descriptor, pattern_key)?,
        });
    }
    Ok(())
}

/// The exact authored range of a step's subject, where a step's judgement
/// ([`check_step_effect`]) points.
fn step_range(
    descriptor: &Descriptor,
    pattern_key: &ProvenanceKey,
) -> Result<Option<Box<krs_ir::SourceRange>>, DescriptorLoweringError> {
    Ok(
        semantic_origin(descriptor, pattern_key.clone(), "framed-rule-pattern")?
            .origin()
            .exact_authored_range()
            .map(Box::new),
    )
}

/// Whether `clause` matches its cell's every content: a fixed cell whose
/// pattern is a variable of the cell's `declared` sort.
pub(super) fn matches_every_content(
    clause: &ConfigurationClause<SemanticId, SemanticTerm>,
    declared: Option<&SemanticSortRef>,
) -> bool {
    clause.as_fixed().is_some_and(|clause| {
        matches!(
            clause.before().kind(),
            krs_ir_levels::SemanticTermKind::Variable { .. }
        ) && declared.is_some_and(|sort| sort == clause.before().sort())
    })
}

/// Whether no clause of a rule changes its cell: each only reads it or
/// restates it. An optional cell (KF-023) changes when it goes from present
/// to absent or from absent to present, and a collection clause whenever it
/// removes or creates an instance, whether or not it mentions the instance's
/// children (`<obj> _ </obj> => .Bag` mentions none); a kept instance changes
/// only where one of its children does.
pub(super) fn changes_no_cell(clauses: &[ConfigurationClause<SemanticId, SemanticTerm>]) -> bool {
    use krs_ir::{InstanceClause, Presence};
    let fixed = |clause: &FixedCellClause<SemanticId, SemanticTerm>| match clause.after() {
        CellPost::Preserve => true,
        CellPost::Local => false,
        CellPost::Replace { term } => same_term(clause.before(), term),
    };
    clauses.iter().all(|clause| match clause {
        ConfigurationClause::Fixed(clause) => fixed(clause),
        ConfigurationClause::Optional(clause) => match (clause.before(), clause.after()) {
            (_, None) | (Presence::Absent, Some(Presence::Absent)) => true,
            (Presence::Present { term: before }, Some(Presence::Present { term })) => {
                same_term(before, term)
            }
            (Presence::Present { .. }, Some(Presence::Absent))
            | (Presence::Absent, Some(Presence::Present { .. })) => false,
        },
        ConfigurationClause::Instances(clause) => {
            clause.instances().all(|instance| match instance {
                InstanceClause::Kept { children, .. } => children.iter().all(fixed),
                InstanceClause::Removed { .. } | InstanceClause::Created { .. } => false,
            })
        }
    })
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
        return Err(DescriptorLoweringError::unsupported_shape(
            "head-anchored rule",
            "readable head completion supports transitions and claims only",
        ));
    }
    let configuration = require_fixed_configuration(
        &rule.configuration,
        declarations,
        "head-anchored rule",
        "head completion requires a fixed configuration",
    )?;
    let Some(computation) = &rule.computation_cell else {
        if rule.head.is_some() {
            return Err(DescriptorLoweringError::unsupported_shape(
                "head-anchored rule",
                "a rule that matches a computation-cell head has no computation cell",
            ));
        }
        return Ok(configuration);
    };
    let computation = require_cell_field(&computation.cell, declarations)?;
    // A `KCell` holds the builtin `KSequence` (descriptor validation), so the computation
    // content is `KCell<KSequence>`.
    let kind = declared_kind(computation, declarations);
    if kind.group().is_some() {
        return Err(DescriptorLoweringError::unsupported_shape(
            "head-anchored rule",
            "resolved computation cell is not a fixed leaf",
        ));
    }
    if !kind.is_computation() {
        return Err(DescriptorLoweringError::unsupported_shape(
            "head-anchored rule",
            "resolved computation cell is not KCell<KSequence>",
        ));
    }
    Ok(configuration)
}

fn seed_head_rule_sorts(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &DescriptorIndex<'_>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
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
    // A `where` sort is a declaration, not a seed: it is checked against
    // each occurrence ([`lower_head_rule_descriptor`]). These seeds are the
    // sorts an undeclared binder takes from the cells it is read from.
    let refinements = rule
        .bindings
        .iter()
        .filter_map(|binding| {
            binding
                .refinement
                .as_ref()
                .map(|refinement| (binding.name.clone(), refinement))
        })
        .collect::<BTreeMap<_, _>>();
    let mut binding_sorts = BTreeMap::new();
    let mut cell_sorts = BTreeMap::new();
    for extra in &rule.extras {
        let cell = head_rule_extra_cell(extra);
        let declared = require_cell_field(&cell.cell, declarations)?;
        let ProtocolCellContent::Leaf { sort, .. } = &declared.content else {
            if let ProtocolCellContent::Nested { declaration } = &declared.content {
                cell_sorts.insert(
                    cell.cell.clone(),
                    SemanticSortRef::Cell(declaration.declaration.clone()),
                );
            }
            continue;
        };
        cell_sorts.insert(cell.cell.clone(), semantic_sort_ref(&sort.sort));
        // A value read from a typed map is one of its values: its binder
        // has the value sort, unless its declaration is a subsort of it,
        // which the read then tests for.
        if let krs_ir::ProtocolHeadRuleExtra::HaveMap { entries, .. } = extra
            && let Some(declared_type) = SortType::of_cell(declared, descriptor)?
            && let Some(value) = declared_type.map_value()
        {
            for entry in entries {
                match refinements.get(&entry.value_binding) {
                    Some(refinement) => {
                        let sort = semantic_sort_ref(&refinement.sort);
                        if !semantic_is_subsort(&sort, value.sort(), sort_parents) {
                            return Err(super::collection_types::map_value_refinement(
                                descriptor,
                                &declared.rust_field,
                                &declared_type,
                                &entry.value_binding,
                                &sort,
                                &refinement.key,
                                sort_parents,
                            ));
                        }
                    }
                    None => {
                        binding_sorts.insert(entry.value_binding.clone(), value.sort().clone());
                    }
                }
            }
        }
        if let krs_ir::ProtocolHeadRuleExtra::UpdateMap { base_binding, .. } = extra {
            let cell_sort = cell_sorts.get(&cell.cell).ok_or_else(|| {
                DescriptorLoweringError::unsupported_shape(
                    "head-anchored rule extra",
                    format!("updated cell {:?} is not a fixed leaf", cell.cell.field),
                )
            })?;
            let refinement = refinements
                .get(base_binding)
                .map(|refinement| semantic_sort_ref(&refinement.sort));
            match refinement
                .as_ref()
                .or_else(|| binding_sorts.get(base_binding))
            {
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
                builder.infer(item, head_item_sort(item, head_sort, &k_item), true)?;
            }
            match &head.result {
                Some(krs_ir::ProtocolHeadRuleResult::Replace(term)) => {
                    builder.infer(term, head_sort, false)?;
                }
                Some(krs_ir::ProtocolHeadRuleResult::Splice(splice)) => {
                    for term in splice.terms() {
                        builder.infer(term, head_sort, false)?;
                    }
                }
                Some(krs_ir::ProtocolHeadRuleResult::Erase) | None => {}
            }
        }
        for extra in &rule.extras {
            match extra {
                krs_ir::ProtocolHeadRuleExtra::HaveMap { entries, .. } => {
                    for entry in entries {
                        let expected = builder.collections.element_sort(&entry.key);
                        builder.infer_key(&entry.key, expected.as_ref())?;
                        // A value read from a bare map is any `KItem`; a typed
                        // map's value binder is seeded with its value sort.
                        if !builder.binding_sorts.contains_key(&entry.value_binding)
                            && let Some(k_item) = builder.collections.untyped_element()
                        {
                            builder
                                .binding_constraints
                                .entry(entry.value_binding.clone())
                                .or_default()
                                .insert(k_item.clone());
                        }
                    }
                }
                krs_ir::ProtocolHeadRuleExtra::UpdateMap {
                    cell,
                    base_binding,
                    update,
                } => {
                    let expected = seeds.cell_sorts.get(&cell.cell).ok_or_else(|| {
                        DescriptorLoweringError::unsupported_shape(
                            "head-anchored rule extra",
                            format!("updated cell {:?} is not a fixed leaf", cell.cell.field),
                        )
                    })?;
                    builder.infer_collection_update(update, base_binding, expected)?;
                }
                krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                    cell,
                    before,
                    after,
                    ..
                } => {
                    let expected = seeds.cell_sorts.get(&cell.cell).ok_or_else(|| {
                        DescriptorLoweringError::unsupported_shape(
                            "head-anchored rule extra",
                            format!("ordinary cell {:?} is not a fixed leaf", cell.cell.field),
                        )
                    })?;
                    // A group record whose computation child is written in brackets is the
                    // record of its children's entries, that child's its K sequence (R4), as
                    // its elaboration reads it; so is a result's group record whose `..` leaves
                    // a child unnamed, whose other children keep their content; any other value
                    // is a term of the cell's sort.
                    let declarations = builder.declarations;
                    let field = require_cell_field(&cell.cell, declarations)?;
                    let sides = std::iter::once((before, true))
                        .chain(after.iter().map(|after| (after, false)));
                    for (term, subject) in sides {
                        if let Some(record) =
                            super::group_records::bracketed_record(term, field, declarations)
                        {
                            infer_readable_state(
                                builder,
                                declarations,
                                field,
                                &krs_ir::ProtocolRuleStateTerm::Record(record),
                                subject,
                            )?;
                        } else if let Some(refusal) =
                            super::cell_states::foreign_group_term(builder.descriptor, field, term)
                        {
                            return Err(refusal);
                        } else if let Some(record) = (!subject)
                            .then(|| super::group_records::kept_record(term, field, declarations))
                            .flatten()
                        {
                            infer_readable_state(
                                builder,
                                declarations,
                                field,
                                &krs_ir::ProtocolRuleStateTerm::Record(record),
                                false,
                            )?;
                        } else {
                            builder.infer(term, Some(expected), subject)?;
                        }
                    }
                }
                krs_ir::ProtocolHeadRuleExtra::RewriteState {
                    cell,
                    before,
                    after,
                    ..
                } => {
                    let declarations = builder.declarations;
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
                    let sort = sort.expect("a list cell is a leaf of its sort");
                    builder.infer_list(before, sort, &list, cell, true)?;
                    if let Some(after) = after {
                        builder.infer_list(after, sort, &list, cell, false)?;
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
/// sort: it is any one item, a `KItem`. The items of a group record's computation
/// child written in brackets are items alike, and so are those of an instance's
/// computation child ([`instance_computation_items`]).
fn default_item_binders(
    builder: &mut StructuredTermBuilder<'_>,
    rule: &krs_ir::DescriptorHeadRule,
    head_sort: Option<&SemanticSortRef>,
) {
    let k_item = builder.k_item_sort.clone();
    let head = rule.head.as_ref().filter(|_| head_sort.is_none());
    // A group record's computation child written in brackets holds items as the head does.
    let declarations = builder.declarations;
    let children = rule
        .extras
        .iter()
        .filter_map(|extra| match extra {
            krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                cell,
                before,
                after,
                ..
            } => Some((cell, before, after)),
            _ => None,
        })
        .flat_map(|(cell, before, after)| {
            let field = require_cell_field(&cell.cell, declarations).ok();
            std::iter::once(before)
                .chain(after)
                .filter_map(move |term| {
                    super::group_records::bracketed_record(term, field?, declarations)
                })
        })
        .flat_map(|record| super::group_records::computation_items(&record))
        .chain(rule.extras.iter().flat_map(|extra| {
            let krs_ir::ProtocolHeadRuleExtra::RewriteState {
                cell,
                before,
                after,
                ..
            } = extra
            else {
                return Vec::new();
            };
            let Ok(field) = require_cell_field(&cell.cell, declarations) else {
                return Vec::new();
            };
            std::iter::once(before)
                .chain(after)
                .flat_map(|state| instance_computation_items(state, field, declarations))
                .collect()
        }))
        .collect::<Vec<_>>();
    {
        for item in head
            .into_iter()
            .flat_map(|head| &head.items)
            .chain(&children)
        {
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

/// The items of the computation children that the instances of `state`, an entry of the
/// collection `field`, write in brackets, in authored order. An instance's computation child is a
/// computation, as the computation cell is, so each item is one item of it; brackets on a list
/// child are that list's elements instead, which its leaf's sort types
/// ([`infer_readable_state`]).
fn instance_computation_items(
    state: &krs_ir::ProtocolRuleStateTerm<DescriptorTerm>,
    field: &krs_ir::DescriptorCellField,
    declarations: &DescriptorIndex<'_>,
) -> Vec<DescriptorTerm> {
    use krs_ir::ProtocolRuleStateTerm as State;
    match state {
        State::Present { value } => instance_computation_items(value, field, declarations),
        State::Instances(instances) => {
            let ProtocolCellContent::Nested { declaration } = &field.content else {
                return Vec::new();
            };
            let Ok(group) = declarations.cell(&declaration.declaration) else {
                return Vec::new();
            };
            instances
                .front
                .iter()
                .chain(&instances.back)
                .filter_map(|instance| {
                    super::cell_states::named_children(&group.fields, &instance.fields).ok()
                })
                .flatten()
                .flat_map(|(child, declared)| {
                    let mut value = &child.value;
                    while let State::Present { value: inner } = value {
                        value = inner;
                    }
                    let computation = matches!(
                        declared.content,
                        ProtocolCellContent::Leaf {
                            wrapper: krs_ir::CellWrapper::KCell,
                            ..
                        }
                    );
                    match (value, computation) {
                        (State::KSequence(sequence), true) => sequence
                            .items
                            .iter()
                            .map(|item| item.value.clone())
                            .collect(),
                        (State::Instances(_), _) => {
                            instance_computation_items(value, declared, declarations)
                        }
                        _ => super::group_records::computation_sequence(value, declared)
                            .map(|sequence| {
                                sequence.items.into_iter().map(|item| item.value).collect()
                            })
                            .unwrap_or_default(),
                    }
                })
                .collect()
        }
        _ => Vec::new(),
    }
}

/// The expected sort of one matched computation item: a `for Sort` table's
/// head has the table's sort; in a record, `_` is any one item, a `KItem`,
/// and every other item has the sort it states or infers.
fn head_item_sort<'a>(
    item: &DescriptorTerm,
    head_sort: Option<&'a SemanticSortRef>,
    k_item: &'a SemanticSortRef,
) -> Option<&'a SemanticSortRef> {
    match (head_sort, item) {
        (None, DescriptorTerm::Wildcard { .. }) => Some(k_item),
        _ => head_sort,
    }
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
        State::Absent => {}
        // A map cell's entries, as a `cells!` map's: a subject's keys are looked up.
        State::Map(map) => match &map.body {
            krs_ir::ProtocolRuleMapBody::Empty { .. } => {}
            krs_ir::ProtocolRuleMapBody::Items { items, .. } => {
                for item in items {
                    let key_sort = builder.collections.element_sort(&item.key);
                    if subject {
                        builder.infer_key(&item.key, key_sort.as_ref())?;
                    } else {
                        builder.infer(&item.key, key_sort.as_ref(), false)?;
                    }
                    let value_sort = builder.collections.element_sort(&item.value);
                    builder.infer(&item.value, value_sort.as_ref(), subject)?;
                }
            }
            krs_ir::ProtocolRuleMapBody::Update {
                base, key, value, ..
            } => {
                builder.infer(base, Some(&SemanticSortRef::map()), subject)?;
                for term in [key, value] {
                    let element_sort = builder.collections.element_sort(term);
                    builder.infer(term, element_sort.as_ref(), subject)?;
                }
            }
        },
        State::Term(term) | State::Group(term) => builder.infer(term, Some(&sort), subject)?,
        // Brackets in a list leaf, an instance's child among them, hold the list's elements, so
        // each item is one element of the leaf's sort (`al: [y, ..]` binds `y` to an element of
        // `al`); in the computation cell they are its items.
        State::KSequence(sequence) => {
            let list = (sort != SemanticSortRef::k_sequence())
                .then(|| builder.cons_list_of(&sort))
                .flatten();
            for item in &sequence.items {
                let expected = list
                    .as_ref()
                    .and_then(|list| builder.list_element_expected(&item.value, list));
                builder.infer(&item.value, expected.as_ref(), subject)?;
            }
        }
        State::Record(record) => {
            infer_readable_record(builder, declarations, field, record, subject)?;
        }
        State::Instances(instances) => {
            let ProtocolCellContent::Nested { declaration } = &field.content else {
                return Ok(());
            };
            // A pattern looks a Set collection up by an instance, read as a key is.
            let looked_up = subject
                && declared_multiplicity(field, declarations) == Multiplicity::Many(Order::Set)
                && super::function_patterns::matches_evaluated_sentence(
                    builder.descriptor.payload(),
                );
            let group = &declaration.declaration;
            let children = &declarations.cell(group)?.fields;
            let mut records = instances.front.iter().chain(&instances.back);
            instance_heads(builder, field, group, records.clone())?;
            let enclosing = builder.in_key;
            builder.in_key |= looked_up;
            let inferred = records.try_for_each(|instance| {
                record_children(
                    builder.descriptor,
                    RecordOf::Instance,
                    group.item_name(),
                    children,
                    &instance.fields,
                    declarations,
                )?
                .into_iter()
                .try_for_each(|(child, declared)| {
                    // Brackets the macros read as list notation are a computation child's items.
                    match super::group_records::computation_sequence(&child.value, declared) {
                        Some(sequence) => infer_readable_state(
                            builder,
                            declarations,
                            declared,
                            &krs_ir::ProtocolRuleStateTerm::KSequence(sequence),
                            subject,
                        ),
                        None => infer_readable_state(
                            builder,
                            declarations,
                            declared,
                            &child.value,
                            subject,
                        ),
                    }
                })
            });
            builder.in_key = enclosing;
            inferred?;
        }
    }
    Ok(())
}

/// Infers a readable group record written as the entry of the cell `field`.
///
/// A group record's children, each at its own cell's sort, as an instance's are; its
/// head names the record and is no term the rule matches or writes. A record that is no
/// record of the cell's group is refused here, before its names are given sorts, so the
/// refusal names the record rather than a name only its field binds; so is a record on a leaf,
/// which holds no group ([`super::cell_states::record_on_leaf`]).
fn infer_readable_record(
    builder: &mut StructuredTermBuilder<'_>,
    declarations: &DescriptorIndex<'_>,
    field: &krs_ir::DescriptorCellField,
    record: &krs_ir::ProtocolRuleRecord<DescriptorTerm>,
    subject: bool,
) -> Result<(), DescriptorLoweringError> {
    let ProtocolCellContent::Nested { declaration } = &field.content else {
        return Err(super::cell_states::record_on_leaf(
            builder.descriptor,
            field,
            &record.key,
        ));
    };
    let group = &declaration.declaration;
    if let Some(refusal) = foreign_record(
        builder.descriptor,
        RecordOf::Group,
        &field.rust_field,
        &record.head,
        &record.key,
        group,
    ) {
        return Err(refusal);
    }
    let children = &declarations.cell(group)?.fields;
    for (child, declared) in record_children(
        builder.descriptor,
        RecordOf::Group,
        group.item_name(),
        children,
        &record.fields,
        declarations,
    )? {
        infer_readable_state(builder, declarations, declared, &child.value, subject)?;
    }
    Ok(())
}

/// Refuses an instance record whose head names another struct than `group`, the instances of
/// the collection cell `field` ([`foreign_record`]).
fn instance_heads<'r>(
    builder: &StructuredTermBuilder<'_>,
    field: &krs_ir::DescriptorCellField,
    group: &StableItemId,
    records: impl Iterator<Item = &'r krs_ir::ProtocolRuleInstance<DescriptorTerm>>,
) -> Result<(), DescriptorLoweringError> {
    for instance in records {
        if let Some(head) = &instance.head
            && let Some(refusal) = foreign_record(
                builder.descriptor,
                RecordOf::Instance,
                &field.rust_field,
                head,
                &instance.key,
                group,
            )
        {
            return Err(refusal);
        }
    }
    Ok(())
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
                    return Err(DescriptorLoweringError::unsupported_shape(
                        "nested cell declaration",
                        "cyclic nominal cell declaration",
                    ));
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
        .chain(super::infer::declared_existentials(
            rule.existentials.iter().chain(&rule.fresh),
        ))
        .collect::<BTreeMap<_, _>>();
    // A function context matches cells, and a subject matches arguments;
    // their binders have the cells' and parameters' element types.
    let typing = structured_rule_typing(descriptor, rule, declarations, catalog, sort_parents)?;
    let mut builder = StructuredTermBuilder {
        descriptor,
        readable: false,
        catalog,
        declarations,
        k_item_sort: framework_k_item_sort(declarations)?,
        sort_parents,
        binding_names: &binding_names,
        pattern_key: Some(&rule.pattern_key),
        binding_sorts: declared_binders
            .iter()
            .map(|(name, (sort, _))| (name.clone(), sort.clone()))
            .chain(existential_sorts)
            .collect(),
        binding_constraints: BTreeMap::new(),
        constraint_sites: BTreeMap::new(),
        wildcard_offset: 0,
        wildcards: Vec::new(),
        result_wildcards: rule
            .unbound_variables
            .as_ref()
            .is_some_and(krs_ir::DescriptorUnboundVariables::lists_wildcard),
        locals: super::infer::LocalBinders::default(),
        in_key: false,
        // The guards of the set elements a pattern over evaluated terms looks up
        // ([`super::set_instances`]), which its condition holds.
        instance_guards: super::function_patterns::matches_evaluated_sentence(descriptor.payload())
            .then(|| super::set_instances::InstanceGuards::after(0)),
        head_pending: false,
        head_place: super::infer::HeadPlace::Sentence,
        operators: super::operators::OperatorInference::default(),
        declared_binders,
        configuration_variables: BTreeMap::new(),
        subject_keys: BTreeMap::new(),
        record_updates: super::record_updates::RecordUpdateState::default(),
        collections: CollectionUse::new(&typing),
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
        declarations,
        rule.sentence_kind != krs_ir::SentenceKind::Claim,
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
    let subject_guards = builder
        .instance_guards
        .take()
        .map(super::set_instances::InstanceGuards::into_guards)
        .unwrap_or_default();
    let guard_variables = subject_guards
        .iter()
        .filter_map(super::set_instances::Guard::variable)
        .collect::<Vec<_>>();
    let mut subject_guards = super::set_instances::SentenceGuards::from(subject_guards);
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
                &typing,
                &builder.binding_sorts,
                builder.wildcards.len(),
                std::mem::take(&mut subject_guards),
            )
        })
        .transpose()?;
    let (function_context, context_wildcards, guards) = match function_context {
        Some((context, wildcards, guards)) => (Some(context), wildcards, guards),
        None => (None, Vec::new(), subject_guards),
    };
    let result = rule
        .result
        .as_ref()
        .map(|result| builder.lower(result, Some(&result_sort), false))
        .transpose()?;
    let requires = lower_rule_requires(&mut builder, rule.requires.as_ref())?;
    // The subject's guarded set elements and the function context's guarded keys hold only where
    // the sentence's condition holds their guards.
    let requires = super::set_instances::guarded_requires(descriptor, requires, guards)?;
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
    variables.extend(guard_variables);
    variables.extend(context_wildcards);
    let rule_origin_role = match rule.sentence_kind {
        krs_ir::SentenceKind::Alias => ProvenanceRole::AliasClause,
        krs_ir::SentenceKind::Desugar => ProvenanceRole::DesugarClause,
        _ => ProvenanceRole::RuleDeclaration,
    };
    let origin = semantic_origin(descriptor, role_key(rule_origin_role, 0), "rule")?;
    let transition = rule.sentence_kind == krs_ir::SentenceKind::Transition;
    // A rule's subject is the computation's first item. A `#[k::rule]` fn
    // whose result is a cell's value replaces that item by the cell; one
    // rooted at a collection's construction (`set::item(x)`, `map![]`,
    // `list::item(x)`) matches the item where it is the collection the
    // construction denotes (decision NT-11-2). Both are stated over the
    // computation cell, where the item is the cell's first and the
    // construction a pattern below the cell, as in a `for KItem` clause.
    let cell_result = transition
        && function_context.is_none()
        && result.as_ref().is_some_and(is_cell_valued)
        && !is_cell_valued(&subject);
    let collection_root = transition
        && rule.anywhere.is_none()
        && rule.evaluation.is_none()
        && restriction.is_none()
        && super::function_patterns::collection_rooted(&rule.subject, catalog);
    // A transition whose result is its subject rewrites the item to itself:
    // the step from a configuration to itself that `check_step_effect`
    // refuses on the cell routes, so it is refused here too.
    if transition
        && result
            .as_ref()
            .is_some_and(|result| same_term(&subject, result))
    {
        return Err(DescriptorLoweringError::RuleChangesNoCell {
            rule: Box::new(descriptor.id().clone()),
            range: step_range(descriptor, &rule.pattern_key)?,
        });
    }
    let lowered = if cell_result || collection_root {
        SemanticRule::new_configuration(
            origin,
            descriptor.id().clone(),
            rule.sentence_kind,
            variables,
            computation_rewrite(
                descriptor,
                rule,
                declarations,
                (sort_parents, catalog),
                subject,
                result,
            )?,
        )?
    } else {
        // A single-body rule's body is its subject, whose rewrites sit below
        // the root (KF-011); the rule body reads it through its images.
        let rewrite = match result {
            Some(result) => SemanticTerm::rewrite(
                semantic_origin_from_primary(descriptor, "rule-rewrite")?,
                result_sort,
                subject,
                result,
            )?,
            None => subject,
        };
        SemanticRule::new(
            origin,
            descriptor.id().clone(),
            rule.sentence_kind,
            variables,
            rewrite,
        )?
    };
    Ok(lowered
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

/// Whether `term`'s value is a cell: a cell term, or a `let` block whose body's value is one.
fn is_cell_valued(term: &SemanticTerm) -> bool {
    match term.kind() {
        krs_ir_levels::IrTermKind::Cell { .. } => true,
        krs_ir_levels::IrTermKind::Let { body, .. } => is_cell_valued(body),
        _ => false,
    }
}

/// A `#[k::rule]` fn's rewrite of the computation's first item, `subject`, into `result` (in
/// place, for a single-body rule's subject, which holds its rewrites), as the computation cell's
/// clause of the definition's one fixed configuration, its other cells left as they are:
/// `<k> SUBJECT => RESULT ... </k>`.
///
/// The fn replaces the item its subject matches by its result. Where the result is a cell's
/// value, a cell is a value a computation holds, of its cell sort below `KItem`, but K completes
/// a bare rewrite to the configuration by the roots of its sides, where a cell at a side's root
/// is the configuration's cell. Where the subject is a collection's construction, a bare rule
/// would match a collection at a rule's root, where no rewrite step meets a function's
/// application. Inside the computation cell both sides are the computation's items, as a
/// `for Stmt` clause's are.
fn computation_rewrite(
    descriptor: &Descriptor,
    rule: &StructuredRuleDescriptor,
    declarations: &DescriptorIndex<'_>,
    (sort_parents, catalog): (
        &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
        &BTreeMap<StableItemId, ProductionSignature>,
    ),
    subject: SemanticTerm,
    result: Option<SemanticTerm>,
) -> Result<FixedConfigurationRewrite<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let shape = |detail| {
        DescriptorLoweringError::unsupported_shape("rule stated over the computation cell", detail)
    };
    let mut configurations = declarations
        .keys()
        .filter(|id| id.item_kind() == ItemKind::Configuration);
    let (Some(configuration_id), None) = (configurations.next(), configurations.next()) else {
        return Err(shape("the definition has no one configuration"));
    };
    let configuration = require_fixed_configuration(
        configuration_id,
        declarations,
        "rule stated over the computation cell",
        "a computation cell rewrite requires a fixed configuration",
    )?;
    // The computation is the configuration's main cell, where every sentence that names no
    // cell runs (`krs_ir::select_main_cell`).
    let computation = match configuration.main_cell() {
        krs_ir::MainCell::Cell(reference) => &reference.cell,
        krs_ir::MainCell::NoComputationCell => {
            return Err(DescriptorLoweringError::ComputationCell {
                reason: format!(
                    "this rule rewrites the computation's first item, but configuration `{}` has \
                     no `KSequence` cell to hold the computation",
                    configuration_id.item_name()
                ),
                range: None,
                item: None,
            }
            .within(
                descriptor.id(),
                key_range(descriptor, &rule.pattern_key).as_ref(),
            ));
        }
        // A configuration with several computation cells and no main cell is the
        // configuration's mistake, which its own lowering refuses: the rule has that one cause,
        // so it reports the configuration's refusal, at the configuration, and adds none.
        krs_ir::MainCell::Ambiguous { .. } => {
            let owner = declarations
                .get(configuration_id)
                .ok_or_else(|| shape("the configuration has no descriptor"))?;
            return Err(
                match super::configuration::lower_fixed_configuration_descriptor(
                    owner,
                    configuration,
                    declarations,
                    sort_parents,
                    catalog,
                ) {
                    Err(refusal) => {
                        refusal.within(owner.id(), super::origin::item_range(owner).as_ref())
                    }
                    Ok(_) => shape("the configuration's lowering accepts it without a main cell"),
                },
            );
        }
    };
    let result_key = rule
        .result_key
        .clone()
        .unwrap_or_else(|| rule.pattern_key.clone());
    let before = SemanticTerm::k_sequence(
        semantic_origin(descriptor, rule.pattern_key.clone(), "completed-k-subject")?,
        subject.sort().clone(),
        vec![subject],
    );
    let post = match result {
        Some(result) => CellPost::Replace {
            term: SemanticTerm::k_sequence(
                semantic_origin(descriptor, result_key, "completed-k-result")?,
                result.sort().clone(),
                vec![result],
            ),
        },
        None => CellPost::Local,
    };
    let clause = FixedCellClause::new(
        semantic_origin(descriptor, rule.pattern_key.clone(), "completed-k-clause")?,
        semantic_cell_id(computation)?,
        before,
        post,
        // A `#[k::rule] fn` over a term keeps the rest of the computation,
        // which no token denotes.
        CellContentFrame::KSequenceTail {
            origin: inserted_origin(
                descriptor,
                rule.pattern_key.clone(),
                "implicit-k-tail",
                InsertedNode::CellFrame,
            )?,
            binding: None,
        },
    );
    let selected = BTreeSet::from([computation.clone()]);
    let omitted = omitted_leaf_cells(&configuration.declaration, declarations, &selected)?;
    Ok(FixedConfigurationRewrite::new(
        semantic_origin(
            descriptor,
            rule.pattern_key.clone(),
            "completed-configuration-rewrite",
        )?,
        generated_semantic_id("configuration", configuration_id, None)?,
        vec![ConfigurationClause::Fixed(clause)],
        omitted,
    )?)
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

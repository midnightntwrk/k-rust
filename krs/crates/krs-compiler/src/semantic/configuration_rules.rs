use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    CellContentFrame, CellPost, ConfigurationClause, Descriptor, DescriptorCellReference,
    DescriptorClaim, DescriptorClaimBinder, DescriptorIndex, DescriptorTerm, FixedCellClause,
    FixedCellPattern, FixedConfigurationPattern, FixedConfigurationRewrite, ItemKind,
    ProtocolCellContent, ProtocolContextAliasBindingKind, ProtocolRuleBindingKind,
    ProtocolRuleCell, ProtocolRuleFrame, ProtocolRuleMapBody, ProtocolRuleStateTerm, ProvenanceKey,
    SemanticId, SourceRange, StableItemId,
};
use krs_ir_levels::{
    IrTermKind, MapEntry, MapOperands, SemanticCondition, SemanticContextAlias, SemanticRule,
    SemanticSortRef, SemanticTerm, SemanticVariable,
};
use krs_syntax::ProvenanceRole;

use super::catalog::{ProductionSignature, common_sequence_item_sort, semantic_sort_ref};
use super::collection_types::{CollectionTyping, Root, Walker};
use super::configuration::{check_stdin_reads, stdin_cells};
use super::error::DescriptorLoweringError;
use super::infer::{
    CollectionUse, StructuredTermBuilder, declared_existentials, initial_binding_constraints,
};
use super::origin::{
    generated_semantic_id, key_range, role_key, semantic_cell_id, semantic_origin,
    shell_payload_key,
};
use super::references::require_cell_field;
use super::rules::{
    check_group_descendants, framework_k_item_sort, lower_nondet_group, lower_rule_label,
    lower_rule_priority, omitted_leaf_cells, require_fixed_configuration,
};

/// Stable rule cell as transported for configuration rules and context aliases.
type DescriptorRuleCell = ProtocolRuleCell<DescriptorCellReference, DescriptorTerm>;

/// The exact authored range of one `cells!` entry.
fn entry_range(descriptor: &Descriptor, entry: &DescriptorRuleCell) -> Option<Box<SourceRange>> {
    key_range(descriptor, &entry.field.key).map(Box::new)
}

/// Shared inputs for lowering the cell terms of one configuration rule or
/// context alias, and the variables those terms introduce, in order.
struct StateRuleTerms<'a> {
    descriptor: &'a Descriptor,
    declarations: &'a DescriptorIndex<'a>,
    sort_parents: &'a BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    /// The element types of the rule's typed cells.
    collections: &'a CollectionTyping,
    /// The rule's term, existential, and fresh binders at their declared
    /// sorts.
    declared_binders: BTreeMap<String, (SemanticSortRef, ProvenanceKey)>,
    wildcard_ordinal: usize,
    variables: Vec<SemanticVariable>,
    /// Computation remainders the result does not put back, each with its
    /// frame key: the rule moves them, so they must be used elsewhere.
    moved_remainders: Vec<(SemanticId, ProvenanceKey)>,
}

impl StateRuleTerms<'_> {
    /// Infers and lowers one ordinary term; its wildcards join `variables`.
    fn term(
        &mut self,
        term: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
        binding_sorts: &BTreeMap<String, SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let binding_names = binding_sorts.keys().cloned().collect::<BTreeSet<_>>();
        let mut builder = StructuredTermBuilder {
            descriptor: self.descriptor,
            catalog: self.catalog,
            declarations: Some(self.declarations),
            k_item_sort: Some(framework_k_item_sort(self.declarations)?),
            sort_parents: self.sort_parents,
            binding_names: &binding_names,
            pattern_key: None,
            binding_sorts: BTreeMap::new(),
            binding_constraints: initial_binding_constraints(binding_sorts),
            constraint_sites: BTreeMap::new(),
            wildcard_offset: self.wildcard_ordinal,
            wildcards: Vec::new(),
            result_wildcards: false,
            locals: super::infer::LocalBinders::default(),
            head_pending: false,
            operators: super::operators::OperatorInference::default(),
            declared_binders: self.declared_binders.clone(),
            subject_keys: BTreeMap::new(),
            record_updates: super::record_updates::RecordUpdateState::default(),
            collections: CollectionUse::new(self.collections),
        };
        builder.infer_sentence(|builder| builder.infer(term, expected_sort, subject))?;
        builder.resolve_binding_sorts()?;
        let lowered = builder.lower(term, expected_sort, subject)?;
        self.wildcard_ordinal += builder.wildcards.len();
        self.variables.append(&mut builder.wildcards);
        Ok(lowered)
    }

    /// Infers and lowers one key or value of a `map![..]` state, at its
    /// element sort when the map is typed and as a `KItem` otherwise.
    fn element(
        &mut self,
        term: &DescriptorTerm,
        binding_sorts: &BTreeMap<String, SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let sort = self.collections.element_sort(term);
        self.term(term, sort.as_ref(), binding_sorts, subject)
    }

    /// Infers and lowers one `requires` or `ensures` condition: an object
    /// Bool, or a matching-logic predicate where `kind` admits one (KF-039).
    /// Its local binders join `variables`.
    fn condition(
        &mut self,
        kind: krs_ir::SentenceKind,
        condition: &krs_ir::DescriptorRuleCondition,
        binding_sorts: &BTreeMap<String, SemanticSortRef>,
        role: &str,
        ensures: bool,
    ) -> Result<SemanticCondition, DescriptorLoweringError> {
        let binding_names = binding_sorts.keys().cloned().collect::<BTreeSet<_>>();
        let mut builder = StructuredTermBuilder {
            descriptor: self.descriptor,
            catalog: self.catalog,
            declarations: Some(self.declarations),
            k_item_sort: Some(framework_k_item_sort(self.declarations)?),
            sort_parents: self.sort_parents,
            binding_names: &binding_names,
            pattern_key: None,
            binding_sorts: BTreeMap::new(),
            binding_constraints: initial_binding_constraints(binding_sorts),
            constraint_sites: BTreeMap::new(),
            wildcard_offset: self.wildcard_ordinal,
            wildcards: Vec::new(),
            result_wildcards: false,
            locals: super::infer::LocalBinders::default(),
            head_pending: false,
            operators: super::operators::OperatorInference::default(),
            declared_binders: self.declared_binders.clone(),
            subject_keys: BTreeMap::new(),
            record_updates: super::record_updates::RecordUpdateState::default(),
            collections: CollectionUse::new(self.collections),
        };
        super::ml::check_condition_placement(&builder, kind, condition, ensures)?;
        builder.infer_sentence(|builder| super::ml::infer_condition(builder, condition))?;
        builder.resolve_binding_sorts()?;
        let lowered = super::ml::lower_condition(&mut builder, condition, role)?;
        self.wildcard_ordinal += builder.wildcards.len();
        self.variables.append(&mut builder.wildcards);
        Ok(lowered)
    }

    /// Lowers one entry's state; an error that names no narrower node is located at the entry,
    /// `entry_key`.
    fn state_term(
        &mut self,
        state: &ProtocolRuleStateTerm<DescriptorTerm>,
        declared_sort: &SemanticSortRef,
        entry_key: &ProvenanceKey,
        binding_sorts: &BTreeMap<String, SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        self.entry_state_term(state, declared_sort, binding_sorts, subject)
            .map_err(|error| {
                error.within(
                    self.descriptor.id(),
                    key_range(self.descriptor, entry_key).as_ref(),
                )
            })
    }

    /// Lowers one cell's state term: an ordinary term, a K sequence, or a map.
    fn entry_state_term(
        &mut self,
        state: &ProtocolRuleStateTerm<DescriptorTerm>,
        declared_sort: &SemanticSortRef,
        binding_sorts: &BTreeMap<String, SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let descriptor = self.descriptor;
        match state {
            ProtocolRuleStateTerm::Present { .. }
            | ProtocolRuleStateTerm::Absent
            | ProtocolRuleStateTerm::Instances(_) => Err(DescriptorLoweringError::invalid_term(
                descriptor.id(),
                "an optional or collection entry occurs where a cell's content belongs",
            )),
            ProtocolRuleStateTerm::Term(term) => {
                if matches!(declared_sort, SemanticSortRef::Cell(_)) {
                    return Err(DescriptorLoweringError::cell_wrapper(None, None, None));
                }
                self.term(term, Some(declared_sort), binding_sorts, subject)
            }
            ProtocolRuleStateTerm::Group(term) => {
                if !matches!(declared_sort, SemanticSortRef::Cell(_)) {
                    let wrapper = super::cell_states::leaf_wrapper(declared_sort);
                    return Err(DescriptorLoweringError::cell_wrapper(
                        None,
                        Some(wrapper),
                        None,
                    ));
                }
                self.term(term, Some(declared_sort), binding_sorts, subject)
            }
            ProtocolRuleStateTerm::KSequence(sequence) => {
                let key = shell_payload_key(descriptor, sequence.payload_key.as_ref())?;
                if *declared_sort != SemanticSortRef::k_sequence() {
                    return Err(DescriptorLoweringError::invalid_term(
                        descriptor.id(),
                        "K sequence occurs in a non-KSequence rule cell",
                    )
                    .within(descriptor.id(), key_range(descriptor, key).as_ref()));
                }
                let items = sequence
                    .items
                    .iter()
                    .map(|item| self.term(&item.value, None, binding_sorts, subject))
                    .collect::<Result<Vec<_>, _>>()?;
                let item_sort =
                    common_sequence_item_sort(descriptor, &items, self.sort_parents, !subject)
                        .map_err(|error| {
                            error.within(descriptor.id(), key_range(descriptor, key).as_ref())
                        })?;
                Ok(SemanticTerm::k_sequence(
                    semantic_origin(descriptor, key.clone(), "rule-k-sequence")?,
                    item_sort,
                    items,
                ))
            }
            ProtocolRuleStateTerm::Map(map) => {
                let key = shell_payload_key(descriptor, map.payload_key.as_ref())?;
                if *declared_sort != SemanticSortRef::map() {
                    return Err(DescriptorLoweringError::invalid_term(
                        descriptor.id(),
                        "map occurs in a non-Map rule cell",
                    )
                    .within(descriptor.id(), key_range(descriptor, key).as_ref()));
                }
                let operands = match &map.body {
                    ProtocolRuleMapBody::Empty { .. } => MapOperands::Empty,
                    ProtocolRuleMapBody::Items { items, .. } => {
                        let mut entries = Vec::with_capacity(items.len());
                        for item in items {
                            entries.push(MapEntry {
                                key: self.element(&item.key, binding_sorts, subject)?,
                                value: self.element(&item.value, binding_sorts, subject)?,
                            });
                        }
                        MapOperands::items(entries).map_err(|error| {
                            DescriptorLoweringError::invalid_term(
                                descriptor.id(),
                                error.to_string(),
                            )
                        })?
                    }
                    ProtocolRuleMapBody::Update {
                        base, key, value, ..
                    } => MapOperands::Update {
                        map: self.term(
                            base,
                            Some(&SemanticSortRef::map()),
                            binding_sorts,
                            subject,
                        )?,
                        key: self.element(key, binding_sorts, subject)?,
                        value: self.element(value, binding_sorts, subject)?,
                    },
                };
                Ok(SemanticTerm::map(
                    semantic_origin(descriptor, key.clone(), "rule-map")?,
                    operands,
                ))
            }
        }
    }
}

/// Binding sorts visible to a configuration rule's subject, result, and
/// conditions, and the declared variables in binding order followed by the
/// existentials and the fresh binders. A condition sees every variable the
/// left side binds, the computation (`K`) and map remainders included.
struct ConfigurationRuleBindings {
    subject_sorts: BTreeMap<String, SemanticSortRef>,
    result_sorts: BTreeMap<String, SemanticSortRef>,
    requires_sorts: BTreeMap<String, SemanticSortRef>,
    variables: Vec<SemanticVariable>,
}

fn configuration_rule_bindings(
    rule: &krs_ir::DescriptorConfigurationRule,
) -> Result<ConfigurationRuleBindings, DescriptorLoweringError> {
    let mut subject_sorts = BTreeMap::new();
    let mut remainder_sorts = BTreeMap::new();
    let mut variables = Vec::new();
    for binding in &rule.bindings {
        let sort = match &binding.kind {
            ProtocolRuleBindingKind::Term { sort } => semantic_sort_ref(&sort.sort),
            ProtocolRuleBindingKind::KSequenceFrame => SemanticSortRef::k_sequence(),
            ProtocolRuleBindingKind::MapFrame => SemanticSortRef::map(),
            ProtocolRuleBindingKind::ConfigurationFrame
            | ProtocolRuleBindingKind::InstancesFrame => continue,
        };
        if matches!(binding.kind, ProtocolRuleBindingKind::Term { .. }) {
            subject_sorts.insert(binding.name.clone(), sort.clone());
        } else {
            remainder_sorts.insert(binding.name.clone(), sort.clone());
        }
        variables.push(SemanticVariable::new(
            SemanticId::new(binding.name.clone())?,
            sort,
        ));
    }
    let mut result_sorts = subject_sorts.clone();
    let claim_existentials = rule
        .claim
        .as_ref()
        .map_or(&[][..], |claim| claim.existentials.as_slice());
    for binder in claim_existentials
        .iter()
        .chain(&rule.existentials)
        .chain(&rule.fresh)
    {
        let sort = semantic_sort_ref(&binder.sort.sort);
        result_sorts.insert(binder.name.clone(), sort.clone());
        variables.push(SemanticVariable::new(
            SemanticId::new(binder.name.clone())?,
            sort,
        ));
    }
    let mut requires_sorts = subject_sorts.clone();
    requires_sorts.extend(remainder_sorts.clone());
    result_sorts.extend(remainder_sorts);
    Ok(ConfigurationRuleBindings {
        subject_sorts,
        result_sorts,
        requires_sorts,
        variables,
    })
}

/// The element types of a `cells!` rule's typed cells: each subject cell at
/// its type as a pattern, each result cell at its type as a written term.
fn configuration_rule_typing(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorConfigurationRule,
    declarations: &DescriptorIndex<'_>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<CollectionTyping, DescriptorLoweringError> {
    let mut walker = Walker::new(descriptor, Some(declarations), catalog, sort_parents);
    if let Some(claim) = &rule.claim {
        walker.existentials(&claim.existentials, true);
    }
    walker.existentials(&rule.existentials, rule.claim.is_some());
    walker.checked_binders(rule.fresh.iter().map(|binder| binder.name.as_str()));
    let mut roots = Vec::new();
    for (cells, subject) in std::iter::once((&rule.subject, true))
        .chain(rule.result.iter().map(|result| (result, false)))
    {
        for cell in &cells.cells {
            let field = require_cell_field(&cell.field.cell, declarations)?;
            walker.state_roots(&cell.value, field, subject, &mut roots)?;
        }
    }
    roots.extend(
        rule.requires
            .iter()
            .chain(&rule.ensures)
            .map(|condition| Root::Term {
                term: &condition.term,
                ty: None,
                subject: false,
            }),
    );
    walker.run(&roots)
}

#[expect(
    clippy::too_many_lines,
    reason = "The rewrite, its conditions, its claim metadata, and its binders are lowered in one ordered pass."
)]
pub(super) fn lower_configuration_rule_descriptor(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorConfigurationRule,
    declarations: &DescriptorIndex<'_>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticRule, DescriptorLoweringError> {
    let configuration = require_fixed_configuration(
        &rule.subject_configuration.configuration,
        declarations,
        "configuration rule",
        "configuration rules require a fixed configuration",
    )?;
    let ConfigurationRuleBindings {
        subject_sorts,
        result_sorts,
        requires_sorts,
        variables,
    } = configuration_rule_bindings(rule)?;
    let typing = configuration_rule_typing(descriptor, rule, declarations, catalog, sort_parents)?;
    let mut declared_binders = declared_existentials(
        rule.claim
            .iter()
            .flat_map(|claim| &claim.existentials)
            .chain(&rule.existentials)
            .chain(&rule.fresh),
    );
    // The binder list declares each term binder, as a `where` does: every
    // cell term checks its occurrences against the declared sort.
    declared_binders.extend(rule.bindings.iter().filter_map(|binding| {
        let ProtocolRuleBindingKind::Term { sort } = &binding.kind else {
            return None;
        };
        Some((
            binding.name.clone(),
            (semantic_sort_ref(&sort.sort), sort.key.clone()),
        ))
    }));
    let mut terms = StateRuleTerms {
        descriptor,
        declarations,
        sort_parents,
        catalog,
        collections: &typing,
        declared_binders,
        wildcard_ordinal: 0,
        variables,
        moved_remainders: Vec::new(),
    };
    let clauses = lower_configuration_rule_clauses(
        &mut terms,
        rule,
        configuration,
        &subject_sorts,
        &result_sorts,
    )?;
    let unused_moved = moved_remainders_unused_by(&terms, &clauses);
    // A context's hole lies in the computation cell (KF-021).
    if rule.sentence_kind == krs_ir::ConfigurationSentenceKind::Context
        && let Some(step) = &rule.evaluation
    {
        let hole = SemanticId::new(step.hole.clone())?;
        for (cell, clause) in rule.subject.cells.iter().zip(&clauses) {
            if cell.wrapper != Some(krs_ir::CellWrapper::KCell)
                && clause
                    .parts()
                    .iter()
                    .filter_map(krs_ir::ClausePart::pre_term)
                    .any(|term| super::evaluation::mentions(term, &hole))
            {
                return Err(super::evaluation::outside_computation_cell(
                    "the context's hole",
                    &step.hole,
                    &cell.field.cell.field,
                    semantic_origin(descriptor, cell.field.key.clone(), "rule-cell")?
                        .origin()
                        .exact_authored_range(),
                ));
            }
        }
    }
    // A claim keeps its stream cells as ordinary List cells: `prove` performs no console I/O.
    if rule.sentence_kind != krs_ir::ConfigurationSentenceKind::Claim {
        let stdin = stdin_cells(&configuration.declaration, declarations)?;
        check_stdin_reads(&clauses, &stdin)?;
    }

    super::cell_states::check_implicit_and_explicit_instances(
        descriptor,
        &rule.pattern_key,
        declarations,
        &clauses,
        &rule
            .subject
            .cells
            .iter()
            .map(|cell| {
                (
                    cell.field.clone(),
                    matches!(cell.value, ProtocolRuleStateTerm::Instances(_)),
                )
            })
            .collect::<Vec<_>>(),
    )?;
    let selected = rule
        .subject
        .cells
        .iter()
        .map(|cell| cell.field.cell.clone())
        .collect::<BTreeSet<_>>();
    check_group_descendants(
        descriptor,
        &rule.pattern_key,
        &configuration.declaration,
        declarations,
        &selected,
    )?;
    let omitted_siblings = omitted_leaf_cells(&configuration.declaration, declarations, &selected)?;
    if matches!(rule.subject.remainder, ProtocolRuleFrame::Exact) && !omitted_siblings.is_empty() {
        return Err(DescriptorLoweringError::unsupported_shape(
            "configuration rule remainder",
            "an exact subject must select every fixed leaf cell",
        ));
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
    let requires = rule
        .requires
        .as_ref()
        .map(|condition| {
            terms.condition(
                rule.sentence_kind.into(),
                condition,
                &requires_sorts,
                "rule-requires",
                false,
            )
        })
        .transpose()?;
    let priority = lower_rule_priority(descriptor, rule.priority.as_ref())?;
    let (existentials, ensures) = lower_existentials(&mut terms, rule, &result_sorts)?;
    check_moved_remainders(&unused_moved, requires.as_ref(), ensures.as_ref())?;
    Ok(SemanticRule::new_configuration(
        semantic_origin(
            descriptor,
            role_key(
                if rule.sentence_kind == krs_ir::ConfigurationSentenceKind::Claim {
                    ProvenanceRole::ClaimDeclaration
                } else {
                    ProvenanceRole::RuleDeclaration
                },
                0,
            ),
            "configuration-rule",
        )?,
        descriptor.id().clone(),
        rule.sentence_kind.into(),
        terms.variables,
        body,
    )?
    .with_label(lower_rule_label(descriptor, rule.label.as_ref())?)
    .with_priority(priority)?
    .with_nondet_group(lower_nondet_group(descriptor, rule.nondet.as_ref())?)
    .with_requires(requires)?
    .with_claim(
        rule.claim
            .as_ref()
            .map(|claim| lower_rule_claim(descriptor, claim))
            .transpose()?,
    )
    .with_existentials(existentials)
    .with_ensures(ensures)
    .with_fresh(super::rules::lower_rule_fresh(descriptor, &rule.fresh)?)
    .with_evaluation(super::rules::lower_rule_evaluation(
        descriptor,
        rule.evaluation.as_ref(),
    )?))
}

/// Checks that the result selects only subject cells and that the remainder
/// frames agree, then lowers one clause per subject cell.
fn lower_configuration_rule_clauses(
    terms: &mut StateRuleTerms<'_>,
    rule: &krs_ir::DescriptorConfigurationRule,
    configuration: &krs_ir::DescriptorFixedConfiguration,
    subject_sorts: &BTreeMap<String, SemanticSortRef>,
    result_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<Vec<ConfigurationClause<SemanticId, SemanticTerm>>, DescriptorLoweringError> {
    let subject_cells = rule
        .subject
        .cells
        .iter()
        .map(|cell| &cell.field.cell)
        .collect::<BTreeSet<_>>();
    // A single-body rule (KF-011) has no result: each cell that holds a
    // `k::rewrite!` is rewritten in place, every other cell is read.
    let result_cells = rule
        .result
        .iter()
        .flat_map(|result| &result.cells)
        .map(|cell| (&cell.field.cell, cell))
        .collect::<BTreeMap<_, _>>();
    if result_cells
        .keys()
        .any(|identity| !subject_cells.contains(identity))
    {
        return Err(DescriptorLoweringError::unsupported_shape(
            "configuration rule",
            "the result selects a fixed cell absent from the subject",
        ));
    }
    if let Some(result) = &rule.result {
        validate_frame_pair(
            terms.descriptor,
            &rule.subject.remainder,
            &result.remainder,
            "configuration remainder",
        )?;
    }
    let clauses = rule
        .subject
        .cells
        .iter()
        .map(|subject| {
            let result = result_cells.get(&subject.field.cell).copied();
            if super::cell_states::is_cell_state(&subject.value)
                || result.is_some_and(|result| super::cell_states::is_cell_state(&result.value))
            {
                return lower_configuration_state_clause(
                    terms,
                    subject,
                    result,
                    configuration,
                    subject_sorts,
                    result_sorts,
                );
            }
            lower_configuration_rule_clause(terms, subject, result, subject_sorts, result_sorts)
                .map(ConfigurationClause::Fixed)
        })
        .collect::<Result<Vec<_>, _>>()?;
    // A context (KF-021) need not rewrite anything.
    if rule.result.is_none()
        && rule.sentence_kind != krs_ir::ConfigurationSentenceKind::Context
        && !clauses.iter().any(|clause| {
            clause
                .as_fixed()
                .is_some_and(|clause| matches!(clause.after(), CellPost::Local))
        })
    {
        return Err(DescriptorLoweringError::InvalidLocalRewrite {
            item: Box::new(terms.descriptor.id().clone()),
            reason: "a single-body rule must change something: no cell of its subject holds a `k::rewrite!`".to_owned(),
            range: semantic_origin(terms.descriptor, rule.pattern_key.clone(), "rule-pattern")?
                .origin()
                .exact_authored_range()
                .map(Box::new),
        });
    }
    Ok(clauses)
}

/// Lowers an optional (`?`) or collection (`*`) cell entry of a `cells!`
/// rule (KF-023): the wrapper of a `Some(..)` leaf agrees with the declared
/// cell, and a group, `None`, or instance list has none.
fn lower_configuration_state_clause(
    terms: &mut StateRuleTerms<'_>,
    subject: &DescriptorRuleCell,
    result: Option<&DescriptorRuleCell>,
    configuration: &krs_ir::DescriptorFixedConfiguration,
    subject_sorts: &BTreeMap<String, SemanticSortRef>,
    result_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<ConfigurationClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = terms.descriptor;
    let declared = require_cell_field(&subject.field.cell, terms.declarations)?;
    // An entry whose state belongs to another kind of cell than the declared one is the
    // mistake, on whichever side it is written: `pc: Cell(x) => None` on a plain cell names the
    // result.
    for cell in std::iter::once(subject).chain(result) {
        super::cell_states::check_state_kind(descriptor, declared, &cell.field, &cell.value)?;
    }
    let expected_wrapper = match &declared.content {
        ProtocolCellContent::Leaf { wrapper, .. } => Some(*wrapper),
        ProtocolCellContent::Nested { .. } => None,
    };
    for cell in std::iter::once(subject).chain(result) {
        let wrapper_valid = match &cell.value {
            ProtocolRuleStateTerm::Present { .. } => cell.wrapper == expected_wrapper,
            _ => cell.wrapper.is_none(),
        };
        if !wrapper_valid {
            return Err(super::cell_states::collection_error(
                descriptor,
                krs_diagnostic::codes::analysis::OPTIONAL_PRESENCE,
                &cell.field.key,
                format!(
                    "`{}` is written `Some(k::configuration::Cell(..))` for a leaf cell, `Some(group)` for a nested cell, or `None`",
                    subject.field.cell.field
                ),
            ));
        }
    }
    let declarations = terms.declarations;
    let mut lowering = CellsStateLowering {
        terms,
        subject_sorts,
        result_sorts,
    };
    match &subject.value {
        ProtocolRuleStateTerm::Instances(before) => {
            let after = match result.map(|result| &result.value) {
                None => None,
                Some(ProtocolRuleStateTerm::Instances(after)) => Some(after),
                // The subject fits the collection, so the result is the entry that does not.
                Some(_) => {
                    let result = result.expect("a result state was matched");
                    return Err(super::cell_states::collection_error(
                        descriptor,
                        krs_diagnostic::codes::analysis::COLLECTION_ENTRY,
                        &result.field.key,
                        format!(
                            "the collection `{}` is written as an instance list on both sides",
                            subject.field.cell.field
                        ),
                    ));
                }
            };
            super::cell_states::lower_instances_clause(
                &mut lowering,
                declarations,
                configuration,
                &subject.field,
                before,
                after,
                result.map(|result| &result.field.key),
            )
        }
        before => super::cell_states::lower_optional_clause(
            &mut lowering,
            declarations,
            &subject.field,
            before,
            result.map(|result| &result.value),
            result.map(|result| &result.field.key),
        ),
    }
}

/// [`super::cell_states::StateLowering`] for `cells!` rules: each term is
/// inferred and lowered on its own against the side's binding sorts.
struct CellsStateLowering<'a, 'b> {
    terms: &'a mut StateRuleTerms<'b>,
    subject_sorts: &'a BTreeMap<String, SemanticSortRef>,
    result_sorts: &'a BTreeMap<String, SemanticSortRef>,
}

impl super::cell_states::StateLowering for CellsStateLowering<'_, '_> {
    fn descriptor(&self) -> &Descriptor {
        self.terms.descriptor
    }

    fn lower_state(
        &mut self,
        state: &ProtocolRuleStateTerm<DescriptorTerm>,
        sort: &SemanticSortRef,
        entry_key: &ProvenanceKey,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let binding_sorts = if subject {
            self.subject_sorts
        } else {
            self.result_sorts
        };
        // An instance child is parsed as a term; a nested child's term is a
        // whole group.
        let group;
        let state = match (state, sort) {
            (ProtocolRuleStateTerm::Term(term), SemanticSortRef::Cell(_)) => {
                group = ProtocolRuleStateTerm::Group(term.clone());
                &group
            }
            (state, _) => state,
        };
        self.terms
            .state_term(state, sort, entry_key, binding_sorts, subject)
    }

    fn same(&self, left: &SemanticTerm, right: &SemanticTerm) -> bool {
        semantic_terms_equivalent(left, right)
    }
}

/// The post-state of a cell a rule reads without restating it: rewritten in
/// place when it holds a `k::rewrite!` (KF-011), otherwise unchanged.
fn unrestated_post(before: &SemanticTerm) -> CellPost<SemanticTerm> {
    if before.contains_rewrite() {
        CellPost::Local
    } else {
        CellPost::Preserve
    }
}

fn lower_configuration_rule_clause(
    terms: &mut StateRuleTerms<'_>,
    subject: &DescriptorRuleCell,
    result: Option<&DescriptorRuleCell>,
    subject_sorts: &BTreeMap<String, SemanticSortRef>,
    result_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<FixedCellClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = terms.descriptor;
    let declared = require_cell_field(&subject.field.cell, terms.declarations)?;
    let name = &subject.field.cell.field;
    // Neither entry is `Some`/`None` or an instance list, so on an optional cell or a collection,
    // whose entries are written that way, the subject's spelling is that cell's mistake.
    match declared
        .multiplicity
        .as_ref()
        .map(|multiplicity| multiplicity.value.as_str())
    {
        Some("?") => {
            return Err(super::cell_states::collection_error(
                descriptor,
                krs_diagnostic::codes::analysis::OPTIONAL_PRESENCE,
                &subject.field.key,
                super::cell_states::bare_optional(name),
            ));
        }
        Some(_) => {
            return Err(super::cell_states::collection_error(
                descriptor,
                krs_diagnostic::codes::analysis::COLLECTION_ENTRY,
                &subject.field.key,
                format!(
                    "`{name}` is a cell collection: its entry is an instance list (`[..]` for a List collection, `{{ .. }}` for a Set or Map one), not one value"
                ),
            ));
        }
        None => {}
    }
    let ProtocolCellContent::Leaf { wrapper, sort, .. } = &declared.content else {
        let ProtocolCellContent::Nested { declaration } = &declared.content else {
            unreachable!("a fixed cell is a leaf or nested");
        };
        return lower_configuration_group_clause(
            terms,
            subject,
            result,
            &declaration.declaration,
            subject_sorts,
            result_sorts,
        );
    };
    // Each check names the entry that disagrees with the declaration, the subject first.
    let entries = || std::iter::once(subject).chain(result);
    if let Some(entry) = entries().find(|entry| entry.wrapper != Some(*wrapper)) {
        return Err(DescriptorLoweringError::cell_wrapper(
            Some(name),
            Some(*wrapper),
            entry_range(descriptor, entry),
        ));
    }
    let declared_sort = semantic_sort_ref(&sort.sort);
    let mut before = terms.state_term(
        &subject.value,
        &declared_sort,
        &subject.field.key,
        subject_sorts,
        true,
    )?;
    let subject_frame = rule_state_frame(&subject.value);
    let mut frame = lower_subject_cell_frame(descriptor, &subject.value)?;
    let post = if let Some(result) = result {
        let after = terms.state_term(
            &result.value,
            &declared_sort,
            &result.field.key,
            result_sorts,
            false,
        )?;
        let result_frame = rule_state_frame(&result.value);
        if let Some(moved) = pair_cell_frames(
            terms,
            &subject.field.cell.field,
            subject_frame,
            result_frame,
            &before,
        )? {
            // The moved remainder is the subject's last item, not a frame.
            before = moved;
            frame = CellContentFrame::Exact;
        }
        if semantic_terms_equivalent(&before, &after) {
            CellPost::Preserve
        } else {
            CellPost::Replace { term: after }
        }
    } else {
        unrestated_post(&before)
    };
    Ok(FixedCellClause::new(
        semantic_origin(descriptor, subject.field.key.clone(), "rule-cell-clause")?,
        semantic_cell_id(&subject.field.cell)?,
        before,
        post,
        frame,
    ))
}

/// Lowers one whole nested (group) cell entry, `frame: f`, `frame: _` or
/// `frame: k::fragment![..]`, into a whole-cell clause whose terms have the
/// group's generated cell sort (KF-016).
fn lower_configuration_group_clause(
    terms: &mut StateRuleTerms<'_>,
    subject: &DescriptorRuleCell,
    result: Option<&DescriptorRuleCell>,
    declaration: &StableItemId,
    subject_sorts: &BTreeMap<String, SemanticSortRef>,
    result_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<FixedCellClause<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = terms.descriptor;
    let group_entry = |cell: &DescriptorRuleCell| {
        cell.wrapper.is_none() && matches!(cell.value, ProtocolRuleStateTerm::Group(_))
    };
    if let Some(entry) = std::iter::once(subject)
        .chain(result)
        .find(|entry| !group_entry(entry))
    {
        return Err(DescriptorLoweringError::cell_wrapper(
            Some(&subject.field.cell.field),
            None,
            entry_range(descriptor, entry),
        ));
    }
    let sort = SemanticSortRef::Cell(declaration.clone());
    let before = terms.state_term(
        &subject.value,
        &sort,
        &subject.field.key,
        subject_sorts,
        true,
    )?;
    let post = match result {
        Some(result) => {
            let after =
                terms.state_term(&result.value, &sort, &result.field.key, result_sorts, false)?;
            if semantic_terms_equivalent(&before, &after) {
                CellPost::Preserve
            } else {
                CellPost::Replace { term: after }
            }
        }
        None => unrestated_post(&before),
    };
    Ok(FixedCellClause::whole(
        semantic_origin(descriptor, subject.field.key.clone(), "rule-group-clause")?,
        semantic_cell_id(&subject.field.cell)?,
        before,
        post,
    ))
}

/// Lowers the existentials and the ensures condition of a configuration rule.
/// A claim carries them in its claim metadata; a transition carries them
/// directly (`#[k::exists]`, `#[k::ensures]`).
fn lower_existentials(
    terms: &mut StateRuleTerms<'_>,
    rule: &krs_ir::DescriptorConfigurationRule,
    result_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<
    (
        Vec<krs_ir_levels::SemanticScopedBinder>,
        Option<SemanticCondition>,
    ),
    DescriptorLoweringError,
> {
    let descriptor = terms.descriptor;
    let (existentials, ensures, binder_role, ensures_role) = match &rule.claim {
        Some(claim) => (
            claim.existentials.as_slice(),
            claim.ensures.as_ref(),
            "claim-existential-binder",
            "claim-ensures",
        ),
        None => (
            rule.existentials.as_slice(),
            rule.ensures.as_ref(),
            "rule-existential-binder",
            "rule-ensures",
        ),
    };
    let existentials = existentials
        .iter()
        .map(|binder| lower_claim_binder(descriptor, binder, binder_role))
        .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
    let ensures = ensures
        .map(|condition| {
            terms.condition(
                rule.sentence_kind.into(),
                condition,
                result_sorts,
                ensures_role,
                true,
            )
        })
        .transpose()?;
    Ok((existentials, ensures))
}

fn lower_rule_claim(
    descriptor: &Descriptor,
    claim: &DescriptorClaim,
) -> Result<krs_ir_levels::SemanticClaim, DescriptorLoweringError> {
    let universals = claim
        .universals
        .iter()
        .map(|binder| lower_claim_binder(descriptor, binder, "claim-universal-binder"))
        .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
    Ok(krs_ir_levels::SemanticClaim::new(
        semantic_origin(descriptor, claim.modality_key.clone(), "claim-modality")?,
        claim.modality,
        claim
            .circularity_key
            .as_ref()
            .map(|key| semantic_origin(descriptor, key.clone(), "claim-circularity"))
            .transpose()?,
        universals,
    )
    .with_trusted_origin(
        claim
            .trusted_key
            .as_ref()
            .map(|key| semantic_origin(descriptor, key.clone(), "claim-trusted"))
            .transpose()?,
    ))
}

fn lower_claim_binder(
    descriptor: &Descriptor,
    binder: &DescriptorClaimBinder,
    role: &str,
) -> Result<krs_ir_levels::SemanticScopedBinder, DescriptorLoweringError> {
    Ok(krs_ir_levels::SemanticScopedBinder::new(
        semantic_origin(descriptor, binder.declaration_key.clone(), role)?,
        semantic_origin(descriptor, binder.name_key.clone(), "claim-binder-name")?,
        SemanticId::new(binder.name.clone())?,
        semantic_origin(descriptor, binder.sort.key.clone(), "claim-binder-sort")?,
        semantic_sort_ref(&binder.sort.sort),
    ))
}

pub(super) fn lower_context_alias_descriptor(
    descriptor: &Descriptor,
    alias: &krs_ir::DescriptorContextAlias,
    declarations: &DescriptorIndex<'_>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticContextAlias, DescriptorLoweringError> {
    let configuration = require_fixed_configuration(
        &alias.configuration.configuration,
        declarations,
        "context alias",
        "context aliases require a fixed configuration",
    )?;
    let k_items = declarations
        .keys()
        .filter(|id| id.item_kind() == ItemKind::Sort && id.item_name() == "KItem")
        .collect::<Vec<_>>();
    let [k_item] = k_items.as_slice() else {
        return Err(DescriptorLoweringError::unsupported_shape(
            "context alias",
            "context aliases require exactly one declared KItem sort",
        ));
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
    let mut terms = StateRuleTerms {
        descriptor,
        declarations,
        sort_parents,
        catalog,
        collections: CollectionTyping::empty(),
        declared_binders: BTreeMap::new(),
        wildcard_ordinal: 0,
        variables,
        moved_remainders: Vec::new(),
    };
    let cells = alias
        .pattern
        .cells
        .iter()
        .map(|pattern| lower_context_alias_cell(&mut terms, pattern, &binding_sorts))
        .collect::<Result<Vec<_>, _>>()?;
    check_here_in_computation_cell(descriptor, alias, &cells)?;
    let selected = alias
        .pattern
        .cells
        .iter()
        .map(|cell| cell.field.cell.clone())
        .collect::<BTreeSet<_>>();
    let omitted_siblings = omitted_leaf_cells(&configuration.declaration, declarations, &selected)?;
    if matches!(alias.pattern.remainder, ProtocolRuleFrame::Exact) && !omitted_siblings.is_empty() {
        return Err(DescriptorLoweringError::unsupported_shape(
            "context alias remainder",
            "an exact pattern must select every fixed leaf cell",
        ));
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
        descriptor.id().clone(),
        semantic_origin(descriptor, alias.name_key.clone(), "context-alias-name")?,
        alias.name.clone(),
        semantic_origin(descriptor, alias.here_key.clone(), "context-alias-here")?,
        SemanticId::new(alias.here.clone())?,
        terms.variables,
        body,
    )
    .with_result(
        alias
            .result
            .as_ref()
            .map(|sort| -> Result<_, DescriptorLoweringError> {
                Ok(krs_ir_levels::IrEvaluationResult::new(
                    semantic_origin(descriptor, sort.key.clone(), "context-alias-result")?,
                    semantic_sort_ref(&sort.sort),
                ))
            })
            .transpose()?,
    ))
}

/// Checks that a context alias's HERE lies in the computation cell
/// (KF-021): heating moves it to the front of `k`.
fn check_here_in_computation_cell(
    descriptor: &Descriptor,
    alias: &krs_ir::DescriptorContextAlias,
    cells: &[FixedCellPattern<SemanticId, SemanticTerm>],
) -> Result<(), DescriptorLoweringError> {
    let here = SemanticId::new(alias.here.clone())?;
    for (pattern, cell) in alias.pattern.cells.iter().zip(cells) {
        if pattern.wrapper != Some(krs_ir::CellWrapper::KCell)
            && super::evaluation::mentions(cell.pattern(), &here)
        {
            return Err(super::evaluation::outside_computation_cell(
                "the context alias's HERE",
                &alias.here,
                &pattern.field.cell.field,
                semantic_origin(descriptor, pattern.field.key.clone(), "context-alias-cell")?
                    .origin()
                    .exact_authored_range(),
            ));
        }
    }
    Ok(())
}

/// Lowers an equation's function context (KF-025): its leaf cells as a
/// one-sided pattern over the fixed configuration, whose term binders have
/// the sorts in `binding_sorts`. Returns the context and its wildcards, which
/// continue after the first `wildcard_ordinal` of the sentence.
pub(super) fn lower_function_context(
    descriptor: &Descriptor,
    context: &krs_ir::DescriptorFunctionContext,
    tables: StateRuleTables<'_>,
    collections: &CollectionTyping,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
    wildcard_ordinal: usize,
) -> Result<
    (
        krs_ir_levels::SemanticFunctionContext,
        Vec<SemanticVariable>,
    ),
    DescriptorLoweringError,
> {
    let StateRuleTables {
        declarations,
        sort_parents,
        catalog,
    } = tables;
    let configuration = require_fixed_configuration(
        &context.configuration.configuration,
        declarations,
        "function context",
        "a function context reads the fixed configuration",
    )?;
    let mut terms = StateRuleTerms {
        descriptor,
        declarations,
        sort_parents,
        catalog,
        collections,
        declared_binders: BTreeMap::new(),
        wildcard_ordinal,
        variables: Vec::new(),
        moved_remainders: Vec::new(),
    };
    let cells = context
        .cells
        .cells
        .iter()
        .map(|cell| lower_function_context_cell(&mut terms, cell, binding_sorts))
        .collect::<Result<Vec<_>, _>>()?;
    let selected = context
        .cells
        .cells
        .iter()
        .map(|cell| cell.field.cell.clone())
        .collect::<BTreeSet<_>>();
    let omitted_siblings = omitted_leaf_cells(&configuration.declaration, declarations, &selected)?;
    let body = FixedConfigurationPattern::new(
        semantic_origin(
            descriptor,
            context.cells.key.clone(),
            "function-context-cells",
        )?,
        generated_semantic_id("configuration", &context.configuration.configuration, None)?,
        cells,
        omitted_siblings,
    )?;
    Ok((
        krs_ir_levels::SemanticFunctionContext::new(
            semantic_origin(descriptor, context.key.clone(), "function-context")?,
            body,
        ),
        terms.variables,
    ))
}

/// The declaration tables a `cells!` pattern is lowered against.
#[derive(Clone, Copy)]
pub(super) struct StateRuleTables<'a> {
    pub(super) declarations: &'a DescriptorIndex<'a>,
    pub(super) sort_parents: &'a BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    pub(super) catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
}

fn lower_function_context_cell(
    terms: &mut StateRuleTerms<'_>,
    pattern: &DescriptorRuleCell,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<FixedCellPattern<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = terms.descriptor;
    let declared = require_cell_field(&pattern.field.cell, terms.declarations)?;
    let invalid =
        |key: &ProvenanceKey, reason: String| DescriptorLoweringError::InvalidFunctionContext {
            item: Box::new(descriptor.id().clone()),
            reason,
            range: descriptor
                .provenance()
                .origin_for(key)
                .and_then(krs_ir::OriginStack::exact_authored_range)
                .map(Box::new),
        };
    let ProtocolCellContent::Leaf { wrapper, sort, .. } = &declared.content else {
        return Err(invalid(
            &pattern.field.key,
            format!(
                "a function context reads leaf cells, not the whole nested cell `{}`; name the cells inside it",
                pattern.field.cell.field
            ),
        ));
    };
    let cell_sort = semantic_sort_ref(&sort.sort);
    if let ProtocolRuleStateTerm::Term(DescriptorTerm::Variable { key, name, .. }) = &pattern.value
        && let Some(declared) = binding_sorts.get(name)
        && !is_subsort_or_equal(declared, &cell_sort, terms.sort_parents)
    {
        return Err(invalid(
            key,
            format!(
                "the function-context binder `{name}` is declared `{}`, but the cell `{}` holds `{}`",
                super::overload::sort_name(declared),
                pattern.field.cell.field,
                super::overload::sort_name(&cell_sort),
            ),
        ));
    }
    if pattern.wrapper.is_none() {
        return Err(DescriptorLoweringError::invalid_term(
            descriptor.id(),
            format!(
                "the leaf cell entry `{}` needs its `Cell(..)` or `KCell(..)` wrapper",
                pattern.field.cell.field
            ),
        ));
    }
    if pattern.wrapper != Some(*wrapper) {
        return Err(DescriptorLoweringError::ParserReferenceDisagreement {
            id: Box::new(pattern.field.cell.owner.clone()),
            detail: "function-context wrapper disagrees with its cell declaration".into(),
            range: None,
        });
    }
    let term = terms.state_term(
        &pattern.value,
        &cell_sort,
        &pattern.field.key,
        binding_sorts,
        true,
    )?;
    Ok(FixedCellPattern::new(
        semantic_origin(
            descriptor,
            pattern.field.key.clone(),
            "function-context-cell",
        )?,
        semantic_cell_id(&pattern.field.cell)?,
        term,
        lower_subject_cell_frame(descriptor, &pattern.value)?,
    ))
}

/// Whether `sort` is `expected` or one of its subsorts, by the declared
/// subsort relation.
fn is_subsort_or_equal(
    sort: &SemanticSortRef,
    expected: &SemanticSortRef,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> bool {
    let mut pending = vec![sort];
    let mut visited = BTreeSet::new();
    while let Some(current) = pending.pop() {
        if current == expected {
            return true;
        }
        if visited.insert(current) {
            pending.extend(sort_parents.get(current).into_iter().flatten());
        }
    }
    false
}

fn lower_context_alias_cell(
    terms: &mut StateRuleTerms<'_>,
    pattern: &DescriptorRuleCell,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<FixedCellPattern<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = terms.descriptor;
    let declared = require_cell_field(&pattern.field.cell, terms.declarations)?;
    let ProtocolCellContent::Leaf { wrapper, sort, .. } = &declared.content else {
        return Err(DescriptorLoweringError::unsupported_shape(
            "context alias cell",
            "context aliases select leaf cells only",
        ));
    };
    if pattern.wrapper != Some(*wrapper) {
        return Err(DescriptorLoweringError::ParserReferenceDisagreement {
            id: Box::new(pattern.field.cell.owner.clone()),
            detail: "context-alias wrapper disagrees with its cell declaration".into(),
            range: None,
        });
    }
    let term = terms.state_term(
        &pattern.value,
        &semantic_sort_ref(&sort.sort),
        &pattern.field.key,
        binding_sorts,
        true,
    )?;
    Ok(FixedCellPattern::new(
        semantic_origin(descriptor, pattern.field.key.clone(), "context-alias-cell")?,
        semantic_cell_id(&pattern.field.cell)?,
        term,
        lower_subject_cell_frame(descriptor, &pattern.value)?,
    ))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AssociativeStateFamily {
    KSequence,
    Map,
}

#[derive(Clone, Copy, Debug)]
enum AssociativeStateFrame<'a> {
    Anonymous {
        key: &'a ProvenanceKey,
    },
    Bind {
        key: &'a ProvenanceKey,
        binding: &'a str,
    },
    Reuse {
        binding: &'a str,
    },
}

#[derive(Clone, Copy, Debug)]
enum RuleStateFrame<'a> {
    // Exactness is independent of surface notation: an ordinary whole-Map
    // term, `.Map`, exact map items, and a functional update all omit no
    // content. The declared cell sort validates their semantic family.
    Exact,
    Framed {
        family: AssociativeStateFamily,
        frame: AssociativeStateFrame<'a>,
    },
}

fn associative_state_frame(
    family: AssociativeStateFamily,
    frame: &ProtocolRuleFrame,
) -> RuleStateFrame<'_> {
    let frame = match frame {
        ProtocolRuleFrame::Exact => return RuleStateFrame::Exact,
        ProtocolRuleFrame::Anonymous { key } => AssociativeStateFrame::Anonymous { key },
        ProtocolRuleFrame::Bind { key, binding } => AssociativeStateFrame::Bind { key, binding },
        ProtocolRuleFrame::Reuse { binding, .. } => AssociativeStateFrame::Reuse { binding },
    };
    RuleStateFrame::Framed { family, frame }
}

fn rule_state_frame(state: &ProtocolRuleStateTerm<DescriptorTerm>) -> RuleStateFrame<'_> {
    match state {
        ProtocolRuleStateTerm::Term(_)
        | ProtocolRuleStateTerm::Group(_)
        | ProtocolRuleStateTerm::Present { .. }
        | ProtocolRuleStateTerm::Absent
        | ProtocolRuleStateTerm::Instances(_) => RuleStateFrame::Exact,
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
            frame: AssociativeStateFrame::Anonymous { key },
        } => Ok(CellContentFrame::KSequenceTail {
            origin: semantic_origin(descriptor, key.clone(), "rule-k-frame")?,
            binding: None,
        }),
        RuleStateFrame::Framed {
            family: AssociativeStateFamily::KSequence,
            frame: AssociativeStateFrame::Bind { key, binding },
        } => Ok(CellContentFrame::KSequenceTail {
            origin: semantic_origin(descriptor, key.clone(), "rule-k-frame")?,
            binding: Some(SemanticId::new(binding)?),
        }),
        RuleStateFrame::Framed {
            family: AssociativeStateFamily::Map,
            frame: AssociativeStateFrame::Anonymous { key },
        } => Ok(CellContentFrame::MapRemainder {
            origin: semantic_origin(descriptor, key.clone(), "rule-map-frame")?,
            binding: None,
        }),
        RuleStateFrame::Framed {
            family: AssociativeStateFamily::Map,
            frame: AssociativeStateFrame::Bind { key, binding },
        } => Ok(CellContentFrame::MapRemainder {
            origin: semantic_origin(descriptor, key.clone(), "rule-map-frame")?,
            binding: Some(SemanticId::new(binding)?),
        }),
        RuleStateFrame::Framed {
            frame: AssociativeStateFrame::Reuse { .. },
            ..
        } => Err(DescriptorLoweringError::unsupported_shape(
            "subject cell frame",
            "a subject frame cannot reuse a result binding",
        )),
    }
}

/// The computation remainder `tail @ ..` and its frame key when the result
/// writes the computation cell exactly, without `..tail`.
fn moved_computation_remainder<'a>(
    subject: RuleStateFrame<'a>,
    result: RuleStateFrame<'_>,
) -> Option<(&'a str, &'a ProvenanceKey)> {
    match (subject, result) {
        (
            RuleStateFrame::Framed {
                family: AssociativeStateFamily::KSequence,
                frame: AssociativeStateFrame::Bind { key, binding },
            },
            RuleStateFrame::Exact,
        ) => Some((binding, key)),
        _ => None,
    }
}

/// Checks that a leaf cell's subject and result frames agree. A result
/// that does not put a bound computation remainder back writes the cell's
/// whole new content, and the remainder, used elsewhere, has been moved:
/// the pattern it returns ends in the remainder as its last item, and the
/// clause keeps no frame. Moving a map remainder needs the pattern
/// `items Rest` as one term, which the IR's map terms do not have yet.
fn pair_cell_frames(
    terms: &mut StateRuleTerms<'_>,
    cell: &str,
    subject_frame: RuleStateFrame<'_>,
    result_frame: RuleStateFrame<'_>,
    before: &SemanticTerm,
) -> Result<Option<SemanticTerm>, DescriptorLoweringError> {
    let descriptor = terms.descriptor;
    if let Some((tail, key)) = moved_computation_remainder(subject_frame, result_frame) {
        let tail = SemanticId::new(tail)?;
        let moved = with_trailing_item(
            descriptor,
            before,
            SemanticTerm::variable(
                semantic_origin(descriptor, key.clone(), "rule-k-frame")?,
                SemanticSortRef::k_sequence(),
                tail.clone(),
            ),
        )?;
        terms.moved_remainders.push((tail, key.clone()));
        return Ok(Some(moved));
    }
    if let Some(rest) = moved_map_remainder(subject_frame, result_frame) {
        return Err(DescriptorLoweringError::invalid_term(
            descriptor.id(),
            format!(
                "the result writes the whole `{cell}` cell without putting back its map remainder `{rest}`; a rule cannot move a map remainder yet, so keep it with `..{rest}`"
            ),
        ));
    }
    validate_state_frame_pair(
        descriptor,
        subject_frame,
        result_frame,
        "cell content frame",
    )?;
    Ok(None)
}

/// The map remainder `rest @ ..` when the result writes the map cell
/// exactly, without `..rest`.
fn moved_map_remainder<'a>(
    subject: RuleStateFrame<'a>,
    result: RuleStateFrame<'_>,
) -> Option<&'a str> {
    match (subject, result) {
        (
            RuleStateFrame::Framed {
                family: AssociativeStateFamily::Map,
                frame: AssociativeStateFrame::Bind { binding, .. },
            },
            RuleStateFrame::Exact,
        ) => Some(binding),
        _ => None,
    }
}

/// The computation pattern `items` followed by `item`.
fn with_trailing_item(
    descriptor: &Descriptor,
    sequence: &SemanticTerm,
    item: SemanticTerm,
) -> Result<SemanticTerm, DescriptorLoweringError> {
    let IrTermKind::KSequence { items, .. } = sequence.kind() else {
        return Err(DescriptorLoweringError::unsupported_shape(
            "cell content frame",
            format!(
                "rule {} binds a computation remainder outside a computation sequence",
                descriptor.id()
            ),
        ));
    };
    let mut items = items.clone();
    items.push(item);
    Ok(SemanticTerm::k_sequence(
        sequence.origin().clone(),
        SemanticSortRef::k_sequence(),
        items,
    ))
}

/// The moved computation remainders no result term uses.
fn moved_remainders_unused_by(
    terms: &StateRuleTerms<'_>,
    clauses: &[ConfigurationClause<SemanticId, SemanticTerm>],
) -> Vec<SemanticId> {
    terms
        .moved_remainders
        .iter()
        .map(|(tail, _)| tail)
        .filter(|tail| {
            !clauses
                .iter()
                .flat_map(ConfigurationClause::parts)
                .filter_map(|part| part.post_term())
                .any(|term| super::evaluation::mentions(term, tail))
        })
        .cloned()
        .collect()
}

/// A moved computation remainder must be used: in a result term or a
/// condition. A bound remainder the rule neither puts back nor uses would
/// be dropped silently, so it keeps the frame-mismatch error.
fn check_moved_remainders(
    unused: &[SemanticId],
    requires: Option<&SemanticCondition>,
    ensures: Option<&SemanticCondition>,
) -> Result<(), DescriptorLoweringError> {
    for tail in unused {
        let used = requires
            .into_iter()
            .chain(ensures)
            .flat_map(SemanticCondition::terms)
            .any(|term| super::evaluation::mentions(term, tail));
        if !used {
            // A subject rest the result drops: the rest-mismatch mistake, whose code is the
            // bracket notation's.
            return Err(DescriptorLoweringError::CellCollection {
                code: krs_diagnostic::codes::syntax::INVALID_LIST_NOTATION,
                reason: format!(
                    "the subject names the rest of the computation `..{tail}`, and the result neither puts it back with `..{tail}` nor uses it, so the rule would drop it: put it back with `..{tail}`, or use it in a condition"
                ),
                range: None,
                item: None,
            });
        }
    }
    Ok(())
}

fn state_frames_compatible(subject: RuleStateFrame<'_>, result: RuleStateFrame<'_>) -> bool {
    match (subject, result) {
        (
            RuleStateFrame::Exact
            | RuleStateFrame::Framed {
                frame: AssociativeStateFrame::Anonymous { .. },
                ..
            },
            RuleStateFrame::Exact,
        ) => true,
        (
            RuleStateFrame::Framed {
                family: subject_family,
                frame:
                    AssociativeStateFrame::Bind {
                        binding: subject, ..
                    },
            },
            RuleStateFrame::Framed {
                family: result_family,
                frame:
                    AssociativeStateFrame::Reuse {
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
        Err(DescriptorLoweringError::unsupported_shape(
            node,
            format!(
                "rule {} uses incompatible subject/result associative state families or frames",
                descriptor.id()
            ),
        ))
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
        Err(DescriptorLoweringError::unsupported_shape(
            node,
            format!(
                "rule {} uses incompatible subject/result frames",
                descriptor.id()
            ),
        ))
    }
}

fn semantic_terms_equivalent(left: &SemanticTerm, right: &SemanticTerm) -> bool {
    if left.sort() != right.sort() {
        return false;
    }
    match (left.kind(), right.kind()) {
        (
            krs_ir_levels::SemanticTermKind::Variable { variable: left },
            krs_ir_levels::SemanticTermKind::Variable { variable: right },
        ) => left == right,
        (
            krs_ir_levels::SemanticTermKind::Application {
                application: left_application,
                arguments: left_arguments,
                instance: left_instance,
                ..
            },
            krs_ir_levels::SemanticTermKind::Application {
                application: right_application,
                arguments: right_arguments,
                instance: right_instance,
                ..
            },
        ) => {
            left_application == right_application
                && left_instance == right_instance
                && semantic_term_slices_equivalent(left_arguments, right_arguments)
        }
        (
            krs_ir_levels::SemanticTermKind::Token { value: left },
            krs_ir_levels::SemanticTermKind::Token { value: right },
        ) => left == right,
        (
            krs_ir_levels::SemanticTermKind::KSequence {
                item_sort: left_sort,
                items: left_items,
            },
            krs_ir_levels::SemanticTermKind::KSequence {
                item_sort: right_sort,
                items: right_items,
            },
        ) => left_sort == right_sort && semantic_term_slices_equivalent(left_items, right_items),
        (
            krs_ir_levels::SemanticTermKind::Map(left),
            krs_ir_levels::SemanticTermKind::Map(right),
        ) => {
            left.operation() == right.operation()
                && semantic_term_iters_equivalent(left.operands(), right.operands())
        }
        (
            krs_ir_levels::SemanticTermKind::List(left),
            krs_ir_levels::SemanticTermKind::List(right),
        ) => {
            left.operation() == right.operation()
                && semantic_term_iters_equivalent(left.operands(), right.operands())
        }
        (
            krs_ir_levels::SemanticTermKind::Set(left),
            krs_ir_levels::SemanticTermKind::Set(right),
        ) => {
            left.operation() == right.operation()
                && semantic_term_iters_equivalent(left.operands(), right.operands())
        }
        (
            krs_ir_levels::SemanticTermKind::Rewrite {
                from: left_from,
                to: left_to,
            },
            krs_ir_levels::SemanticTermKind::Rewrite {
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

fn semantic_term_iters_equivalent<'a>(
    mut left: impl Iterator<Item = &'a SemanticTerm>,
    mut right: impl Iterator<Item = &'a SemanticTerm>,
) -> bool {
    loop {
        match (left.next(), right.next()) {
            (None, None) => return true,
            (Some(left), Some(right)) if semantic_terms_equivalent(left, right) => {}
            _ => return false,
        }
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

    fn key(role: ProvenanceRole) -> ProvenanceKey {
        ProvenanceKey::new(role, 0)
    }

    fn variable(role: ProvenanceRole) -> DescriptorTerm {
        DescriptorTerm::Variable {
            key: key(role),
            path_key: key(role),
            name: "M".into(),
        }
    }

    fn map(body: ProtocolRuleMapBody<DescriptorTerm>) -> ProtocolRuleStateTerm<DescriptorTerm> {
        ProtocolRuleStateTerm::Map(krs_ir::ProtocolRuleMap {
            payload_key: Some(key(ProvenanceRole::MapPayload)),
            body,
        })
    }

    fn exact_map_items() -> ProtocolRuleStateTerm<DescriptorTerm> {
        map(ProtocolRuleMapBody::Items {
            items: vec![krs_ir::ProtocolRuleMapItem {
                key_key: key(ProvenanceRole::MapKey),
                key: variable(ProvenanceRole::RuleLeftReference),
                value_key: key(ProvenanceRole::MapValue),
                value: variable(ProvenanceRole::RuleRightReference),
            }],
            remainder: ProtocolRuleFrame::Exact,
        })
    }

    #[test]
    fn all_exact_map_forms_share_one_associative_family() {
        let empty = map(ProtocolRuleMapBody::Empty { explicit_dot: true });
        let items = exact_map_items();
        let update = map(ProtocolRuleMapBody::Update {
            base_key: key(ProvenanceRole::MapUpdateBase),
            base: variable(ProvenanceRole::TermReference),
            key_key: key(ProvenanceRole::RuleRightMapKey),
            key: variable(ProvenanceRole::RuleRequiresReference),
            value_key: key(ProvenanceRole::RuleRightMapValue),
            value: variable(ProvenanceRole::ClaimEnsuresReference),
        });
        let whole_map_term =
            ProtocolRuleStateTerm::Term(variable(ProvenanceRole::ClaimEnsuresPath));

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
            payload_key: Some(key(ProvenanceRole::KSequencePayload)),
            dot_k_key: None,
            notation: krs_ir::DescriptorKSequenceNotation::Comma,
            items: Vec::new(),
            tail: ProtocolRuleFrame::Bind {
                key: key(ProvenanceRole::KSequenceTail),
                binding: "REST".into(),
            },
        });
        let framed_map = map(ProtocolRuleMapBody::Items {
            items: vec![krs_ir::ProtocolRuleMapItem {
                key_key: key(ProvenanceRole::MapKey),
                key: variable(ProvenanceRole::RuleLeftReference),
                value_key: key(ProvenanceRole::MapValue),
                value: variable(ProvenanceRole::RuleRightReference),
            }],
            remainder: ProtocolRuleFrame::Reuse {
                key: key(ProvenanceRole::MapRemainder),
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

    /// A bound remainder whose result is written exactly is moved: the
    /// computation remainder becomes the subject's last item, and a map
    /// remainder is reported.
    #[test]
    fn a_bound_remainder_with_an_exact_result_is_moved() {
        let framed_k = ProtocolRuleStateTerm::KSequence(krs_ir::ProtocolRuleKSequence {
            payload_key: Some(key(ProvenanceRole::KSequencePayload)),
            dot_k_key: None,
            notation: krs_ir::DescriptorKSequenceNotation::Comma,
            items: Vec::new(),
            tail: ProtocolRuleFrame::Bind {
                key: key(ProvenanceRole::KSequenceTail),
                binding: "tail".into(),
            },
        });
        let exact_k = ProtocolRuleStateTerm::KSequence(krs_ir::ProtocolRuleKSequence {
            payload_key: Some(key(ProvenanceRole::KSequencePayload)),
            dot_k_key: None,
            notation: krs_ir::DescriptorKSequenceNotation::Comma,
            items: Vec::new(),
            tail: ProtocolRuleFrame::Exact,
        });
        let framed_map = map(ProtocolRuleMapBody::Items {
            items: vec![krs_ir::ProtocolRuleMapItem {
                key_key: key(ProvenanceRole::MapKey),
                key: variable(ProvenanceRole::RuleLeftReference),
                value_key: key(ProvenanceRole::MapValue),
                value: variable(ProvenanceRole::RuleRightReference),
            }],
            remainder: ProtocolRuleFrame::Bind {
                key: key(ProvenanceRole::MapRemainder),
                binding: "rest".into(),
            },
        });
        let empty = map(ProtocolRuleMapBody::Empty { explicit_dot: true });

        assert_eq!(
            moved_computation_remainder(rule_state_frame(&framed_k), rule_state_frame(&exact_k))
                .map(|(binding, _)| binding),
            Some("tail")
        );
        assert!(
            moved_computation_remainder(rule_state_frame(&framed_k), rule_state_frame(&framed_k))
                .is_none()
        );
        assert_eq!(
            moved_map_remainder(rule_state_frame(&framed_map), rule_state_frame(&empty)),
            Some("rest")
        );
        assert!(
            moved_computation_remainder(rule_state_frame(&framed_map), rule_state_frame(&empty))
                .is_none()
        );
    }
}

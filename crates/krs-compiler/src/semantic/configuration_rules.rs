use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    BuiltinSort, CellContentFrame, CellPost, Descriptor, DescriptorCellReference, DescriptorClaim,
    DescriptorClaimBinder, DescriptorTerm, FixedCellClause, FixedCellPattern,
    FixedConfigurationPattern, FixedConfigurationRewrite, ItemKind, MapOperation,
    ProtocolCellContent, ProtocolContextAliasBindingKind, ProtocolRuleBindingKind,
    ProtocolRuleCell, ProtocolRuleFrame, ProtocolRuleMapBody, ProtocolRuleStateTerm, ProvenanceKey,
    SemanticContextAlias, SemanticId, SemanticRule, SemanticRuleCondition, SemanticSortRef,
    SemanticTerm, SemanticVariable, StableItemId,
};
use krs_syntax::ProvenanceRole;

use super::catalog::{ProductionSignature, common_sequence_item_sort, semantic_sort_ref};
use super::error::DescriptorLoweringError;
use super::infer::{StructuredTermBuilder, initial_binding_constraints};
use super::origin::{generated_semantic_id, role_key, semantic_cell_id, semantic_origin};
use super::references::require_cell_field;
use super::rules::{
    framework_k_item_sort, lower_rule_label, lower_rule_priority, omitted_leaf_cells,
    require_fixed_configuration,
};

/// Stable rule cell as transported for configuration rules and context aliases.
type DescriptorRuleCell = ProtocolRuleCell<DescriptorCellReference, DescriptorTerm>;

/// Shared inputs for lowering the cell terms of one configuration rule or
/// context alias, and the variables those terms introduce, in order.
struct StateRuleTerms<'a> {
    descriptor: &'a Descriptor,
    declarations: &'a BTreeMap<StableItemId, &'a Descriptor>,
    sort_parents: &'a BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    wildcard_ordinal: usize,
    variables: Vec<SemanticVariable>,
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
            wildcard_offset: self.wildcard_ordinal,
            wildcards: Vec::new(),
        };
        builder.infer(term, expected_sort, subject)?;
        builder.resolve_binding_sorts()?;
        let lowered = builder.lower(term, expected_sort, subject)?;
        self.wildcard_ordinal += builder.wildcards.len();
        self.variables.append(&mut builder.wildcards);
        Ok(lowered)
    }

    /// Lowers one cell's state term: an ordinary term, a K sequence, or a map.
    fn state_term(
        &mut self,
        state: &ProtocolRuleStateTerm<DescriptorTerm>,
        declared_sort: &SemanticSortRef,
        fallback_key: &ProvenanceKey,
        binding_sorts: &BTreeMap<String, SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let descriptor = self.descriptor;
        match state {
            ProtocolRuleStateTerm::Term(term) => {
                self.term(term, Some(declared_sort), binding_sorts, subject)
            }
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
                    .map(|item| self.term(&item.value, None, binding_sorts, subject))
                    .collect::<Result<Vec<_>, _>>()?;
                let item_sort = common_sequence_item_sort(descriptor, &items, self.sort_parents)?;
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
                            arguments.push(self.term(&item.key, None, binding_sorts, subject)?);
                            arguments.push(self.term(&item.value, None, binding_sorts, subject)?);
                        }
                        (MapOperation::Item, arguments)
                    }
                    ProtocolRuleMapBody::Update {
                        base, key, value, ..
                    } => (
                        MapOperation::Update,
                        vec![
                            self.term(base, Some(&SemanticSortRef::map()), binding_sorts, subject)?,
                            self.term(key, None, binding_sorts, subject)?,
                            self.term(value, None, binding_sorts, subject)?,
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
}

/// Binding sorts visible to a configuration rule's subject and result, and the
/// declared variables in binding order followed by claim existentials.
struct ConfigurationRuleBindings {
    subject_sorts: BTreeMap<String, SemanticSortRef>,
    result_sorts: BTreeMap<String, SemanticSortRef>,
    variables: Vec<SemanticVariable>,
}

fn configuration_rule_bindings(
    rule: &krs_ir::DescriptorConfigurationRule,
) -> Result<ConfigurationRuleBindings, DescriptorLoweringError> {
    let mut subject_sorts = BTreeMap::new();
    let mut variables = Vec::new();
    for binding in &rule.bindings {
        let sort = match &binding.kind {
            ProtocolRuleBindingKind::Term { sort } => semantic_sort_ref(&sort.sort),
            ProtocolRuleBindingKind::KSequenceFrame => SemanticSortRef::k_sequence(),
            ProtocolRuleBindingKind::MapFrame => SemanticSortRef::map(),
            ProtocolRuleBindingKind::ConfigurationFrame => continue,
        };
        if matches!(binding.kind, ProtocolRuleBindingKind::Term { .. }) {
            subject_sorts.insert(binding.name.clone(), sort.clone());
        }
        variables.push(SemanticVariable::new(
            SemanticId::new(binding.name.clone())?,
            sort,
        ));
    }
    let mut result_sorts = subject_sorts.clone();
    if let Some(claim) = &rule.claim {
        for binder in &claim.existentials {
            let sort = semantic_sort_ref(&binder.sort.sort);
            result_sorts.insert(binder.name.clone(), sort.clone());
            variables.push(SemanticVariable::new(
                SemanticId::new(binder.name.clone())?,
                sort,
            ));
        }
    }
    Ok(ConfigurationRuleBindings {
        subject_sorts,
        result_sorts,
        variables,
    })
}

pub(super) fn lower_configuration_rule_descriptor(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorConfigurationRule,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
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
        variables,
    } = configuration_rule_bindings(rule)?;
    let mut terms = StateRuleTerms {
        descriptor,
        declarations,
        sort_parents,
        catalog,
        wildcard_ordinal: 0,
        variables,
    };
    let clauses =
        lower_configuration_rule_clauses(&mut terms, rule, &subject_sorts, &result_sorts)?;

    let selected = rule
        .subject
        .cells
        .iter()
        .map(|cell| cell.field.cell.clone())
        .collect::<BTreeSet<_>>();
    let omitted_siblings = omitted_leaf_cells(&configuration.declaration, declarations, &selected)?;
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
                terms.term(&condition.term, Some(&bool_sort), &subject_sorts, false)?,
            ))
        })
        .transpose()?;
    let priority = lower_rule_priority(descriptor, rule.priority.as_ref(), "rule-owise")?;
    let claim = rule
        .claim
        .as_ref()
        .map(|claim| lower_rule_claim(&mut terms, claim, &result_sorts))
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
        terms.variables,
        body,
    )?
    .with_label(lower_rule_label(descriptor, rule.label.as_ref())?)
    .with_priority(priority)?
    .with_requires(requires)?
    .with_claim(claim))
}

/// Checks that the result selects only subject cells and that the remainder
/// frames agree, then lowers one clause per subject cell.
fn lower_configuration_rule_clauses(
    terms: &mut StateRuleTerms<'_>,
    rule: &krs_ir::DescriptorConfigurationRule,
    subject_sorts: &BTreeMap<String, SemanticSortRef>,
    result_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<Vec<FixedCellClause<SemanticId, SemanticTerm>>, DescriptorLoweringError> {
    let subject_cells = rule
        .subject
        .cells
        .iter()
        .map(|cell| &cell.field.cell)
        .collect::<BTreeSet<_>>();
    let result_cells = rule
        .result
        .cells
        .iter()
        .map(|cell| (&cell.field.cell, cell))
        .collect::<BTreeMap<_, _>>();
    if result_cells
        .keys()
        .any(|identity| !subject_cells.contains(identity))
    {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "configuration rule",
            detail: "the result selects a fixed cell absent from the subject".into(),
        });
    }
    validate_frame_pair(
        terms.descriptor,
        &rule.subject.remainder,
        &rule.result.remainder,
        "configuration remainder",
    )?;
    rule.subject
        .cells
        .iter()
        .map(|subject| {
            let result = result_cells.get(&subject.field.cell).copied();
            lower_configuration_rule_clause(terms, subject, result, subject_sorts, result_sorts)
        })
        .collect()
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
    let ProtocolCellContent::Leaf { wrapper, sort, .. } = &declared.content else {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "configuration rule cell",
            detail: "rules over nominal parent cells are not represented by fixed-cell clauses"
                .into(),
        });
    };
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
    let before = terms.state_term(
        &subject.value,
        &declared_sort,
        &subject.field.key,
        subject_sorts,
        true,
    )?;
    let subject_frame = rule_state_frame(&subject.value);
    let frame = lower_subject_cell_frame(descriptor, &subject.value)?;
    let post = if let Some(result) = result {
        let after = terms.state_term(
            &result.value,
            &declared_sort,
            &result.field.key,
            result_sorts,
            false,
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
    Ok(FixedCellClause::new(
        semantic_origin(descriptor, subject.field.key.clone(), "rule-cell-clause")?,
        semantic_cell_id(&subject.field.cell)?,
        before,
        post,
        frame,
    ))
}

fn lower_rule_claim(
    terms: &mut StateRuleTerms<'_>,
    claim: &DescriptorClaim,
    result_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<krs_ir::SemanticClaim, DescriptorLoweringError> {
    let descriptor = terms.descriptor;
    let universals = claim
        .universals
        .iter()
        .map(|binder| lower_claim_binder(descriptor, binder, "claim-universal-binder"))
        .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
    let existentials = claim
        .existentials
        .iter()
        .map(|binder| lower_claim_binder(descriptor, binder, "claim-existential-binder"))
        .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
    let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
    let ensures = claim
        .ensures
        .as_ref()
        .map(|condition| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRuleCondition::new(
                semantic_origin(descriptor, condition.key.clone(), "claim-ensures")?,
                terms.term(&condition.term, Some(&bool_sort), result_sorts, false)?,
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
}

fn lower_claim_binder(
    descriptor: &Descriptor,
    binder: &DescriptorClaimBinder,
    role: &str,
) -> Result<krs_ir::SemanticClaimBinder, DescriptorLoweringError> {
    Ok(krs_ir::SemanticClaimBinder::new(
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
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
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
    let mut terms = StateRuleTerms {
        descriptor,
        declarations,
        sort_parents,
        catalog,
        wildcard_ordinal: 0,
        variables,
    };
    let cells = alias
        .pattern
        .cells
        .iter()
        .map(|pattern| lower_context_alias_cell(&mut terms, pattern, &binding_sorts))
        .collect::<Result<Vec<_>, _>>()?;
    let selected = alias
        .pattern
        .cells
        .iter()
        .map(|cell| cell.field.cell.clone())
        .collect::<BTreeSet<_>>();
    let omitted_siblings = omitted_leaf_cells(&configuration.declaration, declarations, &selected)?;
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
        terms.variables,
        body,
    ))
}

fn lower_context_alias_cell(
    terms: &mut StateRuleTerms<'_>,
    pattern: &DescriptorRuleCell,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<FixedCellPattern<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let descriptor = terms.descriptor;
    let declared = require_cell_field(&pattern.field.cell, terms.declarations)?;
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

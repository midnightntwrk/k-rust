//! Stable configuration descriptors reach the existing semantic/Definition lane.

use krs_ir::testing::{DescriptorBundleInputs, DescriptorInputs};

use std::collections::{BTreeMap, BTreeSet};

use krs_compiler::lower_descriptor_bundle;
use krs_compiler::testing::assert_lowering_contract;
use krs_ir::testing;
use krs_ir::testing::assert_canonical_contract;
use krs_ir::{
    BuiltinSort, CellStream, CellWrapper, DescriptorCellExit, DescriptorCellField,
    DescriptorCellIdentity, DescriptorCellReference, DescriptorCellStream,
    DescriptorConfigurationDeclaration, DescriptorConfigurationInitializer,
    DescriptorConfigurationReference, DescriptorConfigurationRoot, DescriptorConfigurationRule,
    DescriptorConfigurationVariable, DescriptorFixedConfiguration, DescriptorInitializerCell,
    DescriptorNodeOrigin, DescriptorPayload, DescriptorProvenance, DescriptorRuleBinding,
    DescriptorRuleCells, DescriptorSortRef, DescriptorSortReference, DescriptorTerm, ItemKind,
    PackageId, ProtocolCellContent, ProtocolConfigurationVariable, ProtocolInitializerCellContent,
    ProtocolInitializerStateTerm, ProtocolInitializerTerm, ProtocolKSequence,
    ProtocolKSequenceItem, ProtocolRuleBinding, ProtocolRuleBindingKind, ProtocolRuleCell,
    ProtocolRuleFrame, ProtocolRuleKSequence, ProtocolRuleKSequenceItem, ProtocolRuleMap,
    ProtocolRuleMapBody, ProtocolRuleMapItem, ProtocolRuleStateTerm, ProvenanceKey, ProvenanceRole,
    RuleSide, SortDescriptor, StableItemId,
};

fn package() -> PackageId {
    testing::package("KRS-STATE", "state")
}

fn id(name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), "calc", name, kind)
}

fn framework_kitem() -> StableItemId {
    testing::item_in(
        testing::package_with("KRS-FRAMEWORK", "krs", "0.1.0", "framework"),
        "framework",
        "KItem",
        ItemKind::Sort,
    )
}

fn key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal)
}

fn provenance(
    primary: ProvenanceKey,
    keys: impl IntoIterator<Item = ProvenanceKey>,
) -> DescriptorProvenance {
    let mut keys = std::iter::once(primary.clone())
        .chain(keys)
        .collect::<Vec<_>>();
    keys.sort();
    keys.dedup();
    DescriptorProvenance::new(
        primary,
        keys.into_iter()
            .enumerate()
            .map(|(index, key)| {
                let start = u32::try_from(index).unwrap();
                DescriptorNodeOrigin::new(
                    key,
                    testing::authored_in(
                        package(),
                        "src/calc.rs",
                        testing::digest_with("7".repeat(64)),
                        start,
                        start + 1,
                    ),
                )
            })
            .collect(),
    )
    .unwrap()
}

fn sort_ref(
    role: ProvenanceRole,
    ordinal: u32,
    sort: DescriptorSortRef,
) -> DescriptorSortReference {
    DescriptorSortReference {
        key: key(role, ordinal),
        sort,
    }
}

fn cell_field(
    owner: &StableItemId,
    ordinal: u32,
    name: &str,
    wrapper: CellWrapper,
    sort: BuiltinSort,
) -> DescriptorCellField {
    DescriptorCellField {
        reference: DescriptorCellReference {
            key: key(ProvenanceRole::ConfigurationField, ordinal),
            cell: DescriptorCellIdentity {
                owner: owner.clone(),
                field: name.into(),
            },
        },
        rust_field: name.into(),
        emitted_name: None,
        color: None,
        multiplicity: None,
        cell_type: None,
        stream: None,
        exit: None,
        content: ProtocolCellContent::Leaf {
            wrapper_key: key(ProvenanceRole::ConfigurationCellWrapper, ordinal),
            wrapper,
            sort: sort_ref(
                ProvenanceRole::ConfigurationCellContent,
                ordinal,
                DescriptorSortRef::Builtin(sort),
            ),
            arguments: Vec::new(),
        },
    }
}

fn initializer_variable(
    ordinal: u32,
    binding: &str,
    external: &str,
    sort: BuiltinSort,
    main: bool,
) -> DescriptorConfigurationVariable {
    ProtocolConfigurationVariable {
        binding_key: key(ProvenanceRole::ConfigurationVariable, ordinal),
        binding: binding.into(),
        external_name_key: key(ProvenanceRole::ConfigurationVariableName, ordinal),
        external_name: external.into(),
        sort: sort_ref(
            ProvenanceRole::ConfigurationVariableType,
            ordinal,
            DescriptorSortRef::Builtin(sort),
        ),
        main_key: main.then(|| key(ProvenanceRole::ConfigurationVariableMain, ordinal)),
    }
}

fn variable(role: ProvenanceRole, ordinal: u32, name: &str) -> DescriptorTerm {
    let key = key(role, ordinal);
    DescriptorTerm::Variable {
        key: key.clone(),
        path_key: key,
        name: name.into(),
    }
}

fn fixed_configuration() -> (StableItemId, DescriptorFixedConfiguration) {
    let owner = id("Machine", ItemKind::Configuration);
    let k = cell_field(&owner, 0, "k", CellWrapper::KCell, BuiltinSort::KSequence);
    let env = cell_field(&owner, 1, "env", CellWrapper::Cell, BuiltinSort::Map);
    let configuration = DescriptorFixedConfiguration {
        root: DescriptorConfigurationRoot::GeneratedTop,
        declaration: DescriptorConfigurationDeclaration {
            key: key(ProvenanceRole::ConfigurationDeclaration, 0),
            fields: vec![k.clone(), env.clone()],
        },
        initializer: DescriptorConfigurationInitializer {
            key: key(ProvenanceRole::InitializerDeclaration, 0),
            owner_key: key(ProvenanceRole::InitializerResultType, 0),
            owner: owner.clone(),
            variables: vec![
                initializer_variable(0, "pgm", "PGM", BuiltinSort::Id, true),
                initializer_variable(1, "env", "ENV", BuiltinSort::Map, false),
            ],
            body_key: key(ProvenanceRole::InitializerBody, 0),
            cells: vec![
                DescriptorInitializerCell {
                    key: key(ProvenanceRole::InitializerCell, 0),
                    field: DescriptorCellReference {
                        key: key(ProvenanceRole::InitializerField, 0),
                        cell: k.reference.cell,
                    },
                    content: ProtocolInitializerCellContent::Leaf {
                        constructor_key: key(ProvenanceRole::InitializerCellConstructor, 0),
                        wrapper: CellWrapper::KCell,
                        value: ProtocolInitializerStateTerm::KSequence(ProtocolKSequence {
                            payload_key: Some(key(ProvenanceRole::KSequencePayload, 0)),
                            dot_k_key: None,
                            notation: krs_ir::DescriptorKSequenceNotation::Comma,
                            items: vec![ProtocolKSequenceItem {
                                key: key(ProvenanceRole::KSequenceItem, 0),
                                value: ProtocolInitializerTerm {
                                    key: key(ProvenanceRole::InitializerTerm, 0),
                                    term: variable(ProvenanceRole::InitializerTermPath, 0, "pgm"),
                                },
                            }],
                        }),
                    },
                },
                DescriptorInitializerCell {
                    key: key(ProvenanceRole::InitializerCell, 1),
                    field: DescriptorCellReference {
                        key: key(ProvenanceRole::InitializerField, 1),
                        cell: env.reference.cell,
                    },
                    content: ProtocolInitializerCellContent::Leaf {
                        constructor_key: key(ProvenanceRole::InitializerCellConstructor, 1),
                        wrapper: CellWrapper::Cell,
                        value: ProtocolInitializerStateTerm::Term(ProtocolInitializerTerm {
                            key: key(ProvenanceRole::InitializerTerm, 1),
                            term: variable(ProvenanceRole::InitializerTermPath, 1, "env"),
                        }),
                    },
                },
            ],
        },
    };
    (owner, configuration)
}

fn rule_cell(
    owner: &StableItemId,
    side: RuleSide,
    ordinal: u32,
    name: &str,
    wrapper: CellWrapper,
    value: ProtocolRuleStateTerm<DescriptorTerm>,
) -> ProtocolRuleCell<DescriptorCellReference, DescriptorTerm> {
    ProtocolRuleCell {
        field: DescriptorCellReference {
            key: key(
                side_role(
                    side,
                    ProvenanceRole::RuleLeftCellsField,
                    ProvenanceRole::RuleRightCellsField,
                ),
                ordinal,
            ),
            cell: DescriptorCellIdentity {
                owner: owner.clone(),
                field: name.into(),
            },
        },
        wrapper_key: Some(key(
            side_role(
                side,
                ProvenanceRole::RuleLeftCellsWrapper,
                ProvenanceRole::RuleRightCellsWrapper,
            ),
            ordinal,
        )),
        wrapper: Some(wrapper),
        value,
    }
}

fn side_role(side: RuleSide, left: ProvenanceRole, right: ProvenanceRole) -> ProvenanceRole {
    match side {
        RuleSide::Left => left,
        RuleSide::Right => right,
    }
}

fn term_binding(name: &str, ordinal: u32, sort: DescriptorSortRef) -> DescriptorRuleBinding {
    ProtocolRuleBinding {
        name: name.into(),
        kind: ProtocolRuleBindingKind::Term {
            sort: sort_ref(ProvenanceRole::RuleBindingType, ordinal, sort),
        },
    }
}

fn frame_binding(
    name: &str,
    kind: ProtocolRuleBindingKind<DescriptorSortReference>,
) -> DescriptorRuleBinding {
    ProtocolRuleBinding {
        name: name.into(),
        kind,
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "Builds both sides and provenance of the configuration rule fixture together."
)]
fn configuration_rule(owner: &StableItemId) -> DescriptorConfigurationRule {
    let k_state = |side: RuleSide, value: &str, tail| {
        ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
            payload_key: Some(key(
                side_role(
                    side,
                    ProvenanceRole::RuleLeftKSequencePayload,
                    ProvenanceRole::RuleRightKSequencePayload,
                ),
                0,
            )),
            dot_k_key: None,
            notation: krs_ir::DescriptorKSequenceNotation::Comma,
            items: vec![ProtocolRuleKSequenceItem {
                key: key(
                    side_role(
                        side,
                        ProvenanceRole::RuleLeftKSequenceItem,
                        ProvenanceRole::RuleRightKSequenceItem,
                    ),
                    0,
                ),
                value: variable(
                    side_role(
                        side,
                        ProvenanceRole::RuleLeftReference,
                        ProvenanceRole::RuleRightReference,
                    ),
                    0,
                    value,
                ),
            }],
            tail,
        })
    };
    DescriptorConfigurationRule {
        sentence_kind: krs_ir::ConfigurationSentenceKind::Transition,
        label: None,
        priority: None,
        nondet: None,
        requires: None,
        claim: None,
        pattern_key: key(ProvenanceRole::RulePattern, 0),
        subject_configuration: DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleType, 0),
            configuration: owner.clone(),
        },
        result_key: key(ProvenanceRole::RuleResult, 0),
        result_configuration: DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleResultType, 0),
            configuration: owner.clone(),
        },
        bindings: vec![
            term_binding("X", 0, DescriptorSortRef::Builtin(BuiltinSort::Id)),
            frame_binding("tail", ProtocolRuleBindingKind::KSequenceFrame),
            term_binding(
                "V",
                1,
                DescriptorSortRef::Declared(id("Value", ItemKind::Sort)),
            ),
            frame_binding("rest", ProtocolRuleBindingKind::MapFrame),
            frame_binding("state", ProtocolRuleBindingKind::ConfigurationFrame),
        ],
        subject: DescriptorRuleCells {
            key: key(ProvenanceRole::RuleLeftCellsPayload, 0),
            cells: vec![
                rule_cell(
                    owner,
                    RuleSide::Left,
                    0,
                    "k",
                    CellWrapper::KCell,
                    k_state(
                        RuleSide::Left,
                        "X",
                        ProtocolRuleFrame::Bind {
                            key: key(ProvenanceRole::RuleLeftKSequenceTail, 0),
                            binding: "tail".into(),
                        },
                    ),
                ),
                rule_cell(
                    owner,
                    RuleSide::Left,
                    1,
                    "env",
                    CellWrapper::Cell,
                    ProtocolRuleStateTerm::Map(ProtocolRuleMap {
                        payload_key: Some(key(ProvenanceRole::RuleLeftMapPayload, 0)),
                        body: ProtocolRuleMapBody::Items {
                            items: vec![ProtocolRuleMapItem {
                                key_key: key(ProvenanceRole::RuleLeftMapKey, 0),
                                key: variable(ProvenanceRole::RuleLeftReference, 1, "X"),
                                value_key: key(ProvenanceRole::RuleLeftMapValue, 0),
                                value: variable(ProvenanceRole::RuleLeftReference, 2, "V"),
                            }],
                            remainder: ProtocolRuleFrame::Bind {
                                key: key(ProvenanceRole::RuleLeftMapRemainder, 0),
                                binding: "rest".into(),
                            },
                        },
                    }),
                ),
            ],
            remainder: ProtocolRuleFrame::Bind {
                key: key(ProvenanceRole::RuleLeftCellsRemainder, 0),
                binding: "state".into(),
            },
        },
        result: DescriptorRuleCells {
            key: key(ProvenanceRole::RuleRightCellsPayload, 0),
            cells: vec![rule_cell(
                owner,
                RuleSide::Right,
                0,
                "k",
                CellWrapper::KCell,
                k_state(
                    RuleSide::Right,
                    "V",
                    ProtocolRuleFrame::Reuse {
                        key: key(ProvenanceRole::RuleRightKSequenceTail, 0),
                        binding: "tail".into(),
                    },
                ),
            )],
            remainder: ProtocolRuleFrame::Reuse {
                key: key(ProvenanceRole::RuleRightCellsRemainder, 0),
                binding: "state".into(),
            },
        },
        existentials: Vec::new(),
        ensures: None,
        fresh: Vec::new(),
    }
}

fn descriptor(id: StableItemId, payload: DescriptorPayload) -> DescriptorInputs {
    let keys = match &payload {
        DescriptorPayload::Sort(_) => vec![key(ProvenanceRole::SortDeclaration, 0)],
        DescriptorPayload::FixedConfiguration(configuration) => configuration
            .expected_provenance_keys(&id)
            .unwrap()
            .into_iter()
            .collect(),
        DescriptorPayload::ConfigurationRule(rule) => rule
            .expected_provenance_keys(id.item_kind())
            .unwrap()
            .into_iter()
            .collect(),
        _ => unreachable!(),
    };
    let primary = match payload {
        DescriptorPayload::Sort(_) => key(ProvenanceRole::SortDeclaration, 0),
        DescriptorPayload::FixedConfiguration(_) => {
            key(ProvenanceRole::ConfigurationDeclaration, 0)
        }
        DescriptorPayload::ConfigurationRule(_) => key(ProvenanceRole::RuleDeclaration, 0),
        _ => unreachable!(),
    };
    DescriptorInputs::new(id, BTreeMap::new(), provenance(primary, keys), payload)
}

fn bundle() -> DescriptorBundleInputs {
    let (owner, configuration) = fixed_configuration();
    let rule = configuration_rule(&owner);
    DescriptorBundleInputs::new(vec![
        descriptor(
            framework_kitem(),
            DescriptorPayload::Sort(SortDescriptor {
                parents: BTreeSet::new(),
            }),
        ),
        descriptor(
            id("Value", ItemKind::Sort),
            DescriptorPayload::Sort(SortDescriptor {
                parents: BTreeSet::new(),
            }),
        ),
        descriptor(
            owner,
            DescriptorPayload::FixedConfiguration(Box::new(configuration)),
        ),
        descriptor(
            id("var", ItemKind::Rule),
            DescriptorPayload::ConfigurationRule(Box::new(rule)),
        ),
    ])
}

fn refresh_rule_provenance(bundle: &mut DescriptorBundleInputs) {
    let expected = bundle
        .descriptors
        .iter()
        .find_map(|descriptor| match &descriptor.payload {
            DescriptorPayload::ConfigurationRule(rule) => {
                Some(rule.expected_provenance_keys(ItemKind::Rule).unwrap())
            }
            _ => None,
        })
        .unwrap();
    let mut descriptors = bundle.descriptors.clone();
    let descriptor = descriptors
        .iter_mut()
        .find(|descriptor| matches!(&descriptor.payload, DescriptorPayload::ConfigurationRule(_)))
        .unwrap();
    descriptor.provenance = provenance(key(ProvenanceRole::RuleDeclaration, 0), expected);
    bundle.descriptors = descriptors;
}

#[test]
fn fixed_configuration_and_simultaneous_rule_reach_emitted_k_deterministically() {
    let bundle = bundle();
    assert_canonical_contract(&bundle.build().unwrap());
    let semantic = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap();
    let module = semantic
        .modules()
        .iter()
        .find(|module| !module.rules().is_empty())
        .unwrap();
    let krs_ir_levels::RuleBodyRef::Configuration { body: rule, .. } =
        module.rules()[0].relational_body()
    else {
        panic!("a configuration rule must remain a simultaneous configuration rewrite");
    };
    assert_eq!(rule.clauses().len(), 2);
    assert!(matches!(
        rule.clauses()[1].after(),
        krs_ir::CellPost::Preserve
    ));
    let (_lowered, emitted) = assert_lowering_contract(&semantic);
    let source = emitted.source();
    assert!(source.contains("configuration"));
    assert!(source.contains("<k>"));
    assert!(source.contains("<env>"));
    assert!(source.contains("rule ["));
    assert!(source.contains(":Map"));
}

#[test]
fn exact_empty_map_can_rewrite_to_exact_map_items() {
    let mut bundle = bundle();
    let mut descriptors = bundle.descriptors.clone();
    let rule = descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::ConfigurationRule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.subject.cells[1].value = ProtocolRuleStateTerm::Map(ProtocolRuleMap {
        payload_key: Some(key(ProvenanceRole::RuleLeftMapPayload, 0)),
        body: ProtocolRuleMapBody::Empty { explicit_dot: true },
    });
    let ProtocolRuleStateTerm::KSequence(result_k) = &mut rule.result.cells[0].value else {
        unreachable!();
    };
    result_k.items[0].value = variable(ProvenanceRole::RuleRightReference, 0, "X");
    let owner = rule.subject_configuration.configuration.clone();
    rule.result.cells.push(rule_cell(
        &owner,
        RuleSide::Right,
        1,
        "env",
        CellWrapper::Cell,
        ProtocolRuleStateTerm::Map(ProtocolRuleMap {
            payload_key: Some(key(ProvenanceRole::RuleRightMapPayload, 0)),
            body: ProtocolRuleMapBody::Items {
                items: vec![ProtocolRuleMapItem {
                    key_key: key(ProvenanceRole::RuleRightMapKey, 0),
                    key: variable(ProvenanceRole::RuleRightReference, 1, "X"),
                    value_key: key(ProvenanceRole::RuleRightMapValue, 0),
                    value: variable(ProvenanceRole::RuleRightReference, 2, "X"),
                }],
                remainder: ProtocolRuleFrame::Exact,
            },
        }),
    ));
    rule.bindings
        .retain(|binding| matches!(binding.name.as_str(), "X" | "tail" | "state"));
    bundle.descriptors = descriptors;
    refresh_rule_provenance(&mut bundle);
    assert_canonical_contract(&bundle.build().unwrap());
    let semantic = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap();
    let module = semantic
        .modules()
        .iter()
        .find(|module| !module.rules().is_empty())
        .unwrap();
    let krs_ir_levels::RuleBodyRef::Configuration { body: rewrite, .. } =
        module.rules()[0].relational_body()
    else {
        panic!("a configuration rule must remain a simultaneous configuration rewrite");
    };
    let env = &rewrite.clauses()[1];
    assert!(matches!(env.frame(), krs_ir::CellContentFrame::Exact));
    assert!(matches!(
        env.before().kind(),
        krs_ir_levels::semantic::SemanticTermKind::Map(operands)
            if matches!(operands.as_ref(), krs_ir_levels::MapOperands::Empty)
    ));
    assert!(matches!(
        env.after(),
        krs_ir::CellPost::Replace { term }
            if matches!(
                term.kind(),
                krs_ir_levels::semantic::SemanticTermKind::Map(operands)
                    if matches!(operands.as_ref(), krs_ir_levels::MapOperands::Items(entries) if entries.len() == 1)
            )
    ));

    let (_, emitted) = assert_lowering_contract(&semantic);
    assert!(emitted.source().contains(".Map =>"));
    assert!(emitted.source().contains("|->"));
}

#[test]
fn result_only_cell_is_rejected_before_configuration_lowering() {
    let mut bundle = bundle();
    let mut descriptors = bundle.descriptors.clone();
    let rule = descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::ConfigurationRule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.subject.cells.truncate(1);
    rule.result.cells[0].field.cell.field = "env".into();
    let ProtocolRuleStateTerm::KSequence(sequence) = &mut rule.result.cells[0].value else {
        unreachable!();
    };
    sequence.items[0].value = variable(ProvenanceRole::RuleRightReference, 0, "X");
    rule.bindings
        .retain(|binding| matches!(binding.name.as_str(), "X" | "tail" | "state"));
    let expected_keys = rule.expected_provenance_keys(ItemKind::Rule).unwrap();
    let descriptor = descriptors
        .iter_mut()
        .find(|descriptor| matches!(&descriptor.payload, DescriptorPayload::ConfigurationRule(_)))
        .unwrap();
    descriptor.provenance = provenance(key(ProvenanceRole::RuleDeclaration, 0), expected_keys);
    bundle.descriptors = descriptors;
    let error = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("result selects a fixed cell absent from the subject"),
        "unexpected error: {error}"
    );
}

#[test]
fn unknown_owner_qualified_cell_reference_fails_typed() {
    let mut bundle = bundle();
    let mut descriptors = bundle.descriptors.clone();
    let rule = descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::ConfigurationRule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.subject.cells[0].field.cell.field = "missing".into();
    bundle.descriptors = descriptors;
    let error = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap_err();
    assert!(error.to_string().contains("no declared cell field"));
}

#[test]
fn subject_cell_wildcard_keeps_its_rule_side_and_declares_a_fresh_variable() {
    let mut bundle = bundle();
    let mut descriptors = bundle.descriptors.clone();
    let rule = descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::ConfigurationRule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.subject.cells[1].value = ProtocolRuleStateTerm::Term(DescriptorTerm::Wildcard {
        key: key(ProvenanceRole::RuleLeftWildcard, 0),
    });
    let ProtocolRuleStateTerm::KSequence(sequence) = &mut rule.result.cells[0].value else {
        unreachable!();
    };
    sequence.items[0].value = variable(ProvenanceRole::RuleRightReference, 0, "X");
    rule.bindings
        .retain(|binding| matches!(binding.name.as_str(), "X" | "tail" | "state"));
    let expected_keys = rule.expected_provenance_keys(ItemKind::Rule).unwrap();
    let descriptor = descriptors
        .iter_mut()
        .find(|descriptor| matches!(&descriptor.payload, DescriptorPayload::ConfigurationRule(_)))
        .unwrap();
    descriptor.provenance = provenance(key(ProvenanceRole::RuleDeclaration, 0), expected_keys);

    bundle.descriptors = descriptors;
    assert_canonical_contract(&bundle.build().unwrap());
    let semantic = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap();
    assert_canonical_contract(&semantic);
    let variables = semantic
        .modules()
        .iter()
        .find(|module| !module.rules().is_empty())
        .unwrap()
        .rules()[0]
        .variables();
    assert!(
        variables
            .iter()
            .any(|variable| variable.id().as_str() == "__krs_wildcard_0"
                && variable.sort() == &krs_ir_levels::SemanticSortRef::map())
    );
}

#[test]
fn descriptor_lookup_errors_preserve_kind_messages_and_missing_ids() {
    for reference in [
        id("Missing", ItemKind::Sort),
        id("State", ItemKind::Configuration),
    ] {
        let mut bundle = bundle();
        let reference = if reference.item_kind() == ItemKind::Configuration {
            bundle
                .descriptors
                .iter()
                .find(|descriptor| descriptor.id.item_kind() == ItemKind::Configuration)
                .unwrap()
                .id
                .clone()
        } else {
            reference
        };
        bundle.descriptors.push(descriptor(
            id("Referrer", ItemKind::Sort),
            DescriptorPayload::Sort(SortDescriptor {
                parents: BTreeSet::from([reference.clone()]),
            }),
        ));
        let error = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap_err();
        if reference.item_kind() == ItemKind::Sort {
            assert_eq!(
                error,
                krs_compiler::DescriptorLoweringError::DanglingReference(Box::new(
                    reference.clone()
                ))
            );
            assert_eq!(
                error.to_string(),
                format!("dangling descriptor reference {reference}")
            );
        } else {
            assert_eq!(
                error,
                krs_compiler::DescriptorLoweringError::ReferenceKindMismatch {
                    id: Box::new(reference.clone()),
                    expected: ItemKind::Sort,
                    actual: ItemKind::Configuration,
                }
            );
            assert_eq!(
                error.to_string(),
                format!(
                    "descriptor reference {reference} has kind {}, expected {}",
                    ItemKind::Configuration,
                    ItemKind::Sort
                )
            );
        }
    }
}

#[test]
fn duplicate_descriptor_precedes_dangling_reference_validation() {
    let mut bundle = bundle();
    let duplicate_id = id("Referrer", ItemKind::Sort);
    let referrer = descriptor(
        duplicate_id.clone(),
        DescriptorPayload::Sort(SortDescriptor {
            parents: BTreeSet::from([id("Missing", ItemKind::Sort)]),
        }),
    );
    bundle.descriptors.push(referrer.clone());
    bundle.descriptors.push(referrer);
    assert!(
        bundle
            .build()
            .unwrap_err()
            .to_string()
            .contains(&format!("duplicate stable descriptor {duplicate_id}"))
    );
}

/// Edit the configuration descriptor, refresh its provenance, and return the lowering error text.
fn console_error(edit: impl FnOnce(&mut DescriptorFixedConfiguration)) -> String {
    let mut bundle = bundle();
    let mut descriptors = bundle.descriptors.clone();
    let configuration = descriptors
        .iter_mut()
        .find(|descriptor| {
            matches!(
                &descriptor.payload,
                DescriptorPayload::FixedConfiguration(_)
            )
        })
        .unwrap();
    let DescriptorPayload::FixedConfiguration(payload) = &mut configuration.payload else {
        unreachable!();
    };
    edit(payload);
    *configuration = descriptor(configuration.id.clone(), configuration.payload.clone());
    bundle.descriptors = descriptors;
    let error = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap_err();
    assert_eq!(
        krs_diagnostic::ToDiagnostic::to_diagnostic(&error).code,
        krs_diagnostic::codes::analysis::CONSOLE_CELL,
        "{error}"
    );
    error.to_string()
}

fn stream(ordinal: u32, value: CellStream) -> DescriptorCellStream {
    DescriptorCellStream {
        key: key(ProvenanceRole::ConfigurationCellStream, ordinal),
        value,
    }
}

fn exit(ordinal: u32) -> DescriptorCellExit {
    DescriptorCellExit {
        key: key(ProvenanceRole::ConfigurationCellExit, ordinal),
    }
}

fn set_leaf_sort(field: &mut DescriptorCellField, sort: BuiltinSort) {
    let ProtocolCellContent::Leaf { sort: content, .. } = &mut field.content else {
        unreachable!();
    };
    content.sort = DescriptorSortRef::Builtin(sort);
}

#[test]
fn a_stream_cell_must_be_a_list() {
    let error = console_error(|configuration| {
        configuration.declaration.fields[1].stream = Some(stream(1, CellStream::Stdin));
    });
    assert!(
        error.contains("stream cell `env` must have sort List"),
        "{error}"
    );
}

#[test]
fn the_computation_cell_cannot_be_a_stream_or_exit_cell() {
    let error = console_error(|configuration| {
        configuration.declaration.fields[0].stream = Some(stream(0, CellStream::Stdout));
    });
    assert!(
        error.contains("the computation cell `k` cannot be a stream cell"),
        "{error}"
    );
    let error = console_error(|configuration| {
        configuration.declaration.fields[0].exit = Some(exit(0));
    });
    assert!(
        error.contains("the computation cell `k` cannot be the exit cell"),
        "{error}"
    );
}

#[test]
fn an_exit_cell_must_be_an_int_outside_every_repeated_cell() {
    let error = console_error(|configuration| {
        configuration.declaration.fields[1].exit = Some(exit(1));
    });
    assert!(
        error.contains("exit cell `env` must have sort Int"),
        "{error}"
    );
    let error = console_error(|configuration| {
        let env = &mut configuration.declaration.fields[1];
        set_leaf_sort(env, BuiltinSort::Int);
        env.multiplicity = Some(krs_ir::DescriptorCellMultiplicity {
            key: key(ProvenanceRole::ConfigurationCellMultiplicity, 1),
            value: "*".into(),
        });
        env.exit = Some(exit(1));
    });
    assert!(
        error.contains("exit cell `env` is inside the repeated cell `env`"),
        "{error}"
    );
}

#[test]
fn at_most_one_cell_reads_standard_input() {
    let error = console_error(|configuration| {
        let owner = configuration.initializer.owner.clone();
        let mut input = cell_field(&owner, 2, "input", CellWrapper::Cell, BuiltinSort::List);
        input.stream = Some(stream(2, CellStream::Stdin));
        let env = &mut configuration.declaration.fields[1];
        set_leaf_sort(env, BuiltinSort::List);
        env.stream = Some(stream(1, CellStream::Stdin));
        configuration
            .initializer
            .cells
            .push(DescriptorInitializerCell {
                key: key(ProvenanceRole::InitializerCell, 2),
                field: DescriptorCellReference {
                    key: key(ProvenanceRole::InitializerField, 2),
                    cell: input.reference.cell.clone(),
                },
                content: ProtocolInitializerCellContent::Leaf {
                    constructor_key: key(ProvenanceRole::InitializerCellConstructor, 2),
                    wrapper: CellWrapper::Cell,
                    value: ProtocolInitializerStateTerm::Term(ProtocolInitializerTerm {
                        key: key(ProvenanceRole::InitializerTerm, 2),
                        term: variable(ProvenanceRole::InitializerTermPath, 2, "env"),
                    }),
                },
            });
        configuration.declaration.fields.push(input);
    });
    assert!(
        error.contains("cells `env` and `input` both declare stream = \"stdin\""),
        "{error}"
    );
}

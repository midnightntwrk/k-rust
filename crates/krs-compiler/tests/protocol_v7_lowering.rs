//! Stable protocol-v7 state descriptors reach the existing semantic/Definition lane.

use std::collections::BTreeMap;

use krs_compiler::{emit_k, lower_descriptor_bundle, lower_semantic_theory};
use krs_ir::{
    BuiltinSort, CellWrapper, Descriptor, DescriptorBundle, DescriptorCellField,
    DescriptorCellIdentity, DescriptorCellReference, DescriptorConfigurationDeclaration,
    DescriptorConfigurationInitializer, DescriptorConfigurationReference,
    DescriptorConfigurationRoot, DescriptorConfigurationRule, DescriptorConfigurationVariable,
    DescriptorFixedConfiguration, DescriptorInitializerCell, DescriptorNodeOrigin,
    DescriptorPayload, DescriptorProvenance, DescriptorRuleBinding, DescriptorRuleCells,
    DescriptorSortRef, DescriptorSortReference, DescriptorTerm, ItemKind, OriginStack, PackageId,
    ProtocolCellContent, ProtocolConfigurationVariable, ProtocolInitializerCellContent,
    ProtocolInitializerStateTerm, ProtocolInitializerTerm, ProtocolKSequence,
    ProtocolKSequenceItem, ProtocolRuleBinding, ProtocolRuleBindingKind, ProtocolRuleCell,
    ProtocolRuleFrame, ProtocolRuleKSequence, ProtocolRuleKSequenceItem, ProtocolRuleMap,
    ProtocolRuleMapBody, ProtocolRuleMapItem, ProtocolRuleStateTerm, ProvenanceKey, SentenceKind,
    Sha256Digest, SortDescriptor, SourceFileId, SourceRange, StableItemId,
};

fn package() -> PackageId {
    PackageId::new("KRS-V7", "v7", "0.1.0", "workspace").unwrap()
}

fn id(name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(package(), ["calc"], name, kind, "").unwrap()
}

fn framework_kitem() -> StableItemId {
    StableItemId::new(
        PackageId::new("KRS-FRAMEWORK", "krs", "0.1.0", "framework").unwrap(),
        ["framework"],
        "KItem",
        ItemKind::Sort,
        "",
    )
    .unwrap()
}

fn key(role: &str, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal).unwrap()
}

fn provenance(
    primary: ProvenanceKey,
    keys: impl IntoIterator<Item = ProvenanceKey>,
) -> DescriptorProvenance {
    let file = SourceFileId::new(
        package(),
        "src/calc.rs",
        Sha256Digest::new("7".repeat(64)).unwrap(),
    )
    .unwrap();
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
                    OriginStack::authored(
                        SourceRange::new(file.clone(), start, start + 1).unwrap(),
                    ),
                )
            })
            .collect(),
    )
    .unwrap()
}

fn sort_ref(role: &str, ordinal: u32, sort: DescriptorSortRef) -> DescriptorSortReference {
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
            key: key("configuration_field", ordinal),
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
        content: ProtocolCellContent::Leaf {
            wrapper_key: key("configuration_cell_wrapper", ordinal),
            wrapper,
            sort: sort_ref(
                "configuration_cell_content",
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
        binding_key: key("configuration_variable", ordinal),
        binding: binding.into(),
        external_name_key: key("configuration_variable_name", ordinal),
        external_name: external.into(),
        sort: sort_ref(
            "configuration_variable_type",
            ordinal,
            DescriptorSortRef::Builtin(sort),
        ),
        main_key: main.then(|| key("configuration_variable_main", ordinal)),
    }
}

fn variable(role: &str, ordinal: u32, name: &str) -> DescriptorTerm {
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
            key: key("configuration_declaration", 0),
            fields: vec![k.clone(), env.clone()],
        },
        initializer: DescriptorConfigurationInitializer {
            key: key("initializer_declaration", 0),
            owner_key: key("initializer_result_type", 0),
            owner: owner.clone(),
            variables: vec![
                initializer_variable(0, "pgm", "PGM", BuiltinSort::Id, true),
                initializer_variable(1, "env", "ENV", BuiltinSort::Map, false),
            ],
            body_key: key("initializer_body", 0),
            cells: vec![
                DescriptorInitializerCell {
                    key: key("initializer_cell", 0),
                    field: DescriptorCellReference {
                        key: key("initializer_field", 0),
                        cell: k.reference.cell,
                    },
                    content: ProtocolInitializerCellContent::Leaf {
                        constructor_key: key("initializer_cell_constructor", 0),
                        wrapper: CellWrapper::KCell,
                        value: ProtocolInitializerStateTerm::KSequence(ProtocolKSequence {
                            payload_key: Some(key("k_sequence_payload", 0)),
                            dot_k_key: None,
                            notation: krs_ir::DescriptorKSequenceNotation::Comma,
                            items: vec![ProtocolKSequenceItem {
                                key: key("k_sequence_item", 0),
                                value: ProtocolInitializerTerm {
                                    key: key("initializer_term", 0),
                                    term: variable("initializer_term_path", 0, "pgm"),
                                },
                            }],
                        }),
                    },
                },
                DescriptorInitializerCell {
                    key: key("initializer_cell", 1),
                    field: DescriptorCellReference {
                        key: key("initializer_field", 1),
                        cell: env.reference.cell,
                    },
                    content: ProtocolInitializerCellContent::Leaf {
                        constructor_key: key("initializer_cell_constructor", 1),
                        wrapper: CellWrapper::Cell,
                        value: ProtocolInitializerStateTerm::Term(ProtocolInitializerTerm {
                            key: key("initializer_term", 1),
                            term: variable("initializer_term_path", 1, "env"),
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
    side: &str,
    ordinal: u32,
    name: &str,
    wrapper: CellWrapper,
    value: ProtocolRuleStateTerm<DescriptorTerm>,
) -> ProtocolRuleCell<DescriptorCellReference, DescriptorTerm> {
    ProtocolRuleCell {
        field: DescriptorCellReference {
            key: key(&format!("rule_{side}_cells_field"), ordinal),
            cell: DescriptorCellIdentity {
                owner: owner.clone(),
                field: name.into(),
            },
        },
        wrapper_key: key(&format!("rule_{side}_cells_wrapper"), ordinal),
        wrapper,
        value,
    }
}

fn term_binding(name: &str, ordinal: u32, sort: DescriptorSortRef) -> DescriptorRuleBinding {
    ProtocolRuleBinding {
        name: name.into(),
        kind: ProtocolRuleBindingKind::Term {
            sort: sort_ref("rule_binding_type", ordinal, sort),
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

#[allow(clippy::too_many_lines)]
fn configuration_rule(owner: &StableItemId) -> DescriptorConfigurationRule {
    let k_state = |side: &str, value: &str, tail| {
        ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
            payload_key: Some(key(&format!("rule_{side}_k_sequence_payload"), 0)),
            dot_k_key: None,
            notation: krs_ir::DescriptorKSequenceNotation::Comma,
            items: vec![ProtocolRuleKSequenceItem {
                key: key(&format!("rule_{side}_k_sequence_item"), 0),
                value: variable(&format!("rule_{side}_reference"), 0, value),
            }],
            tail,
        })
    };
    DescriptorConfigurationRule {
        sentence_kind: SentenceKind::Transition,
        label: None,
        priority: None,
        requires: None,
        claim: None,
        pattern_key: key("rule_pattern", 0),
        subject_configuration: DescriptorConfigurationReference {
            key: key("rule_type", 0),
            configuration: owner.clone(),
        },
        result_key: key("rule_result", 0),
        result_configuration: DescriptorConfigurationReference {
            key: key("rule_result_type", 0),
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
            key: key("rule_left_cells_payload", 0),
            cells: vec![
                rule_cell(
                    owner,
                    "left",
                    0,
                    "k",
                    CellWrapper::KCell,
                    k_state(
                        "left",
                        "X",
                        ProtocolRuleFrame::Bind {
                            key: key("rule_left_k_sequence_tail", 0),
                            binding: "tail".into(),
                        },
                    ),
                ),
                rule_cell(
                    owner,
                    "left",
                    1,
                    "env",
                    CellWrapper::Cell,
                    ProtocolRuleStateTerm::Map(ProtocolRuleMap {
                        payload_key: Some(key("rule_left_map_payload", 0)),
                        body: ProtocolRuleMapBody::Items {
                            items: vec![ProtocolRuleMapItem {
                                key_key: key("rule_left_map_key", 0),
                                key: variable("rule_left_reference", 1, "X"),
                                value_key: key("rule_left_map_value", 0),
                                value: variable("rule_left_reference", 2, "V"),
                            }],
                            remainder: ProtocolRuleFrame::Bind {
                                key: key("rule_left_map_remainder", 0),
                                binding: "rest".into(),
                            },
                        },
                    }),
                ),
            ],
            remainder: ProtocolRuleFrame::Bind {
                key: key("rule_left_cells_remainder", 0),
                binding: "state".into(),
            },
        },
        result: DescriptorRuleCells {
            key: key("rule_right_cells_payload", 0),
            cells: vec![rule_cell(
                owner,
                "right",
                0,
                "k",
                CellWrapper::KCell,
                k_state(
                    "right",
                    "V",
                    ProtocolRuleFrame::Reuse {
                        key: key("rule_right_k_sequence_tail", 0),
                        binding: "tail".into(),
                    },
                ),
            )],
            remainder: ProtocolRuleFrame::Reuse {
                key: key("rule_right_cells_remainder", 0),
                binding: "state".into(),
            },
        },
    }
}

fn descriptor(id: StableItemId, payload: DescriptorPayload) -> Descriptor {
    let keys = match &payload {
        DescriptorPayload::Sort(_) => vec![key("sort_declaration", 0)],
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
        DescriptorPayload::Sort(_) => key("sort_declaration", 0),
        DescriptorPayload::FixedConfiguration(_) => key("configuration_declaration", 0),
        DescriptorPayload::ConfigurationRule(_) => key("rule_declaration", 0),
        _ => unreachable!(),
    };
    Descriptor {
        id,
        cfg: BTreeMap::new(),
        provenance: provenance(primary, keys),
        payload,
    }
}

fn bundle() -> DescriptorBundle {
    let (owner, configuration) = fixed_configuration();
    let rule = configuration_rule(&owner);
    DescriptorBundle::new(vec![
        descriptor(
            framework_kitem(),
            DescriptorPayload::Sort(SortDescriptor { parents: vec![] }),
        ),
        descriptor(
            id("Value", ItemKind::Sort),
            DescriptorPayload::Sort(SortDescriptor { parents: vec![] }),
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

fn refresh_rule_provenance(bundle: &mut DescriptorBundle) {
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
    let descriptor = bundle
        .descriptors
        .iter_mut()
        .find(|descriptor| matches!(descriptor.payload, DescriptorPayload::ConfigurationRule(_)))
        .unwrap();
    descriptor.provenance = provenance(key("rule_declaration", 0), expected);
}

#[test]
fn fixed_configuration_and_simultaneous_rule_reach_emitted_k_deterministically() {
    let bundle = bundle();
    let semantic = lower_descriptor_bundle(&bundle).unwrap();
    let module = semantic
        .modules()
        .iter()
        .find(|module| !module.rules().is_empty())
        .unwrap();
    let krs_ir::semantic::SemanticRuleBody::Configuration(rule) =
        module.rules()[0].relational_body()
    else {
        panic!("protocol-v7 rule must remain a simultaneous configuration rewrite");
    };
    assert_eq!(rule.clauses().len(), 2);
    assert!(matches!(
        rule.clauses()[1].after(),
        krs_ir::CellPost::Preserve
    ));
    let lowered = lower_semantic_theory(&semantic).unwrap();
    let source = emit_k(&lowered).unwrap().source().to_owned();
    assert!(source.contains("configuration"));
    assert!(source.contains("<k>"));
    assert!(source.contains("<env>"));
    assert!(source.contains("rule ["));
    assert!(source.contains(":Map"));

    let mut reordered = bundle.descriptors.clone();
    reordered.reverse();
    let repeated =
        lower_semantic_theory(&lower_descriptor_bundle(&DescriptorBundle::new(reordered)).unwrap())
            .unwrap();
    assert_eq!(
        lowered.definition().to_canonical_json().unwrap(),
        repeated.definition().to_canonical_json().unwrap()
    );
}

#[test]
fn exact_empty_map_can_rewrite_to_exact_map_items() {
    let mut bundle = bundle();
    let rule = bundle
        .descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::ConfigurationRule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.subject.cells[1].value = ProtocolRuleStateTerm::Map(ProtocolRuleMap {
        payload_key: Some(key("rule_left_map_payload", 0)),
        body: ProtocolRuleMapBody::Empty { explicit_dot: true },
    });
    let ProtocolRuleStateTerm::KSequence(result_k) = &mut rule.result.cells[0].value else {
        unreachable!();
    };
    result_k.items[0].value = variable("rule_right_reference", 0, "X");
    let owner = rule.subject_configuration.configuration.clone();
    rule.result.cells.push(rule_cell(
        &owner,
        "right",
        1,
        "env",
        CellWrapper::Cell,
        ProtocolRuleStateTerm::Map(ProtocolRuleMap {
            payload_key: Some(key("rule_right_map_payload", 0)),
            body: ProtocolRuleMapBody::Items {
                items: vec![ProtocolRuleMapItem {
                    key_key: key("rule_right_map_key", 0),
                    key: variable("rule_right_reference", 1, "X"),
                    value_key: key("rule_right_map_value", 0),
                    value: variable("rule_right_reference", 2, "X"),
                }],
                remainder: ProtocolRuleFrame::Exact,
            },
        }),
    ));
    rule.bindings
        .retain(|binding| matches!(binding.name.as_str(), "X" | "tail" | "state"));
    refresh_rule_provenance(&mut bundle);

    let semantic = lower_descriptor_bundle(&bundle).unwrap();
    let module = semantic
        .modules()
        .iter()
        .find(|module| !module.rules().is_empty())
        .unwrap();
    let krs_ir::semantic::SemanticRuleBody::Configuration(rewrite) =
        module.rules()[0].relational_body()
    else {
        panic!("protocol-v7 rule must remain a simultaneous configuration rewrite");
    };
    let env = &rewrite.clauses()[1];
    assert!(matches!(env.frame(), krs_ir::CellContentFrame::Exact));
    assert!(matches!(
        env.before().kind(),
        krs_ir::semantic::SemanticTermKind::Map {
            operation: krs_ir::MapOperation::Empty,
            arguments,
        } if arguments.is_empty()
    ));
    assert!(matches!(
        env.after(),
        krs_ir::CellPost::Replace { term }
            if matches!(
                term.kind(),
                krs_ir::semantic::SemanticTermKind::Map {
                    operation: krs_ir::MapOperation::Item,
                    arguments,
                } if arguments.len() == 2
            )
    ));

    let emitted = emit_k(&lower_semantic_theory(&semantic).unwrap()).unwrap();
    assert!(emitted.source().contains(".Map =>"));
    assert!(emitted.source().contains("|->"));
}

#[test]
fn result_only_cell_is_rejected_before_configuration_lowering() {
    let mut bundle = bundle();
    let rule = bundle
        .descriptors
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
    sequence.items[0].value = variable("rule_right_reference", 0, "X");
    rule.bindings
        .retain(|binding| matches!(binding.name.as_str(), "X" | "tail" | "state"));
    let expected_keys = rule.expected_provenance_keys(ItemKind::Rule).unwrap();
    let descriptor = bundle
        .descriptors
        .iter_mut()
        .find(|descriptor| matches!(descriptor.payload, DescriptorPayload::ConfigurationRule(_)))
        .unwrap();
    descriptor.provenance = provenance(key("rule_declaration", 0), expected_keys);
    let error = lower_descriptor_bundle(&bundle).unwrap_err();
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
    let rule = bundle
        .descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::ConfigurationRule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.subject.cells[0].field.cell.field = "missing".into();
    let error = lower_descriptor_bundle(&bundle).unwrap_err();
    assert!(error.to_string().contains("no declared cell field"));
}

#[test]
fn subject_cell_wildcard_keeps_its_rule_side_and_declares_a_fresh_variable() {
    let mut bundle = bundle();
    let rule = bundle
        .descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            DescriptorPayload::ConfigurationRule(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    rule.subject.cells[1].value = ProtocolRuleStateTerm::Term(DescriptorTerm::Wildcard {
        key: key("rule_left_wildcard", 0),
    });
    let ProtocolRuleStateTerm::KSequence(sequence) = &mut rule.result.cells[0].value else {
        unreachable!();
    };
    sequence.items[0].value = variable("rule_right_reference", 0, "X");
    rule.bindings
        .retain(|binding| matches!(binding.name.as_str(), "X" | "tail" | "state"));
    let expected_keys = rule.expected_provenance_keys(ItemKind::Rule).unwrap();
    let descriptor = bundle
        .descriptors
        .iter_mut()
        .find(|descriptor| matches!(descriptor.payload, DescriptorPayload::ConfigurationRule(_)))
        .unwrap();
    descriptor.provenance = provenance(key("rule_declaration", 0), expected_keys);

    let semantic = lower_descriptor_bundle(&bundle).unwrap();
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
                && variable.sort() == &krs_ir::SemanticSortRef::map())
    );
}

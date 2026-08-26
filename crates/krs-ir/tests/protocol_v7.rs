//! Staged non-rule collector protocol-v7 contract tests.

use std::any::TypeId;
use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    BuiltinOperation, BuiltinSort, CellWrapper, Descriptor, DescriptorApplicationHeadClass,
    DescriptorApplicationRef, DescriptorApplicationReference, DescriptorBundle,
    DescriptorCellField, DescriptorCellIdentity, DescriptorCellReference,
    DescriptorConfigurationDeclaration, DescriptorConfigurationInitializer,
    DescriptorConfigurationReference, DescriptorConfigurationRoot, DescriptorConfigurationRule,
    DescriptorConfigurationVariable, DescriptorContextAlias, DescriptorFixedConfiguration,
    DescriptorInitializerCell, DescriptorKSequenceNotation, DescriptorLiteral,
    DescriptorNodeOrigin, DescriptorPayload, DescriptorProvenance, DescriptorRuleBinding,
    DescriptorRuleCells, DescriptorRuleCondition, DescriptorSortRef, DescriptorSortReference,
    DescriptorTerm, DescriptorTermArgument, HostBuiltinOperationRegistration, HostBuiltinRegistry,
    HostBuiltinRegistryError, HostBuiltinSortRegistration, HostCellIdentity, HostCellReference,
    HostConfigurationReference, HostConfigurationRule, HostListOperationRegistration,
    HostMapOperationRegistration, HostRuleCells, HostSortReference, HostTerm, HostTypeKey,
    HostTypeReference, ItemKind, ListOperation, MapOperation, OriginStack, PackageId,
    ProtocolCellContent, ProtocolContextAliasBinding, ProtocolContextAliasBindingKind,
    ProtocolInitializerCellContent, ProtocolInitializerStateTerm, ProtocolInitializerTerm,
    ProtocolKSequence, ProtocolKSequenceItem, ProtocolMap, ProtocolMapBody, ProtocolRuleBinding,
    ProtocolRuleBindingKind, ProtocolRuleCell, ProtocolRuleFrame, ProtocolRuleKSequence,
    ProtocolRuleKSequenceItem, ProtocolRuleMap, ProtocolRuleMapBody, ProtocolRuleMapItem,
    ProtocolRuleStateTerm, ProtocolV7ShapeError, ProvenanceKey, SentenceKind, Sha256Digest,
    SourceFileId, SourceRange, StableItemId,
};

fn package() -> PackageId {
    PackageId::new("IMP", "imp-semantics", "0.1.0", "workspace").unwrap()
}

fn item(name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(package(), ["calc"], name, kind, "").unwrap()
}

fn key(role: &str, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal).unwrap()
}

fn sort(role: &str, ordinal: u32, sort: BuiltinSort) -> DescriptorSortReference {
    DescriptorSortReference {
        key: key(role, ordinal),
        sort: DescriptorSortRef::Builtin(sort),
    }
}

fn cell_field(
    owner: &StableItemId,
    ordinal: u32,
    name: &str,
    wrapper: CellWrapper,
    content_sort: BuiltinSort,
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
        content: ProtocolCellContent::Leaf {
            wrapper_key: key("configuration_cell_wrapper", ordinal),
            wrapper,
            sort: sort("configuration_cell_content", ordinal, content_sort),
            arguments: Vec::new(),
        },
    }
}

fn variable(
    ordinal: u32,
    binding: &str,
    external_name: &str,
    sort_value: BuiltinSort,
    main: bool,
) -> DescriptorConfigurationVariable {
    DescriptorConfigurationVariable {
        binding_key: key("configuration_variable", ordinal),
        binding: binding.into(),
        external_name_key: key("configuration_variable_name", ordinal),
        external_name: external_name.into(),
        sort: sort("configuration_variable_type", ordinal, sort_value),
        main_key: main.then(|| key("configuration_variable_main", ordinal)),
    }
}

fn variable_term(
    term_ordinal: u32,
    path_ordinal: u32,
    name: &str,
) -> ProtocolInitializerTerm<DescriptorTerm> {
    let path_key = key("initializer_term_path", path_ordinal);
    ProtocolInitializerTerm {
        key: key("initializer_term", term_ordinal),
        term: DescriptorTerm::Variable {
            key: path_key.clone(),
            path_key,
            name: name.into(),
        },
    }
}

fn fixed_configuration() -> (StableItemId, DescriptorFixedConfiguration) {
    let owner = item("Calc", ItemKind::Configuration);
    let k = cell_field(&owner, 0, "k", CellWrapper::KCell, BuiltinSort::KSequence);
    let env = cell_field(&owner, 1, "env", CellWrapper::Cell, BuiltinSort::Map);
    let k_identity = k.reference.cell.clone();
    let env_identity = env.reference.cell.clone();
    let declaration = DescriptorConfigurationDeclaration {
        key: key("configuration_declaration", 0),
        fields: vec![k, env],
    };
    let initializer = DescriptorConfigurationInitializer {
        key: key("initializer_declaration", 0),
        owner_key: key("initializer_result_type", 0),
        owner: owner.clone(),
        variables: vec![
            variable(0, "pgm", "$PGM", BuiltinSort::KSequence, true),
            variable(1, "env", "$ENV", BuiltinSort::Map, false),
        ],
        body_key: key("initializer_body", 0),
        cells: vec![
            DescriptorInitializerCell {
                key: key("initializer_cell", 0),
                field: DescriptorCellReference {
                    key: key("initializer_field", 0),
                    cell: k_identity,
                },
                content: ProtocolInitializerCellContent::Leaf {
                    constructor_key: key("initializer_cell_constructor", 0),
                    wrapper: CellWrapper::KCell,
                    value: ProtocolInitializerStateTerm::KSequence(ProtocolKSequence {
                        payload_key: Some(key("k_sequence_payload", 0)),
                        dot_k_key: None,
                        notation: DescriptorKSequenceNotation::Comma,
                        items: vec![ProtocolKSequenceItem {
                            key: key("k_sequence_item", 0),
                            value: variable_term(0, 0, "pgm"),
                        }],
                    }),
                },
            },
            DescriptorInitializerCell {
                key: key("initializer_cell", 1),
                field: DescriptorCellReference {
                    key: key("initializer_field", 1),
                    cell: env_identity,
                },
                content: ProtocolInitializerCellContent::Leaf {
                    constructor_key: key("initializer_cell_constructor", 1),
                    wrapper: CellWrapper::Cell,
                    value: ProtocolInitializerStateTerm::Map(ProtocolMap {
                        payload_key: None,
                        body: ProtocolMapBody::Empty {
                            explicit_dot: false,
                        },
                    }),
                },
            },
        ],
    };
    (
        owner,
        DescriptorFixedConfiguration {
            root: DescriptorConfigurationRoot::GeneratedTop,
            declaration,
            initializer,
        },
    )
}

#[test]
fn fixed_configuration_validates_exact_closed_provenance() {
    let (owner, configuration) = fixed_configuration();
    configuration.validate(&owner).unwrap();
    let expected = configuration.expected_provenance_keys(&owner).unwrap();
    configuration
        .validate_complete_provenance(&owner, &key("configuration_declaration", 0), &expected)
        .unwrap();
    assert!(expected.contains(&key("configuration_variable_type", 1)));
    assert!(expected.contains(&key("k_sequence_item", 0)));
    assert_eq!(
        serde_json::to_value(&configuration).unwrap()["root"]["root_kind"],
        "generated_top"
    );
}

#[test]
fn fixed_configuration_rejects_wrong_keys_duplicates_and_tree_drift() {
    let (owner, configuration) = fixed_configuration();

    let mut wrong_key = configuration.clone();
    wrong_key.declaration.fields[1].reference.key = key("configuration_field", 0);
    assert!(matches!(
        wrong_key.validate(&owner),
        Err(ProtocolV7ShapeError::UnexpectedProvenance { .. })
    ));

    let mut duplicate_external = configuration.clone();
    duplicate_external.initializer.variables[1].external_name = "$PGM".into();
    assert_eq!(
        duplicate_external.validate(&owner),
        Err(ProtocolV7ShapeError::DuplicateValue(
            "external configuration variable names"
        ))
    );

    let mut reordered = configuration.clone();
    reordered.initializer.cells.swap(0, 1);
    assert_eq!(
        reordered.validate(&owner),
        Err(ProtocolV7ShapeError::InitializerDeclarationMismatch)
    );

    let expected = configuration.expected_provenance_keys(&owner).unwrap();
    let mut actual = expected.clone();
    actual.insert(key("unexpected", 0));
    assert_eq!(
        configuration.validate_complete_provenance(
            &owner,
            &key("configuration_declaration", 0),
            &actual,
        ),
        Err(ProtocolV7ShapeError::ExtraProvenance(key("unexpected", 0)))
    );
}

#[test]
fn nested_cell_identity_is_owner_qualified() {
    let left = item("LeftFrame", ItemKind::Cell);
    let right = item("RightFrame", ItemKind::Cell);
    let left_field = cell_field(&left, 0, "env", CellWrapper::Cell, BuiltinSort::Map);
    let right_field = cell_field(&right, 0, "env", CellWrapper::Cell, BuiltinSort::Map);
    assert_ne!(left_field.reference.cell, right_field.reference.cell);

    DescriptorConfigurationDeclaration {
        key: key("configuration_declaration", 0),
        fields: vec![left_field],
    }
    .validate(&left)
    .unwrap();
}

struct Marker<const N: usize>;

fn marker<const N: usize>() -> TypeId {
    TypeId::of::<Marker<N>>()
}

#[test]
fn v7_builtin_registry_requires_map_and_id() {
    let sorts = BuiltinSort::ALL
        .into_iter()
        .enumerate()
        .map(|(index, sort)| HostBuiltinSortRegistration {
            sort,
            target: match index {
                0 => HostTypeKey(marker::<0>),
                1 => HostTypeKey(marker::<1>),
                2 => HostTypeKey(marker::<2>),
                3 => HostTypeKey(marker::<3>),
                4 => HostTypeKey(marker::<4>),
                5 => HostTypeKey(marker::<5>),
                _ => HostTypeKey(marker::<6>),
            },
        })
        .collect();
    let operations = BuiltinOperation::ALL
        .into_iter()
        .enumerate()
        .map(|(index, operation)| HostBuiltinOperationRegistration {
            operation,
            target: match index {
                0 => HostTypeKey(marker::<7>),
                1 => HostTypeKey(marker::<8>),
                2 => HostTypeKey(marker::<9>),
                3 => HostTypeKey(marker::<10>),
                4 => HostTypeKey(marker::<11>),
                5 => HostTypeKey(marker::<12>),
                6 => HostTypeKey(marker::<13>),
                7 => HostTypeKey(marker::<14>),
                8 => HostTypeKey(marker::<15>),
                9 => HostTypeKey(marker::<16>),
                10 => HostTypeKey(marker::<17>),
                11 => HostTypeKey(marker::<18>),
                12 => HostTypeKey(marker::<19>),
                13 => HostTypeKey(marker::<20>),
                14 => HostTypeKey(marker::<21>),
                15 => HostTypeKey(marker::<22>),
                16 => HostTypeKey(marker::<23>),
                _ => HostTypeKey(marker::<24>),
            },
        })
        .collect();
    let map_operations = vec![HostMapOperationRegistration {
        operation: MapOperation::Update,
        target: HostTypeKey(marker::<25>),
    }];
    let list_operations = ListOperation::TERM_APPLICATIONS
        .into_iter()
        .enumerate()
        .map(|(index, operation)| HostListOperationRegistration {
            operation,
            target: match index {
                0 => HostTypeKey(marker::<26>),
                1 => HostTypeKey(marker::<27>),
                2 => HostTypeKey(marker::<28>),
                3 => HostTypeKey(marker::<29>),
                4 => HostTypeKey(marker::<30>),
                _ => HostTypeKey(marker::<31>),
            },
        })
        .collect();
    let registry = HostBuiltinRegistry {
        sorts,
        operations,
        map_operations,
        list_operations,
    };
    registry.validate_v7().unwrap();

    let mut missing = registry.clone();
    missing.sorts.retain(|entry| entry.sort != BuiltinSort::Map);
    assert_eq!(
        missing.validate_v7(),
        Err(HostBuiltinRegistryError::MissingSort(BuiltinSort::Map))
    );
}

#[test]
fn primary_key_is_configuration_declaration() {
    let (owner, configuration) = fixed_configuration();
    let actual: BTreeSet<_> = configuration.expected_provenance_keys(&owner).unwrap();
    assert!(matches!(
        configuration.validate_complete_provenance(
            &owner,
            &key("initializer_declaration", 0),
            &actual,
        ),
        Err(ProtocolV7ShapeError::UnexpectedProvenance { .. })
    ));
}

fn rule_variable(side: &str, ordinal: u32, name: &str) -> DescriptorTerm {
    let key = key(&format!("rule_{side}_reference"), ordinal);
    DescriptorTerm::Variable {
        key: key.clone(),
        path_key: key,
        name: name.into(),
    }
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

fn descriptor_context_alias() -> DescriptorContextAlias {
    let configuration = item("Machine", ItemKind::Configuration);
    DescriptorContextAlias {
        declaration_key: key("context_alias_declaration", 0),
        name_key: key("context_alias_name", 0),
        name: "m3d_eval".into(),
        here_key: key("context_alias_here", 0),
        here: "site".into(),
        pattern_key: key("rule_pattern", 0),
        configuration: DescriptorConfigurationReference {
            key: key("rule_type", 0),
            configuration: configuration.clone(),
        },
        bindings: vec![
            ProtocolContextAliasBinding {
                name: "site".into(),
                kind: ProtocolContextAliasBindingKind::Here,
            },
            ProtocolContextAliasBinding {
                name: "tail".into(),
                kind: ProtocolContextAliasBindingKind::KSequenceFrame,
            },
            ProtocolContextAliasBinding {
                name: "state".into(),
                kind: ProtocolContextAliasBindingKind::ConfigurationFrame,
            },
        ],
        pattern: DescriptorRuleCells {
            key: key("rule_left_cells_payload", 0),
            cells: vec![rule_cell(
                &configuration,
                "left",
                0,
                "k",
                CellWrapper::KCell,
                ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
                    payload_key: Some(key("rule_left_k_sequence_payload", 0)),
                    dot_k_key: None,
                    notation: DescriptorKSequenceNotation::Comma,
                    items: vec![ProtocolRuleKSequenceItem {
                        key: key("rule_left_k_sequence_item", 0),
                        value: rule_variable("left", 0, "site"),
                    }],
                    tail: ProtocolRuleFrame::Bind {
                        key: key("rule_left_k_sequence_tail", 0),
                        binding: "tail".into(),
                    },
                }),
            )],
            remainder: ProtocolRuleFrame::Bind {
                key: key("rule_left_cells_remainder", 0),
                binding: "state".into(),
            },
        },
    }
}

#[test]
fn context_alias_protocol_rejects_lost_or_mismatched_structural_frames() {
    let alias = descriptor_context_alias();
    alias.validate(ItemKind::ContextAlias).unwrap();
    let expected = alias.expected_provenance_keys();
    alias
        .validate_complete_provenance(
            ItemKind::ContextAlias,
            &key("context_alias_declaration", 0),
            &expected,
        )
        .unwrap();

    let mut mismatched_tail = alias.clone();
    let ProtocolRuleStateTerm::KSequence(sequence) = &mut mismatched_tail.pattern.cells[0].value
    else {
        unreachable!()
    };
    let ProtocolRuleFrame::Bind { binding, .. } = &mut sequence.tail else {
        unreachable!()
    };
    *binding = "missing_tail".into();
    assert!(matches!(
        mismatched_tail.validate(ItemKind::ContextAlias),
        Err(ProtocolV7ShapeError::InvalidTerm(
            "context-alias frame binding has the wrong structural kind or occurrence"
        ))
    ));

    let mut lost_configuration = alias;
    lost_configuration.pattern.remainder = ProtocolRuleFrame::Exact;
    assert!(matches!(
        lost_configuration.validate(ItemKind::ContextAlias),
        Err(ProtocolV7ShapeError::InvalidTerm(
            "context-alias structural binding catalog does not match its frames"
        ))
    ));
}

fn term_rule_binding(name: &str, ordinal: u32, sort: DescriptorSortRef) -> DescriptorRuleBinding {
    ProtocolRuleBinding {
        name: name.into(),
        kind: ProtocolRuleBindingKind::Term {
            sort: DescriptorSortReference {
                key: key("rule_binding_type", ordinal),
                sort,
            },
        },
    }
}

fn frame_rule_binding(
    name: &str,
    kind: ProtocolRuleBindingKind<DescriptorSortReference>,
) -> DescriptorRuleBinding {
    ProtocolRuleBinding {
        name: name.into(),
        kind,
    }
}

#[allow(clippy::too_many_lines)] // Keeps the complete two-cell rewrite legible in one fixture.
fn var_configuration_rule() -> (StableItemId, DescriptorConfigurationRule) {
    let configuration = item("Machine", ItemKind::Configuration);
    let rule_id = item("var", ItemKind::Rule);
    let subject = DescriptorRuleCells {
        key: key("rule_left_cells_payload", 0),
        cells: vec![
            rule_cell(
                &configuration,
                "left",
                0,
                "k",
                CellWrapper::KCell,
                ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
                    payload_key: Some(key("rule_left_k_sequence_payload", 0)),
                    dot_k_key: None,
                    notation: DescriptorKSequenceNotation::Comma,
                    items: vec![ProtocolRuleKSequenceItem {
                        key: key("rule_left_k_sequence_item", 0),
                        value: rule_variable("left", 0, "X"),
                    }],
                    tail: ProtocolRuleFrame::Bind {
                        key: key("rule_left_k_sequence_tail", 0),
                        binding: "tail".into(),
                    },
                }),
            ),
            rule_cell(
                &configuration,
                "left",
                1,
                "env",
                CellWrapper::Cell,
                ProtocolRuleStateTerm::Map(ProtocolRuleMap {
                    payload_key: Some(key("rule_left_map_payload", 0)),
                    body: ProtocolRuleMapBody::Items {
                        items: vec![ProtocolRuleMapItem {
                            key_key: key("rule_left_map_key", 0),
                            key: rule_variable("left", 1, "X"),
                            value_key: key("rule_left_map_value", 0),
                            value: rule_variable("left", 2, "V"),
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
    };
    let result = DescriptorRuleCells {
        key: key("rule_right_cells_payload", 0),
        cells: vec![rule_cell(
            &configuration,
            "right",
            0,
            "k",
            CellWrapper::KCell,
            ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
                payload_key: Some(key("rule_right_k_sequence_payload", 0)),
                dot_k_key: None,
                notation: DescriptorKSequenceNotation::Comma,
                items: vec![ProtocolRuleKSequenceItem {
                    key: key("rule_right_k_sequence_item", 0),
                    value: rule_variable("right", 0, "V"),
                }],
                tail: ProtocolRuleFrame::Reuse {
                    key: key("rule_right_k_sequence_tail", 0),
                    binding: "tail".into(),
                },
            }),
        )],
        remainder: ProtocolRuleFrame::Reuse {
            key: key("rule_right_cells_remainder", 0),
            binding: "state".into(),
        },
    };
    (
        rule_id,
        DescriptorConfigurationRule {
            sentence_kind: SentenceKind::Transition,
            label: None,
            requires: None,
            claim: None,
            pattern_key: key("rule_pattern", 0),
            subject_configuration: DescriptorConfigurationReference {
                key: key("rule_type", 0),
                configuration: configuration.clone(),
            },
            result_key: key("rule_result", 0),
            result_configuration: DescriptorConfigurationReference {
                key: key("rule_result_type", 0),
                configuration,
            },
            bindings: vec![
                term_rule_binding("X", 0, DescriptorSortRef::Builtin(BuiltinSort::Id)),
                frame_rule_binding("tail", ProtocolRuleBindingKind::KSequenceFrame),
                term_rule_binding(
                    "V",
                    1,
                    DescriptorSortRef::Declared(item("Value", ItemKind::Sort)),
                ),
                frame_rule_binding("rest", ProtocolRuleBindingKind::MapFrame),
                frame_rule_binding("state", ProtocolRuleBindingKind::ConfigurationFrame),
            ],
            subject,
            result,
        },
    )
}

fn rule_origin(index: usize) -> OriginStack {
    let file = SourceFileId::new(
        package(),
        "src/calc.rs",
        Sha256Digest::new("1234567890abcdef".repeat(4)).unwrap(),
    )
    .unwrap();
    let start = u32::try_from(index).unwrap();
    OriginStack::authored(SourceRange::new(file, start, start + 1).unwrap())
}

#[test]
fn configuration_rule_round_trips_with_exact_side_specific_provenance() {
    let (rule_id, rule) = var_configuration_rule();
    rule.validate(ItemKind::Rule).unwrap();
    let expected = rule.expected_provenance_keys(ItemKind::Rule).unwrap();
    rule.validate_complete_provenance(ItemKind::Rule, &key("rule_declaration", 0), &expected)
        .unwrap();
    assert!(expected.contains(&key("rule_binding_type", 0)));
    assert!(expected.contains(&key("rule_binding_type", 1)));
    assert!(expected.contains(&key("rule_left_map_remainder", 0)));
    assert!(expected.contains(&key("rule_right_k_sequence_tail", 0)));
    assert!(
        !expected
            .iter()
            .any(|entry| entry.role() == "rule_left_path")
    );

    let provenance = DescriptorProvenance::new(
        key("rule_declaration", 0),
        expected
            .into_iter()
            .enumerate()
            .map(|(index, key)| DescriptorNodeOrigin::new(key, rule_origin(index)))
            .collect(),
    )
    .unwrap();
    let bundle = DescriptorBundle::new(vec![Descriptor {
        id: rule_id,
        cfg: BTreeMap::default(),
        provenance,
        payload: DescriptorPayload::ConfigurationRule(Box::new(rule)),
    }]);
    let json = bundle.to_canonical_json().unwrap();
    assert!(json.contains("\"protocol_version\": 19"));
    assert!(json.contains("\"configuration_rule\""));
    let decoded: DescriptorBundle = serde_json::from_str(&json).unwrap();
    assert_eq!(decoded, bundle);
}

#[test]
fn configuration_rule_protocol_rejects_static_alias_bodies_on_both_sides() {
    let (_, mut descriptor) = var_configuration_rule();
    descriptor.sentence_kind = SentenceKind::Alias;
    assert!(matches!(
        descriptor.validate(ItemKind::Alias),
        Err(ProtocolV7ShapeError::InvalidTerm(
            "static aliases cannot have configuration rewrite bodies"
        ))
    ));

    let mut host = host_wildcard_configuration_rule();
    host.sentence_kind = SentenceKind::Alias;
    assert!(matches!(
        host.validate(ItemKind::Alias),
        Err(ProtocolV7ShapeError::InvalidTerm(
            "static aliases cannot have configuration rewrite bodies"
        ))
    ));

    let (_, mut descriptor) = var_configuration_rule();
    descriptor.sentence_kind = SentenceKind::Simplification;
    assert!(matches!(
        descriptor.validate(ItemKind::Simplification),
        Err(ProtocolV7ShapeError::InvalidTerm(
            "simplifications cannot have configuration rewrite bodies"
        ))
    ));

    let mut host = host_wildcard_configuration_rule();
    host.sentence_kind = SentenceKind::Simplification;
    assert!(matches!(
        host.validate(ItemKind::Simplification),
        Err(ProtocolV7ShapeError::InvalidTerm(
            "simplifications cannot have configuration rewrite bodies"
        ))
    ));
}

#[test]
fn protocol_v11_configuration_requires_is_exact_and_term_binding_only() {
    let (_, mut rule) = var_configuration_rule();
    rule.requires = Some(DescriptorRuleCondition {
        key: key("rule_requires", 0),
        term: DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: key("rule_requires_application_head", 0),
                application: DescriptorApplicationRef::Builtin(BuiltinOperation::IntGreater),
            },
            path_key: key("rule_requires_path", 0),
            arguments: vec![
                DescriptorTermArgument::Positional {
                    value: Box::new(DescriptorTerm::Variable {
                        key: key("rule_requires_reference", 0),
                        path_key: key("rule_requires_path", 1),
                        name: "X".into(),
                    }),
                },
                DescriptorTermArgument::Positional {
                    value: Box::new(DescriptorTerm::Literal {
                        key: key("rule_requires_literal", 0),
                        literal: DescriptorLiteral::Int("0".into()),
                    }),
                },
            ],
        },
    });

    let expected = rule.expected_provenance_keys(ItemKind::Rule).unwrap();
    assert!(expected.contains(&key("rule_requires", 0)));
    assert!(expected.contains(&key("rule_requires_path", 0)));
    assert!(expected.contains(&key("rule_requires_path", 1)));
    assert!(expected.contains(&key("rule_requires_application_head", 0)));
    assert!(expected.contains(&key("rule_requires_reference", 0)));
    assert!(expected.contains(&key("rule_requires_literal", 0)));

    let mut structural_frame = rule.clone();
    let DescriptorTerm::Application { arguments, .. } =
        &mut structural_frame.requires.as_mut().unwrap().term
    else {
        unreachable!()
    };
    let DescriptorTermArgument::Positional { value } = &mut arguments[0] else {
        unreachable!()
    };
    let DescriptorTerm::Variable { name, .. } = value.as_mut() else {
        unreachable!()
    };
    *name = "tail".into();
    assert!(matches!(
        structural_frame.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::InvalidTerm(
            "rule variable binding is not a term"
        ))
    ));

    let mut wrong_nested_role = rule;
    let DescriptorTerm::Application { arguments, .. } =
        &mut wrong_nested_role.requires.as_mut().unwrap().term
    else {
        unreachable!()
    };
    let DescriptorTermArgument::Positional { value } = &mut arguments[1] else {
        unreachable!()
    };
    let DescriptorTerm::Literal {
        key: literal_key, ..
    } = value.as_mut()
    else {
        unreachable!()
    };
    *literal_key = key("rule_right_literal", 0);
    assert!(matches!(
        wrong_nested_role.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::UnexpectedProvenance { .. })
    ));
}

#[test]
fn configuration_rule_rejects_binding_frame_and_provenance_drift() {
    let (_, rule) = var_configuration_rule();

    let mut wrong_order = rule.clone();
    wrong_order.bindings.swap(0, 1);
    assert!(matches!(
        wrong_order.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::InvalidTerm(_))
    ));

    let mut wrong_kind = rule.clone();
    wrong_kind.bindings[1].kind = ProtocolRuleBindingKind::MapFrame;
    assert!(matches!(
        wrong_kind.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::InvalidTerm(_))
    ));

    let mut wrong_sort_key = rule.clone();
    let ProtocolRuleBindingKind::Term { sort } = &mut wrong_sort_key.bindings[2].kind else {
        unreachable!()
    };
    sort.key = key("rule_binding_type", 2);
    assert!(matches!(
        wrong_sort_key.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::UnexpectedProvenance { .. })
    ));

    let mut wrong_sort_kind = rule.clone();
    let ProtocolRuleBindingKind::Term { sort } = &mut wrong_sort_kind.bindings[2].kind else {
        unreachable!()
    };
    sort.sort = DescriptorSortRef::Declared(item("Machine", ItemKind::Configuration));
    assert!(matches!(
        wrong_sort_kind.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::ItemKind { .. })
    ));

    let mut unbound_reuse = rule.clone();
    unbound_reuse.result.remainder = ProtocolRuleFrame::Reuse {
        key: key("rule_right_cells_remainder", 0),
        binding: "missing".into(),
    };
    assert!(matches!(
        unbound_reuse.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::InvalidTerm(_))
    ));

    let mut wrong_result_kind = rule.clone();
    wrong_result_kind.result.remainder = ProtocolRuleFrame::Reuse {
        key: key("rule_right_cells_remainder", 0),
        binding: "rest".into(),
    };
    assert!(matches!(
        wrong_result_kind.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::InvalidTerm(_))
    ));

    let mut wrong_side = rule;
    wrong_side.result.cells[0].field.key = key("rule_left_cells_field", 0);
    assert!(matches!(
        wrong_side.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::UnexpectedProvenance { .. })
    ));
}

fn wildcard_configuration_rule() -> DescriptorConfigurationRule {
    let configuration = item("Machine", ItemKind::Configuration);
    DescriptorConfigurationRule {
        sentence_kind: SentenceKind::Transition,
        label: None,
        requires: None,
        claim: None,
        pattern_key: key("rule_pattern", 0),
        subject_configuration: DescriptorConfigurationReference {
            key: key("rule_type", 0),
            configuration: configuration.clone(),
        },
        result_key: key("rule_result", 0),
        result_configuration: DescriptorConfigurationReference {
            key: key("rule_result_type", 0),
            configuration: configuration.clone(),
        },
        bindings: Vec::new(),
        subject: DescriptorRuleCells {
            key: key("rule_left_cells_payload", 0),
            cells: vec![rule_cell(
                &configuration,
                "left",
                0,
                "control",
                CellWrapper::Cell,
                ProtocolRuleStateTerm::Term(DescriptorTerm::Wildcard {
                    key: key("rule_left_wildcard", 0),
                }),
            )],
            remainder: ProtocolRuleFrame::Exact,
        },
        result: DescriptorRuleCells {
            key: key("rule_right_cells_payload", 0),
            cells: vec![rule_cell(
                &configuration,
                "right",
                0,
                "control",
                CellWrapper::Cell,
                ProtocolRuleStateTerm::Term(DescriptorTerm::Literal {
                    key: key("rule_right_literal", 0),
                    literal: DescriptorLiteral::Bool(true),
                }),
            )],
            remainder: ProtocolRuleFrame::Exact,
        },
    }
}

#[test]
fn stable_configuration_rule_accepts_only_exact_subject_wildcards() {
    let rule = wildcard_configuration_rule();
    let keys = rule.expected_provenance_keys(ItemKind::Rule).unwrap();
    assert!(keys.contains(&key("rule_left_wildcard", 0)));

    let mut wrong_ordinal = rule.clone();
    let ProtocolRuleStateTerm::Term(DescriptorTerm::Wildcard { key: wildcard }) =
        &mut wrong_ordinal.subject.cells[0].value
    else {
        unreachable!()
    };
    *wildcard = key("rule_left_wildcard", 1);
    assert!(matches!(
        wrong_ordinal.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::UnexpectedProvenance { .. })
    ));

    let mut result_wildcard = rule;
    result_wildcard.result.cells[0].value = ProtocolRuleStateTerm::Term(DescriptorTerm::Wildcard {
        key: key("rule_right_wildcard", 0),
    });
    assert!(matches!(
        result_wildcard.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::InvalidTerm(_))
    ));
}

struct HostRuleConfiguration;
struct HostRuleCellField;
struct HostRuleTermSort;

fn host_type_id<T: 'static>() -> TypeId {
    TypeId::of::<T>()
}

fn host_type_key<T: 'static>() -> HostTypeKey {
    HostTypeKey(host_type_id::<T>)
}

fn host_wildcard_configuration_rule() -> HostConfigurationRule {
    let configuration_key = host_type_key::<HostRuleConfiguration>();
    let configuration = || HostConfigurationReference {
        key: key("rule_type", 0),
        configuration: HostTypeReference {
            key: configuration_key,
            authored_path: "Machine".into(),
        },
    };
    let host_cell = |side: &str, value| ProtocolRuleCell {
        field: HostCellReference {
            key: key(&format!("rule_{side}_cells_field"), 0),
            cell: HostCellIdentity {
                owner: configuration_key,
                field: host_type_key::<HostRuleCellField>(),
            },
        },
        wrapper_key: key(&format!("rule_{side}_cells_wrapper"), 0),
        wrapper: CellWrapper::Cell,
        value: ProtocolRuleStateTerm::Term(value),
    };
    HostConfigurationRule {
        sentence_kind: SentenceKind::Transition,
        label: None,
        requires: None,
        claim: None,
        pattern_key: key("rule_pattern", 0),
        subject_configuration: configuration(),
        result_key: key("rule_result", 0),
        result_configuration: HostConfigurationReference {
            key: key("rule_result_type", 0),
            ..configuration()
        },
        bindings: Vec::new(),
        subject: HostRuleCells {
            key: key("rule_left_cells_payload", 0),
            cells: vec![host_cell(
                "left",
                HostTerm::Wildcard {
                    key: key("rule_left_wildcard", 0),
                },
            )],
            remainder: ProtocolRuleFrame::Exact,
        },
        result: HostRuleCells {
            key: key("rule_right_cells_payload", 0),
            cells: vec![host_cell(
                "right",
                HostTerm::Literal {
                    key: key("rule_right_literal", 0),
                    literal: DescriptorLiteral::Bool(true),
                },
            )],
            remainder: ProtocolRuleFrame::Exact,
        },
    }
}

fn host_typed_configuration_rule() -> HostConfigurationRule {
    let mut rule = host_wildcard_configuration_rule();
    rule.bindings = vec![ProtocolRuleBinding {
        name: "X".into(),
        kind: ProtocolRuleBindingKind::Term {
            sort: HostSortReference {
                key: key("rule_binding_type", 0),
                target: HostTypeReference {
                    key: host_type_key::<HostRuleTermSort>(),
                    authored_path: "Value".into(),
                },
            },
        },
    }];
    rule.subject.cells[0].value = ProtocolRuleStateTerm::Term(HostTerm::Variable {
        key: key("rule_left_reference", 0),
        path_key: key("rule_left_reference", 0),
        name: "X".into(),
    });
    rule.result.cells[0].value = ProtocolRuleStateTerm::Term(HostTerm::Variable {
        key: key("rule_right_reference", 0),
        path_key: key("rule_right_reference", 0),
        name: "X".into(),
    });
    rule
}

#[test]
fn host_configuration_rule_accepts_only_exact_subject_wildcards() {
    let rule = host_wildcard_configuration_rule();
    rule.validate(ItemKind::Rule).unwrap();

    let mut wrong_role = rule.clone();
    let ProtocolRuleStateTerm::Term(HostTerm::Wildcard { key: wildcard }) =
        &mut wrong_role.subject.cells[0].value
    else {
        unreachable!()
    };
    *wildcard = key("rule_left_literal", 0);
    assert!(matches!(
        wrong_role.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::UnexpectedProvenance { .. })
    ));

    let mut result_wildcard = rule;
    result_wildcard.result.cells[0].value = ProtocolRuleStateTerm::Term(HostTerm::Wildcard {
        key: key("rule_right_wildcard", 0),
    });
    assert!(matches!(
        result_wildcard.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::InvalidTerm(_))
    ));
}

#[test]
fn host_configuration_rule_requires_exact_typed_binding_catalog() {
    let rule = host_typed_configuration_rule();
    rule.validate(ItemKind::Rule).unwrap();

    let mut wrong_kind = rule.clone();
    wrong_kind.bindings[0].kind = ProtocolRuleBindingKind::KSequenceFrame;
    assert!(matches!(
        wrong_kind.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::InvalidTerm(_))
    ));

    let mut wrong_sort_key = rule;
    let ProtocolRuleBindingKind::Term { sort } = &mut wrong_sort_key.bindings[0].kind else {
        unreachable!()
    };
    sort.key = key("rule_binding_type", 1);
    assert!(matches!(
        wrong_sort_key.validate(ItemKind::Rule),
        Err(ProtocolV7ShapeError::UnexpectedProvenance { .. })
    ));
}

#[test]
fn simultaneous_k_and_map_update_is_structured() {
    let (_, mut rule) = var_configuration_rule();
    let configuration = rule.result_configuration.configuration.clone();
    rule.bindings.insert(
        4,
        term_rule_binding("E", 2, DescriptorSortRef::Builtin(BuiltinSort::Map)),
    );
    rule.subject.cells.push(rule_cell(
        &configuration,
        "left",
        2,
        "map_source",
        CellWrapper::Cell,
        ProtocolRuleStateTerm::Term(rule_variable("left", 3, "E")),
    ));
    rule.result.cells.push(rule_cell(
        &configuration,
        "right",
        1,
        "env",
        CellWrapper::Cell,
        ProtocolRuleStateTerm::Map(ProtocolRuleMap {
            payload_key: Some(key("rule_right_map_payload", 0)),
            body: ProtocolRuleMapBody::Update {
                base_key: key("rule_right_map_update_base", 0),
                base: rule_variable("right", 1, "E"),
                key_key: key("rule_right_map_key", 0),
                key: rule_variable("right", 2, "X"),
                value_key: key("rule_right_map_value", 0),
                value: rule_variable("right", 3, "V"),
            },
        }),
    ));
    rule.validate(ItemKind::Rule).unwrap();
    let keys = rule.expected_provenance_keys(ItemKind::Rule).unwrap();
    assert!(keys.contains(&key("rule_right_map_update_base", 0)));
    assert!(keys.contains(&key("rule_right_cells_field", 1)));
}

#[test]
fn protocol_seven_is_rejected_after_v9_cutover() {
    let error = serde_json::from_str::<DescriptorBundle>(
        r#"{"protocol_version":7,"descriptors":[],"declarations":[]}"#,
    )
    .unwrap_err();
    assert!(error.to_string().contains("expected 19"));
}

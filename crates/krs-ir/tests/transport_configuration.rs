//! Configuration transport contract tests.

use std::any::TypeId;
use std::collections::{BTreeMap, BTreeSet};

use krs_ir::testing;
use krs_ir::transport::detail::{StateTermReason, TransportField};
use krs_ir::{
    BuiltinOperation, BuiltinSort, CellWrapper, DescriptorApplicationHeadClass,
    DescriptorApplicationRef, DescriptorApplicationReference, DescriptorBundle,
    DescriptorCellField, DescriptorCellIdentity, DescriptorCellReference,
    DescriptorConfigurationDeclaration, DescriptorConfigurationInitializer,
    DescriptorConfigurationReference, DescriptorConfigurationRoot, DescriptorConfigurationRule,
    DescriptorConfigurationVariable, DescriptorContextAlias, DescriptorFixedConfiguration,
    DescriptorInitializerCell, DescriptorKSequenceNotation, DescriptorLiteral,
    DescriptorNodeOrigin, DescriptorPayload, DescriptorProvenance, DescriptorRuleBinding,
    DescriptorRuleCells, DescriptorRuleCondition, DescriptorSortRef, DescriptorSortReference,
    DescriptorTerm, DescriptorTermArgument, HostBuiltinRegistry, HostBuiltinRegistryError,
    HostCellIdentity, HostCellReference, HostConfigurationReference, HostConfigurationRule,
    HostListOperationRegistration, HostMapOperationRegistration, HostRuleCells,
    HostSetOperationRegistration, HostSortReference, HostTerm, HostTypeKey, HostTypeReference,
    ItemKind, ListOperation, OriginStack, PackageId, ProtocolCellContent,
    ProtocolContextAliasBinding, ProtocolContextAliasBindingKind, ProtocolInitializerCellContent,
    ProtocolInitializerStateTerm, ProtocolInitializerTerm, ProtocolKSequence,
    ProtocolKSequenceItem, ProtocolMap, ProtocolMapBody, ProtocolRuleBinding,
    ProtocolRuleBindingKind, ProtocolRuleCell, ProtocolRuleFrame, ProtocolRuleKSequence,
    ProtocolRuleKSequenceItem, ProtocolRuleMap, ProtocolRuleMapBody, ProtocolRuleMapItem,
    ProtocolRuleStateTerm, ProvenanceKey, ProvenanceRole, SentenceKind, SetOperation, StableItemId,
    StateTransportError, TermMapOperation,
};

fn package() -> PackageId {
    testing::package("IMP", "imp-semantics")
}

fn item(name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), "calc", name, kind)
}

fn key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal)
}

fn sort(role: ProvenanceRole, ordinal: u32, sort: BuiltinSort) -> DescriptorSortReference {
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
        content: ProtocolCellContent::Leaf {
            wrapper_key: key(ProvenanceRole::ConfigurationCellWrapper, ordinal),
            wrapper,
            sort: sort(
                ProvenanceRole::ConfigurationCellContent,
                ordinal,
                content_sort,
            ),
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
        binding_key: key(ProvenanceRole::ConfigurationVariable, ordinal),
        binding: binding.into(),
        external_name_key: key(ProvenanceRole::ConfigurationVariableName, ordinal),
        external_name: external_name.into(),
        sort: sort(
            ProvenanceRole::ConfigurationVariableType,
            ordinal,
            sort_value,
        ),
        main_key: main.then(|| key(ProvenanceRole::ConfigurationVariableMain, ordinal)),
    }
}

fn variable_term(
    term_ordinal: u32,
    path_ordinal: u32,
    name: &str,
) -> ProtocolInitializerTerm<DescriptorTerm> {
    let path_key = key(ProvenanceRole::InitializerTermPath, path_ordinal);
    ProtocolInitializerTerm {
        key: key(ProvenanceRole::InitializerTerm, term_ordinal),
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
        key: key(ProvenanceRole::ConfigurationDeclaration, 0),
        fields: vec![k, env],
    };
    let initializer = DescriptorConfigurationInitializer {
        key: key(ProvenanceRole::InitializerDeclaration, 0),
        owner_key: key(ProvenanceRole::InitializerResultType, 0),
        owner: owner.clone(),
        variables: vec![
            variable(0, "pgm", "$PGM", BuiltinSort::KSequence, true),
            variable(1, "env", "$ENV", BuiltinSort::Map, false),
        ],
        body_key: key(ProvenanceRole::InitializerBody, 0),
        cells: vec![
            DescriptorInitializerCell {
                key: key(ProvenanceRole::InitializerCell, 0),
                field: DescriptorCellReference {
                    key: key(ProvenanceRole::InitializerField, 0),
                    cell: k_identity,
                },
                content: ProtocolInitializerCellContent::Leaf {
                    constructor_key: key(ProvenanceRole::InitializerCellConstructor, 0),
                    wrapper: CellWrapper::KCell,
                    value: ProtocolInitializerStateTerm::KSequence(ProtocolKSequence {
                        payload_key: Some(key(ProvenanceRole::KSequencePayload, 0)),
                        dot_k_key: None,
                        notation: DescriptorKSequenceNotation::Comma,
                        items: vec![ProtocolKSequenceItem {
                            key: key(ProvenanceRole::KSequenceItem, 0),
                            value: variable_term(0, 0, "pgm"),
                        }],
                    }),
                },
            },
            DescriptorInitializerCell {
                key: key(ProvenanceRole::InitializerCell, 1),
                field: DescriptorCellReference {
                    key: key(ProvenanceRole::InitializerField, 1),
                    cell: env_identity,
                },
                content: ProtocolInitializerCellContent::Leaf {
                    constructor_key: key(ProvenanceRole::InitializerCellConstructor, 1),
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
        .validate_complete_provenance(
            &owner,
            &key(ProvenanceRole::ConfigurationDeclaration, 0),
            &expected,
        )
        .unwrap();
    assert!(expected.contains(&key(ProvenanceRole::ConfigurationVariableType, 1)));
    assert!(expected.contains(&key(ProvenanceRole::KSequenceItem, 0)));
    assert_eq!(
        serde_json::to_value(&configuration).unwrap()["root"]["root_kind"],
        "generated_top"
    );
}

#[test]
fn fixed_configuration_rejects_wrong_keys_duplicates_and_tree_drift() {
    let (owner, configuration) = fixed_configuration();

    let mut wrong_key = configuration.clone();
    wrong_key.declaration.fields[1].reference.key = key(ProvenanceRole::ConfigurationField, 0);
    assert!(matches!(
        wrong_key.validate(&owner),
        Err(StateTransportError::UnexpectedProvenance { .. })
    ));

    let mut duplicate_external = configuration.clone();
    duplicate_external.initializer.variables[1].external_name = "$PGM".into();
    assert_eq!(
        duplicate_external.validate(&owner),
        Err(StateTransportError::DuplicateValue(
            TransportField::ExternalConfigurationVariableNames
        ))
    );

    let mut reordered = configuration.clone();
    reordered.initializer.cells.swap(0, 1);
    assert_eq!(
        reordered.validate(&owner),
        Err(StateTransportError::InitializerDeclarationMismatch)
    );

    let expected = configuration.expected_provenance_keys(&owner).unwrap();
    let mut actual = expected.clone();
    actual.insert(key(ProvenanceRole::StableSymbol, 0));
    assert_eq!(
        configuration.validate_complete_provenance(
            &owner,
            &key(ProvenanceRole::ConfigurationDeclaration, 0),
            &actual,
        ),
        Err(StateTransportError::ExtraProvenance(key(
            ProvenanceRole::StableSymbol,
            0
        )))
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
        key: key(ProvenanceRole::ConfigurationDeclaration, 0),
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
#[allow(clippy::too_many_lines)] // Constructs the complete registry and verifies sort identity.
fn builtin_registry_resolves_map_and_id() {
    let sorts = [
        HostTypeKey(marker::<0>),
        HostTypeKey(marker::<1>),
        HostTypeKey(marker::<2>),
        HostTypeKey(marker::<3>),
        HostTypeKey(marker::<4>),
        HostTypeKey(marker::<5>),
        HostTypeKey(marker::<6>),
        HostTypeKey(marker::<42>),
        HostTypeKey(marker::<53>),
    ];
    let operations = [
        HostTypeKey(marker::<7>),
        HostTypeKey(marker::<8>),
        HostTypeKey(marker::<9>),
        HostTypeKey(marker::<10>),
        HostTypeKey(marker::<11>),
        HostTypeKey(marker::<12>),
        HostTypeKey(marker::<13>),
        HostTypeKey(marker::<14>),
        HostTypeKey(marker::<15>),
        HostTypeKey(marker::<16>),
        HostTypeKey(marker::<17>),
        HostTypeKey(marker::<18>),
        HostTypeKey(marker::<19>),
        HostTypeKey(marker::<20>),
        HostTypeKey(marker::<21>),
        HostTypeKey(marker::<22>),
        HostTypeKey(marker::<23>),
        HostTypeKey(marker::<24>),
        HostTypeKey(marker::<25>),
        HostTypeKey(marker::<26>),
        HostTypeKey(marker::<27>),
        HostTypeKey(marker::<28>),
        HostTypeKey(marker::<29>),
        HostTypeKey(marker::<30>),
        HostTypeKey(marker::<31>),
        HostTypeKey(marker::<39>),
        HostTypeKey(marker::<40>),
        HostTypeKey(marker::<41>),
        HostTypeKey(marker::<51>),
    ];
    let map_operations = TermMapOperation::ALL
        .into_iter()
        .enumerate()
        .map(|(index, operation)| HostMapOperationRegistration {
            operation,
            target: match index {
                0 => HostTypeKey(marker::<32>),
                1 => HostTypeKey(marker::<43>),
                _ => HostTypeKey(marker::<44>),
            },
        })
        .collect();
    let list_operations = ListOperation::TERM_APPLICATIONS
        .into_iter()
        .enumerate()
        .map(|(index, operation)| HostListOperationRegistration {
            operation,
            target: match index {
                0 => HostTypeKey(marker::<33>),
                1 => HostTypeKey(marker::<34>),
                2 => HostTypeKey(marker::<35>),
                3 => HostTypeKey(marker::<36>),
                4 => HostTypeKey(marker::<37>),
                5 => HostTypeKey(marker::<38>),
                6 => HostTypeKey(marker::<49>),
                7 => HostTypeKey(marker::<50>),
                _ => HostTypeKey(marker::<52>),
            },
        })
        .collect();
    let set_operations = SetOperation::TERM_APPLICATIONS
        .into_iter()
        .enumerate()
        .map(|(index, operation)| HostSetOperationRegistration {
            operation,
            target: match index {
                0 => HostTypeKey(marker::<45>),
                1 => HostTypeKey(marker::<46>),
                2 => HostTypeKey(marker::<47>),
                3 => HostTypeKey(marker::<48>),
                _ => HostTypeKey(marker::<54>),
            },
        })
        .collect();
    let registry = HostBuiltinRegistry {
        sorts,
        operations,
        map_operations,
        list_operations,
        set_operations,
    };
    registry.validate().unwrap();

    assert_eq!(registry.resolve_sort(marker::<3>()), Some(BuiltinSort::Map));
    assert_eq!(registry.resolve_sort(marker::<4>()), Some(BuiltinSort::Id));

    let mut collision = registry.clone();
    collision.sorts[3] = collision.sorts[4];
    assert_eq!(
        collision.validate(),
        Err(HostBuiltinRegistryError::ReusedRustType)
    );
}

#[test]
fn primary_key_is_configuration_declaration() {
    let (owner, configuration) = fixed_configuration();
    let actual: BTreeSet<_> = configuration.expected_provenance_keys(&owner).unwrap();
    assert!(matches!(
        configuration.validate_complete_provenance(
            &owner,
            &key(ProvenanceRole::InitializerDeclaration, 0),
            &actual,
        ),
        Err(StateTransportError::UnexpectedProvenance { .. })
    ));
}

fn side_role(side: &str, left: ProvenanceRole, right: ProvenanceRole) -> ProvenanceRole {
    match side {
        "left" => left,
        "right" => right,
        _ => panic!("invalid test rule side"),
    }
}

fn rule_variable(side: &str, ordinal: u32, name: &str) -> DescriptorTerm {
    let key = key(
        side_role(
            side,
            ProvenanceRole::RuleLeftReference,
            ProvenanceRole::RuleRightReference,
        ),
        ordinal,
    );
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
        wrapper_key: key(
            side_role(
                side,
                ProvenanceRole::RuleLeftCellsWrapper,
                ProvenanceRole::RuleRightCellsWrapper,
            ),
            ordinal,
        ),
        wrapper,
        value,
    }
}

fn descriptor_context_alias() -> DescriptorContextAlias {
    let configuration = item("Machine", ItemKind::Configuration);
    DescriptorContextAlias {
        declaration_key: key(ProvenanceRole::ContextAliasDeclaration, 0),
        name_key: key(ProvenanceRole::ContextAliasName, 0),
        name: "operand_eval".into(),
        here_key: key(ProvenanceRole::ContextAliasHere, 0),
        here: "site".into(),
        pattern_key: key(ProvenanceRole::RulePattern, 0),
        configuration: DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleType, 0),
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
            key: key(ProvenanceRole::RuleLeftCellsPayload, 0),
            cells: vec![rule_cell(
                &configuration,
                "left",
                0,
                "k",
                CellWrapper::KCell,
                ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
                    payload_key: Some(key(ProvenanceRole::RuleLeftKSequencePayload, 0)),
                    dot_k_key: None,
                    notation: DescriptorKSequenceNotation::Comma,
                    items: vec![ProtocolRuleKSequenceItem {
                        key: key(ProvenanceRole::RuleLeftKSequenceItem, 0),
                        value: rule_variable("left", 0, "site"),
                    }],
                    tail: ProtocolRuleFrame::Bind {
                        key: key(ProvenanceRole::RuleLeftKSequenceTail, 0),
                        binding: "tail".into(),
                    },
                }),
            )],
            remainder: ProtocolRuleFrame::Bind {
                key: key(ProvenanceRole::RuleLeftCellsRemainder, 0),
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
            &key(ProvenanceRole::ContextAliasDeclaration, 0),
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
        Err(StateTransportError::InvalidTerm(
            StateTermReason::AliasFrameBindingMismatch
        ))
    ));

    let mut lost_configuration = alias;
    lost_configuration.pattern.remainder = ProtocolRuleFrame::Exact;
    assert!(matches!(
        lost_configuration.validate(ItemKind::ContextAlias),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::AliasBindingCatalogMismatch
        ))
    ));
}

fn term_rule_binding(name: &str, ordinal: u32, sort: DescriptorSortRef) -> DescriptorRuleBinding {
    ProtocolRuleBinding {
        name: name.into(),
        kind: ProtocolRuleBindingKind::Term {
            sort: DescriptorSortReference {
                key: key(ProvenanceRole::RuleBindingType, ordinal),
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
        key: key(ProvenanceRole::RuleLeftCellsPayload, 0),
        cells: vec![
            rule_cell(
                &configuration,
                "left",
                0,
                "k",
                CellWrapper::KCell,
                ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
                    payload_key: Some(key(ProvenanceRole::RuleLeftKSequencePayload, 0)),
                    dot_k_key: None,
                    notation: DescriptorKSequenceNotation::Comma,
                    items: vec![ProtocolRuleKSequenceItem {
                        key: key(ProvenanceRole::RuleLeftKSequenceItem, 0),
                        value: rule_variable("left", 0, "X"),
                    }],
                    tail: ProtocolRuleFrame::Bind {
                        key: key(ProvenanceRole::RuleLeftKSequenceTail, 0),
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
                    payload_key: Some(key(ProvenanceRole::RuleLeftMapPayload, 0)),
                    body: ProtocolRuleMapBody::Items {
                        items: vec![ProtocolRuleMapItem {
                            key_key: key(ProvenanceRole::RuleLeftMapKey, 0),
                            key: rule_variable("left", 1, "X"),
                            value_key: key(ProvenanceRole::RuleLeftMapValue, 0),
                            value: rule_variable("left", 2, "V"),
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
    };
    let result = DescriptorRuleCells {
        key: key(ProvenanceRole::RuleRightCellsPayload, 0),
        cells: vec![rule_cell(
            &configuration,
            "right",
            0,
            "k",
            CellWrapper::KCell,
            ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
                payload_key: Some(key(ProvenanceRole::RuleRightKSequencePayload, 0)),
                dot_k_key: None,
                notation: DescriptorKSequenceNotation::Comma,
                items: vec![ProtocolRuleKSequenceItem {
                    key: key(ProvenanceRole::RuleRightKSequenceItem, 0),
                    value: rule_variable("right", 0, "V"),
                }],
                tail: ProtocolRuleFrame::Reuse {
                    key: key(ProvenanceRole::RuleRightKSequenceTail, 0),
                    binding: "tail".into(),
                },
            }),
        )],
        remainder: ProtocolRuleFrame::Reuse {
            key: key(ProvenanceRole::RuleRightCellsRemainder, 0),
            binding: "state".into(),
        },
    };
    (
        rule_id,
        DescriptorConfigurationRule {
            sentence_kind: krs_ir::ConfigurationSentenceKind::Transition,
            label: None,
            priority: None,
            requires: None,
            claim: None,
            pattern_key: key(ProvenanceRole::RulePattern, 0),
            subject_configuration: DescriptorConfigurationReference {
                key: key(ProvenanceRole::RuleType, 0),
                configuration: configuration.clone(),
            },
            result_key: key(ProvenanceRole::RuleResult, 0),
            result_configuration: DescriptorConfigurationReference {
                key: key(ProvenanceRole::RuleResultType, 0),
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
    let start = u32::try_from(index).unwrap();
    testing::authored_in(
        package(),
        "src/calc.rs",
        testing::digest_with("1234567890abcdef".repeat(4)),
        start,
        start + 1,
    )
}

#[test]
fn configuration_rule_round_trips_with_exact_side_specific_provenance() {
    let (rule_id, rule) = var_configuration_rule();
    rule.validate(ItemKind::Rule).unwrap();
    let expected = rule.expected_provenance_keys(ItemKind::Rule).unwrap();
    rule.validate_complete_provenance(
        ItemKind::Rule,
        &key(ProvenanceRole::RuleDeclaration, 0),
        &expected,
    )
    .unwrap();
    assert!(expected.contains(&key(ProvenanceRole::RuleBindingType, 0)));
    assert!(expected.contains(&key(ProvenanceRole::RuleBindingType, 1)));
    assert!(expected.contains(&key(ProvenanceRole::RuleLeftMapRemainder, 0)));
    assert!(expected.contains(&key(ProvenanceRole::RuleRightKSequenceTail, 0)));
    assert!(
        !expected
            .iter()
            .any(|entry| entry.role() == ProvenanceRole::RuleLeftPath)
    );

    let provenance = DescriptorProvenance::new(
        key(ProvenanceRole::RuleDeclaration, 0),
        expected
            .into_iter()
            .enumerate()
            .map(|(index, key)| DescriptorNodeOrigin::new(key, rule_origin(index)))
            .collect(),
    )
    .unwrap();
    let bundle = DescriptorBundle::new(vec![krs_ir::testing::descriptor(
        rule_id,
        BTreeMap::default(),
        provenance,
        DescriptorPayload::ConfigurationRule(Box::new(rule)),
    )])
    .unwrap();
    testing::assert_canonical_contract(&bundle);
    let json = bundle.to_canonical_json().unwrap();
    assert!(json.contains(&format!(
        "\"protocol_version\": {}",
        krs_ir::SchemaVersion::CURRENT.0
    )));
    assert!(json.contains("\"configuration_rule\""));
}

#[test]
fn configuration_rule_protocol_rejects_alias_and_simplification_at_the_boundary() {
    for (kind, reason) in [
        (
            SentenceKind::Alias,
            StateTermReason::ConfigurationStaticAlias,
        ),
        (
            SentenceKind::Simplification,
            StateTermReason::ConfigurationSimplification,
        ),
    ] {
        let expected = StateTransportError::InvalidTerm(reason);
        assert_eq!(
            krs_ir::ConfigurationSentenceKind::try_from(kind).unwrap_err(),
            expected
        );
        let (_, descriptor) = var_configuration_rule();
        let mut json = serde_json::to_value(descriptor).unwrap();
        json["sentence_kind"] = serde_json::to_value(kind).unwrap();
        let error = serde_json::from_value::<DescriptorConfigurationRule>(json).unwrap_err();
        assert!(error.to_string().contains(&expected.to_string()));
    }
}

#[test]
fn configuration_requires_is_exact_and_term_binding_only() {
    let (_, mut rule) = var_configuration_rule();
    rule.requires = Some(DescriptorRuleCondition {
        key: key(ProvenanceRole::RuleRequires, 0),
        term: DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: key(ProvenanceRole::RuleRequiresApplicationHead, 0),
                application: DescriptorApplicationRef::Builtin(BuiltinOperation::IntGreater),
            },
            path_key: key(ProvenanceRole::RuleRequiresPath, 0),
            arguments: vec![
                DescriptorTermArgument::Positional {
                    value: Box::new(DescriptorTerm::Variable {
                        key: key(ProvenanceRole::RuleRequiresReference, 0),
                        path_key: key(ProvenanceRole::RuleRequiresPath, 1),
                        name: "X".into(),
                    }),
                },
                DescriptorTermArgument::Positional {
                    value: Box::new(DescriptorTerm::Literal {
                        key: key(ProvenanceRole::RuleRequiresLiteral, 0),
                        literal: DescriptorLiteral::Int("0".into()),
                    }),
                },
            ]
            .try_into()
            .unwrap(),
        },
    });

    let expected = rule.expected_provenance_keys(ItemKind::Rule).unwrap();
    assert!(expected.contains(&key(ProvenanceRole::RuleRequires, 0)));
    assert!(expected.contains(&key(ProvenanceRole::RuleRequiresPath, 0)));
    assert!(expected.contains(&key(ProvenanceRole::RuleRequiresPath, 1)));
    assert!(expected.contains(&key(ProvenanceRole::RuleRequiresApplicationHead, 0)));
    assert!(expected.contains(&key(ProvenanceRole::RuleRequiresReference, 0)));
    assert!(expected.contains(&key(ProvenanceRole::RuleRequiresLiteral, 0)));

    let mut structural_frame = rule.clone();
    let DescriptorTerm::Application { arguments, .. } =
        &mut structural_frame.requires.as_mut().unwrap().term
    else {
        unreachable!()
    };
    let krs_ir::Arguments::Positional(arguments) = arguments else {
        unreachable!()
    };
    let value = &mut arguments[0];
    let DescriptorTerm::Variable { name, .. } = value.as_mut() else {
        unreachable!()
    };
    *name = "tail".into();
    assert!(matches!(
        structural_frame.validate(ItemKind::Rule),
        Err(StateTransportError::InvalidTerm(
            StateTermReason::RuleVariableBindingIsNotATerm
        ))
    ));

    let mut state_role_in_term = rule.clone();
    let DescriptorTerm::Application { arguments, .. } =
        &mut state_role_in_term.requires.as_mut().unwrap().term
    else {
        unreachable!()
    };
    let krs_ir::Arguments::Positional(arguments) = arguments else {
        unreachable!()
    };
    let value = &mut arguments[1];
    let DescriptorTerm::Literal {
        key: literal_key, ..
    } = value.as_mut()
    else {
        unreachable!()
    };
    *literal_key = key(ProvenanceRole::CellsPayload, 0);
    assert!(matches!(
        state_role_in_term.validate(ItemKind::Rule),
        Err(StateTransportError::UnexpectedProvenance { .. })
    ));

    let mut wrong_nested_role = rule;
    let DescriptorTerm::Application { arguments, .. } =
        &mut wrong_nested_role.requires.as_mut().unwrap().term
    else {
        unreachable!()
    };
    let krs_ir::Arguments::Positional(arguments) = arguments else {
        unreachable!()
    };
    let value = &mut arguments[1];
    let DescriptorTerm::Literal {
        key: literal_key, ..
    } = value.as_mut()
    else {
        unreachable!()
    };
    *literal_key = key(ProvenanceRole::RuleRightLiteral, 0);
    assert!(matches!(
        wrong_nested_role.validate(ItemKind::Rule),
        Err(StateTransportError::UnexpectedProvenance { .. })
    ));
}

#[test]
fn configuration_rule_rejects_binding_frame_and_provenance_drift() {
    let (_, rule) = var_configuration_rule();

    let mut wrong_order = rule.clone();
    wrong_order.bindings.swap(0, 1);
    assert!(matches!(
        wrong_order.validate(ItemKind::Rule),
        Err(StateTransportError::InvalidTerm(_))
    ));

    let mut wrong_kind = rule.clone();
    wrong_kind.bindings[1].kind = ProtocolRuleBindingKind::MapFrame;
    assert!(matches!(
        wrong_kind.validate(ItemKind::Rule),
        Err(StateTransportError::InvalidTerm(_))
    ));

    let mut wrong_sort_key = rule.clone();
    let ProtocolRuleBindingKind::Term { sort } = &mut wrong_sort_key.bindings[2].kind else {
        unreachable!()
    };
    sort.key = key(ProvenanceRole::RuleBindingType, 2);
    assert!(matches!(
        wrong_sort_key.validate(ItemKind::Rule),
        Err(StateTransportError::UnexpectedProvenance { .. })
    ));

    let mut wrong_sort_kind = rule.clone();
    let ProtocolRuleBindingKind::Term { sort } = &mut wrong_sort_kind.bindings[2].kind else {
        unreachable!()
    };
    sort.sort = DescriptorSortRef::Declared(item("Machine", ItemKind::Configuration));
    assert!(matches!(
        wrong_sort_kind.validate(ItemKind::Rule),
        Err(StateTransportError::ItemKind { .. })
    ));

    let mut unbound_reuse = rule.clone();
    unbound_reuse.result.remainder = ProtocolRuleFrame::Reuse {
        key: key(ProvenanceRole::RuleRightCellsRemainder, 0),
        binding: "missing".into(),
    };
    assert!(matches!(
        unbound_reuse.validate(ItemKind::Rule),
        Err(StateTransportError::InvalidTerm(_))
    ));

    let mut wrong_result_kind = rule.clone();
    wrong_result_kind.result.remainder = ProtocolRuleFrame::Reuse {
        key: key(ProvenanceRole::RuleRightCellsRemainder, 0),
        binding: "rest".into(),
    };
    assert!(matches!(
        wrong_result_kind.validate(ItemKind::Rule),
        Err(StateTransportError::InvalidTerm(_))
    ));

    let mut wrong_side = rule;
    wrong_side.result.cells[0].field.key = key(ProvenanceRole::RuleLeftCellsField, 0);
    assert!(matches!(
        wrong_side.validate(ItemKind::Rule),
        Err(StateTransportError::UnexpectedProvenance { .. })
    ));
}

fn wildcard_configuration_rule() -> DescriptorConfigurationRule {
    let configuration = item("Machine", ItemKind::Configuration);
    DescriptorConfigurationRule {
        sentence_kind: krs_ir::ConfigurationSentenceKind::Transition,
        label: None,
        priority: None,
        requires: None,
        claim: None,
        pattern_key: key(ProvenanceRole::RulePattern, 0),
        subject_configuration: DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleType, 0),
            configuration: configuration.clone(),
        },
        result_key: key(ProvenanceRole::RuleResult, 0),
        result_configuration: DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleResultType, 0),
            configuration: configuration.clone(),
        },
        bindings: Vec::new(),
        subject: DescriptorRuleCells {
            key: key(ProvenanceRole::RuleLeftCellsPayload, 0),
            cells: vec![rule_cell(
                &configuration,
                "left",
                0,
                "control",
                CellWrapper::Cell,
                ProtocolRuleStateTerm::Term(DescriptorTerm::Wildcard {
                    key: key(ProvenanceRole::RuleLeftWildcard, 0),
                }),
            )],
            remainder: ProtocolRuleFrame::Exact,
        },
        result: DescriptorRuleCells {
            key: key(ProvenanceRole::RuleRightCellsPayload, 0),
            cells: vec![rule_cell(
                &configuration,
                "right",
                0,
                "control",
                CellWrapper::Cell,
                ProtocolRuleStateTerm::Term(DescriptorTerm::Literal {
                    key: key(ProvenanceRole::RuleRightLiteral, 0),
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
    assert!(keys.contains(&key(ProvenanceRole::RuleLeftWildcard, 0)));

    let mut wrong_ordinal = rule.clone();
    let ProtocolRuleStateTerm::Term(DescriptorTerm::Wildcard { key: wildcard }) =
        &mut wrong_ordinal.subject.cells[0].value
    else {
        unreachable!()
    };
    *wildcard = key(ProvenanceRole::RuleLeftWildcard, 1);
    assert!(matches!(
        wrong_ordinal.validate(ItemKind::Rule),
        Err(StateTransportError::UnexpectedProvenance { .. })
    ));

    let mut result_wildcard = rule;
    result_wildcard.result.cells[0].value = ProtocolRuleStateTerm::Term(DescriptorTerm::Wildcard {
        key: key(ProvenanceRole::RuleLeftWildcard, 0),
    });
    assert!(matches!(
        result_wildcard.validate(ItemKind::Rule),
        Err(StateTransportError::InvalidTerm(_))
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
        key: key(ProvenanceRole::RuleType, 0),
        configuration: HostTypeReference {
            key: configuration_key,
            authored_path: "Machine".into(),
        },
    };
    let host_cell = |side: &str, value| ProtocolRuleCell {
        field: HostCellReference {
            key: key(
                side_role(
                    side,
                    ProvenanceRole::RuleLeftCellsField,
                    ProvenanceRole::RuleRightCellsField,
                ),
                0,
            ),
            cell: HostCellIdentity {
                owner: configuration_key,
                field: host_type_key::<HostRuleCellField>(),
            },
        },
        wrapper_key: key(
            side_role(
                side,
                ProvenanceRole::RuleLeftCellsWrapper,
                ProvenanceRole::RuleRightCellsWrapper,
            ),
            0,
        ),
        wrapper: CellWrapper::Cell,
        value: ProtocolRuleStateTerm::Term(value),
    };
    HostConfigurationRule {
        sentence_kind: krs_ir::ConfigurationSentenceKind::Transition,
        label: None,
        priority: None,
        requires: None,
        claim: None,
        pattern_key: key(ProvenanceRole::RulePattern, 0),
        subject_configuration: configuration(),
        result_key: key(ProvenanceRole::RuleResult, 0),
        result_configuration: HostConfigurationReference {
            key: key(ProvenanceRole::RuleResultType, 0),
            ..configuration()
        },
        bindings: Vec::new(),
        subject: HostRuleCells {
            key: key(ProvenanceRole::RuleLeftCellsPayload, 0),
            cells: vec![host_cell(
                "left",
                HostTerm::Wildcard {
                    key: key(ProvenanceRole::RuleLeftWildcard, 0),
                },
            )],
            remainder: ProtocolRuleFrame::Exact,
        },
        result: HostRuleCells {
            key: key(ProvenanceRole::RuleRightCellsPayload, 0),
            cells: vec![host_cell(
                "right",
                HostTerm::Literal {
                    key: key(ProvenanceRole::RuleRightLiteral, 0),
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
                key: key(ProvenanceRole::RuleBindingType, 0),
                target: HostTypeReference {
                    key: host_type_key::<HostRuleTermSort>(),
                    authored_path: "Value".into(),
                },
            },
        },
    }];
    rule.subject.cells[0].value = ProtocolRuleStateTerm::Term(HostTerm::Variable {
        key: key(ProvenanceRole::RuleLeftReference, 0),
        path_key: key(ProvenanceRole::RuleLeftReference, 0),
        name: "X".into(),
    });
    rule.result.cells[0].value = ProtocolRuleStateTerm::Term(HostTerm::Variable {
        key: key(ProvenanceRole::RuleRightReference, 0),
        path_key: key(ProvenanceRole::RuleRightReference, 0),
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
    *wildcard = key(ProvenanceRole::RuleLeftLiteral, 0);
    assert!(matches!(
        wrong_role.validate(ItemKind::Rule),
        Err(StateTransportError::UnexpectedProvenance { .. })
    ));

    let mut result_wildcard = rule;
    result_wildcard.result.cells[0].value = ProtocolRuleStateTerm::Term(HostTerm::Wildcard {
        key: key(ProvenanceRole::RuleLeftWildcard, 0),
    });
    assert!(matches!(
        result_wildcard.validate(ItemKind::Rule),
        Err(StateTransportError::InvalidTerm(_))
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
        Err(StateTransportError::InvalidTerm(_))
    ));

    let mut wrong_sort_key = rule;
    let ProtocolRuleBindingKind::Term { sort } = &mut wrong_sort_key.bindings[0].kind else {
        unreachable!()
    };
    sort.key = key(ProvenanceRole::RuleBindingType, 1);
    assert!(matches!(
        wrong_sort_key.validate(ItemKind::Rule),
        Err(StateTransportError::UnexpectedProvenance { .. })
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
            payload_key: Some(key(ProvenanceRole::RuleRightMapPayload, 0)),
            body: ProtocolRuleMapBody::Update {
                base_key: key(ProvenanceRole::RuleRightMapUpdateBase, 0),
                base: rule_variable("right", 1, "E"),
                key_key: key(ProvenanceRole::RuleRightMapKey, 0),
                key: rule_variable("right", 2, "X"),
                value_key: key(ProvenanceRole::RuleRightMapValue, 0),
                value: rule_variable("right", 3, "V"),
            },
        }),
    ));
    rule.validate(ItemKind::Rule).unwrap();
    let keys = rule.expected_provenance_keys(ItemKind::Rule).unwrap();
    assert!(keys.contains(&key(ProvenanceRole::RuleRightMapUpdateBase, 0)));
    assert!(keys.contains(&key(ProvenanceRole::RuleRightCellsField, 1)));
}

#[test]
fn repeated_cell_collection_spelling_is_closed_at_the_boundary() {
    use krs_ir::transport::configuration::DescriptorCellCollectionType;

    for (spelling, collection) in [
        ("Bag", DescriptorCellCollectionType::Bag),
        ("List", DescriptorCellCollectionType::List),
        ("Map", DescriptorCellCollectionType::Map),
        ("Set", DescriptorCellCollectionType::Set),
    ] {
        assert_eq!(
            DescriptorCellCollectionType::try_from(spelling.to_owned()).unwrap(),
            collection
        );
        let json = serde_json::to_string(spelling).unwrap();
        assert_eq!(serde_json::to_string(&collection).unwrap(), json);
        assert_eq!(
            serde_json::from_str::<DescriptorCellCollectionType>(&json).unwrap(),
            collection
        );
    }

    for spelling in ["", "bag", "sample", "Other"] {
        let expected =
            StateTransportError::InvalidTerm(StateTermReason::UnsupportedRepeatedCellCollection);
        assert_eq!(
            DescriptorCellCollectionType::try_from(spelling.to_owned()).unwrap_err(),
            expected
        );
        let json = serde_json::to_string(spelling).unwrap();
        assert!(
            serde_json::from_str::<DescriptorCellCollectionType>(&json)
                .unwrap_err()
                .to_string()
                .starts_with(&expected.to_string())
        );
    }
}

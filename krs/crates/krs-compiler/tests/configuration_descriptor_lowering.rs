//! Stable configuration descriptors reach the existing semantic/Definition lane.

use krs_ir::testing::DescriptorBundleInputs;

use std::collections::BTreeSet;

use krs_compiler::lower_descriptor_bundle;
use krs_compiler::testing::assert_lowering_contract;
use krs_ir::testing::assert_canonical_contract;
use krs_ir::{
    BuiltinSort, CellStream, CellWrapper, DescriptorCellExit, DescriptorCellField,
    DescriptorCellReference, DescriptorCellStream, DescriptorFixedConfiguration,
    DescriptorInitializerCell, DescriptorPayload, DescriptorSortRef, DescriptorTerm, ItemKind,
    ProtocolCellContent, ProtocolInitializerCellContent, ProtocolInitializerStateTerm,
    ProtocolInitializerTerm, ProtocolRuleFrame, ProtocolRuleMap, ProtocolRuleMapBody,
    ProtocolRuleMapItem, ProtocolRuleStateTerm, ProvenanceRole, RuleSide, SortDescriptor,
};

#[path = "fixtures/configuration.rs"]
mod fixture;

use fixture::{bundle, cell_field, descriptor, id, key, provenance, rule_cell, variable};

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
        rule.clauses()[1].as_fixed().unwrap().after(),
        krs_ir::CellPost::Preserve
    ));
    let (lowered, emitted) = assert_lowering_contract(&semantic);
    // Each cell records the Rust field that declares it, for tools that address cells by
    // their KRS names.
    let fields = lowered
        .definition()
        .modules()
        .iter()
        .flat_map(krs_ir_levels::DefinitionModule::sentences)
        .find_map(|sentence| match sentence {
            krs_ir_levels::DefinitionSentence::Configuration(configuration) => Some(
                configuration
                    .cells()
                    .iter()
                    .map(|cell| (cell.name().to_owned(), cell.field().map(str::to_owned)))
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        fields,
        [
            ("k".to_owned(), Some("k".to_owned())),
            ("env".to_owned(), Some("env".to_owned()))
        ]
    );
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
    let ProtocolRuleStateTerm::KSequence(result_k) =
        &mut rule.result.as_mut().unwrap().cells[0].value
    else {
        unreachable!();
    };
    result_k.items[0].value = variable(ProvenanceRole::RuleRightReference, 0, "X");
    let owner = rule.subject_configuration.configuration.clone();
    rule.result.as_mut().unwrap().cells.push(rule_cell(
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
    let env = rewrite.clauses()[1].as_fixed().unwrap();
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

/// `env: Cell(k::map![])` on a cell declared `Int` is refused at the empty
/// map's own key, anchored at its `k::map![]` invocation, not at the cell.
#[test]
fn an_empty_map_in_a_non_map_rule_cell_is_reported_at_its_spelling() {
    let mut bundle = bundle();
    let mut descriptors = bundle.descriptors.clone();
    for entry in &mut descriptors {
        match &mut entry.payload {
            DescriptorPayload::FixedConfiguration(configuration) => {
                set_leaf_sort(&mut configuration.declaration.fields[1], BuiltinSort::Int);
                configuration.initializer.variables[1].sort.sort =
                    DescriptorSortRef::Builtin(BuiltinSort::Int);
                *entry = descriptor(entry.id.clone(), entry.payload.clone());
            }
            DescriptorPayload::ConfigurationRule(rule) => {
                rule.subject.cells[1].value = ProtocolRuleStateTerm::Map(ProtocolRuleMap {
                    payload_key: Some(key(ProvenanceRole::RuleLeftMapPayload, 0)),
                    body: ProtocolRuleMapBody::Empty {
                        explicit_dot: false,
                    },
                });
                let ProtocolRuleStateTerm::KSequence(result_k) =
                    &mut rule.result.as_mut().unwrap().cells[0].value
                else {
                    unreachable!();
                };
                result_k.items[0].value = variable(ProvenanceRole::RuleRightReference, 0, "X");
                rule.bindings
                    .retain(|binding| matches!(binding.name.as_str(), "X" | "tail" | "state"));
            }
            _ => {}
        }
    }
    bundle.descriptors = descriptors;
    refresh_rule_provenance(&mut bundle);
    let bundle = bundle.build().unwrap();
    let error = lower_descriptor_bundle(&bundle).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("map occurs in a non-Map rule cell"),
        "unexpected error: {error}"
    );
    let rule = bundle
        .descriptors()
        .iter()
        .find(|descriptor| {
            matches!(
                descriptor.payload(),
                DescriptorPayload::ConfigurationRule(_)
            )
        })
        .unwrap();
    let range_of = |role| {
        rule.provenance()
            .origin_for(&key(role, 0))
            .and_then(krs_ir::OriginStack::exact_authored_range)
            .unwrap()
    };
    assert_eq!(
        error.range(),
        Some(&range_of(ProvenanceRole::RuleLeftMapPayload))
    );
    assert_ne!(
        error.range(),
        Some(&range_of(ProvenanceRole::RuleLeftCellsField))
    );
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
    rule.result.as_mut().unwrap().cells[0].field.cell.field = "env".into();
    let ProtocolRuleStateTerm::KSequence(sequence) =
        &mut rule.result.as_mut().unwrap().cells[0].value
    else {
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
    let ProtocolRuleStateTerm::KSequence(sequence) =
        &mut rule.result.as_mut().unwrap().cells[0].value
    else {
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
            assert!(
                matches!(
                    &error,
                    krs_compiler::DescriptorLoweringError::DanglingReference { id, .. }
                        if **id == reference
                ),
                "{error:?}"
            );
            assert_eq!(
                error.to_string(),
                format!("dangling descriptor reference {reference}")
            );
        } else {
            assert!(
                matches!(
                    &error,
                    krs_compiler::DescriptorLoweringError::ReferenceKindMismatch {
                        id,
                        expected: ItemKind::Sort,
                        actual: ItemKind::Configuration,
                        ..
                    } if **id == reference
                ),
                "{error:?}"
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
            value: "?".into(),
        });
        env.exit = Some(exit(1));
    });
    assert!(
        error.contains("exit cell `env` is a repeated cell"),
        "{error}"
    );
}

#[test]
fn a_stream_cell_is_outside_every_repeated_cell() {
    let error = console_error(|configuration| {
        let env = &mut configuration.declaration.fields[1];
        set_leaf_sort(env, BuiltinSort::List);
        env.multiplicity = Some(krs_ir::DescriptorCellMultiplicity {
            key: key(ProvenanceRole::ConfigurationCellMultiplicity, 1),
            value: "?".into(),
        });
        env.stream = Some(stream(1, CellStream::Stdout));
    });
    assert!(
        error.contains("stream cell `env` is a repeated cell"),
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

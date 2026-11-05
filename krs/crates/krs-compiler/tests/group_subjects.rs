//! Sentences about a `#[k::cell]` group: a library's rule written for its group is lowered
//! against each definition's own configuration, and its subject is judged against it.
//!
//! The library package (the configuration fixture's) declares the group `Core { k, env }`, the
//! `Value` sort and the rule `var`, which moves a value of `env` into the computation and is
//! about `Core`. Each definition package declares a configuration that holds `Core`, and the
//! rule's descriptor names that configuration, as collection gives it to every definition that
//! selects the library.

use std::collections::BTreeSet;

use krs_compiler::{
    DescriptorLoweringError, emit_k, lower_descriptor_bundle, lower_semantic_theory,
};
use krs_ir::testing::{self, DescriptorBundleInputs, DescriptorInputs};
use krs_ir::{
    BuiltinSort, CellWrapper, DescriptorCellCollectionType, DescriptorCellDeclarationReference,
    DescriptorCellIdentity, DescriptorCellMultiplicity, DescriptorCellReference,
    DescriptorCellType, DescriptorComputationCell, DescriptorConfigurationDeclaration,
    DescriptorConfigurationInitializer, DescriptorConfigurationReference,
    DescriptorConfigurationRoot, DescriptorContextAlias, DescriptorFixedConfiguration,
    DescriptorHeadRule, DescriptorInitializerCell, DescriptorKSequenceNotation, DescriptorPayload,
    DescriptorRuleCells, DescriptorSubject, DescriptorTerm, ItemKind, PackageId,
    ProtocolCellContent, ProtocolContextAliasBinding, ProtocolContextAliasBindingKind,
    ProtocolHeadRuleExtra, ProtocolHeadRuleHead, ProtocolHeadRuleResult,
    ProtocolInitializerCellContent, ProtocolInitializerStateTerm, ProtocolInitializerTerm,
    ProtocolKSequence, ProtocolKSequenceItem, ProtocolRuleFrame, ProtocolRuleKSequence,
    ProtocolRuleKSequenceItem, ProtocolRuleStateTerm, ProvenanceKey, ProvenanceRole, SentenceKind,
    SortDescriptor, StableItemId,
};

#[path = "fixtures/configuration.rs"]
#[expect(dead_code, reason = "The shared fixture serves several test files.")]
mod fixture;

use fixture::{
    cell_field, configuration_rule, descriptor, framework_kitem, id, initializer_variable, key,
    provenance, rule_cell, variable,
};

/// A cell of a definition's configuration, as the test writes it.
enum Cell {
    /// A leaf cell holding a configuration variable of this name and sort.
    Variable(&'static str, BuiltinSort),
    /// A field holding a group, whose cells hold these configuration variables.
    Group(
        &'static str,
        Vec<(&'static str, &'static str, CellWrapper, BuiltinSort)>,
    ),
    /// A field holding a group with this multiplicity: `?`, `*` (a `List` collection), or `*`
    /// with a collection type (`*Map`, `*Set`).
    Held(
        &'static str,
        &'static str,
        Vec<(&'static str, &'static str, CellWrapper, BuiltinSort)>,
    ),
}

/// A definition package's identity: `KRS-<NAME>`.
fn definition_package(name: &str) -> PackageId {
    testing::package(&format!("KRS-{}", name.to_ascii_uppercase()), name)
}

/// A `#[k::cell]` group of the library, its fields given as `(field, wrapper, sort)`.
fn group(name: &str, fields: &[(&str, CellWrapper, BuiltinSort)]) -> DescriptorInputs {
    let owner = id(name, ItemKind::Cell);
    let declaration = DescriptorConfigurationDeclaration {
        key: key(ProvenanceRole::ConfigurationDeclaration, 0),
        fields: fields
            .iter()
            .zip(0..)
            .map(|(&(field, wrapper, sort), ordinal)| {
                cell_field(&owner, ordinal, field, wrapper, sort)
            })
            .collect(),
    };
    let keys = declaration.expected_provenance_keys(&owner).unwrap();
    DescriptorInputs::new(
        owner,
        std::collections::BTreeMap::default(),
        provenance(key(ProvenanceRole::ConfigurationDeclaration, 0), keys),
        DescriptorPayload::Cell(Box::new(declaration)),
    )
}

#[expect(
    clippy::too_many_lines,
    reason = "The declaration, the variables and the initializer of each cell are built together."
)]
/// The configuration `Name` of the package `definition_package(name)`, its cells given in
/// order. Every leaf cell holds a configuration variable; the first variable is the main one.
fn configuration(name: &str, cells: &[Cell]) -> DescriptorInputs {
    let owner = configuration_id(name);
    let mut fields = Vec::new();
    let mut variables = Vec::new();
    let mut initializer = Vec::new();
    let mut ordinal = 0;
    let mut next = || {
        ordinal += 1;
        ordinal - 1
    };
    let leaf = |cell: &DescriptorCellIdentity,
                variable_name: &str,
                wrapper: CellWrapper,
                sort: BuiltinSort,
                variables: &mut Vec<_>,
                index: u32| {
        let main = variables.is_empty();
        variables.push(initializer_variable(
            u32::try_from(variables.len()).unwrap(),
            variable_name,
            &variable_name.to_ascii_uppercase(),
            sort,
            main,
        ));
        let term = ProtocolInitializerTerm {
            key: key(ProvenanceRole::InitializerTerm, index),
            term: variable(ProvenanceRole::InitializerTermPath, index, variable_name),
        };
        DescriptorInitializerCell {
            absent: None,
            key: key(ProvenanceRole::InitializerCell, index),
            field: DescriptorCellReference {
                key: key(ProvenanceRole::InitializerField, index),
                cell: cell.clone(),
            },
            content: ProtocolInitializerCellContent::Leaf {
                constructor_key: key(ProvenanceRole::InitializerCellConstructor, index),
                wrapper,
                value: if wrapper == CellWrapper::KCell {
                    ProtocolInitializerStateTerm::KSequence(ProtocolKSequence {
                        payload_key: key(ProvenanceRole::KSequencePayload, index),
                        dot_k_key: None,
                        notation: krs_ir::DescriptorKSequenceNotation::Comma,
                        items: vec![ProtocolKSequenceItem {
                            key: key(ProvenanceRole::KSequenceItem, index),
                            value: term,
                        }],
                    })
                } else {
                    ProtocolInitializerStateTerm::Term(term)
                },
            },
        }
    };
    for (field_ordinal, cell) in (0..).zip(cells) {
        match cell {
            Cell::Variable(field, sort) => {
                let index = next();
                let declared = cell_field(&owner, field_ordinal, field, CellWrapper::Cell, *sort);
                initializer.push(leaf(
                    &declared.reference.cell,
                    field,
                    CellWrapper::Cell,
                    *sort,
                    &mut variables,
                    index,
                ));
                fields.push(declared);
            }
            Cell::Group(field, children) | Cell::Held(field, _, children) => {
                let index = next();
                let group = id(children_owner(children), ItemKind::Cell);
                let mut declared = cell_field(
                    &owner,
                    field_ordinal,
                    field,
                    CellWrapper::Cell,
                    BuiltinSort::Int,
                );
                declared.content = ProtocolCellContent::Nested {
                    declaration: DescriptorCellDeclarationReference {
                        key: key(ProvenanceRole::ConfigurationCellContent, field_ordinal),
                        declaration: group.clone(),
                    },
                };
                if let Cell::Held(_, multiplicity, _) = cell {
                    let (mark, order) = multiplicity.split_at(1);
                    declared.multiplicity = Some(DescriptorCellMultiplicity {
                        key: key(ProvenanceRole::ConfigurationCellMultiplicity, field_ordinal),
                        value: mark.to_owned(),
                    });
                    if mark == "*" {
                        declared.cell_type = Some(DescriptorCellType {
                            key: key(ProvenanceRole::ConfigurationCellType, field_ordinal),
                            value: match order {
                                "Map" => DescriptorCellCollectionType::Map,
                                "Set" => DescriptorCellCollectionType::Set,
                                _ => DescriptorCellCollectionType::List,
                            },
                        });
                    }
                }
                initializer.push(DescriptorInitializerCell {
                    absent: None,
                    key: key(ProvenanceRole::InitializerCell, index),
                    field: DescriptorCellReference {
                        key: key(ProvenanceRole::InitializerField, index),
                        cell: declared.reference.cell.clone(),
                    },
                    content: ProtocolInitializerCellContent::Nested {
                        declaration: DescriptorCellDeclarationReference {
                            key: key(ProvenanceRole::InitializerNestedConstructor, index),
                            declaration: group.clone(),
                        },
                        children: children
                            .iter()
                            .map(|&(_, child, wrapper, sort)| {
                                let index = next();
                                let cell = DescriptorCellIdentity {
                                    owner: group.clone(),
                                    field: child.into(),
                                };
                                leaf(
                                    &cell,
                                    &format!("{field}_{child}"),
                                    wrapper,
                                    sort,
                                    &mut variables,
                                    index,
                                )
                            })
                            .collect(),
                    },
                });
                fields.push(declared);
            }
        }
    }
    let payload = DescriptorFixedConfiguration {
        root: DescriptorConfigurationRoot::GeneratedTop,
        declaration: DescriptorConfigurationDeclaration {
            key: key(ProvenanceRole::ConfigurationDeclaration, 0),
            fields,
        },
        initializer: DescriptorConfigurationInitializer {
            key: key(ProvenanceRole::InitializerDeclaration, 0),
            owner_key: key(ProvenanceRole::InitializerResultType, 0),
            owner: owner.clone(),
            variables,
            body_key: key(ProvenanceRole::InitializerBody, 0),
            cells: initializer,
        },
    };
    descriptor(
        owner,
        DescriptorPayload::FixedConfiguration(Box::new(payload)),
    )
}

/// The identity of the configuration [`configuration`] declares for `name`.
fn configuration_id(name: &str) -> StableItemId {
    testing::item_in(
        definition_package(name),
        "state",
        &format!("{}{}", name[..1].to_ascii_uppercase(), &name[1..]),
        ItemKind::Configuration,
    )
}

/// The group a [`Cell::Group`]'s children belong to: every child names it.
fn children_owner<'a>(children: &[(&'a str, &str, CellWrapper, BuiltinSort)]) -> &'a str {
    let owners = children
        .iter()
        .map(|&(owner, ..)| owner)
        .collect::<BTreeSet<_>>();
    assert_eq!(owners.len(), 1, "one group per field");
    owners.into_iter().next().unwrap()
}

/// `Core`'s cells as a configuration field holds them.
fn core_cells() -> Vec<(&'static str, &'static str, CellWrapper, BuiltinSort)> {
    vec![
        ("Core", "k", CellWrapper::KCell, BuiltinSort::KSequence),
        ("Core", "env", CellWrapper::Cell, BuiltinSort::Map),
    ]
}

fn core() -> DescriptorInputs {
    group(
        "Core",
        &[
            ("k", CellWrapper::KCell, BuiltinSort::KSequence),
            ("env", CellWrapper::Cell, BuiltinSort::Map),
        ],
    )
}

/// The library rule `var`, about `subject`, lowered against `configuration`.
fn library_rule(configuration: &StableItemId, subject: &str) -> DescriptorInputs {
    let mut rule = configuration_rule(&id("Core", ItemKind::Cell));
    let reference = |role| DescriptorConfigurationReference {
        key: key(role, 0),
        configuration: configuration.clone(),
        subject: Some(DescriptorSubject::Group {
            declaration: id(subject, ItemKind::Cell),
        }),
    };
    rule.subject_configuration = reference(ProvenanceRole::RuleType);
    rule.result_configuration = Some(reference(ProvenanceRole::RuleResultType));
    descriptor(
        id("var", ItemKind::Rule),
        DescriptorPayload::ConfigurationRule(Box::new(rule)),
    )
}

/// A definition: the library (the framework `KItem`, `Value`, `Core`, `extra` and the rule
/// `var` about `subject`) and the configuration `name` with `cells`.
fn definition(
    name: &str,
    cells: &[Cell],
    subject: &str,
    extra: Vec<DescriptorInputs>,
) -> DescriptorBundleInputs {
    let configuration = configuration(name, cells);
    let rule = library_rule(&configuration.id, subject);
    let sort = |id| {
        descriptor(
            id,
            DescriptorPayload::Sort(SortDescriptor {
                parents: BTreeSet::new(),
            }),
        )
    };
    let mut descriptors = vec![
        sort(framework_kitem()),
        sort(id("Value", ItemKind::Sort)),
        core(),
        configuration,
        rule,
    ];
    descriptors.extend(extra);
    DescriptorBundleInputs::new(descriptors)
}

/// The emitted module `name`: its text from `module NAME` to its `endmodule`.
fn module<'a>(source: &'a str, name: &str) -> &'a str {
    let start = source
        .find(&format!("module {name}\n"))
        .unwrap_or_else(|| panic!("no module {name} in:\n{source}"));
    let end = start + source[start..].find("endmodule").unwrap();
    &source[start..end]
}

fn emitted(bundle: &DescriptorBundleInputs) -> String {
    let theory = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap();
    let lowered = lower_semantic_theory(&theory).unwrap();
    emit_k(&lowered).unwrap().source().to_owned()
}

fn refusal(bundle: &DescriptorBundleInputs) -> DescriptorLoweringError {
    lower_descriptor_bundle(&bundle.build().unwrap()).unwrap_err()
}

/// One library rule about `Core`, in two definitions whose configurations hold `Core` beside
/// different cells: the rule's text is the same in both, and the library's module imports each
/// definition's own configuration module, which breaks the import cycle a library rule naming
/// its definition's cells would close.
#[test]
fn a_library_rule_about_a_group_has_one_text_in_every_definition_holding_the_group() {
    let small = emitted(&definition(
        "small",
        &[
            Cell::Group("core", core_cells()),
            Cell::Variable("mem", BuiltinSort::Map),
        ],
        "Core",
        Vec::new(),
    ));
    let big = emitted(&definition(
        "big",
        &[
            Cell::Group("core", core_cells()),
            Cell::Variable("timer", BuiltinSort::Int),
            Cell::Variable("mem", BuiltinSort::Map),
        ],
        "Core",
        Vec::new(),
    ));
    // The module's sentences: everything but its header and its imports.
    let rules = |source: &str| {
        module(source, "KRS-STATE")
            .lines()
            .skip(1)
            .filter(|line| !line.trim().starts_with("imports ") && !line.trim().is_empty())
            .collect::<Vec<_>>()
            .join("\n")
    };
    let imports = |source: &str| {
        module(source, "KRS-STATE")
            .lines()
            .filter_map(|line| line.trim().strip_prefix("imports "))
            .map(str::to_owned)
            .collect::<BTreeSet<_>>()
    };
    expect_test::expect![[r#"
        (
            "  // KRS state/src/calc.rs: var\n  rule [var]:\n    <k> X:Id ~> Tail:K => V:Value ~> Tail:K </k>\n    <env> X:Id |-> V:Value Rest:Map </env>",
            {
                "ID-SYNTAX",
                "KRS-SMALL-CONFIGURATION",
                "KRS-STATE-SYNTAX",
                "MAP",
            },
        )
    "#]].assert_debug_eq(&(rules(&small), imports(&small)));
    assert_eq!(rules(&small), rules(&big), "{small}\n{big}");
    assert!(imports(&big).contains("KRS-BIG-CONFIGURATION"), "{big}");
    assert!(
        imports(&small).iter().all(|import| !import.contains("BIG")),
        "{small}"
    );
    for (source, configured) in [(&small, "KRS-SMALL"), (&big, "KRS-BIG")] {
        assert!(
            module(source, configured)
                .lines()
                .any(|line| line.trim() == format!("imports {configured}-CONFIGURATION")),
            "{source}"
        );
    }
}

/// A rule about a group the configuration does not hold has no cells to be about. Collection
/// refuses it before a descriptor exists, so semantic analysis states the disagreement.
#[test]
fn a_rule_about_a_group_the_configuration_does_not_hold_is_refused() {
    let error = refusal(&definition(
        "small",
        &[Cell::Group("core", core_cells())],
        "Other",
        vec![group(
            "Other",
            &[("x", CellWrapper::Cell, BuiltinSort::Int)],
        )],
    ));
    expect_test::expect![[r#"
        "the sentence is about the group `Other`, which has no position a rule about it applies at in the configuration `Small`: no cell of `Small` holds it"
    "#]]
    .assert_debug_eq(&match &error {
        DescriptorLoweringError::ParserReferenceDisagreement { detail, .. } => detail.clone(),
        other => panic!("{other:?}"),
    });
}

/// A rule about the group `Other` that names `Core`'s cells names cells outside its subject.
#[test]
fn a_rule_about_a_group_naming_another_groups_cells_is_refused() {
    let error = refusal(&definition(
        "small",
        &[
            Cell::Group("core", core_cells()),
            Cell::Group(
                "other",
                vec![("Other", "x", CellWrapper::Cell, BuiltinSort::Int)],
            ),
        ],
        "Other",
        vec![group(
            "Other",
            &[("x", CellWrapper::Cell, BuiltinSort::Int)],
        )],
    ));
    assert!(
        matches!(error, DescriptorLoweringError::CellOutsideSubject { .. }),
        "{error:?}"
    );
    expect_test::expect![[r#"
        "`var` is about the group `Other` and names the cell `Core::k`, which is not inside `Other`"
    "#]]
    .assert_debug_eq(&error.to_string());
}

/// A group two fields hold has two positions; the configuration is refused for it, whatever
/// sentence is about the group, with the refusal of the configuration itself.
#[test]
fn a_rule_about_a_group_held_twice_is_refused_as_the_configuration_is() {
    let error = refusal(&definition(
        "small",
        &[
            Cell::Group("left", core_cells()),
            Cell::Group("right", core_cells()),
        ],
        "Core",
        Vec::new(),
    ));
    expect_test::expect![[r#"
        "cell declaration `Core` is the content of more than one cell field (`left`, `right`), so its K cell sort is ambiguous; declare one struct per nested cell"
    "#]]
    .assert_debug_eq(&error.to_string());
}

/// A cell beside a group may not take the K name of one of the group's cells: K names each cell
/// of a configuration once. The refusal names both cells by their owners.
#[test]
fn a_cell_with_the_name_of_a_group_cell_is_refused_naming_both_owners() {
    let error = refusal(&definition(
        "small",
        &[
            Cell::Group("core", core_cells()),
            Cell::Variable("env", BuiltinSort::Map),
        ],
        "Core",
        Vec::new(),
    ));
    expect_test::expect![[r#"
        "cells `Core::env` and `Small::env` both have the K cell name `env`; a configuration names each of its cells once"
    "#]]
    .assert_debug_eq(&error.to_string());
}

/// A cell named by its owner and field.
fn named(owner: &StableItemId, field: &str) -> DescriptorCellIdentity {
    DescriptorCellIdentity {
        owner: owner.clone(),
        field: field.into(),
    }
}

/// The `Core` group's identity.
fn core_id() -> StableItemId {
    id("Core", ItemKind::Cell)
}

/// The group `Other { x }`, beside `Core` in some configurations.
fn other() -> DescriptorInputs {
    group("Other", &[("x", CellWrapper::Cell, BuiltinSort::Int)])
}

/// The head rule `step` (`k: [x: Int, ..], <extra>: e => k: [e, ..], <extra>: e`) lowered against
/// `configuration`, about `subject` (the whole configuration when absent), whose computation cell
/// is `computation` and whose one extra cell is `extra`.
fn head_rule(
    configuration: &StableItemId,
    subject: Option<&str>,
    computation: DescriptorCellIdentity,
    extra: DescriptorCellIdentity,
) -> DescriptorInputs {
    let variable = |reference, path, ordinal, name: &str| DescriptorTerm::Variable {
        key: key(reference, ordinal),
        path_key: key(path, ordinal),
        name: name.into(),
    };
    let left = |ordinal, name| {
        variable(
            ProvenanceRole::RuleLeftReference,
            ProvenanceRole::RuleLeftPath,
            ordinal,
            name,
        )
    };
    let right = |ordinal, name| {
        variable(
            ProvenanceRole::RuleRightReference,
            ProvenanceRole::RuleRightPath,
            ordinal,
            name,
        )
    };
    let rule = DescriptorHeadRule {
        sentence_kind: SentenceKind::Transition,
        label: None,
        priority: None,
        nondet: None,
        pattern_key: key(ProvenanceRole::RulePattern, 0),
        result_key: key(ProvenanceRole::RuleResult, 0),
        head_sort: None,
        configuration: configuration.clone(),
        configuration_key: Some(key(ProvenanceRole::RuleType, 0)),
        subject: subject.map(|name| DescriptorSubject::Group {
            declaration: id(name, ItemKind::Cell),
        }),
        result_type_key: key(ProvenanceRole::RuleResultType, 0),
        computation_cell: Some(DescriptorComputationCell {
            cell: computation,
            key: Some(key(ProvenanceRole::RuleLeftCellsField, 1)),
            result_key: Some(key(ProvenanceRole::RuleRightCellsField, 1)),
        }),
        // `x: Int` keeps the rule apart from `var`, whose head is an `Id`.
        bindings: vec![
            krs_ir::DescriptorHeadRuleBinding {
                name: "x".into(),
                refinement: Some(fixture::sort_ref(
                    ProvenanceRole::RuleBindingType,
                    0,
                    krs_ir::DescriptorSortRef::Builtin(BuiltinSort::Int),
                )),
            },
            krs_ir::DescriptorHeadRuleBinding {
                name: "e".into(),
                refinement: None,
            },
        ],
        head: Some(ProtocolHeadRuleHead {
            items: vec![left(0, "x")],
            exact: false,
            tail_key: None,
            result: Some(ProtocolHeadRuleResult::Replace(right(0, "e"))),
        }),
        requires: None,
        extras: vec![ProtocolHeadRuleExtra::RewriteCell {
            cell: DescriptorCellReference {
                key: key(ProvenanceRole::RuleLeftCellsField, 0),
                cell: extra,
            },
            result_key: Some(key(ProvenanceRole::RuleRightCellsField, 0)),
            before: left(1, "e"),
            after: Some(right(1, "e")),
        }],
        existentials: Vec::new(),
        ensures: None,
        fresh: Vec::new(),
        evaluation: None,
        claim: None,
    };
    DescriptorInputs::new(
        id("step", ItemKind::Rule),
        std::collections::BTreeMap::default(),
        provenance(key(ProvenanceRole::RuleDeclaration, 0), head_rule_keys()),
        DescriptorPayload::HeadRule(Box::new(rule)),
    )
}

/// The keys of [`head_rule`]'s nodes: its header, its two cells on each side, and its terms.
fn head_rule_keys() -> Vec<ProvenanceKey> {
    let mut keys = vec![
        key(ProvenanceRole::RuleBindingType, 0),
        key(ProvenanceRole::RulePattern, 0),
        key(ProvenanceRole::RuleResult, 0),
        key(ProvenanceRole::RuleType, 0),
        key(ProvenanceRole::RuleResultType, 0),
        key(ProvenanceRole::RuleLeftCellsField, 0),
        key(ProvenanceRole::RuleRightCellsField, 0),
        key(ProvenanceRole::RuleLeftCellsField, 1),
        key(ProvenanceRole::RuleRightCellsField, 1),
    ];
    for ordinal in 0..2 {
        keys.extend([
            key(ProvenanceRole::RuleLeftReference, ordinal),
            key(ProvenanceRole::RuleLeftPath, ordinal),
            key(ProvenanceRole::RuleRightReference, ordinal),
            key(ProvenanceRole::RuleRightPath, ordinal),
        ]);
    }
    keys
}

/// The context alias `operand` (`k: [HERE, ..]`) lowered against `configuration`, about the
/// group `subject`, whose computation cell is `computation`.
fn context_alias(
    configuration: &StableItemId,
    subject: &str,
    computation: &StableItemId,
) -> DescriptorInputs {
    let alias = DescriptorContextAlias {
        declaration_key: key(ProvenanceRole::ContextAliasDeclaration, 0),
        name_key: key(ProvenanceRole::ContextAliasName, 0),
        name: "operand".into(),
        here_key: key(ProvenanceRole::ContextAliasHere, 0),
        here: "site".into(),
        pattern_key: key(ProvenanceRole::RulePattern, 0),
        configuration: DescriptorConfigurationReference {
            key: key(ProvenanceRole::RuleType, 0),
            configuration: configuration.clone(),
            subject: Some(DescriptorSubject::Group {
                declaration: id(subject, ItemKind::Cell),
            }),
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
                computation,
                krs_ir::RuleSide::Left,
                0,
                "k",
                CellWrapper::KCell,
                ProtocolRuleStateTerm::KSequence(ProtocolRuleKSequence {
                    payload_key: key(ProvenanceRole::RuleLeftKSequencePayload, 0),
                    dot_k_key: None,
                    notation: DescriptorKSequenceNotation::Comma,
                    items: vec![ProtocolRuleKSequenceItem {
                        key: key(ProvenanceRole::RuleLeftKSequenceItem, 0),
                        value: variable(ProvenanceRole::RuleLeftReference, 0, "site"),
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
        result: None,
    };
    let keys = alias.expected_provenance_keys().unwrap();
    DescriptorInputs::new(
        id("operand", ItemKind::ContextAlias),
        std::collections::BTreeMap::default(),
        provenance(key(ProvenanceRole::ContextAliasDeclaration, 0), keys),
        DescriptorPayload::ContextAlias(Box::new(alias)),
    )
}

/// `Small { core: Core, mem }`.
fn small_cells() -> Vec<Cell> {
    vec![
        Cell::Group("core", core_cells()),
        Cell::Variable("mem", BuiltinSort::Map),
    ]
}

/// `Small { core: Core, other: Other, mem }`.
fn small_with_other_cells() -> Vec<Cell> {
    vec![
        Cell::Group("core", core_cells()),
        Cell::Group(
            "other",
            vec![("Other", "x", CellWrapper::Cell, BuiltinSort::Int)],
        ),
        Cell::Variable("mem", BuiltinSort::Map),
    ]
}

/// A head rule about `Core` names `Core`'s computation cell and another of its cells: both are
/// in its scope, so the definition lowers.
#[test]
fn a_head_rule_about_a_group_naming_the_groups_cells_lowers() {
    let small = configuration_id("small");
    let bundle = definition(
        "small",
        &small_cells(),
        "Core",
        vec![head_rule(
            &small,
            Some("Core"),
            named(&core_id(), "k"),
            named(&core_id(), "env"),
        )],
    );
    let lowered = lower_descriptor_bundle(&bundle.build().unwrap());
    assert!(lowered.is_ok(), "{:?}", lowered.err());
}

/// A head rule about `Core` whose extra cell is `Other::x`, a cell of another group, names a
/// cell outside its subject, and so does one about `Other` whose computation cell is `Core::k`.
/// (A cell the configuration declares itself, such as `Small::mem`, is never named by a
/// sentence about a group: the IR refuses such a descriptor before lowering.)
#[test]
fn a_head_rule_about_a_group_naming_a_cell_outside_it_is_refused() {
    let small = configuration_id("small");
    let extra = refusal(&definition(
        "small",
        &small_with_other_cells(),
        "Core",
        vec![
            other(),
            head_rule(
                &small,
                Some("Core"),
                named(&core_id(), "k"),
                named(&id("Other", ItemKind::Cell), "x"),
            ),
        ],
    ));
    let computation = refusal(&definition(
        "small",
        &small_with_other_cells(),
        "Core",
        vec![
            other(),
            head_rule(
                &small,
                Some("Other"),
                named(&core_id(), "k"),
                named(&id("Other", ItemKind::Cell), "x"),
            ),
        ],
    ));
    for error in [&extra, &computation] {
        assert!(
            matches!(error, DescriptorLoweringError::CellOutsideSubject { .. }),
            "{error:?}"
        );
    }
    expect_test::expect![[r#"
        [
            "`step` is about the group `Core` and names the cell `Other::x`, which is not inside `Core`",
            "`step` is about the group `Other` and names the cell `Core::k`, which is not inside `Other`",
        ]
    "#]]
    .assert_debug_eq(&[extra.to_string(), computation.to_string()]);
}

/// A head rule naming a field its owner does not declare is a descriptor that disagrees with its
/// declarations, which collection resolves names against, not a cell outside its subject.
#[test]
fn a_head_rule_naming_an_undeclared_field_is_a_disagreement() {
    let small = configuration_id("small");
    let error = refusal(&definition(
        "small",
        &small_cells(),
        "Core",
        vec![head_rule(
            &small,
            None,
            named(&core_id(), "k"),
            named(&small, "nope"),
        )],
    ));
    assert!(
        matches!(
            error,
            DescriptorLoweringError::ParserReferenceDisagreement { .. }
        ),
        "{error:?}"
    );
}

/// A context alias about `Core` matches in `Core`'s computation cell; one about `Other` whose
/// pattern names `Core::k` names a cell outside its subject.
#[test]
fn a_context_alias_about_a_group_is_judged_against_its_scope() {
    let small = configuration_id("small");
    let inside = definition(
        "small",
        &small_cells(),
        "Core",
        vec![context_alias(&small, "Core", &core_id())],
    );
    let lowered = lower_descriptor_bundle(&inside.build().unwrap());
    assert!(lowered.is_ok(), "{:?}", lowered.err());
    let error = refusal(&definition(
        "small",
        &small_with_other_cells(),
        "Core",
        vec![other(), context_alias(&small, "Other", &core_id())],
    ));
    expect_test::expect![[r#"
        "`operand` is about the group `Other` and names the cell `Core::k`, which is not inside `Other`"
    "#]]
    .assert_debug_eq(&error.to_string());
}

/// A group in a Set or a List collection has no position a local step of one instance applies at
/// (a Set merges a stepped instance with an equal one; a List's instance at any position is not
/// matched yet). Collection refuses a sentence about it, so semantic analysis states the
/// disagreement, naming the collection.
#[test]
fn a_rule_about_a_group_in_a_set_or_a_list_collection_is_refused() {
    let details = ["*Set", "*"].map(|multiplicity| {
        let error = refusal(&definition(
            "small",
            &[
                Cell::Group("core", core_cells()),
                Cell::Held(
                    "held",
                    multiplicity,
                    vec![("Other", "x", CellWrapper::Cell, BuiltinSort::Int)],
                ),
            ],
            "Other",
            vec![other()],
        ));
        match error {
            DescriptorLoweringError::ParserReferenceDisagreement { detail, .. } => detail,
            other => panic!("{other:?}"),
        }
    });
    expect_test::expect![[r#"
        [
            "the sentence is about the group `Other`, which has no position a rule about it applies at in the configuration `Small`: it sits in an instance of the Set collection cell `held`, whose instances a local step of one does not keep apart",
            "the sentence is about the group `Other`, which has no position a rule about it applies at in the configuration `Small`: it sits in an instance of the List collection cell `held`, where a step of the instance at any position is not supported yet",
        ]
    "#]]
    .assert_debug_eq(&details);
}

/// A rule about one instance of a Map collection writes the instance's key, its first child, only
/// as its subject matched it. Here `Core`'s first child is its computation `k`, which the rule
/// `var` rewrites: the compiler states the key check over the descriptor's terms, so a key the
/// collector would have refused is refused here too.
#[test]
fn a_rule_about_a_map_instance_that_writes_its_key_is_refused() {
    let error = refusal(&definition(
        "small",
        &[Cell::Held("cores", "*Map", core_cells())],
        "Core",
        Vec::new(),
    ));
    expect_test::expect![[r#"
        (
            "krs::analysis::map-collection-key",
            "the rule writes `k`, the key of the instance of the Map collection `cores` it is about: a rule for `Core` is a local step of one instance, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it",
        )
    "#]].assert_debug_eq(&(error.to_diagnostics()[0].code.to_string(), error.to_string()));
}

/// A main cell inside a Set collection's instance is refused, naming the collection: a sentence
/// that names no cell is a local step of that instance, which a Set merges with an equal one.
#[test]
fn a_main_cell_inside_a_set_instance_is_refused() {
    let error = refusal(&definition(
        "small",
        &[
            Cell::Held(
                "objs",
                "*Set",
                vec![
                    ("Obj", "code", CellWrapper::KCell, BuiltinSort::KSequence),
                    ("Obj", "n", CellWrapper::Cell, BuiltinSort::Int),
                ],
            ),
            Cell::Group("core", core_cells()),
        ],
        "Core",
        vec![group(
            "Obj",
            &[
                ("code", CellWrapper::KCell, BuiltinSort::KSequence),
                ("n", CellWrapper::Cell, BuiltinSort::Int),
            ],
        )],
    ));
    expect_test::expect![[r#"
        (
            "krs::analysis::main-cell",
            "the computation cell `code` sits in an instance of the Set collection cell `objs` of configuration `Small`: a sentence that names no cell (a term rule, a context, a strict production's heating) runs at the computation cell, so it is a local step of the instance that holds it, and a Set identifies an instance by its whole content, so a step that makes that instance equal to another merges the two, removing an instance the step never touched; hold the instances in a Map collection keyed by an id",
        )
    "#]].assert_debug_eq(&(error.to_diagnostics()[0].code.to_string(), error.to_string()));
}

/// A main cell that is a Map instance's key is refused, naming the key: a sentence that names no
/// cell would rewrite the instance's identity.
#[test]
fn a_main_cell_that_is_a_map_key_is_refused() {
    let error = refusal(&definition(
        "small",
        &[
            Cell::Held(
                "cpus",
                "*Map",
                vec![
                    ("Cpu", "code", CellWrapper::KCell, BuiltinSort::KSequence),
                    ("Cpu", "n", CellWrapper::Cell, BuiltinSort::Int),
                ],
            ),
            Cell::Group("core", core_cells()),
        ],
        "Core",
        vec![group(
            "Cpu",
            &[
                ("code", CellWrapper::KCell, BuiltinSort::KSequence),
                ("n", CellWrapper::Cell, BuiltinSort::Int),
            ],
        )],
    ));
    expect_test::expect![[r#"
        (
            "krs::analysis::main-cell",
            "the computation cell `code` is the key `code` of the instances of the Map collection cell `cpus` of configuration `Small`, or lies inside it: a sentence that names no cell (a term rule, a context, a strict production's heating) runs at the computation cell, so it would rewrite an instance's key, and the whole key is the instance's identity, which no step of the instance changes; key the instances by another child, declared first",
        )
    "#]]
        .assert_debug_eq(&(error.to_diagnostics()[0].code.to_string(), error.to_string()));
}

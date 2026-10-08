//! Stable grammar and structured-rule descriptors lower without reparsing Rust spellings.

use krs_ir::testing::{DescriptorBundleInputs, DescriptorInputs};

use std::collections::{BTreeMap, BTreeSet};

use krs_compiler::testing::assert_lowering_contract;
use krs_compiler::{
    LoweringError, MappedIdentity, SourceMapNodeKind, lower_descriptor_bundle,
    lower_semantic_theory,
};
use krs_ir::testing;
use krs_ir::testing::assert_canonical_contract;
use krs_ir::{
    BuiltinOperation, BuiltinSort, CellWrapper, ConstructorDescriptor, ConstructorFieldDescriptor,
    DescriptorApplicationHeadClass, DescriptorApplicationRef, DescriptorApplicationReference,
    DescriptorGroupReference, DescriptorLiteral, DescriptorNodeOrigin, DescriptorPayload,
    DescriptorPrecedenceChain, DescriptorProduction, DescriptorProductionAttribute,
    DescriptorProductionItem, DescriptorProductionOwner, DescriptorProvenance,
    DescriptorRuleCondition, DescriptorRuleLabel, DescriptorSortRef, DescriptorSortReference,
    DescriptorTerm, DescriptorTermArgument, GeneratedProductionKind, GrammarDescriptor,
    GroupAssociativity, ItemKind, PackageId, ProductionFieldId, ProductionGroupId, ProvenanceKey,
    ProvenanceRole, SentenceKind, SortDescriptor, StableItemId, StructuredRuleDescriptor,
    generated_production_id,
};
use krs_ir_levels::{MapOperands, SemanticSortRef, SemanticTerm, SemanticTermKind};

fn package() -> PackageId {
    testing::package("KRS-GRAMMAR", "grammar")
}

fn id(name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), "expr", name, kind)
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
                let index = u32::try_from(index).unwrap();
                DescriptorNodeOrigin::new(
                    key,
                    testing::authored_in(
                        package(),
                        "src/expr.rs",
                        testing::digest_with("2".repeat(64)),
                        index,
                        index + 1,
                    ),
                )
            })
            .collect(),
    )
    .unwrap()
}

fn declared_sort(
    role: ProvenanceRole,
    ordinal: u32,
    sort: StableItemId,
) -> DescriptorSortReference {
    DescriptorSortReference {
        key: key(role, ordinal),
        sort: DescriptorSortRef::Declared(sort),
    }
}

fn declaration(
    id: StableItemId,
    payload: DescriptorPayload,
    primary: ProvenanceRole,
) -> DescriptorInputs {
    let extra = matches!(payload, DescriptorPayload::Constructor(_))
        .then(|| key(ProvenanceRole::ConstructorDeclaration, 0));
    DescriptorInputs::new(
        id,
        BTreeMap::new(),
        provenance(key(primary, 0), extra),
        payload,
    )
}

fn machine_configuration(start: StableItemId) -> DescriptorInputs {
    let owner = id("Machine", ItemKind::Configuration);
    let k = krs_ir::DescriptorCellIdentity {
        owner: owner.clone(),
        field: "k".into(),
    };
    let configuration = krs_ir::DescriptorFixedConfiguration {
        root: krs_ir::DescriptorConfigurationRoot::GeneratedTop,
        declaration: krs_ir::DescriptorConfigurationDeclaration {
            key: key(ProvenanceRole::ConfigurationDeclaration, 0),
            fields: vec![krs_ir::DescriptorCellField {
                reference: krs_ir::DescriptorCellReference {
                    key: key(ProvenanceRole::ConfigurationField, 0),
                    cell: k.clone(),
                },
                rust_field: "k".into(),
                emitted_name: None,
                color: None,
                multiplicity: None,
                cell_type: None,
                stream: None,
                exit: None,
                content: krs_ir::ProtocolCellContent::Leaf {
                    wrapper_key: key(ProvenanceRole::ConfigurationCellWrapper, 0),
                    wrapper: CellWrapper::KCell,
                    sort: DescriptorSortReference {
                        key: key(ProvenanceRole::ConfigurationCellContent, 0),
                        sort: DescriptorSortRef::Builtin(BuiltinSort::KSequence),
                    },
                    arguments: Vec::new(),
                },
            }],
        },
        initializer: krs_ir::DescriptorConfigurationInitializer {
            key: key(ProvenanceRole::InitializerDeclaration, 0),
            owner_key: key(ProvenanceRole::InitializerResultType, 0),
            owner: owner.clone(),
            variables: Vec::new(),
            body_key: key(ProvenanceRole::InitializerBody, 0),
            cells: vec![krs_ir::DescriptorInitializerCell {
                key: key(ProvenanceRole::InitializerCell, 0),
                field: krs_ir::DescriptorCellReference {
                    key: key(ProvenanceRole::InitializerField, 0),
                    cell: k,
                },
                content: krs_ir::ProtocolInitializerCellContent::Leaf {
                    constructor_key: key(ProvenanceRole::InitializerCellConstructor, 0),
                    wrapper: CellWrapper::KCell,
                    value: krs_ir::ProtocolInitializerStateTerm::KSequence(
                        krs_ir::ProtocolKSequence {
                            payload_key: Some(key(ProvenanceRole::KSequencePayload, 0)),
                            dot_k_key: None,
                            notation: krs_ir::DescriptorKSequenceNotation::Comma,
                            items: vec![krs_ir::ProtocolKSequenceItem {
                                key: key(ProvenanceRole::KSequenceItem, 0),
                                value: krs_ir::ProtocolInitializerTerm {
                                    key: key(ProvenanceRole::InitializerTerm, 0),
                                    term: DescriptorTerm::Application {
                                        head_class: DescriptorApplicationHeadClass::BareReference,
                                        reference: DescriptorApplicationReference {
                                            key: key(ProvenanceRole::InitializerTermPath, 0),
                                            application: DescriptorApplicationRef::Declared(start),
                                        },
                                        path_key: key(ProvenanceRole::InitializerTermPath, 0),
                                        arguments: vec![].try_into().unwrap(),
                                    },
                                },
                            }],
                        },
                    ),
                },
            }],
        },
    };
    let keys = configuration.expected_provenance_keys(&owner).unwrap();
    DescriptorInputs::new(
        owner,
        BTreeMap::new(),
        provenance(key(ProvenanceRole::ConfigurationDeclaration, 0), keys),
        DescriptorPayload::FixedConfiguration(Box::new(configuration)),
    )
}

#[expect(
    clippy::too_many_lines,
    reason = "Builds the complete grammar descriptor bundle in one place."
)]
fn bundle() -> (DescriptorBundleInputs, StableItemId) {
    let expr = id("Expr", ItemKind::Sort);
    let add = id("Add", ItemKind::Constructor);
    let unit = id("Unit", ItemKind::Constructor);
    let start = id("Start", ItemKind::Constructor);
    let add_grammar_id = id("Add", ItemKind::Grammar);
    let unit_grammar_id =
        StableItemId::new(package(), ["expr"], "Unit", ItemKind::Grammar, "production").unwrap();
    let start_grammar_id = StableItemId::new(
        package(),
        ["expr"],
        "Start",
        ItemKind::Grammar,
        "production",
    )
    .unwrap();
    let bracket_grammar_id = id("ExprBracket", ItemKind::Grammar);
    let additive = ProductionGroupId::new("additive").unwrap();
    let atom = ProductionGroupId::new("atom").unwrap();

    let mut descriptors = vec![
        declaration(
            expr.clone(),
            DescriptorPayload::Sort(SortDescriptor {
                parents: BTreeSet::new(),
            }),
            ProvenanceRole::SortDeclaration,
        ),
        declaration(
            add.clone(),
            DescriptorPayload::Constructor(ConstructorDescriptor {
                sort: DescriptorSortRef::Declared(expr.clone()),
                fields: vec![
                    ConstructorFieldDescriptor {
                        name: "lhs".into(),
                        sort: Some(DescriptorSortRef::Declared(expr.clone())),
                    },
                    ConstructorFieldDescriptor {
                        name: "rhs".into(),
                        sort: Some(DescriptorSortRef::Declared(expr.clone())),
                    },
                ],
            }),
            ProvenanceRole::ConstructorSort,
        ),
        declaration(
            unit.clone(),
            DescriptorPayload::Constructor(ConstructorDescriptor {
                sort: DescriptorSortRef::Declared(expr.clone()),
                fields: vec![],
            }),
            ProvenanceRole::ConstructorSort,
        ),
        declaration(
            start.clone(),
            DescriptorPayload::Constructor(ConstructorDescriptor {
                sort: DescriptorSortRef::Declared(expr.clone()),
                fields: vec![],
            }),
            ProvenanceRole::ConstructorSort,
        ),
    ];

    let add_primary = key(ProvenanceRole::ConstructorDeclaration, 0);
    descriptors.push(DescriptorInputs::new(
        add_grammar_id,
        BTreeMap::new(),
        provenance(
            add_primary.clone(),
            [
                key(ProvenanceRole::ConstructorSort, 0),
                key(ProvenanceRole::ConstructorSyntax, 0),
                key(ProvenanceRole::ConstructorSyntaxItem, 0),
                key(ProvenanceRole::ConstructorSyntaxItem, 1),
                key(ProvenanceRole::ConstructorSyntaxItem, 2),
                key(ProvenanceRole::ConstructorSyntaxFieldReference, 0),
                key(ProvenanceRole::ConstructorSyntaxFieldReference, 1),
                key(ProvenanceRole::ConstructorFieldDeclaration, 0),
                key(ProvenanceRole::ConstructorFieldDeclaration, 1),
                key(ProvenanceRole::ConstructorFieldSort, 0),
                key(ProvenanceRole::ConstructorFieldSort, 1),
                key(ProvenanceRole::ConstructorGroup, 0),
            ],
        ),
        DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Production(
            DescriptorProduction {
                key: add_primary.clone(),
                template_key: Some(key(ProvenanceRole::ConstructorSyntax, 0)),
                owner: DescriptorProductionOwner::Constructor {
                    constructor: DescriptorApplicationReference {
                        key: add_primary,
                        application: DescriptorApplicationRef::Declared(add.clone()),
                    },
                },
                result_sort: declared_sort(ProvenanceRole::ConstructorSort, 0, expr.clone()),
                items: vec![
                    DescriptorProductionItem::NonTerminal {
                        key: key(ProvenanceRole::ConstructorSyntaxItem, 0),
                        field_key: key(ProvenanceRole::ConstructorSyntaxFieldReference, 0),
                        declaration_key: Some(key(ProvenanceRole::ConstructorFieldDeclaration, 0)),
                        field: ProductionFieldId::new("lhs").unwrap(),
                        sort: Box::new(declared_sort(
                            ProvenanceRole::ConstructorFieldSort,
                            0,
                            expr.clone(),
                        )),
                    },
                    DescriptorProductionItem::Terminal {
                        key: key(ProvenanceRole::ConstructorSyntaxItem, 1),
                        text: "+".into(),
                    },
                    DescriptorProductionItem::NonTerminal {
                        key: key(ProvenanceRole::ConstructorSyntaxItem, 2),
                        field_key: key(ProvenanceRole::ConstructorSyntaxFieldReference, 1),
                        declaration_key: Some(key(ProvenanceRole::ConstructorFieldDeclaration, 1)),
                        field: ProductionFieldId::new("rhs").unwrap(),
                        sort: Box::new(declared_sort(
                            ProvenanceRole::ConstructorFieldSort,
                            1,
                            expr.clone(),
                        )),
                    },
                ],
                attributes: vec![DescriptorProductionAttribute::Group {
                    reference: DescriptorGroupReference {
                        key: key(ProvenanceRole::ConstructorGroup, 0),
                        group: additive.clone(),
                    },
                }],
            },
        ))),
    ));

    let unit_primary = key(ProvenanceRole::ConstructorDeclaration, 0);
    descriptors.push(DescriptorInputs::new(
        unit_grammar_id,
        BTreeMap::new(),
        provenance(
            unit_primary.clone(),
            [
                key(ProvenanceRole::ConstructorSort, 0),
                key(ProvenanceRole::ConstructorGroup, 0),
            ],
        ),
        DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Production(
            DescriptorProduction {
                key: unit_primary.clone(),
                template_key: None,
                owner: DescriptorProductionOwner::Constructor {
                    constructor: DescriptorApplicationReference {
                        key: unit_primary.clone(),
                        application: DescriptorApplicationRef::Declared(unit.clone()),
                    },
                },
                result_sort: declared_sort(ProvenanceRole::ConstructorSort, 0, expr.clone()),
                items: vec![DescriptorProductionItem::Terminal {
                    key: unit_primary,
                    text: "unit".into(),
                }],
                attributes: vec![DescriptorProductionAttribute::Group {
                    reference: DescriptorGroupReference {
                        key: key(ProvenanceRole::ConstructorGroup, 0),
                        group: atom.clone(),
                    },
                }],
            },
        ))),
    ));

    let start_primary = key(ProvenanceRole::ConstructorDeclaration, 0);
    descriptors.push(DescriptorInputs::new(
        start_grammar_id,
        BTreeMap::new(),
        provenance(
            start_primary.clone(),
            [key(ProvenanceRole::ConstructorSort, 0)],
        ),
        DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Production(
            DescriptorProduction {
                key: start_primary.clone(),
                template_key: None,
                owner: DescriptorProductionOwner::Constructor {
                    constructor: DescriptorApplicationReference {
                        key: start_primary.clone(),
                        application: DescriptorApplicationRef::Declared(start.clone()),
                    },
                },
                result_sort: declared_sort(ProvenanceRole::ConstructorSort, 0, expr.clone()),
                items: vec![DescriptorProductionItem::Terminal {
                    key: start_primary,
                    text: "start".into(),
                }],
                attributes: Vec::new(),
            },
        ))),
    ));

    let bracket_primary = key(ProvenanceRole::BracketDeclaration, 0);
    descriptors.push(DescriptorInputs::new(
        bracket_grammar_id.clone(),
        BTreeMap::new(),
        provenance(
            bracket_primary.clone(),
            [
                key(ProvenanceRole::SortDeclaration, 0),
                key(ProvenanceRole::BracketSyntaxItem, 0),
                key(ProvenanceRole::BracketSyntaxItem, 1),
                key(ProvenanceRole::BracketSyntaxItem, 2),
                key(ProvenanceRole::BracketValueReference, 0),
            ],
        ),
        DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Production(
            DescriptorProduction {
                key: bracket_primary.clone(),
                template_key: None,
                owner: DescriptorProductionOwner::BracketSort {
                    sort: declared_sort(ProvenanceRole::SortDeclaration, 0, expr.clone()),
                },
                result_sort: declared_sort(ProvenanceRole::SortDeclaration, 0, expr.clone()),
                items: vec![
                    DescriptorProductionItem::Terminal {
                        key: key(ProvenanceRole::BracketSyntaxItem, 0),
                        text: "(".into(),
                    },
                    DescriptorProductionItem::NonTerminal {
                        key: key(ProvenanceRole::BracketSyntaxItem, 1),
                        field_key: key(ProvenanceRole::BracketValueReference, 0),
                        declaration_key: None,
                        field: ProductionFieldId::new("value").unwrap(),
                        sort: Box::new(declared_sort(
                            ProvenanceRole::SortDeclaration,
                            0,
                            expr.clone(),
                        )),
                    },
                    DescriptorProductionItem::Terminal {
                        key: key(ProvenanceRole::BracketSyntaxItem, 2),
                        text: ")".into(),
                    },
                ],
                attributes: vec![DescriptorProductionAttribute::Bracket {
                    key: bracket_primary,
                }],
            },
        ))),
    ));

    let precedence_primary = key(ProvenanceRole::PrecedenceDeclaration, 0);
    descriptors.push(DescriptorInputs::new(
        id("Precedence", ItemKind::Grammar),
        BTreeMap::new(),
        provenance(
            precedence_primary.clone(),
            [
                key(ProvenanceRole::PrecedenceChain, 0),
                key(ProvenanceRole::PrecedenceGroupReference, 0),
                key(ProvenanceRole::PrecedenceGroupReference, 1),
            ],
        ),
        DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Precedence {
            key: precedence_primary,
            chains: vec![DescriptorPrecedenceChain {
                key: key(ProvenanceRole::PrecedenceChain, 0),
                groups: vec![
                    DescriptorGroupReference {
                        key: key(ProvenanceRole::PrecedenceGroupReference, 0),
                        group: atom.clone(),
                    },
                    DescriptorGroupReference {
                        key: key(ProvenanceRole::PrecedenceGroupReference, 1),
                        group: additive.clone(),
                    },
                ]
                .try_into()
                .unwrap(),
            }],
        })),
    ));
    let assoc_primary = key(ProvenanceRole::AssociativityDeclaration, 0);
    descriptors.push(DescriptorInputs::new(
        id("Associativity", ItemKind::Grammar),
        BTreeMap::new(),
        provenance(
            assoc_primary.clone(),
            [
                key(ProvenanceRole::AssociativitySentence, 0),
                key(ProvenanceRole::AssociativityGroupReference, 0),
            ],
        ),
        DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Associativity {
            key: assoc_primary,
            sentences: vec![krs_ir::DescriptorAssociativitySentence {
                key: key(ProvenanceRole::AssociativitySentence, 0),
                associativity: GroupAssociativity::Left,
                groups: vec![DescriptorGroupReference {
                    key: key(ProvenanceRole::AssociativityGroupReference, 0),
                    group: additive,
                }],
            }],
        })),
    ));

    let rule_primary = key(ProvenanceRole::RuleDeclaration, 0);
    descriptors.push(DescriptorInputs::new(
        id("add_wildcard", ItemKind::Rule),
        BTreeMap::new(),
        provenance(
            rule_primary.clone(),
            [
                key(ProvenanceRole::RulePattern, 0),
                key(ProvenanceRole::RuleResult, 0),
                key(ProvenanceRole::RuleType, 0),
                key(ProvenanceRole::RuleResultType, 0),
                key(ProvenanceRole::RuleLeftPath, 0),
                key(ProvenanceRole::RuleLeftPath, 1),
                key(ProvenanceRole::RuleLeftApplicationHead, 0),
                key(ProvenanceRole::RuleLeftRecordFieldName, 0),
                key(ProvenanceRole::RuleLeftRecordFieldName, 1),
                key(ProvenanceRole::RuleLeftReference, 0),
                key(ProvenanceRole::RuleLeftWildcard, 0),
                key(ProvenanceRole::RuleRightPath, 0),
                key(ProvenanceRole::RuleRightReference, 0),
            ],
        ),
        DescriptorPayload::StructuredRule(Box::new(StructuredRuleDescriptor {
            sentence_kind: SentenceKind::Transition,
            label: None,
            requires: None,
            priority: None,
            nondet: None,
            anywhere: None,
            simplification: None,
            pattern_key: key(ProvenanceRole::RulePattern, 0),
            typed_bindings: vec![],
            result_key: key(ProvenanceRole::RuleResult, 0),
            subject_sort: declared_sort(ProvenanceRole::RuleType, 0, expr.clone()),
            result_sort: declared_sort(ProvenanceRole::RuleResultType, 0, expr.clone()),
            bindings: vec!["x".into()],
            subject: DescriptorTerm::Application {
                head_class: DescriptorApplicationHeadClass::Applied,
                reference: DescriptorApplicationReference {
                    key: key(ProvenanceRole::RuleLeftApplicationHead, 0),
                    application: DescriptorApplicationRef::Declared(add),
                },
                path_key: key(ProvenanceRole::RuleLeftPath, 0),
                arguments: vec![
                    DescriptorTermArgument::Named {
                        key: key(ProvenanceRole::RuleLeftRecordFieldName, 0),
                        field: ProductionFieldId::new("rhs").unwrap(),
                        value: Box::new(DescriptorTerm::Wildcard {
                            key: key(ProvenanceRole::RuleLeftWildcard, 0),
                        }),
                    },
                    DescriptorTermArgument::Named {
                        key: key(ProvenanceRole::RuleLeftRecordFieldName, 1),
                        field: ProductionFieldId::new("lhs").unwrap(),
                        value: Box::new(DescriptorTerm::Variable {
                            key: key(ProvenanceRole::RuleLeftReference, 0),
                            path_key: key(ProvenanceRole::RuleLeftPath, 1),
                            name: "x".into(),
                        }),
                    },
                ]
                .try_into()
                .unwrap(),
            },
            result: DescriptorTerm::Application {
                head_class: DescriptorApplicationHeadClass::BareReference,
                reference: DescriptorApplicationReference {
                    key: key(ProvenanceRole::RuleRightReference, 0),
                    application: DescriptorApplicationRef::Declared(unit),
                },
                path_key: key(ProvenanceRole::RuleRightPath, 0),
                arguments: vec![].try_into().unwrap(),
            },
            existentials: Vec::new(),
            ensures: None,
        })),
    ));

    descriptors.push(machine_configuration(start));
    (
        DescriptorBundleInputs::new(descriptors),
        generated_production_id(&bracket_grammar_id, GeneratedProductionKind::Bracket).unwrap(),
    )
}

/// Adds a descriptor with inherited declaration metadata, as [`bundle`] builds them.
fn push_descriptor(bundle: &mut DescriptorBundleInputs, descriptor: DescriptorInputs) {
    let mut descriptors = bundle.descriptors.clone();
    descriptors.push(descriptor);
    *bundle = DescriptorBundleInputs::new(descriptors);
}

fn add_builtin_expr_subsort(
    bundle: &mut DescriptorBundleInputs,
    builtin: BuiltinSort,
    builtin_name: &str,
) {
    let expr = id("Expr", ItemKind::Sort);
    let value = id("Value", ItemKind::Sort);
    push_descriptor(
        bundle,
        DescriptorInputs::new(
            value.clone(),
            BTreeMap::new(),
            provenance(
                key(ProvenanceRole::SortDeclaration, 0),
                [key(ProvenanceRole::SortParent, 0)],
            ),
            DescriptorPayload::Sort(SortDescriptor {
                parents: [expr].into(),
            }),
        ),
    );
    let primary = key(ProvenanceRole::SubsortDeclaration, 0);
    push_descriptor(
        bundle,
        DescriptorInputs::new(
            StableItemId::new(
                package(),
                ["expr"],
                format!("__subsort_{builtin_name}_Value"),
                ItemKind::Grammar,
                "subsort",
            )
            .unwrap(),
            BTreeMap::new(),
            provenance(
                primary.clone(),
                [
                    key(ProvenanceRole::SubsortSubSort, 0),
                    key(ProvenanceRole::SubsortSuperSort, 0),
                ],
            ),
            DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Subsort {
                key: primary,
                subsort: DescriptorSortReference {
                    key: key(ProvenanceRole::SubsortSubSort, 0),
                    sort: DescriptorSortRef::Builtin(builtin),
                },
                supersort: declared_sort(ProvenanceRole::SubsortSuperSort, 0, value),
            })),
        ),
    );
}

fn replace_rule_result_with_builtin(
    bundle: &mut DescriptorBundleInputs,
    operation: BuiltinOperation,
    second_argument: Option<DescriptorLiteral>,
) {
    let mut descriptors = bundle.descriptors.clone();
    let descriptor = descriptors
        .iter_mut()
        .find(|descriptor| matches!(&descriptor.payload, DescriptorPayload::StructuredRule(_)))
        .unwrap();
    let mut provenance_keys = vec![
        key(ProvenanceRole::RulePattern, 0),
        key(ProvenanceRole::RuleResult, 0),
        key(ProvenanceRole::RuleType, 0),
        key(ProvenanceRole::RuleResultType, 0),
        key(ProvenanceRole::RuleLeftPath, 0),
        key(ProvenanceRole::RuleLeftPath, 1),
        key(ProvenanceRole::RuleLeftApplicationHead, 0),
        key(ProvenanceRole::RuleLeftRecordFieldName, 0),
        key(ProvenanceRole::RuleLeftRecordFieldName, 1),
        key(ProvenanceRole::RuleLeftReference, 0),
        key(ProvenanceRole::RuleLeftWildcard, 0),
        key(ProvenanceRole::RuleRightPath, 0),
        key(ProvenanceRole::RuleRightPath, 1),
        key(ProvenanceRole::RuleRightApplicationHead, 0),
        key(ProvenanceRole::RuleRightReference, 0),
    ];
    if second_argument.is_some() {
        provenance_keys.push(key(ProvenanceRole::RuleRightLiteral, 0));
    }
    descriptor.provenance = provenance(key(ProvenanceRole::RuleDeclaration, 0), provenance_keys);
    let DescriptorPayload::StructuredRule(rule) = &mut descriptor.payload else {
        unreachable!();
    };
    let mut arguments = vec![DescriptorTermArgument::Positional {
        value: Box::new(DescriptorTerm::Variable {
            key: key(ProvenanceRole::RuleRightReference, 0),
            path_key: key(ProvenanceRole::RuleRightPath, 1),
            name: "x".into(),
        }),
    }];
    if let Some(literal) = second_argument {
        arguments.push(DescriptorTermArgument::Positional {
            value: Box::new(DescriptorTerm::Literal {
                key: key(ProvenanceRole::RuleRightLiteral, 0),
                literal,
            }),
        });
    }
    rule.result = DescriptorTerm::Application {
        head_class: DescriptorApplicationHeadClass::Applied,
        reference: DescriptorApplicationReference {
            key: key(ProvenanceRole::RuleRightApplicationHead, 0),
            application: DescriptorApplicationRef::Builtin(operation),
        },
        path_key: key(ProvenanceRole::RuleRightPath, 0),
        arguments: arguments.try_into().unwrap(),
    };
    bundle.descriptors = descriptors;
}

fn add_bool_common_descendant(bundle: &mut DescriptorBundleInputs, name: &str) -> StableItemId {
    let expr = id("Expr", ItemKind::Sort);
    let descendant = id(name, ItemKind::Sort);
    push_descriptor(
        bundle,
        DescriptorInputs::new(
            descendant.clone(),
            BTreeMap::new(),
            provenance(
                key(ProvenanceRole::SortDeclaration, 0),
                [key(ProvenanceRole::SortParent, 0)],
            ),
            DescriptorPayload::Sort(SortDescriptor {
                parents: [expr].into(),
            }),
        ),
    );
    let primary = key(ProvenanceRole::SubsortDeclaration, 0);
    push_descriptor(
        bundle,
        DescriptorInputs::new(
            StableItemId::new(
                package(),
                ["expr"],
                format!("__subsort_{name}_Bool"),
                ItemKind::Grammar,
                "subsort",
            )
            .unwrap(),
            BTreeMap::new(),
            provenance(
                primary.clone(),
                [
                    key(ProvenanceRole::SubsortSubSort, 0),
                    key(ProvenanceRole::SubsortSuperSort, 0),
                ],
            ),
            DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Subsort {
                key: primary,
                subsort: declared_sort(ProvenanceRole::SubsortSubSort, 0, descendant.clone()),
                supersort: DescriptorSortReference {
                    key: key(ProvenanceRole::SubsortSuperSort, 0),
                    sort: DescriptorSortRef::Builtin(BuiltinSort::Bool),
                },
            })),
        ),
    );
    descendant
}

fn add_builtin_member(
    bundle: &mut DescriptorBundleInputs,
    builtin: BuiltinSort,
    builtin_name: &str,
    parent: StableItemId,
) {
    let primary = key(ProvenanceRole::SubsortDeclaration, 0);
    push_descriptor(
        bundle,
        DescriptorInputs::new(
            StableItemId::new(
                package(),
                ["expr"],
                format!("__subsort_{builtin_name}_{}", parent.item_name()),
                ItemKind::Grammar,
                "subsort",
            )
            .unwrap(),
            BTreeMap::new(),
            provenance(
                primary.clone(),
                [
                    key(ProvenanceRole::SubsortSubSort, 0),
                    key(ProvenanceRole::SubsortSuperSort, 0),
                ],
            ),
            DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Subsort {
                key: primary,
                subsort: DescriptorSortReference {
                    key: key(ProvenanceRole::SubsortSubSort, 0),
                    sort: DescriptorSortRef::Builtin(builtin),
                },
                supersort: declared_sort(ProvenanceRole::SubsortSuperSort, 0, parent),
            })),
        ),
    );
}

fn add_bool_not_binding_condition(bundle: &mut DescriptorBundleInputs) {
    let mut descriptors = bundle.descriptors.clone();
    let descriptor = descriptors
        .iter_mut()
        .find(|descriptor| matches!(&descriptor.payload, DescriptorPayload::StructuredRule(_)))
        .unwrap();
    let condition_keys = [
        key(ProvenanceRole::RuleRequires, 0),
        key(ProvenanceRole::RuleRequiresPath, 0),
        key(ProvenanceRole::RuleRequiresPath, 1),
        key(ProvenanceRole::RuleRequiresApplicationHead, 0),
        key(ProvenanceRole::RuleRequiresReference, 0),
    ];
    let primary = descriptor.provenance.primary_key().clone();
    let mut origins = descriptor.provenance.origins().to_vec();
    origins.extend(
        condition_keys
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, key)| {
                let start = 200 + u32::try_from(index).unwrap();
                DescriptorNodeOrigin::new(
                    key,
                    testing::authored_in(
                        package(),
                        "src/expr.rs",
                        testing::digest_with("2".repeat(64)),
                        start,
                        start + 1,
                    ),
                )
            }),
    );
    descriptor.provenance = DescriptorProvenance::new(primary, origins).unwrap();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptor.payload else {
        unreachable!()
    };
    rule.requires = Some(DescriptorRuleCondition {
        key: key(ProvenanceRole::RuleRequires, 0),
        term: DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: key(ProvenanceRole::RuleRequiresApplicationHead, 0),
                application: DescriptorApplicationRef::Builtin(BuiltinOperation::BoolNot),
            },
            path_key: key(ProvenanceRole::RuleRequiresPath, 0),
            arguments: vec![DescriptorTermArgument::Positional {
                value: Box::new(DescriptorTerm::Variable {
                    key: key(ProvenanceRole::RuleRequiresReference, 0),
                    path_key: key(ProvenanceRole::RuleRequiresPath, 1),
                    name: "x".into(),
                }),
            }]
            .try_into()
            .unwrap(),
        },
    });
    bundle.descriptors = descriptors;
}

fn variable_sorts(term: &SemanticTerm, output: &mut Vec<SemanticSortRef>) {
    match term.kind() {
        SemanticTermKind::Variable { variable } if variable.as_str() == "x" => {
            output.push(term.sort().clone());
        }
        SemanticTermKind::Application { arguments, .. } => {
            for argument in arguments {
                variable_sorts(argument, output);
            }
        }
        SemanticTermKind::Map(operands) => {
            for operand in operands.operands() {
                variable_sorts(operand, output);
            }
        }
        SemanticTermKind::List(operands) => {
            for operand in operands.operands() {
                variable_sorts(operand, output);
            }
        }
        SemanticTermKind::Set(operands) => {
            for operand in operands.operands() {
                variable_sorts(operand, output);
            }
        }
        SemanticTermKind::Cell { children, .. } => {
            for child in children {
                variable_sorts(child, output);
            }
        }
        SemanticTermKind::Rewrite { from, to } => {
            variable_sorts(from, output);
            variable_sorts(to, output);
        }
        SemanticTermKind::KSequence { items, .. } => {
            for item in items {
                variable_sorts(item, output);
            }
        }
        SemanticTermKind::Variable { .. } | SemanticTermKind::Token { .. } => {}
    }
}

fn replace_rule_result_with_nested_map_update(bundle: &mut DescriptorBundleInputs) {
    let mut descriptors = bundle.descriptors.clone();
    let descriptor = descriptors
        .iter_mut()
        .find(|descriptor| matches!(&descriptor.payload, DescriptorPayload::StructuredRule(_)))
        .unwrap();
    descriptor.provenance = provenance(
        key(ProvenanceRole::RuleDeclaration, 0),
        [
            key(ProvenanceRole::RulePattern, 0),
            key(ProvenanceRole::RuleResult, 0),
            key(ProvenanceRole::RuleType, 0),
            key(ProvenanceRole::RuleResultType, 0),
            key(ProvenanceRole::RuleLeftPath, 0),
            key(ProvenanceRole::RuleLeftPath, 1),
            key(ProvenanceRole::RuleLeftApplicationHead, 0),
            key(ProvenanceRole::RuleLeftRecordFieldName, 0),
            key(ProvenanceRole::RuleLeftRecordFieldName, 1),
            key(ProvenanceRole::RuleLeftReference, 0),
            key(ProvenanceRole::RuleLeftWildcard, 0),
            key(ProvenanceRole::RuleRightPath, 0),
            key(ProvenanceRole::RuleRightPath, 1),
            key(ProvenanceRole::RuleRightPath, 2),
            key(ProvenanceRole::RuleRightPath, 3),
            key(ProvenanceRole::RuleRightApplicationHead, 0),
            key(ProvenanceRole::RuleRightApplicationHead, 1),
            key(ProvenanceRole::RuleRightReference, 0),
            key(ProvenanceRole::RuleRightReference, 1),
            key(ProvenanceRole::RuleRightLiteral, 0),
            key(ProvenanceRole::RuleRightLiteral, 1),
        ],
    );
    let DescriptorPayload::StructuredRule(rule) = &mut descriptor.payload else {
        unreachable!()
    };
    let variable = |ordinal: u32, path: u32| DescriptorTerm::Variable {
        key: key(ProvenanceRole::RuleRightReference, ordinal),
        path_key: key(ProvenanceRole::RuleRightPath, path),
        name: "x".into(),
    };
    let literal = |ordinal: u32, value: &str| DescriptorTerm::Literal {
        key: key(ProvenanceRole::RuleRightLiteral, ordinal),
        literal: DescriptorLiteral::Int(value.into()),
    };
    let update = DescriptorTerm::Application {
        head_class: DescriptorApplicationHeadClass::Applied,
        reference: DescriptorApplicationReference {
            key: key(ProvenanceRole::RuleRightApplicationHead, 1),
            application: DescriptorApplicationRef::Map(krs_ir::TermMapOperation::Update),
        },
        path_key: key(ProvenanceRole::RuleRightPath, 1),
        arguments: vec![
            DescriptorTermArgument::Positional {
                value: Box::new(variable(0, 2)),
            },
            DescriptorTermArgument::Positional {
                value: Box::new(literal(0, "0")),
            },
            DescriptorTermArgument::Positional {
                value: Box::new(literal(1, "1")),
            },
        ]
        .try_into()
        .unwrap(),
    };
    rule.result = DescriptorTerm::Application {
        head_class: DescriptorApplicationHeadClass::Applied,
        reference: DescriptorApplicationReference {
            key: key(ProvenanceRole::RuleRightApplicationHead, 0),
            application: DescriptorApplicationRef::Declared(id("Add", ItemKind::Constructor)),
        },
        path_key: key(ProvenanceRole::RuleRightPath, 0),
        arguments: vec![
            DescriptorTermArgument::Positional {
                value: Box::new(update),
            },
            DescriptorTermArgument::Positional {
                value: Box::new(variable(1, 3)),
            },
        ]
        .try_into()
        .unwrap(),
    };
    bundle.descriptors = descriptors;
}

fn forge_non_map_update_base(bundle: &mut DescriptorBundleInputs) {
    let mut descriptors = bundle.descriptors.clone();
    let descriptor = descriptors
        .iter_mut()
        .find(|descriptor| matches!(&descriptor.payload, DescriptorPayload::StructuredRule(_)))
        .unwrap();
    descriptor.provenance = provenance(
        key(ProvenanceRole::RuleDeclaration, 0),
        [
            key(ProvenanceRole::RulePattern, 0),
            key(ProvenanceRole::RuleResult, 0),
            key(ProvenanceRole::RuleType, 0),
            key(ProvenanceRole::RuleResultType, 0),
            key(ProvenanceRole::RuleLeftPath, 0),
            key(ProvenanceRole::RuleLeftPath, 1),
            key(ProvenanceRole::RuleLeftApplicationHead, 0),
            key(ProvenanceRole::RuleLeftRecordFieldName, 0),
            key(ProvenanceRole::RuleLeftRecordFieldName, 1),
            key(ProvenanceRole::RuleLeftReference, 0),
            key(ProvenanceRole::RuleLeftWildcard, 0),
            key(ProvenanceRole::RuleRightPath, 0),
            key(ProvenanceRole::RuleRightPath, 1),
            key(ProvenanceRole::RuleRightPath, 2),
            key(ProvenanceRole::RuleRightApplicationHead, 0),
            key(ProvenanceRole::RuleRightApplicationHead, 1),
            key(ProvenanceRole::RuleRightReference, 0),
            key(ProvenanceRole::RuleRightLiteral, 0),
            key(ProvenanceRole::RuleRightLiteral, 1),
            key(ProvenanceRole::RuleRightLiteral, 2),
        ],
    );
    let DescriptorPayload::StructuredRule(rule) = &mut descriptor.payload else {
        unreachable!()
    };
    let DescriptorTerm::Application {
        arguments: outer, ..
    } = &mut rule.result
    else {
        unreachable!()
    };
    let krs_ir::Arguments::Positional(outer) = outer else {
        unreachable!()
    };
    let update = &mut outer[0];
    let DescriptorTerm::Application {
        arguments: update_arguments,
        ..
    } = update.as_mut()
    else {
        unreachable!()
    };
    let krs_ir::Arguments::Positional(update_arguments) = update_arguments else {
        unreachable!()
    };
    *update_arguments[0] = DescriptorTerm::Literal {
        key: key(ProvenanceRole::RuleRightLiteral, 0),
        literal: DescriptorLiteral::Int("2".into()),
    };
    for (argument, ordinal) in update_arguments[1..].iter_mut().zip(1_u32..) {
        let value = argument;
        let DescriptorTerm::Literal {
            key: literal_key, ..
        } = value.as_mut()
        else {
            unreachable!()
        };
        *literal_key = key(ProvenanceRole::RuleRightLiteral, ordinal);
    }
    let second = &mut outer[1];
    let DescriptorTerm::Variable {
        key: reference_key,
        path_key,
        ..
    } = second.as_mut()
    else {
        unreachable!()
    };
    *reference_key = key(ProvenanceRole::RuleRightReference, 0);
    *path_key = key(ProvenanceRole::RuleRightPath, 2);
    bundle.descriptors = descriptors;
}

#[test]
fn declared_sort_names_cannot_collide_with_builtin_k_names() {
    for builtin in BuiltinSort::ALL {
        let (mut descriptors, _) = bundle();
        let sort_id = id(builtin.k_name(), ItemKind::Sort);
        descriptors.descriptors.push(declaration(
            sort_id.clone(),
            DescriptorPayload::Sort(SortDescriptor {
                parents: BTreeSet::new(),
            }),
            ProvenanceRole::SortDeclaration,
        ));
        let error = lower_descriptor_bundle(&descriptors.build().unwrap())
            .unwrap_err()
            .to_string();
        assert!(
            error.contains(&format!("use `k::builtin::{builtin:?}` instead")),
            "{error}"
        );
    }

    let (mut descriptors, _) = bundle();
    let sort_id = id("Renamed", ItemKind::Sort);
    descriptors.descriptors.push(declaration(
        sort_id.clone(),
        DescriptorPayload::Sort(SortDescriptor {
            parents: BTreeSet::new(),
        }),
        ProvenanceRole::SortDeclaration,
    ));
    let input = descriptors.descriptors.last_mut().unwrap();
    let mut origins = input.provenance.origins().to_vec();
    origins.push(DescriptorNodeOrigin::new(
        key(ProvenanceRole::StableSymbol, 0),
        testing::authored(0, 3),
    ));
    input.provenance =
        DescriptorProvenance::new(input.provenance.primary_key().clone(), origins).unwrap();
    descriptors
        .declarations
        .push(krs_ir::DescriptorDeclaration::new(
            sort_id,
            krs_ir::RustVisibility::Public,
            Some(krs_ir::ExplicitSymbol::new("domain::String").unwrap()),
        ));
    let error = lower_descriptor_bundle(&descriptors.build().unwrap())
        .unwrap_err()
        .to_string();
    assert!(
        error.contains("use `k::builtin::String` instead"),
        "{error}"
    );
}

#[test]
fn constructor_without_grammar_descriptor_is_rejected() {
    let (mut bundle, _) = bundle();
    let escaped = id("Escaped", ItemKind::Constructor);
    bundle.descriptors.push(declaration(
        escaped.clone(),
        DescriptorPayload::Constructor(ConstructorDescriptor {
            sort: DescriptorSortRef::Declared(id("Expr", ItemKind::Sort)),
            fields: vec![ConstructorFieldDescriptor {
                name: "value".into(),
                sort: Some(DescriptorSortRef::Declared(id("Expr", ItemKind::Sort))),
            }],
        }),
        ProvenanceRole::ConstructorSort,
    ));

    let error = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap_err();
    let krs_compiler::DescriptorLoweringError::UnsupportedShape { node, detail } = error else {
        panic!("unexpected error: {error:?}")
    };
    assert_eq!(node, "constructor");
    assert_eq!(
        detail,
        format!("no grammar descriptor owns constructor {escaped}")
    );
}

#[test]
fn named_record_wildcard_bare_constructor_and_generated_bracket_lower() {
    let (bundle, bracket_id) = bundle();
    assert_canonical_contract(&bundle.build().unwrap());
    let semantic = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap();
    assert_canonical_contract(&semantic);
    assert!(
        semantic.modules()[0]
            .productions()
            .iter()
            .any(|production| production.id() == &bracket_id)
    );
    let rule = &semantic.modules()[0].rules()[0];
    assert_eq!(
        rule.variables().len(),
        2,
        "one binding plus one anonymous wildcard"
    );
    let (_, k) = assert_lowering_contract(&semantic);
    assert!(k.source().contains("syntax priority"));
    assert!(k.source().contains("syntax left"));
    // A bracket is parse-only and is emitted without a symbol
    // (bracket-production-constructor).
    assert!(k.source().contains("[bracket, format(%1%2%3)]"));
    assert!(
        !k.source()
            .lines()
            .any(|line| line.contains("bracket") && line.contains("symbol("))
    );
    assert!(
        !k.source()
            .contains("symbol(__krs_generated_semantic_production)")
    );
    assert!(k.source().contains("=> unit"));
}

#[test]
fn nested_ordinary_map_update_survives_every_ir_and_emission_layer() {
    let (mut bundle, _) = bundle();
    add_builtin_member(
        &mut bundle,
        BuiltinSort::Map,
        "Map",
        id("Expr", ItemKind::Sort),
    );
    replace_rule_result_with_nested_map_update(&mut bundle);

    assert_canonical_contract(&bundle.build().unwrap());
    let semantic = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap();
    assert_canonical_contract(&semantic);
    let rule = &semantic.modules()[0].rules()[0];
    assert_eq!(rule.variables()[0].sort(), &SemanticSortRef::map());
    let body = rule.body().unwrap();
    let SemanticTermKind::Application { arguments, .. } = body.to().kind() else {
        panic!("map update must remain nested under Add")
    };
    assert!(matches!(
        arguments[0].kind(),
        SemanticTermKind::Map(operands)
            if matches!(operands.as_ref(), MapOperands::Update { .. })
    ));

    let (_definition, emitted) = assert_lowering_contract(&semantic);
    assert!(emitted.source().contains(" [ 0 <- 1 ]"));
}

#[test]
fn ordinary_map_update_rejects_a_non_map_base_locally() {
    let (mut bundle, _) = bundle();
    add_builtin_member(
        &mut bundle,
        BuiltinSort::Map,
        "Map",
        id("Expr", ItemKind::Sort),
    );
    replace_rule_result_with_nested_map_update(&mut bundle);
    forge_non_map_update_base(&mut bundle);

    let error = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap_err();
    let krs_compiler::DescriptorLoweringError::InvalidTerm { detail, .. } = error else {
        panic!("unexpected error: {error:?}")
    };
    assert_eq!(detail, "literal of sort Int is not admissible at sort Map");
}

#[test]
fn explicit_rule_label_controls_emission_sidecars_provenance_and_collisions() {
    let (mut bundle, _) = bundle();
    let mut descriptors = bundle.descriptors.clone();
    let descriptor = descriptors
        .iter_mut()
        .find(|descriptor| matches!(&descriptor.payload, DescriptorPayload::StructuredRule(_)))
        .unwrap();
    let label_key = key(ProvenanceRole::RuleLabel, 0);
    let label_origin = testing::authored_in(
        package(),
        "src/expr.rs",
        testing::digest_with("2".repeat(64)),
        77,
        84,
    );
    let primary = descriptor.provenance.primary_key().clone();
    let mut origins = descriptor.provenance.origins().to_vec();
    origins.push(DescriptorNodeOrigin::new(
        label_key.clone(),
        label_origin.clone(),
    ));
    descriptor.provenance = DescriptorProvenance::new(primary, origins).unwrap();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptor.payload else {
        unreachable!()
    };
    rule.label = Some(DescriptorRuleLabel {
        key: label_key,
        name: "if-true".into(),
    });

    bundle.descriptors = descriptors;
    assert_canonical_contract(&bundle.build().unwrap());
    let semantic = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap();
    assert_canonical_contract(&semantic);
    let (_lowered, emitted) = assert_lowering_contract(&semantic);
    assert!(emitted.source().contains("[label(if-true)]"));
    let symbol = emitted
        .symbol_map()
        .entries()
        .iter()
        .find(|entry| {
            matches!(entry.identity(), MappedIdentity::Label(_))
                && entry.emitted_name() == "if-true"
        })
        .unwrap();
    let source = emitted
        .source_map()
        .entries()
        .iter()
        .find(|entry| {
            entry.node_kind() == SourceMapNodeKind::Rule && entry.key() == symbol.source_map_key()
        })
        .unwrap();
    assert_eq!(
        source.origin().frames().first(),
        label_origin.frames().first()
    );
    let generated = source.generated().unwrap();
    let start = usize::try_from(generated.start_byte()).unwrap();
    let end = usize::try_from(generated.end_byte()).unwrap();
    assert!(emitted.source()[start..end].contains("[label(if-true)]"));

    let mut collision = bundle.clone();
    let mut duplicate = collision
        .descriptors
        .iter()
        .find(|descriptor| matches!(&descriptor.payload, DescriptorPayload::StructuredRule(_)))
        .unwrap()
        .clone();
    duplicate.id = id("other_rule", ItemKind::Rule);
    // A different priority keeps the overlap check (F2) from rejecting the
    // duplicate before the label collision is reached.
    let priority_key = key(ProvenanceRole::RulePriority, 0);
    let primary = duplicate.provenance.primary_key().clone();
    let mut origins = duplicate.provenance.origins().to_vec();
    origins.push(DescriptorNodeOrigin::new(
        priority_key.clone(),
        label_origin.clone(),
    ));
    duplicate.provenance = DescriptorProvenance::new(primary, origins).unwrap();
    let DescriptorPayload::StructuredRule(rule) = &mut duplicate.payload else {
        unreachable!()
    };
    rule.priority = Some(krs_ir::DescriptorRulePriority {
        key: priority_key,
        value: 40,
    });
    collision.descriptors.push(duplicate);
    let semantic = lower_descriptor_bundle(&collision.build().unwrap()).unwrap();
    assert!(matches!(
        lower_semantic_theory(&semantic),
        Err(LoweringError::NameCollision {
            namespace: krs_compiler::CollisionNamespace::EmittedLabel,
            value,
            ..
        }) if value == "if-true"
    ));
}

#[test]
fn grammar_owned_constructor_field_preserves_builtin_sort_through_lowering() {
    let (mut bundle, _) = bundle();
    let add = id("Add", ItemKind::Constructor);
    let mut descriptors = bundle.descriptors.clone();
    let constructor = descriptors
        .iter_mut()
        .find(|descriptor| descriptor.id == add)
        .unwrap();
    let DescriptorPayload::Constructor(constructor) = &mut constructor.payload else {
        unreachable!();
    };
    constructor.fields[0].sort = Some(DescriptorSortRef::Builtin(BuiltinSort::Id));

    let grammar = descriptors.iter_mut()
        .find(|descriptor| {
            matches!(
                &descriptor.payload,
                DescriptorPayload::Grammar(grammar)
                    if matches!(
                        grammar.as_ref(),
                        GrammarDescriptor::Production(DescriptorProduction {
                            owner: DescriptorProductionOwner::Constructor { constructor },
                            ..
                        }) if constructor.application == DescriptorApplicationRef::Declared(add.clone())
                    )
            )
        })
        .unwrap();
    let DescriptorPayload::Grammar(grammar) = &mut grammar.payload else {
        unreachable!();
    };
    let GrammarDescriptor::Production(production) = grammar.as_mut() else {
        unreachable!();
    };
    let DescriptorProductionItem::NonTerminal { sort, .. } = &mut production.items[0] else {
        unreachable!();
    };
    sort.sort = DescriptorSortRef::Builtin(BuiltinSort::Id);

    bundle.descriptors = descriptors;
    assert_canonical_contract(&bundle.build().unwrap());
    let semantic = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap();
    assert_canonical_contract(&semantic);
    let production = semantic.modules()[0]
        .productions()
        .iter()
        .find(|production| production.id() == &add)
        .unwrap();
    assert!(matches!(
        production.items()[0].kind(),
        krs_ir::GrammarProductionItemKind::NonTerminal {
            sort: SemanticSortRef::Builtin(BuiltinSort::Id),
            ..
        }
    ));
    let (_, emitted) = assert_lowering_contract(&semantic);
    assert!(emitted.source().contains("syntax Expr ::= Id \"+\" Expr"));
}

#[test]
fn structured_rule_bindings_refine_to_builtin_subsort_in_every_occurrence() {
    let (mut bundle, _) = bundle();
    add_builtin_expr_subsort(&mut bundle, BuiltinSort::Int, "Int");
    replace_rule_result_with_builtin(
        &mut bundle,
        BuiltinOperation::IntAdd,
        Some(DescriptorLiteral::Int("1".into())),
    );

    assert_canonical_contract(&bundle.build().unwrap());
    let semantic = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap();
    assert_canonical_contract(&semantic);
    let rule = &semantic.modules()[0].rules()[0];
    assert_eq!(
        rule.variables()[0].sort(),
        &SemanticSortRef::Builtin(BuiltinSort::Int)
    );
    let mut occurrences = Vec::new();
    variable_sorts(rule.body().unwrap().from(), &mut occurrences);
    variable_sorts(rule.body().unwrap().to(), &mut occurrences);
    assert_eq!(
        occurrences,
        vec![
            SemanticSortRef::Builtin(BuiltinSort::Int),
            SemanticSortRef::Builtin(BuiltinSort::Int),
        ],
        "subject and result occurrences must use the one inferred binding sort"
    );
}

#[test]
fn structured_rule_bindings_infer_unique_common_descendant_from_all_occurrences() {
    let (mut bundle, _) = bundle();
    let value = add_bool_common_descendant(&mut bundle, "Value");
    add_builtin_member(&mut bundle, BuiltinSort::Int, "Int", value.clone());
    add_bool_not_binding_condition(&mut bundle);

    assert_canonical_contract(&bundle.build().unwrap());
    let semantic = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap();
    assert_canonical_contract(&semantic);
    let rule = &semantic.modules()[0].rules()[0];
    let expected = SemanticSortRef::Declared(value);
    assert_eq!(rule.variables()[0].sort(), &expected);

    let mut occurrences = Vec::new();
    variable_sorts(rule.body().unwrap().from(), &mut occurrences);
    variable_sorts(rule.body().unwrap().to(), &mut occurrences);
    variable_sorts(rule.requires().unwrap().term(), &mut occurrences);
    assert_eq!(
        occurrences,
        vec![expected.clone(), expected],
        "subject and condition occurrences must use the unique common descendant"
    );
}

#[test]
fn structured_rule_bindings_reject_ambiguous_common_descendants_deterministically() {
    let (mut bundle, _) = bundle();
    add_bool_common_descendant(&mut bundle, "LeftValue");
    add_bool_common_descendant(&mut bundle, "RightValue");
    add_bool_not_binding_condition(&mut bundle);

    let first = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap_err();
    let second = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap_err();
    assert_eq!(first, second, "ambiguous inference must be deterministic");
    let krs_compiler::DescriptorLoweringError::InvalidTerm {
        id: offending_id,
        detail,
    } = first
    else {
        panic!("unexpected error: {first}")
    };
    assert_eq!(*offending_id, id("add_wildcard", ItemKind::Rule));
    assert!(
        detail.contains("variable \"x\" has ambiguous most-specific common descendants"),
        "unexpected detail: {detail}"
    );
    let left = detail.find("LeftValue").unwrap();
    let right = detail.find("RightValue").unwrap();
    assert!(
        left < right,
        "candidates must use stable sort order: {detail}"
    );
}

#[test]
fn structured_rule_bindings_reject_absent_common_descendant() {
    let (mut bundle, _) = bundle();
    add_builtin_expr_subsort(&mut bundle, BuiltinSort::Int, "Int");

    let bool_primary = key(ProvenanceRole::SubsortDeclaration, 0);
    push_descriptor(
        &mut bundle,
        DescriptorInputs::new(
            StableItemId::new(
                package(),
                ["expr"],
                "__subsort_Bool_Value",
                ItemKind::Grammar,
                "subsort",
            )
            .unwrap(),
            BTreeMap::new(),
            provenance(
                bool_primary.clone(),
                [
                    key(ProvenanceRole::SubsortSubSort, 0),
                    key(ProvenanceRole::SubsortSuperSort, 0),
                ],
            ),
            DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Subsort {
                key: bool_primary,
                subsort: DescriptorSortReference {
                    key: key(ProvenanceRole::SubsortSubSort, 0),
                    sort: DescriptorSortRef::Builtin(BuiltinSort::Bool),
                },
                supersort: declared_sort(
                    ProvenanceRole::SubsortSuperSort,
                    0,
                    id("Value", ItemKind::Sort),
                ),
            })),
        ),
    );

    let add = id("Add", ItemKind::Constructor);
    let mut descriptors = bundle.descriptors.clone();
    let grammar = descriptors.iter_mut()
        .find(|descriptor| {
            descriptor.id.item_kind() == ItemKind::Grammar
                && matches!(
                    &descriptor.payload,
                    DescriptorPayload::Grammar(grammar)
                        if matches!(
                            grammar.as_ref(),
                            GrammarDescriptor::Production(DescriptorProduction {
                                owner: DescriptorProductionOwner::Constructor { constructor },
                                ..
                            }) if constructor.application == DescriptorApplicationRef::Declared(add.clone())
                        )
                )
        })
        .unwrap();
    let DescriptorPayload::Grammar(grammar) = &mut grammar.payload else {
        unreachable!();
    };
    let GrammarDescriptor::Production(production) = grammar.as_mut() else {
        unreachable!();
    };
    let DescriptorProductionItem::NonTerminal { sort, .. } = &mut production.items[0] else {
        unreachable!();
    };
    sort.sort = DescriptorSortRef::Builtin(BuiltinSort::Int);

    bundle.descriptors = descriptors;
    replace_rule_result_with_builtin(&mut bundle, BuiltinOperation::BoolNot, None);
    let error = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("variable \"x\" has no declared common descendant"),
        "unexpected error: {error}"
    );
}

#[test]
fn malformed_or_orphaned_grammar_provenance_is_rejected_before_semantics() {
    let (mut bundle, _) = bundle();
    let mut descriptors = bundle.descriptors.clone();
    let descriptor = descriptors
        .iter_mut()
        .find(|descriptor| matches!(&descriptor.payload, DescriptorPayload::StructuredRule(_)))
        .unwrap();
    descriptor.provenance = provenance(
        key(ProvenanceRole::RuleDeclaration, 0),
        [
            key(ProvenanceRole::RulePattern, 0),
            key(ProvenanceRole::StableSymbol, 0),
        ],
    );
    bundle.descriptors = descriptors;
    let error = bundle.build().unwrap_err();
    assert!(error.to_string().contains("provenance"));
}

#[test]
fn non_bool_requires_is_rejected_after_descriptor_sort_inference() {
    let (mut bundle, _) = bundle();

    let add = id("Add", ItemKind::Constructor);
    let mut descriptors = bundle.descriptors.clone();
    let grammar = descriptors.iter_mut()
        .find(|descriptor| {
            matches!(
                &descriptor.payload,
                DescriptorPayload::Grammar(grammar)
                    if matches!(
                        grammar.as_ref(),
                        GrammarDescriptor::Production(DescriptorProduction {
                            owner: DescriptorProductionOwner::Constructor { constructor },
                            ..
                        }) if constructor.application == DescriptorApplicationRef::Declared(add.clone())
                    )
            )
        })
        .unwrap();
    let DescriptorPayload::Grammar(grammar) = &mut grammar.payload else {
        unreachable!()
    };
    let GrammarDescriptor::Production(production) = grammar.as_mut() else {
        unreachable!()
    };
    let DescriptorProductionItem::NonTerminal { sort, .. } = &mut production.items[0] else {
        unreachable!()
    };
    sort.sort = DescriptorSortRef::Builtin(BuiltinSort::Int);

    let descriptor = descriptors
        .iter_mut()
        .find(|descriptor| matches!(&descriptor.payload, DescriptorPayload::StructuredRule(_)))
        .unwrap();
    let condition_keys = [
        key(ProvenanceRole::RuleRequires, 0),
        key(ProvenanceRole::RuleRequiresPath, 0),
        key(ProvenanceRole::RuleRequiresPath, 1),
        key(ProvenanceRole::RuleRequiresApplicationHead, 0),
        key(ProvenanceRole::RuleRequiresReference, 0),
        key(ProvenanceRole::RuleRequiresLiteral, 0),
    ];
    let primary = descriptor.provenance.primary_key().clone();
    let mut origins = descriptor.provenance.origins().to_vec();
    origins.extend(
        condition_keys
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, key)| {
                let start = 100 + u32::try_from(index).unwrap();
                DescriptorNodeOrigin::new(
                    key,
                    testing::authored_in(
                        package(),
                        "src/expr.rs",
                        testing::digest_with("2".repeat(64)),
                        start,
                        start + 1,
                    ),
                )
            }),
    );
    descriptor.provenance = DescriptorProvenance::new(primary, origins).unwrap();
    let DescriptorPayload::StructuredRule(rule) = &mut descriptor.payload else {
        unreachable!()
    };
    rule.requires = Some(DescriptorRuleCondition {
        key: key(ProvenanceRole::RuleRequires, 0),
        term: DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: key(ProvenanceRole::RuleRequiresApplicationHead, 0),
                application: DescriptorApplicationRef::Builtin(BuiltinOperation::IntAdd),
            },
            path_key: key(ProvenanceRole::RuleRequiresPath, 0),
            arguments: vec![
                DescriptorTermArgument::Positional {
                    value: Box::new(DescriptorTerm::Variable {
                        key: key(ProvenanceRole::RuleRequiresReference, 0),
                        path_key: key(ProvenanceRole::RuleRequiresPath, 1),
                        name: "x".into(),
                    }),
                },
                DescriptorTermArgument::Positional {
                    value: Box::new(DescriptorTerm::Literal {
                        key: key(ProvenanceRole::RuleRequiresLiteral, 0),
                        literal: DescriptorLiteral::Int("1".into()),
                    }),
                },
            ]
            .try_into()
            .unwrap(),
        },
    });

    bundle.descriptors = descriptors;
    let error = lower_descriptor_bundle(&bundle.build().unwrap()).unwrap_err();
    assert!(matches!(
        error,
        krs_compiler::DescriptorLoweringError::InvalidTerm { detail, .. }
            if detail == "application result sort Int is not admissible at sort Bool"
    ));
}

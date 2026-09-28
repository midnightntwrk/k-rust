//! Stable grammar and structured-rule descriptors lower without reparsing Rust spellings.

use std::collections::BTreeMap;

use krs_compiler::{
    LoweringError, MappedIdentity, SourceMapNodeKind, emit_k, lower_descriptor_bundle,
    lower_semantic_theory,
};
use krs_ir::testing;
use krs_ir::{
    BuiltinOperation, BuiltinSort, CellWrapper, ConstructorDescriptor, ConstructorFieldDescriptor,
    Descriptor, DescriptorApplicationHeadClass, DescriptorApplicationRef,
    DescriptorApplicationReference, DescriptorBundle, DescriptorGroupReference, DescriptorLiteral,
    DescriptorNodeOrigin, DescriptorPayload, DescriptorPrecedenceChain, DescriptorProduction,
    DescriptorProductionAttribute, DescriptorProductionItem, DescriptorProductionOwner,
    DescriptorProvenance, DescriptorRuleCondition, DescriptorRuleLabel, DescriptorSortRef,
    DescriptorSortReference, DescriptorTerm, DescriptorTermArgument, GeneratedProductionKind,
    GrammarDescriptor, GroupAssociativity, ItemKind, MapOperation, PackageId, ProductionFieldId,
    ProductionGroupId, ProvenanceKey, ProvenanceRole, SemanticSortRef, SemanticTerm,
    SemanticTermKind, SentenceKind, SortDescriptor, StableItemId, StructuredRuleDescriptor,
    generated_production_id,
};

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
) -> Descriptor {
    let extra = matches!(payload, DescriptorPayload::Constructor(_))
        .then(|| key(ProvenanceRole::ConstructorDeclaration, 0));
    Descriptor {
        id,
        cfg: BTreeMap::new(),
        provenance: provenance(key(primary, 0), extra),
        payload,
    }
}

fn machine_configuration(start: StableItemId) -> Descriptor {
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
                                        arguments: vec![],
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
    Descriptor {
        id: owner,
        cfg: BTreeMap::new(),
        provenance: provenance(key(ProvenanceRole::ConfigurationDeclaration, 0), keys),
        payload: DescriptorPayload::FixedConfiguration(Box::new(configuration)),
    }
}

#[allow(clippy::too_many_lines)]
fn bundle() -> (DescriptorBundle, StableItemId) {
    let expr = id("Expr", ItemKind::Sort);
    let add = id("Add", ItemKind::Constructor);
    let unit = id("Unit", ItemKind::Constructor);
    let start = id("Start", ItemKind::Constructor);
    let add_grammar_id = id("Add", ItemKind::Grammar);
    let unit_grammar_id =
        StableItemId::new(package(), ["expr"], "Unit", ItemKind::Grammar, "production").unwrap();
    let bracket_grammar_id = id("ExprBracket", ItemKind::Grammar);
    let additive = ProductionGroupId::new("additive").unwrap();
    let atom = ProductionGroupId::new("atom").unwrap();

    let mut descriptors = vec![
        declaration(
            expr.clone(),
            DescriptorPayload::Sort(SortDescriptor { parents: vec![] }),
            ProvenanceRole::SortDeclaration,
        ),
        declaration(
            add.clone(),
            DescriptorPayload::Constructor(ConstructorDescriptor {
                sort: DescriptorSortRef::Declared(expr.clone()),
                syntax: None,
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
                syntax: None,
                fields: vec![],
            }),
            ProvenanceRole::ConstructorSort,
        ),
        declaration(
            start.clone(),
            DescriptorPayload::Constructor(ConstructorDescriptor {
                sort: DescriptorSortRef::Declared(expr.clone()),
                syntax: None,
                fields: vec![],
            }),
            ProvenanceRole::ConstructorSort,
        ),
    ];

    let add_primary = key(ProvenanceRole::ConstructorDeclaration, 0);
    descriptors.push(Descriptor {
        id: add_grammar_id,
        cfg: BTreeMap::new(),
        provenance: provenance(
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
        payload: DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Production(
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
    });

    let unit_primary = key(ProvenanceRole::ConstructorDeclaration, 0);
    descriptors.push(Descriptor {
        id: unit_grammar_id,
        cfg: BTreeMap::new(),
        provenance: provenance(
            unit_primary.clone(),
            [
                key(ProvenanceRole::ConstructorSort, 0),
                key(ProvenanceRole::ConstructorGroup, 0),
            ],
        ),
        payload: DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Production(
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
    });

    let bracket_primary = key(ProvenanceRole::BracketDeclaration, 0);
    descriptors.push(Descriptor {
        id: bracket_grammar_id.clone(),
        cfg: BTreeMap::new(),
        provenance: provenance(
            bracket_primary.clone(),
            [
                key(ProvenanceRole::SortDeclaration, 0),
                key(ProvenanceRole::BracketSyntaxItem, 0),
                key(ProvenanceRole::BracketSyntaxItem, 1),
                key(ProvenanceRole::BracketSyntaxItem, 2),
                key(ProvenanceRole::BracketValueReference, 0),
            ],
        ),
        payload: DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Production(
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
    });

    let precedence_primary = key(ProvenanceRole::PrecedenceDeclaration, 0);
    descriptors.push(Descriptor {
        id: id("Precedence", ItemKind::Grammar),
        cfg: BTreeMap::new(),
        provenance: provenance(
            precedence_primary.clone(),
            [
                key(ProvenanceRole::PrecedenceChain, 0),
                key(ProvenanceRole::PrecedenceGroupReference, 0),
                key(ProvenanceRole::PrecedenceGroupReference, 1),
            ],
        ),
        payload: DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Precedence {
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
                ],
            }],
        })),
    });
    let assoc_primary = key(ProvenanceRole::AssociativityDeclaration, 0);
    descriptors.push(Descriptor {
        id: id("Associativity", ItemKind::Grammar),
        cfg: BTreeMap::new(),
        provenance: provenance(
            assoc_primary.clone(),
            [
                key(ProvenanceRole::AssociativitySentence, 0),
                key(ProvenanceRole::AssociativityGroupReference, 0),
            ],
        ),
        payload: DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Associativity {
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
    });

    let rule_primary = key(ProvenanceRole::RuleDeclaration, 0);
    descriptors.push(Descriptor {
        id: id("add_wildcard", ItemKind::Rule),
        cfg: BTreeMap::new(),
        provenance: provenance(
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
        payload: DescriptorPayload::StructuredRule(Box::new(StructuredRuleDescriptor {
            sentence_kind: SentenceKind::Transition,
            label: None,
            requires: None,
            priority: None,
            simplification: None,
            pattern_key: key(ProvenanceRole::RulePattern, 0),
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
                ],
            },
            result: DescriptorTerm::Application {
                head_class: DescriptorApplicationHeadClass::BareReference,
                reference: DescriptorApplicationReference {
                    key: key(ProvenanceRole::RuleRightReference, 0),
                    application: DescriptorApplicationRef::Declared(unit),
                },
                path_key: key(ProvenanceRole::RuleRightPath, 0),
                arguments: vec![],
            },
        })),
    });

    descriptors.push(machine_configuration(start));
    (
        DescriptorBundle::new(descriptors),
        generated_production_id(&bracket_grammar_id, GeneratedProductionKind::Bracket).unwrap(),
    )
}

fn add_builtin_expr_subsort(
    bundle: &mut DescriptorBundle,
    builtin: BuiltinSort,
    builtin_name: &str,
) {
    let expr = id("Expr", ItemKind::Sort);
    let value = id("Value", ItemKind::Sort);
    bundle.descriptors.push(Descriptor {
        id: value.clone(),
        cfg: BTreeMap::new(),
        provenance: provenance(
            key(ProvenanceRole::SortDeclaration, 0),
            [key(ProvenanceRole::SortParent, 0)],
        ),
        payload: DescriptorPayload::Sort(SortDescriptor {
            parents: vec![expr],
        }),
    });
    let primary = key(ProvenanceRole::SubsortDeclaration, 0);
    bundle.descriptors.push(Descriptor {
        id: StableItemId::new(
            package(),
            ["expr"],
            format!("__subsort_{builtin_name}_Value"),
            ItemKind::Grammar,
            "subsort",
        )
        .unwrap(),
        cfg: BTreeMap::new(),
        provenance: provenance(
            primary.clone(),
            [
                key(ProvenanceRole::SubsortSubSort, 0),
                key(ProvenanceRole::SubsortSuperSort, 0),
            ],
        ),
        payload: DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Subsort {
            key: primary,
            subsort: DescriptorSortReference {
                key: key(ProvenanceRole::SubsortSubSort, 0),
                sort: DescriptorSortRef::Builtin(builtin),
            },
            supersort: declared_sort(ProvenanceRole::SubsortSuperSort, 0, value),
        })),
    });
}

fn replace_rule_result_with_builtin(
    bundle: &mut DescriptorBundle,
    operation: BuiltinOperation,
    second_argument: Option<DescriptorLiteral>,
) {
    let descriptor = bundle
        .descriptors
        .iter_mut()
        .find(|descriptor| matches!(descriptor.payload, DescriptorPayload::StructuredRule(_)))
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
        arguments,
    };
}

fn add_bool_common_descendant(bundle: &mut DescriptorBundle, name: &str) -> StableItemId {
    let expr = id("Expr", ItemKind::Sort);
    let descendant = id(name, ItemKind::Sort);
    bundle.descriptors.push(Descriptor {
        id: descendant.clone(),
        cfg: BTreeMap::new(),
        provenance: provenance(
            key(ProvenanceRole::SortDeclaration, 0),
            [key(ProvenanceRole::SortParent, 0)],
        ),
        payload: DescriptorPayload::Sort(SortDescriptor {
            parents: vec![expr],
        }),
    });
    let primary = key(ProvenanceRole::SubsortDeclaration, 0);
    bundle.descriptors.push(Descriptor {
        id: StableItemId::new(
            package(),
            ["expr"],
            format!("__subsort_{name}_Bool"),
            ItemKind::Grammar,
            "subsort",
        )
        .unwrap(),
        cfg: BTreeMap::new(),
        provenance: provenance(
            primary.clone(),
            [
                key(ProvenanceRole::SubsortSubSort, 0),
                key(ProvenanceRole::SubsortSuperSort, 0),
            ],
        ),
        payload: DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Subsort {
            key: primary,
            subsort: declared_sort(ProvenanceRole::SubsortSubSort, 0, descendant.clone()),
            supersort: DescriptorSortReference {
                key: key(ProvenanceRole::SubsortSuperSort, 0),
                sort: DescriptorSortRef::Builtin(BuiltinSort::Bool),
            },
        })),
    });
    descendant
}

fn add_builtin_member(
    bundle: &mut DescriptorBundle,
    builtin: BuiltinSort,
    builtin_name: &str,
    parent: StableItemId,
) {
    let primary = key(ProvenanceRole::SubsortDeclaration, 0);
    bundle.descriptors.push(Descriptor {
        id: StableItemId::new(
            package(),
            ["expr"],
            format!("__subsort_{builtin_name}_{}", parent.item_name()),
            ItemKind::Grammar,
            "subsort",
        )
        .unwrap(),
        cfg: BTreeMap::new(),
        provenance: provenance(
            primary.clone(),
            [
                key(ProvenanceRole::SubsortSubSort, 0),
                key(ProvenanceRole::SubsortSuperSort, 0),
            ],
        ),
        payload: DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Subsort {
            key: primary,
            subsort: DescriptorSortReference {
                key: key(ProvenanceRole::SubsortSubSort, 0),
                sort: DescriptorSortRef::Builtin(builtin),
            },
            supersort: declared_sort(ProvenanceRole::SubsortSuperSort, 0, parent),
        })),
    });
}

fn add_bool_not_binding_condition(bundle: &mut DescriptorBundle) {
    let descriptor = bundle
        .descriptors
        .iter_mut()
        .find(|descriptor| matches!(descriptor.payload, DescriptorPayload::StructuredRule(_)))
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
            }],
        },
    });
}

fn variable_sorts(term: &SemanticTerm, output: &mut Vec<SemanticSortRef>) {
    match term.kind() {
        SemanticTermKind::Variable { variable } if variable.as_str() == "x" => {
            output.push(term.sort().clone());
        }
        SemanticTermKind::Application { arguments, .. }
        | SemanticTermKind::Map { arguments, .. }
        | SemanticTermKind::List { arguments, .. }
        | SemanticTermKind::Set { arguments, .. } => {
            for argument in arguments {
                variable_sorts(argument, output);
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

fn replace_rule_result_with_nested_map_update(bundle: &mut DescriptorBundle) {
    let descriptor = bundle
        .descriptors
        .iter_mut()
        .find(|descriptor| matches!(descriptor.payload, DescriptorPayload::StructuredRule(_)))
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
            application: DescriptorApplicationRef::Map(MapOperation::Update),
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
        ],
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
        ],
    };
}

fn forge_non_map_update_base(bundle: &mut DescriptorBundle) {
    let descriptor = bundle
        .descriptors
        .iter_mut()
        .find(|descriptor| matches!(descriptor.payload, DescriptorPayload::StructuredRule(_)))
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
    let DescriptorTermArgument::Positional { value: update } = &mut outer[0] else {
        unreachable!()
    };
    let DescriptorTerm::Application {
        arguments: update_arguments,
        ..
    } = update.as_mut()
    else {
        unreachable!()
    };
    update_arguments[0] = DescriptorTermArgument::Positional {
        value: Box::new(DescriptorTerm::Literal {
            key: key(ProvenanceRole::RuleRightLiteral, 0),
            literal: DescriptorLiteral::Int("2".into()),
        }),
    };
    for (argument, ordinal) in update_arguments[1..].iter_mut().zip(1_u32..) {
        let DescriptorTermArgument::Positional { value } = argument else {
            unreachable!()
        };
        let DescriptorTerm::Literal {
            key: literal_key, ..
        } = value.as_mut()
        else {
            unreachable!()
        };
        *literal_key = key(ProvenanceRole::RuleRightLiteral, ordinal);
    }
    let DescriptorTermArgument::Positional { value: second } = &mut outer[1] else {
        unreachable!()
    };
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
}

#[test]
fn declared_sort_names_cannot_collide_with_builtin_k_names() {
    for builtin in BuiltinSort::ALL {
        let (mut descriptors, _) = bundle();
        let sort_id = id(builtin.k_name(), ItemKind::Sort);
        descriptors.descriptors.push(declaration(
            sort_id.clone(),
            DescriptorPayload::Sort(SortDescriptor { parents: vec![] }),
            ProvenanceRole::SortDeclaration,
        ));
        let error = lower_descriptor_bundle(&descriptors)
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
        DescriptorPayload::Sort(SortDescriptor { parents: vec![] }),
        ProvenanceRole::SortDeclaration,
    ));
    descriptors
        .declarations
        .push(krs_ir::DescriptorDeclaration::new(
            sort_id,
            krs_ir::RustVisibility::Public,
            Some(krs_ir::ExplicitSymbol::new("domain::String").unwrap()),
        ));
    let error = lower_descriptor_bundle(&descriptors)
        .unwrap_err()
        .to_string();
    assert!(
        error.contains("use `k::builtin::String` instead"),
        "{error}"
    );
}

#[test]
fn named_record_wildcard_bare_constructor_and_generated_bracket_lower() {
    let (bundle, bracket_id) = bundle();
    let semantic = lower_descriptor_bundle(&bundle).unwrap();
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
    let k = emit_k(&lower_semantic_theory(&semantic).unwrap()).unwrap();
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

    let semantic = lower_descriptor_bundle(&bundle).unwrap();
    let rule = &semantic.modules()[0].rules()[0];
    assert_eq!(rule.variables()[0].sort(), &SemanticSortRef::map());
    let SemanticTermKind::Rewrite { to, .. } = rule.body().unwrap().kind() else {
        panic!("ordinary rule must lower to a rewrite")
    };
    let SemanticTermKind::Application { arguments, .. } = to.kind() else {
        panic!("map update must remain nested under Add")
    };
    assert!(matches!(
        arguments[0].kind(),
        SemanticTermKind::Map {
            operation: MapOperation::Update,
            arguments,
        } if arguments.len() == 3
    ));

    let definition = lower_semantic_theory(&semantic).unwrap();
    let emitted = emit_k(&definition).unwrap();
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

    let error = lower_descriptor_bundle(&bundle).unwrap_err();
    let krs_compiler::DescriptorLoweringError::InvalidTerm { detail, .. } = error else {
        panic!("unexpected error: {error:?}")
    };
    assert_eq!(detail, "literal of sort Int is not admissible at sort Map");
}

#[test]
fn explicit_rule_label_controls_emission_sidecars_provenance_and_collisions() {
    let (mut bundle, _) = bundle();
    let descriptor = bundle
        .descriptors
        .iter_mut()
        .find(|descriptor| matches!(descriptor.payload, DescriptorPayload::StructuredRule(_)))
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

    let semantic = lower_descriptor_bundle(&bundle).unwrap();
    let lowered = lower_semantic_theory(&semantic).unwrap();
    let emitted = emit_k(&lowered).unwrap();
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
        .find(|descriptor| matches!(descriptor.payload, DescriptorPayload::StructuredRule(_)))
        .unwrap()
        .clone();
    duplicate.id = id("other_rule", ItemKind::Rule);
    collision.descriptors.push(duplicate);
    let semantic = lower_descriptor_bundle(&collision).unwrap();
    assert!(matches!(
        lower_semantic_theory(&semantic),
        Err(LoweringError::NameCollision {
            namespace: "emitted label",
            value,
            ..
        }) if value == "if-true"
    ));
}

#[test]
fn grammar_owned_constructor_field_preserves_builtin_sort_through_lowering() {
    let (mut bundle, _) = bundle();
    let add = id("Add", ItemKind::Constructor);
    let constructor = bundle
        .descriptors
        .iter_mut()
        .find(|descriptor| descriptor.id == add)
        .unwrap();
    let DescriptorPayload::Constructor(constructor) = &mut constructor.payload else {
        unreachable!();
    };
    constructor.fields[0].sort = Some(DescriptorSortRef::Builtin(BuiltinSort::Id));

    let grammar = bundle
        .descriptors
        .iter_mut()
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

    let semantic = lower_descriptor_bundle(&bundle).unwrap();
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
    let emitted = emit_k(&lower_semantic_theory(&semantic).unwrap()).unwrap();
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

    let semantic = lower_descriptor_bundle(&bundle).unwrap();
    let rule = &semantic.modules()[0].rules()[0];
    assert_eq!(
        rule.variables()[0].sort(),
        &SemanticSortRef::Builtin(BuiltinSort::Int)
    );
    let mut occurrences = Vec::new();
    variable_sorts(rule.body().unwrap(), &mut occurrences);
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

    let semantic = lower_descriptor_bundle(&bundle).unwrap();
    let rule = &semantic.modules()[0].rules()[0];
    let expected = SemanticSortRef::Declared(value);
    assert_eq!(rule.variables()[0].sort(), &expected);

    let mut occurrences = Vec::new();
    variable_sorts(rule.body().unwrap(), &mut occurrences);
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

    let first = lower_descriptor_bundle(&bundle).unwrap_err();
    let second = lower_descriptor_bundle(&bundle).unwrap_err();
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
    bundle.descriptors.push(Descriptor {
        id: StableItemId::new(
            package(),
            ["expr"],
            "__subsort_Bool_Value",
            ItemKind::Grammar,
            "subsort",
        )
        .unwrap(),
        cfg: BTreeMap::new(),
        provenance: provenance(
            bool_primary.clone(),
            [
                key(ProvenanceRole::SubsortSubSort, 0),
                key(ProvenanceRole::SubsortSuperSort, 0),
            ],
        ),
        payload: DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Subsort {
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
    });

    let add = id("Add", ItemKind::Constructor);
    let grammar = bundle
        .descriptors
        .iter_mut()
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

    replace_rule_result_with_builtin(&mut bundle, BuiltinOperation::BoolNot, None);
    let error = lower_descriptor_bundle(&bundle).unwrap_err();
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
    let descriptor = bundle
        .descriptors
        .iter_mut()
        .find(|descriptor| matches!(descriptor.payload, DescriptorPayload::StructuredRule(_)))
        .unwrap();
    descriptor.provenance = provenance(
        key(ProvenanceRole::RuleDeclaration, 0),
        [
            key(ProvenanceRole::RulePattern, 0),
            key(ProvenanceRole::StableSymbol, 0),
        ],
    );
    let error = lower_descriptor_bundle(&bundle).unwrap_err();
    assert!(error.to_string().contains("provenance"));
}

#[test]
fn non_bool_requires_is_rejected_after_descriptor_sort_inference() {
    let (mut bundle, _) = bundle();

    let add = id("Add", ItemKind::Constructor);
    let grammar = bundle
        .descriptors
        .iter_mut()
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

    let descriptor = bundle
        .descriptors
        .iter_mut()
        .find(|descriptor| matches!(descriptor.payload, DescriptorPayload::StructuredRule(_)))
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
            ],
        },
    });

    let error = lower_descriptor_bundle(&bundle).unwrap_err();
    assert!(matches!(
        error,
        krs_compiler::DescriptorLoweringError::InvalidTerm { detail, .. }
            if detail == "application result sort Int is not admissible at sort Bool"
    ));
}

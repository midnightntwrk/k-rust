//! The grammar fixture bundle: an `Expr` sort with constructors, productions, a bracket, and a
//! structured rule, and the edit that adds `Value: Expr` with a builtin below `Value`.

use krs_ir::testing::{DescriptorBundleInputs, DescriptorInputs};

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::testing;
use krs_ir::{
    BuiltinSort, CellWrapper, ConstructorDescriptor, ConstructorFieldDescriptor,
    DescriptorApplicationHeadClass, DescriptorApplicationRef, DescriptorApplicationReference,
    DescriptorGroupReference, DescriptorNodeOrigin, DescriptorPayload, DescriptorPrecedenceChain,
    DescriptorProduction, DescriptorProductionAttribute, DescriptorProductionItem,
    DescriptorProductionOwner, DescriptorProvenance, DescriptorSortRef, DescriptorSortReference,
    DescriptorTerm, DescriptorTermArgument, GeneratedProductionKind, GrammarDescriptor,
    GroupAssociativity, ItemKind, PackageId, ProductionFieldId, ProductionGroupId, ProvenanceKey,
    ProvenanceRole, SentenceKind, SortDescriptor, StableItemId, StructuredRuleDescriptor,
    generated_production_id,
};

pub fn package() -> PackageId {
    testing::package("KRS-GRAMMAR", "grammar")
}

pub fn id(name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), "expr", name, kind)
}

pub fn key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal)
}

pub fn provenance(
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

pub fn declared_sort(
    role: ProvenanceRole,
    ordinal: u32,
    sort: StableItemId,
) -> DescriptorSortReference {
    DescriptorSortReference {
        key: key(role, ordinal),
        sort: DescriptorSortRef::Declared(sort),
    }
}

pub fn declaration(
    id: StableItemId,
    payload: DescriptorPayload,
    primary: ProvenanceRole,
) -> DescriptorInputs {
    let keys = testing::declaration_keys(&payload);
    DescriptorInputs::new(
        id,
        BTreeMap::new(),
        provenance(key(primary, 0), keys),
        payload,
    )
}

pub fn machine_configuration(start: StableItemId) -> DescriptorInputs {
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
                initial: None,
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
                            payload_key: key(ProvenanceRole::KSequencePayload, 0),
                            dot_k_key: None,
                            notation: krs_ir::DescriptorKSequenceNotation::Comma,
                            items: vec![krs_ir::ProtocolKSequenceItem {
                                key: key(ProvenanceRole::KSequenceItem, 0),
                                value: krs_ir::ProtocolInitializerTerm {
                                    key: key(ProvenanceRole::InitializerTerm, 0),
                                    term: DescriptorTerm::Application {
                                        instance: Vec::new(),
                                        head_class: DescriptorApplicationHeadClass::BareReference,
                                        reference: DescriptorApplicationReference {
                                            key: key(ProvenanceRole::InitializerTermPath, 0),
                                            application: DescriptorApplicationRef::Declared(start),
                                        },
                                        path_key: key(ProvenanceRole::InitializerTermPath, 0),
                                        arguments: vec![].try_into().unwrap(),
                                        update: None,
                                        open: false,
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
pub fn bundle() -> (DescriptorBundleInputs, StableItemId) {
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
                parameters: Vec::new(),
                sort: DescriptorSortRef::Declared(expr.clone()),
                fields: vec![
                    ConstructorFieldDescriptor {
                        name: "lhs".into(),
                        sort: declared_sort(ProvenanceRole::ConstructorFieldSort, 0, expr.clone()),
                        arguments: Vec::new(),
                    },
                    ConstructorFieldDescriptor {
                        name: "rhs".into(),
                        sort: declared_sort(ProvenanceRole::ConstructorFieldSort, 1, expr.clone()),
                        arguments: Vec::new(),
                    },
                ],
                arguments: Vec::new(),
            }),
            ProvenanceRole::ConstructorSort,
        ),
        declaration(
            unit.clone(),
            DescriptorPayload::Constructor(ConstructorDescriptor {
                parameters: Vec::new(),
                sort: DescriptorSortRef::Declared(expr.clone()),
                fields: vec![],
                arguments: Vec::new(),
            }),
            ProvenanceRole::ConstructorSort,
        ),
        declaration(
            start.clone(),
            DescriptorPayload::Constructor(ConstructorDescriptor {
                parameters: Vec::new(),
                sort: DescriptorSortRef::Declared(expr.clone()),
                fields: vec![],
                arguments: Vec::new(),
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
                parameters: Vec::new(),
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
                parameters: Vec::new(),
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
                parameters: Vec::new(),
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
                parameters: Vec::new(),
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
            result_key: Some(key(ProvenanceRole::RuleResult, 0)),
            subject_sort: declared_sort(ProvenanceRole::RuleType, 0, expr.clone()),
            result_sort: Some(declared_sort(
                ProvenanceRole::RuleResultType,
                0,
                expr.clone(),
            )),
            bindings: vec!["x".into()],
            subject: DescriptorTerm::Application {
                instance: Vec::new(),
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
                update: None,
                open: false,
            },
            result: Some(DescriptorTerm::Application {
                instance: Vec::new(),
                head_class: DescriptorApplicationHeadClass::BareReference,
                reference: DescriptorApplicationReference {
                    key: key(ProvenanceRole::RuleRightReference, 0),
                    application: DescriptorApplicationRef::Declared(unit),
                },
                path_key: key(ProvenanceRole::RuleRightPath, 0),
                arguments: vec![].try_into().unwrap(),
                update: None,
                open: false,
            }),
            existentials: Vec::new(),
            ensures: None,
            fresh: Vec::new(),
            equation: None,
            unbound_variables: None,
            function_context: None,
            predicate: false,
            evaluation: None,
        })),
    ));

    descriptors.push(machine_configuration(start));
    (
        DescriptorBundleInputs::new(descriptors),
        generated_production_id(&bracket_grammar_id, GeneratedProductionKind::Bracket).unwrap(),
    )
}

/// Adds a descriptor with inherited declaration metadata, as [`bundle`] builds them.
pub fn push_descriptor(bundle: &mut DescriptorBundleInputs, descriptor: DescriptorInputs) {
    let mut descriptors = bundle.descriptors.clone();
    descriptors.push(descriptor);
    *bundle = DescriptorBundleInputs::new(descriptors);
}

pub fn add_builtin_expr_subsort(
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
                parents: [krs_ir::DescriptorSortParent {
                    sort: expr,
                    key: key(ProvenanceRole::SortParent, 0),
                }]
                .into(),
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

//! Typed hook signatures in semantic and Definition IR.

use krs_ir::testing::{assert_canonical_contract, item, origin as node};
use krs_ir::{
    ConfigurationRoot, DefinitionIr, DefinitionModule, DefinitionSentence, DefinitionSortRef,
    DefinitionTerm, DefinitionValidationError, FixedCell, FixedConfiguration, FixedInitializerCell,
    HookOperation, ItemKind, ModuleId, ProductionAttribute, ProductionFieldId, ProductionItem,
    ProductionSentence, SemanticId, SemanticProduction, SemanticProductionItem, SemanticSortRef,
    SemanticValidationError, SymbolId, SymbolIdentity, SymbolKind, SyntaxSortSentence,
};

fn symbol(id: &str, name: &str, kind: SymbolKind) -> SymbolIdentity {
    SymbolIdentity::new(SymbolId::new(id).unwrap(), name, kind).unwrap()
}

#[test]
fn typed_hook_signatures_are_enforced_in_semantic_and_definition_ir() {
    let semantic_items = |sort| {
        vec![
            SemanticProductionItem::terminal(node("hook.semantic.open"), "Keccak256raw(").unwrap(),
            SemanticProductionItem::non_terminal(
                node("hook.semantic.value"),
                ProductionFieldId::new("value").unwrap(),
                sort,
            ),
            SemanticProductionItem::terminal(node("hook.semantic.close"), ")").unwrap(),
        ]
    };
    let semantic_attributes = || {
        vec![
            ProductionAttribute::Function {
                origin: node("hook.semantic.function"),
            },
            ProductionAttribute::Total {
                origin: node("hook.semantic.total"),
            },
            ProductionAttribute::Hook {
                origin: node("hook.semantic.hook"),
                operation: HookOperation::KryptoKeccak256Raw,
            },
        ]
    };
    assert!(
        SemanticProduction::new(
            node("hook.semantic.production.valid"),
            item("syntax", "Keccak", ItemKind::Constructor),
            SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bytes),
            semantic_items(SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bytes)),
            semantic_attributes(),
        )
        .is_ok()
    );
    assert_eq!(
        SemanticProduction::new(
            node("hook.semantic.production.invalid"),
            item("syntax", "BadKeccak", ItemKind::Constructor),
            SemanticSortRef::Builtin(krs_ir::BuiltinSort::Int),
            semantic_items(SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bytes)),
            semantic_attributes(),
        ),
        Err(SemanticValidationError::InvalidHookSignature(
            HookOperation::KryptoKeccak256Raw,
        ))
    );

    let definition_items = |sort| {
        vec![
            ProductionItem::terminal(node("hook.definition.open"), "Keccak256raw(").unwrap(),
            ProductionItem::non_terminal(
                node("hook.definition.value"),
                ProductionFieldId::new("value").unwrap(),
                sort,
            ),
            ProductionItem::terminal(node("hook.definition.close"), ")").unwrap(),
        ]
    };
    let definition_attributes = || {
        vec![
            ProductionAttribute::Function {
                origin: node("hook.definition.function"),
            },
            ProductionAttribute::Total {
                origin: node("hook.definition.total"),
            },
            ProductionAttribute::Hook {
                origin: node("hook.definition.hook"),
                operation: HookOperation::KryptoKeccak256Raw,
            },
        ]
    };
    assert!(
        ProductionSentence::new(
            node("hook.definition.production.valid"),
            symbol("production.keccak", "Keccak256raw", SymbolKind::Production),
            DefinitionSortRef::Builtin(krs_ir::BuiltinSort::Bytes),
            definition_items(DefinitionSortRef::Builtin(krs_ir::BuiltinSort::Bytes)),
            definition_attributes(),
        )
        .is_ok()
    );
    assert_eq!(
        ProductionSentence::new(
            node("hook.definition.production.invalid"),
            symbol("production.bad-keccak", "BadKeccak", SymbolKind::Production),
            DefinitionSortRef::Builtin(krs_ir::BuiltinSort::Bytes),
            definition_items(DefinitionSortRef::Builtin(krs_ir::BuiltinSort::Int)),
            definition_attributes(),
        ),
        Err(DefinitionValidationError::InvalidHookSignature(
            HookOperation::KryptoKeccak256Raw,
        ))
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Exercises every declared-sort BN128 signature in both IR layers.
fn declared_sort_bn128_hook_signatures_are_enforced_in_both_ir_layers() {
    let point = item("syntax", "G1Point", ItemKind::Sort);
    let other = item("syntax", "OtherPoint", ItemKind::Sort);
    let semantic_attributes = |operation| {
        vec![
            ProductionAttribute::Function {
                origin: node("hook.bn128.semantic.function"),
            },
            ProductionAttribute::Total {
                origin: node("hook.bn128.semantic.total"),
            },
            ProductionAttribute::Hook {
                origin: node("hook.bn128.semantic.hook"),
                operation,
            },
        ]
    };
    let semantic_argument = |key: &str, field: &str, sort| {
        SemanticProductionItem::non_terminal(
            node(key),
            ProductionFieldId::new(field).unwrap(),
            sort,
        )
    };
    assert!(
        SemanticProduction::new(
            node("hook.bn128.semantic.valid.production"),
            item("syntax", "Bn128Valid", ItemKind::Constructor),
            SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bool),
            vec![semantic_argument(
                "hook.bn128.semantic.valid.point",
                "point",
                SemanticSortRef::declared(point.clone()),
            )],
            semantic_attributes(HookOperation::KryptoBn128Valid),
        )
        .is_ok()
    );
    assert!(
        SemanticProduction::new(
            node("hook.bn128.semantic.add.production"),
            item("syntax", "Bn128Add", ItemKind::Constructor),
            SemanticSortRef::declared(point.clone()),
            vec![
                semantic_argument(
                    "hook.bn128.semantic.add.left",
                    "left",
                    SemanticSortRef::declared(point.clone()),
                ),
                semantic_argument(
                    "hook.bn128.semantic.add.right",
                    "right",
                    SemanticSortRef::declared(point.clone()),
                ),
            ],
            semantic_attributes(HookOperation::KryptoBn128Add),
        )
        .is_ok()
    );
    assert!(
        SemanticProduction::new(
            node("hook.bn128.semantic.mul.production"),
            item("syntax", "Bn128Mul", ItemKind::Constructor),
            SemanticSortRef::declared(point.clone()),
            vec![
                semantic_argument(
                    "hook.bn128.semantic.mul.point",
                    "point",
                    SemanticSortRef::declared(point.clone()),
                ),
                semantic_argument(
                    "hook.bn128.semantic.mul.scalar",
                    "scalar",
                    SemanticSortRef::Builtin(krs_ir::BuiltinSort::Int),
                ),
            ],
            semantic_attributes(HookOperation::KryptoBn128Mul),
        )
        .is_ok()
    );
    assert_eq!(
        SemanticProduction::new(
            node("hook.bn128.semantic.bad-add.production"),
            item("syntax", "BadBn128Add", ItemKind::Constructor),
            SemanticSortRef::declared(point.clone()),
            vec![
                semantic_argument(
                    "hook.bn128.semantic.bad-add.left",
                    "left",
                    SemanticSortRef::declared(point.clone()),
                ),
                semantic_argument(
                    "hook.bn128.semantic.bad-add.right",
                    "right",
                    SemanticSortRef::declared(other.clone()),
                ),
            ],
            semantic_attributes(HookOperation::KryptoBn128Add),
        ),
        Err(SemanticValidationError::InvalidHookSignature(
            HookOperation::KryptoBn128Add,
        ))
    );
    assert_eq!(
        SemanticProduction::new(
            node("hook.bn128.semantic.bad-mul.production"),
            item("syntax", "BadBn128Mul", ItemKind::Constructor),
            SemanticSortRef::declared(point.clone()),
            vec![
                semantic_argument(
                    "hook.bn128.semantic.bad-mul.point",
                    "point",
                    SemanticSortRef::declared(point.clone()),
                ),
                semantic_argument(
                    "hook.bn128.semantic.bad-mul.scalar",
                    "scalar",
                    SemanticSortRef::declared(other),
                ),
            ],
            semantic_attributes(HookOperation::KryptoBn128Mul),
        ),
        Err(SemanticValidationError::InvalidHookSignature(
            HookOperation::KryptoBn128Mul,
        ))
    );

    let point = SymbolId::new("sort.g1-point").unwrap();
    let other = SymbolId::new("sort.other-point").unwrap();
    let definition_attributes = |operation| {
        vec![
            ProductionAttribute::Function {
                origin: node("hook.bn128.definition.function"),
            },
            ProductionAttribute::Total {
                origin: node("hook.bn128.definition.total"),
            },
            ProductionAttribute::Hook {
                origin: node("hook.bn128.definition.hook"),
                operation,
            },
        ]
    };
    let definition_argument = |key: &str, field: &str, sort| {
        ProductionItem::non_terminal(node(key), ProductionFieldId::new(field).unwrap(), sort)
    };
    assert!(
        ProductionSentence::new(
            node("hook.bn128.definition.valid.production"),
            symbol(
                "production.bn128-valid",
                "Bn128Valid",
                SymbolKind::Production,
            ),
            DefinitionSortRef::Builtin(krs_ir::BuiltinSort::Bool),
            vec![definition_argument(
                "hook.bn128.definition.valid.point",
                "point",
                DefinitionSortRef::declared(point.clone()),
            )],
            definition_attributes(HookOperation::KryptoBn128Valid),
        )
        .is_ok()
    );
    assert!(
        ProductionSentence::new(
            node("hook.bn128.definition.add.production"),
            symbol("production.bn128-add", "Bn128Add", SymbolKind::Production,),
            DefinitionSortRef::declared(point.clone()),
            vec![
                definition_argument(
                    "hook.bn128.definition.add.left",
                    "left",
                    DefinitionSortRef::declared(point.clone()),
                ),
                definition_argument(
                    "hook.bn128.definition.add.right",
                    "right",
                    DefinitionSortRef::declared(point.clone()),
                ),
            ],
            definition_attributes(HookOperation::KryptoBn128Add),
        )
        .is_ok()
    );
    assert!(
        ProductionSentence::new(
            node("hook.bn128.definition.mul.production"),
            symbol("production.bn128-mul", "Bn128Mul", SymbolKind::Production,),
            DefinitionSortRef::declared(point.clone()),
            vec![
                definition_argument(
                    "hook.bn128.definition.mul.point",
                    "point",
                    DefinitionSortRef::declared(point.clone()),
                ),
                definition_argument(
                    "hook.bn128.definition.mul.scalar",
                    "scalar",
                    DefinitionSortRef::Builtin(krs_ir::BuiltinSort::Int),
                ),
            ],
            definition_attributes(HookOperation::KryptoBn128Mul),
        )
        .is_ok()
    );
    assert_eq!(
        ProductionSentence::new(
            node("hook.bn128.definition.bad-add.production"),
            symbol(
                "production.bad-bn128-add",
                "BadBn128Add",
                SymbolKind::Production,
            ),
            DefinitionSortRef::declared(point.clone()),
            vec![
                definition_argument(
                    "hook.bn128.definition.bad-add.left",
                    "left",
                    DefinitionSortRef::declared(point.clone()),
                ),
                definition_argument(
                    "hook.bn128.definition.bad-add.right",
                    "right",
                    DefinitionSortRef::declared(other.clone()),
                ),
            ],
            definition_attributes(HookOperation::KryptoBn128Add),
        ),
        Err(DefinitionValidationError::InvalidHookSignature(
            HookOperation::KryptoBn128Add,
        ))
    );
    assert_eq!(
        ProductionSentence::new(
            node("hook.bn128.definition.bad-mul.production"),
            symbol(
                "production.bad-bn128-mul",
                "BadBn128Mul",
                SymbolKind::Production,
            ),
            DefinitionSortRef::declared(point.clone()),
            vec![
                definition_argument(
                    "hook.bn128.definition.bad-mul.point",
                    "point",
                    DefinitionSortRef::declared(point),
                ),
                definition_argument(
                    "hook.bn128.definition.bad-mul.scalar",
                    "scalar",
                    DefinitionSortRef::declared(other),
                ),
            ],
            definition_attributes(HookOperation::KryptoBn128Mul),
        ),
        Err(DefinitionValidationError::InvalidHookSignature(
            HookOperation::KryptoBn128Mul,
        ))
    );
}

#[allow(clippy::too_many_lines)] // Builds a complete Definition IR fixture around one BN128 hook.
fn bn128_definition(
    point_sort_name: &str,
    point_constructors: &[(&str, usize)],
    hook: HookOperation,
    g2_arity: Option<usize>,
) -> Result<DefinitionIr, DefinitionValidationError> {
    let point_sort = SymbolId::new("sort.point").unwrap();
    let mut sentences = vec![DefinitionSentence::SyntaxSort(
        SyntaxSortSentence::new(
            node("bn128.sort.point"),
            SymbolIdentity::new(point_sort.clone(), point_sort_name, SymbolKind::Sort).unwrap(),
        )
        .unwrap(),
    )];
    for &(name, arity) in point_constructors {
        let items = (0..arity)
            .map(|index| {
                ProductionItem::non_terminal(
                    node(&format!("bn128.constructor.{name}.{index}")),
                    ProductionFieldId::new(format!("coord{index}")).unwrap(),
                    DefinitionSortRef::int(),
                )
            })
            .collect();
        sentences.push(DefinitionSentence::Production(
            ProductionSentence::new(
                node(&format!("bn128.constructor.{name}")),
                symbol(&format!("production.{name}"), name, SymbolKind::Production),
                DefinitionSortRef::declared(point_sort.clone()),
                items,
                vec![],
            )
            .unwrap(),
        ));
    }
    if let Some(arity) = g2_arity {
        let g2_sort = SymbolId::new("sort.g2-point").unwrap();
        sentences.push(DefinitionSentence::SyntaxSort(
            SyntaxSortSentence::new(
                node("bn128.sort.g2-point"),
                symbol("sort.g2-point", "G2Point", SymbolKind::Sort),
            )
            .unwrap(),
        ));
        sentences.push(DefinitionSentence::Production(
            ProductionSentence::new(
                node("bn128.constructor.g2"),
                symbol("production.g2", "G2", SymbolKind::Production),
                DefinitionSortRef::declared(g2_sort),
                (0..arity)
                    .map(|index| {
                        ProductionItem::non_terminal(
                            node(&format!("bn128.constructor.g2.{index}")),
                            ProductionFieldId::new(format!("g2coord{index}")).unwrap(),
                            DefinitionSortRef::int(),
                        )
                    })
                    .collect(),
                vec![],
            )
            .unwrap(),
        ));
    }
    let point = DefinitionSortRef::declared(point_sort);
    let (result_sort, arguments) = match hook {
        HookOperation::KryptoBn128Valid | HookOperation::KryptoBn128G2Valid => {
            (DefinitionSortRef::bool(), vec![point])
        }
        HookOperation::KryptoBn128Add => (point.clone(), vec![point.clone(), point]),
        HookOperation::KryptoBn128Mul => (point.clone(), vec![point, DefinitionSortRef::int()]),
        HookOperation::KryptoBn128Ate => (
            DefinitionSortRef::bool(),
            vec![DefinitionSortRef::list(), DefinitionSortRef::list()],
        ),
        _ => panic!("the fixture requires a BN128 hook"),
    };
    sentences.push(DefinitionSentence::Production(
        ProductionSentence::new(
            node("bn128.hook.production"),
            symbol("production.hook", "Bn128Hook", SymbolKind::Production),
            result_sort,
            arguments
                .into_iter()
                .enumerate()
                .map(|(index, sort)| {
                    ProductionItem::non_terminal(
                        node(&format!("bn128.hook.argument.{index}")),
                        ProductionFieldId::new(format!("argument{index}")).unwrap(),
                        sort,
                    )
                })
                .collect(),
            vec![
                ProductionAttribute::Function {
                    origin: node("bn128.hook.function"),
                },
                ProductionAttribute::Total {
                    origin: node("bn128.hook.total"),
                },
                ProductionAttribute::Hook {
                    origin: node("bn128.hook.attribute"),
                    operation: hook,
                },
            ],
        )
        .unwrap(),
    ));
    let cell = SymbolId::new("cell.main").unwrap();
    sentences.push(DefinitionSentence::Configuration(
        FixedConfiguration::new(
            node("bn128.configuration"),
            SemanticId::new("configuration.bn128").unwrap(),
            ConfigurationRoot::GeneratedTop,
            vec![
                FixedCell::leaf(
                    node("bn128.cell.main"),
                    cell.clone(),
                    "main",
                    vec![],
                    DefinitionSortRef::int(),
                )
                .unwrap(),
            ],
            node("bn128.initializer"),
            SemanticId::new("initializer.bn128").unwrap(),
            vec![],
            vec![FixedInitializerCell::term(
                node("bn128.initializer.main"),
                cell,
                DefinitionTerm::token(node("bn128.zero"), DefinitionSortRef::int(), "0").unwrap(),
            )],
        )
        .unwrap(),
    ));
    let module = ModuleId::new("BN128").unwrap();
    DefinitionIr::new(
        module.clone(),
        vec![DefinitionModule::new(
            node("bn128.module"),
            module,
            vec![],
            vec![],
            sentences,
        )],
    )
}

#[test]
fn bn128_hooks_require_a_unique_point_constructor_with_the_expected_sort_and_signature() {
    let hook = HookOperation::KryptoBn128Valid;
    let definition = bn128_definition("G1Point", &[("Point", 2)], hook, None).unwrap();
    assert_canonical_contract(&definition);
    for (sort, constructors, count) in [
        ("OtherPoint", vec![("Point", 2)], 1),
        ("G1Point", vec![], 0),
        ("G1Point", vec![("Point", 2), ("OtherPoint", 2)], 2),
        ("G1Point", vec![("Point", 3)], 0),
    ] {
        assert_eq!(
            bn128_definition(sort, &constructors, hook, None),
            Err(DefinitionValidationError::InvalidBn128PointConstructor {
                hook,
                sort: sort.to_owned(),
                expected_signature: krs_ir::Bn128PointSignature::G1,
                matching_constructors: count,
            })
        );
    }
    assert_eq!(
        bn128_definition(
            "G1Point",
            &[("Point", 2)],
            HookOperation::KryptoBn128Ate,
            None,
        ),
        Err(DefinitionValidationError::InvalidBn128PointConstructor {
            hook: HookOperation::KryptoBn128Ate,
            sort: "G2Point".to_owned(),
            expected_signature: krs_ir::Bn128PointSignature::G2,
            matching_constructors: 0,
        })
    );
    let definition = bn128_definition(
        "G1Point",
        &[("Point", 2)],
        HookOperation::KryptoBn128Ate,
        Some(4),
    )
    .unwrap();
    assert_canonical_contract(&definition);
}

#[test]
fn bn128_add_and_mul_require_g1_constructors_for_the_result_sort() {
    for (hook, expected_message) in [
        (
            HookOperation::KryptoBn128Add,
            "hook KRYPTO.bn128add requires a unique G1Point(Int, Int) constructor; sort OtherPoint has 1 matching constructors",
        ),
        (
            HookOperation::KryptoBn128Mul,
            "hook KRYPTO.bn128mul requires a unique G1Point(Int, Int) constructor; sort OtherPoint has 1 matching constructors",
        ),
    ] {
        let definition = bn128_definition("G1Point", &[("Point", 2)], hook, None).unwrap();
        assert_canonical_contract(&definition);
        let error = bn128_definition("OtherPoint", &[("Point", 2)], hook, None).unwrap_err();
        assert_eq!(
            error,
            DefinitionValidationError::InvalidBn128PointConstructor {
                hook,
                sort: "OtherPoint".to_owned(),
                expected_signature: krs_ir::Bn128PointSignature::G1,
                matching_constructors: 1,
            }
        );
        assert_eq!(error.to_string(), expected_message);
        assert_eq!(
            bn128_definition("G1Point", &[("Point", 3)], hook, None),
            Err(DefinitionValidationError::InvalidBn128PointConstructor {
                hook,
                sort: "G1Point".to_owned(),
                expected_signature: krs_ir::Bn128PointSignature::G1,
                matching_constructors: 0,
            })
        );
    }
}

#[test]
fn bn128_g2_valid_requires_g2_constructors_for_the_first_argument_sort() {
    let hook = HookOperation::KryptoBn128G2Valid;
    let definition = bn128_definition("G2Point", &[("Point", 4)], hook, None).unwrap();
    assert_canonical_contract(&definition);
    for (sort, constructors, count, expected_message) in [
        (
            "OtherPoint",
            vec![("Point", 4)],
            1,
            "hook KRYPTO.bn128g2valid requires a unique G2Point(Int, Int, Int, Int) constructor; sort OtherPoint has 1 matching constructors",
        ),
        (
            "G2Point",
            vec![("Point", 2)],
            0,
            "hook KRYPTO.bn128g2valid requires a unique G2Point(Int, Int, Int, Int) constructor; sort G2Point has 0 matching constructors",
        ),
        (
            "G2Point",
            vec![("Point", 4), ("OtherPoint", 4)],
            2,
            "hook KRYPTO.bn128g2valid requires a unique G2Point(Int, Int, Int, Int) constructor; sort G2Point has 2 matching constructors",
        ),
    ] {
        let error = bn128_definition(sort, &constructors, hook, None).unwrap_err();
        assert_eq!(
            error,
            DefinitionValidationError::InvalidBn128PointConstructor {
                hook,
                sort: sort.to_owned(),
                expected_signature: krs_ir::Bn128PointSignature::G2,
                matching_constructors: count,
            }
        );
        assert_eq!(error.to_string(), expected_message);
    }
}

#[test]
fn bn128_pairing_checks_named_g1_before_named_g2() {
    let hook = HookOperation::KryptoBn128Ate;
    for (sort, constructors, g2_arity, expected_signature, expected_sort, expected_message) in [
        (
            "OtherPoint",
            vec![("Point", 2)],
            None,
            krs_ir::Bn128PointSignature::G1,
            "G1Point",
            "hook KRYPTO.bn128ate requires a unique G1Point(Int, Int) constructor; sort G1Point has 0 matching constructors",
        ),
        (
            "G1Point",
            vec![("Point", 3)],
            Some(2),
            krs_ir::Bn128PointSignature::G1,
            "G1Point",
            "hook KRYPTO.bn128ate requires a unique G1Point(Int, Int) constructor; sort G1Point has 0 matching constructors",
        ),
        (
            "G1Point",
            vec![("Point", 2)],
            Some(2),
            krs_ir::Bn128PointSignature::G2,
            "G2Point",
            "hook KRYPTO.bn128ate requires a unique G2Point(Int, Int, Int, Int) constructor; sort G2Point has 0 matching constructors",
        ),
    ] {
        let error = bn128_definition(sort, &constructors, hook, g2_arity).unwrap_err();
        assert_eq!(
            error,
            DefinitionValidationError::InvalidBn128PointConstructor {
                hook,
                sort: expected_sort.to_owned(),
                expected_signature,
                matching_constructors: 0,
            }
        );
        assert_eq!(error.to_string(), expected_message);
    }
}

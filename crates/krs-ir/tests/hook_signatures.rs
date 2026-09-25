//! Typed hook signatures in semantic and Definition IR.

use krs_ir::{
    ConfigurationRoot, DefinitionIr, DefinitionModule, DefinitionSentence, DefinitionSortRef,
    DefinitionTerm, DefinitionValidationError, FixedCell, FixedConfiguration, FixedInitializerCell,
    HookOperation, ItemKind, ModuleId, NodeOrigin, OriginStack, PackageId, ProductionAttribute,
    ProductionFieldId, ProductionItem, ProductionSentence, SemanticId, SemanticProduction,
    SemanticProductionItem, SemanticSortRef, SemanticValidationError, Sha256Digest, SourceFileId,
    SourceMapKey, SourceRange, StableItemId, SymbolId, SymbolIdentity, SymbolKind,
    SyntaxSortSentence,
};

fn package() -> PackageId {
    PackageId::new("ORG-EXAMPLE-SMOKE", "smoke-semantics", "0.1.0", "workspace").unwrap()
}

fn item(module: &str, name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(package(), [module], name, kind, "").unwrap()
}

fn node(key: &str) -> NodeOrigin {
    let file = SourceFileId::new(
        package(),
        "src/lib.rs",
        Sha256Digest::new("0123456789abcdef".repeat(4)).unwrap(),
    )
    .unwrap();
    NodeOrigin::new(
        SourceMapKey::new(key).unwrap(),
        OriginStack::authored(SourceRange::new(file, 0, 3).unwrap()),
    )
}

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
    let (result_sort, arguments) = if hook == HookOperation::KryptoBn128Ate {
        (
            DefinitionSortRef::bool(),
            vec![DefinitionSortRef::list(), DefinitionSortRef::list()],
        )
    } else {
        (
            DefinitionSortRef::bool(),
            vec![DefinitionSortRef::declared(point_sort)],
        )
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
    assert!(bn128_definition("G1Point", &[("Point", 2)], hook, None).is_ok());
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
                expected_signature: "G1Point(Int, Int)",
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
            expected_signature: "G2Point(Int, Int, Int, Int)",
            matching_constructors: 0,
        })
    );
    assert!(
        bn128_definition(
            "G1Point",
            &[("Point", 2)],
            HookOperation::KryptoBn128Ate,
            Some(4),
        )
        .is_ok()
    );
}

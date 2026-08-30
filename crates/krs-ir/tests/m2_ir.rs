//! M2 target-neutral semantic and Definition IR contracts.

use krs_ir::{
    ApplicationRef, CellDeclaration, ConfigurationSentence, DefinitionIr, DefinitionModule,
    DefinitionSentence, DefinitionSortRef, DefinitionTerm, DefinitionValidationError,
    HookOperation, InitializerDeclaration, IrSchemaVersion, ItemKind, LabelId, LabelIdentity,
    ModuleId, NodeOrigin, OriginStack, PackageId, ProductionAttribute, ProductionFieldId,
    ProductionItem, ProductionSentence, RuleSentence, SemanticCell, SemanticConfiguration,
    SemanticId, SemanticInitializer, SemanticModule, SemanticProduction, SemanticProductionItem,
    SemanticRule, SemanticSort, SemanticSortRef, SemanticSubsort, SemanticTerm, SemanticTheory,
    SemanticValidationError, SentenceKind, Sha256Digest, SourceFileId, SourceMapKey, SourceRange,
    StableItemId, SymbolId, SymbolIdentity, SymbolKind, SyntaxSortSentence,
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

#[allow(clippy::too_many_lines, clippy::disallowed_names)] // Stable golden fixture vocabulary.
fn semantic_theory(reverse_sets: bool, bar_reference: Option<StableItemId>) -> SemanticTheory {
    let k_item = item("syntax", "KItem", ItemKind::Sort);
    let k_result = item("syntax", "KResult", ItemKind::Sort);
    let value = item("syntax", "Value", ItemKind::Sort);
    let foo = item("syntax", "Foo", ItemKind::Constructor);
    let bar = item("syntax", "Bar", ItemKind::Constructor);
    let rule_id = item("rules", "foo_to_bar", ItemKind::Rule);

    let mut sorts = vec![
        SemanticSort::new(node("sem.sort.kitem"), k_item.clone()),
        SemanticSort::new(node("sem.sort.kresult"), k_result.clone()),
        SemanticSort::new(node("sem.sort.value"), value.clone()),
    ];
    let mut subsorts = vec![
        SemanticSubsort::new(
            node("sem.subsort.kresult-kitem"),
            SemanticSortRef::declared(k_result.clone()),
            SemanticSortRef::declared(k_item),
        ),
        SemanticSubsort::new(
            node("sem.subsort.value-kresult"),
            SemanticSortRef::declared(value.clone()),
            SemanticSortRef::declared(k_result),
        ),
    ];
    let mut productions = vec![
        SemanticProduction::new(
            node("sem.production.foo"),
            foo.clone(),
            SemanticSortRef::declared(value.clone()),
            vec![
                SemanticProductionItem::terminal(node("sem.production.foo.terminal"), "foo")
                    .unwrap(),
            ],
            vec![],
        )
        .unwrap(),
        SemanticProduction::new(
            node("sem.production.bar"),
            bar.clone(),
            SemanticSortRef::declared(value.clone()),
            vec![
                SemanticProductionItem::terminal(node("sem.production.bar.terminal"), "bar")
                    .unwrap(),
            ],
            vec![],
        )
        .unwrap(),
    ];
    if reverse_sets {
        sorts.reverse();
        subsorts.reverse();
        productions.reverse();
    }

    let syntax_id = ModuleId::new("SMOKE-SYNTAX").unwrap();
    let main_id = ModuleId::new("SMOKE").unwrap();
    let syntax = SemanticModule::new(
        node("sem.module.syntax"),
        syntax_id.clone(),
        vec![],
        sorts,
        subsorts,
        productions,
        vec![],
        vec![],
        None,
        vec![],
    );
    let initializer = SemanticInitializer::new(
        node("sem.initializer"),
        SemanticId::new("machine.init").unwrap(),
        vec![],
        SemanticTerm::application(
            node("sem.term.init.foo"),
            SemanticSortRef::declared(value.clone()),
            ApplicationRef::Declared(foo.clone()),
            vec![],
        ),
    );
    let configuration = SemanticConfiguration::new(
        node("sem.configuration"),
        SemanticId::new("machine").unwrap(),
        SemanticCell::new(
            node("sem.cell.k"),
            SemanticId::new("machine.k").unwrap(),
            "k",
            SemanticSortRef::declared(value.clone()),
        )
        .unwrap(),
        initializer,
    );
    let lhs = SemanticTerm::application(
        node("sem.term.rule.foo"),
        SemanticSortRef::declared(value.clone()),
        ApplicationRef::Declared(foo),
        vec![],
    );
    let rhs = SemanticTerm::application(
        node("sem.term.rule.bar"),
        SemanticSortRef::declared(value.clone()),
        ApplicationRef::Declared(bar_reference.unwrap_or(bar)),
        vec![],
    );
    let rewrite = SemanticTerm::rewrite(
        node("sem.term.rule.rewrite"),
        SemanticSortRef::declared(value),
        lhs,
        rhs,
    )
    .unwrap();
    let rule = SemanticRule::new(
        node("sem.rule.foo-to-bar"),
        rule_id,
        SentenceKind::Transition,
        vec![],
        rewrite,
    )
    .unwrap();
    let main = SemanticModule::new(
        node("sem.module.main"),
        main_id,
        vec![syntax_id],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        Some(configuration),
        vec![rule],
    );
    let modules = if reverse_sets {
        vec![main, syntax]
    } else {
        vec![syntax, main]
    };
    SemanticTheory::new(modules).unwrap()
}

fn symbol(id: &str, name: &str, kind: SymbolKind) -> SymbolIdentity {
    SymbolIdentity::new(SymbolId::new(id).unwrap(), name, kind).unwrap()
}

#[allow(clippy::too_many_lines, clippy::disallowed_names)] // Mirrors the semantic golden fixture.
fn definition_ir(reverse_sets: bool, bar_reference: Option<SymbolId>) -> DefinitionIr {
    let value = SymbolId::new("sort.value").unwrap();
    let foo = SymbolId::new("production.foo").unwrap();
    let bar = SymbolId::new("production.bar").unwrap();

    let mut syntax_sentences = vec![
        DefinitionSentence::SyntaxSort(
            SyntaxSortSentence::new(
                node("def.sort.kitem"),
                symbol("sort.kitem", "KItem", SymbolKind::Sort),
            )
            .unwrap(),
        ),
        DefinitionSentence::SyntaxSort(
            SyntaxSortSentence::new(
                node("def.sort.kresult"),
                symbol("sort.kresult", "KResult", SymbolKind::Sort),
            )
            .unwrap(),
        ),
        DefinitionSentence::SyntaxSort(
            SyntaxSortSentence::new(
                node("def.sort.value"),
                symbol("sort.value", "Value", SymbolKind::Sort),
            )
            .unwrap(),
        ),
        DefinitionSentence::Production(
            ProductionSentence::new(
                node("def.production.foo"),
                symbol("production.foo", "Lblfoo", SymbolKind::Production),
                DefinitionSortRef::declared(value.clone()),
                vec![ProductionItem::terminal(node("def.production.foo.terminal"), "foo").unwrap()],
                vec![],
            )
            .unwrap(),
        ),
        DefinitionSentence::Production(
            ProductionSentence::new(
                node("def.production.bar"),
                symbol("production.bar", "Lblbar", SymbolKind::Production),
                DefinitionSortRef::declared(value.clone()),
                vec![ProductionItem::terminal(node("def.production.bar.terminal"), "bar").unwrap()],
                vec![],
            )
            .unwrap(),
        ),
    ];
    if reverse_sets {
        syntax_sentences.reverse();
    }
    let syntax_id = ModuleId::new("SMOKE-SYNTAX").unwrap();
    let main_id = ModuleId::new("SMOKE").unwrap();
    let syntax = DefinitionModule::new(
        node("def.module.syntax"),
        syntax_id.clone(),
        vec![],
        vec![],
        syntax_sentences,
    );

    let init = InitializerDeclaration::new(
        node("def.initializer"),
        symbol(
            "initializer.machine",
            "initMachine",
            SymbolKind::Initializer,
        ),
        vec![],
        DefinitionTerm::application(
            node("def.term.init.foo"),
            DefinitionSortRef::declared(value.clone()),
            ApplicationRef::Declared(foo.clone()),
            vec![],
        ),
    )
    .unwrap();
    let cell = CellDeclaration::new(
        node("def.cell.k"),
        symbol("cell.k", "k", SymbolKind::Cell),
        DefinitionSortRef::declared(value.clone()),
    )
    .unwrap();
    let configuration = DefinitionSentence::Configuration(ConfigurationSentence::new(
        node("def.configuration"),
        cell,
        init,
    ));
    let lhs = DefinitionTerm::application(
        node("def.term.rule.foo"),
        DefinitionSortRef::declared(value.clone()),
        ApplicationRef::Declared(foo),
        vec![],
    );
    let rhs = DefinitionTerm::application(
        node("def.term.rule.bar"),
        DefinitionSortRef::declared(value.clone()),
        ApplicationRef::Declared(bar_reference.unwrap_or(bar)),
        vec![],
    );
    let rewrite = DefinitionTerm::rewrite(
        node("def.term.rule.rewrite"),
        DefinitionSortRef::declared(value),
        lhs,
        rhs,
    )
    .unwrap();
    let rule = DefinitionSentence::Rule(
        RuleSentence::new(
            node("def.rule.foo-to-bar"),
            LabelIdentity::new(
                LabelId::new("rule.foo-to-bar").unwrap(),
                "ORG-EXAMPLE-SMOKE.rules.foo-to-bar",
            )
            .unwrap(),
            SentenceKind::Transition,
            vec![],
            rewrite,
        )
        .unwrap(),
    );
    let main_sentences = if reverse_sets {
        vec![rule, configuration]
    } else {
        vec![configuration, rule]
    };
    let main = DefinitionModule::new(
        node("def.module.main"),
        main_id.clone(),
        vec![syntax_id],
        vec![],
        main_sentences,
    );
    let modules = if reverse_sets {
        vec![main, syntax]
    } else {
        vec![syntax, main]
    };
    DefinitionIr::new(main_id, modules).unwrap()
}

#[test]
fn semantic_foo_bar_matches_golden_and_set_reordering() {
    let normal = semantic_theory(false, None).to_canonical_json().unwrap();
    let reversed = semantic_theory(true, None).to_canonical_json().unwrap();
    assert_eq!(normal, reversed);
    assert_eq!(normal, include_str!("golden/semantic_foo_bar.json"));
}

#[test]
fn definition_foo_bar_matches_golden_and_set_reordering() {
    let normal = definition_ir(false, None).to_canonical_json().unwrap();
    let reversed = definition_ir(true, None).to_canonical_json().unwrap();
    assert_eq!(normal, reversed);
    assert_eq!(normal, include_str!("golden/definition_foo_bar.json"));
}

#[test]
fn schema_version_is_not_the_collector_protocol() {
    assert_eq!(
        semantic_theory(false, None).schema_version(),
        IrSchemaVersion::CURRENT
    );
    assert_eq!(
        definition_ir(false, None).schema_version(),
        IrSchemaVersion::CURRENT
    );
    assert_ne!(
        IrSchemaVersion::CURRENT.0,
        krs_ir::ProtocolVersion::CURRENT.0
    );
}

#[test]
fn empty_and_path_shaped_ids_are_rejected() {
    assert!(SourceMapKey::new(" ").is_err());
    assert!(ModuleId::new("/tmp/SMOKE").is_err());
    assert!(SymbolId::new("native/production/7").is_err());
    assert!(LabelId::new("").is_err());
}

#[test]
fn dangling_semantic_production_is_rejected() {
    let missing = item("syntax", "Missing", ItemKind::Constructor);
    let result = std::panic::catch_unwind(|| semantic_theory(false, Some(missing)));
    assert!(result.is_err());
}

#[test]
fn dangling_definition_symbol_is_rejected() {
    let missing = SymbolId::new("production.missing").unwrap();
    let result = std::panic::catch_unwind(|| definition_ir(false, Some(missing)));
    assert!(result.is_err());
}

#[test]
fn missing_origin_is_rejected_during_deserialization() {
    let mut json = serde_json::to_value(definition_ir(false, None)).unwrap();
    json["modules"][0]["origin"]["origin"] = serde_json::json!([]);
    assert!(serde_json::from_value::<DefinitionIr>(json).is_err());
}

#[test]
fn duplicate_node_key_is_rejected() {
    let mut json = serde_json::to_value(definition_ir(false, None)).unwrap();
    let duplicate = json["modules"][0]["origin"]["key"].clone();
    json["modules"][1]["origin"]["key"] = duplicate;
    assert!(serde_json::from_value::<DefinitionIr>(json).is_err());
}

#[test]
fn adapter_specific_fields_are_rejected() {
    let mut json = serde_json::to_value(definition_ir(false, None)).unwrap();
    let modules = json["modules"].as_array_mut().unwrap();
    let sentence = modules
        .iter_mut()
        .flat_map(|module| module["sentences"].as_array_mut().unwrap())
        .find(|sentence| sentence["sentence_kind"] == "production")
        .unwrap();
    sentence["sentence"]["k_rust_resolved_production_id"] = serde_json::json!(7);
    assert!(serde_json::from_value::<DefinitionIr>(json).is_err());
}

#[test]
fn prior_ir_schema_is_rejected() {
    let mut json = serde_json::to_value(definition_ir(false, None)).unwrap();
    json["schema_version"] = serde_json::json!(0);
    assert!(serde_json::from_value::<DefinitionIr>(json).is_err());
}

#[test]
fn print_goldens_for_review() {
    println!(
        "SEMANTIC\n{}",
        semantic_theory(false, None).to_canonical_json().unwrap()
    );
    println!(
        "DEFINITION\n{}",
        definition_ir(false, None).to_canonical_json().unwrap()
    );
}

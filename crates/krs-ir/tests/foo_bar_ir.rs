//! Target-neutral semantic and Definition IR contracts over the foo-bar theory.

use krs_ir::{
    ApplicationRef, ConfigurationRoot, DefinitionIr, DefinitionModule, DefinitionSentence,
    DefinitionSortRef, DefinitionTerm, FixedCell, FixedConfiguration, FixedInitializerCell,
    ItemKind, LabelId, LabelIdentity, ModuleId, NodeOrigin, OriginStack, PackageId, ProductionItem,
    ProductionSentence, RuleSentence, SchemaVersion, SemanticId, SemanticModule,
    SemanticProduction, SemanticProductionItem, SemanticRule, SemanticSort, SemanticSortRef,
    SemanticSubsort, SemanticTerm, SemanticTheory, SentenceKind, Sha256Digest, SourceFileId,
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
    let k_cell = SemanticId::new("machine.k").unwrap();
    let configuration = FixedConfiguration::new(
        node("sem.configuration"),
        SemanticId::new("machine").unwrap(),
        ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                node("sem.cell.k"),
                k_cell.clone(),
                "k",
                vec![],
                SemanticSortRef::declared(value.clone()),
            )
            .unwrap(),
        ],
        node("sem.initializer"),
        SemanticId::new("machine.init").unwrap(),
        vec![],
        vec![FixedInitializerCell::term(
            node("sem.initializer.k"),
            k_cell,
            SemanticTerm::application(
                node("sem.term.init.foo"),
                SemanticSortRef::declared(value.clone()),
                ApplicationRef::Declared(foo.clone()),
                vec![],
            ),
        )],
    )
    .unwrap();
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

    let k_cell = SymbolId::new("cell.k").unwrap();
    let configuration = DefinitionSentence::Configuration(
        FixedConfiguration::new(
            node("def.configuration"),
            SemanticId::new("machine").unwrap(),
            ConfigurationRoot::GeneratedTop,
            vec![
                FixedCell::leaf(
                    node("def.cell.k"),
                    k_cell.clone(),
                    "k",
                    vec![],
                    DefinitionSortRef::declared(value.clone()),
                )
                .unwrap(),
            ],
            node("def.initializer"),
            SemanticId::new("machine.init").unwrap(),
            vec![],
            vec![FixedInitializerCell::term(
                node("def.initializer.k"),
                k_cell,
                DefinitionTerm::application(
                    node("def.term.init.foo"),
                    DefinitionSortRef::declared(value.clone()),
                    ApplicationRef::Declared(foo.clone()),
                    vec![],
                ),
            )],
        )
        .unwrap(),
    );
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
fn semantic_and_definition_ir_carry_the_one_schema_version() {
    assert_eq!(
        semantic_theory(false, None).schema_version(),
        SchemaVersion::CURRENT
    );
    assert_eq!(
        definition_ir(false, None).schema_version(),
        SchemaVersion::CURRENT
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

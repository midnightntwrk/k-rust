//! M2 target-neutral semantic and Definition IR contracts.

use krs_ir::{
    CellDeclaration, ConfigurationSentence, DefinitionIr, DefinitionModule, DefinitionSentence,
    DefinitionTerm, InitializerDeclaration, IrSchemaVersion, ItemKind, LabelId, LabelIdentity,
    ModuleId, NodeOrigin, OriginStack, PackageId, ProductionItem, ProductionSentence, RuleSentence,
    SemanticCell, SemanticConfiguration, SemanticId, SemanticInitializer, SemanticModule,
    SemanticProduction, SemanticRule, SemanticSort, SemanticTerm, SemanticTheory, SentenceKind,
    Sha256Digest, SourceFileId, SourceMapKey, SourceRange, StableItemId, SymbolId, SymbolIdentity,
    SymbolKind, SyntaxSortSentence,
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

fn semantic_theory(reverse_sets: bool, bar_reference: Option<StableItemId>) -> SemanticTheory {
    let k_item = item("syntax", "KItem", ItemKind::Sort);
    let k_result = item("syntax", "KResult", ItemKind::Sort);
    let value = item("syntax", "Value", ItemKind::Sort);
    let foo = item("syntax", "Foo", ItemKind::Constructor);
    let bar = item("syntax", "Bar", ItemKind::Constructor);
    let rule_id = item("rules", "foo_to_bar", ItemKind::Rule);

    let mut sorts = vec![
        SemanticSort::new(node("sem.sort.kitem"), k_item, vec![]),
        SemanticSort::new(
            node("sem.sort.kresult"),
            k_result.clone(),
            vec![item("syntax", "KItem", ItemKind::Sort)],
        ),
        SemanticSort::new(
            node("sem.sort.value"),
            value.clone(),
            vec![k_result],
        ),
    ];
    let mut productions = vec![
        SemanticProduction::new(
            node("sem.production.foo"),
            foo.clone(),
            value.clone(),
            vec![],
            "foo",
        )
        .unwrap(),
        SemanticProduction::new(
            node("sem.production.bar"),
            bar.clone(),
            value.clone(),
            vec![],
            "bar",
        )
        .unwrap(),
    ];
    if reverse_sets {
        sorts.reverse();
        productions.reverse();
    }

    let syntax_id = ModuleId::new("SMOKE-SYNTAX").unwrap();
    let main_id = ModuleId::new("SMOKE").unwrap();
    let syntax = SemanticModule::new(
        node("sem.module.syntax"),
        syntax_id.clone(),
        vec![],
        sorts,
        productions,
        None,
        vec![],
    );
    let initializer = SemanticInitializer::new(
        node("sem.initializer"),
        SemanticId::new("machine.init").unwrap(),
        vec![],
        SemanticTerm::application(
            node("sem.term.init.foo"),
            value.clone(),
            foo.clone(),
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
            value.clone(),
        )
        .unwrap(),
        initializer,
    );
    let lhs = SemanticTerm::application(
        node("sem.term.rule.foo"),
        value.clone(),
        foo,
        vec![],
    );
    let rhs = SemanticTerm::application(
        node("sem.term.rule.bar"),
        value.clone(),
        bar_reference.unwrap_or(bar),
        vec![],
    );
    let rewrite = SemanticTerm::rewrite(node("sem.term.rule.rewrite"), value, lhs, rhs).unwrap();
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
        Some(configuration),
        vec![rule],
    );
    let modules = if reverse_sets { vec![main, syntax] } else { vec![syntax, main] };
    SemanticTheory::new(modules).unwrap()
}

fn symbol(id: &str, name: &str, kind: SymbolKind) -> SymbolIdentity {
    SymbolIdentity::new(SymbolId::new(id).unwrap(), name, kind).unwrap()
}

fn definition_ir(reverse_sets: bool, bar_reference: Option<SymbolId>) -> DefinitionIr {
    let k_item = SymbolId::new("sort.kitem").unwrap();
    let k_result = SymbolId::new("sort.kresult").unwrap();
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
                value.clone(),
                vec![ProductionItem::terminal("foo").unwrap()],
            )
            .unwrap(),
        ),
        DefinitionSentence::Production(
            ProductionSentence::new(
                node("def.production.bar"),
                symbol("production.bar", "Lblbar", SymbolKind::Production),
                value.clone(),
                vec![ProductionItem::terminal("bar").unwrap()],
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
        syntax_sentences,
    );

    let init = InitializerDeclaration::new(
        node("def.initializer"),
        symbol("initializer.machine", "initMachine", SymbolKind::Initializer),
        vec![],
        DefinitionTerm::application(
            node("def.term.init.foo"),
            value.clone(),
            foo.clone(),
            vec![],
        ),
    )
    .unwrap();
    let cell = CellDeclaration::new(
        node("def.cell.k"),
        symbol("cell.k", "k", SymbolKind::Cell),
        value.clone(),
    )
    .unwrap();
    let configuration = DefinitionSentence::Configuration(ConfigurationSentence::new(
        node("def.configuration"),
        cell,
        init,
    ));
    let lhs = DefinitionTerm::application(
        node("def.term.rule.foo"),
        value.clone(),
        foo,
        vec![],
    );
    let rhs = DefinitionTerm::application(
        node("def.term.rule.bar"),
        value.clone(),
        bar_reference.unwrap_or(bar),
        vec![],
    );
    let rewrite = DefinitionTerm::rewrite(node("def.term.rule.rewrite"), value, lhs, rhs).unwrap();
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
        main_sentences,
    );
    let modules = if reverse_sets { vec![main, syntax] } else { vec![syntax, main] };
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
    assert_eq!(semantic_theory(false, None).schema_version(), IrSchemaVersion::CURRENT);
    assert_eq!(definition_ir(false, None).schema_version(), IrSchemaVersion::CURRENT);
    assert_ne!(IrSchemaVersion::CURRENT.0, krs_ir::ProtocolVersion::CURRENT.0);
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
    println!("SEMANTIC\n{}", semantic_theory(false, None).to_canonical_json().unwrap());
    println!("DEFINITION\n{}", definition_ir(false, None).to_canonical_json().unwrap());
}

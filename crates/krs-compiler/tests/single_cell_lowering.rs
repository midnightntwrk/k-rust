//! One-cell fixed configuration lowering on the current classified IR.

use krs_compiler::{LoweringError, emit_k, lower_semantic_theory};
use krs_ir::testing;
use krs_ir::{
    ApplicationRef, ConfigurationRoot, DefinitionSentence, FixedCell, FixedConfiguration,
    FixedInitializerCell, ItemKind, ModuleId, NodeOrigin, OriginFrame, PackageId, RangedOriginKind,
    SemanticId, SemanticModule, SemanticProduction, SemanticProductionItem, SemanticRule,
    SemanticSort, SemanticSortRef, SemanticSubsort, SemanticTerm, SemanticTheory, SentenceKind,
    StableItemId, TransformationOriginKind,
};

fn package() -> PackageId {
    testing::package("KRS-FOO-BAR", "foo-bar-semantics")
}

fn item(module: &str, name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), module, name, kind)
}

fn origin(key: &str) -> NodeOrigin {
    origin_with_label(key, None)
}

fn origin_with_label(key: &str, label: Option<&str>) -> NodeOrigin {
    let mut stack = testing::authored_in(package(), "src/lib.rs", testing::digest(), 0, 3);
    stack.push(OriginFrame::Transformation {
        kind: TransformationOriginKind::SemanticIr,
        item: None,
        label: label.map(str::to_owned).or_else(|| Some(key.to_owned())),
    });
    NodeOrigin::new(krs_ir::SourceMapKey::new(key).unwrap(), stack)
}

#[allow(clippy::too_many_lines)]
fn theory(reverse: bool) -> SemanticTheory {
    let k_item = item("syntax", "KItem", ItemKind::Sort);
    let k_result = item("syntax", "KResult", ItemKind::Sort);
    let object = item("syntax", "Obj", ItemKind::Sort);
    let foo_production = item("syntax", "Foo", ItemKind::Constructor);
    let bar = item("syntax", "Bar", ItemKind::Constructor);
    let rule = item("rules", "foo_to_bar", ItemKind::Rule);
    let mut sorts = vec![
        SemanticSort::new(origin("sem.sort.kitem"), k_item.clone()),
        SemanticSort::new(origin("sem.sort.kresult"), k_result.clone()),
        SemanticSort::new(origin("sem.sort.object"), object.clone()),
    ];
    let subsorts = vec![
        SemanticSubsort::new(
            origin("sem.subsort.kresult-kitem"),
            SemanticSortRef::Declared(k_result.clone()),
            SemanticSortRef::Declared(k_item.clone()),
        ),
        SemanticSubsort::new(
            origin("sem.subsort.object-kresult"),
            SemanticSortRef::Declared(object.clone()),
            SemanticSortRef::Declared(k_result),
        ),
    ];
    let mut productions = vec![
        SemanticProduction::new(
            origin("sem.production.foo"),
            foo_production.clone(),
            SemanticSortRef::Declared(object.clone()),
            vec![
                SemanticProductionItem::terminal(origin("sem.production.foo.item"), "foo").unwrap(),
            ],
            vec![],
        )
        .unwrap(),
        SemanticProduction::new(
            origin("sem.production.bar"),
            bar.clone(),
            SemanticSortRef::Declared(object.clone()),
            vec![
                SemanticProductionItem::terminal(origin("sem.production.bar.item"), "bar").unwrap(),
            ],
            vec![],
        )
        .unwrap(),
    ];
    if reverse {
        sorts.reverse();
        productions.reverse();
    }
    let k_cell = SemanticId::new("machine.k").unwrap();
    let configuration = FixedConfiguration::new(
        origin("sem.configuration"),
        SemanticId::new("machine").unwrap(),
        ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                origin("sem.cell.k"),
                k_cell.clone(),
                "k",
                vec![],
                SemanticSortRef::k_sequence(),
            )
            .unwrap(),
        ],
        origin("sem.initializer"),
        SemanticId::new("machine.init").unwrap(),
        vec![],
        vec![FixedInitializerCell::term(
            origin("sem.initializer.k"),
            k_cell,
            SemanticTerm::k_sequence(
                origin("sem.term.init.sequence"),
                SemanticSortRef::Declared(k_item),
                vec![SemanticTerm::application(
                    origin("sem.term.init.foo"),
                    SemanticSortRef::Declared(object.clone()),
                    ApplicationRef::Declared(foo_production.clone()),
                    vec![],
                )],
            ),
        )],
    )
    .unwrap();
    let rewrite = SemanticTerm::rewrite(
        origin("sem.term.rule.rewrite"),
        SemanticSortRef::Declared(object.clone()),
        SemanticTerm::application(
            origin("sem.term.rule.foo"),
            SemanticSortRef::Declared(object.clone()),
            ApplicationRef::Declared(foo_production),
            vec![],
        ),
        SemanticTerm::application(
            origin("sem.term.rule.bar"),
            SemanticSortRef::Declared(object),
            ApplicationRef::Declared(bar),
            vec![],
        ),
    )
    .unwrap();
    let rule = SemanticRule::new(
        origin("sem.rule.foo-to-bar"),
        rule,
        SentenceKind::Transition,
        vec![],
        rewrite,
    )
    .unwrap();
    SemanticTheory::new(vec![SemanticModule::new(
        origin("sem.module.main"),
        ModuleId::new("KRS-FOO-BAR").unwrap(),
        vec![],
        sorts,
        subsorts,
        productions,
        vec![],
        vec![],
        Some(configuration),
        vec![rule],
    )])
    .unwrap()
}

#[test]
fn exact_source_snapshot_and_reordering_are_byte_identical() {
    let normal = lower_semantic_theory(&theory(false)).unwrap();
    let reordered = lower_semantic_theory(&theory(true)).unwrap();
    assert_eq!(
        normal.definition().to_canonical_json().unwrap(),
        reordered.definition().to_canonical_json().unwrap()
    );
    assert_eq!(
        normal.symbol_map().to_canonical_json().unwrap(),
        reordered.symbol_map().to_canonical_json().unwrap()
    );
    assert_eq!(
        normal.source_map().to_canonical_json().unwrap(),
        reordered.source_map().to_canonical_json().unwrap()
    );
    let emitted = emit_k(&normal).unwrap();
    let reemitted = emit_k(&reordered).unwrap();
    assert_eq!(emitted, reemitted);
    expect_test::expect![[r#"module KRS-FOO-BAR
  syntax KItem
  syntax KResult
  syntax Obj

  syntax Obj ::= "bar" [symbol(bar)]
  syntax Obj ::= "foo" [symbol(foo)]

  syntax KItem ::= KResult
  syntax KResult ::= Obj

  configuration
    <k> foo </k>


  rule foo => bar [label(krsRule_7ff2bcc3f880afc8861cfcfe)]
endmodule
"#]]
    .assert_eq(emitted.source());
}

#[test]
fn lowering_appends_definition_origins_and_source_ranges_are_honest() {
    let lowered = lower_semantic_theory(&theory(false)).unwrap();
    for entry in lowered.source_map().entries() {
        assert!(matches!(
            entry.origin().frames().last(),
            Some(OriginFrame::Transformation {
                kind: TransformationOriginKind::DefinitionIr,
                ..
            })
        ));
        assert!(matches!(
            entry.origin().frames().first(),
            Some(OriginFrame::Ranged {
                kind: RangedOriginKind::Authored,
                ..
            })
        ));
        assert!(entry.generated().is_none());
    }
    let emitted = emit_k(&lowered).unwrap();
    assert!(emitted.source_map().entries().iter().all(|entry| {
        entry.generated().is_some() || entry.node_kind() == krs_compiler::SourceMapNodeKind::Term
    }));
    assert!(
        emitted
            .source_map()
            .to_canonical_json()
            .unwrap()
            .contains("\"artifact\": \"definition.k\"")
    );
}

#[test]
fn one_cell_configuration_and_initializer_remain_structural() {
    let lowered = lower_semantic_theory(&theory(false)).unwrap();
    let configuration = lowered
        .definition()
        .modules()
        .iter()
        .flat_map(krs_ir::DefinitionModule::sentences)
        .find_map(|sentence| match sentence {
            DefinitionSentence::Configuration(value) => Some(value),
            _ => None,
        })
        .unwrap();
    let [cell] = configuration.cells() else {
        panic!("the configuration declares exactly one cell");
    };
    assert_eq!(cell.name(), "k");
    let [initializer] = configuration.initializer() else {
        panic!("the initializer fills exactly one cell");
    };
    assert!(matches!(
        initializer.content(),
        krs_ir::FixedInitializerContent::Term { term }
            if matches!(term.kind(), krs_ir::DefinitionTermKind::KSequence { items, .. } if items.len() == 1)
    ));
}

#[test]
fn name_collisions_are_rejected_before_definition_construction() {
    let mut json = serde_json::to_value(theory(false)).unwrap();
    let module = &mut json["modules"][0];
    let duplicate = module["productions"][0].clone();
    let mut second = duplicate;
    second["id"]["module_path"] = serde_json::json!(["extension"]);
    second["origin"]["key"] = serde_json::json!("sem.production.colliding-foo");
    second["items"][0]["origin"]["key"] = serde_json::json!("sem.production.colliding-foo.item");
    module["productions"].as_array_mut().unwrap().push(second);
    let theory: SemanticTheory = serde_json::from_value(json).unwrap();
    let expected_origin = theory.modules()[0]
        .productions()
        .last()
        .unwrap()
        .origin()
        .origin();
    assert!(matches!(
        lower_semantic_theory(&theory),
        Err(LoweringError::NameCollision {
            namespace: "emitted symbol",
            value,
            second_origin,
            ..
        }) if value == "foo" && &second_origin == expected_origin
    ));
}

#[test]
fn stale_template_shaped_production_is_rejected_by_schema_nine() {
    let mut json = serde_json::to_value(theory(false)).unwrap();
    let module = &mut json["modules"][0];
    let production = module["productions"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|production| production["id"]["item_name"] == "Foo")
        .unwrap();
    production["argument_sorts"] = serde_json::json!([]);
    production["syntax"] = serde_json::json!("box");
    assert!(serde_json::from_value::<SemanticTheory>(json).is_err());
}

#[test]
fn invalid_equation_root_is_rejected_before_lowering() {
    let mut json = serde_json::to_value(theory(false)).unwrap();
    let rule = &mut json["modules"][0]["rules"][0];
    rule["kind"] = serde_json::json!("equation");
    rule["id"]["item_kind"] = serde_json::json!("equation");
    assert!(serde_json::from_value::<SemanticTheory>(json).is_err());
}

#[test]
fn dangling_semantic_references_are_rejected_before_lowering() {
    let mut json = serde_json::to_value(theory(false)).unwrap();
    json["modules"][0]["rules"][0]["body"]["to"]["production"]["item_name"] =
        serde_json::json!("Missing");
    assert!(serde_json::from_value::<SemanticTheory>(json).is_err());
}

#[test]
fn absolute_origin_labels_cannot_leak_into_sidecars() {
    let mut json = serde_json::to_value(theory(false)).unwrap();
    json["modules"][0]["origin"]["origin"][1]["label"] =
        serde_json::json!("/home/worker/private/checkout");
    let theory = serde_json::from_value::<SemanticTheory>(json).unwrap();
    assert!(matches!(
        lower_semantic_theory(&theory),
        Err(LoweringError::InvalidSidecar(detail)) if detail.contains("absolute path")
    ));
}

#[test]
fn sidecars_contain_no_adapter_or_absolute_path_ids() {
    let lowered = lower_semantic_theory(&theory(false)).unwrap();
    let combined = format!(
        "{}{}",
        lowered.symbol_map().to_canonical_json().unwrap(),
        lowered.source_map().to_canonical_json().unwrap()
    );
    assert!(!combined.contains("/home/"));
    assert!(!combined.contains("native_id"));
    assert!(!combined.contains("k_rust"));
}

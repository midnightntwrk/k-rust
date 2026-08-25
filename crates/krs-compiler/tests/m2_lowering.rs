use krs_compiler::{LoweringError, emit_k, lower_semantic_theory};
use krs_ir::{
    DefinitionSentence, ItemKind, ModuleId, NodeOrigin, OriginFrame, OriginStack, PackageId,
    RangedOriginKind, SemanticCell, SemanticConfiguration, SemanticId, SemanticInitializer,
    SemanticModule, SemanticProduction, SemanticRule, SemanticSort, SemanticSortRef, SemanticTerm,
    SemanticTheory, SentenceKind, Sha256Digest, SourceFileId, SourceMapKey, SourceRange,
    StableItemId, TransformationOriginKind,
};

fn package() -> PackageId {
    PackageId::new("KRS-M2", "m2-semantics", "0.1.0", "workspace").unwrap()
}

fn item(module: &str, name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(package(), [module], name, kind, "").unwrap()
}

fn origin(key: &str) -> NodeOrigin {
    origin_with_label(key, None)
}

fn origin_with_label(key: &str, label: Option<&str>) -> NodeOrigin {
    let file = SourceFileId::new(
        package(),
        "src/lib.rs",
        Sha256Digest::new("0123456789abcdef".repeat(4)).unwrap(),
    )
    .unwrap();
    let mut stack = OriginStack::authored(SourceRange::new(file, 0, 3).unwrap());
    stack.push(OriginFrame::Transformation {
        kind: TransformationOriginKind::SemanticIr,
        item: None,
        label: label.map(str::to_owned).or_else(|| Some(key.to_owned())),
    });
    NodeOrigin::new(SourceMapKey::new(key).unwrap(), stack)
}

#[allow(clippy::too_many_lines)]
fn theory(reverse: bool) -> SemanticTheory {
    let k_item = item("syntax", "KItem", ItemKind::Sort);
    let k_result = item("syntax", "KResult", ItemKind::Sort);
    let object = item("syntax", "M2Obj", ItemKind::Sort);
    let foo = item("syntax", "Foo", ItemKind::Constructor);
    let bar = item("syntax", "Bar", ItemKind::Constructor);
    let rule = item("rules", "foo_to_bar", ItemKind::Rule);
    let mut sorts = vec![
        SemanticSort::new(origin("sem.sort.kitem"), k_item.clone(), vec![]),
        SemanticSort::new(
            origin("sem.sort.kresult"),
            k_result.clone(),
            vec![k_item.clone()],
        ),
        SemanticSort::new(
            origin("sem.sort.object"),
            object.clone(),
            vec![k_result],
        ),
    ];
    let mut productions = vec![
        SemanticProduction::new(
            origin("sem.production.foo"),
            foo.clone(),
            object.clone(),
            vec![],
            "foo",
        )
        .unwrap(),
        SemanticProduction::new(
            origin("sem.production.bar"),
            bar.clone(),
            object.clone(),
            vec![],
            "bar",
        )
        .unwrap(),
    ];
    if reverse {
        sorts.reverse();
        productions.reverse();
    }
    let configuration = SemanticConfiguration::new(
        origin("sem.configuration"),
        SemanticId::new("machine").unwrap(),
        SemanticCell::new(
            origin("sem.cell.k"),
            SemanticId::new("machine.k").unwrap(),
            "k",
            SemanticSortRef::k_sequence(),
        )
        .unwrap(),
        SemanticInitializer::new(
            origin("sem.initializer"),
            SemanticId::new("machine.init").unwrap(),
            vec![],
            SemanticTerm::k_sequence(
                origin("sem.term.init.sequence"),
                k_item,
                vec![SemanticTerm::application(
                    origin("sem.term.init.foo"),
                    object.clone(),
                    foo.clone(),
                    vec![],
                )],
            ),
        ),
    );
    let rewrite = SemanticTerm::rewrite(
        origin("sem.term.rule.rewrite"),
        object.clone(),
        SemanticTerm::application(
            origin("sem.term.rule.foo"),
            object.clone(),
            foo,
            vec![],
        ),
        SemanticTerm::application(origin("sem.term.rule.bar"), object, bar, vec![]),
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
        ModuleId::new("KRS-M2-REFERENCE").unwrap(),
        vec![],
        sorts,
        productions,
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
    assert_eq!(
        emitted.source(),
        r#"module KRS-M2-REFERENCE
  syntax KItem
  syntax KResult
  syntax M2Obj

  syntax M2Obj ::= "bar" [symbol(bar)]
  syntax M2Obj ::= "foo" [symbol(foo)]

  syntax KItem ::= KResult
  syntax KResult ::= M2Obj

  configuration <k> foo </k>

  rule foo => bar [label(krsRule_1d8b3a8a977ae6f58988f622)]
endmodule
"#
    );
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
    assert!(emitted
        .source_map()
        .to_canonical_json()
        .unwrap()
        .contains("\"artifact\": \"definition.k\""));
}

#[test]
fn exact_chain_configuration_and_initializer_remain_structural() {
    let lowered = lower_semantic_theory(&theory(false)).unwrap();
    let configuration = lowered
        .definition()
        .modules()
        .iter()
        .flat_map(|module| module.sentences())
        .find_map(|sentence| match sentence {
            DefinitionSentence::Configuration(value) => Some(value),
            _ => None,
        })
        .unwrap();
    assert_eq!(configuration.cell().symbol().emitted_name(), "k");
    assert_eq!(
        configuration.initializer().symbol().emitted_name(),
        "initKCell"
    );
    assert!(matches!(
        configuration.initializer().body().kind(),
        krs_ir::DefinitionTermKind::KSequence { items, .. } if items.len() == 1
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
    module["productions"].as_array_mut().unwrap().push(second);
    let theory: SemanticTheory = serde_json::from_value(json).unwrap();
    assert!(matches!(
        lower_semantic_theory(&theory),
        Err(LoweringError::NameCollision {
            namespace: "emitted symbol",
            value,
            ..
        }) if value == "foo"
    ));
}

#[test]
fn malformed_record_template_fails_typed_and_is_never_dropped() {
    let mut json = serde_json::to_value(theory(false)).unwrap();
    let module = &mut json["modules"][0];
    let object = module["sorts"]
        .as_array()
        .unwrap()
        .iter()
        .find(|sort| sort["id"]["item_name"] == "M2Obj")
        .unwrap()["id"]
        .clone();
    let production = module["productions"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|production| production["id"]["item_name"] == "Foo")
        .unwrap();
    production["argument_sorts"] = serde_json::json!([object]);
    production["syntax"] = serde_json::json!("box");
    let theory = serde_json::from_value::<SemanticTheory>(json).unwrap();
    assert!(matches!(
        lower_semantic_theory(&theory),
        Err(LoweringError::InvalidProductionTemplate { .. })
    ));
}

#[test]
fn unsupported_sentence_kind_fails_typed() {
    let mut json = serde_json::to_value(theory(false)).unwrap();
    let rule = &mut json["modules"][0]["rules"][0];
    rule["kind"] = serde_json::json!("equation");
    rule["id"]["item_kind"] = serde_json::json!("equation");
    let theory = serde_json::from_value::<SemanticTheory>(json).unwrap();
    assert!(matches!(
        lower_semantic_theory(&theory),
        Err(LoweringError::UnsupportedShape {
            node: "sentence",
            ..
        })
    ));
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

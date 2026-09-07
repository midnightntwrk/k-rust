use std::{
    collections::BTreeMap,
    sync::{Arc, Barrier},
};

use k_rust::definition::{
    Attributes, Definition, FlatImport, FlatModule, ProductionItem, ResolveError,
    ResolvedDefinition, Sentence,
};
use k_rust::kast::{Label, ResolvedProductionId, Sort, Term, TermMetadata, TermSpan};
use k_rust::provenance::{
    GeneratingPass, LogicalSourceId, ORIGIN_ATTRIBUTE, OriginRecord, ProvenanceLink, SourceTable,
};
use serde_json::{Value, json};

fn attrs(entries: &[(&str, &str)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), Value::String((*value).into())))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn marker(name: &str) -> Sentence {
    Sentence::Bubble {
        sentence_type: "rule".into(),
        contents: name.into(),
        attributes: Attributes::default(),
    }
}

fn module(name: &str, imports: &[(&str, bool)]) -> FlatModule {
    FlatModule {
        name: name.into(),
        imports: imports
            .iter()
            .map(|(name, public)| FlatImport {
                name: (*name).into(),
                public: *public,
            })
            .collect(),
        local_sentences: vec![marker(name)],
        attributes: Attributes::default(),
    }
}

fn definition(modules: Vec<FlatModule>) -> Definition {
    Definition {
        main_module: "A".into(),
        modules,
        attributes: Attributes::default(),
    }
}

fn module_names(
    resolved: &ResolvedDefinition,
    modules: &[k_rust::definition::ModuleId],
) -> Vec<String> {
    modules
        .iter()
        .map(|id| resolved.module(*id).name.clone())
        .collect()
}

#[test]
fn resolves_diamond_imports_dependency_first() {
    let definition = definition(vec![
        module("A", &[("C", false), ("B", true)]),
        module("B", &[("D", true)]),
        module("C", &[("D", true)]),
        module("D", &[]),
    ]);
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let a = resolved.main_module_id();

    assert_eq!(
        module_names(&resolved, resolved.dependency_order()),
        ["D", "B", "C", "A"]
    );
    assert_eq!(
        resolved
            .direct_imports(a)
            .into_iter()
            .map(|import| (resolved.module(import.module).name.as_str(), import.public))
            .collect::<Vec<_>>(),
        [("B", true), ("C", false)]
    );
    assert_eq!(
        module_names(&resolved, &resolved.transitive_imports(a)),
        ["B", "C", "D"]
    );
    assert_eq!(
        resolved
            .sentences(a)
            .into_iter()
            .map(|sentence| match sentence {
                Sentence::Bubble { contents, .. } => contents.as_str(),
                _ => panic!("expected marker sentence"),
            })
            .collect::<Vec<_>>(),
        ["D", "B", "C", "A"]
    );
}

#[test]
fn topology_is_independent_of_flat_module_order() {
    let forward = ResolvedDefinition::resolve(&definition(vec![
        module("A", &[("B", true), ("C", true)]),
        module("B", &[("D", true)]),
        module("C", &[("D", true)]),
        module("D", &[]),
    ]))
    .unwrap();
    let reverse = ResolvedDefinition::resolve(&definition(vec![
        module("D", &[]),
        module("C", &[("D", true)]),
        module("B", &[("D", true)]),
        module("A", &[("C", true), ("B", true)]),
    ]))
    .unwrap();

    assert_eq!(
        module_names(&forward, forward.dependency_order()),
        module_names(&reverse, reverse.dependency_order())
    );
}

#[test]
fn rejects_invalid_module_graphs_with_specific_errors() {
    assert_eq!(
        ResolvedDefinition::resolve(&definition(vec![module("A", &[]), module("A", &[])]))
            .unwrap_err(),
        ResolveError::DuplicateModule("A".into())
    );

    let mut missing_main = definition(vec![module("A", &[])]);
    missing_main.main_module = "MAIN".into();
    assert_eq!(
        ResolvedDefinition::resolve(&missing_main).unwrap_err(),
        ResolveError::MissingMainModule("MAIN".into())
    );

    assert_eq!(
        ResolvedDefinition::resolve(&definition(vec![module("A", &[("MISSING", true)])]))
            .unwrap_err(),
        ResolveError::MissingImport {
            module: "A".into(),
            import: "MISSING".into(),
        }
    );
    assert_eq!(
        ResolvedDefinition::resolve(&definition(vec![module("A", &[("A", true)])])).unwrap_err(),
        ResolveError::SelfImport("A".into())
    );

    let cycle = definition(vec![
        module("A", &[("B", true)]),
        module("B", &[("C", true)]),
        module("C", &[("A", true)]),
    ]);
    assert_eq!(
        ResolvedDefinition::resolve(&cycle).unwrap_err(),
        ResolveError::CircularImports(vec!["A".into(), "B".into(), "C".into(), "A".into()])
    );
}

#[test]
fn applies_scala_public_sentence_rules() {
    let mut public = marker("public");
    let Sentence::Bubble { attributes, .. } = &mut public else {
        unreachable!()
    };
    *attributes = attrs(&[("public", "")]);

    let mut private = marker("private");
    let Sentence::Bubble { attributes, .. } = &mut private else {
        unreachable!()
    };
    *attributes = attrs(&[("private", "")]);

    let mut private_module = module("A", &[]);
    private_module.attributes = attrs(&[("private", "")]);
    private_module.local_sentences = vec![marker("ordinary"), public.clone(), private.clone()];
    let resolved = ResolvedDefinition::resolve(&definition(vec![private_module])).unwrap();
    assert_eq!(
        resolved.public_sentences(resolved.main_module_id()),
        [&public]
    );

    let mut ordinary_module = module("A", &[]);
    ordinary_module.local_sentences = vec![marker("ordinary"), public, private];
    let resolved = ResolvedDefinition::resolve(&definition(vec![ordinary_module])).unwrap();
    assert_eq!(
        resolved.public_sentences(resolved.main_module_id()).len(),
        2
    );
}

fn sentence_markers(sentences: Vec<&Sentence>) -> Vec<&str> {
    sentences
        .into_iter()
        .map(|sentence| match sentence {
            Sentence::Bubble { contents, .. } => contents.as_str(),
            _ => panic!("expected marker sentence"),
        })
        .collect()
}

#[test]
fn signature_sentences_keep_the_modules_own_private_imports_one_level() {
    let resolved = ResolvedDefinition::resolve(&definition(vec![
        module("A", &[("B", false)]),
        module("B", &[("C", false)]),
        module("C", &[]),
    ]))
    .unwrap();

    for (id, _) in resolved.modules() {
        resolved.sentences(id);
    }

    assert_eq!(
        sentence_markers(resolved.signature_sentences(resolved.main_module_id())),
        ["B", "A"]
    );
}

#[test]
fn signature_sentences_follow_only_public_imports_transitively() {
    let resolved = ResolvedDefinition::resolve(&definition(vec![
        module("A", &[("B", false)]),
        module("B", &[("C", true)]),
        module("C", &[("D", false)]),
        module("D", &[]),
    ]))
    .unwrap();

    for (id, _) in resolved.modules() {
        resolved.sentences(id);
    }

    assert_eq!(
        sentence_markers(resolved.signature_sentences(resolved.main_module_id())),
        ["C", "B", "A"]
    );
}

#[test]
fn signature_sentences_apply_public_sentences_of_private_modules() {
    let mut exported = marker("exported");
    *exported.attributes_mut() = attrs(&[("public", "")]);
    let mut hidden = marker("hidden");
    *hidden.attributes_mut() = attrs(&[("private", "")]);
    let mut private = module("B", &[]);
    private.attributes = attrs(&[("private", "")]);
    private.local_sentences = vec![marker("ordinary"), exported, hidden];
    let resolved =
        ResolvedDefinition::resolve(&definition(vec![module("A", &[("B", true)]), private]))
            .unwrap();

    for (id, _) in resolved.modules() {
        resolved.sentences(id);
    }

    assert_eq!(
        sentence_markers(resolved.signature_sentences(resolved.main_module_id())),
        ["exported", "A"]
    );
}

#[test]
fn deduplicates_flat_sets_only_during_resolution() {
    let repeated = marker("same");
    let mut a = module("A", &[("B", true), ("B", true)]);
    a.local_sentences = vec![repeated.clone(), repeated.clone()];
    let mut b = module("B", &[]);
    b.local_sentences = vec![repeated];
    let definition = definition(vec![a, b]);

    assert_eq!(definition.modules[0].local_sentences.len(), 2);
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let a = resolved.main_module_id();
    assert_eq!(resolved.module(a).local_sentences.len(), 1);
    assert_eq!(resolved.direct_imports(a).len(), 1);
    assert_eq!(resolved.sentences(a).len(), 1);
}

#[test]
fn deduplicates_productions_using_scala_equality() {
    let production = |line| Sentence::Production {
        label: Some(Label::new("label")),
        parameters: Vec::new(),
        sort: Sort::new("K"),
        items: vec![ProductionItem::Terminal("token".into())],
        attributes: Attributes::new(BTreeMap::from([(
            "org.kframework.attributes.Location".into(),
            json!([line, 1, line, 2]),
        )])),
    };
    let mut a = module("A", &[]);
    a.local_sentences = vec![production(1), production(2)];
    let resolved = ResolvedDefinition::resolve(&definition(vec![a])).unwrap();
    assert_eq!(resolved.main_module().local_sentences.len(), 1);
}

#[test]
fn resolves_the_upstream_reduced_fixture() {
    let definition =
        k_rust::definition::json::from_str(include_str!("fixtures/kast/definition.json")).unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    assert_eq!(resolved.module(resolved.main_module_id()).name, "IMP");
    assert_eq!(
        module_names(&resolved, resolved.dependency_order()),
        ["BOOL-SYNTAX", "IMP"]
    );
    for (module, _) in resolved.modules() {
        resolved.sorted_local_sentences(module).unwrap();
    }
}

fn assert_owned_locations(
    resolved: &ResolvedDefinition,
    sentences: &[&Sentence],
    expected: &[(&str, usize)],
) {
    assert_eq!(sentences.len(), expected.len());
    for (sentence, &(owner, index)) in sentences.iter().zip(expected) {
        let owner = resolved.module(resolved.module_id(owner).unwrap());
        assert!(
            std::ptr::eq(*sentence, &owner.local_sentences[index]),
            "result must borrow the expected receiver-owned sentence {owner:?} at {index}"
        );
    }
}

#[test]
fn cached_diamond_sentences_preserve_order_and_owner_references() {
    let resolved = ResolvedDefinition::resolve(&definition(vec![
        module("A", &[("C", false), ("B", true)]),
        module("B", &[("D", true)]),
        module("C", &[("D", true)]),
        module("D", &[]),
    ]))
    .unwrap();
    for _ in 0..3 {
        let sentences = resolved.sentences(resolved.main_module_id());
        assert_owned_locations(
            &resolved,
            &sentences,
            &[("D", 0), ("B", 0), ("C", 0), ("A", 0)],
        );
        assert_eq!(sentence_markers(sentences), ["D", "B", "C", "A"]);
    }
}

#[test]
fn cached_empty_visibility_does_not_add_or_leak_sentences() {
    let mut empty = module("B", &[]);
    empty.local_sentences.clear();
    let resolved =
        ResolvedDefinition::resolve(&definition(vec![module("A", &[("B", true)]), empty])).unwrap();
    let b = resolved.module_id("B").unwrap();
    assert!(resolved.sentences(b).is_empty());
    assert_eq!(
        sentence_markers(resolved.sentences(resolved.main_module_id())),
        ["A"]
    );
    assert!(resolved.sentences(b).is_empty());
    assert!(resolved.clone().sentences(b).is_empty());
}

#[test]
fn cached_productions_keep_first_metadata_representative_and_distinct_semantics() {
    let production = |line, pass| {
        let mut attributes = Attributes::new(BTreeMap::from([
            (
                "org.kframework.attributes.Location".into(),
                json!([line, 1, line, 2]),
            ),
            (
                "org.kframework.attributes.Source".into(),
                json!(format!("source-{line}.k")),
            ),
        ]));
        attributes.insert(
            ORIGIN_ATTRIBUTE,
            OriginRecord {
                pass,
                origins: Vec::new().into(),
                destination: None,
            }
            .to_value(),
        );
        Sentence::Production {
            label: Some(Label::new("p")),
            parameters: Vec::new(),
            sort: Sort::new("Exp"),
            items: vec![ProductionItem::Terminal("x".into())],
            attributes,
        }
    };
    let first = production(1, GeneratingPass::SubsortKItem);
    let duplicate = production(2, GeneratingPass::MacroExpansion);
    let mut function = duplicate.clone();
    function.attributes_mut().insert("function", json!(""));
    let mut symbol = duplicate.clone();
    symbol.attributes_mut().insert("symbol", json!(""));
    assert!(k_rust::definition::sentence_equivalent(&first, &duplicate));
    assert!(!k_rust::definition::sentence_equivalent(&first, &function));
    assert!(!k_rust::definition::sentence_equivalent(&first, &symbol));
    let mut a = module("A", &[("B", true), ("C", true)]);
    a.local_sentences.clear();
    let mut b = module("B", &[("D", true)]);
    b.local_sentences = vec![duplicate, function, symbol];
    let mut c = module("C", &[("D", true)]);
    c.local_sentences.clear();
    let mut d = module("D", &[]);
    d.local_sentences = vec![first];
    let resolved = ResolvedDefinition::resolve(&definition(vec![a, b, c, d])).unwrap();
    for _ in 0..3 {
        let sentences = resolved.sentences(resolved.main_module_id());
        assert_owned_locations(&resolved, &sentences, &[("D", 0), ("B", 1), ("B", 2)]);
        assert_eq!(sentences[0].attributes().source(), Some("source-1.k"));
        assert_eq!(sentences[0].attributes().location().unwrap().start_line, 1);
        assert_eq!(
            sentences[0].attributes().get(ORIGIN_ATTRIBUTE),
            resolved
                .module(resolved.module_id("D").unwrap())
                .local_sentences[0]
                .attributes()
                .get(ORIGIN_ATTRIBUTE)
        );
    }
}

fn visible_provenance(resolved: &ResolvedDefinition, sources: &SourceTable) -> String {
    let mut visible = module("A", &[]);
    visible.local_sentences = resolved
        .sentences(resolved.main_module_id())
        .into_iter()
        .cloned()
        .collect();
    k_rust::definition::json::to_provenance_string_pretty(&definition(vec![visible]), sources)
        .unwrap()
}

#[test]
fn cached_clones_borrow_their_own_graph_and_outlive_the_original_with_metadata() {
    let mut sources = SourceTable::default();
    let source = sources.intern(LogicalSourceId::new("source.k", b"X"));
    let span = TermSpan {
        source,
        start: 0,
        end: 1,
    };
    let origin = Arc::new(OriginRecord {
        pass: GeneratingPass::MacroExpansion,
        origins: vec![ProvenanceLink::Source { span }].into(),
        destination: None,
    });
    let metadata = TermMetadata {
        span: Some(span),
        production: Some(ResolvedProductionId(0)),
        sort: Some(Sort::new("Exp")),
        origin: Some(origin.clone()),
    };
    let mut a = module("A", &[("B", true)]);
    a.local_sentences.clear();
    let mut b = module("B", &[]);
    b.local_sentences = vec![
        Sentence::Production {
            label: Some(Label::new("p")),
            parameters: Vec::new(),
            sort: Sort::new("Exp"),
            items: vec![ProductionItem::Terminal("x".into())],
            attributes: Attributes::default(),
        },
        Sentence::Rule {
            body: Term::variable("X").with_metadata(metadata.clone()),
            requires: Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
            ensures: Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
            attributes: Attributes::new(BTreeMap::from([(
                ORIGIN_ATTRIBUTE.into(),
                origin.to_value(),
            )])),
        },
    ];
    let original = ResolvedDefinition::resolve(&definition(vec![a, b])).unwrap();
    let cold_clone = original.clone();
    let expected = visible_provenance(&original, &sources);
    let warm_clone = original.clone();
    for cloned in [&cold_clone, &warm_clone] {
        let sentences = cloned.sentences(cloned.main_module_id());
        assert_owned_locations(cloned, &sentences, &[("B", 0), ("B", 1)]);
        let original_sentences = original.sentences(original.main_module_id());
        for (cloned_sentence, original_sentence) in sentences.iter().zip(original_sentences) {
            assert!(!std::ptr::eq(*cloned_sentence, original_sentence));
        }
    }
    drop(original);
    for cloned in [cold_clone, warm_clone] {
        let sentences = cloned.sentences(cloned.main_module_id());
        assert_owned_locations(&cloned, &sentences, &[("B", 0), ("B", 1)]);
        let Sentence::Rule { body, .. } = sentences[1] else {
            panic!("expected rule")
        };
        assert_eq!(body.metadata(), Some(&metadata));
        assert_eq!(visible_provenance(&cloned, &sources), expected);
    }
}

#[test]
fn cached_visibility_is_not_reused_for_a_new_graph_with_matching_indices() {
    let mut input = definition(vec![
        module("A", &[("B", true)]),
        module("B", &[]),
        module("C", &[]),
    ]);
    let old = ResolvedDefinition::resolve(&input).unwrap();
    assert_eq!(
        sentence_markers(old.sentences(old.main_module_id())),
        ["B", "A"]
    );
    input.modules[0].imports[0].name = "C".into();
    input.modules[2].local_sentences[0] = marker("changed-C");
    let new = ResolvedDefinition::resolve(&input).unwrap();
    assert_eq!(old.main_module_id(), new.main_module_id());
    for _ in 0..2 {
        let sentences = new.sentences(new.main_module_id());
        assert_owned_locations(&new, &sentences, &[("C", 0), ("A", 0)]);
        assert_eq!(sentence_markers(sentences), ["changed-C", "A"]);
        assert_eq!(
            sentence_markers(old.sentences(old.main_module_id())),
            ["B", "A"]
        );
    }
}

#[test]
fn concurrent_cold_sentence_reads_preserve_shared_owner_references() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<ResolvedDefinition>();
    let resolved = ResolvedDefinition::resolve(&definition(vec![
        module("A", &[("B", true), ("C", false)]),
        module("B", &[("D", true)]),
        module("C", &[("D", true)]),
        module("D", &[]),
    ]))
    .unwrap();
    let barrier = Barrier::new(4);
    std::thread::scope(|scope| {
        let mut readers = Vec::new();
        for _ in 0..4 {
            let (resolved, barrier) = (&resolved, &barrier);
            readers.push(scope.spawn(move || {
                barrier.wait();
                for _ in 0..3 {
                    let sentences = resolved.sentences(resolved.main_module_id());
                    assert_owned_locations(
                        resolved,
                        &sentences,
                        &[("D", 0), ("B", 0), ("C", 0), ("A", 0)],
                    );
                    assert_eq!(sentence_markers(sentences), ["D", "B", "C", "A"]);
                }
            }));
        }
        for reader in readers {
            reader.join().unwrap();
        }
    });
}

#[test]
fn warming_sentence_caches_does_not_change_debug_output() {
    let resolved = ResolvedDefinition::resolve(&definition(vec![
        module("A", &[("B", true)]),
        module("B", &[]),
    ]))
    .unwrap();
    let compact = format!("{resolved:?}");
    let pretty = format!("{resolved:#?}");
    for (id, _) in resolved.modules() {
        resolved.sentences(id);
    }
    assert_eq!(format!("{resolved:?}"), compact);
    assert_eq!(format!("{resolved:#?}"), pretty);
    assert_eq!(format!("{:?}", resolved.clone()), compact);
}

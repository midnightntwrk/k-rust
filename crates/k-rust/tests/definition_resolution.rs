use std::{
    collections::{BTreeMap, BTreeSet},
    sync::{Arc, Barrier},
};

use k_rust::definition::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, ModuleId, ProductionItem,
    ResolveError, ResolvedDefinition, SENTENCE_END_OFFSET_ATTRIBUTE,
    SENTENCE_START_OFFSET_ATTRIBUTE, Sentence, sentence_equivalent,
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

// Deliberately retain the original complete scan as an independent selection oracle.
fn quadratic_visible_sentences(resolved: &ResolvedDefinition, module: ModuleId) -> Vec<&Sentence> {
    let mut visible = resolved
        .transitive_imports(module)
        .into_iter()
        .collect::<BTreeSet<_>>();
    visible.insert(module);
    let mut result: Vec<&Sentence> = Vec::new();
    for (id, owner) in resolved.modules() {
        if visible.contains(&id) {
            for sentence in &owner.local_sentences {
                if !result
                    .iter()
                    .any(|existing| sentence_equivalent(existing, sentence))
                {
                    result.push(sentence);
                }
            }
        }
    }
    result
}

fn assert_bucket_sequence(sentences: Vec<Sentence>, expected_indices: &[usize]) {
    // One candidate per module prevents local resolution from deduplicating the fixtures.
    let mut modules = Vec::new();
    for (index, sentence) in sentences.into_iter().enumerate() {
        let mut owner = module(&format!("B{index:03}"), &[]);
        if index > 0 {
            owner.imports.push(FlatImport {
                name: format!("B{:03}", index - 1),
                public: index % 2 == 0,
            });
        }
        owner.local_sentences = vec![sentence];
        modules.push(owner);
    }
    let mut main = module("A", &[]);
    main.imports.push(FlatImport {
        name: modules.last().unwrap().name.clone(),
        public: true,
    });
    main.local_sentences.clear();
    modules.push(main);
    let original = ResolvedDefinition::resolve(&definition(modules)).unwrap();
    let cold_clone = original.clone();
    original.sentences(original.main_module_id());
    let warm_clone = original.clone();
    for resolved in [original, cold_clone, warm_clone] {
        let expected_owners = expected_indices
            .iter()
            .map(|index| format!("B{index:03}"))
            .collect::<Vec<_>>();
        let expected_locations = expected_owners
            .iter()
            .map(|owner| (owner.as_str(), 0))
            .collect::<Vec<_>>();
        assert_owned_locations(
            &resolved,
            &resolved.sentences(resolved.main_module_id()),
            &expected_locations,
        );
        for (id, _) in resolved.modules() {
            let expected = quadratic_visible_sentences(&resolved, id);
            for _ in 0..2 {
                let actual = resolved.sentences(id);
                assert_eq!(actual.len(), expected.len());
                for (actual, expected) in actual.iter().zip(&expected) {
                    assert!(
                        std::ptr::eq(*actual, *expected),
                        "bucket selection must retain the quadratic oracle's exact owner and order"
                    );
                }
            }
        }
    }
}

fn assert_equivalent_with_collisions(
    first: Sentence,
    equivalent: Sentence,
    collisions: Vec<Sentence>,
) {
    assert!(sentence_equivalent(&first, &equivalent));
    let mut sequence = vec![first, marker("intervening-unrelated-sentence")];
    for collision in &collisions {
        assert!(
            !sequence
                .iter()
                .any(|earlier| sentence_equivalent(earlier, collision))
        );
        sequence.push(collision.clone());
    }
    let expected = (0..sequence.len()).collect::<Vec<_>>();
    sequence.push(equivalent);
    sequence.extend(collisions);
    assert_bucket_sequence(sequence, &expected);
}

#[test]
fn sentence_buckets_preserve_term_equality_and_condition_attribute_collisions() {
    let body = |annotated| {
        let variable = Term::Variable {
            name: "X".into(),
            sort: Some(Sort::new(if annotated { "Bool" } else { "Int" })),
        };
        let metadata = TermMetadata {
            sort: Some(Sort::new("Generated")),
            production: Some(ResolvedProductionId(7)),
            ..TermMetadata::default()
        };
        let variable = if annotated {
            Term::Annotated {
                term: Box::new(Term::Annotated {
                    term: Box::new(variable),
                    metadata: metadata.clone(),
                }),
                metadata: metadata.clone(),
            }
        } else {
            variable
        };
        let body = Term::Rewrite {
            left: Box::new(Term::apply(
                "f",
                vec![Term::As {
                    pattern: Box::new(variable),
                    alias: Box::new(Term::variable("Y")),
                }],
            )),
            right: Box::new(Term::Sequence(vec![
                Term::InjectedLabel(Label::with_parameters("g", vec![Sort::new("Int")])),
                Term::Token {
                    token: "1".into(),
                    sort: Sort::with_parameters("List", vec![Sort::new("Int")]),
                },
            ])),
        };
        if annotated {
            body.with_metadata(metadata)
        } else {
            body
        }
    };
    let term_sentence = |variant, body, condition, attributes| match variant {
        0 => Sentence::ContextAlias {
            body,
            requires: condition,
            attributes,
        },
        1 => Sentence::Context {
            body,
            requires: condition,
            attributes,
        },
        2 => Sentence::Rule {
            body,
            requires: condition,
            ensures: Term::variable("E"),
            attributes,
        },
        3 => Sentence::Claim {
            body,
            requires: condition,
            ensures: Term::variable("E"),
            attributes,
        },
        4 => Sentence::Configuration {
            body,
            ensures: condition,
            attributes,
        },
        _ => unreachable!(),
    };
    let mut distinct_variants = Vec::new();
    for variant in 0..5 {
        let first = term_sentence(
            variant,
            body(false),
            Term::variable("C"),
            Attributes::default(),
        );
        let mut equivalent = term_sentence(
            variant,
            body(true),
            Term::variable("C"),
            Attributes::default(),
        );
        equivalent.attributes_mut().insert(
            ORIGIN_ATTRIBUTE,
            json!({"pass": "macro-expansion", "origins": [], "destination": null}),
        );
        equivalent
            .attributes_mut()
            .insert(SENTENCE_START_OFFSET_ATTRIBUTE, json!(10));
        equivalent
            .attributes_mut()
            .insert(SENTENCE_END_OFFSET_ATTRIBUTE, json!(20));
        let condition = term_sentence(
            variant,
            body(false),
            Term::variable("different-condition"),
            Attributes::default(),
        );
        let attribute = term_sentence(
            variant,
            body(false),
            Term::variable("C"),
            attrs(&[("org.kframework.attributes.Source", "different.k")]),
        );
        let mut collisions = vec![condition, attribute];
        if let Sentence::Rule { ensures, .. } | Sentence::Claim { ensures, .. } = &mut equivalent {
            *ensures = Term::Variable {
                name: "E".into(),
                sort: Some(Sort::new("Bool")),
            };
            let mut distinct_ensures = first.clone();
            if let Sentence::Rule { ensures, .. } | Sentence::Claim { ensures, .. } =
                &mut distinct_ensures
            {
                *ensures = Term::variable("different-ensures");
            }
            collisions.push(distinct_ensures);
        }
        assert_equivalent_with_collisions(first.clone(), equivalent, collisions);
        distinct_variants.push(first);
    }
    distinct_variants.extend(distinct_variants.clone());
    assert_bucket_sequence(distinct_variants, &[0, 1, 2, 3, 4]);
}

#[test]
fn sentence_buckets_preserve_production_exceptions_and_prefix_collisions() {
    let first = Sentence::Production {
        label: Some(Label::with_parameters("p", vec![Sort::new("Int")])),
        parameters: vec![Sort::new("S")],
        sort: Sort::with_parameters("List", vec![Sort::new("Int")]),
        items: vec![
            ProductionItem::regex("[a-z]+"),
            ProductionItem::Terminal("end".into()),
        ],
        attributes: attrs(&[("org.kframework.attributes.Source", "first.k")]),
    };
    let mut equivalent = first.clone();
    if let Sentence::Production {
        items, attributes, ..
    } = &mut equivalent
    {
        items[0] = ProductionItem::RegexTerminal {
            precede_regex: Some("before".into()),
            regex: "[a-z]+".into(),
            follow_regex: Some("after".into()),
        };
        attributes.insert("klabel", json!("p"));
        attributes.insert("function", json!(false));
        attributes.insert("symbol", json!(17));
        attributes.insert("org.kframework.attributes.Source", json!("later.k"));
    }
    let mut collisions = Vec::new();
    for (key, value) in [("klabel", "other"), ("function", ""), ("symbol", "")] {
        let mut changed = first.clone();
        changed.attributes_mut().insert(key, json!(value));
        collisions.push(changed);
    }
    let mut later_item = first.clone();
    if let Sentence::Production { items, .. } = &mut later_item {
        items[1] = ProductionItem::Terminal("different-end".into());
    }
    collisions.push(later_item);
    assert_equivalent_with_collisions(first.clone(), equivalent, collisions);
    let mut nonstring_label = first.clone();
    nonstring_label
        .attributes_mut()
        .insert("klabel", json!({"name": "ignored"}));
    assert_equivalent_with_collisions(first.clone(), nonstring_label, vec![]);

    let mut boundary_variants = vec![first.clone()];
    for field in 0..7 {
        let mut changed = first.clone();
        if let Sentence::Production {
            label,
            parameters,
            sort,
            items,
            ..
        } = &mut changed
        {
            match field {
                0 => label.as_mut().unwrap().parameters[0] = Sort::new("Bool"),
                1 => *label = None,
                2 => parameters[0] = Sort::new("T"),
                3 => sort.parameters[0] = Sort::new("Bool"),
                4 => items.clear(),
                5 => {
                    items[0] = ProductionItem::NonTerminal {
                        sort: Sort::new("Int"),
                        name: Some("x".into()),
                    }
                }
                6 => items[0] = ProductionItem::Terminal("[a-z]+".into()),
                _ => unreachable!(),
            }
        }
        assert!(!sentence_equivalent(&first, &changed));
        boundary_variants.push(changed);
    }
    let expected = (0..boundary_variants.len()).collect::<Vec<_>>();
    boundary_variants.extend(boundary_variants.clone());
    assert_bucket_sequence(boundary_variants, &expected);
}

#[test]
fn sentence_buckets_preserve_set_valued_tags_and_ordered_priority_rows() {
    let tags = |values: &[&str]| {
        values
            .iter()
            .map(|value| (*value).into())
            .collect::<Vec<String>>()
    };
    for associativity in [
        Associativity::Left,
        Associativity::Right,
        Associativity::NonAssoc,
        Associativity::Unspecified,
    ] {
        let first = Sentence::SyntaxAssociativity {
            associativity,
            tags: tags(&["b", "a", "a"]),
            attributes: Attributes::default(),
        };
        let equivalent = Sentence::SyntaxAssociativity {
            associativity,
            tags: tags(&["a", "b"]),
            attributes: Attributes::default(),
        };
        let collision = Sentence::SyntaxAssociativity {
            associativity,
            tags: tags(&["a", "c"]),
            attributes: Attributes::default(),
        };
        assert_equivalent_with_collisions(first, equivalent, vec![collision]);
    }
    let first = Sentence::SyntaxPriority {
        priorities: vec![tags(&["b", "a", "a"]), vec![], tags(&["c"])],
        attributes: Attributes::default(),
    };
    let equivalent = Sentence::SyntaxPriority {
        priorities: vec![tags(&["a", "b"]), vec![], tags(&["c", "c"])],
        attributes: Attributes::default(),
    };
    let reordered = Sentence::SyntaxPriority {
        priorities: vec![tags(&["c"]), vec![], tags(&["a", "b"])],
        attributes: Attributes::default(),
    };
    let changed_empty = Sentence::SyntaxPriority {
        priorities: vec![tags(&["a", "b"]), tags(&["a"]), tags(&["c"])],
        attributes: Attributes::default(),
    };
    assert_equivalent_with_collisions(first, equivalent, vec![reordered, changed_empty]);
}

#[test]
fn sentence_buckets_match_quadratic_selection_for_remaining_syntax_and_attributes() {
    let syntax = vec![
        Sentence::SyntaxSort {
            parameters: vec![Sort::new("S")],
            sort: Sort::with_parameters("List", vec![Sort::new("Int")]),
            attributes: Attributes::default(),
        },
        Sentence::SortSynonym {
            new_sort: Sort::new("Alias"),
            old_sort: Sort::new("Int"),
            attributes: Attributes::default(),
        },
        Sentence::SyntaxLexical {
            name: "token".into(),
            regex: "[a-z]+".into(),
            attributes: Attributes::default(),
        },
        marker("same-body"),
    ];
    let mut combined = Vec::new();
    for first in syntax {
        let mut equivalent = first.clone();
        equivalent
            .attributes_mut()
            .insert(SENTENCE_START_OFFSET_ATTRIBUTE, json!(32));
        let mut source_collision = first.clone();
        source_collision
            .attributes_mut()
            .insert("org.kframework.attributes.Source", json!("source.k"));
        let mut typed_collision = first.clone();
        typed_collision.attributes_mut().insert("custom", json!(1));
        let mut string_collision = first.clone();
        string_collision
            .attributes_mut()
            .insert("custom", json!("1"));
        assert_equivalent_with_collisions(
            first.clone(),
            equivalent,
            vec![source_collision, typed_collision, string_collision],
        );
        combined.push(first);
    }
    combined.extend(combined.clone());
    assert_bucket_sequence(combined, &[0, 1, 2, 3]);
}

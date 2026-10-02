use std::sync::Arc;

use std::collections::{BTreeMap, BTreeSet};

use k_rust::definition::{
    AttributeConflict, Attributes, Definition, FlatImport, FlatModule, ProductionItem,
    ResolvedDefinition, Sentence, SortCatalog, SortHead, Spelling,
};
use k_rust::kast::{Label, Sort};
use serde_json::{Value, json};

fn attrs(entries: &[(&str, Value)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), value.clone()))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn syntax_sort(parameters: Vec<Sort>, sort: Sort, attributes: Attributes) -> Sentence {
    Sentence::SyntaxSort {
        parameters,
        sort,
        attributes,
    }
}

fn production(
    result: Sort,
    parameters: Vec<Sort>,
    arguments: Vec<Sort>,
    attributes: Attributes,
) -> Sentence {
    Sentence::Production {
        label: Some(Label::new(format!("make{}", result.name))),
        parameters,
        sort: result,
        items: arguments
            .into_iter()
            .map(|sort| ProductionItem::NonTerminal { sort, name: None })
            .collect(),
        attributes,
    }
}

fn fixture() -> ResolvedDefinition {
    let int = Sort::new("Int");
    let variable = Sort::new("T");
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![
            Arc::new(syntax_sort(
                Vec::new(),
                int.clone(),
                attrs(&[("hook", json!("INT.Int")), ("token", json!(""))]),
            )),
            Arc::new(production(
                Sort::new("TokenFromProduction"),
                Vec::new(),
                Vec::new(),
                attrs(&[("token", json!(""))]),
            )),
        ],
        attributes: Attributes::default(),
    };
    let main = FlatModule {
        name: "MAIN".into(),
        imports: vec![FlatImport {
            name: "BASE".into(),
            public: true,
        }],
        local_sentences: vec![
            Arc::new(syntax_sort(
                vec![variable.clone()],
                Sort::with_parameters("List", vec![variable.clone()]),
                Attributes::default(),
            )),
            Arc::new(production(
                Sort::with_parameters("List", vec![int.clone()]),
                Vec::new(),
                vec![int.clone()],
                attrs(&[("userList", json!(""))]),
            )),
            Arc::new(production(
                Sort::with_parameters("Map", vec![Sort::new("K"), Sort::new("V")]),
                vec![Sort::new("K"), Sort::new("V")],
                Vec::new(),
                Attributes::default(),
            )),
            Arc::new(syntax_sort(
                Vec::new(),
                Sort::with_parameters("Vec", vec![Sort::new("3")]),
                Attributes::default(),
            )),
            Arc::new(Sentence::SortSynonym {
                new_sort: Sort::new("Nat"),
                old_sort: int,
                attributes: Attributes::default(),
            }),
        ],
        attributes: Attributes::default(),
    };
    ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![main, base],
        attributes: Attributes::default(),
    })
    .unwrap()
}

#[test]
fn merge_attributes_reports_conflicts_and_preserves_the_java_result() {
    let first = attrs(&[("same", json!(1)), ("conflict", json!("left"))]);
    let second = attrs(&[
        ("same", json!(1)),
        ("conflict", json!("right")),
        ("unique", json!(true)),
    ]);
    let error = Attributes::merge([&first, &second]).unwrap_err();
    let merged = &error.merged;

    assert_eq!(merged.get("same"), Some(&json!(1)));
    assert_eq!(merged.get("unique"), Some(&json!(true)));
    assert_eq!(merged.get("conflict"), None);
    assert_eq!(
        error.conflicts,
        [AttributeConflict {
            key: "conflict".into(),
            values: vec![json!("left"), json!("right")],
        }]
    );
}

#[test]
fn sort_heads_include_parameter_arity() {
    let nullary = SortHead::nullary("Map");
    let binary = SortHead::new("Map", 2);
    assert_ne!(nullary, binary);
    assert_eq!(nullary.to_string(), "Map");
    assert_eq!(binary.to_string(), "Map{S0,S1}");
    assert_eq!(
        SortHead::from(&Sort::with_parameters(
            "Map",
            vec![Sort::new("K"), Sort::new("V")]
        )),
        binary
    );
}

#[test]
fn derives_concrete_instantiations_and_numeric_parameter_sorts() {
    let resolved = fixture();
    let catalog = resolved.sort_catalog(resolved.main_module_id());

    assert_eq!(
        catalog.instantiations()[&SortHead::new("List", 1)],
        [Sort::with_parameters("List", vec![Sort::new("Int")])]
            .into_iter()
            .collect()
    );
    assert!(catalog.instantiations()[&SortHead::new("Map", 2)].is_empty());
    assert_eq!(
        catalog.instantiations()[&SortHead::new("Vec", 1)],
        [Sort::with_parameters("Vec", vec![Sort::new("3")])]
            .into_iter()
            .collect()
    );
    assert!(catalog.defined_heads().contains(&SortHead::nullary("3")));
    assert!(catalog.all_sorts().contains(&Sort::new("3")));
    assert!(!catalog.all_sorts().contains(&Sort::with_parameters(
        "Map",
        vec![Sort::new("K"), Sort::new("V")]
    )));
}

#[test]
fn numeral_instance_arguments_of_any_length_are_declared() {
    let declarations = ["4294967296", "8"].map(|name| {
        syntax_sort(
            Vec::new(),
            Sort::with_parameters("MInt", vec![Sort::new(name)]),
            Attributes::default(),
        )
    });
    let catalog = SortCatalog::from_visible(&declarations);

    for name in ["4294967296", "8"] {
        assert!(
            catalog.defined_heads().contains(&SortHead::nullary(name)),
            "{name} must be a defined head"
        );
        assert!(
            catalog.all_sorts().contains(&Sort::new(name)),
            "{name} must be a catalog sort"
        );
    }
}

#[test]
fn a_production_sort_with_a_nested_sort_parameter_is_no_instance() {
    // Property: `MInt{MInt{W}}` names one sort per `W`, so a production with that result declares
    // no instance of `MInt`, however deep its parameter sits.
    let w = Sort::new("W");
    let mint = |argument: Sort| Sort::with_parameters("MInt", vec![argument]);
    let declaration = syntax_sort(vec![w.clone()], mint(w.clone()), Attributes::default());
    let bar = syntax_sort(Vec::new(), Sort::new("Bar"), Attributes::default());
    let nest = Sentence::Production {
        label: Some(Label::new("nest")),
        parameters: vec![w.clone()],
        sort: mint(mint(w.clone())),
        items: vec![ProductionItem::NonTerminal {
            sort: Sort::new("Bar"),
            name: None,
        }],
        attributes: Attributes::default(),
    };
    let catalog = SortCatalog::from_visible([&declaration, &bar, &nest]);

    assert_eq!(
        catalog.instantiations().get(&SortHead::new("MInt", 1)),
        Some(&BTreeSet::new())
    );
    assert!(!catalog.all_sorts().contains(&mint(mint(w))));
}

#[test]
fn a_result_with_a_nested_parameter_is_not_a_declared_instance() {
    // Property: a production result is a declared instance iff no formal parameter of the
    // production occurs in it at any depth, so beside the ground declaration `MInt{8}` the
    // result `MInt{MInt{W}}` adds nothing to the instances of `MInt`.
    let w = Sort::new("W");
    let mint = |argument: Sort| Sort::with_parameters("MInt", vec![argument]);
    let nest = production(
        mint(mint(w.clone())),
        vec![w],
        Vec::new(),
        Attributes::default(),
    );
    let declaration = syntax_sort(Vec::new(), mint(Sort::new("8")), Attributes::default());
    let catalog = SortCatalog::from_visible([&nest, &declaration]);

    assert_eq!(
        catalog.instantiations()[&SortHead::new("MInt", 1)],
        BTreeSet::from([mint(Sort::new("8"))])
    );
}

#[test]
fn derives_synonym_hook_token_and_list_views() {
    let resolved = fixture();
    let catalog = resolved.sort_catalog(resolved.main_module_id());

    assert_eq!(
        catalog.sort_synonyms().spelling(&Sort::new("Nat")),
        Spelling::Synonym {
            denotes: &Sort::new("Int")
        }
    );
    assert_eq!(catalog.hooks().get("Int"), Some(&"INT.Int".into()));
    assert_eq!(
        catalog.token_sorts(),
        &[Sort::new("Int"), Sort::new("TokenFromProduction"),]
            .into_iter()
            .collect()
    );
    assert_eq!(
        catalog.list_sorts(),
        &[Sort::with_parameters("List", vec![Sort::new("Int")])]
            .into_iter()
            .collect()
    );
}

#[test]
fn local_sorts_exclude_every_sort_visible_through_direct_imports() {
    let resolved = fixture();
    let catalog = resolved.sort_catalog(resolved.main_module_id());

    assert!(!catalog.local_sorts().contains(&Sort::new("Int")));
    assert!(
        !catalog
            .local_sorts()
            .contains(&Sort::new("TokenFromProduction"))
    );
    assert!(
        catalog
            .local_sorts()
            .contains(&Sort::with_parameters("List", vec![Sort::new("Int")])),
    );
    assert_eq!(
        catalog.sorted_all_sorts().cloned().collect::<BTreeSet<_>>(),
        catalog.all_sorts().clone()
    );
}

#[test]
fn conflicting_sort_hooks_are_removed_by_attribute_merge() {
    let left = syntax_sort(
        Vec::new(),
        Sort::new("Conflict"),
        attrs(&[("hook", json!("LEFT.Hook"))]),
    );
    let right = syntax_sort(
        Vec::new(),
        Sort::new("Conflict"),
        attrs(&[("hook", json!("RIGHT.Hook"))]),
    );
    let catalog = SortCatalog::from_visible([&left, &right]);

    assert_eq!(
        catalog
            .declarations_for(&SortHead::nullary("Conflict"))
            .len(),
        2
    );
    assert_eq!(
        catalog
            .attributes_for(&SortHead::nullary("Conflict"))
            .unwrap()
            .get("hook"),
        None
    );
    assert!(!catalog.hooks().contains_key("Conflict"));
}

fn assert_declaring_sentence_indexes(
    parameters: Vec<Sort>,
    sort: Sort,
    heads: BTreeSet<SortHead>,
    instances: BTreeMap<SortHead, BTreeSet<Sort>>,
    all_sorts: BTreeSet<Sort>,
) {
    let declaration = syntax_sort(parameters.clone(), sort.clone(), Attributes::default());
    let result = production(sort, parameters, Vec::new(), Attributes::default());
    let declared = SortCatalog::from_visible([&declaration]);
    let produced = SortCatalog::from_visible([&result]);

    assert_eq!(declared.defined_heads(), produced.defined_heads());
    assert_eq!(declared.instantiations(), produced.instantiations());
    assert_eq!(declared.all_sorts(), produced.all_sorts());
    for catalog in [declared, produced] {
        assert_eq!(catalog.defined_heads(), &heads);
        assert_eq!(catalog.instantiations(), &instances);
        assert_eq!(catalog.all_sorts(), &all_sorts);
    }
}

#[test]
fn fu19_schematic_declarations_and_results_register_only_their_head() {
    let w = Sort::new("W");
    assert_declaring_sentence_indexes(
        vec![w.clone(), Sort::new("Unused")],
        Sort::with_parameters("MInt", vec![w]),
        BTreeSet::from([SortHead::new("MInt", 1)]),
        BTreeMap::from([(SortHead::new("MInt", 1), BTreeSet::new())]),
        BTreeSet::new(),
    );
}

#[test]
fn fu19_unused_binders_preserve_ground_declarations_and_results() {
    let mint8 = Sort::with_parameters("MInt", vec![Sort::new("8")]);
    assert_declaring_sentence_indexes(
        vec![Sort::new("W")],
        mint8.clone(),
        BTreeSet::from([SortHead::new("MInt", 1), SortHead::nullary("8")]),
        BTreeMap::from([(SortHead::new("MInt", 1), BTreeSet::from([mint8.clone()]))]),
        BTreeSet::from([mint8, Sort::new("8")]),
    );
}

#[test]
fn fu19_unused_binders_preserve_nullary_declarations_and_results() {
    assert_declaring_sentence_indexes(
        vec![Sort::new("W")],
        Sort::new("Foo"),
        BTreeSet::from([SortHead::nullary("Foo")]),
        BTreeMap::new(),
        BTreeSet::from([Sort::new("Foo")]),
    );
}

#[test]
fn fu19_bare_bound_declarations_and_results_register_nothing() {
    let s = Sort::new("S");
    assert_declaring_sentence_indexes(
        vec![s.clone()],
        s,
        BTreeSet::new(),
        BTreeMap::new(),
        BTreeSet::new(),
    );
}

#[test]
fn fu19_nested_unchecked_declarations_and_results_are_not_ground_instances() {
    let w = Sort::new("W");
    assert_declaring_sentence_indexes(
        vec![w.clone()],
        Sort::with_parameters("MInt", vec![Sort::with_parameters("MInt", vec![w])]),
        BTreeSet::from([SortHead::new("MInt", 1)]),
        BTreeMap::from([(SortHead::new("MInt", 1), BTreeSet::new())]),
        BTreeSet::new(),
    );
}

#[test]
fn fu19_mixed_declarations_are_order_independent_and_deduplicate_instances() {
    let w = Sort::new("W");
    let schematic = Sort::with_parameters("MInt", vec![w.clone()]);
    let ground = Sort::with_parameters("MInt", vec![Sort::new("8")]);
    let declaration = syntax_sort(vec![w.clone()], schematic.clone(), Attributes::default());
    let concrete = syntax_sort(vec![w.clone()], ground.clone(), Attributes::default());
    let result = production(
        schematic,
        vec![w.clone()],
        Vec::new(),
        Attributes::default(),
    );
    let ground_result = production(ground.clone(), vec![w], Vec::new(), Attributes::default());
    let sentences = [
        &declaration,
        &concrete,
        &concrete,
        &ground_result,
        &declaration,
        &result,
    ];
    let forward = SortCatalog::from_visible(sentences);
    let reverse = SortCatalog::from_visible(sentences.into_iter().rev());

    for catalog in [forward, reverse] {
        assert_eq!(
            catalog.sorted_defined_heads().cloned().collect::<Vec<_>>(),
            vec![SortHead::nullary("8"), SortHead::new("MInt", 1)]
        );
        assert_eq!(
            catalog.instantiations(),
            &BTreeMap::from([(SortHead::new("MInt", 1), BTreeSet::from([ground.clone()]))])
        );
        assert_eq!(
            catalog.sorted_all_sorts().cloned().collect::<Vec<_>>(),
            vec![Sort::new("8"), ground.clone()]
        );
    }
}

#[test]
fn fu19_schematic_heads_preserve_merged_attributes_without_instances() {
    let w = Sort::new("W");
    let sort = Sort::with_parameters("MInt", vec![w.clone()]);
    let hooked = syntax_sort(
        vec![w.clone()],
        sort.clone(),
        attrs(&[("hook", json!("MINT.MInt"))]),
    );
    let annotated = syntax_sort(vec![w], sort, attrs(&[("documentation", json!("width"))]));
    let catalog = SortCatalog::from_visible([&hooked, &annotated]);
    let head = SortHead::new("MInt", 1);

    assert_eq!(catalog.defined_heads(), &BTreeSet::from([head.clone()]));
    assert_eq!(catalog.instantiations().get(&head), Some(&BTreeSet::new()));
    assert!(catalog.all_sorts().is_empty());
    assert_eq!(catalog.declarations_for(&head), [&hooked, &annotated]);
    let attributes = catalog.attributes_for(&head).unwrap();
    assert_eq!(attributes.get("hook"), Some(&json!("MINT.MInt")));
    assert_eq!(attributes.get("documentation"), Some(&json!("width")));
    assert_eq!(catalog.hooks().get("MInt"), Some(&"MINT.MInt".into()));
}

#[test]
fn fu19_imported_ground_sorts_and_local_unused_binder_sorts_keep_membership() {
    let w = Sort::new("W");
    let ground = Sort::with_parameters("MInt", vec![Sort::new("8")]);
    let resolved = ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![
            FlatModule {
                name: "BASE".into(),
                imports: Vec::new(),
                local_sentences: vec![Arc::new(syntax_sort(
                    vec![w.clone()],
                    ground.clone(),
                    Attributes::default(),
                ))],
                attributes: Attributes::default(),
            },
            FlatModule {
                name: "MAIN".into(),
                imports: vec![FlatImport {
                    name: "BASE".into(),
                    public: true,
                }],
                local_sentences: vec![
                    Arc::new(syntax_sort(
                        vec![w.clone()],
                        Sort::with_parameters("MInt", vec![w.clone()]),
                        Attributes::default(),
                    )),
                    Arc::new(syntax_sort(
                        vec![w],
                        Sort::new("Foo"),
                        Attributes::default(),
                    )),
                ],
                attributes: Attributes::default(),
            },
        ],
        attributes: Attributes::default(),
    })
    .unwrap();
    let catalog = resolved.sort_catalog(resolved.main_module_id());

    assert_eq!(
        catalog.all_sorts(),
        &BTreeSet::from([ground.clone(), Sort::new("8"), Sort::new("Foo")])
    );
    assert_eq!(catalog.local_sorts(), &BTreeSet::from([Sort::new("Foo")]));
    assert_eq!(
        catalog.instantiations(),
        &BTreeMap::from([(SortHead::new("MInt", 1), BTreeSet::from([ground]))])
    );
}

#[test]
fn fu19_a_separate_global_declaration_can_share_a_binders_spelling() {
    let w = Sort::new("W");
    let bound = syntax_sort(vec![w.clone()], w.clone(), Attributes::default());
    let schematic = syntax_sort(
        vec![w.clone()],
        Sort::with_parameters("MInt", vec![w.clone()]),
        Attributes::default(),
    );
    let global = syntax_sort(Vec::new(), w.clone(), Attributes::default());
    let sentences = [&bound, &schematic, &global];

    for catalog in [
        SortCatalog::from_visible(sentences),
        SortCatalog::from_visible(sentences.into_iter().rev()),
    ] {
        assert_eq!(
            catalog.defined_heads(),
            &BTreeSet::from([SortHead::new("MInt", 1), SortHead::nullary("W")])
        );
        assert_eq!(
            catalog.instantiations(),
            &BTreeMap::from([(SortHead::new("MInt", 1), BTreeSet::new())])
        );
        assert_eq!(catalog.all_sorts(), &BTreeSet::from([w.clone()]));
    }
}

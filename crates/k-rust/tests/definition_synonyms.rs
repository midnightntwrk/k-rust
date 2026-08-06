use k_rust::definition::{
    Attributes, Definition, FlatImport, FlatModule, ProductionItem, ResolveError, Sentence,
    apply_sort_synonyms,
};
use k_rust::kast::{Label, Sort};
use proptest::prelude::*;

fn module(name: &str, imports: &[&str], sentences: Vec<Sentence>) -> FlatModule {
    FlatModule {
        name: name.into(),
        imports: imports
            .iter()
            .map(|name| FlatImport {
                name: (*name).into(),
                public: true,
            })
            .collect(),
        local_sentences: sentences,
        attributes: Attributes::default(),
    }
}

fn synonym(new_sort: Sort, old_sort: Sort) -> Sentence {
    Sentence::SortSynonym {
        new_sort,
        old_sort,
        attributes: Attributes::default(),
    }
}

#[test]
fn applies_visible_synonyms_once_to_only_production_sorts() {
    let alias = Sort::new("Alias");
    let expression = Sort::new("Exp");
    let term = Sort::new("Term");
    let wrapper = Sort::with_parameters("Wrapper", vec![alias.clone()]);
    let parameter = Sort::new("S");
    let production_attributes = {
        let mut attributes = Attributes::default();
        attributes.insert("marker", serde_json::json!("preserved"));
        attributes
    };
    let production = Sentence::Production {
        label: Some(Label::new("wrap")),
        parameters: vec![parameter.clone(), alias.clone()],
        sort: alias.clone(),
        items: vec![
            ProductionItem::Terminal("[".into()),
            ProductionItem::NonTerminal {
                sort: alias.clone(),
                name: Some("value".into()),
            },
            ProductionItem::NonTerminal {
                sort: wrapper.clone(),
                name: None,
            },
            ProductionItem::regex("[a-z]+"),
        ],
        attributes: production_attributes.clone(),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module(
                "BASE",
                &[],
                vec![
                    synonym(alias.clone(), expression.clone()),
                    synonym(expression.clone(), term),
                ],
            ),
            module("MAIN", &["BASE"], vec![production]),
        ],
        attributes: Attributes::default(),
    };

    let transformed = apply_sort_synonyms(&definition).unwrap();
    let main = transformed.main_module().unwrap();
    let Sentence::Production {
        label,
        parameters,
        sort,
        items,
        attributes,
    } = &main.local_sentences[0]
    else {
        panic!("expected production")
    };

    assert_eq!(label.as_ref().unwrap().name, "wrap");
    assert_eq!(parameters, &[parameter, alias.clone()]);
    assert_eq!(sort, &expression, "synonyms are applied only once");
    assert_eq!(attributes, &production_attributes);
    assert_eq!(
        items,
        &[
            ProductionItem::Terminal("[".into()),
            ProductionItem::NonTerminal {
                sort: expression,
                name: Some("value".into()),
            },
            ProductionItem::NonTerminal {
                sort: wrapper,
                name: None,
            },
            ProductionItem::regex("[a-z]+"),
        ]
    );
    assert_eq!(
        transformed.modules[0].local_sentences, definition.modules[0].local_sentences,
        "sort-synonym declarations are syntax and remain unchanged"
    );

    insta::assert_debug_snapshot!(transformed);
}

#[test]
fn matches_only_the_entire_parameterized_sort() {
    let int = Sort::new("Int");
    let bool_sort = Sort::new("Bool");
    let alias_int = Sort::with_parameters("Alias", vec![int.clone()]);
    let alias_bool = Sort::with_parameters("Alias", vec![bool_sort]);
    let target = Sort::new("Target");
    let nested = Sort::with_parameters("Box", vec![alias_int.clone()]);
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            &[],
            vec![
                synonym(alias_int.clone(), target.clone()),
                Sentence::Production {
                    label: None,
                    parameters: vec![],
                    sort: alias_int,
                    items: vec![
                        ProductionItem::NonTerminal {
                            sort: alias_bool.clone(),
                            name: None,
                        },
                        ProductionItem::NonTerminal {
                            sort: nested.clone(),
                            name: None,
                        },
                    ],
                    attributes: Attributes::default(),
                },
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = apply_sort_synonyms(&definition).unwrap();
    let Sentence::Production { sort, items, .. } = &transformed.modules[0].local_sentences[1]
    else {
        panic!("expected production")
    };
    assert_eq!(sort, &target);
    assert_eq!(
        items,
        &[
            ProductionItem::NonTerminal {
                sort: alias_bool,
                name: None,
            },
            ProductionItem::NonTerminal {
                sort: nested,
                name: None,
            },
        ]
    );
}

#[test]
fn does_not_apply_synonyms_from_modules_outside_the_import_closure() {
    let alias = Sort::new("Alias");
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module(
                "HIDDEN",
                &[],
                vec![synonym(alias.clone(), Sort::new("Hidden"))],
            ),
            module(
                "MAIN",
                &[],
                vec![Sentence::Production {
                    label: None,
                    parameters: vec![],
                    sort: alias.clone(),
                    items: vec![],
                    attributes: Attributes::default(),
                }],
            ),
        ],
        attributes: Attributes::default(),
    };

    let transformed = apply_sort_synonyms(&definition).unwrap();
    let Sentence::Production { sort, .. } = &transformed.main_module().unwrap().local_sentences[0]
    else {
        panic!("expected production")
    };
    assert_eq!(sort, &alias);
}

#[test]
fn reports_resolution_errors_before_transforming() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module("MAIN", &["MISSING"], vec![])],
        attributes: Attributes::default(),
    };

    assert_eq!(
        apply_sort_synonyms(&definition),
        Err(ResolveError::MissingImport {
            module: "MAIN".into(),
            import: "MISSING".into(),
        })
    );
}

proptest! {
    #[test]
    fn synonym_application_is_an_exact_non_recursive_lookup(
        alias_name in "[A-Z][A-Za-z0-9]{0,7}",
        target_name in "[A-Z][A-Za-z0-9]{0,7}",
        other_name in "[A-Z][A-Za-z0-9]{0,7}",
    ) {
        prop_assume!(alias_name != target_name);
        prop_assume!(alias_name != other_name);
        let alias = Sort::new(alias_name);
        let target = Sort::new(target_name);
        let other = Sort::new(other_name);
        let nested = Sort::with_parameters("Box", vec![alias.clone()]);
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![module(
                "MAIN",
                &[],
                vec![
                    synonym(alias.clone(), target.clone()),
                    Sentence::Production {
                        label: None,
                        parameters: vec![alias.clone()],
                        sort: alias,
                        items: vec![
                            ProductionItem::NonTerminal {
                                sort: other.clone(),
                                name: None,
                            },
                            ProductionItem::NonTerminal {
                                sort: nested.clone(),
                                name: None,
                            },
                        ],
                        attributes: Attributes::default(),
                    },
                ],
            )],
            attributes: Attributes::default(),
        };

        let transformed = apply_sort_synonyms(&definition).unwrap();
        let Sentence::Production {
            parameters,
            sort,
            items,
            ..
        } = &transformed.modules[0].local_sentences[1]
        else {
            panic!("expected production")
        };
        prop_assert_eq!(sort, &target);
        prop_assert_eq!(parameters, match &definition.modules[0].local_sentences[1] {
            Sentence::Production { parameters, .. } => parameters,
            _ => unreachable!(),
        });
        prop_assert_eq!(
            items,
            &vec![
                ProductionItem::NonTerminal {
                    sort: other,
                    name: None,
                },
                ProductionItem::NonTerminal {
                    sort: nested,
                    name: None,
                },
            ]
        );
    }
}

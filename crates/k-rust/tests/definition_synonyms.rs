use std::sync::Arc;

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
        local_sentences: sentences.into_iter().map(Arc::new).collect(),
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

fn load_synonym_source(
    source: &str,
) -> Result<k_rust::outer::LoadedDefinition, k_rust::outer::LoadError> {
    use k_rust::{
        builtin::embedded,
        outer::{LoadOptions, ResolvedSource, load_with_options},
    };
    load_with_options(
        ResolvedSource::new("synonym-attributes.k", source),
        "MAIN",
        &mut |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        },
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..Default::default()
        },
    )
}

#[test]
fn applies_chained_synonyms_to_sort_valued_attributes_of_loaded_sentences() {
    let loaded = load_synonym_source(
        r#"
        module MAIN
          imports INT
          syntax B = Int
          syntax R = B
          syntax Exp ::= f(Int) [strict, result(R), symbol(f)]
                       | h(Int) [hybrid(R, Bool), symbol(h)]
                       | plain(Int) [result(Int), symbol(plain)]
                       | bare(Int) [hybrid, symbol(bare)]
          syntax {R} R ::= "parameter" [result(R), hybrid(R), symbol(parameter)]
          rule f(1) => f(1) [heat, result(R)]
          context f(HOLE) [result(R)]
          context alias [a]: HERE [result(R)]
        endmodule
    "#,
    )
    .unwrap();
    let sentences = &loaded.definition().main_module().unwrap().local_sentences;
    let production = |name: &str| {
        sentences.iter().find(|sentence| {
        matches!(&***sentence, Sentence::Production { label: Some(label), .. } if label.name == name)
    }).unwrap().attributes()
    };
    assert_eq!(production("f").get_str("result"), Some("Int"));
    assert_eq!(production("h").get_str("hybrid"), Some("Int, Bool"));
    assert_eq!(production("plain").get_str("result"), Some("Int"));
    assert_eq!(production("bare").get_str("hybrid"), Some(""));
    assert_eq!(production("parameter").get_str("result"), Some("R"));
    assert_eq!(production("parameter").get_str("hybrid"), Some("R"));
    for kind in ["rule", "context", "context alias"] {
        let sentence = sentences
            .iter()
            .find(|sentence| match &***sentence {
                Sentence::Rule { .. } => kind == "rule",
                Sentence::Context { .. } => kind == "context",
                Sentence::ContextAlias { .. } => kind == "context alias",
                _ => false,
            })
            .unwrap();
        assert_eq!(
            sentence.attributes().get_str("result"),
            Some("Int"),
            "{kind}"
        );
    }
}

#[test]
fn sort_valued_attributes_use_the_declaring_modules_full_private_view() {
    let loaded = load_synonym_source(
        r#"
        module HIDDEN
          imports INT
          syntax R = Int
        endmodule
        module MAIN
          imports private HIDDEN
          syntax Exp ::= f(Int) [strict, result(R), hybrid(R, Bool), symbol(f)]
        endmodule
    "#,
    )
    .unwrap();
    let production = loaded.definition().main_module().unwrap().local_sentences.iter()
        .find(|sentence| matches!(&***sentence, Sentence::Production { label: Some(label), .. } if label.name == "f"))
        .unwrap();
    assert_eq!(production.attributes().get_str("result"), Some("Int"));
    assert_eq!(production.attributes().get_str("hybrid"), Some("Int, Bool"));
}

#[test]
fn a_cyclic_synonym_in_a_result_attribute_is_a_load_diagnostic() {
    let error = load_synonym_source(
        r#"
        module MAIN
          imports INT
          syntax A = A
          syntax Exp ::= f(Int) [strict, result(A), symbol(f)]
        endmodule
    "#,
    )
    .unwrap_err();
    let k_rust::outer::LoadError::SourceDiagnostics(diagnostics) = error else {
        panic!("expected InvalidSortSynonym source diagnostics: {error:?}");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.code == k_rust::diagnostic::DiagnosticCode::InvalidSortSynonym
        }),
        "{diagnostics:?}"
    );
}

#[test]
fn applies_the_end_of_each_synonym_chain_to_only_production_sorts() {
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
        parameters: vec![parameter.clone()],
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
                    synonym(expression.clone(), term.clone()),
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
    } = &*main.local_sentences[0]
    else {
        panic!("expected production")
    };

    assert_eq!(label.as_ref().unwrap().name, "wrap");
    assert_eq!(parameters, &[parameter]);
    assert_eq!(sort, &term);
    assert_eq!(attributes, &production_attributes);
    assert_eq!(
        items,
        &[
            ProductionItem::Terminal("[".into()),
            ProductionItem::NonTerminal {
                sort: term,
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
    let Sentence::Production { sort, items, .. } = &*transformed.modules[0].local_sentences[1]
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
    let Sentence::Production { sort, .. } = &*transformed.main_module().unwrap().local_sentences[0]
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

#[test]
fn a_production_parameter_shadows_a_synonym_of_its_spelling() {
    let alias = Sort::new("Alias");
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module("BASE", &[], vec![synonym(alias.clone(), Sort::new("Exp"))]),
            module(
                "MAIN",
                &["BASE"],
                vec![Sentence::Production {
                    label: None,
                    parameters: vec![alias.clone()],
                    sort: alias.clone(),
                    items: vec![ProductionItem::NonTerminal {
                        sort: alias.clone(),
                        name: None,
                    }],
                    attributes: Attributes::default(),
                }],
            ),
        ],
        attributes: Attributes::default(),
    };

    let transformed = apply_sort_synonyms(&definition).unwrap();
    let Sentence::Production {
        parameters,
        sort,
        items,
        ..
    } = &*transformed.main_module().unwrap().local_sentences[0]
    else {
        panic!("expected production")
    };
    assert_eq!(parameters.as_slice(), std::slice::from_ref(&alias));
    assert_eq!(sort, &alias);
    assert_eq!(
        items,
        &[ProductionItem::NonTerminal {
            sort: alias,
            name: None
        }]
    );
}

#[test]
fn undenoted_synonyms_are_left_in_place() {
    let alias = Sort::new("A");
    let referent = Sort::new("B");
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            &[],
            vec![
                synonym(alias.clone(), referent.clone()),
                synonym(referent, alias.clone()),
                Sentence::Production {
                    label: None,
                    parameters: vec![],
                    sort: alias.clone(),
                    items: vec![ProductionItem::NonTerminal {
                        sort: alias.clone(),
                        name: None,
                    }],
                    attributes: Attributes::default(),
                },
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = apply_sort_synonyms(&definition).unwrap();
    let Sentence::Production { sort, items, .. } = &*transformed.modules[0].local_sentences[2]
    else {
        panic!("expected production")
    };
    assert_eq!(sort, &alias);
    assert_eq!(
        items,
        &[ProductionItem::NonTerminal {
            sort: alias,
            name: None
        }]
    );
}

proptest! {
    #[test]
    fn synonym_application_follows_chains_and_is_idempotent(
        names in prop::collection::btree_set("[A-Z][A-Za-z0-9]{0,7}", 2..=5),
    ) {
        let names = names.into_iter().map(Sort::new).collect::<Vec<_>>();
        let alias = names.first().unwrap().clone();
        let target = names.last().unwrap().clone();
        let nested = Sort::with_parameters("Box", vec![alias.clone()]);
        let mut sentences = names.windows(2).rev()
            .map(|pair| synonym(pair[0].clone(), pair[1].clone()))
            .collect::<Vec<_>>();
        sentences.push(Sentence::Production {
            label: None,
            parameters: vec![],
            sort: alias.clone(),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: alias,
                    name: None,
                },
                ProductionItem::NonTerminal {
                    sort: nested.clone(),
                    name: None,
                },
            ],
            attributes: Attributes::default(),
        });
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![module("MAIN", &[], sentences)],
            attributes: Attributes::default(),
        };

        let transformed = apply_sort_synonyms(&definition).unwrap();
        let Sentence::Production { parameters, sort, items, .. } =
            &**transformed.modules[0].local_sentences.last().unwrap()
        else {
            panic!("expected production")
        };
        prop_assert_eq!(sort, &target);
        prop_assert!(parameters.is_empty());
        prop_assert_eq!(
            items,
            &vec![
                ProductionItem::NonTerminal {
                    sort: target,
                    name: None,
                },
                ProductionItem::NonTerminal {
                    sort: nested,
                    name: None,
                },
            ]
        );
        prop_assert_eq!(apply_sort_synonyms(&transformed).unwrap(), transformed);
    }
}

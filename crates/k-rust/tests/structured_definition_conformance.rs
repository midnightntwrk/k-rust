use std::collections::BTreeMap;

#[cfg(feature = "z3-inference")]
use k_rust::{
    builtin::embedded,
    outer::{LoadOptions, ResolvedSource, load_structured, load_with_options},
};
use k_rust::{
    definition::{
        Attributes, Definition, FlatModule, ProductionItem, ResolvedDefinition, Sentence,
    },
    kast::{Label, Sort, Term},
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::parser::parse_definition,
    outer::LoadedDefinition,
};
use serde_json::json;

#[test]
fn reference_bracket_symbol_fixture_matches_k_parsed_json() {
    // reference: kompile test.k --backend haskell --emit-json
    let source = include_str!("fixtures/reference/outer/bracket-symbol/test.k");
    let expected: serde_json::Value = serde_json::from_str(include_str!(
        "fixtures/reference/outer/bracket-symbol/bracket-label.json"
    ))
    .unwrap();
    let parsed = k_rust::outer::parse("bracket-symbol.k", source).unwrap();
    let definition = k_rust::outer::lower(&parsed, "BRACKET-SYMBOL").unwrap();
    let actual = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Production { attributes, .. }
                if attributes.get_str("symbol") == Some("paren") =>
            {
                attributes.get("bracketLabel")
            }
            _ => None,
        })
        .expect("the reference bracket production should be lowered");

    assert_eq!(actual, &expected);
}

#[test]
fn hand_built_definition_conforms_to_the_complete_public_compiler_pipeline() {
    assert_compiles_on_both_backends(structured_definition(false), |artifacts| {
        assert!(artifacts.definition_kore.contains("SortExp"));
        assert_eq!(artifacts.macros_kore, "\n");
    });
}

#[test]
fn structured_configuration_compiles_through_the_public_pipeline() {
    assert_compiles_on_both_backends(structured_definition(true), |artifacts| {
        assert!(
            artifacts.definition_kore.contains("'-LT-'top'-GT-'"),
            "{}",
            artifacts.definition_kore
        );
        assert!(
            artifacts
                .definition_kore
                .contains("LblinitGeneratedTopCell"),
            "{}",
            artifacts.definition_kore
        );
    });
}

#[cfg(feature = "z3-inference")]
#[test]
fn load_structured_compiles_an_authored_instrs_configuration() {
    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        let loaded = load_structured(
            structured_definition_with_configuration_cell("instrs"),
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                excluded_module_attributes: vec![backend.excluded_module_attribute().into()],
                ..LoadOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend} rejected structured loading: {error}"));

        assert!(loaded.definition.modules.iter().all(|module| {
            module.name != "DEFAULT-CONFIGURATION"
                && module
                    .imports
                    .iter()
                    .all(|import| import.name != "DEFAULT-CONFIGURATION")
        }));

        let artifacts = compile_loaded_definition(
            &loaded,
            CompileOptions {
                backend,
                ..CompileOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend} rejected structured input: {error:#?}"));
        assert!(artifacts.definition_kore.contains("instrs"));
        assert!(!artifacts.definition_kore.contains("Lbl'-LT-'k'-GT-'"));
    }
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

/// `syntax Int ::= "<name>(" <Collection> "," <Key> ")" [function, symbol(<name>)]`
fn collection_function(name: &str, collection: &str, key: &str) -> Sentence {
    Sentence::Production {
        label: Some(Label::new(name)),
        parameters: Vec::new(),
        sort: Sort::new("Int"),
        items: vec![
            ProductionItem::Terminal(format!("{name}(")),
            ProductionItem::NonTerminal {
                sort: Sort::new(collection),
                name: None,
            },
            ProductionItem::Terminal(",".into()),
            ProductionItem::NonTerminal {
                sort: Sort::new(key),
                name: None,
            },
            ProductionItem::Terminal(")".into()),
        ],
        attributes: Attributes::new(BTreeMap::from([("function".into(), json!(""))])),
    }
}

/// `rule <name>(C, K) => #SemanticCastToInt(<lookup>(C, K))`
fn semantic_downcast_equation(name: &str, lookup: &str, collection: &str, key: &str) -> Sentence {
    let variable = |name: &str, sort: &str| Term::Variable {
        name: name.into(),
        sort: Some(Sort::new(sort)),
    };
    let arguments = || vec![variable("C", collection), variable("K", key)];
    Sentence::Rule {
        body: Term::Rewrite {
            left: Box::new(Term::apply(name, arguments())),
            right: Box::new(Term::apply(
                "#SemanticCastToInt",
                vec![Term::apply(lookup, arguments())],
            )),
        },
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    }
}

/// The patterns of the equation axioms whose left side applies `name`.
fn equation_patterns(definition_kore: &str, name: &str) -> Vec<String> {
    let head = format!("\\equals{{SortInt{{}}, R}}(Lbl{name}{{}}(");
    parse_definition(definition_kore)
        .unwrap()
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            k_rust::kore::ast::Sentence::Axiom { pattern, .. } => {
                Some(k_rust::kore::printer::Printer::pretty(usize::MAX).print_pattern(pattern))
            }
            _ => None,
        })
        .filter(|pattern| pattern.contains(&head))
        .collect()
}

#[test]
fn a_semantic_downcast_equation_is_an_equation_of_its_function() {
    for (name, lookup, collection, key) in [
        ("f", "List:get", "List", "Int"),
        ("g", "Map:lookup", "Map", "KItem"),
    ] {
        let lookup_production = Sentence::Production {
            label: Some(Label::new(lookup)),
            parameters: Vec::new(),
            sort: Sort::new("KItem"),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: Sort::new(collection),
                    name: None,
                },
                ProductionItem::Terminal("[".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new(key),
                    name: None,
                },
                ProductionItem::Terminal("]".into()),
            ],
            attributes: Attributes::new(BTreeMap::from([("function".into(), json!(""))])),
        };
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: vec![
                    Sentence::Production {
                        label: None,
                        parameters: Vec::new(),
                        sort: Sort::new("Int"),
                        items: vec![ProductionItem::regex("[0-9]+")],
                        attributes: Attributes::new(BTreeMap::from([("token".into(), json!(""))])),
                    },
                    Sentence::SyntaxSort {
                        parameters: Vec::new(),
                        sort: Sort::new(collection),
                        attributes: Attributes::default(),
                    },
                    lookup_production,
                    collection_function(name, collection, key),
                    semantic_downcast_equation(name, lookup, collection, key),
                ]
                .into_iter()
                .map(std::sync::Arc::new)
                .collect(),
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        };
        assert_compiles_on_both_backends(definition, |artifacts| {
            let equations = equation_patterns(&artifacts.definition_kore, name);
            assert_eq!(equations.len(), 1, "{equations:#?}");
            assert!(
                equations[0].contains("\\and{SortInt{}}(Lblproject'Coln'Int{}("),
                "{}",
                equations[0]
            );
        });
    }
}

#[cfg(feature = "z3-inference")]
#[test]
fn load_structured_semantic_downcast_equation_matches_the_source_projection_cast() {
    for (name, lookup, collection, key, source_rule) in [
        (
            "f",
            "List:get",
            "List",
            "Int",
            "rule f(C, K) => {C[K]}:>Int",
        ),
        (
            "g",
            "Map:lookup",
            "Map",
            "KItem",
            "rule g(C, K) => {C[K]}:>Int",
        ),
    ] {
        for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
            let options = LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                excluded_module_attributes: vec![backend.excluded_module_attribute().into()],
                ..LoadOptions::default()
            };
            let compile_options = || CompileOptions {
                backend,
                ..CompileOptions::default()
            };
            let structured = load_structured(
                Definition {
                    main_module: "MAIN".into(),
                    modules: vec![FlatModule {
                        name: "MAIN".into(),
                        imports: vec![k_rust::definition::FlatImport {
                            name: "DOMAINS".into(),
                            public: true,
                        }],
                        local_sentences: vec![
                            collection_function(name, collection, key),
                            semantic_downcast_equation(name, lookup, collection, key),
                        ]
                        .into_iter()
                        .map(std::sync::Arc::new)
                        .collect(),
                        attributes: Attributes::default(),
                    }],
                    attributes: Attributes::default(),
                },
                &options,
            )
            .unwrap_or_else(|error| panic!("{backend} rejected structured loading: {error}"));
            let structured = compile_loaded_definition(&structured, compile_options())
                .unwrap_or_else(|error| panic!("{backend} rejected {lookup}: {error}"));

            let source = format!(
                "module MAIN\n  imports DOMAINS\n  syntax Int ::= \"{name}(\" {collection} \",\" {key} \")\" [function, symbol({name})]\n  {source_rule}\nendmodule\n"
            );
            let mut resolver = |_: &str, required: &str| {
                embedded(required).ok_or_else(|| format!("unexpected require {required}"))
            };
            let from_source = load_with_options(
                ResolvedSource::new("source.k", &source),
                "MAIN",
                &mut resolver,
                &options,
            )
            .unwrap_or_else(|error| panic!("{backend} rejected source loading: {error}"));
            let from_source = compile_loaded_definition(&from_source, compile_options())
                .unwrap_or_else(|error| panic!("{backend} rejected {source_rule}: {error}"));

            let structured = equation_patterns(&structured.definition_kore, name);
            let from_source = equation_patterns(&from_source.definition_kore, name);
            assert_eq!(structured.len(), 1, "{backend} {lookup}: {structured:#?}");
            assert_eq!(structured, from_source, "{backend} {lookup}");
        }
    }
}

fn assert_compiles_on_both_backends(
    definition: Definition,
    assert_artifacts: impl Fn(&k_rust::kompile::CompiledKoreArtifacts),
) {
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let loaded = LoadedDefinition {
        files: Vec::new(),
        source_table: Default::default(),
        definition,
        resolved,
        diagnostics: Vec::new(),
    };

    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        let artifacts = compile_loaded_definition(
            &loaded,
            CompileOptions {
                backend,
                ..CompileOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend} rejected structured input: {error:#?}"));

        assert!(parse_definition(&artifacts.definition_kore).is_ok());
        assert!(parse_definition(&artifacts.syntax_definition_kore).is_ok());
        assert_artifacts(&artifacts);
    }
}

fn structured_definition(with_configuration: bool) -> Definition {
    structured_definition_with_optional_configuration_cell(
        with_configuration.then_some("top"),
        with_configuration,
    )
}

#[cfg(feature = "z3-inference")]
fn structured_definition_with_configuration_cell(cell: &str) -> Definition {
    structured_definition_with_optional_configuration_cell(Some(cell), false)
}

fn structured_definition_with_optional_configuration_cell(
    configuration_cell: Option<&str>,
    declare_map_lookup: bool,
) -> Definition {
    let mut local_sentences = vec![
        Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("Int"),
            items: vec![ProductionItem::regex("[0-9]+")],
            attributes: Attributes::new(BTreeMap::from([("token".into(), json!(""))])),
        },
        Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("Exp"),
            items: vec![ProductionItem::NonTerminal {
                sort: Sort::new("Int"),
                name: None,
            }],
            attributes: Attributes::default(),
        },
    ];
    if declare_map_lookup {
        // Configuration initializers read their variables from the configuration map. Structured
        // callers currently supply that builtin closure themselves; this minimal declaration is
        // the only prelude contract this fixture needs.
        local_sentences.push(Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("Map"),
            attributes: Attributes::default(),
        });
        local_sentences.push(Sentence::Production {
            label: Some(Label::new("Map:lookup")),
            parameters: Vec::new(),
            sort: Sort::new("KItem"),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: Sort::new("Map"),
                    name: None,
                },
                ProductionItem::NonTerminal {
                    sort: Sort::new("KItem"),
                    name: None,
                },
            ],
            attributes: Attributes::new(BTreeMap::from([("function".into(), json!(""))])),
        });
    }
    if let Some(configuration_cell) = configuration_cell {
        local_sentences.push(Sentence::Configuration {
            body: config_cell(
                configuration_cell,
                Term::apply(
                    "#SemanticCastToExp",
                    vec![Term::Token {
                        token: "$PGM".into(),
                        sort: Sort::new("KConfigVar"),
                    }],
                ),
            ),
            ensures: Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
            attributes: Attributes::default(),
        });
    }

    Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: local_sentences
                .into_iter()
                .map(std::sync::Arc::new)
                .collect(),
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    }
}

fn config_cell(name: &str, contents: Term) -> Term {
    let cell_name = || Term::Token {
        token: name.into(),
        sort: Sort::new("#CellName"),
    };
    Term::apply(
        "#configCell",
        vec![
            cell_name(),
            Term::apply("#cellPropertyListTerminator", vec![]),
            contents,
            cell_name(),
        ],
    )
}

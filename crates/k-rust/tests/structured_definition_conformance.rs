use std::collections::BTreeMap;

#[cfg(feature = "z3-inference")]
use k_rust::{
    builtin::embedded,
    outer::{LoadOptions, load_structured},
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
            local_sentences,
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

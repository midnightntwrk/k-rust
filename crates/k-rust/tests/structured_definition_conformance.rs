use std::collections::BTreeMap;

use k_rust::{
    builtin::embedded,
    outer::{LoadOptions, load_structured},
};
use k_rust::{
    definition::{
        Attributes, Definition, FlatImport, FlatModule, ProductionItem, ResolvedDefinition,
        Sentence,
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

/// A structured definition importing prelude modules loads through `load_structured` and
/// compiles on both backends to the same `definition.kore` in either build. The snapshot is the
/// digest of each backend's `definition.kore`, recorded by the z3-inference build and asserted
/// by the portable build.
#[test]
fn structured_definition_importing_the_prelude_compiles_to_the_same_kore_in_both_builds() {
    let mut definition = structured_definition(false);
    definition.modules[0].imports = ["INT", "BOOL", "MAP", "LIST", "SET"]
        .into_iter()
        .map(|name| FlatImport {
            name: name.into(),
            public: false,
        })
        .collect();
    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        let excluded = backend.excluded_module_attribute();
        let loaded = load_structured(
            definition.clone(),
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                excluded_module_attributes: vec![excluded.into()],
                ..LoadOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend} rejected structured loading: {error}"));
        let artifacts = compile_loaded_definition(
            &loaded,
            CompileOptions {
                backend,
                ..CompileOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend} rejected structured input: {error:#?}"));
        assert!(parse_definition(&artifacts.definition_kore).is_ok());
        let digest = artifact_digest(
            &format!("structured-prelude-{backend}.kore"),
            &artifacts.definition_kore,
        );
        insta::with_settings!({
            description => format!(
                "definition.kore of a structured MAIN importing INT, BOOL, MAP, LIST, SET with the embedded prelude, {backend} backend ({excluded} excluded)"
            ),
            omit_expression => true,
            prepend_module_to_snapshot => true,
            snapshot_suffix => backend.to_string(),
        }, {
            insta::assert_debug_snapshot!("structured_prelude_definition_kore", digest);
        });
    }
}

/// The size and SHA-256 of a large artifact. The artifact itself is written under the test
/// binary's temporary directory, where a mismatch can be diffed against the other build's copy.
#[derive(Debug)]
#[allow(dead_code)]
struct ArtifactDigest {
    bytes: usize,
    sha256: String,
}

fn artifact_digest(name: &str, text: &str) -> ArtifactDigest {
    use sha2::Digest;
    // A rerun under a type-inference mode writes its own copy.
    let mode = std::env::var("KRUST_TYPE_INFERENCE_MODE").map_or(String::new(), |mode| mode + "-");
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(mode + name);
    std::fs::write(&path, text).unwrap();
    eprintln!("{name}: {}", path.display());
    ArtifactDigest {
        bytes: text.len(),
        sha256: sha2::Sha256::digest(text.as_bytes())
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect(),
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

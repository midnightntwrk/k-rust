use std::collections::BTreeMap;

use k_rust::{
    definition::{
        Attributes, Definition, FlatModule, ProductionItem, ResolvedDefinition, Sentence,
    },
    kast::Sort,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::parser::parse_definition,
    outer::LoadedDefinition,
};
use serde_json::json;

#[test]
fn hand_built_definition_conforms_to_the_complete_public_compiler_pipeline() {
    let definition = structured_definition();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let loaded = LoadedDefinition {
        files: Vec::new(),
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
        .unwrap_or_else(|error| panic!("{backend} rejected structured input at {error}"));

        assert!(parse_definition(&artifacts.definition_kore).is_ok());
        assert!(parse_definition(&artifacts.syntax_definition_kore).is_ok());
        assert!(artifacts.definition_kore.contains("SortExp"));
        assert_eq!(artifacts.macros_kore, "\n");
    }
}

fn structured_definition() -> Definition {
    Definition {
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
            ],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    }
}

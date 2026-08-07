use k_rust::definition::{Attributes, Definition, FlatModule, ProductionItem, Sentence};
use k_rust::inner::{ConfigError, resolve_configuration_bubbles};
use k_rust::kast::{Label, Sort};
use proptest::prelude::*;

fn definition(contents: &str) -> Definition {
    let mut token_attributes = Attributes::default();
    token_attributes.insert("token", serde_json::json!(""));
    Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: vec![],
            local_sentences: vec![
                Sentence::Production {
                    label: None,
                    parameters: vec![],
                    sort: Sort::new("Int"),
                    items: vec![ProductionItem::regex("[0-9]+")],
                    attributes: token_attributes,
                },
                Sentence::Bubble {
                    sentence_type: "config".into(),
                    contents: contents.into(),
                    attributes: Attributes::default(),
                },
            ],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    }
}

#[test]
fn parses_nested_cells_properties_casts_and_ensures() {
    let transformed = resolve_configuration_bubbles(&definition(
        r#"<top multiplicity="1"><k> $PGM:Int </k><counter> 0 </counter></top> ensures true"#,
    ))
    .unwrap();

    insta::assert_debug_snapshot!(transformed);
    assert!(matches!(
        transformed.main_module().unwrap().local_sentences[1],
        Sentence::Configuration { .. }
    ));
}

#[test]
fn preserves_external_cells() {
    let transformed = resolve_configuration_bubbles(&definition("<shared/>")).unwrap();
    let Sentence::Configuration { body, .. } =
        &transformed.main_module().unwrap().local_sentences[1]
    else {
        panic!("expected configuration")
    };
    assert!(matches!(
        body,
        k_rust::kast::Term::Apply { label, arguments }
            if label == &Label::new("#externalCell") && arguments.len() == 1
    ));
}

#[test]
fn parses_chained_casts_and_empty_bags() {
    let transformed = resolve_configuration_bubbles(&definition(
        "<top><k> $PGM:Int:K </k><cells> .Bag </cells></top>",
    ))
    .unwrap();

    insta::assert_debug_snapshot!(
        "chained_casts_and_empty_bags",
        &transformed.main_module().unwrap().local_sentences[1]
    );
}

#[test]
fn rejects_requires_clauses_after_parsing_them() {
    assert!(matches!(
        resolve_configuration_bubbles(&definition("<k> 0 </k> requires true")),
        Err(ConfigError::IllegalRequires { module, .. }) if module == "MAIN"
    ));
}

#[test]
fn configuration_grammar_includes_imported_productions() {
    let mut input = definition("<k> zero </k>");
    input.modules.insert(
        0,
        FlatModule {
            name: "BASE".into(),
            imports: vec![],
            local_sentences: vec![Sentence::Production {
                label: Some(Label::new("zero")),
                parameters: vec![],
                sort: Sort::new("Exp"),
                items: vec![ProductionItem::Terminal("zero".into())],
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        },
    );
    input.modules[1]
        .imports
        .push(k_rust::definition::FlatImport {
            name: "BASE".into(),
            public: true,
        });

    let transformed = resolve_configuration_bubbles(&input).unwrap();
    let Sentence::Configuration { body, .. } =
        &transformed.main_module().unwrap().local_sentences[1]
    else {
        panic!("expected configuration")
    };
    let mut labels = Vec::new();
    body.visit_preorder(&mut |term| {
        if let k_rust::kast::Term::Apply { label, .. } = term {
            labels.push(label.name.clone());
        }
    });
    assert!(labels.contains(&"zero".to_owned()));
}

proptest! {
    #[test]
    fn arbitrary_configuration_bubbles_never_panic(contents in any::<String>()) {
        let _ = resolve_configuration_bubbles(&definition(&contents));
    }
}

use k_rust::definition::{Attributes, Definition, FlatModule, ProductionItem, Sentence};
use k_rust::inner::{ConfigError, resolve_configuration_bubbles};
use k_rust::kast::{Label, Sort};
use proptest::prelude::*;

macro_rules! assert_config_snapshot {
    ($source:expr, $value:expr) => {{
        let source = $source;
        let value = &$value;
        insta::with_settings!({
            description => format!("Configuration bubble:\n\n{source}"),
            omit_expression => true,
            prepend_module_to_snapshot => true,
        }, {
            insta::assert_debug_snapshot!(value);
        });
    }};
}

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
    let source =
        r#"<top multiplicity="1"><k> $PGM:Int </k><counter> 0 </counter></top> ensures true"#;
    let transformed = resolve_configuration_bubbles(&definition(source)).unwrap();

    assert_config_snapshot!(source, transformed);
    assert!(matches!(
        transformed.main_module().unwrap().local_sentences[1],
        Sentence::Configuration { .. }
    ));
}

#[test]
fn declared_kconfigvar_does_not_create_a_reflexive_subsort_bridge() {
    let mut input = definition("<k> $PGM:Int </k>");
    input.modules[0].local_sentences.insert(
        0,
        Sentence::SyntaxSort {
            parameters: vec![],
            sort: Sort::new("KConfigVar"),
            attributes: Attributes::default(),
        },
    );

    resolve_configuration_bubbles(&input).unwrap();
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
        body.unannotated(),
        k_rust::kast::Term::Apply { label, arguments }
            if label == &Label::new("#externalCell") && arguments.len() == 1
    ));
}

#[test]
fn parses_chained_casts_and_empty_bags() {
    let source = "<top><k> $PGM:Int:K </k><cells> .Bag </cells></top>";
    let transformed = resolve_configuration_bubbles(&definition(source)).unwrap();

    assert_config_snapshot!(
        source,
        &transformed.main_module().unwrap().local_sentences[1]
    );
}

#[test]
fn parses_record_productions_in_configurations() {
    let source = "<k> pair(... left: 1) </k>";
    let mut input = definition(source);
    input.modules[0].local_sentences.insert(
        1,
        Sentence::Production {
            label: Some(Label::new("pair")),
            parameters: vec![],
            sort: Sort::new("Pair"),
            items: vec![
                ProductionItem::Terminal("pair".into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("Int"),
                    name: Some("left".into()),
                },
                ProductionItem::Terminal(",".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("Int"),
                    name: Some("right".into()),
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes: Attributes::default(),
        },
    );
    let transformed = resolve_configuration_bubbles(&input).unwrap();

    assert_config_snapshot!(
        source,
        &transformed.main_module().unwrap().local_sentences[2]
    );
}

#[test]
fn parses_literal_cell_names_that_are_also_user_terminals() {
    let source = "<value> .K </value>";
    let mut input = definition(source);
    input.modules[0].local_sentences.insert(
        1,
        Sentence::Production {
            label: Some(Label::new("value")),
            parameters: vec![],
            sort: Sort::new("Exp"),
            items: vec![ProductionItem::Terminal("value".into())],
            attributes: Attributes::default(),
        },
    );
    let transformed = resolve_configuration_bubbles(&input).unwrap();

    assert_config_snapshot!(
        source,
        &transformed.main_module().unwrap().local_sentences[2]
    );
}

#[test]
fn parses_uppercase_cell_names_without_treating_them_as_variables() {
    let source = "<T><k> $PGM:Int </k></T>";
    let transformed = resolve_configuration_bubbles(&definition(source)).unwrap();

    assert_config_snapshot!(
        source,
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

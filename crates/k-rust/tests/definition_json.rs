use std::collections::BTreeMap;

use k_rust::definition::json;
use k_rust::definition::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, ProductionItem, Sentence,
};
use k_rust::kast::{Label, Sort, Term};
use serde_json::{Value, json as value};

fn empty_attributes() -> Attributes {
    Attributes::default()
}

fn bool_token(token: &str) -> Term {
    Term::Token {
        token: token.into(),
        sort: Sort::new("Bool"),
    }
}

fn complete_definition(sentences: Vec<Sentence>) -> Definition {
    Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: vec![FlatImport {
                name: "PRELUDE".into(),
                public: true,
            }],
            local_sentences: sentences,
            attributes: empty_attributes(),
        }],
        attributes: empty_attributes(),
    }
}

macro_rules! assert_definition_round_trip {
    ($definition:expr) => {{
        let definition = $definition;
        let encoded = json::to_string_pretty(&definition).unwrap();
        assert_eq!(json::from_str(&encoded).unwrap(), definition);
        serde_json::from_str::<Value>(&encoded).unwrap()
    }};
}

#[test]
fn upstream_reduced_definition_round_trips_structurally() {
    let input = include_str!("fixtures/kast/definition.json");
    let definition = json::from_str(input).unwrap();
    let encoded = json::to_string(&definition).unwrap();

    assert_eq!(
        serde_json::from_str::<Value>(&encoded).unwrap(),
        serde_json::from_str::<Value>(input).unwrap()
    );
    assert_eq!(definition.main_module().unwrap().name, "IMP");

    let attributes = definition.modules[0].local_sentences[1].attributes();
    assert_eq!(attributes.source(), Some("imp.k"));
    assert_eq!(attributes.location().unwrap().start_line, 4);
}

#[test]
fn every_java_json_sentence_has_a_round_trip() {
    let empty = empty_attributes;
    let truth = || bool_token("true");
    let variable = || Term::variable("X");
    let sentences = vec![
        Sentence::SyntaxSort {
            parameters: vec![Sort::new("S")],
            sort: Sort::with_parameters("List", vec![Sort::new("S")]),
            attributes: empty(),
        },
        Sentence::SortSynonym {
            new_sort: Sort::new("Nat"),
            old_sort: Sort::new("Int"),
            attributes: empty(),
        },
        Sentence::SyntaxLexical {
            name: "Identifier".into(),
            regex: "[a-z][A-Za-z0-9]*".into(),
            attributes: empty(),
        },
        Sentence::Production {
            label: Some(Label::new("cons")),
            parameters: vec![Sort::new("S")],
            sort: Sort::new("List"),
            items: vec![
                ProductionItem::Terminal("[".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("S"),
                    name: Some("head".into()),
                },
                ProductionItem::regex("[ ]*"),
            ],
            attributes: empty(),
        },
        Sentence::SyntaxAssociativity {
            associativity: Associativity::Left,
            tags: vec!["plus".into()],
            attributes: empty(),
        },
        Sentence::SyntaxPriority {
            priorities: vec![vec!["times".into()], vec!["plus".into()]],
            attributes: empty(),
        },
        Sentence::Context {
            body: variable(),
            requires: truth(),
            attributes: empty(),
        },
        Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(variable()),
                right: Box::new(truth()),
            },
            requires: truth(),
            ensures: truth(),
            attributes: empty(),
        },
        Sentence::Claim {
            body: variable(),
            requires: truth(),
            ensures: truth(),
            attributes: empty(),
        },
        Sentence::Configuration {
            body: Term::apply("<k>", vec![variable()]),
            ensures: truth(),
            attributes: empty(),
        },
        Sentence::Bubble {
            sentence_type: "rule".into(),
            contents: "X => Y".into(),
            attributes: empty(),
        },
    ];

    let encoded = assert_definition_round_trip!(complete_definition(sentences));
    let sentence_nodes = encoded["term"]["modules"][0]["localSentences"]
        .as_array()
        .unwrap()
        .iter()
        .map(|sentence| sentence["node"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        sentence_nodes,
        vec![
            "KSyntaxSort",
            "KSortSynonym",
            "KSyntaxLexical",
            "KProduction",
            "KSyntaxAssociativity",
            "KSyntaxPriority",
            "KContext",
            "KRule",
            "KClaim",
            "KConfiguration",
            "KBubble",
        ]
    );
}

#[test]
fn preserves_unknown_and_typed_attributes() {
    let mut entries = BTreeMap::new();
    entries.insert("unknown-internal".into(), value!({"nested": [1, true]}));
    entries.insert("flag".into(), value!(""));
    let attributes = Attributes::new(entries);

    let definition = complete_definition(vec![Sentence::Bubble {
        sentence_type: "rule".into(),
        contents: "X".into(),
        attributes: attributes.clone(),
    }]);
    let encoded = json::to_string(&definition).unwrap();
    let decoded = json::from_str(&encoded).unwrap();

    assert_eq!(
        decoded.modules[0].local_sentences[0].attributes(),
        &attributes
    );
}

#[test]
fn rejects_non_unique_main_modules_and_unrepresentable_context_aliases() {
    let missing = complete_definition(Vec::new());
    let mut missing = missing;
    missing.main_module = "MISSING".into();
    let encoded = json::to_string(&missing).unwrap();
    assert!(matches!(
        json::from_str(&encoded),
        Err(json::Error::MissingMainModule(_))
    ));

    let alias = complete_definition(vec![Sentence::ContextAlias {
        body: Term::variable("X"),
        requires: bool_token("true"),
        attributes: empty_attributes(),
    }]);
    assert!(matches!(
        json::to_string(&alias),
        Err(json::Error::UnsupportedSentence("KContextAlias"))
    ));
}

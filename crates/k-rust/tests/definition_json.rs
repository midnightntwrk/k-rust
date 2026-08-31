use std::{collections::BTreeMap, sync::Arc};

use k_rust::definition::json;
use k_rust::definition::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, ProductionItem, Sentence,
};
use k_rust::kast::{Label, ResolvedProductionId, Sort, Term, TermMetadata, TermSpan};
use k_rust::provenance::{
    DestinationAnchor, GeneratingPass, LogicalSourceId, ORIGIN_ATTRIBUTE, OriginRecord,
    ProvenanceLink, SourceOffsetMap, SourceTable,
};
use serde::Deserialize;
use serde_json::{Value, json as value};

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProvenanceAttributeManifest {
    version: u32,
    representation: String,
    key_policy: String,
    duplicate_keys: String,
    source_order: String,
    value_kinds: Vec<String>,
    unsupported_sentence_forms: Vec<String>,
}

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

#[test]
fn provenance_export_round_trips_sources_attributes_and_term_metadata() {
    let mut sources = SourceTable::default();
    let source = sources.intern(LogicalSourceId::new("src/definition.k", b"module MAIN\n"));
    sources
        .set_offset_map(source, SourceOffsetMap::identity("module MAIN\n".len()))
        .unwrap();
    let span = TermSpan {
        source,
        start: 7,
        end: 11,
    };
    let origin = Arc::new(OriginRecord {
        pass: GeneratingPass::MacroExpansion,
        origins: vec![ProvenanceLink::Source { span }].into(),
        destination: Some(DestinationAnchor {
            module: "MAIN".into(),
            sentence: "subject".into(),
            sentence_index: 0,
            path: vec![0, 1],
        }),
    });
    let body = Term::apply(
        "f",
        vec![Term::variable("X").with_metadata(TermMetadata {
            span: Some(span),
            ..TermMetadata::default()
        })],
    )
    .with_metadata(TermMetadata {
        span: Some(span),
        production: Some(ResolvedProductionId(3)),
        sort: Some(Sort::new("Exp")),
        origin: Some(Arc::clone(&origin)),
    });
    let mut attributes = Attributes::new(BTreeMap::from([
        (
            k_rust::definition::SOURCE_ID_ATTRIBUTE.into(),
            value!(source.0),
        ),
        (
            "typed-values".into(),
            value!([null, true, 7, "text", {"x": 1}]),
        ),
    ]));
    attributes.insert(ORIGIN_ATTRIBUTE, origin.to_value());
    let definition = complete_definition(vec![Sentence::Rule {
        body,
        requires: bool_token("true"),
        ensures: bool_token("true"),
        attributes,
    }]);

    let encoded = json::to_provenance_string_pretty(&definition, &sources).unwrap();
    let envelope: Value = serde_json::from_str(&encoded).unwrap();
    assert_eq!(envelope["format"], json::PROVENANCE_FORMAT);
    assert_eq!(envelope["version"], json::PROVENANCE_VERSION);
    let wire_source = &envelope["sources"][0];
    assert_eq!(wire_source["logical"], "src/definition.k");
    assert_eq!(wire_source["contentHash"].as_str().unwrap().len(), 64);
    assert_eq!(
        wire_source["offsetMap"]["semanticLength"],
        "module MAIN\n".len()
    );
    let wire_identity = value!({
        "logical": wire_source["logical"],
        "contentHash": wire_source["contentHash"],
    });
    assert_eq!(
        &envelope["termMetadata"][0]["metadata"]["span"]["source"],
        &wire_identity
    );
    assert_eq!(
        &envelope["term"]["modules"][0]["localSentences"][0]["att"]["att"]
            [k_rust::definition::SOURCE_ID_ATTRIBUTE],
        &wire_identity
    );
    assert_eq!(
        &envelope["term"]["modules"][0]["localSentences"][0]["att"]["att"][ORIGIN_ATTRIBUTE]["origins"]
            [0]["source"],
        &wire_identity
    );
    let decoded = json::from_provenance_str(&encoded).unwrap();

    assert_eq!(decoded.source_table, sources);
    assert_eq!(decoded.definition, definition);
    let Sentence::Rule {
        body: decoded_body,
        attributes: decoded_attributes,
        ..
    } = &decoded.definition.modules[0].local_sentences[0]
    else {
        panic!("expected a rule")
    };
    let Sentence::Rule {
        body: expected_body,
        attributes: expected_attributes,
        ..
    } = &definition.modules[0].local_sentences[0]
    else {
        unreachable!()
    };
    assert_eq!(decoded_attributes.entries(), expected_attributes.entries());
    assert_eq!(decoded_body.metadata(), expected_body.metadata());
    let Term::Apply {
        arguments: decoded_arguments,
        ..
    } = decoded_body.unannotated()
    else {
        unreachable!()
    };
    let Term::Apply {
        arguments: expected_arguments,
        ..
    } = expected_body.unannotated()
    else {
        unreachable!()
    };
    assert_eq!(
        decoded_arguments[0].metadata(),
        expected_arguments[0].metadata()
    );
}

#[test]
fn provenance_attribute_manifest_matches_the_enforced_round_trip_subset() {
    let manifest: ProvenanceAttributeManifest =
        toml::from_str(include_str!("fixtures/provenance-attributes.toml"))
            .expect("provenance attribute manifest must be valid TOML");
    assert_eq!(manifest.version, 1, "unsupported manifest version");
    assert_eq!(manifest.representation, "unique-json-map");
    assert_eq!(manifest.key_policy, "any-unique-string");
    assert_eq!(manifest.duplicate_keys, "typed-rejection");
    assert_eq!(manifest.source_order, "canonical-key-order");
    assert_eq!(
        manifest.value_kinds,
        ["null", "boolean", "number", "string", "array", "object"]
    );
    assert_eq!(manifest.unsupported_sentence_forms, ["context-alias"]);

    let attributes = Attributes::new(BTreeMap::from([
        ("".into(), Value::Null),
        ("array".into(), value!([1, "two"])),
        ("boolean".into(), Value::Bool(true)),
        ("number".into(), value!(3.5)),
        ("object".into(), value!({"nested": false})),
        ("unicodé-key".into(), Value::String("text".into())),
    ]));
    let definition = complete_definition(vec![Sentence::Bubble {
        sentence_type: "rule".into(),
        contents: "X".into(),
        attributes: attributes.clone(),
    }]);
    let encoded = json::to_provenance_string(&definition, &SourceTable::default()).unwrap();
    let decoded = json::from_provenance_str(&encoded).unwrap();
    assert_eq!(
        decoded.definition.modules[0].local_sentences[0]
            .attributes()
            .entries(),
        attributes.entries()
    );

    let conflict = Attributes::merge([
        &Attributes::new(BTreeMap::from([("key".into(), value!(1))])),
        &Attributes::new(BTreeMap::from([("key".into(), value!(2))])),
    ])
    .expect_err("distinct duplicate values must be rejected");
    assert_eq!(conflict.conflicts[0].key, "key");

    let context_alias = complete_definition(vec![Sentence::ContextAlias {
        body: Term::variable("X"),
        requires: bool_token("true"),
        attributes: empty_attributes(),
    }]);
    assert!(matches!(
        json::to_provenance_string(&context_alias, &SourceTable::default()),
        Err(json::Error::UnsupportedSentence("KContextAlias"))
    ));
}

#[test]
fn provenance_export_rejects_malformed_source_attributes() {
    let definition = complete_definition(vec![Sentence::Bubble {
        sentence_type: "rule".into(),
        contents: "X".into(),
        attributes: Attributes::new(BTreeMap::from([(
            k_rust::definition::SOURCE_ID_ATTRIBUTE.into(),
            value!("not-an-index"),
        )])),
    }]);

    assert!(matches!(
        json::to_provenance_string(&definition, &SourceTable::default()),
        Err(json::Error::InvalidProvenance(_))
    ));
}

#[test]
fn provenance_decoder_rejects_malformed_wire_forms() {
    let mut sources = SourceTable::default();
    let source = sources.intern(LogicalSourceId::new("src/definition.k", b"X"));
    sources
        .set_offset_map(source, SourceOffsetMap::identity(1))
        .unwrap();
    let origin = OriginRecord {
        pass: GeneratingPass::MacroExpansion,
        origins: vec![ProvenanceLink::Source {
            span: TermSpan {
                source,
                start: 0,
                end: 1,
            },
        }]
        .into(),
        destination: None,
    };
    let definition = complete_definition(vec![Sentence::Rule {
        body: Term::variable("X").with_metadata(TermMetadata {
            origin: Some(Arc::new(origin.clone())),
            ..TermMetadata::default()
        }),
        requires: bool_token("true"),
        ensures: bool_token("true"),
        attributes: Attributes::new(BTreeMap::from([(
            ORIGIN_ATTRIBUTE.into(),
            origin.to_value(),
        )])),
    }]);
    let encoded = json::to_provenance_string(&definition, &sources).unwrap();
    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["unexpected"] = value!(true);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::Json(_))
    ));

    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["sources"][0]["offsetMap"]["unexpected"] = value!(true);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::Json(_))
    ));

    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["sources"][0]["offsetMap"]["segments"][0]["unexpected"] = value!(true);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::Json(_))
    ));

    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["sources"][0]["unexpected"] = value!(true);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::Json(_))
    ));

    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["termMetadata"][0]["metadata"]["origin"]["origins"][0]["unexpected"] = value!(true);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::Json(_))
    ));

    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["term"]["modules"][0]["localSentences"][0]["att"]["att"][ORIGIN_ATTRIBUTE]["origins"]
        [0]["unexpected"] = value!(true);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::Json(_))
    ));

    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["sources"] = value!([]);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::InvalidProvenance(_))
    ));

    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["sources"][0]["offsetMap"]["semanticLength"] = value!(2);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::InvalidProvenance(_))
    ));

    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["sources"][0]["offsetMap"] = value!({
        "semanticLength": 2,
        "rawLength": 2,
        "segments": [
            {"semanticStart": 0, "rawStart": 1, "length": 1},
            {"semanticStart": 1, "rawStart": 0, "length": 1}
        ]
    });
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::InvalidProvenance(_))
    ));

    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    let duplicate = envelope["termMetadata"][0].clone();
    envelope["termMetadata"]
        .as_array_mut()
        .unwrap()
        .push(duplicate);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::InvalidProvenance(_))
    ));
}

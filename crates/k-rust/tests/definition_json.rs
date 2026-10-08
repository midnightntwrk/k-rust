use std::{collections::BTreeMap, sync::Arc};

use k_rust::definition::json;
use k_rust::definition::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, ProductionItem, Sentence,
};
use k_rust::kast::{Label, ProductionIdentity, Sort, Term, TermMetadata, TermSpan};
use k_rust::outer::{LoadOptions, ResolvedSource, load_with_options};
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
            local_sentences: sentences.into_iter().map(std::sync::Arc::new).collect(),
            attributes: empty_attributes(),
        }],
        attributes: empty_attributes(),
    }
}

fn assert_term_metadata_equal(expected: &Term, actual: &Term) {
    assert_eq!(actual.metadata(), expected.metadata());
    match (expected.unannotated(), actual.unannotated()) {
        (
            Term::Rewrite {
                left: expected_left,
                right: expected_right,
            },
            Term::Rewrite {
                left: actual_left,
                right: actual_right,
            },
        )
        | (
            Term::As {
                pattern: expected_left,
                alias: expected_right,
            },
            Term::As {
                pattern: actual_left,
                alias: actual_right,
            },
        ) => {
            assert_term_metadata_equal(expected_left, actual_left);
            assert_term_metadata_equal(expected_right, actual_right);
        }
        (Term::Sequence(expected), Term::Sequence(actual))
        | (
            Term::Apply {
                arguments: expected,
                ..
            },
            Term::Apply {
                arguments: actual, ..
            },
        ) => {
            assert_eq!(actual.len(), expected.len());
            for (expected, actual) in expected.iter().zip(actual) {
                assert_term_metadata_equal(expected, actual);
            }
        }
        _ => {}
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
fn every_kast_json_sentence_kind_round_trips() {
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

    let mut definition = complete_definition(sentences);
    let encoded = assert_definition_round_trip!(definition.clone());
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

    definition.modules[0]
        .local_sentences
        .push(Arc::new(Sentence::ContextAlias {
            body: variable(),
            requires: truth(),
            attributes: empty(),
        }));
    let provenance = json::to_provenance_string(&definition, &SourceTable::default()).unwrap();
    assert_eq!(
        json::from_provenance_str(&provenance).unwrap().definition,
        definition
    );
}

#[test]
fn decodes_definitions_with_deep_rule_bodies() {
    let mut body = Term::variable("X");
    for _ in 0..300 {
        body = Term::apply("wrap", vec![body]);
    }
    let definition = complete_definition(vec![Sentence::Rule {
        body,
        requires: bool_token("true"),
        ensures: bool_token("true"),
        attributes: empty_attributes(),
    }]);

    let encoded = json::to_string(&definition).unwrap();
    assert_eq!(json::from_str(&encoded).unwrap(), definition);
}

/// A definition `k_rust` wrote reads back whatever the depth of its terms: a rule body 300
/// applications deep, which nests more than serde's recursion limit of JSON levels.
#[test]
fn decodes_provenance_definitions_with_deep_rule_bodies() {
    let definition = deep_rule_definition(300);
    let encoded = json::to_provenance_string(&definition, &SourceTable::default()).unwrap();
    assert_eq!(
        json::from_provenance_str(&encoded).unwrap().definition,
        definition
    );
}

/// The text of `encoded`, a document of [`deep_rule_definition`]`(1)`, with the rule body
/// replaced by `levels` applications of `wrap` around `X`.
fn deepen_rule_body(encoded: &str, levels: usize) -> String {
    let wrap = r#"{"node":"KApply","label":{"node":"KLabel","name":"wrap","params":[]},"arity":1,"args":["#;
    let leaf = r#"{"node":"KVariable","name":"X"}"#;
    let one = format!("{wrap}{leaf}]}}");
    assert_eq!(encoded.matches(&one).count(), 1, "{encoded}");
    encoded.replace(
        &one,
        &format!("{}{leaf}{}", wrap.repeat(levels), "]}".repeat(levels)),
    )
}

/// A definition whose one rule's body is `levels` applications of `wrap` around `X`.
fn deep_rule_definition(levels: usize) -> Definition {
    let mut body = Term::variable("X");
    for _ in 0..levels {
        body = Term::apply("wrap", vec![body]);
    }
    complete_definition(vec![Sentence::Rule {
        body,
        requires: bool_token("true"),
        ensures: bool_token("true"),
        attributes: empty_attributes(),
    }])
}

/// The number of applications of `wrap` the rule body of `definition` nests, counted without
/// recursion.
fn rule_body_depth(definition: &Definition) -> usize {
    let Sentence::Rule { body, .. } = definition.modules[0].local_sentences[0].as_ref() else {
        panic!("the sentence is a rule");
    };
    let mut depth = 0;
    let mut term = body;
    while let Term::Apply { arguments, .. } = term {
        depth += 1;
        term = &arguments[0];
    }
    depth
}

/// Run `work` on a thread of `bytes` of stack.
fn on_stack<T: Send + 'static>(bytes: usize, work: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(bytes)
        .spawn(work)
        .expect("the worker should spawn")
        .join()
        .expect("the worker should finish")
}

/// Both definition readers decode the terms of a document with explicit work stacks, and a term
/// is dropped with an explicit work list, so a definition whose rule body is 100,000
/// applications deep is read and dropped on a 1 MiB thread. Each document takes about 9 MB,
/// and the test peaks at about 210 MB of resident memory unoptimized (opt-level 0).
#[test]
fn definitions_of_any_depth_are_read_on_a_small_stack() {
    let levels = 100_000;
    let shallow = deep_rule_definition(1);
    let kast = deepen_rule_body(&json::to_string(&shallow).unwrap(), levels);
    let provenance = deepen_rule_body(
        &json::to_provenance_string(&shallow, &SourceTable::default()).unwrap(),
        levels,
    );
    on_stack(1 << 20, move || {
        let from_kast = json::from_str(&kast).expect("the KAST document is read");
        let from_provenance = json::from_provenance_str(&provenance)
            .expect("the provenance document is read")
            .definition;
        assert_eq!(rule_body_depth(&from_kast), levels);
        assert_eq!(rule_body_depth(&from_provenance), levels);
        drop((from_kast, from_provenance));
    });
}

/// The JSON text of a KAST term: `levels` applications of `wrap` around the variable `X`.
fn deep_term_text(levels: usize) -> String {
    let wrap = r#"{"node":"KApply","label":{"node":"KLabel","name":"wrap","params":[]},"arity":1,"args":["#;
    let leaf = r#"{"node":"KVariable","name":"X"}"#;
    format!("{}{leaf}{}", wrap.repeat(levels), "]}".repeat(levels))
}

/// The JSON text of a KAST sort: `levels` applications of the sort constructor `S`.
fn deep_sort_text(levels: usize) -> String {
    let sort = r#"{"node":"KSort","name":"S","params":["#;
    let leaf = r#"{"node":"KSort","name":"S","params":[]}"#;
    format!("{}{leaf}{}", sort.repeat(levels), "]}".repeat(levels))
}

const BOGUS: &str = r#"{"node":"Bogus"}"#;

/// Read each case's document with `read` on a 1 MiB thread and check that it is refused with an
/// error whose text contains the case's expected text.
fn assert_refused_on_a_small_stack<T: 'static, E: std::fmt::Display + 'static>(
    read: fn(&str) -> Result<T, E>,
    cases: Vec<(&'static str, String, &'static str)>,
) {
    for (case, document, expected) in cases {
        let error = on_stack(1 << 20, move || {
            read(&document).err().map(|error| error.to_string())
        });
        let error = error.unwrap_or_else(|| panic!("{case}: the document is read"));
        assert!(error.contains(expected), "{case}: {error}");
    }
}

/// A refused KAST term document is refused without recursing over the depth of what the reader
/// built before it found the error: each document below builds a term or sort 50,000 levels
/// deep (about 5 MB of text) before it fails, and each is refused on a 1 MiB thread.
#[test]
fn malformed_terms_of_any_depth_are_refused_on_a_small_stack() {
    let levels = 50_000;
    let term = deep_term_text(levels);
    let sort = deep_sort_text(levels);
    let label = |params: &str| format!(r#"{{"node":"KLabel","name":"f","params":[{params}]}}"#);
    let envelope = |term: String| format!(r#"{{"format":"KAST","version":4,"term":{term}}}"#);
    let apply = |label: String, arity: &str, args: String| {
        envelope(format!(
            r#"{{"node":"KApply","label":{label},{arity}"args":[{args}]}}"#
        ))
    };
    assert_refused_on_a_small_stack(
        k_rust::kast::json::from_str,
        vec![
            (
                "a malformed sibling of a deep term",
                apply(label(""), r#""arity":2,"#, format!("{term},{BOGUS}")),
                "unknown variant `Bogus`",
            ),
            (
                "an arity that does not count a deep argument",
                apply(label(""), r#""arity":2,"#, term.clone()),
                "declares arity 2, but contains 1 children",
            ),
            (
                "a malformed sibling of a variable of a deep sort",
                apply(
                    label(""),
                    r#""arity":2,"#,
                    format!(r#"{{"node":"KVariable","name":"X","sort":{sort}}},{BOGUS}"#),
                ),
                "unknown variant `Bogus`",
            ),
            (
                "a token of a deep sort without its text",
                envelope(format!(r#"{{"node":"KToken","sort":{sort}}}"#)),
                "missing field `token`",
            ),
            (
                "a malformed sibling of a deep sort parameter",
                envelope(format!(
                    r#"{{"node":"KToken","token":"t","sort":{{"node":"KSort","name":"S","params":[{sort},{BOGUS}]}}}}"#
                )),
                "unknown variant `Bogus`, expected `KSort`",
            ),
            (
                "a malformed sibling of a deep label parameter",
                apply(
                    label(&format!("{sort},{BOGUS}")),
                    r#""arity":0,"#,
                    String::new(),
                ),
                "unknown variant `Bogus`, expected `KSort`",
            ),
            (
                "an application of a deeply parametric label without its arity",
                apply(label(&sort), "", String::new()),
                "missing field `arity`",
            ),
        ],
    );
}

/// The definition readers, and the module list reader, drop the terms they decoded with explicit
/// work stacks when a later part of the document is refused: a malformed sibling, another field
/// of the same sentence, a later sentence or module, or a check of the whole definition. Each
/// document below holds a term 50,000 levels deep and is refused on a 1 MiB thread.
#[test]
fn definitions_refused_after_a_deep_term_are_refused_on_a_small_stack() {
    let levels = 50_000;
    let one = deep_term_text(1);
    let deep = deep_term_text(levels);
    // An outermost application of arity 2 whose second argument is malformed.
    let malformed_sibling = format!(
        r#"{{"node":"KApply","label":{{"node":"KLabel","name":"wrap","params":[]}},"arity":2,"args":[{},{BOGUS}]}}"#,
        deep_term_text(levels - 1)
    );
    let requires = r#"{"node":"KVariable","name":"R"}"#;
    let later = r#"{"node":"KVariable","name":"L"}"#;
    let other = r#"{"node":"KVariable","name":"M"}"#;

    // `MAIN` holds a rule whose body is `wrap(X)` and whose requires is `R`, then a rule whose
    // body is `L`; a module `LATER` follows, whose one rule's body is `L` too.
    let later_rule = || Sentence::Rule {
        body: Term::variable("L"),
        requires: bool_token("true"),
        ensures: bool_token("true"),
        attributes: empty_attributes(),
    };
    let mut definition = complete_definition(vec![
        Sentence::Rule {
            body: Term::apply("wrap", vec![Term::variable("X")]),
            requires: Term::variable("R"),
            ensures: bool_token("true"),
            attributes: empty_attributes(),
        },
        later_rule(),
    ]);
    definition.modules.push(FlatModule {
        name: "LATER".into(),
        imports: Vec::new(),
        local_sentences: vec![Arc::new(later_rule())],
        attributes: empty_attributes(),
    });
    // Apply each edit to its first occurrence, after checking how often it occurs.
    let edit = |text: &str, edits: &[(&str, &str, usize)]| {
        edits
            .iter()
            .fold(text.to_owned(), |text, (from, to, count)| {
                assert_eq!(text.matches(from).count(), *count, "{from}");
                text.replacen(from, to, 1)
            })
    };
    let kast = json::to_string(&definition).unwrap();
    let provenance = json::to_provenance_string(&definition, &SourceTable::default()).unwrap();
    let main = r#""mainModule":"MAIN""#;
    let missing_main = r#""mainModule":"NOPE""#;
    let cases = |text: &str| {
        vec![
            (
                "a malformed sibling inside the deep body",
                edit(text, &[(&one, &malformed_sibling, 1)]),
                "unknown variant `Bogus`",
            ),
            (
                "a malformed requires of the deep rule",
                edit(text, &[(&one, &deep, 1), (requires, BOGUS, 1)]),
                "unknown variant `Bogus`",
            ),
            (
                "a malformed later rule",
                edit(text, &[(&one, &deep, 1), (later, BOGUS, 2)]),
                "unknown variant `Bogus`",
            ),
            (
                "a malformed rule in a later module",
                edit(
                    text,
                    &[(&one, &deep, 1), (later, other, 2), (later, BOGUS, 1)],
                ),
                "unknown variant `Bogus`",
            ),
            (
                "a missing main module",
                edit(text, &[(&one, &deep, 1), (main, missing_main, 1)]),
                "\"NOPE\"",
            ),
        ]
    };
    assert_refused_on_a_small_stack(json::from_str, cases(&kast));
    assert_refused_on_a_small_stack(json::from_provenance_str, cases(&provenance));

    let list = edit(
        &kast,
        &[
            (&one, &deep, 1),
            (r#""node":"KDefinition""#, r#""node":"KFlatModuleList""#, 1),
            (r#""modules":"#, r#""term":"#, 1),
            (main, missing_main, 1),
        ],
    );
    assert_refused_on_a_small_stack(
        json::module_list_from_str,
        vec![("a module list without its main module", list, "\"NOPE\"")],
    );
}

/// Outside its terms a definition nests only a few levels, so serde's recursion limit stays on
/// there: an attribute value, or the sort of a production, nested 100,000 levels deep is refused
/// with an ordinary error on a 1 MiB thread rather than read by recursion. A declaration's sort
/// nests at most two levels in a definition that passes the sort checks, which reject nested
/// parametric sorts.
#[test]
fn deep_values_outside_terms_are_refused() {
    let levels = 100_000;
    let mut attributes = BTreeMap::new();
    attributes.insert("nested".to_owned(), value!([]));
    let mut definition = deep_rule_definition(1);
    definition.attributes = Attributes::new(attributes);
    definition.modules[0]
        .local_sentences
        .push(Arc::new(Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("Declared"),
            items: Vec::new(),
            attributes: empty_attributes(),
        }));
    let encoded = json::to_string(&definition).unwrap();
    let edit = |from: &str, to: &str| {
        assert_eq!(encoded.matches(from).count(), 1, "{encoded}");
        encoded.replace(from, to)
    };
    let deep_attribute = edit(
        r#""nested":[]"#,
        &format!(r#""nested":{}{}"#, "[".repeat(levels), "]".repeat(levels)),
    );
    let deep_production_sort = edit(
        r#"{"node":"KSort","name":"Declared","params":[]}"#,
        &deep_sort_text(levels),
    );
    for deep in [deep_attribute, deep_production_sort] {
        let error = on_stack(1 << 20, move || {
            json::from_str(&deep).map(drop).unwrap_err()
        });
        assert!(
            matches!(&error, json::Error::Json(_)) && error.to_string().contains("recursion limit"),
            "{error}"
        );
    }
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
fn bracket_label_round_trips_as_a_klabel_node() {
    let bracket_label = value!({
        "node": "KLabel",
        "name": "paren",
        "params": [{"node": "KSort", "name": "S", "params": []}],
    });
    let definition = complete_definition(vec![Sentence::Production {
        label: None,
        parameters: vec![Sort::new("S")],
        sort: Sort::with_parameters("Box", vec![Sort::new("S")]),
        items: vec![
            ProductionItem::Terminal("(".into()),
            ProductionItem::NonTerminal {
                sort: Sort::with_parameters("Box", vec![Sort::new("S")]),
                name: None,
            },
            ProductionItem::Terminal(")".into()),
        ],
        attributes: Attributes::new(BTreeMap::from([
            ("bracket".into(), value!("")),
            ("bracketLabel".into(), bracket_label.clone()),
        ])),
    }]);

    let wire = assert_definition_round_trip!(definition);
    assert_eq!(
        wire["term"]["modules"][0]["localSentences"][0]["att"]["att"]["bracketLabel"],
        bracket_label
    );

    let legacy = complete_definition(vec![Sentence::Production {
        label: None,
        parameters: Vec::new(),
        sort: Sort::new("Exp"),
        items: vec![ProductionItem::NonTerminal {
            sort: Sort::new("Exp"),
            name: None,
        }],
        attributes: Attributes::new(BTreeMap::from([(
            "bracketLabel".into(),
            value!("legacy-bracket"),
        )])),
    }]);
    let legacy_wire = assert_definition_round_trip!(legacy);
    assert_eq!(
        legacy_wire["term"]["modules"][0]["localSentences"][0]["att"]["att"]["bracketLabel"],
        "legacy-bracket"
    );
}

#[test]
fn cloning_attributes_shares_provenance_receipt_storage() {
    let receipt = value!({
        "pass": "subsort-kitem",
        "origins": (0..256)
            .map(|start| value!({
                "kind": "source",
                "source": 0,
                "start": start,
                "end": start + 1,
            }))
            .collect::<Vec<_>>(),
        "destination": null,
    });
    let attributes = Attributes::new(BTreeMap::from([(ORIGIN_ATTRIBUTE.into(), receipt.clone())]));
    let cloned = attributes.clone();

    assert!(std::ptr::eq(
        attributes.get(ORIGIN_ATTRIBUTE).unwrap(),
        cloned.get(ORIGIN_ATTRIBUTE).unwrap(),
    ));
    assert_eq!(cloned.entries().get(ORIGIN_ATTRIBUTE), Some(&receipt));
}

#[test]
fn rejects_non_unique_main_modules_and_unrepresentable_sentences() {
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
    let encoded = json::to_string(&alias).unwrap();
    let wire: Value = serde_json::from_str(&encoded).unwrap();
    assert_eq!(
        wire["term"]["modules"][0]["localSentences"][0]["node"],
        "badsentence"
    );
    let error = json::from_str(&encoded).unwrap_err();
    assert!(matches!(
        error,
        json::Error::UnsupportedSentence("badsentence")
    ));
    assert_eq!(
        error.to_string(),
        "KAST JSON version 4 document contains badsentence: its writer could not represent a sentence"
    );
}

#[test]
fn provenance_export_round_trips_sources_attributes_and_term_metadata() {
    let mut sources = SourceTable::default();
    let source = sources.intern_extraction(
        LogicalSourceId::new("src/definition.k", b"module MAIN\n"),
        Some(SourceOffsetMap::identity("module MAIN\n".len())),
    );
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
            path: vec![0, 1].into(),
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
        production: Some(ProductionIdentity::from_hex(&format!("{:032x}", 3)).unwrap()),
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
    // Every source reference is the index of its entry in the sources table.
    let wire_identity = value!(0);
    assert_eq!(
        &envelope["termMetadata"][0]["metadata"]["span"]["source"],
        &wire_identity
    );
    assert_eq!(
        &envelope["term"]["modules"][0]["localSentences"][0]["att"]["att"]
            [k_rust::definition::SOURCE_ID_ATTRIBUTE],
        &wire_identity
    );
    // The sentence receipt and the body's term receipt hold one origin set, written once.
    assert_eq!(envelope["originSets"].as_array().unwrap().len(), 1);
    assert_eq!(&envelope["originSets"][0][0]["source"], &wire_identity);
    assert_eq!(
        envelope["term"]["modules"][0]["localSentences"][0]["att"]["att"][ORIGIN_ATTRIBUTE]["origins"],
        0
    );
    assert_eq!(
        envelope["termMetadata"][0]["metadata"]["origin"]["origins"],
        0
    );
    let decoded = json::from_provenance_str(&encoded).unwrap();

    assert_eq!(decoded.source_table, sources);
    assert_eq!(decoded.definition, definition);
    let Sentence::Rule {
        body: decoded_body,
        attributes: decoded_attributes,
        ..
    } = &*decoded.definition.modules[0].local_sentences[0]
    else {
        panic!("expected a rule")
    };
    let Sentence::Rule {
        body: expected_body,
        attributes: expected_attributes,
        ..
    } = &*definition.modules[0].local_sentences[0]
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
    assert!(manifest.unsupported_sentence_forms.is_empty());

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
    let encoded = json::to_provenance_string(&context_alias, &SourceTable::default()).unwrap();
    let wire: Value = serde_json::from_str(&encoded).unwrap();
    assert_eq!(
        wire["term"]["modules"][0]["localSentences"][0]["node"],
        "KContextAlias"
    );
    assert_eq!(
        json::from_provenance_str(&encoded).unwrap().definition,
        context_alias
    );
    let mut provenance_with_placeholder = wire.clone();
    provenance_with_placeholder["term"]["modules"][0]["localSentences"][0] =
        value!({"node": "badsentence"});
    assert!(matches!(
        json::from_provenance_str(&provenance_with_placeholder.to_string()),
        Err(json::Error::InvalidProvenance(_))
    ));
    let kast: Value = serde_json::from_str(&json::to_string(&context_alias).unwrap()).unwrap();
    let mut kast_with_alias = kast;
    kast_with_alias["term"]["modules"][0]["localSentences"][0] =
        wire["term"]["modules"][0]["localSentences"][0].clone();
    assert!(matches!(
        json::from_str(&kast_with_alias.to_string()),
        Err(json::Error::UnsupportedSentence("KContextAlias"))
    ));
}

#[test]
fn loaded_context_alias_preserves_later_rule_term_metadata() {
    let source = "module MAIN\n  imports INT\n  syntax KResult ::= Int\n  syntax Exp ::= Int | foo(Exp) [strict(c)] | a() | b()\n  context alias [c]: HERE\n  rule a() => 1\n  rule b() => 2\nendmodule\n";
    let prelude = k_rust::builtin::embedded("prelude.md").unwrap();
    let mut resolver = |_: &str, required: &str| {
        k_rust::builtin::embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("main.k", source),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            ..LoadOptions::default()
        },
    )
    .unwrap();
    let encoded = json::to_provenance_string(loaded.definition(), loaded.source_table()).unwrap();
    let decoded = json::from_provenance_str(&encoded).unwrap();
    assert_eq!(&decoded.definition, loaded.definition());
    assert_eq!(&decoded.source_table, loaded.source_table());
    let expected = &loaded.definition().main_module().unwrap().local_sentences;
    let actual = &decoded.definition.main_module().unwrap().local_sentences;
    let alias_index = expected
        .iter()
        .position(|sentence| matches!(&**sentence, Sentence::ContextAlias { .. }))
        .expect("loaded definition contains the context alias");
    let mut later_rules = 0;
    for (expected, actual) in expected.iter().zip(actual).skip(alias_index + 1) {
        if let (
            Sentence::Rule {
                body: expected_body,
                requires: expected_requires,
                ensures: expected_ensures,
                ..
            },
            Sentence::Rule {
                body: actual_body,
                requires: actual_requires,
                ensures: actual_ensures,
                ..
            },
        ) = (&**expected, &**actual)
        {
            later_rules += 1;
            assert!(expected_body.metadata().is_some());
            assert_term_metadata_equal(expected_body, actual_body);
            assert_term_metadata_equal(expected_requires, actual_requires);
            assert_term_metadata_equal(expected_ensures, actual_ensures);
        }
    }
    assert!(later_rules >= 2);
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
    let source = sources.intern_extraction(
        LogicalSourceId::new("src/definition.k", b"X"),
        Some(SourceOffsetMap::identity(1)),
    );
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
    envelope["originSets"][0][0]["unexpected"] = value!(true);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::Json(_))
    ));

    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["termMetadata"][0]["metadata"]["origin"]["unexpected"] = value!(true);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::Json(_))
    ));

    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["term"]["modules"][0]["localSentences"][0]["att"]["att"][ORIGIN_ATTRIBUTE]["unexpected"] =
        value!(true);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::Json(_))
    ));

    // A receipt must name an entry of the origin-set table.
    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["termMetadata"][0]["metadata"]["origin"]["origins"] = value!(1);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::InvalidProvenance(_))
    ));

    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["term"]["modules"][0]["localSentences"][0]["att"]["att"][ORIGIN_ATTRIBUTE]["origins"] =
        value!(1);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::InvalidProvenance(_))
    ));

    // Each set is written once, so a repeated table entry is malformed.
    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    let duplicate = envelope["originSets"][0].clone();
    envelope["originSets"]
        .as_array_mut()
        .unwrap()
        .push(duplicate);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::InvalidProvenance(_))
    ));

    // Version 2 wrote every receipt's origin set in place; its documents are rebuilt, not read.
    let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
    envelope["version"] = value!(2);
    assert!(matches!(
        json::from_provenance_str(&serde_json::to_string(&envelope).unwrap()),
        Err(json::Error::UnsupportedProvenanceVersion(2))
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

#[test]
fn omitting_reader_skips_badsentence_and_reports_its_wire_position() {
    let rule = Sentence::Rule {
        body: bool_token("true"),
        requires: bool_token("true"),
        ensures: bool_token("true"),
        attributes: empty_attributes(),
    };
    let alias = Sentence::ContextAlias {
        body: Term::variable("X"),
        requires: bool_token("true"),
        attributes: empty_attributes(),
    };
    let mut written = complete_definition(vec![rule.clone(), alias.clone(), alias, rule.clone()]);
    written.modules.insert(
        0,
        FlatModule {
            name: "PRELUDE".into(),
            imports: Vec::new(),
            local_sentences: Vec::new(),
            attributes: empty_attributes(),
        },
    );
    let encoded = json::to_string(&written).unwrap();

    assert!(matches!(
        json::from_str(&encoded),
        Err(json::Error::UnsupportedSentence("badsentence"))
    ));

    let (decoded, omitted) = json::from_str_omitting_unrepresentable(&encoded).unwrap();
    let mut expected = written.clone();
    expected.modules[1].local_sentences = vec![Arc::new(rule.clone()), Arc::new(rule)];
    assert_eq!(decoded, expected);
    let omission = |index| json::OmittedSentence {
        module_index: 1,
        module: "MAIN".into(),
        index,
    };
    assert_eq!(omitted, vec![omission(1), omission(2)]);

    // Without badsentence nodes the lossy reader is the strict one with nothing omitted.
    let (decoded, omitted) = json::from_str_omitting_unrepresentable(
        &json::to_string(&complete_definition(Vec::new())).unwrap(),
    )
    .unwrap();
    assert_eq!(decoded, complete_definition(Vec::new()));
    assert!(omitted.is_empty());
}

fn module_list_document(main_module: &str, modules: Vec<Value>) -> String {
    value!({
        "format": "KAST",
        "version": 4,
        "term": {
            "node": "KFlatModuleList",
            "mainModule": main_module,
            "term": modules,
        },
    })
    .to_string()
}

fn wire_module(name: &str, imports: &[&str], sentences: Vec<Value>) -> Value {
    value!({
        "node": "KFlatModule",
        "name": name,
        "imports": imports
            .iter()
            .map(|name| value!({"node": "KImport", "name": name, "isPublic": true}))
            .collect::<Vec<_>>(),
        "localSentences": sentences,
        "att": {"node": "KAtt", "att": {}},
    })
}

#[test]
fn module_list_reader_decodes_specification_modules() {
    let token = |token: &str| value!({"node": "KToken", "token": token, "sort": {"node": "KSort", "name": "Bool", "params": []}});
    let claim = value!({
        "node": "KClaim",
        "body": token("true"),
        "requires": token("true"),
        "ensures": token("true"),
        "att": {"node": "KAtt", "att": {"label": "SPEC.one"}},
    });
    let document = module_list_document(
        "SPEC",
        vec![
            wire_module("VERIFICATION", &["IMP"], Vec::new()),
            wire_module("SPEC", &["VERIFICATION"], vec![claim]),
        ],
    );

    let list = json::module_list_from_str(&document).unwrap();
    assert_eq!(list.main_module, "SPEC");
    assert_eq!(list.modules.len(), 2);
    // `IMP` lies outside the list; the reader keeps the import as written.
    assert_eq!(list.modules[0].imports[0].name, "IMP");
    let spec = &list.modules[1];
    assert_eq!(spec.name, "SPEC");
    assert_eq!(spec.local_sentences.len(), 1);
    assert!(matches!(&*spec.local_sentences[0], Sentence::Claim { .. }));

    let bad = module_list_document(
        "SPEC",
        vec![wire_module(
            "SPEC",
            &[],
            vec![value!({"node": "badsentence"})],
        )],
    );
    assert!(matches!(
        json::module_list_from_str(&bad),
        Err(json::Error::UnsupportedSentence("badsentence"))
    ));
}

#[test]
fn module_list_reader_rejects_bad_main_modules_and_other_nodes() {
    let missing = module_list_document("SPEC", vec![wire_module("OTHER", &[], Vec::new())]);
    assert!(matches!(
        json::module_list_from_str(&missing),
        Err(json::Error::MissingMainModule(name)) if name == "SPEC"
    ));
    let duplicate = module_list_document(
        "SPEC",
        vec![
            wire_module("SPEC", &[], Vec::new()),
            wire_module("SPEC", &[], Vec::new()),
        ],
    );
    assert!(matches!(
        json::module_list_from_str(&duplicate),
        Err(json::Error::DuplicateMainModule(name)) if name == "SPEC"
    ));

    // A definition is not a module list, nor the reverse.
    let definition = json::to_string(&complete_definition(Vec::new())).unwrap();
    assert!(matches!(
        json::module_list_from_str(&definition),
        Err(json::Error::Json(_))
    ));
    let list = module_list_document("SPEC", vec![wire_module("SPEC", &[], Vec::new())]);
    assert!(matches!(json::from_str(&list), Err(json::Error::Json(_))));
    assert!(matches!(
        json::from_str_omitting_unrepresentable(&list),
        Err(json::Error::Json(_))
    ));

    let mut wrong_version: Value = serde_json::from_str(&list).unwrap();
    wrong_version["version"] = value!(3);
    assert!(matches!(
        json::module_list_from_str(&wrong_version.to_string()),
        Err(json::Error::UnsupportedVersion(3))
    ));

    // KContextAlias is not KAST v4 vocabulary, whichever reader meets it.
    let alias = module_list_document(
        "SPEC",
        vec![wire_module(
            "SPEC",
            &[],
            vec![value!({
                "node": "KContextAlias",
                "body": {"node": "KVariable", "name": "X"},
                "requires": {"node": "KToken", "token": "true", "sort": {"node": "KSort", "name": "Bool", "params": []}},
                "att": {"node": "KAtt", "att": {}},
            })],
        )],
    );
    assert!(matches!(
        json::module_list_from_str(&alias),
        Err(json::Error::UnsupportedSentence("KContextAlias"))
    ));
    // The lossy definition reader skips only `badsentence`; other foreign nodes stay errors.
    let mut alias_definition: Value = serde_json::from_str(&alias).unwrap();
    let modules = alias_definition["term"]["term"].take();
    alias_definition["term"] = value!({
        "node": "KDefinition",
        "mainModule": "SPEC",
        "modules": modules,
        "att": {"node": "KAtt", "att": {}},
    });
    assert!(matches!(
        json::from_str_omitting_unrepresentable(&alias_definition.to_string()),
        Err(json::Error::UnsupportedSentence("KContextAlias"))
    ));
}

/// A document of version 8 whose tables hold every kind of entry: a rule `f(X)` (spans `f` at
/// 0..1 and `X` at 1..2) rebuilt as `h(X)` by a generating pass. The sentence receipt names the
/// flat set of the rule's spans (entry 0) and the root anchor of the rule (anchor 0); `h`'s
/// receipt names a set holding `f`'s span and entry 0 (entry 1), and the anchor one step below
/// the root (anchor 1). `h` is node 0 of the body, `X` node 1.
fn version_8_document() -> (String, SourceTable) {
    let mut sources = SourceTable::default();
    let source = sources.intern(LogicalSourceId::new("src/definition.k", b"fX"));
    let spanned = |term: Term, start: usize| {
        term.with_metadata(TermMetadata {
            span: Some(TermSpan {
                source,
                start,
                end: start + 1,
            }),
            ..TermMetadata::default()
        })
    };
    let rule = |body: Term| Sentence::Rule {
        body,
        requires: bool_token("true"),
        ensures: bool_token("true"),
        attributes: Attributes::new(BTreeMap::from([("label".into(), value!("MAIN.rule"))])),
    };
    let x = spanned(Term::variable("X"), 1);
    let before = complete_definition(vec![rule(spanned(Term::apply("f", vec![x.clone()]), 0))]);
    let after = k_rust::provenance::record_generated_origins(
        &before,
        complete_definition(vec![rule(Term::apply("h", vec![x]))]),
        GeneratingPass::MacroExpansion,
    );
    (
        json::to_provenance_string(&after, &sources).unwrap(),
        sources,
    )
}

/// The reader of version 8 checks what the writer guarantees, entry by entry, and refuses
/// anything else as invalid provenance: a set reference that is not to an earlier entry, an
/// entry that is not in normal form (naming the empty entry, repeating a part, being a single
/// reference) or repeats another, a sentence receipt naming a set that names sets, an anchor
/// that repeats another or extends no earlier entry, a receipt naming an absent anchor, and
/// metadata addresses out of order (between fields, or within one), repeated or past their
/// field.
#[test]
fn provenance_version_8_tables_reject_malformed_entries() {
    let (encoded, _) = version_8_document();
    let envelope: Value = serde_json::from_str(&encoded).unwrap();
    assert_eq!(envelope["version"], 8);
    let source = value!(0);
    let span =
        |start: u64| value!({"kind": "source", "source": source, "start": start, "end": start + 1});
    assert_eq!(
        envelope["originSets"],
        value!([[span(0), span(1)], [span(0), {"kind": "set", "set": 0}]])
    );
    assert_eq!(
        envelope["anchors"],
        value!([
            {"module": "MAIN", "sentence": "MAIN.rule", "sentenceIndex": 0},
            {"parent": 0, "step": 0}
        ])
    );
    assert_eq!(
        envelope["termMetadata"]
            .as_array()
            .unwrap()
            .iter()
            .map(|entry| entry["node"].clone())
            .collect::<Vec<_>>(),
        [value!(0), value!(1)]
    );
    assert!(json::from_provenance_str(&encoded).is_ok());
    // A span on the rule's `requires` (field 1): its metadata follows the body's.
    let requires_span = |e: &Value| {
        let mut entry = e["termMetadata"][1].clone();
        entry["field"] = value!(1);
        entry["node"] = value!(0);
        entry
    };
    let mut two_fields: Value = serde_json::from_str(&encoded).unwrap();
    let entry = requires_span(&two_fields);
    two_fields["termMetadata"]
        .as_array_mut()
        .unwrap()
        .push(entry);
    assert!(json::from_provenance_str(&two_fields.to_string()).is_ok());

    let invalid = |change: &dyn Fn(&mut Value)| {
        let mut envelope: Value = serde_json::from_str(&encoded).unwrap();
        change(&mut envelope);
        json::from_provenance_str(&envelope.to_string())
    };
    let set = |index: u64| value!({"kind": "set", "set": index});
    let sentence = |id: &str| value!({"kind": "sentence", "uniqueId": id});
    let push = |envelope: &mut Value, table: &str, entry: Value| {
        envelope[table].as_array_mut().unwrap().push(entry);
    };
    type Change<'a> = Box<dyn Fn(&mut Value) + 'a>;
    let refused: [(&str, Change<'_>); 25] = [
        (
            "a link naming an absent source",
            Box::new(|e| e["originSets"][0][0]["source"] = value!(1)),
        ),
        (
            "a span naming an absent source",
            Box::new(|e| e["termMetadata"][1]["metadata"]["span"]["source"] = value!(1)),
        ),
        (
            "a sentence naming an absent source",
            Box::new(|e| {
                e["term"]["modules"][0]["localSentences"][0]["att"]["att"]
                    [k_rust::definition::SOURCE_ID_ATTRIBUTE] = value!(1);
            }),
        ),
        (
            "a set naming itself",
            Box::new(|e| e["originSets"][1][1] = set(1)),
        ),
        (
            "a set naming an absent set",
            Box::new(|e| e["originSets"][1][1] = set(9)),
        ),
        (
            "a set naming a later set",
            Box::new(|e| e["originSets"][0].as_array_mut().unwrap().push(set(1))),
        ),
        (
            "a set naming the empty set",
            Box::new(|e| {
                push(e, "originSets", value!([]));
                push(e, "originSets", value!([set(2), sentence("x")]));
            }),
        ),
        (
            "a set repeating a link",
            Box::new(|e| {
                let link = e["originSets"][1][0].clone();
                e["originSets"][1].as_array_mut().unwrap().push(link);
            }),
        ),
        (
            "a set repeating a set",
            Box::new(|e| push(e, "originSets", value!([set(0), sentence("x"), set(0)]))),
        ),
        (
            "a set that is one reference",
            Box::new(|e| push(e, "originSets", value!([set(0)]))),
        ),
        (
            "a set repeating another",
            Box::new(|e| {
                let entry = e["originSets"][1].clone();
                push(e, "originSets", entry);
            }),
        ),
        (
            "a sentence receipt naming a set that names sets",
            Box::new(|e| {
                e["term"]["modules"][0]["localSentences"][0]["att"]["att"][ORIGIN_ATTRIBUTE]["origins"] =
                    value!(1);
            }),
        ),
        (
            "a repeated root",
            Box::new(|e| {
                let root = e["anchors"][0].clone();
                push(e, "anchors", root);
            }),
        ),
        (
            "a repeated step",
            Box::new(|e| {
                let step = e["anchors"][1].clone();
                push(e, "anchors", step);
            }),
        ),
        (
            "a step extending itself",
            Box::new(|e| e["anchors"][1]["parent"] = value!(1)),
        ),
        (
            "a step extending an absent anchor",
            Box::new(|e| e["anchors"][1]["parent"] = value!(7)),
        ),
        (
            "a receipt naming an absent anchor",
            Box::new(|e| e["termMetadata"][0]["metadata"]["origin"]["destination"] = value!(9)),
        ),
        (
            "a receipt naming an absent set",
            Box::new(|e| e["termMetadata"][0]["metadata"]["origin"]["origins"] = value!(9)),
        ),
        (
            "metadata in decreasing order",
            Box::new(|e| e["termMetadata"].as_array_mut().unwrap().swap(0, 1)),
        ),
        (
            "metadata of two fields in decreasing field order",
            Box::new(|e| {
                let entry = requires_span(e);
                e["termMetadata"].as_array_mut().unwrap().insert(0, entry);
            }),
        ),
        (
            "metadata repeating a node",
            Box::new(|e| e["termMetadata"][1]["node"] = value!(0)),
        ),
        (
            "metadata past the end of its field",
            Box::new(|e| e["termMetadata"][1]["node"] = value!(2)),
        ),
        (
            "metadata naming no field",
            Box::new(|e| e["termMetadata"][1]["field"] = value!(3)),
        ),
        (
            "metadata naming no sentence",
            Box::new(|e| e["termMetadata"][1]["sentenceIndex"] = value!(1)),
        ),
        (
            "metadata naming no module",
            Box::new(|e| e["termMetadata"][1]["moduleIndex"] = value!(4)),
        ),
    ];
    for (what, change) in &refused {
        let result = invalid(change.as_ref());
        assert!(
            matches!(result, Err(json::Error::InvalidProvenance(_))),
            "{what}: {result:?}"
        );
    }
    assert!(matches!(
        invalid(&|e| push(
            e,
            "anchors",
            value!({"parent": 0, "step": 1, "module": "MAIN"})
        )),
        Err(json::Error::Json(_))
    ));
}

/// A `KRUST-PROVENANCE` document written by the version 7 writer (k-rust `480a0d3b`), from the
/// definition [`version_8_document`] builds.
const PROVENANCE_VERSION_7: &str = include_str!("fixtures/provenance-version-7.json");

/// A document of another version is refused by its version whatever the shape of its body, and
/// a document of another format by its format, before the body is read: a document the version
/// 7 writer wrote (sources named by identity, full paths, no anchor table), the same document as
/// version 6 (whose shape version 7 kept), a document of a version this build does not know
/// whose body version 8 cannot read, and a version 8 body under another version.
#[test]
fn provenance_documents_of_other_versions_are_refused_by_version() {
    let version_7: Value = serde_json::from_str(PROVENANCE_VERSION_7).unwrap();
    assert_eq!(version_7["version"], 7);
    assert!(version_7["originSets"][0][0]["source"].is_object());
    assert!(version_7.get("anchors").is_none());
    assert!(version_7["termMetadata"][1]["path"].is_array());
    let refused = |text: &str| json::from_provenance_str(text).unwrap_err();

    let error = refused(PROVENANCE_VERSION_7);
    assert!(
        matches!(error, json::Error::UnsupportedProvenanceVersion(7)),
        "{error:?}"
    );
    assert_eq!(
        error.to_string(),
        "KRUST-PROVENANCE version 7 is not supported; this build reads version 8"
    );
    let mut version_6 = version_7.clone();
    version_6["version"] = value!(6);
    let error = refused(&version_6.to_string());
    assert!(
        matches!(error, json::Error::UnsupportedProvenanceVersion(6)),
        "{error:?}"
    );

    let (encoded, _) = version_8_document();
    let mut later: Value = serde_json::from_str(&encoded).unwrap();
    later["version"] = value!(9);
    later["anchors"] = value!({"roots": [], "steps": []});
    later["receipts"] = value!([]);
    let error = refused(&later.to_string());
    assert!(
        matches!(error, json::Error::UnsupportedProvenanceVersion(9)),
        "{error:?}"
    );
    let mut relabelled: Value = serde_json::from_str(&encoded).unwrap();
    relabelled["version"] = value!(7);
    let error = refused(&relabelled.to_string());
    assert!(
        matches!(error, json::Error::UnsupportedProvenanceVersion(7)),
        "{error:?}"
    );

    let mut foreign = version_7;
    foreign["format"] = value!("KAST");
    let error = refused(&foreign.to_string());
    assert!(
        matches!(&error, json::Error::UnsupportedFormat(format) if format == "KAST"),
        "{error:?}"
    );
}

/// A path allocation may extend different roots (anchors built by hand share whatever they
/// like): two receipts holding one path under two sentences are written as two step chains,
/// one under each root, and each decodes to its own module, sentence and full path.
#[test]
fn a_path_shared_by_two_roots_is_written_under_each() {
    let path = k_rust::provenance::AnchorPath::from(vec![0, 0]);
    let receipt = |module: &str, sentence: &str, index| {
        Arc::new(OriginRecord {
            pass: GeneratingPass::MacroExpansion,
            origins: k_rust::provenance::OriginSet::new(),
            destination: Some(DestinationAnchor {
                module: module.into(),
                sentence: sentence.into(),
                sentence_index: index,
                path: path.clone(),
            }),
        })
    };
    let rule = |origin| Sentence::Rule {
        body: Term::apply("f", vec![Term::variable("X")]).with_metadata(TermMetadata {
            origin: Some(origin),
            ..TermMetadata::default()
        }),
        requires: bool_token("true"),
        ensures: bool_token("true"),
        attributes: empty_attributes(),
    };
    let definition = complete_definition(vec![
        rule(receipt("MAIN", "first", 0)),
        rule(receipt("OTHER", "second", 1)),
    ]);
    let encoded = json::to_provenance_string(&definition, &SourceTable::default()).unwrap();
    let envelope: Value = serde_json::from_str(&encoded).unwrap();
    assert_eq!(
        envelope["anchors"],
        value!([
            {"module": "MAIN", "sentence": "first", "sentenceIndex": 0},
            {"parent": 0, "step": 0},
            {"parent": 1, "step": 0},
            {"module": "OTHER", "sentence": "second", "sentenceIndex": 1},
            {"parent": 3, "step": 0},
            {"parent": 4, "step": 0}
        ])
    );
    let decoded = json::from_provenance_str(&encoded).unwrap().definition;
    for (sentence, expected) in decoded.modules[0]
        .local_sentences
        .iter()
        .zip(&definition.modules[0].local_sentences)
    {
        let receipt = |sentence: &Sentence| {
            let Sentence::Rule { body, .. } = sentence else {
                unreachable!()
            };
            body.metadata().unwrap().origin.clone().unwrap()
        };
        assert_eq!(receipt(sentence), receipt(expected));
    }
}

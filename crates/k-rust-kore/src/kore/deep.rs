use std::cmp::Ordering;

use super::{
    ast::{Attributes, Definition, Module, Sentence, Sort},
    binary, json, normalize,
    parser::parse_pattern,
    printer::Printer,
};

const DEEP_PATTERN_LEVELS: usize = 200_000;
const DEEP_SORT_LEVELS: usize = 100_000;
const PRETTY_LEVELS: usize = 2_000;

fn on_stack<T: Send + 'static>(bytes: usize, work: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(bytes)
        .spawn(work)
        .expect("deep-pattern worker should spawn")
        .join()
        .expect("deep-pattern worker should finish")
}

fn not_chain(depth: usize, leaf: &str) -> String {
    let mut source = String::with_capacity(depth * 12 + leaf.len());
    for _ in 0..depth {
        source.push_str(r"\not{S{}}(");
    }
    source.push_str(leaf);
    for _ in 0..depth {
        source.push(')');
    }
    source
}

fn kseq_chain(depth: usize) -> String {
    let mut source = String::with_capacity(depth * 70 + 8);
    for _ in 0..depth {
        source.push_str(r#"kseq{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")), "#);
    }
    source.push_str("dotk{}()");
    for _ in 0..depth {
        source.push(')');
    }
    source
}

#[test]
fn deep_patterns_survive_a_one_mebibyte_thread() {
    on_stack(1 << 20, || {
        let source = not_chain(DEEP_PATTERN_LEVELS, r"\top{S{}}()");
        let pattern = parse_pattern(&source).expect("deep KORE text should parse");

        let compact = Printer::compact().print_pattern(&pattern);
        assert_eq!(compact, source);
        let reparsed = parse_pattern(&compact).expect("printed deep KORE should parse");
        assert_eq!(reparsed.cmp(&pattern), Ordering::Equal);
        drop(reparsed);

        let different = parse_pattern(&not_chain(DEEP_PATTERN_LEVELS, r"\bottom{S{}}()"))
            .expect("comparison control should parse");
        assert_eq!(pattern.cmp(&different), Ordering::Less);
        drop(different);

        let cloned = pattern.clone();
        assert_eq!(cloned, pattern);
        drop(cloned);

        let debug = format!("{pattern:?}");
        assert!(debug.starts_with(
            r#"Not { sort: Application { name: "S", arguments: [] }, argument: Not { "#
        ));
        let leaf = r#"argument: Top { sort: Application { name: "S", arguments: [] } }"#;
        assert!(debug.ends_with(&format!("{leaf}{}", " }".repeat(DEEP_PATTERN_LEVELS))));
        assert_eq!(debug.matches("Not {").count(), DEEP_PATTERN_LEVELS);
        drop(debug);

        let normalized = normalize::for_kast(&pattern);
        assert_eq!(normalized, pattern);
        drop(normalized);

        let encoded = binary::encode_term(&pattern).expect("deep binary KORE should encode");
        let decoded = binary::decode_term(&encoded).expect("deep binary KORE should decode");
        assert_eq!(decoded, pattern);
        drop(decoded);

        let encoded = json::to_string(&pattern).expect("deep KORE JSON should encode");
        let decoded = json::from_str(&encoded).expect("deep KORE JSON should decode");
        assert_eq!(decoded, pattern);
        drop(decoded);

        #[allow(deprecated)]
        let decoded = json::from_str_unbounded(&encoded)
            .expect("the compatibility JSON entry point should remain unbounded");
        assert_eq!(decoded, pattern);
        drop(decoded);

        let value = json::to_value(&pattern).expect("deep KORE JSON value should build");
        assert_eq!(value["format"], json::FORMAT);
        // serde_json::Value retains recursive drop glue. The public capacity table documents
        // that remaining host limit; this test measures codec capacity independently of Value drop.
        std::mem::forget(value);

        drop(pattern);

        // The reference's collection encodings add two Pattern nodes per source element.
        let collection = parse_pattern(&kseq_chain(DEEP_PATTERN_LEVELS / 2))
            .expect("a 200k-pattern collection chain should parse");
        drop(collection);
    });
}

#[test]
fn deep_pretty_outputs_preserve_existing_formatting() {
    on_stack(1 << 20, || {
        let source = not_chain(PRETTY_LEVELS, r"\top{S{}}()");
        let pattern = parse_pattern(&source).unwrap();

        let pretty = Printer::pretty(100).print_pattern(&pattern);
        assert_eq!(parse_pattern(&pretty).unwrap(), pattern);

        let pretty_json = json::to_string_pretty(&pattern).unwrap();
        assert_eq!(json::from_str(&pretty_json).unwrap(), pattern);
    });
}

#[test]
fn alternate_debug_of_deep_patterns_runs_on_a_small_thread() {
    on_stack(256 << 10, || {
        let pattern = parse_pattern(&not_chain(PRETTY_LEVELS, r"\top{S{}}()")).unwrap();
        let debug = format!("{pattern:#?}");
        assert!(debug.starts_with("Not {\n    sort: Application {\n        name: \"S\",\n"));
        assert!(debug.ends_with("\n    },\n}"));
        assert_eq!(debug.matches("Not {").count(), PRETTY_LEVELS);
        let leaf = format!("\n{}argument: Top {{\n", " ".repeat(4 * PRETTY_LEVELS));
        assert!(debug.contains(&leaf));
    });
}

#[test]
fn definitions_with_deep_patterns_clone_compare_print_and_drop() {
    on_stack(1 << 20, || {
        let pattern =
            parse_pattern(&not_chain(50_000, r"\top{S{}}()")).expect("deep axiom should parse");
        let definition = Definition {
            attributes: Attributes::default(),
            modules: vec![Module {
                name: "M".into(),
                sentences: vec![Sentence::Axiom {
                    parameters: Vec::new(),
                    pattern: Box::new(pattern),
                    attributes: Attributes::default(),
                }],
                attributes: Attributes::default(),
            }],
        };

        let cloned = definition.clone();
        assert_eq!(cloned, definition);
        let printed = Printer::compact().print_definition(&definition);
        assert_eq!(
            super::parser::parse_definition(&printed).unwrap(),
            definition
        );
        drop(cloned);
        drop(definition);
    });
}

fn sort_chain(depth: usize, leaf: &str) -> String {
    let mut source = String::with_capacity(depth * 3 + leaf.len());
    for _ in 0..depth {
        source.push_str("S{");
    }
    source.push_str(leaf);
    for _ in 0..depth {
        source.push('}');
    }
    source
}

#[test]
fn deeply_nested_sorts_decode_and_drop_on_a_one_mebibyte_thread() {
    on_stack(1 << 20, || {
        let source = format!("a{{{}}}()", sort_chain(DEEP_SORT_LEVELS, "T"));
        let pattern = parse_pattern(&source).expect("deep textual sort should parse");
        assert_eq!(Printer::compact().print_pattern(&pattern), source);

        let encoded = binary::encode_term(&pattern).expect("deep binary sort should encode");
        let decoded = binary::decode_term(&encoded).expect("deep binary sort should decode");
        assert_eq!(decoded, pattern);
        drop(decoded);

        let encoded = json::to_string(&pattern).expect("deep JSON sort should encode");
        let decoded = json::from_str(&encoded).expect("deep JSON sort should decode");
        assert_eq!(decoded, pattern);
        drop(decoded);
        drop(pattern);

        let mut sort = String::from(r#"{"tag":"SortVar","name":"T"}"#);
        for _ in 0..DEEP_SORT_LEVELS {
            sort = format!(r#"{{"tag":"SortApp","name":"S","args":[{sort}]}}"#);
        }
        let source =
            format!(r#"{{"format":"KORE","version":1,"term":{{"tag":"Top","sort":{sort}}}}}"#);
        drop(json::from_str(&source).expect("deep JSON sort should parse"));
    });
}

#[test]
fn deeply_nested_sorts_clone_compare_format_and_drop_on_a_one_mebibyte_thread() {
    on_stack(1 << 20, || {
        let chain = |leaf| {
            let mut sort = leaf;
            for _ in 0..DEEP_SORT_LEVELS {
                sort = Sort::Application {
                    name: "S".into(),
                    arguments: vec![sort],
                };
            }
            sort
        };
        let sort = chain(Sort::Variable("T".into()));
        let other = chain(Sort::Application {
            name: "U".into(),
            arguments: Vec::new(),
        });

        let cloned = sort.clone();
        assert_eq!(cloned, sort);
        drop(cloned);
        // A variable precedes an application at the same position.
        assert_eq!(sort.cmp(&other), Ordering::Less);
        assert_ne!(sort, other);
        drop(other);

        let debug = format!("{sort:?}");
        assert!(debug.starts_with(r#"Application { name: "S", arguments: [Application { "#));
        assert!(debug.ends_with(&format!(
            r#"Variable("T"){}"#,
            "] }".repeat(DEEP_SORT_LEVELS)
        )));
        drop(debug);
        drop(sort);
    });
}

#[test]
fn sort_traits_match_their_derived_forms() {
    let map = Sort::Application {
        name: "Map".into(),
        arguments: vec![Sort::Variable("K".into()), Sort::Variable("V".into())],
    };
    let nested = Sort::Application {
        name: "List".into(),
        arguments: vec![map.clone()],
    };
    assert_eq!(map.clone(), map);
    assert_eq!(nested.clone(), nested);
    assert_eq!(
        format!("{nested:?}"),
        r#"Application { name: "List", arguments: [Application { name: "Map", arguments: [Variable("K"), Variable("V")] }] }"#
    );
    assert_eq!(
        format!("{map:#?}"),
        indoc::indoc! {r#"
        Application {
            name: "Map",
            arguments: [
                Variable(
                    "K",
                ),
                Variable(
                    "V",
                ),
            ],
        }"#}
    );

    // Variables precede applications; then names; then arguments left to right; then count.
    let ordered = [
        Sort::Variable("A".into()),
        Sort::Variable("B".into()),
        Sort::Application {
            name: "A".into(),
            arguments: Vec::new(),
        },
        Sort::Application {
            name: "A".into(),
            arguments: vec![Sort::Variable("X".into())],
        },
        Sort::Application {
            name: "A".into(),
            arguments: vec![Sort::Variable("X".into()), Sort::Variable("X".into())],
        },
        Sort::Application {
            name: "A".into(),
            arguments: vec![Sort::Variable("Y".into())],
        },
        Sort::Application {
            name: "A".into(),
            arguments: vec![Sort::Application {
                name: "A".into(),
                arguments: Vec::new(),
            }],
        },
        Sort::Application {
            name: "B".into(),
            arguments: Vec::new(),
        },
    ];
    for (index, left) in ordered.iter().enumerate() {
        for (other, right) in ordered.iter().enumerate() {
            assert_eq!(
                left.cmp(right),
                index.cmp(&other),
                "{left:?} against {right:?}"
            );
        }
    }

    assert_eq!(nested.into_parts(), ("List".to_owned(), Some(vec![map])));
    assert_eq!(
        Sort::Variable("T".into()).into_parts(),
        ("T".to_owned(), None)
    );
}

#[test]
fn json_writers_keep_serde_compatible_bytes() {
    let pattern = parse_pattern(r#"f{S{}}(X:S{}, \dv{S{}}("x"))"#).unwrap();
    assert_eq!(
        json::to_string(&pattern).unwrap(),
        r#"{"format":"KORE","version":1,"term":{"tag":"App","name":"f","sorts":[{"tag":"SortApp","name":"S","args":[]}],"args":[{"tag":"EVar","name":"X","sort":{"tag":"SortApp","name":"S","args":[]}},{"tag":"DV","sort":{"tag":"SortApp","name":"S","args":[]},"value":"x"}]}}"#
    );
    assert_eq!(
        json::to_string_pretty(&pattern).unwrap(),
        indoc::indoc! {r#"
        {
          "format": "KORE",
          "version": 1,
          "term": {
            "tag": "App",
            "name": "f",
            "sorts": [
              {
                "tag": "SortApp",
                "name": "S",
                "args": []
              }
            ],
            "args": [
              {
                "tag": "EVar",
                "name": "X",
                "sort": {
                  "tag": "SortApp",
                  "name": "S",
                  "args": []
                }
              },
              {
                "tag": "DV",
                "sort": {
                  "tag": "SortApp",
                  "name": "S",
                  "args": []
                },
                "value": "x"
              }
            ]
          }
        }"#}
    );
}

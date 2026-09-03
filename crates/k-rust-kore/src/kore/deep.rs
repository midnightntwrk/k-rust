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
        // that host-envelope residue; do not turn this syntax-layer test into that later ticket.
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

#[test]
fn deeply_nested_sorts_parse_on_a_one_mebibyte_thread() {
    let text_pattern = on_stack(1 << 20, || {
        let mut source = String::from("a{");
        for _ in 0..DEEP_SORT_LEVELS {
            source.push_str("S{");
        }
        source.push('T');
        for _ in 0..DEEP_SORT_LEVELS {
            source.push('}');
        }
        source.push_str("}()");
        parse_pattern(&source).expect("deep textual sort should parse")
    });
    on_stack(64 << 20, move || drop(text_pattern));

    let json_pattern = on_stack(1 << 20, || {
        let mut sort = String::from(r#"{"tag":"SortVar","name":"T"}"#);
        for _ in 0..DEEP_SORT_LEVELS {
            sort = format!(r#"{{"tag":"SortApp","name":"S","args":[{sort}]}}"#);
        }
        let source =
            format!(r#"{{"format":"KORE","version":1,"term":{{"tag":"Top","sort":{sort}}}}}"#);
        json::from_str(&source).expect("deep JSON sort should parse")
    });
    on_stack(64 << 20, move || drop(json_pattern));
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

#[test]
fn sort_exception_is_limited_to_recursive_traits() {
    // Parsing and every Pattern traversal are iterative. Sort intentionally retains its public
    // derived Clone/Eq/Ord/Drop traits because real KORE producers keep sort depth below four.
    let shallow = Sort::Application {
        name: "Map".into(),
        arguments: vec![Sort::Variable("K".into()), Sort::Variable("V".into())],
    };
    assert_eq!(shallow.clone(), shallow);
}

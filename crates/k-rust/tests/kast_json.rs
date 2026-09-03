use k_rust::kast::{ResolvedProductionId, Sort, Term, TermMetadata, TermSpan, json};
use serde::Deserialize;
use serde_json::Value;

const DEEP_APPLY_LEVELS: usize = 200_000;

fn on_stack<T: Send + 'static>(bytes: usize, work: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(bytes)
        .spawn(work)
        .expect("deep KAST worker should spawn")
        .join()
        .expect("deep KAST worker should finish")
}

fn value_unbounded(source: &str) -> Value {
    let mut deserializer = serde_json::Deserializer::from_str(source);
    deserializer.disable_recursion_limit();
    let value = Value::deserialize(&mut deserializer).unwrap();
    deserializer.end().unwrap();
    value
}

#[test]
fn reference_kast_json_v4_terms_round_trip_structurally() {
    let envelopes: Vec<Value> =
        serde_json::from_str(include_str!("fixtures/kast/terms.json")).unwrap();
    assert_eq!(envelopes.len(), 7);

    for envelope in envelopes {
        let term = json::from_str(&envelope.to_string()).unwrap();
        let encoded = json::to_string(&term).unwrap();
        assert_eq!(serde_json::from_str::<Value>(&encoded).unwrap(), envelope);
    }
}

#[test]
fn encoding_ignores_compiler_metadata() {
    let plain = Term::apply("f", vec![Term::variable("X")]);
    let annotated = plain.clone().with_metadata(TermMetadata {
        span: Some(TermSpan {
            source: k_rust::provenance::SourceId(0),
            start: 0,
            end: 4,
        }),
        production: Some(ResolvedProductionId(3)),
        sort: Some(Sort::new("Exp")),
        origin: None,
    });

    assert_eq!(
        json::to_string(&annotated).unwrap(),
        json::to_string(&plain).unwrap()
    );
}

#[test]
fn rejects_bad_envelopes_and_arities() {
    assert!(
        json::from_str(
            r#"{"format":"KORE","version":4,"term":{"node":"KSequence","arity":0,"items":[]}}"#
        )
        .is_err()
    );
    assert!(
        json::from_str(
            r#"{"format":"KAST","version":3,"term":{"node":"KSequence","arity":0,"items":[]}}"#
        )
        .is_err()
    );
    assert!(
        json::from_str(
            r#"{"format":"KAST","version":4,"term":{"node":"KSequence","arity":2,"items":[]}}"#
        )
        .is_err()
    );
}

#[test]
fn reference_kast_json_deep_program_round_trips() {
    // reference: k/result/bin/kast --definition ref --output json p2.test
    let source = include_str!("fixtures/reference/kast/json/deep-70/ref-p2.json");
    let expected = value_unbounded(source);
    let term = json::from_str(source).expect("the reference depth-146 document should decode");
    let encoded = json::to_string(&term).expect("the reference document should re-encode");
    assert_eq!(value_unbounded(&encoded), expected);
}

#[test]
fn round_trips_a_deep_apply_chain_without_a_depth_limit() {
    let terms = on_stack(1 << 20, || {
        let term = (0..DEEP_APPLY_LEVELS).fold(Term::variable("X"), |argument, _| {
            Term::apply("f", vec![argument])
        });
        let encoded = json::to_string(&term).expect("deep KAST should encode");
        let decoded = json::from_str(&encoded).expect("deep KAST should decode");
        assert_eq!(
            json::to_string(&decoded).unwrap(),
            encoded,
            "the iterative codecs must preserve the complete deep tree"
        );
        (term, decoded)
    });

    // Term retains recursive compiler-generated drop glue; this ticket covers its JSON codec.
    on_stack(64 << 20, move || drop(terms));
}

#[test]
fn json_writers_keep_serde_compatible_bytes() {
    let term = Term::apply("f", vec![Term::variable("X")]);
    assert_eq!(
        json::to_string(&term).unwrap(),
        r#"{"format":"KAST","version":4,"term":{"node":"KApply","label":{"node":"KLabel","name":"f","params":[]},"arity":1,"args":[{"node":"KVariable","name":"X"}]}}"#
    );
    assert_eq!(
        json::to_string_pretty(&term).unwrap(),
        indoc::indoc! {r#"
        {
          "format": "KAST",
          "version": 4,
          "term": {
            "node": "KApply",
            "label": {
              "node": "KLabel",
              "name": "f",
              "params": []
            },
            "arity": 1,
            "args": [
              {
                "node": "KVariable",
                "name": "X"
              }
            ]
          }
        }"#}
    );
}

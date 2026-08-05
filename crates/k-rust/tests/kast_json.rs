use k_rust::kast::json;
use serde_json::Value;

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

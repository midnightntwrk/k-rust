use std::collections::{BTreeMap, HashMap};

use k_rust::{
    backend::{Backend, BackendOptions, ObservedRequest, SearchRequest, TransitionIdOutput},
    kore::{codec, parser::parse_pattern},
};

const DEFINITION: &str = r#"[]
    module MAIN
        sort SortS{} []
        symbol a{}() : SortS{} [constructor{}()]
        symbol b{}() : SortS{} [constructor{}()]
        symbol c{}() : SortS{} [constructor{}()]
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(a{}(), \top{SortS{}}()), b{}()
        ) [label{}("a-to-b")]
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(b{}(), \top{SortS{}}()), c{}()
        ) [label{}("b-to-c")]
    endmodule []"#;

#[test]
fn public_observed_transition_ids_are_ordered_hash_keys() {
    let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::default()).unwrap();
    let state = codec::to_value(&parse_pattern("a{}()").unwrap()).unwrap();
    let result = backend
        .search_observed(ObservedRequest {
            request: SearchRequest {
                state,
                ..SearchRequest::default()
            },
            rules: None,
        })
        .unwrap();
    let [first, second] = result.states[0].branch.as_slice() else {
        panic!("expected a two-transition branch")
    };
    assert_eq!(first.rule, "a-to-b");
    assert_eq!(second.rule, "b-to-c");

    let same = TransitionIdOutput {
        rule: first.rule.clone(),
        target: first.target.clone(),
    };
    let different_rule = TransitionIdOutput {
        rule: second.rule.clone(),
        target: first.target.clone(),
    };
    let different_target = TransitionIdOutput {
        rule: first.rule.clone(),
        target: second.target.clone(),
    };
    assert_eq!(first, &same);
    assert_ne!(first, &different_rule);
    assert_ne!(first, &different_target);
    assert!(first < &different_rule);
    assert_eq!(
        first.cmp(&different_target),
        first.target.cmp(&different_target.target)
    );

    let ordered = BTreeMap::from([(first.clone(), 1), (second.clone(), 2)]);
    let hashed = HashMap::from([(first.clone(), 1), (second.clone(), 2)]);
    assert_eq!(ordered.get(&same), Some(&1));
    assert_eq!(hashed.get(&same), Some(&1));
    assert_eq!(ordered.get(&different_target), None);
    assert_eq!(hashed.get(&different_target), None);
    assert_eq!(
        serde_json::to_value(first).unwrap(),
        serde_json::json!({ "rule": first.rule, "target": first.target })
    );
}

use k_rust::{
    backend::{
        ExecuteRequest, ProveRequest, SearchPatternRequest, SearchRequest, deserialize_request,
    },
    kore::parser::parse_pattern,
};
use k_rust_backend::{
    proof::ProofOptions,
    rewrite::ExecutionOptions,
    search::SearchOptions,
    simplify::{DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationOptions},
};

#[test]
fn default_simplification_budgets_agree_across_all_surfaces() {
    let expected = DEFAULT_MAX_SIMPLIFICATION_ITERATIONS;

    assert_eq!(SimplificationOptions::default().max_iterations, expected);
    assert_eq!(
        ExecutionOptions::default().max_simplification_iterations,
        expected
    );
    assert_eq!(
        SearchOptions::default().max_simplification_iterations,
        expected
    );
    assert_eq!(
        ProofOptions::default().max_simplification_iterations,
        expected
    );
    let state = || parse_pattern("a{}()").unwrap();
    assert_eq!(
        ExecuteRequest::new(state()).max_simplification_iterations,
        expected
    );
    assert_eq!(
        SearchRequest::new(state()).max_simplification_iterations,
        expected
    );
    assert_eq!(
        SearchPatternRequest::new(state(), state()).max_simplification_iterations,
        expected
    );
    let state =
        r#"{"format":"KORE","version":1,"term":{"tag":"App","name":"a","sorts":[],"args":[]}}"#;
    let wire = format!(r#"{{"state":{state}}}"#);
    assert_eq!(
        deserialize_request::<ExecuteRequest>(&wire)
            .unwrap()
            .max_simplification_iterations,
        expected
    );
    assert_eq!(
        deserialize_request::<SearchRequest>(&wire)
            .unwrap()
            .max_simplification_iterations,
        expected
    );
    assert_eq!(
        deserialize_request::<SearchPatternRequest>(&format!(
            r#"{{"state":{state},"pattern":{state}}}"#
        ))
        .unwrap()
        .max_simplification_iterations,
        expected
    );
    assert_eq!(
        ProveRequest::default().max_simplification_iterations,
        expected
    );
}

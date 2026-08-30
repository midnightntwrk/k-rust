use k_rust::backend::{ExecuteRequest, ProveRequest};
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
    assert_eq!(
        ExecuteRequest::default().max_simplification_iterations,
        expected
    );
    assert_eq!(
        ProveRequest::default().max_simplification_iterations,
        expected
    );
}

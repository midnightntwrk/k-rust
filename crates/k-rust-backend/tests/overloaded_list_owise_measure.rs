//! A ground overloaded list case executes to one leaf without symbolic recovery.

#![cfg(all(feature = "measure", feature = "z3"))]

use k_rust_backend::{
    definition::BackendDefinition,
    rewrite::{ExecutionOptions, HaltReason, Pattern, execute_with_solver},
    smt::Z3Solver,
};
use k_rust_kore::{
    kore::parser::{parse_definition, parse_pattern},
    measure::{Counter, Snapshot, snapshot},
};

const OVERLOADED_LIST_OWISE: &str = include_str!("fixtures/overloaded-list-owise.kore");

fn definition_in(source: &str, module: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, module).expect("definition should internalize")
}

fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
    definition
        .internalize_pattern(&parse_pattern(source).expect("pattern should parse"), &[])
        .expect("pattern should internalize")
}

fn nonzero(snapshot: &Snapshot) -> Vec<(&'static str, u64)> {
    snapshot.iter().filter(|(_, value)| *value > 0).collect()
}

fn measured<T>(work: impl FnOnce() -> T) -> (T, Snapshot) {
    let before = snapshot();
    let result = work();
    (result, snapshot().delta(&before))
}

/// `state(getMatchingAux(.Bottoms, (1, .Bottoms)))` steps once to `failed()` without an
/// indeterminate recovery or SMT query.
#[test]
fn ground_nil_cons_case_selection_does_not_branch_or_query_smt() {
    let definition = definition_in(OVERLOADED_LIST_OWISE, "OVERLOADED-LIST-OWISE");
    let solver = Z3Solver::new(&definition).unwrap();
    let initial = pattern(
        &definition,
        "state{}(getMatchingAux{}(inj{SortBottoms{}, SortExps{}}(dotBottoms{}()), vals{}(one{}(), inj{SortBottoms{}, SortVals{}}(dotBottoms{}()))))",
    );
    let (result, delta) = measured(|| {
        execute_with_solver(
            &definition,
            initial,
            ExecutionOptions {
                max_depth: 1,
                ..ExecutionOptions::default()
            },
            &solver,
        )
    });
    eprintln!("ground nil/cons: {:?}", nonzero(&delta));
    for leaf in &result.leaves {
        eprintln!(
            "overloaded list leaf: depth={} constraints={} halt={:?}",
            leaf.depth,
            leaf.pattern.constraints.len(),
            leaf.halt_reason
        );
    }
    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    assert_eq!(
        result.leaves[0].pattern.term,
        pattern(&definition, "failed{}()").term
    );
    assert!(
        !matches!(
            result.leaves[0].halt_reason,
            HaltReason::Indeterminate { .. }
        ),
        "{:?}",
        result.leaves[0].halt_reason
    );
    assert_eq!(delta.get(Counter::RewriteRulesApplied), 1);
    assert_eq!(delta.get(Counter::RewriteIndeterminateRecoveries), 0);
    assert_eq!(delta.get(Counter::SmtQueries), 0);
}

//! The variable-identity boundary contract, checked whenever the k-rust pin moves.
//! Name equality includes kind and sort; byte identity is recorded but is not required,
//! because internalization can normalize collections and predicates independently of names.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::{collections::BTreeSet, time::Duration};

use k_rust::backend::{Backend, BackendError, BackendOptions};
use k_rust::kompile::CompileOptions;
use k_rust::kore::{
    ast::{Pattern, Variable},
    codec, walk,
};
use k_rust_backend::{
    definition::BackendDefinition,
    externalize,
    term::names::{VARIABLE_IDENTITY, VariableProvenance, decode_variable_name, split_marker},
};
use kink_native::NativeValidator;
use kink_native::execution::{ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile};

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
};

fn program() -> Pattern {
    let seq = |head, tail| support::app("Lblseq", vec![head, tail]);
    support::initial_state(
        seq(
            support::app("Lblcheck", vec![support::var("ExVarI0", "SortInt")]),
            seq(
                support::app("Lblcheck2", vec![support::var("ExVarI1", "SortInt")]),
                seq(
                    support::app("Lblgo", vec![support::var("X", "SortBox")]),
                    support::app("Lbldone", vec![]),
                ),
            ),
        ),
        "SortProg",
    )
}

fn bound_variables(pattern: &Pattern) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    walk::for_each_post_order(pattern, |node| match node {
        Pattern::Exists { variable, .. }
        | Pattern::Forall { variable, .. }
        | Pattern::Mu { variable, .. }
        | Pattern::Nu { variable, .. } => {
            variables.insert(variable.as_ref().clone());
        }
        _ => {}
    });
    variables
}

fn check_names(
    definition: &BackendDefinition,
    pattern: &Pattern,
    initial_variables: &BTreeSet<Variable>,
    initial_names: &BTreeSet<String>,
    decoded_initial_names: &BTreeSet<String>,
) -> bool {
    let internal = definition
        .internalize_pattern(pattern, &[])
        .expect("decoded state internalizes");
    let printed = externalize::constrained_pattern(&internal);
    assert_eq!(pattern.free_variables(), printed.free_variables());
    assert_eq!(bound_variables(pattern), bound_variables(&printed));
    for variable in pattern.free_variables() {
        if initial_variables.contains(&variable) {
            continue;
        }
        assert!(
            !initial_names.contains(&variable.name),
            "non-initial variable shares an initial wire name: {variable:?}"
        );
        let name = decode_variable_name(&variable.name).expect("name is in the encoding image");
        assert!(
            !decoded_initial_names.contains(&name),
            "non-initial variable shares an initial decoded name: {variable:?}"
        );
        // conflate's non-initial free variables are narrowing mints. A mint must never
        // share an initial name, regardless of its kind or sort.
        assert_eq!(
            split_marker(&name, &VariableProvenance::ALL).0,
            Some(VariableProvenance::Existential),
            "non-initial free variable is not an Existential mint: {variable:?}"
        );
    }
    serde_json::to_vec(&codec::to_value(pattern).expect("input encodes")).expect("input JSON")
        == serde_json::to_vec(&codec::to_value(&printed).expect("output encodes"))
            .expect("output JSON")
}

/// conflate's initial ExVarI0/ExVarI1 remain distinct from its narrowing mints.
/// With Z3 the five leaves and their stepped pre-states exercise free mints and binders;
/// without Z3 the one Indeterminate leaf still exercises the name round trip.
#[test]
fn decoded_leaf_and_step_names_round_trip() {
    assert_eq!(VARIABLE_IDENTITY, 2);
    let validator = NativeValidator::bind(support::load("conflate.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("conflate compiles");
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        "CONFLATE",
        BackendOptions {
            smt_timeout_ms: 4000,
            smt_retry_limit: 2,
        },
    )
    .expect("backend");
    let initial = program();
    let initial_variables = initial.free_variables();
    let initial_names = initial_variables.iter().map(|v| v.name.clone()).collect();
    let decoded_initial_names = initial_variables
        .iter()
        .map(|v| decode_variable_name(&v.name).expect("initial name is in the encoding image"))
        .collect();
    let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
    let execution = adapter
        .execute(&mut backend, &initial, BUDGET)
        .expect("leaf run");
    let stepped = adapter
        .execute_steps(&mut backend, &initial, BUDGET)
        .expect("stepped execution")
        .expect("step states decode");
    let expected_leaves = if cfg!(feature = "z3") { 5 } else { 1 };
    assert_eq!(execution.leaves().len(), expected_leaves);
    assert_eq!(stepped.states.len(), expected_leaves);
    if !cfg!(feature = "z3") {
        assert!(
            execution
                .leaves()
                .iter()
                .all(|leaf| leaf.halt == HaltClass::Indeterminate)
        );
    }
    let leaves = execution
        .leaves()
        .iter()
        .map(|leaf| codec::from_value(&leaf.branch.state).expect("leaf KORE decodes"))
        .collect::<Vec<_>>();
    backend
        .with_solver(None, |definition, _| {
            let patterns = leaves.iter().chain(stepped.states.iter().flatten());
            let mut checked = 0;
            let mut byte_identical = 0;
            for pattern in patterns {
                byte_identical += usize::from(check_names(
                    definition,
                    pattern,
                    &initial_variables,
                    &initial_names,
                    &decoded_initial_names,
                ));
                checked += 1;
            }
            eprintln!(
                "{}: {checked} states checked, {byte_identical} byte-identical re-encodings",
                SolverProfile::BUILD.name()
            );
            Ok::<_, BackendError>(())
        })
        .expect("round trips");
}

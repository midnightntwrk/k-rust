//! The variable-identity boundary contract, checked whenever the k-rust pin moves.
//! Name equality includes kind and sort; byte identity is recorded but is not required,
//! because internalization can normalize collections and predicates independently of names.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::{collections::BTreeSet, time::Duration};

use k_rust::backend::{Backend, BackendError, BackendOptions};
use k_rust::kast::{Sort, Term};
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
use kink_native::execution::{
    ExecutionAdapter, ExecutionAdapterFailure, ExecutionBudget, HaltClass, SolverProfile,
};
use kink_native::execution_difference::{
    CertifiedSide, DifferenceCertificate, Exclusion, NotProvedReason, StateSequences,
    certify_difference, definition_facts,
};
use kink_native::{
    bridge,
    feasibility::{LeafFeasibility, TestInitialState},
};
use kink_patch::{Edit, Patch, TermRef};

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
    classified_initial_names: &BTreeSet<String>,
) -> bool {
    let internal = definition
        .admit_unverified(pattern, &[])
        .internalize_pattern()
        .expect("read state internalizes");
    let internal_variables = internal
        .term
        .attributes()
        .variables
        .iter()
        .cloned()
        .chain(
            internal
                .constraints
                .iter()
                .flat_map(|predicate| predicate.free_variables()),
        )
        .map(|variable| variable.name.to_string())
        .collect::<BTreeSet<_>>();
    let wire_names = pattern
        .free_variables()
        .into_iter()
        .map(|variable| variable.name)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        internal_variables, wire_names,
        "v3 reads free names verbatim"
    );
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
            !classified_initial_names.contains(&name),
            "non-initial variable shares an initial classified name: {variable:?}"
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
/// Contract change (VI-03F): version 3 reads names verbatim and preserves printed identity.
#[test]
fn decoded_leaf_and_step_names_round_trip() {
    assert_eq!(VARIABLE_IDENTITY, 3);
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
    let classified_initial_names = initial_variables
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
        .map(|leaf| codec::from_value(&leaf.branch.state).expect("leaf KORE reads"))
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
                    &classified_initial_names,
                ));
                checked += 1;
            }
            assert_eq!(checked, if cfg!(feature = "z3") { 21 } else { 2 });
            eprintln!(
                "{}: {checked} states checked, {byte_identical} byte-identical re-encodings",
                SolverProfile::BUILD.name()
            );
            Ok::<_, BackendError>(())
        })
        .expect("round trips");
}

fn leaf_rows(
    fixture: &str,
    module: &str,
    initial: &Pattern,
) -> Vec<(HaltClass, LeafFeasibility, Option<bridge::DiscardReason>)> {
    let validator = NativeValidator::bind(support::load(fixture), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .expect("backend");
    ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute(&mut backend, initial, BUDGET)
        .expect("event-free execution")
        .leaves()
        .iter()
        .map(|leaf| (leaf.halt, leaf.feasibility, bridge::discarded(leaf)))
        .collect()
}

/// Before VI, ExVarI0 made Z3 leaf 0 (Stuck, Unsat, Some(Unsat)).
/// Under VI both initial names have the neutral name's three undiscarded leaves;
/// without Z3 each run has one (Indeterminate, Syntactic, None) leaf.
#[test]
fn initial_names_do_not_conflate_with_narrowing_mints() {
    for name in ["A", "ExVarI0"] {
        let initial = support::initial_state(
            support::app(
                "Lblseq",
                vec![
                    support::app("Lblcheck", vec![support::var(name, "SortInt")]),
                    support::app(
                        "Lblseq",
                        vec![
                            support::app("Lblmk", vec![]),
                            support::app("Lbldone", vec![]),
                        ],
                    ),
                ],
            ),
            "SortProg",
        );
        let expected = if cfg!(feature = "z3") {
            vec![
                (HaltClass::Stuck, LeafFeasibility::Unknown, None),
                (HaltClass::Stuck, LeafFeasibility::Unknown, None),
                (HaltClass::Stuck, LeafFeasibility::Solver, None),
            ]
        } else {
            vec![(HaltClass::Indeterminate, LeafFeasibility::Syntactic, None)]
        };
        assert_eq!(
            leaf_rows("conflate2.k", "CONFLATE2", &initial),
            expected,
            "{name}"
        );
    }
}

/// Before VI, nine burns made Z3 leaf 0 (Stuck, Unsat, Some(Unsat)).
/// Under VI eight and nine burns both have three (Stuck, Unknown, None) leaves;
/// without Z3 each has one (Indeterminate, Syntactic, None) leaf.
#[test]
fn fresh_counters_do_not_conflate_distinct_narrowing_mints() {
    for burns in [8, 9] {
        let mut program = support::app(
            "Lblseq",
            vec![
                support::app("Lblnew2", vec![]),
                support::app("Lbldone", vec![]),
            ],
        );
        for _ in 0..burns {
            program = support::app("Lblseq", vec![support::app("LblburnNew", vec![]), program]);
        }
        program = support::app("Lblseq", vec![support::app("Lblnew1", vec![]), program]);
        let initial = support::initial_state(program, "SortProg");
        assert!(initial.free_variables().is_empty(), "ground initial state");
        let expected = if cfg!(feature = "z3") {
            vec![(HaltClass::Stuck, LeafFeasibility::Unknown, None); 3]
        } else {
            vec![(HaltClass::Indeterminate, LeafFeasibility::Syntactic, None)]
        };
        assert_eq!(
            leaf_rows("conflate3.k", "CONFLATE3", &initial),
            expected,
            "{burns} burns"
        );
    }
}

fn scope_backend(validator: &NativeValidator, patch: Option<&Patch>) -> Backend {
    let side = match patch {
        Some(patch) => validator.validate(patch).expect("scope mutant compiles"),
        None => validator
            .compile_baseline()
            .expect("scope baseline compiles"),
    };
    Backend::new(
        &side.artifacts().definition_kore,
        "SCOPEFORGE",
        BackendOptions::default(),
    )
    .expect("scope backend")
}

fn scope_mutant(validator: &NativeValidator, positive_control: bool) -> Patch {
    let baseline = validator.baseline();
    let variable = |name: &str| Term::Variable {
        name: name.into(),
        sort: Some(Sort::new("Ab")),
    };
    let x = variable("X");
    let y = variable("?Y");
    let right = if positive_control {
        Term::apply("pair", vec![Term::apply("a", vec![]); 2])
    } else {
        Term::apply("pair", vec![x.clone(), y.clone()])
    };
    let replacement = Term::Rewrite {
        left: Box::new(Term::apply("start", vec![x.clone()])),
        right: Box::new(right),
    };
    let at = TermRef::new(support::rule(baseline, "SCOPEFORGE.startA"), [0]);
    let mut edits = vec![
        Edit::ReplaceTerm {
            expected: baseline.term(&at).expect("rule body").clone(),
            replacement,
            at,
        },
        Edit::DeleteSentence {
            at: support::rule(baseline, "SCOPEFORGE.startB"),
        },
    ];
    if !positive_control {
        let at = TermRef::new(support::rule(baseline, "SCOPEFORGE.startA"), [2]);
        edits.push(Edit::ReplaceTerm {
            expected: baseline.term(&at).expect("ensures").clone(),
            replacement: Term::apply("_=/=K_", vec![y, x]),
            at,
        });
    }
    Patch::new(edits).expect("scope patch")
}

fn scope_sequences(backend: &mut Backend, initial: &Pattern) -> StateSequences {
    ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute_steps(backend, initial, BUDGET)
        .expect("scope run")
        .expect("step states decode")
        .certificate_sequences()
        .expect("certificate sequences")
}

/// VI-AT1: the identical-relation existential mutant has NoWitness in both profiles.
/// Per-position scope prefixes contain `.`, so the forged EI!M0!1 cannot equal a scope
/// name (variable-identity README 16.3). Contract change (VI-03F): every KORE identifier
/// is accepted verbatim, including EI-bB0-u2e-0-b1; a non-identifier is refused.
/// The positive control always returns pair(a,a), proving [Clash, Clash] under Z3.
/// Without Z3 baseline narrowing stops at the initial state, so that control has NoWitness.
#[test]
fn scope_name_forgery_does_not_prove_an_identical_relation() {
    let validator = NativeValidator::bind(support::load("scopeforge.k"), CompileOptions::default());
    let mut baseline = scope_backend(&validator, None);
    let mut mutant = scope_backend(&validator, Some(&scope_mutant(&validator, false)));
    let mut positive = scope_backend(&validator, Some(&scope_mutant(&validator, true)));
    let facts = definition_facts(&mut baseline).expect("baseline facts");
    let mutant_facts = definition_facts(&mut mutant).expect("mutant facts");
    let positive_facts = definition_facts(&mut positive).expect("positive facts");
    for name in ["X", "EI-bM0-b1"] {
        let initial = support::initial_state(
            support::app("Lblstart", vec![support::var(name, "SortAb")]),
            "SortProg",
        );
        let bs = scope_sequences(&mut baseline, &initial);
        let ms = scope_sequences(&mut mutant, &initial);
        assert_eq!(
            certify_difference(
                &mut baseline,
                TestInitialState::of_test(&initial),
                &facts,
                &mutant_facts,
                &bs,
                &ms
            ),
            DifferenceCertificate::NotProved(NotProvedReason::NoWitness),
            "{name}",
        );
        let ps = scope_sequences(&mut positive, &initial);
        let certificate = certify_difference(
            &mut baseline,
            TestInitialState::of_test(&initial),
            &facts,
            &positive_facts,
            &bs,
            &ps,
        );
        let expected = if cfg!(feature = "z3") {
            DifferenceCertificate::Proved {
                witness_side: CertifiedSide::Mutant,
                witness_leaf: 0,
                exclusions: vec![Exclusion::Clash, Exclusion::Clash],
            }
        } else {
            DifferenceCertificate::NotProved(NotProvedReason::NoWitness)
        };
        assert_eq!(certificate, expected, "positive control {name}");
        // The portable control cannot compare a post-state the baseline never exposes.
        assert_eq!(bs.leaves.len(), if cfg!(feature = "z3") { 2 } else { 1 },);
        if !cfg!(feature = "z3") {
            assert_eq!(bs.leaves[0].halt, HaltClass::Indeterminate);
            assert_eq!(bs.leaves[0].states.len(), 1);
        }
    }
    let initial = support::initial_state(
        support::app("Lblstart", vec![support::var("EI-bB0-u2e-0-b1", "SortAb")]),
        "SortProg",
    );
    let bs = scope_sequences(&mut baseline, &initial);
    let ms = scope_sequences(&mut mutant, &initial);
    assert_eq!(
        certify_difference(
            &mut baseline,
            TestInitialState::of_test(&initial),
            &facts,
            &mutant_facts,
            &bs,
            &ms
        ),
        DifferenceCertificate::NotProved(NotProvedReason::NoWitness),
        "ordinary identifier EI-bB0-u2e-0-b1",
    );
    let invalid = support::initial_state(
        support::app("Lblstart", vec![support::var("EI!B0.0!1", "SortAb")]),
        "SortProg",
    );
    let failure = ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute_steps(&mut baseline, &invalid, BUDGET)
        .expect_err("non-identifier refused");
    assert_eq!(
        failure,
        ExecutionAdapterFailure::InvalidState(
            "VariableName { name: \"EI!B0.0!1\", set: false }".into(),
        )
    );
}

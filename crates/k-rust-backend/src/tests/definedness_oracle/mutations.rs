//! V7: each mutation switch (`confluence::switches`, and the oracle's own outermost evaluation)
//! must make the oracle test meant for its class fail at the default size. A switch whose test
//! still passes is a test that cannot see its class.

use super::{DEFAULT_CASES, DEFAULT_SEED, Rng, checks::check_definition, engine::OUTERMOST};
use crate::confluence::switches::{self, Switches};

/// The failures of the V4-V6 run (templates and random definitions) under `switches`.
fn contract_failures(switches: Switches) -> Vec<String> {
    switches::with(switches, || {
        super::run_random(0, DEFAULT_CASES, DEFAULT_SEED).failures
    })
}

/// The failures of the probes under `switches`, with their unmet expectations.
fn probe_failures(switches: Switches) -> Vec<String> {
    switches::with(switches, || {
        let (tally, mut unmet) = super::run_probes();
        unmet.extend(tally.failures);
        unmet
    })
}

/// The failures of V3 under `switches`.
fn completeness_failures(switches: Switches) -> Vec<String> {
    switches::with(switches, || {
        super::completeness::run_completeness(DEFAULT_CASES, DEFAULT_SEED).failures
    })
}

/// The failures of V2 under `switches`.
fn unifier_failures(switches: Switches) -> Vec<String> {
    switches::with(switches, || {
        let tally = super::unifier::run_unifier(DEFAULT_CASES * 80, DEFAULT_SEED);
        let mut failures = tally.failures;
        if tally.unresolved * 100 > tally.pairs * 15 {
            failures.push("unresolved above the ceiling".into());
        }
        failures
    })
}

/// The failures of the claim-dependent refutation probe: `f(X) = c1 requires isH1(h(2))` beside
/// `f(X) = c2`, where the total `isH1` is `true` on `h(1)` and `false` otherwise (`owise`).
/// Refuting the pair needs `h(2)` to be a value other than `h(1)`, so that the `owise` equation
/// applies: a claim about `h`, which the pair itself withdraws (T-sym, through the `requires`).
/// The check runs with every claim withheld, so it does not refute the pair, and `h` must be
/// tainted.
fn claim_dependent_failures(switches: Switches) -> Vec<String> {
    use super::language::{Definition, OWISE_PRIORITY, app, cons, int, var};
    let definition = Definition::new(&["A", "B"])
        .constructor("c1", &[], "B")
        .constructor("c2", &[], "B")
        .head("h", &["Int"], "A")
        .total_function("isH1", &["A"], "Bool")
        .equation(
            app("isH1", vec![app("h", vec![int(1)])]),
            super::generator::boolean(true),
        )
        .full(
            app("isH1", vec![var("VarY", "A")]),
            super::generator::boolean(false),
            None,
            None,
            OWISE_PRIORITY,
        )
        .function("f", &["A"], "B")
        .conditional(
            app("f", vec![var("VarX", "A")]),
            cons("c1"),
            Some(app("isH1", vec![app("h", vec![int(2)])])),
        )
        .equation(app("f", vec![var("VarX", "A")]), cons("c2"));
    switches::with(switches, || {
        let mut rng = Rng(DEFAULT_SEED);
        let (mut tally, verdict) = check_definition(
            "claim-dependent refutation",
            &definition,
            &[app("f", vec![app("h", vec![int(1)])])],
            &[],
            &mut rng,
        );
        if std::env::var_os("KRUST_DEFINEDNESS_ORACLE_VERBOSE").is_some() {
            eprintln!("claim-dependent probe: tainted {:?}", verdict.tainted);
        }
        if !verdict.tainted.contains("h") {
            tally
                .failures
                .push(format!("h is not tainted: {:?}", verdict.tainted));
        }
        tally.failures
    })
}

#[test]
fn the_claim_dependent_refutation_probe_taints_the_head() {
    super::on_large_stack(|| {
        let failures = claim_dependent_failures(Switches::default());
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    });
}

/// Asserts that `run` under the switch `name` reports a failure.
fn assert_caught(name: &str, failures: Vec<String>) {
    assert!(
        !failures.is_empty(),
        "the switch {name} went unnoticed by the test meant to catch it"
    );
}

macro_rules! mutation {
    ($(#[$attribute:meta])* $test:ident, $field:ident, $run:ident) => {
        $(#[$attribute])*
        #[test]
        fn $test() {
            super::on_large_stack(|| {
                let switches = Switches {
                    $field: true,
                    ..Switches::default()
                };
                assert_caught(stringify!($field), $run(switches));
            });
        }
    };
}

mutation!(
    dropping_inner_positions_is_caught,
    drop_inner_positions,
    completeness_failures
);
mutation!(
    dropping_injected_inner_pairs_is_caught,
    drop_injected_inner,
    completeness_failures
);
mutation!(
    dropping_glb_branches_is_caught,
    drop_glb_branches,
    unifier_failures
);
mutation!(dropping_lifting_is_caught, drop_lifting, unifier_failures);
mutation!(
    dropping_lesser_productions_is_caught,
    drop_lesser_productions,
    unifier_failures
);
mutation!(
    separating_inner_pairs_by_priority_is_caught,
    separate_inner_by_priority,
    completeness_failures
);
mutation!(
    refuting_every_condition_is_caught,
    refute_every_condition,
    contract_failures
);
mutation!(
    ignoring_ensures_is_caught,
    ignore_ensures,
    contract_failures
);
mutation!(
    erasing_partial_residuals_is_caught,
    erase_partial_residuals,
    contract_failures
);
mutation!(
    decomposing_a_refused_redex_is_caught,
    decompose_refused_redex,
    contract_failures
);
mutation!(
    ignoring_higher_groups_is_caught,
    ignore_higher_groups,
    contract_failures
);
mutation!(
    joining_with_symbolic_equations_is_caught,
    join_with_symbolic,
    contract_failures
);
mutation!(
    skipping_renaming_apart_is_caught,
    no_rename_apart,
    probe_failures
);
mutation!(
    checking_with_claims_is_caught,
    claims_during_check,
    claim_dependent_failures
);
mutation!(dropping_t1_is_caught, drop_t1, contract_failures);
mutation!(
    dropping_tsym_on_right_hand_sides_is_caught,
    drop_tsym_rhs,
    contract_failures
);
mutation!(dropping_tobs_is_caught, drop_tobs, contract_failures);
mutation!(
    seeding_heads_only_is_caught,
    seed_heads_only,
    contract_failures
);
mutation!(
    admitting_equation_heads_is_caught,
    admit_equation_heads,
    contract_failures
);
mutation!(
    admitting_certificates_is_caught,
    admit_certificates,
    contract_failures
);

/// The oracle's own discipline: with outermost steps too, CS M1's `f(b())` has the normal forms
/// `c` and `d`, so V4 fails on its template, showing the template has teeth.
#[test]
fn an_oracle_that_is_not_innermost_fails_the_priority_template() {
    super::on_large_stack(|| {
        OUTERMOST.set(true);
        let failures = super::run_random(0, 0, DEFAULT_SEED).failures;
        OUTERMOST.set(false);
        assert!(
            failures
                .iter()
                .any(|failure| failure.starts_with("template priority (CS M1)")),
            "{failures:?}"
        );
    });
}

/// The V6 (d) failures of the V4-V6 run under `switches`: review 1's classes, which only the
/// forced-consequence check sees independently of the closure's own rules.
fn forced_failures(switches: Switches) -> Vec<String> {
    contract_failures(switches)
        .into_iter()
        .filter(|failure| failure.contains(super::checks::FORCED))
        .collect()
}

mutation!(
    collapsing_every_total_symbol_is_caught_by_the_forced_consequences,
    collapse_every_total,
    forced_failures
);
mutation!(
    reading_stuck_totals_as_bottom_is_caught_by_the_forced_consequences,
    stuck_total_is_bottom,
    forced_failures
);
mutation!(
    dropping_the_supersort_closure_is_caught_by_the_forced_consequences,
    drop_supersort_inhabitation,
    forced_failures
);
mutation!(
    dropping_t_obs_is_caught_by_the_forced_consequences,
    drop_tobs,
    forced_failures
);

/// V9's failures on N1 observed by a function under `switches`: the template where only T-obs
/// makes a pair relevant to the load's scope.
fn scope_failures_on_observation_by_a_function(switches: Switches) -> Vec<String> {
    contract_failures(switches)
        .into_iter()
        .filter(|failure| {
            failure.starts_with("template observation by a function:")
                && failure.contains(super::checks::SCOPES)
        })
        .collect()
}

mutation!(
    relevance_without_t_obs_is_caught_by_the_scope_comparison,
    relevance_ignores_tobs,
    scope_failures_on_observation_by_a_function
);

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
    use super::language::{app, int};
    let definition = super::generator::claim_dependent();
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

/// The failures of the refutation with a withdrawn claim
/// (`generator::withdrawn_claim_refutation`) under `switches`: `hv` keeps a claim that holds in
/// no model unless the check refutes no pair with a claim another pair withdraws.
fn withdrawn_claim_failures(switches: Switches) -> Vec<String> {
    let definition = super::generator::withdrawn_claim_refutation();
    switches::with(switches, || match super::checks::backend(&definition) {
        Ok(backend) => {
            let tainted = backend.value_claims().tainted_symbols();
            if tainted.iter().any(|symbol| symbol.as_ref() == "hv") {
                Vec::new()
            } else {
                vec![format!("hv is not tainted: {tainted:?}")]
            }
        }
        Err(error) => vec![format!("rejected: {error}")],
    })
}

#[test]
fn a_refutation_with_a_claim_another_pair_withdraws_taints_the_head() {
    super::on_large_stack(|| {
        let failures = withdrawn_claim_failures(Switches::default());
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    });
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
mutation!(
    checking_with_claims_another_pair_withdraws_is_caught,
    claims_during_check,
    withdrawn_claim_failures
);
mutation!(
    discharging_before_the_check_keeps_a_withdrawn_claim,
    discharge_before_check,
    withdrawn_claim_failures
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

/// The failures of the axiom-instance harness (`axioms`) under `switches`, on the oracle's and
/// the harness's templates, the probes and their variants, and the fixtures.
fn axiom_failures(switches: Switches) -> Vec<String> {
    switches::with(switches, || super::run_axioms(0, DEFAULT_SEED).failures)
}

/// The three switches that drop an overlap modulo the overload axioms withdraw no fewer claims:
/// on the oracle's templates, the harness's definitions and random definitions, the heads a
/// switch leaves tainted include those the check taints without it, and where they are the same
/// the claims are the same. Each switch still changes the pairs named somewhere, so the run
/// reaches the overlaps it drops. This is why the axiom-instance harness, which judges claims,
/// cannot see them (`axiom_mutation!`).
#[test]
fn the_overload_switches_withdraw_no_fewer_claims() {
    super::on_large_stack(|| {
        let mut definitions = super::generator::templates()
            .into_iter()
            .map(|(name, definition, _)| (name, definition))
            .collect::<Vec<_>>();
        definitions.extend(super::axiom_definitions(DEFAULT_CASES, DEFAULT_SEED));
        for case in 0..DEFAULT_CASES * 20 {
            let mut rng = Rng(DEFAULT_SEED ^ case.wrapping_mul(0x9e37_79b9_7f4a_7c15));
            definitions.push((
                format!("random case {case}"),
                super::generator::random_definition(&mut rng).0,
            ));
        }
        let mut failures = Vec::new();
        for (name, switches) in [
            (
                "drop_injected_inner",
                Switches {
                    drop_injected_inner: true,
                    ..Switches::default()
                },
            ),
            (
                "drop_lifting",
                Switches {
                    drop_lifting: true,
                    ..Switches::default()
                },
            ),
            (
                "drop_lesser_productions",
                Switches {
                    drop_lesser_productions: true,
                    ..Switches::default()
                },
            ),
        ] {
            let mut pairs_changed = false;
            for (label, definition) in &definitions {
                let (Ok(off), Ok(on)) = (
                    super::checks::backend(definition),
                    switches::with(switches, || super::checks::backend(definition)),
                ) else {
                    continue;
                };
                let (off_tainted, on_tainted) = (
                    off.value_claims().tainted_symbols(),
                    on.value_claims().tainted_symbols(),
                );
                let differences = off
                    .value_claims()
                    .claim_differences(on.value_claims(), &off);
                pairs_changed |= differences
                    .iter()
                    .any(|difference| difference.starts_with("warned pairs"));
                let claims = differences
                    .iter()
                    .filter(|difference| !difference.starts_with("warned pairs"))
                    .collect::<Vec<_>>();
                let fewer = off_tainted
                    .iter()
                    .any(|symbol| !on_tainted.contains(symbol));
                let rows = claims
                    .iter()
                    .any(|difference| difference.starts_with("tainted indexes of the rows"));
                if fewer || rows || (off_tainted == on_tainted && !claims.is_empty()) {
                    failures.push(format!("{name} on {label}: {claims:?}"));
                }
            }
            if !pairs_changed {
                failures.push(format!("{name} changes no pair named"));
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    });
}

/// The harness's own acceptance: each switch below makes a claim false, or makes the check
/// accept a definition that has no model or whose evaluation depends on its axioms' order, on
/// one of the definitions the harness runs, and the harness sees it. That is 25 of the 31 defect
/// switches of `confluence::switches` (`no_condition_memo` configures the load and seeds no
/// defect). The other six it cannot see:
///
/// - `drop_injected_inner`, `drop_lifting` and `drop_lesser_productions` make no claim false:
///   each drops a pair whose overlap exists only modulo an overload axiom, and the check also
///   pairs the same outer equation with that overload axiom at the position where it applies
///   (`len2`'s second equation with `consE`'s overload axiom in `generator::lowered_family`,
///   `use`'s equation with `go`'s in `generator::injected_inner`). That pair's overlap is one
///   overload step from the dropped one, and its lowered side holds the subterm the dropped
///   pair's other equation rewrites, so it fails to join where the dropped pair does and
///   withdraws the same heads. `drop_lifting` also takes lifting out of the join, so pairs that
///   join modulo the overload axioms are named, which withdraws more claims, never fewer.
///   `the_overload_switches_withdraw_no_fewer_claims` measures this;
/// - `claims_during_check`, and `discharge_before_check`, which runs the check the same way (its
///   other effect is on the rewrite rules' definedness, which no equation instance reads): the
///   check refutes a pair with a claim that another pair withdraws, and so keeps a false claim
///   (`generator::withdrawn_claim_refutation`: `f(X) = hv(1) requires isD(g(2))` beside
///   `f(X) = hv(2)`, with `g(1) = d` beside `g(1) = g(2)`; every model has `g(2) = d` and so
///   `hv(1) = hv(2)`, but `hv` keeps its claims). The harness's judge is the backend's
///   evaluation, which applies an equation from left to right only: `g(2) = d` follows from
///   `g(1) = g(2)` read from right to left, so `isD(g(2))` stays undecided and every instance
///   that would show `hv(1) = hv(2)` is skipped. Deciding it takes equational reasoning in both
///   directions, a second engine;
/// - `self_pair_reads_opaque_rhs_as_nothing`: its self pairs have a disjunction, `\top` or
///   predicates as right-hand side, which the harness does not instantiate.
///
/// The oracle sees the overload switches by comparing the pairs with its own (V2 and the
/// completeness run), `claims_during_check` with the claim-dependent probe and both check
/// switches with `withdrawn_claim_failures`, `discharge_before_check` also by the rewrite rule's
/// definedness obligation (`confluence::tests::discharging_before_the_check_is_caught`), and the
/// last by V3c's brute-force self pairs
/// (`the_self_pair_brute_force_sees_a_disjunction_read_as_reading_nothing`).
macro_rules! axiom_mutation {
    ($test:ident, $field:ident) => {
        #[test]
        fn $test() {
            super::on_large_stack(|| {
                let switches = Switches {
                    $field: true,
                    ..Switches::default()
                };
                assert!(
                    !axiom_failures(switches).is_empty(),
                    "the switch {} went unnoticed by the axiom-instance harness",
                    stringify!($field)
                );
            });
        }
    };
}

axiom_mutation!(
    the_axiom_harness_sees_dropped_inner_positions,
    drop_inner_positions
);
axiom_mutation!(
    the_axiom_harness_sees_dropped_glb_branches,
    drop_glb_branches
);
axiom_mutation!(
    the_axiom_harness_sees_inner_pairs_separated_by_priority,
    separate_inner_by_priority
);
axiom_mutation!(
    the_axiom_harness_sees_every_condition_refuted,
    refute_every_condition
);
axiom_mutation!(the_axiom_harness_sees_ignored_ensures, ignore_ensures);
axiom_mutation!(
    the_axiom_harness_sees_erased_partial_residuals,
    erase_partial_residuals
);
axiom_mutation!(
    the_axiom_harness_sees_a_decomposed_refused_redex,
    decompose_refused_redex
);
axiom_mutation!(
    the_axiom_harness_sees_ignored_higher_groups,
    ignore_higher_groups
);
axiom_mutation!(
    the_axiom_harness_sees_joins_with_symbolic_equations,
    join_with_symbolic
);
axiom_mutation!(
    the_axiom_harness_sees_skipped_renaming_apart,
    no_rename_apart
);
axiom_mutation!(the_axiom_harness_sees_a_dropped_t1, drop_t1);
axiom_mutation!(
    the_axiom_harness_sees_a_dropped_tsym_on_right_hand_sides,
    drop_tsym_rhs
);
axiom_mutation!(the_axiom_harness_sees_a_dropped_tobs, drop_tobs);
axiom_mutation!(the_axiom_harness_sees_heads_only_seeding, seed_heads_only);
axiom_mutation!(
    the_axiom_harness_sees_admitted_equation_heads,
    admit_equation_heads
);
axiom_mutation!(
    the_axiom_harness_sees_admitted_certificates,
    admit_certificates
);
axiom_mutation!(
    the_axiom_harness_sees_every_total_symbol_collapsed,
    collapse_every_total
);
axiom_mutation!(
    the_axiom_harness_sees_stuck_totals_read_as_bottom,
    stuck_total_is_bottom
);
axiom_mutation!(
    the_axiom_harness_sees_a_dropped_supersort_closure,
    drop_supersort_inhabitation
);
axiom_mutation!(
    the_axiom_harness_sees_relevance_without_tobs,
    relevance_ignores_tobs
);
axiom_mutation!(
    the_axiom_harness_sees_several_matches_dropped,
    drop_several_matches
);
axiom_mutation!(
    the_axiom_harness_sees_self_pairs_that_ignore_ensures,
    self_pair_ignores_ensures
);
axiom_mutation!(the_axiom_harness_sees_a_misread_int_le, misread_int_le);
axiom_mutation!(
    the_axiom_harness_sees_relevance_that_needs_both_equations,
    relevance_needs_both
);
axiom_mutation!(
    the_axiom_harness_sees_dropped_collection_edges,
    drop_collection_edges
);

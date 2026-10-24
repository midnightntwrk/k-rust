//! V7: each defect switch of `confluence::switches` must make a test meant for its class fail at
//! the default size: the axiom-instance harness where the switch makes a claim false or lets the
//! check accept a definition it must not (`axiom_mutation!`), and the oracle's comparisons with
//! the check's own steps, the probes and the scope comparison (`mutation!`), which also see the
//! switches the harness cannot. A switch whose test still passes is a test that cannot see its
//! class.

use super::{DEFAULT_CASES, DEFAULT_SEED, Rng, checks::check_definition};
use crate::confluence::switches::{self, Switches};

/// The failures of the V9 and memo run (templates and random definitions) under `switches`.
fn scope_failures(switches: Switches) -> Vec<String> {
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
    let definition = super::generator::claim_dependent();
    switches::with(switches, || {
        let (mut tally, verdict) = check_definition("claim-dependent refutation", &definition);
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

/// The constants check's failures (`checks::junk_check`) on the two empty-sort templates
/// (`generator::empty_sort`, the repro `r4-empty`) under `switches`, each judged where its full
/// check reports nothing, in `D+` (`constants`) or in the definition itself; and whether the
/// full check reported nothing on the clashing one.
fn empty_sort_failures(switches: Switches, constants: bool) -> (Vec<String>, bool) {
    use super::language::Definition;
    let base = Definition::new(&["A"])
        .constructor("c", &[], "A")
        .constructor("d", &[], "A");
    switches::with(switches, || {
        let mut failures = Vec::new();
        let mut clash_accepted = false;
        for clash in [true, false] {
            let (definition, _) = super::generator::empty_sort(base.clone(), clash);
            let backend = super::checks::backend(&definition).expect("the template loads");
            let full = backend.value_claims_in_scope(crate::confluence::CheckScope::All);
            if full.unjoined().is_empty() && full.violations().is_empty() {
                clash_accepted |= clash;
                failures.extend(
                    super::checks::junk_check(&definition, &[], constants, &mut Rng(DEFAULT_SEED))
                        .failures,
                );
            }
        }
        (failures, clash_accepted)
    })
}

/// `separate_uninhabited` restores vacuity: the check sets aside `fEm(X:Em) = c` beside
/// `fEm(X:Em) = d` over the empty `Em`, and the full check reports nothing. Without `D+`'s
/// constants nothing sees it: `Em` has no value, so the clashing instance does not exist, and no
/// other run of the oracle or the harness judges an element of `Em`. With them `fEm(*_Em)` has
/// the normal forms `c` and `d`. Without the switch the full check names the pair, and the
/// joining template holds in `D+`.
#[test]
fn restored_vacuity_goes_unnoticed_without_the_constants_and_is_caught_with_them() {
    super::on_large_stack(|| {
        let switch = Switches {
            separate_uninhabited: true,
            ..Switches::default()
        };
        let (without, accepted) = empty_sort_failures(switch, false);
        assert!(accepted, "the switch leaves the clashing pair reported");
        assert!(without.is_empty(), "{}", without.join("\n"));
        let (with, _) = empty_sort_failures(switch, true);
        assert!(
            with.iter()
                .any(|failure| failure.contains("fEm(junkEm) has the normal forms c, d")),
            "{with:?}"
        );
        let (off, accepted) = empty_sort_failures(Switches::default(), true);
        assert!(!accepted, "the full check names the clashing pair");
        assert!(off.is_empty(), "{}", off.join("\n"));
    });
}

mutation!(
    restored_vacuity_is_caught_by_the_constants,
    separate_uninhabited,
    scope_failures
);

/// The shapes of `generator::constructor_split` whose full check reports nothing under
/// `switches`.
fn accepted_splits(switches: Switches) -> Vec<super::generator::Split> {
    switches::with(switches, || {
        super::generator::Split::ALL
            .into_iter()
            .filter(|split| {
                let definition = super::generator::constructor_split(*split);
                let backend = super::checks::backend(&definition).expect("the template loads");
                let full = backend.value_claims_in_scope(crate::confluence::CheckScope::All);
                full.unjoined().is_empty() && full.violations().is_empty()
            })
            .collect()
    })
}

/// F1 and F2 (`confluence/join.rs`): the pair joins after a split on a residual over the sort
/// `Tc`, whose constructors cover it, when each branch's conditions are refuted under its
/// unifier (WASM's `sparse-bytes.k:121/133` shape) or each branch joins. It stays named where a
/// branch's conditions may hold, where a constructor has no branch, where an empty subsort gives
/// `Tc` an element in every model that no constructor builds, where an equation head or a total
/// function produces `Tc`, where a branch binds a constructor to a specific argument, and where
/// `Tc` is not surely inhabited. Each defect switch of the two rules accepts the shapes it should
/// not.
#[test]
fn a_constructor_split_joins_exactly_where_the_constructors_cover_the_sort() {
    use super::generator::Split;
    super::on_large_stack(|| {
        let joining = Split::ALL
            .into_iter()
            .filter(|split| split.joins())
            .collect::<Vec<_>>();
        assert_eq!(
            joining,
            [Split::Refuted, Split::Covered, Split::CoveredUnary]
        );
        assert_eq!(accepted_splits(Switches::default()), joining);
        for (switches, also) in [
            (
                Switches {
                    close_case_without_refutation: true,
                    ..Switches::default()
                },
                vec![Split::Open],
            ),
            (
                Switches {
                    drop_complement_without_coverage: true,
                    ..Switches::default()
                },
                vec![
                    Split::Uncovered,
                    Split::EmptySubsort,
                    Split::HeadProducer,
                    Split::TotalProducer,
                    Split::Specific,
                    Split::Uninhabited,
                ],
            ),
            (
                Switches {
                    coverage_ignores_empty_subsorts: true,
                    ..Switches::default()
                },
                vec![Split::EmptySubsort],
            ),
        ] {
            let mut expected = joining.clone();
            expected.extend(also);
            let mut accepted = accepted_splits(switches);
            accepted.sort_by_key(|split| Split::ALL.iter().position(|other| other == split));
            expected.sort_by_key(|split| Split::ALL.iter().position(|other| other == split));
            assert_eq!(accepted, expected, "{switches:?}");
        }
    });
}

/// `coverage_ignores_empty_subsorts` counts `Tc` covered by `tc1` and `tc2` although its empty
/// subsort `Ec` gives it an element in every model, and the full check accepts
/// `hTc(X) = c` beside `hTc(X) = pTc(X)`. Without `D+`'s constants nothing sees it, since no
/// value of `Tc` is outside the constructors; with them `hTc(inj(junkEc))` is `c` by one
/// equation and `\bottom` by the other.
#[test]
fn coverage_that_ignores_empty_subsorts_is_caught_by_the_constants() {
    use super::generator::{Split, constructor_split};
    super::on_large_stack(|| {
        let switch = Switches {
            coverage_ignores_empty_subsorts: true,
            ..Switches::default()
        };
        assert!(accepted_splits(switch).contains(&Split::EmptySubsort));
        let definition = constructor_split(Split::EmptySubsort);
        // The pair is over `Tc`, which has normal forms, so it proposes no witness: `D+` is
        // judged without witness equations.
        let run = |constants| {
            switches::with(switch, || {
                super::checks::junk_check(&definition, &[], constants, &mut Rng(DEFAULT_SEED))
                    .failures
            })
        };
        let without = run(false);
        assert!(without.is_empty(), "{}", without.join("\n"));
        let with = run(true);
        assert!(
            with.iter().any(|failure| failure.contains("junkEc")),
            "{with:?}"
        );
    });
}

mutation!(
    coverage_that_ignores_empty_subsorts_is_caught_by_the_scope_run,
    coverage_ignores_empty_subsorts,
    scope_failures
);

/// V9's failures on N1 observed by a function under `switches`: the template where only T-obs
/// makes a pair relevant to the load's scope.
fn scope_failures_on_observation_by_a_function(switches: Switches) -> Vec<String> {
    scope_failures(switches)
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
/// one of the definitions the harness runs, and the harness sees it. That is 25 of the 32 defect
/// switches of `confluence::switches` (`no_condition_memo` configures the load and seeds no
/// defect). The other seven it cannot see:
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
///   predicates as right-hand side, which the harness does not instantiate;
/// - `drop_supersort_inhabitation` since FZ-EMPTYJOIN-CLAIMS: a pair over a sort read as having
///   no normal form withdraws like any other, so the switch no longer keeps a claim; it moves the
///   reason and the witnesses open mode proposes, and a witness at a sort that has a normal form
///   applies where `M_NF` reads the stuck application as `\bottom`, which no generated
///   definition here exercises;
/// - `separate_uninhabited` (not counted above) sets aside overlaps over a sort with no normal
///   form, which the harness, instantiating with the backend's values, has no value of; and
///   `coverage_ignores_empty_subsorts` (not counted above) drops a split's complement whose only
///   instances are at an element of an empty subsort, of which the harness has no value either.
///
/// The oracle sees the overload switches by comparing the pairs with its own (V2 and the
/// completeness run), `claims_during_check` with the claim-dependent probe and both check
/// switches with `withdrawn_claim_failures`, `discharge_before_check` also by the rewrite rule's
/// definedness obligation (`confluence::tests::discharging_before_the_check_is_caught`), and the
/// last by V3c's brute-force self pairs
/// (`the_self_pair_brute_force_sees_a_disjunction_read_as_reading_nothing`);
/// `drop_supersort_inhabitation` by the witness it proposes at a sort with a normal form
/// (`confluence::tests::witness::a_dropped_supersort_closure_proposes_a_witness_at_a_sort_with_a_normal_form`)
/// and the reason it names (`confluence::tests::review_one`);
/// `separate_uninhabited` by the constants of `D+`
/// (`restored_vacuity_goes_unnoticed_without_the_constants_and_is_caught_with_them`), and
/// `coverage_ignores_empty_subsorts` too
/// (`coverage_that_ignores_empty_subsorts_is_caught_by_the_constants`). The four
/// witness switches (`adopt_unvalidated_witnesses`, `witnesses_only_at_their_pair`,
/// `witness_without_empty_variable`, `adopt_with_tainted_witness_head`) are not counted either:
/// the harness's judge, the backend's evaluation, never reads a witness equation, and its values
/// are free of constants. The oracle sees the first three in `D+` with the verdict's witnesses
/// and the last by the closure (`checks::witness_failures`), each on its witness template
/// (`generator::witness_templates`), in the tests after this macro's uses.
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
// `generator::constructor_split`'s `Open` shape: `gTc(tc1, 1)` is `c` and `m(2)`.
axiom_mutation!(
    the_axiom_harness_sees_cases_closed_without_refutation,
    close_case_without_refutation
);
// `generator::constructor_split`'s `Uncovered` shape: `hTc(tc3)` is `c` and `\bottom`.
axiom_mutation!(
    the_axiom_harness_sees_complements_dropped_without_coverage,
    drop_complement_without_coverage
);
// The written-meaning template whose equation disagrees with `KEQUAL.ite` has no model; without
// the hook pairs the full check names no pair for it.
axiom_mutation!(the_axiom_harness_sees_skipped_hook_pairs, skip_hook_pairs);
// A relaxed solution accepted without refuting its conditions drops the list template's suffix
// pair (`hl([X, R..]) = mk(X)` beside `hl([R.., Y]) = mk(Y)`), whose definition has no model.
axiom_mutation!(
    the_axiom_harness_sees_deferral_without_refutation,
    defer_without_refutation
);
axiom_mutation!(
    the_axiom_harness_sees_relevance_that_needs_both_equations,
    relevance_needs_both
);
axiom_mutation!(
    the_axiom_harness_sees_dropped_collection_edges,
    drop_collection_edges
);
// The scan reads an overloaded production written in an equation's argument pattern up to
// equations, since the overload axioms equate `g(inj(x))` with `inj(l(x))`; read by its root
// instead, it mints a token on an instance over values that the overload equation reaches
// (`len(inj(nilN))` under `len(nilE) = mk(0)` in `generator::family`), which the token judge on
// instances over values sees.
axiom_mutation!(
    the_axiom_harness_sees_overloaded_patterns_read_by_their_root,
    root_read_overloaded_patterns
);

// The map rule's decisions (`unify.rs`, `Unifier::maps`), each against the `same_key_maps`
// pair whose real overlap its defect hides (`generator::same_key_maps`): `sk` for keys
// decomposed when only unifiable and for a last resort that clashes, `sa` for a size test that
// ignores rests, `one` for a rest counted as an entry, `sb` for a clash of a side left without
// entries whatever its rest. A rest binding that drops the other side's rest (`sc`) differs
// only at a map of three entries, which the harness's value pool did not reach: it and the
// opaque-rest clash are caught by the unit checks (`confluence::tests`).
axiom_mutation!(
    the_axiom_harness_sees_decomposed_unifiable_keys,
    decompose_unifiable_keys
);
axiom_mutation!(
    the_axiom_harness_sees_a_last_resort_that_clashes,
    last_resort_clashes
);
axiom_mutation!(
    the_axiom_harness_sees_a_size_test_that_ignores_rests,
    size_clash_ignores_rest
);
axiom_mutation!(
    the_axiom_harness_sees_rests_counted_as_entries,
    size_counts_rest
);
axiom_mutation!(
    the_axiom_harness_sees_an_empty_side_clashed_whatever_its_rest,
    empty_clash_ignores_rest
);

/// What the oracle found on one witness template ([`super::generator::witness_templates`]) under
/// some switches: its failures (V9, the memo, `M+` and `W`), the two scopes' verdicts, and
/// whether the constants check judged it with witness equations, and how many of their instances.
struct WitnessRun {
    failures: Vec<String>,
    gate: crate::confluence::ValueClaims,
    full: crate::confluence::ValueClaims,
    witnessed: usize,
    witness_instances: usize,
    /// The full check's witnesses in the oracle's language, as text.
    witnesses: Vec<String>,
}

fn witness_template(name: &str) -> super::language::Definition {
    super::generator::witness_templates()
        .into_iter()
        .find(|(template, _)| template == name)
        .unwrap_or_else(|| panic!("no template {name}"))
        .1
}

fn witness_run(switches: Switches, name: &str) -> WitnessRun {
    let definition = witness_template(name);
    switches::with(switches, || {
        let (tally, _) = check_definition(name, &definition);
        let backend = super::checks::backend(&definition).expect("the template loads");
        let full = backend.value_claims_in_scope(crate::confluence::CheckScope::All);
        let witnesses = super::checks::witness_equations(&definition, &full)
            .expect("the witnesses are equations of the oracle's language")
            .iter()
            .map(|equation| {
                format!(
                    "{} => {}",
                    super::checks::show(&equation.lhs),
                    super::checks::show(&equation.rhs)
                )
            })
            .collect();
        WitnessRun {
            failures: tally.failures,
            gate: backend.value_claims().clone(),
            full,
            witnessed: tally.junk_witnessed,
            witness_instances: tally.junk_witness_instances,
            witnesses,
        }
    })
}

fn template_name(shape: super::generator::WitnessShape) -> String {
    super::generator::witness_template_name(shape)
}

/// The WASM template's witness, in the oracle's language.
const WASM_WITNESS: &str = "ib(VarWitness0, inj{Ew, Bw}(VarWitness1)) => inj{Ew, Bw}(VarWitness1)";

/// The witness templates without a switch: none fails the oracle, and each verdict is the one
/// the design gives. The WASM shape is adopted with its one witness in both scopes and accepted,
/// and the constants check judges `D+` with it, instances of the witness included; with `Ew`
/// inhabited the pair is a clash, which proposes nothing; the `z` variant (`Kept`) and B2 keep
/// pass 1, and on B2 the load's scope never classifies `m`'s pair while both scopes agree (V9,
/// in the failures); B1 (`TaintedHead`) keeps pass 1 because the unrelated pair taints `ib`;
/// `k`'s proposal alone is adopted, and with `g`'s conflicting one neither is.
#[test]
fn the_witness_templates_hold_with_the_verdicts_the_design_gives() {
    use super::generator::WitnessShape;
    use crate::confluence::WitnessPass;
    super::on_large_stack(|| {
        let mut failures = Vec::new();
        for (name, _) in super::generator::witness_templates() {
            failures.extend(witness_run(Switches::default(), &name).failures);
        }
        assert!(failures.is_empty(), "{}", failures.join("\n"));
        let both = |run: &WitnessRun| [run.gate.clone(), run.full.clone()];

        let wasm = witness_run(Switches::default(), &template_name(WitnessShape::Wasm));
        assert_eq!(wasm.witnesses, [WASM_WITNESS]);
        for claims in both(&wasm) {
            assert!(claims.witness_pass_adopted());
            assert!(claims.unjoined().is_empty() && claims.violations().is_empty());
        }
        assert_eq!(wasm.witnessed, 1);
        assert!(wasm.witness_instances > 0);

        let inhabited = witness_run(Switches::default(), &template_name(WitnessShape::Inhabited));
        for claims in both(&inhabited) {
            assert_eq!(claims.counts().witness_pass, WitnessPass::NotProposed);
            assert_eq!(claims.unjoined().len(), 1);
            assert!(!claims.unjoined()[0].over_uninhabited_sort());
        }

        for shape in [WitnessShape::Kept, WitnessShape::B2] {
            let run = witness_run(Switches::default(), &template_name(shape));
            for claims in both(&run) {
                assert_eq!(claims.counts().witness_pass, WitnessPass::Kept, "{shape:?}");
                assert!(claims.witnesses().is_empty(), "{shape:?}");
                assert_eq!(claims.unjoined().len(), 1, "{shape:?}");
                assert!(claims.unjoined()[0].over_uninhabited_sort(), "{shape:?}");
            }
            if shape == WitnessShape::B2 {
                assert!(
                    run.gate.counts().skipped > 0,
                    "the load classifies m's pair"
                );
            }
        }

        let tainted = witness_run(
            Switches::default(),
            &template_name(WitnessShape::TaintedHead),
        );
        assert!(
            tainted
                .full
                .tainted_symbols()
                .iter()
                .any(|symbol| symbol.as_ref() == "ib")
        );
        for claims in both(&tainted) {
            assert_eq!(claims.counts().witness_pass, WitnessPass::Kept);
        }

        let alone = witness_run(
            Switches::default(),
            "template witness conflict (both false)",
        );
        assert_eq!(alone.witnesses, ["f(VarWitness0) => dw(VarWitness0)"]);
        assert_eq!(alone.witnessed, 1);
        let conflict = witness_run(Switches::default(), "template witness conflict (both true)");
        for claims in both(&conflict) {
            assert_eq!(claims.counts().witness_pass, WitnessPass::Kept);
            assert_eq!(claims.unjoined().len(), 2);
        }
    });
}

/// `D+` needs the verdict's witnesses: the full check accepts the WASM template with one
/// witness, and without it `D+` gives `s(C, inj(*_Ew))` two normal forms, `inj(*_Ew)` by `da`'s
/// `owise` and `\bottom` by `ib`'s stuck application, a false alarm on a definition that has
/// the model; with it each instance holds.
#[test]
fn the_wasm_template_has_the_model_d_plus_with_its_witness_only() {
    super::on_large_stack(|| {
        let definition = witness_template(&template_name(super::generator::WitnessShape::Wasm));
        let backend = super::checks::backend(&definition).expect("the template loads");
        let full = backend.value_claims_in_scope(crate::confluence::CheckScope::All);
        let witnesses = super::checks::witness_equations(&definition, &full)
            .expect("the witness is an equation of the oracle's language");
        assert_eq!(witnesses.len(), 1);
        let without = super::checks::junk_check(&definition, &[], true, &mut Rng(DEFAULT_SEED));
        assert!(
            without
                .failures
                .iter()
                .any(|failure| failure.contains("has the normal forms ⊥, inj{Ew, Sw}(junkEw)")),
            "{:?}",
            without.failures
        );
        let with = super::checks::junk_check(&definition, &witnesses, true, &mut Rng(DEFAULT_SEED));
        assert!(with.failures.is_empty(), "{:?}", with.failures);
        assert!(with.witness_instances > 0 && with.with_constants > 0);
    });
}

/// The failures of the witness template `name` under the one switch `switches`, after checking
/// that the template has none without it.
fn witness_switch_failures(switches: Switches, name: &str) -> Vec<String> {
    let off = witness_run(Switches::default(), name);
    assert!(off.failures.is_empty(), "{}", off.failures.join("\n"));
    witness_run(switches, name).failures
}

/// Asserts that some failure of `failures` contains every one of `texts`.
fn assert_failure(name: &str, failures: &[String], texts: &[&str]) {
    assert!(
        failures
            .iter()
            .any(|failure| texts.iter().all(|text| failure.contains(text))),
        "the switch {name} went unnoticed: no failure holds {texts:?} in {failures:#?}"
    );
}

/// `adopt_unvalidated_witnesses` adopts each pair's own proposal, without the conflict drop or
/// pass 2: on the conflicting template both `f(X) => dw(X)` and `f(X) => inj(X)` are adopted
/// and the full check reports nothing, but in `D+` with them `k(*_Ew, Y)` has the two normal
/// forms `dw(*_Ew)` and `inj(*_Ew)`.
#[test]
fn unvalidated_witnesses_are_caught_in_d_plus() {
    super::on_large_stack(|| {
        let switch = Switches {
            adopt_unvalidated_witnesses: true,
            ..Switches::default()
        };
        let failures = witness_switch_failures(switch, "template witness conflict (both true)");
        assert_failure(
            "adopt_unvalidated_witnesses",
            &failures,
            &[
                super::checks::JUNK,
                "has the normal forms dw(junkEw), inj{Ew, Bw}(junkEw)",
            ],
        );
    });
}

/// `witnesses_only_at_their_pair` validates the witness at `s`'s pair alone: on the `z` template
/// and on B2 it is adopted although it splits `m`'s pair, which pass 1 joins, and in `D+`
/// `m(…, *_Ew)` has the normal forms `\bottom` (by `z`) and `inj(*_Ew)` (by `ib`'s witness).
#[test]
fn witnesses_validated_only_at_their_pair_are_caught_in_d_plus() {
    use super::generator::WitnessShape;
    super::on_large_stack(|| {
        let switch = Switches {
            witnesses_only_at_their_pair: true,
            ..Switches::default()
        };
        for shape in [WitnessShape::Kept, WitnessShape::B2] {
            let failures = witness_switch_failures(switch, &template_name(shape));
            assert_failure(
                "witnesses_only_at_their_pair",
                &failures,
                &[
                    super::checks::JUNK,
                    "has the normal forms ⊥, inj{Ew, Bw}(junkEw)",
                ],
            );
        }
    });
}

/// `witness_without_empty_variable` proposes from a clash over an inhabited sort: with `Ew`
/// inhabited by `ew`, `ib(C, inj(X:Ew)) => inj(X)` is adopted, so `ib(c0, inj(ew))`, `\bottom`
/// in the definition, is `inj(ew)` in `D+`: a term free of constants that `D+` evaluates
/// otherwise. The oracle's reading of the witness's well-formedness names it too.
#[test]
fn witnesses_without_an_empty_variable_are_caught() {
    super::on_large_stack(|| {
        let switch = Switches {
            witness_without_empty_variable: true,
            ..Switches::default()
        };
        let name = template_name(super::generator::WitnessShape::Inhabited);
        let failures = witness_switch_failures(switch, &name);
        assert_failure(
            "witness_without_empty_variable",
            &failures,
            &[
                super::checks::JUNK,
                "ib(c0, inj{Ew, Bw}(ew)) evaluates in D+ to [\"inj{Ew, Bw}(ew)\"] and in the definition to [\"⊥\"]",
            ],
        );
        assert_failure(
            "witness_without_empty_variable",
            &failures,
            &[
                super::checks::WITNESS,
                "holds no variable of a sort outside the surely-inhabited ones",
            ],
        );
    });
}

/// `adopt_with_tainted_witness_head` drops adoption condition 4: on B1 (`TaintedHead`) the witness
/// at `ib` is adopted although the unrelated pair `q` taints `ib`. No evaluation shows it: the
/// full check still names `q`'s pair, so `D+` is not judged, and the claims' model `M'`, where
/// the witness fails at a context holding a new element, has elements no evaluation builds. So
/// the closure is checked instead (design 4.3): an adopted witness's head is tainted.
#[test]
fn a_witness_adopted_at_a_tainted_head_is_caught_by_the_closure() {
    super::on_large_stack(|| {
        let switch = Switches {
            adopt_with_tainted_witness_head: true,
            ..Switches::default()
        };
        let name = template_name(super::generator::WitnessShape::TaintedHead);
        let failures = witness_switch_failures(switch, &name);
        assert_failure(
            "adopt_with_tainted_witness_head",
            &failures,
            &[
                super::checks::WITNESS,
                "its head is tainted in the full check's closure",
            ],
        );
        let run = witness_run(switch, &name);
        assert!(run.full.witness_pass_adopted());
        assert_eq!(
            run.witnessed, 0,
            "D+ is judged although the full check names q's pair"
        );
    });
}

/// The axiom-instance harness on the witness templates (also run by `run_axioms` through
/// `generator::templates`): every instance it judges holds in the backend's evaluation, whose
/// values are free of constants, so no witness applies at them.
#[test]
fn the_axiom_harness_holds_on_the_witness_templates() {
    super::on_large_stack(|| {
        let mut failures = Vec::new();
        for (name, definition) in super::generator::witness_templates() {
            let tally =
                super::axioms::check_with_a_model(&name, &definition, &mut Rng(DEFAULT_SEED));
            failures.extend(tally.failures);
        }
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    });
}

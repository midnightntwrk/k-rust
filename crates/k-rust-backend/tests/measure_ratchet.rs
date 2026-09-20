//! Work-counter ratchets for the backend families of `k_rust_kore::measure`.
//!
//! Each family pins a bound on a small KORE-text definition and a growth shape on a
//! parameterised run of the same definition. Bounds are measured values with headroom, recorded
//! next to the assertion; a bound that trips after a deliberate algorithm change is re-pinned
//! with the new value and the reason. Every test measures a `Snapshot::delta` around the call
//! under test, so tests never depend on the counters being zero when they start.

// The counters only count in `measure` builds; the crate's dev-dependencies enable the feature.
const _: () = assert!(cfg!(feature = "measure"));

use k_rust_backend::{
    definition::BackendDefinition,
    proof::{ProofOptions, ProofStatus, prove_claim},
    rewrite::{
        ExecutionBranchMode, ExecutionMode, ExecutionOptions, HaltReason, Pattern, execute,
        execute_with_solver,
    },
    search::{SearchOptions, SearchType, search_graph},
    smt::NoSolver,
    substitution::Substitution,
    unification::{UnificationResult, unify_term_pairs},
};
use k_rust_kore::{
    kore::parser::{parse_definition, parse_pattern},
    measure::{Counter, Snapshot, snapshot},
};

/// `inc(N) => inc(f(N))` with `f(N) = N + 1` as a function equation.
const COUNTING: &str = r#"[]
module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    sort SortS{} []
    hooked-symbol plusInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    symbol inc{}(SortInt{}) : SortS{} [constructor{}()]
    symbol f{}(SortInt{}) : SortInt{} [function{}(), total{}()]
    alias weakAlwaysFinally{S}(S) : S where weakAlwaysFinally{S}(@X:S) := @X:S []
    axiom{R} \implies{R}(
        \top{R}(),
        \equals{SortInt{}, R}(
            f{}(N:SortInt{}),
            \and{SortInt{}}(plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")), \top{SortInt{}}())
        )
    ) [label{}("f"), simplification{}()]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(inc{}(N:SortInt{}), \top{SortS{}}()),
        inc{}(f{}(N:SortInt{}))
    ) [label{}("step")]
    claim{} \implies{SortS{}}(
        \and{SortS{}}(inc{}(\dv{SortInt{}}("0")), \top{SortS{}}()),
        weakAlwaysFinally{SortS{}}(inc{}(\dv{SortInt{}}("10")))
    ) [label{}("ten")]
    claim{} \implies{SortS{}}(
        \and{SortS{}}(inc{}(\dv{SortInt{}}("0")), \top{SortS{}}()),
        weakAlwaysFinally{SortS{}}(inc{}(\dv{SortInt{}}("20")))
    ) [label{}("twenty")]
endmodule []"#;

/// Two rules that both step `inc(N)` to `inc(N + 1)`, so every depth reaches one state twice.
const BRANCHING: &str = r#"[]
module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    sort SortS{} []
    hooked-symbol plusInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    symbol inc{}(SortInt{}) : SortS{} [constructor{}()]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(inc{}(N:SortInt{}), \top{SortS{}}()),
        inc{}(plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")))
    ) [label{}("left")]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(inc{}(N:SortInt{}), \top{SortS{}}()),
        inc{}(plusInt{}(\dv{SortInt{}}("1"), N:SortInt{}))
    ) [label{}("right")]
endmodule []"#;

/// A SIMPLE-shaped heating rule whose normalized anywhere head cannot match the rigid program
/// head.  The lower-priority program rule must run without symbolic recovery or SMT work.
const GROUND_ANYWHERE_HEATING: &str = r#"[]
module MAIN
    sort SortS{} []
    symbol state{}(SortS{}) : SortS{} [constructor{}(), total{}()]
    symbol anywhereHead{}(SortS{}, SortS{}) : SortS{} [anywhere{}(), total{}()]
    symbol programHead{}(SortS{}) : SortS{} [constructor{}(), total{}()]
    symbol value{}() : SortS{} [constructor{}(), total{}()]
    symbol done{}() : SortS{} [constructor{}(), total{}()]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(
            state{}(anywhereHead{}(HOLE:SortS{}, REST:SortS{})),
            \top{SortS{}}()
        ),
        state{}(HOLE:SortS{})
    ) [label{}("heat"), priority{}("40")]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(state{}(programHead{}(X:SortS{})), \top{SortS{}}()),
        done{}()
    ) [label{}("program"), priority{}("50")]
endmodule []"#;

const CELL_MAP_COVERAGE: &str = include_str!("fixtures/cell-map-coverage.kore");
const CELL_SET_COVERAGE: &str = include_str!("fixtures/cell-set-coverage.kore");

const GROUND_OVERLOAD: &str = include_str!("fixtures/ground-overload.kore");
const SIMPLIFIER_GROWTH: &str = include_str!("fixtures/simplifier-growth.kore");

fn definition(source: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn definition_in(source: &str, module: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, module).expect("definition should internalize")
}

fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
    definition
        .internalize_pattern(&parse_pattern(source).expect("pattern should parse"), &[])
        .expect("pattern should internalize")
}

/// The counters a run touched, for the measurement line a ratchet prints.
fn nonzero(snapshot: &Snapshot) -> Vec<(&'static str, u64)> {
    snapshot.iter().filter(|(_, value)| *value > 0).collect()
}

fn measured<T>(work: impl FnOnce() -> T) -> (T, Snapshot) {
    let before = snapshot();
    let result = work();
    (result, snapshot().delta(&before))
}

#[cfg(feature = "z3")]
fn be08_measure_definition(rules: &str) -> BackendDefinition {
    definition(
        &r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            symbol wrap{}(SortInt{}) : SortInt{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), smt-hook{}("<")]
            $RULES
        endmodule []"#
            .replace("$RULES", rules),
    )
}

#[cfg(feature = "z3")]
fn be08_measure_s0() -> BackendDefinition {
    be08_measure_definition(
        r#"
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(
                wrap{}(X:SortInt{}),
                \equals{SortBool{}, SortInt{}}(
                    lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                    \dv{SortBool{}}("true")
                )
            ),
            \dv{SortInt{}}("-1")
        ) [label{}("negative"), priority{}("10")]
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(
                wrap{}(X:SortInt{}),
                \equals{SortBool{}, SortInt{}}(
                    lt{}(\dv{SortInt{}}("0"), X:SortInt{}),
                    \dv{SortBool{}}("true")
                )
            ),
            \dv{SortInt{}}("1")
        ) [label{}("positive"), priority{}("10")]
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
            \dv{SortInt{}}("2")
        ) [label{}("zero-a"), priority{}("50")]
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
            \dv{SortInt{}}("3")
        ) [label{}("zero-b"), priority{}("50")]
        "#,
    )
}

#[cfg(feature = "z3")]
fn be08_measure_s1() -> BackendDefinition {
    let mut rules = String::new();
    for index in 0..8 {
        rules.push_str(&format!(
            r#"
            axiom{{}} \rewrites{{SortInt{{}}}}(
                \and{{SortInt{{}}}}(
                    wrap{{}}(X:SortInt{{}}),
                    \equals{{SortBool{{}}, SortInt{{}}}}(
                        lt{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("{index}")),
                        \dv{{SortBool{{}}}}("true")
                    )
                ),
                \dv{{SortInt{{}}}}("{}")
            ) [label{{}}("be08-symbolic-{index}"), priority{{}}("{}")]
            "#,
            100 + index,
            10 + index * 10,
        ));
    }
    rules.push_str(
        r#"
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
            \dv{SortInt{}}("200")
        ) [label{}("be08-fallback-a"), priority{}("90")]
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
            \dv{SortInt{}}("201")
        ) [label{}("be08-fallback-b"), priority{}("90")]
        "#,
    );
    be08_measure_definition(&rules)
}

#[cfg(feature = "z3")]
fn be08_measure_any_replay() -> BackendDefinition {
    be08_measure_definition(
        r#"
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(
                wrap{}(X:SortInt{}),
                \equals{SortBool{}, SortInt{}}(
                    lt{}(X:SortInt{}, \dv{SortInt{}}("10")),
                    \dv{SortBool{}}("true")
                )
            ),
            \dv{SortInt{}}("100")
        ) [label{}("conditional"), priority{}("10")]
        "#,
    )
}

#[cfg(feature = "z3")]
fn be08_measure_stopped(definition: &BackendDefinition, mode: ExecutionMode) -> Snapshot {
    let initial = pattern(definition, "wrap{}(X:SortInt{})");
    let solver = k_rust_backend::smt::Z3Solver::new(definition).unwrap();
    let (result, delta) = measured(|| {
        execute_with_solver(
            definition,
            initial,
            ExecutionOptions {
                mode,
                branch_mode: ExecutionBranchMode::StopAtBranch,
                ..ExecutionOptions::default()
            },
            &solver,
        )
    });
    assert!(matches!(
        result.leaves.as_slice(),
        [k_rust_backend::rewrite::ExecutionLeaf {
            halt_reason: HaltReason::Branch { .. },
            ..
        }]
    ));
    delta
}

#[cfg(feature = "z3")]
fn assert_be08_snapshot(name: &str, actual: Snapshot, expected: [u64; Counter::COUNT]) {
    if std::env::var_os("KRUST_BE08_CAPTURE").is_some() {
        eprintln!("BE08 capture {name}: {:?}", actual.0);
    } else {
        assert_eq!(actual, Snapshot(expected), "BE08 counter capture {name}");
    }
}

/// T3 / I9 and T15 / D4. Replay baseline captured at 40b5d6d214cdd833e027a814744d9f98c5e7542d;
/// S2-P2 S0/S1 cascade counters captured at 538f2a79bd1e81f45fad1dbc72d386052021e493.
/// T15's Any replay snapshot remains the baseline capture.
#[cfg(feature = "z3")]
#[test]
fn stopped_branch_cascade_attempts_each_candidate_rule_once() {
    let s0 = be08_measure_stopped(&be08_measure_s0(), ExecutionMode::All);
    let s1 = be08_measure_stopped(&be08_measure_s1(), ExecutionMode::All);
    let any_replay = be08_measure_stopped(&be08_measure_any_replay(), ExecutionMode::Any);

    assert_eq!(s0.get(Counter::RewriteRuleAttempts), 4);
    assert_eq!(s0.get(Counter::RewriteRulesApplied), 4);
    assert_eq!(s0.get(Counter::RewriteMatchFailures), 0);
    assert_eq!(s0.get(Counter::RewriteSteps), 1);
    assert_eq!(s1.get(Counter::RewriteRuleAttempts), 10);
    assert_eq!(s1.get(Counter::RewriteRulesApplied), 10);
    assert_eq!(s1.get(Counter::RewriteMatchFailures), 0);
    assert_eq!(s1.get(Counter::RewriteSteps), 1);
    assert_eq!(any_replay.get(Counter::RewriteRuleAttempts), 2);
    assert_eq!(any_replay.get(Counter::RewriteRulesApplied), 1);
    assert_eq!(any_replay.get(Counter::RewriteMatchFailures), 0);
    assert_eq!(any_replay.get(Counter::RewriteSteps), 1);
    assert_be08_snapshot(
        "T3 S0 All",
        s0,
        [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 4, 0, 4, 8,
            0, 0, 20, 30, 32, 0, 0, 17, 9, 0, 0, 0, 28,
        ],
    );
    assert_be08_snapshot(
        "T3 S1 All",
        s1,
        [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10, 0, 10, 0, 10,
            20, 0, 0, 96, 73, 172, 0, 0, 128, 108, 0, 0, 0, 162,
        ],
    );
    assert_be08_snapshot(
        "T15 Any replay",
        any_replay,
        [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 2, 4,
            0, 0, 12, 16, 18, 0, 0, 7, 5, 0, 0, 0, 17,
        ],
    );
}

fn execute_counting(definition: &BackendDefinition, depth: u64) -> Snapshot {
    let initial = pattern(definition, r#"inc{}(\dv{SortInt{}}("0"))"#);
    let (result, delta) = measured(|| {
        execute(
            definition,
            initial,
            ExecutionOptions {
                max_depth: depth,
                ..ExecutionOptions::default()
            },
        )
    });
    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    assert_eq!(result.leaves[0].depth, depth);
    assert_eq!(
        result.leaves[0].pattern.term,
        pattern(
            definition,
            &format!(r#"inc{{}}(\dv{{SortInt{{}}}}("{depth}"))"#)
        )
        .term
    );
    delta
}

// ---------- rewrite, simplify, term ----------

#[test]
fn counting_execution_to_depth_100_stays_within_the_pinned_rewrite_work() {
    let definition = definition(COUNTING);
    let delta = execute_counting(&definition, 100);
    eprintln!("rewrite/simplify/term at depth 100: {:?}", nonzero(&delta));
    // The initial state plus one pop per step.
    assert_eq!(delta.get(Counter::RewriteSteps), STEPS_100);
    assert_eq!(delta.get(Counter::RewriteRulesApplied), 100);
    assert!(delta.get(Counter::RewriteRuleAttempts) <= RULE_ATTEMPTS_100);
    assert!(delta.get(Counter::RewriteMatchFailures) <= delta.get(Counter::RewriteRuleAttempts));
    assert_eq!(delta.get(Counter::RewriteIndeterminateRecoveries), 0);
    assert_eq!(delta.get(Counter::MatchingCollectionProblems), 0);
    assert!(delta.get(Counter::MatchingPairs) >= delta.get(Counter::MatchingProblems));
    assert!(delta.get(Counter::MatchingProblems) >= 100);
    assert!(
        delta.get(Counter::SimplifyRounds)
            <= STEPS_100 * k_rust_backend::simplify::DEFAULT_MAX_SIMPLIFICATION_ITERATIONS as u64
    );
    assert!(delta.get(Counter::SimplifyEquationAttempts) >= 100);
    assert!(delta.get(Counter::SimplifyBuiltinEvaluations) >= 100);
    assert_eq!(delta.get(Counter::SmtQueries), 0);
}

#[test]
fn counting_execution_work_grows_linearly_with_depth() {
    let definition = definition(COUNTING);
    let at_100 = execute_counting(&definition, 100);
    let at_200 = execute_counting(&definition, 200);
    eprintln!("rewrite/simplify/term at depth 200: {:?}", nonzero(&at_200));
    for counter in [
        Counter::RewriteSteps,
        Counter::RewriteRuleAttempts,
        Counter::MatchingProblems,
        Counter::MatchingPairs,
        Counter::SimplifyRounds,
        Counter::SimplifyEquationAttempts,
        Counter::SimplifyBuiltinEvaluations,
        Counter::TermConstructed,
    ] {
        assert!(
            at_200.get(counter) <= 2 * at_100.get(counter) + LINEAR_SLACK,
            "{}: {} at depth 200 versus {} at depth 100",
            counter.name(),
            at_200.get(counter),
            at_100.get(counter)
        );
    }
}

#[test]
fn ground_anywhere_heating_does_not_enter_symbolic_recovery() {
    let definition = definition(GROUND_ANYWHERE_HEATING);
    let initial = pattern(&definition, "state{}(programHead{}(value{}()))");
    let (result, delta) = measured(|| {
        execute(
            &definition,
            initial,
            ExecutionOptions {
                max_depth: 1,
                ..ExecutionOptions::default()
            },
        )
    });
    eprintln!("ground anywhere heating: {:?}", nonzero(&delta));
    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    assert_eq!(
        result.leaves[0].pattern.term,
        pattern(&definition, "done{}()").term
    );
    assert_eq!(delta.get(Counter::RewriteRulesApplied), 1);
    assert_eq!(delta.get(Counter::RewriteIndeterminateRecoveries), 0);
    assert_eq!(delta.get(Counter::SmtQueries), 0);
}

#[test]
fn ground_cell_map_heating_does_not_enter_symbolic_unification() {
    let definition = definition_in(CELL_MAP_COVERAGE, "CELL-MAP-COVERAGE");
    let initial = pattern(
        &definition,
        r#"cellState{}(mapConcat{}(
            mapItem{}(
                \dv{SortKey{}}("first"),
                thread{}(
                    \dv{SortKey{}}("first"),
                    kseq{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("0")), dotk{}())
                )
            ),
            mapItem{}(
                \dv{SortKey{}}("second"),
                thread{}(
                    \dv{SortKey{}}("second"),
                    kseq{}(inj{SortStmt{}, SortKItem{}}(stmt{}()), dotk{}())
                )
            )
        ))"#,
    );
    let (result, delta) = measured(|| {
        execute(
            &definition,
            initial,
            ExecutionOptions {
                max_depth: 1,
                ..ExecutionOptions::default()
            },
        )
    });
    eprintln!("ground cell-map heating: {:?}", nonzero(&delta));
    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    assert_eq!(
        result.leaves[0].pattern.term,
        pattern(&definition, "fallback{}()").term
    );
    assert_eq!(delta.get(Counter::RewriteRulesApplied), 1);
    assert!(delta.get(Counter::MatchingCollectionProblems) >= 1);
    assert_eq!(delta.get(Counter::UnificationProblems), 0);
    assert_eq!(delta.get(Counter::SmtQueries), 0);
}

#[test]
fn ground_cell_set_heating_does_not_enter_symbolic_unification() {
    let definition = definition_in(CELL_SET_COVERAGE, "CELL-SET-COVERAGE");
    let initial = pattern(
        &definition,
        r#"cellState{}(setConcat{}(
            setItem{}(task{}(kseq{}(
                inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("0")),
                dotk{}()
            ))),
            setItem{}(task{}(kseq{}(
                inj{SortStmt{}, SortKItem{}}(stmt{}()),
                dotk{}()
            )))
        ))"#,
    );
    let (result, delta) = measured(|| {
        execute(
            &definition,
            initial,
            ExecutionOptions {
                max_depth: 1,
                ..ExecutionOptions::default()
            },
        )
    });
    eprintln!("ground cell-set heating: {:?}", nonzero(&delta));
    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    assert_eq!(
        result.leaves[0].pattern.term,
        pattern(&definition, "fallback{}()").term
    );
    assert_eq!(delta.get(Counter::RewriteRulesApplied), 1);
    assert!(delta.get(Counter::MatchingCollectionProblems) >= 1);
    assert_eq!(delta.get(Counter::UnificationProblems), 0);
    assert_eq!(delta.get(Counter::SmtQueries), 0);
}

#[test]
fn ground_overload_heating_does_not_branch_or_query_smt() {
    let definition = definition_in(GROUND_OVERLOAD, "GROUND-OVERLOAD");
    let initial = pattern(
        &definition,
        "state{}(exps{}(fun{}(), inj{SortVals{}, SortExps{}}(dotVals{}())))",
    );
    let (result, delta) = measured(|| {
        execute(
            &definition,
            initial,
            ExecutionOptions {
                max_depth: 1,
                ..ExecutionOptions::default()
            },
        )
    });
    eprintln!("ground overload heating: {:?}", nonzero(&delta));
    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    assert_eq!(
        result.leaves[0].pattern.term,
        pattern(&definition, "heated{}()").term
    );
    assert_eq!(delta.get(Counter::RewriteRulesApplied), 1);
    assert_eq!(delta.get(Counter::RewriteIndeterminateRecoveries), 0);
    assert_eq!(delta.get(Counter::SmtQueries), 0);
}

fn execute_simplifier_growth(definition: &BackendDefinition, depth: u64) -> Snapshot {
    let initial = pattern(
        definition,
        r#"state{}(\dv{SortInt{}}("0"), listUnit{}(), mapUnit{}())"#,
    );
    let (result, delta) = measured(|| {
        execute(
            definition,
            initial,
            ExecutionOptions {
                max_depth: depth,
                ..ExecutionOptions::default()
            },
        )
    });
    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    assert_eq!(result.leaves[0].depth, depth);
    delta
}

fn one_simplifier_growth_step(definition: &BackendDefinition, depth: u64) -> Snapshot {
    execute_simplifier_growth(definition, depth + 1)
        .delta(&execute_simplifier_growth(definition, depth))
}

#[test]
fn simplifier_work_per_step_stays_flat_with_cached_closed_collections() {
    let definition = definition(SIMPLIFIER_GROWTH);
    let early = one_simplifier_growth_step(&definition, 8);
    let late = one_simplifier_growth_step(&definition, 64);
    eprintln!("simplifier growth at step 8: {:?}", nonzero(&early));
    eprintln!("simplifier growth at step 64: {:?}", nonzero(&late));
    assert_eq!(early.get(Counter::RewriteSteps), 1);
    assert_eq!(late.get(Counter::RewriteSteps), 1);
    // CB-12-4 caches each closed anywhere head after its inapplicable equation scan. Measured on
    // this change: 7/7 rounds, 9/9 public entries, and 15/15 constructed terms at steps 8/64.
    assert!(early.get(Counter::SimplifyRounds) <= 10);
    assert!(late.get(Counter::SimplifyRounds) <= 10);
    assert_eq!(early.get(Counter::SimplifyInvocations), 9);
    assert_eq!(late.get(Counter::SimplifyInvocations), 9);
    assert!(early.get(Counter::SimplifyNodesSkippedEvaluated) > 0);
    assert!(late.get(Counter::SimplifyRounds) <= early.get(Counter::SimplifyRounds) + 2);
    assert!(early.get(Counter::TermConstructed) <= 20);
    assert!(late.get(Counter::TermConstructed) <= 20);
    for counter in [Counter::SimplifyInvocations, Counter::TermConstructed] {
        assert!(
            late.get(counter) <= early.get(counter) + LINEAR_SLACK,
            "{}: {} at step 64 versus {} at step 8",
            counter.name(),
            late.get(counter),
            early.get(counter)
        );
    }
}

// ---------- search ----------

fn search_branching(definition: &BackendDefinition, depth: u64) -> Snapshot {
    let initial = pattern(definition, r#"inc{}(\dv{SortInt{}}("0"))"#);
    let (result, delta) = measured(|| {
        search_graph(
            definition,
            initial,
            SearchOptions {
                search_type: SearchType::Final,
                max_depth: depth,
                ..SearchOptions::default()
            },
        )
    });
    assert_eq!(result.states.len(), 1, "{result:#?}");
    delta
}

#[test]
fn branching_search_deduplicates_the_state_both_rules_reach() {
    let definition = definition(BRANCHING);
    let delta = search_branching(&definition, 4);
    eprintln!("search at depth 4: {:?}", nonzero(&delta));
    // Both rules take inc(N) to inc(N + 1); the second arrival at every depth is dropped.
    assert!(delta.get(Counter::SearchStatesDeduplicated) >= 1);
    assert!(delta.get(Counter::SearchStatesDeduplicated) <= DEDUPLICATED_4);
}

#[test]
fn branching_search_deduplication_grows_linearly_with_depth() {
    let definition = definition(BRANCHING);
    let at_4 = search_branching(&definition, 4);
    let at_8 = search_branching(&definition, 8);
    assert!(
        at_8.get(Counter::SearchStatesDeduplicated)
            <= 2 * at_4.get(Counter::SearchStatesDeduplicated) + LINEAR_SLACK,
        "{} deduplicated at depth 8 versus {} at depth 4",
        at_8.get(Counter::SearchStatesDeduplicated),
        at_4.get(Counter::SearchStatesDeduplicated)
    );
    assert!(at_8.get(Counter::RewriteSteps) <= 2 * at_4.get(Counter::RewriteSteps) + LINEAR_SLACK);
}

// ---------- proof, unification ----------

fn prove_counting(definition: &BackendDefinition, label: &str) -> Snapshot {
    let claim = definition
        .reachability_claims
        .iter()
        .find(|claim| claim.attributes.label.as_deref() == Some(label))
        .expect("claim should exist");
    let circularities = definition.reachability_claims.iter().collect::<Vec<_>>();
    let (result, delta) = measured(|| {
        prove_claim(
            definition,
            claim,
            &circularities,
            ProofOptions::default(),
            &NoSolver,
        )
    });
    let result = result.expect("claim should execute");
    assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
    delta
}

#[test]
fn counting_proof_checks_the_implication_once_per_explored_state() {
    let definition = definition(COUNTING);
    let delta = prove_counting(&definition, "ten");
    eprintln!("proof to 10: {:?}", nonzero(&delta));
    assert_eq!(delta.get(Counter::ProofStatesExplored), EXPLORED_10);
    assert_eq!(
        delta.get(Counter::ProofImplicationChecks),
        delta.get(Counter::ProofStatesExplored)
    );
}

#[test]
fn counting_proof_work_grows_linearly_with_claim_depth() {
    let definition = definition(COUNTING);
    let to_10 = prove_counting(&definition, "ten");
    let to_20 = prove_counting(&definition, "twenty");
    for counter in [
        Counter::ProofStatesExplored,
        Counter::ProofImplicationChecks,
        Counter::UnificationProblems,
    ] {
        assert!(
            to_20.get(counter) <= 2 * to_10.get(counter) + 1,
            "{}: {} to 20 versus {} to 10",
            counter.name(),
            to_20.get(counter),
            to_10.get(counter)
        );
    }
}

// ---------- unification ----------

#[test]
fn unification_counts_one_problem_per_unify_call() {
    let definition = definition(COUNTING);
    let pattern_term = |source: &str| pattern(&definition, source).term;
    for calls in [1_u64, 4] {
        let (_, delta) = measured(|| {
            for _ in 0..calls {
                let result = unify_term_pairs(
                    &definition,
                    Substitution::new(),
                    [(
                        pattern_term("inc{}(N:SortInt{})"),
                        pattern_term(r#"inc{}(\dv{SortInt{}}("7"))"#),
                    )],
                );
                assert!(
                    matches!(result, UnificationResult::Unified(_)),
                    "{result:?}"
                );
            }
        });
        assert_eq!(delta.get(Counter::UnificationProblems), calls);
    }
}

// ---------- matching over collections ----------

/// A map store with `entries` keys; the one rule removes an entry whose key is a free variable,
/// so matching must choose among the entries (an AC collection problem) and branches per key.
fn map_definition(entries: usize) -> String {
    let mut keys = String::new();
    for index in 0..entries {
        keys.push_str(&format!(
            "    symbol key{index}{{}}() : SortKey{{}} [constructor{{}}()]\n"
        ));
    }
    format!(
        r#"[]
module MAIN
    sort SortKey{{}} []
    sort SortS{{}} []
    hooked-sort SortMap{{}}
        [hook{{}}("MAP.Map"), unit{{}}(dot{{}}()), element{{}}(item{{}}()), concat{{}}(concat{{}}())]
    hooked-symbol dot{{}}() : SortMap{{}} [function{{}}(), functional{{}}(), hook{{}}("MAP.unit")]
    hooked-symbol item{{}}(SortKey{{}}, SortKey{{}}) : SortMap{{}}
        [function{{}}(), functional{{}}(), hook{{}}("MAP.element")]
    hooked-symbol concat{{}}(SortMap{{}}, SortMap{{}}) : SortMap{{}}
        [function{{}}(), assoc{{}}(), hook{{}}("MAP.concat")]
    symbol cfg{{}}(SortMap{{}}) : SortS{{}} [constructor{{}}()]
{keys}    axiom{{}} \rewrites{{SortS{{}}}}(
        \and{{SortS{{}}}}(
            cfg{{}}(concat{{}}(item{{}}(K:SortKey{{}}, V:SortKey{{}}), Rest:SortMap{{}})),
            \top{{SortS{{}}}}()
        ),
        cfg{{}}(Rest:SortMap{{}})
    ) [label{{}}("drop")]
endmodule []"#
    )
}

fn map_initial(entries: usize) -> String {
    let mut store = "dot{}()".to_owned();
    for index in (0..entries).rev() {
        store = format!("concat{{}}(item{{}}(key{index}{{}}(), key{index}{{}}()), {store})");
    }
    format!("cfg{{}}({store})")
}

/// One step over a store of `entries` keys: one rule attempt, `entries` successors.
fn execute_map(entries: usize) -> Snapshot {
    let definition = definition(&map_definition(entries));
    let initial = pattern(&definition, &map_initial(entries));
    let (result, delta) = measured(|| {
        execute(
            &definition,
            initial,
            ExecutionOptions {
                max_depth: 1,
                ..ExecutionOptions::default()
            },
        )
    });
    assert_eq!(result.leaves.len(), entries, "{result:#?}");
    delta
}

#[test]
fn map_matching_with_a_free_key_stays_within_the_pinned_collection_work() {
    let delta = execute_map(4);
    eprintln!("map step with 4 entries: {:?}", nonzero(&delta));
    assert!(delta.get(Counter::MatchingCollectionProblems) >= 1);
    assert!(delta.get(Counter::MatchingCollectionProblems) <= COLLECTION_PROBLEMS_4);
    assert!(delta.get(Counter::MatchingCollectionProblems) <= delta.get(Counter::MatchingProblems));
    assert_eq!(delta.get(Counter::RewriteRulesApplied), 1);
}

#[test]
fn map_matching_collection_problems_grow_at_most_linearly_with_the_store() {
    let at_4 = execute_map(4);
    let at_8 = execute_map(8);
    assert!(
        at_8.get(Counter::MatchingCollectionProblems)
            <= 2 * at_4.get(Counter::MatchingCollectionProblems) + LINEAR_SLACK,
        "{} collection problems with 8 entries versus {} with 4",
        at_8.get(Counter::MatchingCollectionProblems),
        at_4.get(Counter::MatchingCollectionProblems)
    );
}

// ---------- smt ----------

#[cfg(feature = "z3")]
mod smt {
    use k_rust_backend::{
        rule::Predicate,
        smt::{Satisfiability, SmtSolver, Z3Solver},
        substitution::Substitution,
        term::{Sort, Term, Variable},
    };
    use k_rust_kore::measure::{Counter, snapshot};

    use super::{COUNTING, definition, measured};

    fn positive(name: &str) -> Predicate {
        let int = Sort::simple("SortInt");
        Predicate::Equals(
            Term::variable(Variable::new(name, int.clone())),
            Term::domain_value(int, "1"),
        )
    }

    #[test]
    fn identical_queries_run_the_solver_once_after_the_prelude_check() {
        let definition = definition(COUNTING);
        let (solver, construction) = measured(|| Z3Solver::new(&definition).unwrap());
        assert_eq!(construction.get(Counter::SmtSolverRuns), 1);
        assert_eq!(construction.get(Counter::SmtQueries), 0);

        let (_, delta) = measured(|| {
            for _ in 0..2 {
                assert_eq!(
                    solver.is_sat(&[positive("X")], &Substitution::new()),
                    Ok(Satisfiability::Sat)
                );
            }
        });
        assert_eq!(delta.get(Counter::SmtQueries), 2);
        assert_eq!(delta.get(Counter::SmtSolverRuns), 1);
    }

    #[test]
    fn repeated_queries_never_run_the_solver_again() {
        let definition = definition(COUNTING);
        let solver = Z3Solver::new(&definition).unwrap();
        let before = snapshot();
        for _ in 0..16 {
            assert_eq!(
                solver.is_sat(&[positive("Y")], &Substitution::new()),
                Ok(Satisfiability::Sat)
            );
        }
        let delta = snapshot().delta(&before);
        assert_eq!(delta.get(Counter::SmtQueries), 16);
        assert_eq!(delta.get(Counter::SmtSolverRuns), 1);
    }
}

// ---------- pinned values ----------
// Measured at the commit that added this file, then rounded up by about 10 %. The measured
// values are in that commit's message; re-pin in a commit that says why the value moved.

/// Counting execution to depth 100: the initial state plus one pop per step.
const STEPS_100: u64 = 101;
/// Counting execution to depth 100: 100 rule attempts, one per step.
const RULE_ATTEMPTS_100: u64 = 110;
/// Branching search to depth 4: 4 states dropped, one per depth.
const DEDUPLICATED_4: u64 = 5;
/// Counting proof to 10: 11 states, inc(0) through inc(10).
const EXPLORED_10: u64 = 11;
/// One map step with a free key over 4 entries: 1 collection problem.
const COLLECTION_PROBLEMS_4: u64 = 2;
/// Additive slack of the `f(2n) <= 2 f(n) + c` growth assertions.
const LINEAR_SLACK: u64 = 16;

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
    rewrite::{ExecutionOptions, Pattern, execute},
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

fn definition(source: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
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

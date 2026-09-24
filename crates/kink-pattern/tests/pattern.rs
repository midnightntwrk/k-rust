//! Execution-pattern denotation, trace honesty and plan well-formedness over KORE payloads.
//! The rows were ported from the former `execution-pattern-vectors.json`; their IDs are kept.

mod support;

use kink_pattern::{
    CollectionEvidence, CollectionStop, EmptySearchDecision, EvaluationOptions, EventVocabulary,
    ExecutionStop, ExecutionTerminal, ExecutionTerminalKind, PathInput, PathStop,
    PatternFailureKind, PatternOutcome, PatternPlan, Relation, SearchPolicy, SideCondition,
    TermRelation, aggregate_existential, evaluate,
};
use support::{
    PathSpec, app, bind, collection, context, done, exhaustive_options, make_match_stop, path,
    paths, plan, plan_parts, predicate, side_table, sort, stopped, term, terminal_state, use_, var,
};

use PathStop::{DepthLimit, SolverUnknown};
use PatternOutcome::{Error, Match, NoMatch, Unknown};

/// A path without a stable key.
const fn unkeyed(events: &'static [&'static str]) -> PathSpec {
    PathSpec {
        key: None,
        ..done("", events)
    }
}

/// The expected primary witness: its path key, event indices, bindings in plan declaration
/// order, arm, and path predicate.
struct Witnessed {
    key: &'static str,
    indices: &'static [usize],
    bindings: &'static [(&'static str, &'static str)],
    arm: usize,
    predicate: &'static str,
}

const A_AT_0_1: Witnessed = Witnessed {
    key: "p0",
    indices: &[0, 1],
    bindings: &[("A", "a")],
    arm: 0,
    predicate: "true",
};

struct Case {
    id: &'static str,
    plan: &'static str,
    stable: bool,
    search: SearchPolicy,
    input_failure: bool,
    paths: &'static [PathSpec],
    outcome: PatternOutcome,
    complete_coverage: bool,
    failure: Option<PathStop>,
    search_stopped: bool,
    witness: Option<Witnessed>,
    all_indices: Option<&'static [&'static [usize]]>,
    all_paths: Option<&'static [&'static str]>,
    /// The result is invariant under path reversal and has this many witnesses.
    permutation_witnesses: Option<usize>,
}

const CASE: Case = Case {
    id: "",
    plan: "write-eventually-load",
    stable: true,
    search: SearchPolicy::Exhaustive,
    input_failure: false,
    paths: &[],
    outcome: Match,
    complete_coverage: true,
    failure: None,
    search_stopped: false,
    witness: None,
    all_indices: None,
    all_paths: None,
    permutation_witnesses: None,
};

const CASES: [Case; 32] = [
    Case {
        id: "single-event",
        plan: "single-write",
        paths: &[done("p0", &["wa"])],
        witness: Some(Witnessed {
            indices: &[0],
            ..A_AT_0_1
        }),
        ..CASE
    },
    Case {
        id: "occurrence-with-prefix-and-suffix",
        plan: "write-next-load",
        paths: &[done("p0", &["x", "wa", "la", "x"])],
        witness: Some(Witnessed {
            indices: &[1, 2],
            ..A_AT_0_1
        }),
        ..CASE
    },
    Case {
        id: "gap-is-not-next-event",
        plan: "write-next-load",
        paths: &[done("p0", &["wa", "x", "la"])],
        outcome: NoMatch,
        ..CASE
    },
    Case {
        id: "gap-is-eventually-after",
        paths: &[done("p0", &["wa", "x", "la"])],
        witness: Some(Witnessed {
            indices: &[0, 2],
            ..A_AT_0_1
        }),
        ..CASE
    },
    Case {
        id: "reversed-order",
        paths: &[done("p0", &["la", "wa"])],
        outcome: NoMatch,
        ..CASE
    },
    Case {
        id: "shared-binding-mismatch",
        paths: &[done("p0", &["wa", "lb"])],
        outcome: NoMatch,
        ..CASE
    },
    Case {
        id: "canonical-typed-term-alias-equality",
        paths: &[done("p0", &["wa", "lAlias"])],
        witness: Some(A_AT_0_1),
        ..CASE
    },
    Case {
        id: "canonical-earliest-witness",
        paths: &[done("p0", &["wa", "wb", "lb"])],
        witness: Some(Witnessed {
            indices: &[1, 2],
            bindings: &[("A", "b")],
            ..A_AT_0_1
        }),
        ..CASE
    },
    Case {
        id: "overlapping-occurrences-primary-earliest",
        paths: &[done("p0", &["wa", "la", "la"])],
        witness: Some(A_AT_0_1),
        all_indices: Some(&[&[0, 1], &[0, 2]]),
        ..CASE
    },
    Case {
        id: "no-stable-path-key-reports-all-without-primary",
        stable: false,
        paths: &[unkeyed(&["wa", "la", "la"])],
        all_indices: Some(&[&[0, 1], &[0, 2]]),
        ..CASE
    },
    Case {
        id: "unkeyed-full-report-is-permutation-invariant",
        stable: false,
        paths: &[unkeyed(&["wa", "la", "la"]), unkeyed(&["wb", "lb"])],
        permutation_witnesses: Some(3),
        ..CASE
    },
    Case {
        id: "existential-first-stops-after-match",
        search: SearchPolicy::ExistentialFirst,
        paths: &[stopped("p0", PathStop::MatchFound, &["wa", "la"])],
        complete_coverage: false,
        search_stopped: true,
        witness: Some(A_AT_0_1),
        ..CASE
    },
    Case {
        id: "sibling-branches-never-combine",
        paths: &[done("left", &["wa"]), done("right", &["la"])],
        outcome: NoMatch,
        ..CASE
    },
    Case {
        id: "matching-branch-dominates-truncated-sibling",
        paths: &[
            done("left", &["wa", "la"]),
            stopped("right", DepthLimit, &["wa"]),
        ],
        complete_coverage: false,
        witness: Some(Witnessed {
            key: "left",
            ..A_AT_0_1
        }),
        ..CASE
    },
    Case {
        id: "bounded-absence-is-unknown",
        paths: &[done("left", &["wa"]), stopped("right", DepthLimit, &["wa"])],
        outcome: Unknown,
        complete_coverage: false,
        failure: Some(DepthLimit),
        ..CASE
    },
    Case {
        id: "shared-symbolic-payload",
        paths: &[done("symbolic", &["wSymbolic", "lSymbolic"])],
        witness: Some(Witnessed {
            key: "symbolic",
            bindings: &[("A", "symbolicA")],
            ..A_AT_0_1
        }),
        ..CASE
    },
    Case {
        id: "distinct-symbolic-terms-related-by-constraint",
        paths: &[PathSpec {
            equivalences: &[("symbolicX", "symbolicY")],
            predicate: "x-equals-y",
            ..done("symbolic-equality", &["wSymbolicX", "lSymbolicY"])
        }],
        witness: Some(Witnessed {
            key: "symbolic-equality",
            bindings: &[("A", "symbolicX")],
            predicate: "x-equals-y",
            ..A_AT_0_1
        }),
        ..CASE
    },
    Case {
        id: "distinct-symbolic-terms-proven-unequal",
        paths: &[PathSpec {
            inequalities: &[("symbolicX", "symbolicY")],
            predicate: "x-not-equals-y",
            ..done("symbolic-inequality", &["wSymbolicX", "lSymbolicY"])
        }],
        outcome: NoMatch,
        ..CASE
    },
    Case {
        id: "feasible-match-dominates-indeterminate-candidate",
        paths: &[
            stopped("unknown", SolverUnknown, &["wSymbolicX", "lSymbolicY"]),
            done("feasible", &["wa", "la"]),
        ],
        complete_coverage: false,
        witness: Some(Witnessed {
            key: "feasible",
            ..A_AT_0_1
        }),
        ..CASE
    },
    Case {
        id: "solver-indeterminate-absence",
        paths: &[stopped(
            "symbolic",
            SolverUnknown,
            &["wSymbolicX", "lSymbolicY"],
        )],
        outcome: Unknown,
        complete_coverage: false,
        failure: Some(SolverUnknown),
        ..CASE
    },
    Case {
        id: "malformed-structured-result",
        input_failure: true,
        outcome: Error,
        complete_coverage: false,
        failure: Some(PathStop::Error),
        ..CASE
    },
    Case {
        id: "side-condition-true",
        plan: "write-then-load-side-condition",
        paths: &[done("p0", &["wa", "la"])],
        witness: Some(A_AT_0_1),
        ..CASE
    },
    Case {
        id: "side-condition-false",
        plan: "write-then-load-side-condition",
        paths: &[done("p0", &["wb", "lb"])],
        outcome: NoMatch,
        ..CASE
    },
    Case {
        id: "side-condition-indeterminate",
        plan: "write-then-load-side-condition",
        paths: &[stopped("p0", SolverUnknown, &["wSymbolic", "lSymbolic"])],
        outcome: Unknown,
        complete_coverage: false,
        failure: Some(SolverUnknown),
        ..CASE
    },
    Case {
        id: "alternative-load-arm",
        plan: "write-eventually-load-or-free",
        paths: &[done("p0", &["wa", "la"])],
        witness: Some(A_AT_0_1),
        ..CASE
    },
    Case {
        id: "alternative-free-arm",
        plan: "write-eventually-load-or-free",
        paths: &[done("p0", &["wa", "fa"])],
        witness: Some(Witnessed { arm: 1, ..A_AT_0_1 }),
        ..CASE
    },
    Case {
        id: "alternative-neither-arm",
        plan: "write-eventually-load-or-free",
        paths: &[done("p0", &["wa", "x"])],
        outcome: NoMatch,
        ..CASE
    },
    Case {
        id: "overlapping-alternatives-use-declaration-order",
        plan: "overlapping-load-alternatives",
        paths: &[done("p0", &["wa", "la"])],
        witness: Some(A_AT_0_1),
        ..CASE
    },
    Case {
        id: "canonical-primary-across-paths",
        paths: &[done("later", &["wa", "la"]), done("earlier", &["wa", "la"])],
        witness: Some(Witnessed {
            key: "earlier",
            ..A_AT_0_1
        }),
        all_paths: Some(&["earlier", "later"]),
        ..CASE
    },
    Case {
        id: "counter-family-occurrence",
        plan: "increment-eventually-branch",
        paths: &[done("counter", &["counterIncrement", "x", "branchTaken"])],
        witness: Some(Witnessed {
            key: "counter",
            indices: &[0, 2],
            bindings: &[("N", "v8")],
            ..A_AT_0_1
        }),
        ..CASE
    },
    Case {
        id: "constant-side-condition-true",
        plan: "write-then-load-constant-side-condition",
        paths: &[done("p0", &["wa", "la"])],
        witness: Some(A_AT_0_1),
        ..CASE
    },
    Case {
        id: "subset-side-condition-preserves-nonlexical-declaration-order",
        plan: "nonlexical-subset-side-condition",
        paths: &[done("p0", &["wa", "la"])],
        witness: Some(Witnessed {
            bindings: &[("VALUE", "v7"), ("ADDRESS", "a")],
            ..A_AT_0_1
        }),
        ..CASE
    },
];

#[test]
fn every_execution_pattern_row_matches_its_denotation() {
    let table = side_table();
    for case in &CASES {
        let id = case.id;
        let plan = plan(case.plan);
        let paths = paths(case.paths, id);
        let context = context(id);
        let collection = collection(&paths, case.search);
        let options = EvaluationOptions {
            stable_path_keys: case.stable,
            search_policy: case.search,
            input_error: case.input_failure,
        };
        let result = evaluate(&context, &plan, &paths, &collection, Some(&table), options)
            .unwrap_or_else(|error| panic!("{id}: {error}"));
        assert_eq!(result.outcome, case.outcome, "{id}");
        assert_eq!(result.complete_coverage, case.complete_coverage, "{id}");
        assert_eq!(result.bounds, context.bounds, "{id}");
        assert_eq!(result.failure, case.failure, "{id}");
        assert_eq!(
            collection.stop == CollectionStop::MatchFound,
            case.search_stopped,
            "{id}"
        );
        assert_eq!(result.search_policy, case.search, "{id}");
        if let Some(expected) = &case.witness {
            let actual = &result.witnesses[result.primary_witness.expect("keyed primary")];
            assert_eq!(actual.path_key.as_deref(), Some(expected.key), "{id}");
            assert_eq!(actual.event_indices, expected.indices, "{id}");
            let source = &paths[actual.path_ordinal];
            assert_eq!(actual.stop_reason, source.stop, "{id}");
            assert_eq!(actual.execution_stop_reason, source.execution_stop, "{id}");
            assert_eq!(
                actual.events,
                actual
                    .event_indices
                    .iter()
                    .map(|index| source.events[*index].clone())
                    .collect::<Vec<_>>(),
                "{id}"
            );
            assert_eq!(actual.arm_ordinal, expected.arm, "{id}");
            let expected_bindings = expected
                .bindings
                .iter()
                .map(|(name, value)| ((*name).to_owned(), term(value)))
                .collect::<Vec<_>>();
            assert_eq!(
                actual
                    .bindings
                    .iter()
                    .map(|binding| (binding.name.clone(), binding.term.clone()))
                    .collect::<Vec<_>>(),
                expected_bindings,
                "{id}"
            );
            assert_eq!(actual.path_predicate, predicate(expected.predicate), "{id}");
        } else {
            assert_eq!(result.primary_witness, None, "{id}");
        }
        if let Some(expected) = case.all_indices {
            let actual = result
                .witnesses
                .iter()
                .map(|witness| witness.event_indices.as_slice())
                .collect::<Vec<_>>();
            assert_eq!(actual, expected, "{id}");
        }
        if let Some(expected) = case.all_paths {
            let actual = result
                .witnesses
                .iter()
                .map(|witness| witness.path_key.as_deref().expect("keyed witness"))
                .collect::<Vec<_>>();
            assert_eq!(actual, expected, "{id}");
        }
        if let Some(count) = case.permutation_witnesses {
            let mut reversed = paths.clone();
            reversed.reverse();
            let permuted = evaluate(
                &context,
                &plan,
                &reversed,
                &collection,
                Some(&table),
                options,
            )
            .expect("permuted evaluation");
            assert_eq!(result, permuted, "{id}");
            assert_eq!(result.witnesses.len(), count, "{id}");
        }
    }
}

/// The plan adversaries that remain expressible once plans are typed values: an extension
/// field, an unsupported mode or relation, and a stale plan or query identity are no
/// longer representable.
#[test]
fn plan_adversaries_fail_closed() {
    type Mutation = fn(&mut support::PlanParts);
    let rows: [(&str, &str, Mutation, PatternFailureKind); 3] = [
        (
            "lowercase-binding",
            "write-eventually-load",
            |parts| parts.variables[0].0 = "lowercase".to_owned(),
            PatternFailureKind::InvalidVariable,
        ),
        (
            "duplicate-payload-position",
            "write-eventually-load",
            |parts| {
                let duplicate = parts.arms[0].atoms[0].payload[0].clone();
                parts.arms[0].atoms[0].payload.push(duplicate);
            },
            PatternFailureKind::InvalidPayload,
        ),
        (
            "noncanonical-side-subset",
            "nonlexical-subset-side-condition",
            |parts| {
                parts.side_condition = Some(SideCondition {
                    name: support::SIDE_CONDITION.to_owned(),
                    input_variables: vec!["ADDRESS".to_owned(), "VALUE".to_owned()],
                });
            },
            PatternFailureKind::InvalidVariable,
        ),
    ];
    for (id, name, mutate, expected) in rows {
        let mut parts = plan_parts(name);
        mutate(&mut parts);
        let failure = PatternPlan::new(
            &support::memory(),
            parts.variables,
            parts.arms,
            parts.side_condition,
        )
        .expect_err(id);
        assert_eq!(failure.kind(), expected, "{id}: {failure}");
    }
}

/// Evaluates `paths` of the single-write-load row with a modified context.
fn evaluate_single(
    id: &str,
    paths: &[PathInput],
    context: &kink_pattern::EvaluationContext,
) -> Result<kink_pattern::Evaluation, kink_pattern::PatternFailure> {
    evaluate(
        context,
        &plan("write-eventually-load"),
        paths,
        &collection(paths, SearchPolicy::Exhaustive),
        None,
        exhaustive_options(),
    )
    .map_err(|failure| {
        eprintln!("{id}: {failure}");
        failure
    })
}

/// Test, bounds, origin and relation roots of a trace are checked against its context; empty
/// exhaustion needs an explicit decision; aggregation needs exhaustion before absence.
#[test]
fn trace_context_nested_symbolics_and_empty_exhaustion_fail_closed() {
    let id = "single-event";
    let base = paths(&[done("p0", &["wa", "la"])], id);
    evaluate_single(id, &base, &context(id)).expect("validated base row");

    let mut wrong_test = base.clone();
    wrong_test[0].test_id = "another-test".to_owned();
    assert_eq!(
        evaluate_single(id, &wrong_test, &context(id))
            .expect_err("another test's trace")
            .kind(),
        PatternFailureKind::TestMismatch
    );

    let mut wrong_bounds = context(id);
    wrong_bounds.bounds.time_ms = Some(0);
    assert_eq!(
        evaluate_single(id, &base, &wrong_bounds)
            .expect_err("invalid bounds")
            .kind(),
        PatternFailureKind::BoundsMismatch
    );

    let mut empty_role = base.clone();
    empty_role[0].events[0]
        .origin
        .semantic_site
        .as_mut()
        .expect("memory event site")
        .role
        .clear();
    assert_eq!(
        evaluate_single(id, &empty_role, &context(id))
            .expect_err("semantic site without a role")
            .kind(),
        PatternFailureKind::InvalidOrigin
    );
    let mut missing_site = base.clone();
    missing_site[0].events[0].origin.semantic_site = None;
    assert_eq!(
        evaluate_single(id, &missing_site, &context(id))
            .expect_err("memory event without its semantic site")
            .kind(),
        PatternFailureKind::InvalidOrigin
    );

    // A nested symbolic payload is neither equal nor unequal without a relation.
    let symbolic = |name: &str| app("LblsymbolicAddress", vec![var(name, "SortInt")]);
    let mut nested = paths(&[done("p0", &["wa", "lb"])], id);
    nested[0].events[0].payload[0] = symbolic("X");
    nested[0].events[1].payload[0] = symbolic("Y");
    let result = evaluate_single(id, &nested, &context(id)).expect("typed unknown");
    assert_eq!(result.outcome, Unknown);
    assert!(!result.complete_coverage);
    assert_eq!(result.failure, Some(SolverUnknown));

    let empty = context("empty-search");
    let missing_decision = CollectionEvidence {
        stop: CollectionStop::SearchExhausted,
        pending_work: 0,
        empty_search_decision: None,
    };
    let write_load = plan("write-eventually-load");
    assert_eq!(
        evaluate(
            &empty,
            &write_load,
            &[],
            &missing_decision,
            None,
            exhaustive_options()
        )
        .expect_err("empty exhaustion without evidence")
        .kind(),
        PatternFailureKind::InvalidCollection
    );
    let decided = CollectionEvidence {
        empty_search_decision: Some(EmptySearchDecision),
        ..missing_decision.clone()
    };
    assert_eq!(
        evaluate(
            &empty,
            &write_load,
            &[],
            &decided,
            None,
            exhaustive_options()
        )
        .expect("explicit empty exhaustion")
        .outcome,
        NoMatch
    );
    let visited = paths(&[done("p0", &["wa"])], "empty-search");
    assert_eq!(
        evaluate(
            &empty,
            &write_load,
            &visited,
            &decided,
            None,
            exhaustive_options()
        )
        .expect_err("an empty-search decision beside a visited path")
        .kind(),
        PatternFailureKind::InvalidCollection
    );
    assert_eq!(aggregate_existential(&[], false, None), Unknown);
    assert_eq!(
        aggregate_existential(&[], false, Some(EmptySearchDecision)),
        NoMatch
    );

    // (components, global error, expected), from the former `aggregationCases`.
    let rows: [(&[PatternOutcome], bool, PatternOutcome); 6] = [
        (&[NoMatch, NoMatch], false, NoMatch),
        (&[NoMatch, Unknown], false, Unknown),
        (&[Match, Unknown], false, Match),
        (&[Match, Error], false, Match),
        (&[Match, NoMatch], true, Error),
        (&[NoMatch, Error], false, Unknown),
    ];
    for (components, global_error, expected) in rows {
        assert_eq!(
            aggregate_existential(components, global_error, Some(EmptySearchDecision)),
            expected,
            "{components:?} global error {global_error}"
        );
    }
}

/// P7: a semantic crash is a complete terminal carrying its own terminal term.
#[test]
fn semantic_termination_rows_preserve_terminal_evidence() {
    let write_load = plan("write-eventually-load");
    let exhausted = CollectionEvidence {
        stop: CollectionStop::SearchExhausted,
        pending_work: 0,
        empty_search_decision: None,
    };
    // (id, terminal kind or none, witness events kept, expected outcome or rejection)
    type Expected = Result<PatternOutcome, PatternFailureKind>;
    let rows: [(&str, Option<ExecutionTerminalKind>, bool, Expected); 3] = [
        (
            "crash-with-prior-witness",
            Some(ExecutionTerminalKind::SemanticCrash),
            true,
            Ok(Match),
        ),
        (
            "crash-with-exhaustive-absence",
            Some(ExecutionTerminalKind::SemanticCrash),
            false,
            Ok(NoMatch),
        ),
        (
            "missing-crash-evidence",
            None,
            false,
            Err(PatternFailureKind::TerminalMismatch),
        ),
    ];
    for (id, kind, witness, expected) in rows {
        let mut paths = paths(&[done("p0", &["wa", "la"])], id);
        paths[0].execution_terminal = kind.map(|kind| ExecutionTerminal {
            kind,
            state: terminal_state(kind),
        });
        if !witness {
            paths[0].events.clear();
        }
        let result = evaluate(
            &context(id),
            &write_load,
            &paths,
            &exhausted,
            None,
            exhaustive_options(),
        );
        assert_eq!(
            result
                .map(|evaluation| evaluation.outcome)
                .map_err(|failure| failure.kind()),
            expected,
            "{id}"
        );
    }
    let id = "backend-error-before-path";
    let result = evaluate(
        &context(id),
        &write_load,
        &[],
        &CollectionEvidence {
            stop: CollectionStop::Error,
            pending_work: 0,
            empty_search_decision: None,
        },
        None,
        EvaluationOptions {
            input_error: true,
            ..exhaustive_options()
        },
    )
    .expect("global backend error result");
    assert_eq!(result.outcome, Error, "{id}");
}

/// One path of an inline row with explicit transition ordinals; emission ordinals are
/// derived. An empty `transitions` keeps one transition per event.
struct LiteralPath {
    key: Option<&'static str>,
    events: &'static [&'static str],
    transitions: &'static [u64],
}

fn literal_paths(id: &str, rows: &[LiteralPath]) -> Vec<PathInput> {
    rows.iter()
        .enumerate()
        .map(|(ordinal, row)| {
            let spec = PathSpec {
                key: row.key,
                ..done("", row.events)
            };
            let mut path = path(&spec, id, ordinal);
            if !row.transitions.is_empty() {
                assert_eq!(row.transitions.len(), path.events.len(), "{id}");
                let mut previous = None;
                let mut emission = 0;
                for (event, transition) in path.events.iter_mut().zip(row.transitions) {
                    emission = if previous == Some(*transition) {
                        emission + 1
                    } else {
                        0
                    };
                    event.transition_ordinal = *transition;
                    event.emission_ordinal = emission;
                    previous = Some(*transition);
                }
            }
            path
        })
        .collect()
}

struct DenotationRow {
    id: &'static str,
    plan: &'static str,
    stable: bool,
    paths: &'static [LiteralPath],
    witnesses: &'static [(Option<&'static str>, &'static [usize])],
}

#[test]
fn inline_occurrence_and_adjacency_rows_report_every_witness() {
    let rows = [
        // P1: every occurrence is reported; the primary witness is the earliest one.
        DenotationRow {
            id: "write-load-load-reports-both-occurrences",
            plan: "write-eventually-load",
            stable: true,
            paths: &[LiteralPath {
                key: Some("p0"),
                events: &["wa", "la", "la"],
                transitions: &[],
            }],
            witnesses: &[(Some("p0"), &[0, 1]), (Some("p0"), &[0, 2])],
        },
        DenotationRow {
            id: "unkeyed-write-load-load-reports-both-occurrences",
            plan: "write-eventually-load",
            stable: false,
            paths: &[LiteralPath {
                key: None,
                events: &["wa", "la", "la"],
                transitions: &[],
            }],
            witnesses: &[(None, &[0, 1]), (None, &[0, 2])],
        },
        // O2: next-event is adjacency on the observed-event clock, not on transitions.
        DenotationRow {
            id: "adjacent-events-from-non-adjacent-transitions",
            plan: "write-next-load",
            stable: true,
            paths: &[LiteralPath {
                key: Some("p0"),
                events: &["wa", "la"],
                transitions: &[7, 9],
            }],
            witnesses: &[(Some("p0"), &[0, 1])],
        },
        DenotationRow {
            id: "two-events-of-one-transition-are-adjacent",
            plan: "write-next-load",
            stable: true,
            paths: &[LiteralPath {
                key: Some("p0"),
                events: &["wa", "la"],
                transitions: &[7, 7],
            }],
            witnesses: &[(Some("p0"), &[0, 1])],
        },
        // P8: two branches with identical traces are two occurrences.
        DenotationRow {
            id: "identical-keyed-branches-are-two-occurrences",
            plan: "write-eventually-load",
            stable: true,
            paths: &[
                LiteralPath {
                    key: Some("left"),
                    events: &["wa", "la"],
                    transitions: &[],
                },
                LiteralPath {
                    key: Some("right"),
                    events: &["wa", "la"],
                    transitions: &[],
                },
            ],
            witnesses: &[(Some("left"), &[0, 1]), (Some("right"), &[0, 1])],
        },
    ];
    for row in rows {
        let paths = literal_paths(row.id, row.paths);
        let result = evaluate(
            &context(row.id),
            &plan(row.plan),
            &paths,
            &collection(&paths, SearchPolicy::Exhaustive),
            None,
            EvaluationOptions {
                stable_path_keys: row.stable,
                ..exhaustive_options()
            },
        )
        .unwrap_or_else(|error| panic!("{}: {error}", row.id));
        assert_eq!(result.outcome, Match, "{}", row.id);
        assert!(result.complete_coverage, "{}", row.id);
        assert_eq!(
            result
                .witnesses
                .iter()
                .map(|witness| (
                    witness.path_key.as_deref(),
                    witness.event_indices.as_slice()
                ))
                .collect::<Vec<_>>(),
            row.witnesses.to_vec(),
            "{}",
            row.id
        );
        assert_eq!(
            result.primary_witness,
            row.stable.then_some(0),
            "{}",
            row.id
        );
    }
}

// P8: unkeyed mode has no schedule-independent way to tell identical branches apart,
// so it rejects them instead of reporting two occurrences (the former BAG-16 did) or
// coalescing them.
#[test]
fn identical_unkeyed_branches_are_rejected() {
    let id = "identical-unkeyed-branches-are-rejected";
    let branch = || LiteralPath {
        key: None,
        events: &["wa", "la"],
        transitions: &[],
    };
    let paths = literal_paths(id, &[branch(), branch()]);
    let failure = evaluate(
        &context(id),
        &plan("write-eventually-load"),
        &paths,
        &collection(&paths, SearchPolicy::Exhaustive),
        None,
        EvaluationOptions {
            stable_path_keys: false,
            ..exhaustive_options()
        },
    )
    .expect_err(id);
    assert_eq!(
        failure.kind(),
        PatternFailureKind::InvalidPath,
        "{id}: {failure}"
    );
}

/// The trace shape covers relations: two unkeyed paths whose events agree but whose
/// relations differ are two paths, and evaluate differently.
#[test]
fn unkeyed_paths_differing_only_in_relations_are_distinct() {
    let id = "unkeyed-paths-differing-only-in-relations";
    let related = |equivalences, inequalities| PathSpec {
        key: None,
        equivalences,
        inequalities,
        ..done("", &["wSymbolicX", "lSymbolicY"])
    };
    let paths = paths(
        &[
            related(&[("symbolicX", "symbolicY")], &[]),
            related(&[], &[("symbolicX", "symbolicY")]),
        ],
        id,
    );
    let result = evaluate(
        &context(id),
        &plan("write-eventually-load"),
        &paths,
        &collection(&paths, SearchPolicy::Exhaustive),
        None,
        EvaluationOptions {
            stable_path_keys: false,
            ..exhaustive_options()
        },
    )
    .unwrap_or_else(|failure| panic!("{id}: {failure}"));
    assert_eq!(result.outcome, Match);
    assert!(result.complete_coverage);
    assert_eq!(result.witnesses.len(), 1);
    assert_eq!(result.witnesses[0].path_ordinal, 0);
    assert_eq!(result.witnesses[0].path_key, None);
}

/// O3: an event's payload must have its constructor's sorts under the definition's symbol
/// sorts, and it must come from a rule that was observed.
#[test]
fn payload_sort_drift_and_unselected_origin_are_rejected() {
    let id = "payload-sort-drift-and-unselected-origin";
    let base = paths(&[done("p0", &["wa", "la"])], id);
    type Mutation = fn(&mut PathInput, &mut kink_pattern::EvaluationContext);
    let rows: [(&str, Mutation, PatternFailureKind); 6] = [
        (
            "int-in-an-address-position",
            |path, _| path.events[0].payload[0] = term("v7"),
            PatternFailureKind::InvalidPayload,
        ),
        (
            "variable-of-another-sort",
            |path, _| path.events[0].payload[0] = var("A0", "SortInt"),
            PatternFailureKind::InvalidPayload,
        ),
        (
            "undeclared-symbol-has-no-decidable-sort",
            |path, _| path.events[0].payload[0] = app("LblnoSuchSymbol", Vec::new()),
            PatternFailureKind::InvalidPayload,
        ),
        (
            "symbol-sort-drift",
            |_, context| {
                context.symbol_sorts = kink_pattern::SymbolSorts::new([(
                    "Lbladdr".to_owned(),
                    vec![sort("SortInt")],
                    sort("SortInt"),
                )]);
            },
            PatternFailureKind::InvalidPayload,
        ),
        (
            "unselected-origin",
            |_, context| {
                context.selected_rule_labels.remove("MEMORY.write");
            },
            PatternFailureKind::InvalidOrigin,
        ),
        (
            "unknown-trace-constructor",
            |path, _| path.events[0].constructor = "memoryStore".to_owned(),
            PatternFailureKind::UnknownConstructor,
        ),
    ];
    for (row, mutate, expected) in rows {
        let mut paths = base.clone();
        let mut context = context(id);
        mutate(&mut paths[0], &mut context);
        assert_eq!(
            evaluate_single(row, &paths, &context)
                .expect_err(row)
                .kind(),
            expected,
            "{row}"
        );
    }
    // An injection is typed at its target sort.
    let mut injected = base;
    injected[0].events[0].payload[0] = k_rust::kore::ast::Pattern::Application {
        symbol: k_rust::kore::ast::Symbol {
            name: "inj".to_owned(),
            sort_parameters: vec![sort("SortNat"), sort("SortAddress")],
        },
        arguments: vec![app("Lblz", Vec::new())],
    };
    injected[0].events[1].payload[0] = injected[0].events[0].payload[0].clone();
    assert_eq!(
        evaluate_single(id, &injected, &context(id))
            .expect("inj{Nat, Address} is an Address")
            .outcome,
        Match
    );
}

struct RejectionScenario {
    paths: Vec<PathInput>,
    collection: CollectionEvidence,
    search_policy: SearchPolicy,
}

fn complete_with_depth_limit(scenario: &mut RejectionScenario) {
    let path = &mut scenario.paths[0];
    path.stop = PathStop::DepthLimit;
    path.execution_stop = ExecutionStop::DepthLimit;
    path.execution_terminal = None;
}

fn complete_with_depth_limit_and_terminal(scenario: &mut RejectionScenario) {
    let path = &mut scenario.paths[0];
    path.stop = PathStop::DepthLimit;
    path.execution_stop = ExecutionStop::DepthLimit;
}

fn duplicate_event_index(scenario: &mut RejectionScenario) {
    scenario.paths[0].events[1].index = 0;
}

fn existential_match_without_match_stop(scenario: &mut RejectionScenario) {
    make_match_stop(&mut scenario.paths[0]);
    scenario.search_policy = SearchPolicy::ExistentialFirst;
}

fn existential_match_stop(scenario: &mut RejectionScenario) {
    existential_match_without_match_stop(scenario);
    scenario.collection.stop = CollectionStop::MatchFound;
    scenario.collection.pending_work = 1;
}

/// Path 0 stays a complete matching path; its clone as path 1 carries the match stop.
fn existential_match_stop_beside_matching_path(scenario: &mut RejectionScenario) {
    let mut stopped = scenario.paths[0].clone();
    stopped.path_ordinal = 1;
    stopped.path_key = Some("p1".to_owned());
    make_match_stop(&mut stopped);
    scenario.paths.push(stopped);
    scenario.search_policy = SearchPolicy::ExistentialFirst;
    scenario.collection.stop = CollectionStop::MatchFound;
    scenario.collection.pending_work = 1;
}

fn match_stop_under_exhaustive_policy(scenario: &mut RejectionScenario) {
    existential_match_without_match_stop(scenario);
    scenario.search_policy = SearchPolicy::Exhaustive;
    scenario.collection.stop = CollectionStop::MatchFound;
    scenario.collection.pending_work = 1;
}

fn exhaustion_with_pending_work(scenario: &mut RejectionScenario) {
    scenario.collection.pending_work = 1;
}

fn contradictory_symbolic_relations(scenario: &mut RejectionScenario) {
    let path = &mut scenario.paths[0];
    let pair = path.inequalities[0].clone();
    path.equivalences.push(pair);
}

fn relation_across_sorts(scenario: &mut RejectionScenario) {
    scenario.paths[0].equivalences.push(TermRelation {
        left: term("symbolicX"),
        right: term("v7"),
    });
}

#[test]
fn inline_trace_honesty_and_relation_rows_reject_with_typed_kinds() {
    const WRITE_LOAD: PathSpec = done("p0", &["wa", "la"]);
    const PROVEN_UNEQUAL: PathSpec = PathSpec {
        inequalities: &[("symbolicX", "symbolicY")],
        predicate: "x-not-equals-y",
        ..done("p0", &["wSymbolicX", "lSymbolicY"])
    };
    const WRITE_ONLY: PathSpec = done("p0", &["wa"]);
    type Mutation = fn(&mut RejectionScenario);
    let rows: [(&str, PathSpec, Mutation, PatternFailureKind); 11] = [
        // P2: a complete trace cannot carry a bounded stop.
        (
            "complete-trace-with-depth-limit-stop",
            WRITE_LOAD,
            complete_with_depth_limit,
            PatternFailureKind::TerminalMismatch,
        ),
        (
            "complete-trace-with-depth-limit-stop-and-terminal",
            WRITE_LOAD,
            complete_with_depth_limit_and_terminal,
            PatternFailureKind::TerminalMismatch,
        ),
        // P2: event indices are dense and unique.
        (
            "duplicate-event-index",
            WRITE_LOAD,
            duplicate_event_index,
            PatternFailureKind::InvalidPath,
        ),
        // P2: an existential match stop appears only as the collection's own stop.
        (
            "existential-match-path-under-exhausted-collection",
            WRITE_LOAD,
            existential_match_without_match_stop,
            PatternFailureKind::InvalidCollection,
        ),
        (
            "match-found-collection-under-exhaustive-policy",
            WRITE_LOAD,
            match_stop_under_exhaustive_policy,
            PatternFailureKind::InvalidCollection,
        ),
        // P2: an existential-first witness lies exactly on the match-found path, and a
        // determinate match-found path has one: the stop must be the plan's own match.
        (
            "existential-first-exhausted-collection-retains-witness",
            WRITE_LOAD,
            |scenario| scenario.search_policy = SearchPolicy::ExistentialFirst,
            PatternFailureKind::InvalidCollection,
        ),
        (
            "existential-first-witness-outside-match-stop",
            WRITE_LOAD,
            existential_match_stop_beside_matching_path,
            PatternFailureKind::InvalidCollection,
        ),
        (
            "existential-first-match-stop-without-witness",
            WRITE_ONLY,
            existential_match_stop,
            PatternFailureKind::InvalidCollection,
        ),
        (
            "clean-exhaustion-with-pending-work",
            WRITE_LOAD,
            exhaustion_with_pending_work,
            PatternFailureKind::InvalidCollection,
        ),
        // P3: one path cannot both equate and separate two terms.
        (
            "contradictory-symbolic-relations",
            PROVEN_UNEQUAL,
            contradictory_symbolic_relations,
            PatternFailureKind::InvalidPath,
        ),
        (
            "relation-across-sorts",
            PROVEN_UNEQUAL,
            relation_across_sorts,
            PatternFailureKind::InvalidTerm,
        ),
    ];
    let plan = plan("write-eventually-load");
    for (id, base, mutate, expected) in rows {
        let paths = vec![path(&base, id, 0)];
        let mut scenario = RejectionScenario {
            collection: collection(&paths, SearchPolicy::Exhaustive),
            paths,
            search_policy: SearchPolicy::Exhaustive,
        };
        evaluate(
            &context(id),
            &plan,
            &scenario.paths,
            &scenario.collection,
            None,
            exhaustive_options(),
        )
        .unwrap_or_else(|error| panic!("{id}: unmutated base rejected: {error}"));
        mutate(&mut scenario);
        let failure = evaluate(
            &context(id),
            &plan,
            &scenario.paths,
            &scenario.collection,
            None,
            EvaluationOptions {
                search_policy: scenario.search_policy,
                ..exhaustive_options()
            },
        )
        .expect_err(id);
        assert_eq!(failure.kind(), expected, "{id}: {failure}");
    }
}

/// One existential-first row over a single path, optionally turned into the match stop.
struct ExistentialRow {
    id: &'static str,
    plan: &'static str,
    events: &'static [&'static str],
    predicate: &'static str,
    match_stop: bool,
    outcome: PatternOutcome,
    complete_coverage: bool,
    failure: Option<PathStop>,
}

#[test]
fn inline_existential_first_rows_keep_absence_and_missing_evidence() {
    let table = side_table();
    let rows = [
        // Absence under exhaustion does not depend on the stop policy. Backed only by
        // BAG-16: the v1 vectors hold no existential-first absence case.
        ExistentialRow {
            id: "existential-first-exhausted-absence-is-no-match",
            plan: "write-eventually-load",
            events: &["wa"],
            predicate: "true",
            match_stop: false,
            outcome: NoMatch,
            complete_coverage: true,
            failure: None,
        },
        // A match stop whose only candidate has no side-condition row is missing
        // evidence, not a dishonest stop; BAG-16 raised here instead. The cause is the
        // indeterminate candidate, not the match stop.
        ExistentialRow {
            id: "existential-first-indeterminate-match-stop-is-unknown",
            plan: "write-then-load-side-condition",
            events: &["wa", "la"],
            predicate: "false",
            match_stop: true,
            outcome: Unknown,
            complete_coverage: false,
            failure: Some(SolverUnknown),
        },
    ];
    for row in rows {
        let spec = PathSpec {
            predicate: row.predicate,
            ..done("p0", row.events)
        };
        let mut path = path(&spec, row.id, 0);
        if row.match_stop {
            make_match_stop(&mut path);
        }
        let paths = vec![path];
        let result = evaluate(
            &context(row.id),
            &plan(row.plan),
            &paths,
            &collection(&paths, SearchPolicy::ExistentialFirst),
            Some(&table),
            EvaluationOptions {
                search_policy: SearchPolicy::ExistentialFirst,
                ..exhaustive_options()
            },
        )
        .unwrap_or_else(|error| panic!("{}: {error}", row.id));
        assert_eq!(result.outcome, row.outcome, "{}", row.id);
        assert_eq!(
            result.complete_coverage, row.complete_coverage,
            "{}",
            row.id
        );
        assert!(result.witnesses.is_empty(), "{}", row.id);
        assert_eq!(result.failure, row.failure, "{}", row.id);
    }
}

/// The indeterminate exemption belongs to the match-found path's own candidates: an
/// indeterminate candidate on another path does not excuse a match stop without a
/// witness, while the same candidate on the stop path still leaves `Unknown` caused
/// by `SolverUnknown`.
#[test]
fn existential_first_indeterminate_exemption_is_local_to_the_match_stop() {
    let table = side_table();
    let plan = plan("write-then-load-side-condition");
    let options = EvaluationOptions {
        search_policy: SearchPolicy::ExistentialFirst,
        ..exhaustive_options()
    };
    // (id, events on p0, events on the match-found p1, rejected)
    #[rustfmt::skip]
    let rows: [(&str, &'static [&'static str], &'static [&'static str], bool); 2] = [
        ("existential-first-indeterminate-elsewhere-does-not-excuse-match-stop", &["wa", "la"], &["wa"], true),
        ("existential-first-indeterminate-on-match-stop-beside-absence", &["wa"], &["wa", "la"], false),
    ];
    for (id, first, stopped, rejected) in rows {
        let first = path(
            &PathSpec {
                predicate: "false",
                ..done("p0", first)
            },
            id,
            0,
        );
        let mut stopped = path(
            &PathSpec {
                predicate: "false",
                ..done("p1", stopped)
            },
            id,
            1,
        );
        make_match_stop(&mut stopped);
        let paths = vec![first, stopped];
        let result = evaluate(
            &context(id),
            &plan,
            &paths,
            &collection(&paths, SearchPolicy::ExistentialFirst),
            Some(&table),
            options,
        );
        if rejected {
            assert_eq!(
                result.expect_err(id).kind(),
                PatternFailureKind::InvalidCollection,
                "{id}"
            );
        } else {
            let result = result.unwrap_or_else(|error| panic!("{id}: {error}"));
            assert_eq!(result.outcome, Unknown, "{id}");
            assert!(result.witnesses.is_empty(), "{id}");
            assert_eq!(result.failure, Some(SolverUnknown), "{id}");
        }
    }
}

/// One side-condition lookup row. `address` replaces the address payload of every event.
struct SideKeyRow {
    id: &'static str,
    plan: &'static str,
    events: &'static [&'static str],
    predicate: &'static str,
    address: Option<&'static str>,
    outcome: PatternOutcome,
}

#[test]
fn inline_side_condition_rows_key_only_declared_inputs_and_path_predicate() {
    let table = side_table();
    let rows = [
        SideKeyRow {
            id: "exact-key-resolves-true",
            plan: "write-then-load-side-condition",
            events: &["wa", "la"],
            predicate: "true",
            address: None,
            outcome: Match,
        },
        SideKeyRow {
            id: "exact-key-resolves-false",
            plan: "write-then-load-side-condition",
            events: &["wb", "lb"],
            predicate: "true",
            address: None,
            outcome: NoMatch,
        },
        SideKeyRow {
            id: "another-path-predicate-is-unknown",
            plan: "write-then-load-side-condition",
            events: &["wa", "la"],
            predicate: "false",
            address: None,
            outcome: Unknown,
        },
        SideKeyRow {
            id: "another-binding-tuple-is-unknown",
            plan: "write-then-load-side-condition",
            events: &["wa", "la"],
            predicate: "true",
            address: Some("3"),
            outcome: Unknown,
        },
        // A = b has a false row, but a constant condition keys on no binding at all.
        SideKeyRow {
            id: "constant-condition-ignores-witness-bindings",
            plan: "write-then-load-constant-side-condition",
            events: &["wb", "lb"],
            predicate: "true",
            address: None,
            outcome: Match,
        },
        // Only VALUE is declared; the undeclared ADDRESS binding never enters the key.
        SideKeyRow {
            id: "undeclared-binding-never-enters-the-key",
            plan: "nonlexical-subset-side-condition",
            events: &["wa", "la"],
            predicate: "true",
            address: Some("2"),
            outcome: Match,
        },
    ];
    for row in rows {
        let mut path = path(
            &PathSpec {
                predicate: row.predicate,
                ..done("p0", row.events)
            },
            row.id,
            0,
        );
        if let Some(value) = row.address {
            for event in &mut path.events {
                event.payload[0] = support::address(value);
            }
        }
        let paths = vec![path];
        let result = evaluate(
            &context(row.id),
            &plan(row.plan),
            &paths,
            &collection(&paths, SearchPolicy::Exhaustive),
            Some(&table),
            exhaustive_options(),
        )
        .unwrap_or_else(|error| panic!("{}: {error}", row.id));
        assert_eq!(result.outcome, row.outcome, "{}", row.id);
        assert_eq!(
            result.complete_coverage,
            row.outcome != Unknown,
            "{}",
            row.id
        );
        if row.outcome == Unknown {
            assert!(result.witnesses.is_empty(), "{}", row.id);
        }
    }
}

#[test]
fn inline_plan_adversaries_return_their_typed_failure_kind() {
    type Mutation = fn(&mut support::PlanParts);
    let rows: [(&str, Mutation, PatternFailureKind); 8] = [
        (
            "unknown-constructor",
            |parts| parts.arms[0].atoms[0].constructor = "missingEvent".to_owned(),
            PatternFailureKind::UnknownConstructor,
        ),
        (
            "payload-position-out-of-range",
            |parts| parts.arms[0].atoms[0].payload[0].position = 9,
            PatternFailureKind::InvalidPayload,
        ),
        (
            "duplicate-payload-position",
            |parts| parts.arms[0].atoms[0].payload.push(use_(0, "A")),
            PatternFailureKind::InvalidPayload,
        ),
        (
            "cross-sort-variable",
            |parts| parts.variables[0].1 = sort("SortInt"),
            PatternFailureKind::InvalidPayload,
        ),
        (
            "use-before-bind",
            |parts| parts.arms[0].atoms[0].payload[0] = use_(0, "A"),
            PatternFailureKind::InvalidVariable,
        ),
        (
            "rebound-variable",
            |parts| parts.arms[0].atoms[1].payload[0] = bind(0, "A"),
            PatternFailureKind::InvalidVariable,
        ),
        (
            "unused-declared-variable",
            |parts| {
                parts.variables.push(("B".to_owned(), sort("SortAddress")));
            },
            PatternFailureKind::InvalidVariable,
        ),
        (
            "relation-count-drift",
            |parts| parts.arms[0].relations.push(Relation::EventuallyAfter),
            PatternFailureKind::InvalidArm,
        ),
    ];
    for (id, mutate, expected) in rows {
        let mut parts = plan_parts("write-eventually-load");
        mutate(&mut parts);
        assert_eq!(
            PatternPlan::new(
                &support::memory(),
                parts.variables,
                parts.arms,
                parts.side_condition,
            )
            .expect_err(id)
            .kind(),
            expected,
            "{id}"
        );
    }

    // The unchanged plan against a vocabulary whose memoryWrite lost its payload.
    let mut constructors = support::memory_constructors();
    constructors
        .iter_mut()
        .find(|item| item.name == "memoryWrite")
        .expect("memoryWrite")
        .payload_sorts
        .clear();
    let drifted = EventVocabulary::new(constructors).expect("drifted vocabulary");
    let parts = plan_parts("write-eventually-load");
    assert_eq!(
        PatternPlan::new(&drifted, parts.variables, parts.arms, parts.side_condition)
            .expect_err("constructor arity drift")
            .kind(),
        PatternFailureKind::InvalidPayload
    );

    // A plan bound to one vocabulary, evaluated over a trace whose vocabulary gives the same
    // constructor other payload sorts.
    let id = "plan-bound-to-another-vocabulary";
    let mut trace_constructors = support::memory_constructors();
    trace_constructors
        .iter_mut()
        .find(|item| item.name == "memoryWrite")
        .expect("memoryWrite")
        .payload_sorts = vec![sort("SortAddress")];
    let mut other = context(id);
    other.vocabulary = EventVocabulary::new(trace_constructors).expect("trace vocabulary");
    let mut paths = paths(&[done("p0", &["wa", "la"])], id);
    paths[0].events[0].payload.truncate(1);
    assert_eq!(
        evaluate_single(id, &paths, &other).expect_err(id).kind(),
        PatternFailureKind::VocabularyMismatch
    );
    assert_eq!(
        EventVocabulary::new(vec![
            support::memory_constructors()[0].clone(),
            support::memory_constructors()[0].clone(),
        ])
        .expect_err("duplicate constructor")
        .kind(),
        PatternFailureKind::UnknownConstructor
    );
}

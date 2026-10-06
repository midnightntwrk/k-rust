//! Oracle projection, operand-eligibility and failure rows over hand-built runs.
//!
//! Sides are computed the way the runner computes them, from bridged paths
//! (`state_side`) and pattern evaluations (`pattern_side`), and compared with
//! `slot_outcome`. The E2 row IDs are those of the former
//! `oracle-semantics-vectors.json` (`evidenceCases`) for the kept oracle kinds;
//! its `concrete-output` rows wait for that kind. The E6 rows include its
//! `incompleteCases`.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::kompile::CompileError;
use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
use k_rust::kore::ast::Pattern;
use kink_campaign::{
    CrashPolicy, ExecutionFailureKind, ExitStop, FinalResult, ManifestTest, MutantId, MutantPlan,
    MutantScopeFailure, MutantStatus, OracleDeclaration, OracleFailureKind, OracleKind,
    OracleOutcome, OracleSide, OracleValue, PatternValue, Projection, ScheduleMode,
    StateProjection, TerminalClass, TestPlan, TestRun, compare_supplied, derive_mutant_report,
    pattern_side, slot_outcome, state_side,
};
use kink_native::MutantRejection;
use kink_native::bridge::{BridgeFailure, BridgedPaths, halt_stop};
use kink_native::execution::{ExecutionAdapterFailure, HaltClass};
use kink_patch::{Edit, Patch, PatchFailureKind, TermRef, Withdrawal, apply};
use kink_pattern::{
    Atom, Binding, CollectionEvidence, CollectionStop, Constructor, Evaluation, EvaluationContext,
    EvaluationOptions, EventVocabulary, ExecutionBounds, ExecutionStop, ExecutionTerminal,
    ExecutionTerminalKind, PathInput, PathStop, PatternArm, PatternFailure, PatternOutcome,
    PatternPlan, SearchPolicy, SymbolSorts, Witness, evaluate,
};

use CrashPolicy::{CompareIdentity, Distinguish as Distinguishes, Reject};
use ExecutionTerminalKind::{Normal, SemanticCrash, Stuck, UndefinedStep};
use OracleOutcome::{Agree, Distinguish, Incomparable};

const POLICIES: [CrashPolicy; 3] = [Reject, CompareIdentity, Distinguishes];

fn app(name: &str, arguments: Vec<Pattern>) -> Pattern {
    kore_application(&format!("Lbl{name}"), Vec::new(), arguments)
}

fn constant(name: &str) -> Pattern {
    app(name, Vec::new())
}

fn int(value: &str) -> Pattern {
    Pattern::DomainValue {
        sort: kore_sort("SortInt"),
        value: value.into(),
    }
}

/// `top(k(program), counter(count))`: the program at path `[0, 0]`.
fn configuration(program: &str, count: &str) -> Pattern {
    app(
        "top",
        vec![
            app("k", vec![constant(program)]),
            app("counter", vec![int(count)]),
        ],
    )
}

fn top() -> Pattern {
    Pattern::Top {
        sort: kore_sort("SortGeneratedTopCell"),
    }
}

fn path(
    ordinal: usize,
    complete: bool,
    stop: PathStop,
    terminal: Option<(ExecutionTerminalKind, Pattern)>,
) -> PathInput {
    PathInput {
        test_id: "t".to_owned(),
        path_ordinal: ordinal,
        path_key: Some(format!("p{ordinal}")),
        complete,
        stop,
        execution_stop: match stop {
            PathStop::Terminal => ExecutionStop::Terminal,
            PathStop::Stuck => ExecutionStop::Stuck,
            PathStop::UndefinedStep => ExecutionStop::UndefinedStep,
            PathStop::MatchFound => ExecutionStop::QuerySatisfied,
            PathStop::DepthLimit => ExecutionStop::DepthLimit,
            PathStop::TimeLimit => ExecutionStop::TimeLimit,
            PathStop::BranchLimit => ExecutionStop::BranchLimit,
            PathStop::ResultLimit => ExecutionStop::ResultLimit,
            PathStop::ResourceLimit => ExecutionStop::ResourceLimit,
            PathStop::SolverUnknown => ExecutionStop::SolverUnknown,
            PathStop::BackendLimit => ExecutionStop::BackendLimit,
            PathStop::Error => ExecutionStop::Error,
        },
        execution_terminal: terminal.map(|(kind, state)| ExecutionTerminal { kind, state }),
        events: Vec::new(),
        path_predicate: top(),
        equivalences: Vec::new(),
        inequalities: Vec::new(),
    }
}

/// A complete path ending in `state`, classified `kind`.
fn terminal(ordinal: usize, kind: ExecutionTerminalKind, state: Pattern) -> PathInput {
    let stop = match kind {
        Stuck => PathStop::Stuck,
        UndefinedStep => PathStop::UndefinedStep,
        Normal | SemanticCrash => PathStop::Terminal,
    };
    path(ordinal, true, stop, Some((kind, state)))
}

fn incomplete(ordinal: usize, stop: PathStop) -> PathInput {
    path(ordinal, false, stop, None)
}

fn collection(stop: CollectionStop) -> CollectionEvidence {
    CollectionEvidence {
        stop,
        pending_work: u64::from(stop != CollectionStop::SearchExhausted),
        empty_search_decision: None,
    }
}

/// Paths of a synthetic PathSet run: the collection is exhausted exactly when they are all
/// complete, and otherwise stops at the first incomplete path's stop.
fn run(paths: Vec<PathInput>) -> BridgedPaths {
    let stop =
        paths
            .iter()
            .find(|path| !path.complete)
            .map_or(CollectionStop::SearchExhausted, |path| match path.stop {
                PathStop::TimeLimit => CollectionStop::TimeLimit,
                PathStop::Error => CollectionStop::Error,
                PathStop::DepthLimit => CollectionStop::DepthLimit,
                PathStop::BranchLimit => CollectionStop::BranchLimit,
                PathStop::BackendLimit => CollectionStop::BackendLimit,
                _ => CollectionStop::SolverUnknown,
            });
    BridgedPaths {
        paths,
        collection: collection(stop),
    }
}

/// One complete path ending in `state`.
fn single(kind: ExecutionTerminalKind, state: Pattern) -> BridgedPaths {
    run(vec![terminal(0, kind, state)])
}

fn declaration(crash_policy: CrashPolicy, projection: Projection) -> OracleDeclaration {
    OracleDeclaration::new(crash_policy, projection).expect("declaration")
}

fn state(projection: StateProjection) -> OracleDeclaration {
    declaration(CompareIdentity, Projection::State(projection))
}

fn exit_stop(cell: Option<&str>) -> StateProjection {
    StateProjection::ExitStop {
        exit_code_cell: cell.map(str::to_owned),
    }
}

fn vocabulary() -> EventVocabulary {
    EventVocabulary::new(vec![Constructor {
        name: "write".to_owned(),
        payload_sorts: Vec::new(),
    }])
    .expect("vocabulary")
}

fn plan() -> PatternPlan {
    PatternPlan::new(
        &vocabulary(),
        Vec::new(),
        vec![PatternArm {
            atoms: vec![Atom {
                constructor: "write".to_owned(),
                payload: Vec::new(),
            }],
            relations: Vec::new(),
        }],
        None,
    )
    .expect("plan")
}

fn pattern(with_bindings: bool) -> OracleDeclaration {
    declaration(
        CompareIdentity,
        Projection::Pattern {
            plan: plan(),
            with_bindings,
        },
    )
}

/// An evaluation with one witness per binding tuple, in the given order.
fn evaluation(
    outcome: PatternOutcome,
    complete_coverage: bool,
    search_policy: SearchPolicy,
    tuples: &[&[(&str, &str)]],
) -> Result<Evaluation, PatternFailure> {
    Ok(Evaluation {
        outcome,
        complete_coverage,
        witnesses: tuples
            .iter()
            .enumerate()
            .map(|(ordinal, tuple)| Witness {
                path_ordinal: ordinal,
                path_key: Some(format!("p{ordinal}")),
                arm_ordinal: 0,
                event_indices: vec![0],
                events: Vec::new(),
                bindings: tuple
                    .iter()
                    .map(|(name, term)| Binding {
                        name: (*name).to_owned(),
                        term: constant(term),
                    })
                    .collect(),
                assumptions: Vec::new(),
                path_predicate: top(),
                stop_reason: PathStop::Terminal,
                execution_stop_reason: ExecutionStop::Terminal,
            })
            .collect(),
        primary_witness: (!tuples.is_empty()).then_some(0),
        failure: None,
        search_policy,
        bounds: ExecutionBounds {
            depth: None,
            time_ms: Some(1000),
            branches: None,
            results: None,
        },
    })
}

fn complete(
    outcome: PatternOutcome,
    tuples: &[&[(&str, &str)]],
) -> Result<Evaluation, PatternFailure> {
    evaluation(outcome, true, SearchPolicy::Exhaustive, tuples)
}

/// A real pattern failure: a path of another test than the evaluation context's.
fn pattern_failure() -> Result<Evaluation, PatternFailure> {
    let context = EvaluationContext {
        test_id: "other".to_owned(),
        bounds: ExecutionBounds {
            depth: None,
            time_ms: Some(1000),
            branches: None,
            results: None,
        },
        vocabulary: vocabulary(),
        symbol_sorts: SymbolSorts::default(),
    };
    let bridged = single(Normal, constant("done"));
    let result = evaluate(
        &context,
        &plan(),
        &bridged.paths,
        &bridged.collection,
        None,
        EvaluationOptions {
            stable_path_keys: true,
            search_policy: SearchPolicy::Exhaustive,
            input_error: false,
        },
    );
    assert!(result.is_err(), "a path of another test is rejected");
    result
}

fn normal(value: OracleValue) -> OracleSide {
    OracleSide::Normal(value)
}

/// (id, declaration, baseline, mutant, expected)
type ComparisonRow = (
    &'static str,
    OracleDeclaration,
    OracleSide,
    OracleSide,
    OracleOutcome,
);

/// E2: each comparator looks only at its own projection.
#[test]
fn e2_comparators_look_only_at_their_projection() {
    use PatternOutcome::{Match, NoMatch};
    let exit = || state(exit_stop(None));
    let whole = || state(StateProjection::WholeTerm);
    let paths = || state(StateProjection::TermPaths(vec![vec![0, 0]]));
    let side = |declaration: &OracleDeclaration, run: &BridgedPaths| match declaration.projection()
    {
        Projection::State(projection) => state_side(projection, run),
        Projection::Pattern { .. } => panic!("a state declaration"),
    };
    let done = configuration("done", "1");
    let rows: Vec<ComparisonRow> = vec![
        (
            // The terms differ; the terminal class and the absent exit code do not.
            "exit-stop-terminal-class-and-declared-exit-agree",
            exit(),
            side(&exit(), &single(Normal, done.clone())),
            side(&exit(), &single(Normal, configuration("distinct", "1"))),
            Agree,
        ),
        (
            "exit-stop-terminal-class-and-declared-exit-distinguish",
            exit(),
            side(&exit(), &single(Normal, done.clone())),
            side(&exit(), &single(Stuck, done.clone())),
            Distinguish,
        ),
        (
            "final-result-whole-portable-term-agree",
            whole(),
            side(&whole(), &single(Normal, done.clone())),
            side(&whole(), &single(Normal, done.clone())),
            Agree,
        ),
        (
            "final-result-whole-portable-term-distinguish",
            whole(),
            side(&whole(), &single(Normal, done.clone())),
            side(&whole(), &single(Normal, configuration("distinct", "1"))),
            Distinguish,
        ),
        (
            // The whole terms differ outside `[0, 0]`, as a counter cell would.
            "final-result-selected-term-paths-agree",
            paths(),
            side(&paths(), &single(Normal, done.clone())),
            side(&paths(), &single(Normal, configuration("done", "2"))),
            Agree,
        ),
        (
            "final-result-selected-term-paths-distinguish",
            paths(),
            side(&paths(), &single(Normal, done.clone())),
            side(&paths(), &single(Normal, configuration("distinct", "1"))),
            Distinguish,
        ),
        (
            "execution-pattern-pattern-outcome-agree",
            pattern(false),
            pattern_side(&complete(NoMatch, &[]), false),
            pattern_side(&complete(NoMatch, &[]), false),
            Agree,
        ),
        (
            "execution-pattern-pattern-outcome-distinguish",
            pattern(false),
            pattern_side(&complete(Match, &[&[]]), false),
            pattern_side(&complete(NoMatch, &[]), false),
            Distinguish,
        ),
        (
            // A binding set does not depend on witness order.
            "execution-pattern-pattern-outcome-bindings-agree",
            pattern(true),
            pattern_side(
                &complete(
                    Match,
                    &[&[("A", "a"), ("V", "v")], &[("A", "b"), ("V", "v")]],
                ),
                true,
            ),
            pattern_side(
                &complete(
                    Match,
                    &[&[("A", "b"), ("V", "v")], &[("A", "a"), ("V", "v")]],
                ),
                true,
            ),
            Agree,
        ),
        (
            "execution-pattern-pattern-outcome-bindings-distinguish",
            pattern(true),
            pattern_side(&complete(Match, &[&[("A", "a")]]), true),
            pattern_side(&complete(NoMatch, &[]), true),
            Distinguish,
        ),
        (
            "incomparable-baseline-normal",
            whole(),
            side(&whole(), &single(Normal, done.clone())),
            side(&whole(), &single(SemanticCrash, constant("crash"))),
            Incomparable,
        ),
        (
            "incomparable-baseline-crash",
            whole(),
            side(&whole(), &single(SemanticCrash, constant("crash"))),
            side(&whole(), &single(Normal, done.clone())),
            Incomparable,
        ),
    ];
    assert_eq!(rows.len(), 12);
    for (id, declaration, baseline, mutant, expected) in rows {
        for side in [&baseline, &mutant] {
            assert!(
                matches!(side, OracleSide::Normal(_) | OracleSide::SemanticCrash(_)),
                "{id}: {side:?} is complete evidence"
            );
        }
        assert_eq!(
            slot_outcome(&declaration, &baseline, &mutant),
            expected,
            "{id}"
        );
    }
}

/// E3: selected term paths are nonempty, sorted and prefix-free.
#[test]
fn e3_term_path_declarations_are_sorted_and_prefix_free() {
    let rows: [(&str, Vec<Vec<u32>>, bool); 7] = [
        ("one-path", vec![vec![0, 0]], true),
        ("sorted-siblings", vec![vec![0, 0], vec![1]], true),
        ("no-paths", Vec::new(), false),
        ("empty-path", vec![Vec::new()], false),
        ("unsorted", vec![vec![1], vec![0, 0]], false),
        ("duplicate", vec![vec![0], vec![0]], false),
        ("prefix-overlap", vec![vec![0], vec![0, 1]], false),
    ];
    for (id, paths, valid) in rows {
        let declared = OracleDeclaration::new(
            CompareIdentity,
            Projection::State(StateProjection::TermPaths(paths)),
        );
        match declared {
            Ok(declaration) => {
                assert!(valid, "{id}");
                assert_eq!(declaration.kind(), OracleKind::FinalResult, "{id}");
            }
            Err(failure) => {
                assert!(!valid, "{id}");
                assert_eq!(
                    failure.kind(),
                    OracleFailureKind::InvalidDeclaration,
                    "{id}"
                );
            }
        }
    }
}

/// `result` with every witness moved onto a path that stopped at `stop`.
fn witnessed_on(
    stop: PathStop,
    result: Result<Evaluation, PatternFailure>,
) -> Result<Evaluation, PatternFailure> {
    result.map(|mut evaluation| {
        for witness in &mut evaluation.witnesses {
            witness.stop_reason = stop;
            witness.execution_stop_reason = path(0, false, stop, None).execution_stop;
        }
        evaluation
    })
}

/// E4: only a match or a complete no-match is an operand, bindings only come from
/// complete exhaustive coverage (critique C5), and a match only from witnesses on real
/// prefixes (review P1).
#[test]
fn e4_operand_eligibility() {
    use PatternOutcome::{Error, Match, NoMatch, Unknown};
    use SearchPolicy::{Exhaustive, ExistentialFirst};
    let matched = |bindings| normal(OracleValue::Pattern(PatternValue::Match { bindings }));
    #[rustfmt::skip]
    let rows: [(&str, Result<Evaluation, PatternFailure>, bool, OracleSide); 14] = [
        ("unknown-evaluation-is-unknown", evaluation(Unknown, false, Exhaustive, &[]), false, OracleSide::Unknown),
        ("error-evaluation-is-error", evaluation(Error, false, Exhaustive, &[]), false, OracleSide::Error),
        ("pattern-failure-is-error", pattern_failure(), false, OracleSide::Error),
        ("complete-no-match", complete(NoMatch, &[]), true, normal(OracleValue::Pattern(PatternValue::NoMatch))),
        ("incomplete-match-without-bindings-is-a-match", evaluation(Match, false, Exhaustive, &[&[]]), false, matched(None)),
        ("complete-bindings", complete(Match, &[&[("A", "a")]]), true, matched(Some([vec![Binding { name: "A".to_owned(), term: constant("a") }]].into()))),
        // An explore-all collection has no exhaustion record.
        ("bindings-without-complete-coverage-are-unknown", evaluation(Match, false, Exhaustive, &[&[("A", "a")]]), true, OracleSide::Unknown),
        ("bindings-from-existential-first-are-unknown", evaluation(Match, true, ExistentialFirst, &[&[("A", "a")]]), true, OracleSide::Unknown),
        // `evaluate` never returns it; the side still refuses it.
        ("incomplete-no-match-is-unknown", evaluation(NoMatch, false, Exhaustive, &[]), false, OracleSide::Unknown),
        ("match-on-a-depth-limited-prefix-is-a-match", witnessed_on(PathStop::DepthLimit, evaluation(Match, false, Exhaustive, &[&[]])), false, matched(None)),
        // `evaluate` never returns these; the side still refuses them.
        ("match-without-witness-is-unknown", evaluation(Match, false, Exhaustive, &[]), false, OracleSide::Unknown),
        ("match-on-an-undecided-path-is-unknown", witnessed_on(PathStop::SolverUnknown, evaluation(Match, false, Exhaustive, &[&[]])), false, OracleSide::Unknown),
        ("match-on-a-diagnosed-run-is-unknown", witnessed_on(PathStop::BackendLimit, evaluation(Match, false, Exhaustive, &[&[]])), false, OracleSide::Unknown),
        ("bindings-on-an-errored-path-are-unknown", witnessed_on(PathStop::Error, complete(Match, &[&[("A", "a")]])), true, OracleSide::Unknown),
    ];
    for (id, evaluation, with_bindings, expected) in rows {
        assert_eq!(pattern_side(&evaluation, with_bindings), expected, "{id}");
    }

    // A match without bindings never meets one with them: the values are of different
    // shapes, and the slot is an error rather than a distinction.
    let without = matched(None);
    let with = matched(Some([Vec::new()].into()));
    for (baseline, mutant) in [(&without, &with), (&with, &without)] {
        assert_eq!(
            compare_supplied(
                OracleKind::ExecutionPattern,
                CompareIdentity,
                baseline,
                mutant
            )
            .expect_err("mismatched shapes")
            .kind(),
            OracleFailureKind::InvalidKindValue
        );
        assert_eq!(
            slot_outcome(&pattern(true), baseline, mutant),
            OracleOutcome::Error
        );
    }

    // The terminal class comes from the classified trace terminal, not from a label.
    let term = configuration("done", "1");
    assert_eq!(
        state_side(&exit_stop(None), &single(Stuck, term.clone())),
        normal(OracleValue::ExitStop(
            [ExitStop {
                class: TerminalClass::Stuck,
                code: None,
            }]
            .into()
        ))
    );
    assert_eq!(
        state_side(&exit_stop(None), &single(Normal, term)),
        normal(OracleValue::ExitStop(
            [ExitStop {
                class: TerminalClass::Normal,
                code: None,
            }]
            .into()
        ))
    );
}

#[test]
fn symbolic_binding_values_are_unknown() {
    use PatternOutcome::Match;

    let mut symbolic = witnessed_on(PathStop::Terminal, complete(Match, &[&[("A", "a")]]));
    let variable = Pattern::Variable(k_rust::kore::ast::Variable {
        kind: k_rust::kore::ast::VariableKind::Element,
        name: "X".to_owned(),
        sort: kore_sort("SortInt"),
    });
    symbolic.as_mut().expect("evaluation").witnesses[0].bindings[0].term = variable;
    assert_eq!(pattern_side(&symbolic, true), OracleSide::Unknown);
    assert_eq!(
        pattern_side(&symbolic, false),
        normal(OracleValue::Pattern(PatternValue::Match { bindings: None }))
    );

    let mut assumed = complete(Match, &[&[("A", "a")]]);
    assumed.as_mut().expect("evaluation").witnesses[0]
        .assumptions
        .push(kink_pattern::TermRelation {
            left: constant("a"),
            right: constant("a"),
        });
    assert_eq!(pattern_side(&assumed, true), OracleSide::Unknown);

    let ground_bindings = [vec![Binding {
        name: "A".to_owned(),
        term: constant("a"),
    }]]
    .into();
    assert_eq!(
        pattern_side(&complete(Match, &[&[("A", "a")]]), true),
        normal(OracleValue::Pattern(PatternValue::Match {
            bindings: Some(ground_bindings),
        }))
    );
}

/// An undefined step is its own exit-stop class. It has no exit code, so a declared exit-code cell
/// is not read. A mutant that makes a stuck or normal terminal an undefined step is
/// distinguished, and two undefined steps agree. The final result of an undefined step is its
/// last configuration, so a stuck baseline and an undefined mutant at the same term agree there.
#[test]
fn an_undefined_step_is_its_own_exit_stop_class() {
    let cell = "Lbl'-LT-'exit-code'-GT-'";
    let at = |program: &str| {
        app(
            "top",
            vec![
                app("k", vec![constant(program)]),
                kore_application(cell, Vec::new(), vec![int("7")]),
            ],
        )
    };
    let undefined = single(UndefinedStep, at("divide"));
    let class = |class, code| normal(OracleValue::ExitStop([ExitStop { class, code }].into()));
    for projection in [exit_stop(None), exit_stop(Some(cell))] {
        assert_eq!(
            state_side(&projection, &undefined),
            class(TerminalClass::UndefinedStep, None),
            "{projection:?}"
        );
    }
    let exit = state_side(&exit_stop(None), &undefined);
    #[rustfmt::skip]
    let rows = [
        ("stuck-baseline", state_side(&exit_stop(None), &single(Stuck, at("divide"))), Distinguish),
        ("normal-baseline", state_side(&exit_stop(None), &single(Normal, at("done"))), Distinguish),
        ("undefined-baseline", exit.clone(), Agree),
    ];
    for (id, baseline, expected) in rows {
        for policy in POLICIES {
            assert_eq!(
                compare_supplied(OracleKind::ExitStop, policy, &baseline, &exit),
                Ok(expected),
                "{id} under {policy:?}"
            );
        }
    }
    let whole = |kind| state_side(&StateProjection::WholeTerm, &single(kind, at("divide")));
    assert_eq!(
        compare_supplied(
            OracleKind::FinalResult,
            CompareIdentity,
            &whole(Stuck),
            &whole(UndefinedStep)
        ),
        Ok(Agree)
    );
}

/// A complete terminal term with a free variable stands for every instance of a symbolic run,
/// not for one value: no state projection reads it, whatever the terminal class.
#[test]
fn symbolic_terminal_terms_are_unknown_to_state_oracles() {
    let symbolic = app(
        "top",
        vec![
            app("k", vec![constant("done")]),
            app(
                "counter",
                vec![Pattern::Variable(k_rust::kore::ast::Variable {
                    kind: k_rust::kore::ast::VariableKind::Element,
                    name: "X".to_owned(),
                    sort: kore_sort("SortInt"),
                })],
            ),
        ],
    );
    for projection in [
        exit_stop(None),
        exit_stop(Some("counter")),
        StateProjection::WholeTerm,
        StateProjection::TermPaths(vec![vec![0, 0]]),
    ] {
        for kind in [Normal, Stuck, SemanticCrash, UndefinedStep] {
            assert_eq!(
                state_side(&projection, &single(kind, symbolic.clone())),
                OracleSide::Unknown,
                "{projection:?} {kind:?}"
            );
        }
    }
}

/// The side of a single leaf that halted with `halt`, as the bridge reads it: a stuck
/// leaf is a ground normal terminal, and a trivial leaf a ground undefined step.
fn halt_side(
    projection: &StateProjection,
    halt: HaltClass,
) -> Result<OracleSide, ExecutionFailureKind> {
    match halt_stop(halt) {
        Ok(Some(stop)) => Ok(state_side(projection, &run(vec![incomplete(0, stop)]))),
        Ok(None) => Ok(state_side(
            projection,
            &single(
                if halt == HaltClass::Trivial {
                    UndefinedStep
                } else {
                    Normal
                },
                configuration("done", "1"),
            ),
        )),
        Err(failure) => Err(ExecutionFailureKind::from(&failure)),
    }
}

fn mutant_status(run: TestRun) -> MutantStatus {
    let plan = MutantPlan {
        mutant_id: MutantId(0),
        tests: vec![TestPlan {
            test_id: "t".to_owned(),
            run,
        }],
        mutant_failure: None,
        claims: Withdrawal::default(),
    };
    let manifest = [ManifestTest {
        test_id: "t".to_owned(),
        slot_count: 1,
    }];
    derive_mutant_report(&plan, &manifest, ScheduleMode::Full)
        .expect("report")
        .status
}

/// E6: a failure never distinguishes. Leaf rows go through the bridge's halt mapping.
#[test]
fn e6_failures_never_distinguish() {
    enum Expected {
        Side(OracleSide, MutantStatus),
        Failed(ExecutionFailureKind, MutantStatus),
    }
    let cell = "Lbl'-LT-'exit-code'-GT-'";
    let with_code = |code: Pattern| {
        single(
            Normal,
            app(
                "top",
                vec![
                    app("k", vec![constant("done")]),
                    kore_application(cell, Vec::new(), vec![code]),
                ],
            ),
        )
    };
    let exit = exit_stop(Some(cell));
    let leaf = |halt| halt_side(&StateProjection::WholeTerm, halt).expect("a leaf side");
    let backend = ExecutionFailureKind::from(&ExecutionAdapterFailure::Backend("lost".to_owned()));
    #[rustfmt::skip]
    let rows: [(&str, Result<OracleSide, ExecutionFailureKind>, Expected); 6] = [
        ("cancelled-leaf-is-error", Ok(leaf(HaltClass::Cancelled)), Expected::Side(OracleSide::Error, MutantStatus::Error)),
        ("backend-error-is-infrastructure", Err(backend), Expected::Failed(ExecutionFailureKind::Infrastructure, MutantStatus::Error)),
        ("solver-indeterminate", Ok(leaf(HaltClass::Indeterminate)), Expected::Side(OracleSide::Unknown, MutantStatus::Unknown)),
        ("missing-output-bytes", Ok(state_side(&exit, &single(Normal, constant("done")))), Expected::Side(OracleSide::Error, MutantStatus::Error)),
        ("projection-invalid-utf8", Ok(state_side(&exit, &with_code(Pattern::DomainValue { sort: kore_sort("SortInt"), value: vec![0xff, 0xfe].into() }))), Expected::Side(OracleSide::Error, MutantStatus::Error)),
        ("non-int-exit-code", Ok(state_side(&exit, &with_code(Pattern::DomainValue { sort: kore_sort("SortString"), value: "0".into() }))), Expected::Side(OracleSide::Error, MutantStatus::Error)),
    ];
    let baseline = normal(OracleValue::FinalResult(FinalResult::WholeTerm(
        [configuration("done", "1")].into(),
    )));
    for (id, actual, expected) in rows {
        match (actual, expected) {
            (Ok(side), Expected::Side(expected, status)) => {
                assert_eq!(side, expected, "{id}");
                for policy in POLICIES {
                    let outcome =
                        compare_supplied(OracleKind::FinalResult, policy, &baseline, &side)
                            .expect("a failed side compares");
                    assert_ne!(outcome, Distinguish, "{id} under {policy:?}");
                    assert_eq!(
                        mutant_status(TestRun::Compared(vec![outcome])),
                        status,
                        "{id}"
                    );
                }
            }
            (Err(kind), Expected::Failed(expected, status)) => {
                assert_eq!(kind, expected, "{id}");
                assert_eq!(mutant_status(TestRun::Failed(kind)), status, "{id}");
            }
            (actual, _) => panic!("{id}: {actual:?}"),
        }
    }
    // The watchdog-fired run is `Failed(TimeLimit)` in the runner (end_to_end.rs).
    assert_eq!(
        mutant_status(TestRun::Compared(vec![Incomparable])),
        MutantStatus::Error,
        "an incomparable slot is an error"
    );
    // A well-formed exit code is a value.
    assert_eq!(
        state_side(&exit, &with_code(int("3"))),
        normal(OracleValue::ExitStop(
            [ExitStop {
                class: TerminalClass::Normal,
                code: Some(3),
            }]
            .into()
        ))
    );
}

/// Formerly `incomplete_normal_side_is_unknown_even_against_a_crash` (critique C6): a
/// bounded or indeterminate run is `Unknown` against any other side, including a crash
/// and under every crash policy, so a bounded baseline that might crash beyond its bound
/// never kills a crashing mutant.
#[test]
fn bounded_or_indeterminate_sides_are_unknown_even_against_a_crash() {
    let projection = StateProjection::WholeTerm;
    let done = configuration("done", "1");
    let mut bounded = [
        HaltClass::Vacuous,
        HaltClass::Indeterminate,
        HaltClass::UnsupportedHook,
        HaltClass::SimplificationError,
    ]
    .map(|halt| {
        (
            format!("{halt:?}"),
            run(vec![incomplete(
                0,
                halt_stop(halt).expect("mapped").expect("incomplete"),
            )]),
        )
    })
    .to_vec();
    bounded.extend([
        // A symbolic or constrained stuck leaf.
        (
            "symbolic-stuck".to_owned(),
            run(vec![incomplete(0, PathStop::SolverUnknown)]),
        ),
        // Complete leaves, but a backend diagnostic was collected.
        (
            "backend-diagnostic".to_owned(),
            BridgedPaths {
                paths: vec![terminal(0, Normal, done.clone())],
                collection: collection(CollectionStop::BackendLimit),
            },
        ),
        // A crash beside an unfinished branch.
        (
            "crash-beside-a-bounded-branch".to_owned(),
            run(vec![
                terminal(0, SemanticCrash, constant("crash")),
                incomplete(1, PathStop::DepthLimit),
            ]),
        ),
    ]);
    let crash = state_side(&projection, &single(SemanticCrash, constant("crash")));
    let complete = state_side(&projection, &single(Normal, done));
    for (id, bridged) in bounded {
        let side = state_side(&projection, &bridged);
        assert_eq!(side, OracleSide::Unknown, "{id}");
        #[rustfmt::skip]
        let rows = [
            ("bounded-baseline-against-crash", &side, &crash),
            ("crash-against-bounded-mutant", &crash, &side),
            ("bounded-baseline-against-complete", &side, &complete),
            ("complete-against-bounded-mutant", &complete, &side),
        ];
        for (row, baseline, mutant) in rows {
            for policy in POLICIES {
                assert_eq!(
                    compare_supplied(OracleKind::FinalResult, policy, baseline, mutant)
                        .expect("bounded evidence always compares"),
                    OracleOutcome::Unknown,
                    "{id} {row} under {policy:?}"
                );
            }
        }
    }
}

fn exhaustive_adapter_failure(failure: &ExecutionAdapterFailure) {
    // Fails to compile when a variant is added without a row.
    match failure {
        ExecutionAdapterFailure::SolverProfileMismatch
        | ExecutionAdapterFailure::InvalidState(_)
        | ExecutionAdapterFailure::Backend(_)
        | ExecutionAdapterFailure::ContractViolation(_)
        | ExecutionAdapterFailure::UninhabitedVariable(_) => {}
    }
}

fn exhaustive_bridge_failure(failure: &BridgeFailure) {
    match failure {
        BridgeFailure::NoLeaves
        | BridgeFailure::ContractViolation(_)
        | BridgeFailure::UndecodableState(_)
        | BridgeFailure::UndecidedStateSort
        | BridgeFailure::DuplicatePathIdentity(_)
        | BridgeFailure::ClassifiedUndefinedStep => {}
    }
}

/// Complete paths are a state value only when PathSet ran out of work.
/// An unrecorded stop does not certify a complete state value.

#[test]
fn state_values_need_a_collection_that_ran_out_of_work() {
    use CollectionStop::{ExhaustionUnrecorded, SearchExhausted};
    let done = configuration("done", "1");
    let value = normal(OracleValue::FinalResult(FinalResult::WholeTerm(
        [done.clone()].into_iter().collect(),
    )));
    #[rustfmt::skip]
    let rows = [
        ("exhausted", SearchExhausted, value.clone()),
        ("unrecorded", ExhaustionUnrecorded, OracleSide::Unknown),
    ];
    for (id, stop, expected) in rows {
        let bridged = BridgedPaths {
            paths: vec![terminal(0, Normal, done.clone())],
            collection: collection(stop),
        };
        assert_eq!(
            state_side(&StateProjection::WholeTerm, &bridged),
            expected,
            "{id}"
        );
    }
}

/// One row per `HaltClass`, `ExecutionAdapterFailure`, `BridgeFailure`,
/// `MutantRejection` and `PatternOutcome` variant, plus the terminal-set shapes and the
/// comparison failures.
#[test]
fn runner_mapping_is_exhaustive() {
    use HaltClass as H;
    let whole = StateProjection::WholeTerm;
    let done = configuration("done", "1");
    let value = |terms: &[Pattern]| {
        normal(OracleValue::FinalResult(FinalResult::WholeTerm(
            terms.iter().cloned().collect(),
        )))
    };
    let infrastructure = Err(ExecutionFailureKind::Infrastructure);
    #[rustfmt::skip]
    let halts: [(HaltClass, Result<OracleSide, ExecutionFailureKind>); 13] = [
        (H::Stuck, Ok(value(std::slice::from_ref(&done)))),
        // An undefined step's final result is its last configuration.
        (H::Trivial, Ok(value(std::slice::from_ref(&done)))),
        (H::Vacuous, Ok(OracleSide::Unknown)),
        (H::Branch, infrastructure.clone()),
        (H::CutPoint, infrastructure.clone()),
        (H::TerminalRule, infrastructure.clone()),
        // Requested bounds are incomplete paths; the adapter rejects an unrequested one first.
        (H::DepthBound, Ok(OracleSide::Unknown)),
        (H::BreadthBound, Ok(OracleSide::Unknown)),
        (H::Indeterminate, Ok(OracleSide::Unknown)),
        (H::UnsupportedHook, Ok(OracleSide::Unknown)),
        (H::SimplificationError, Ok(OracleSide::Unknown)),
        (H::Timeout, infrastructure.clone()),
        // Until upstream tells cancellation from timeout.
        (H::Cancelled, Ok(OracleSide::Error)),
    ];
    assert_eq!(
        halts.iter().map(|(halt, _)| *halt).collect::<Vec<_>>(),
        HaltClass::ALL
    );
    for (halt, expected) in halts {
        assert_eq!(halt_side(&whole, halt), expected, "{halt:?}");
    }

    // Terminal sets.
    let crash = constant("crash");
    #[rustfmt::skip]
    let shapes = [
        ("single-crash-is-its-terminal-term", single(SemanticCrash, crash.clone()), OracleSide::SemanticCrash(crash.clone())),
        ("crash-among-terminals-is-unknown", run(vec![terminal(0, Normal, done.clone()), terminal(1, SemanticCrash, crash.clone())]), OracleSide::Unknown),
        ("explore-all-final-states", BridgedPaths { paths: vec![terminal(0, Normal, done.clone()), terminal(1, Normal, configuration("done", "2"))], collection: collection(CollectionStop::SearchExhausted) }, value(&[done.clone(), configuration("done", "2")])),
        ("error-over-timeout", run(vec![incomplete(0, PathStop::TimeLimit), incomplete(1, PathStop::Error)]), OracleSide::Error),
        ("timeout-over-unknown", run(vec![incomplete(0, PathStop::DepthLimit), incomplete(1, PathStop::TimeLimit)]), OracleSide::Timeout),
        ("no-paths-is-error", run(Vec::new()), OracleSide::Error),
        ("complete-path-without-terminal-is-error", run(vec![path(0, true, PathStop::Terminal, None)]), OracleSide::Error),
        ("missing-term-path-is-error", single(Normal, constant("done")), OracleSide::Error),
    ];
    for (id, bridged, expected) in shapes {
        let projection = if id == "missing-term-path-is-error" {
            StateProjection::TermPaths(vec![vec![0, 0]])
        } else {
            whole.clone()
        };
        assert_eq!(state_side(&projection, &bridged), expected, "{id}");
    }

    // Adapter and bridge failures produce no operand.
    let adapter = [
        ExecutionAdapterFailure::SolverProfileMismatch,
        ExecutionAdapterFailure::InvalidState(String::new()),
        ExecutionAdapterFailure::Backend(String::new()),
        ExecutionAdapterFailure::ContractViolation(H::Branch),
        ExecutionAdapterFailure::UninhabitedVariable(k_rust::kore::ast::Variable {
            kind: k_rust::kore::ast::VariableKind::Element,
            name: "VarX".to_owned(),
            sort: kore_sort("SortEmpty"),
        }),
    ];
    for failure in &adapter {
        exhaustive_adapter_failure(failure);
        assert_eq!(
            ExecutionFailureKind::from(failure),
            ExecutionFailureKind::Infrastructure,
            "{failure:?}"
        );
    }
    let bridge = [
        BridgeFailure::NoLeaves,
        BridgeFailure::ContractViolation(H::CutPoint),
        BridgeFailure::UndecodableState(String::new()),
        BridgeFailure::UndecidedStateSort,
        BridgeFailure::DuplicatePathIdentity("root".to_owned()),
    ];
    for failure in &bridge {
        exhaustive_bridge_failure(failure);
        assert_eq!(
            ExecutionFailureKind::from(failure),
            ExecutionFailureKind::Infrastructure,
            "{failure:?}"
        );
    }

    // A rejected mutant is invalid and never runs.
    let counter = support::load("counter.k");
    let at = TermRef::new(support::rule(&counter, "COUNTER.increment"), [0, 1, 0]);
    let stale = Patch::new(vec![Edit::ReplaceTerm {
        expected: counter
            .term(&TermRef::new(at.sentence.clone(), [0, 0]))
            .expect("lhs")
            .clone(),
        replacement: counter
            .term(&TermRef::new(at.sentence.clone(), [0, 1, 0, 0]))
            .expect("cast argument")
            .clone(),
        at,
    }])
    .expect("one edit");
    let patch_failure = apply(&counter, &stale).expect_err("the precondition is stale");
    assert_eq!(patch_failure.kind(), PatchFailureKind::StalePrecondition);
    // New row (VI-03F): a loaded-stage relink refusal is Rejected / Invalid.
    let rejections = [
        MutantRejection::Relink(k_rust::outer::LoadError::MissingSyntaxModule(
            "missing".into(),
        )),
        MutantRejection::Patch(patch_failure),
        MutantRejection::Compilation(CompileError {
            stage: "definition checks",
            message: String::new(),
            diagnostics: Vec::new(),
        }),
    ];
    for rejection in &rejections {
        let failure = MutantScopeFailure::from(rejection);
        assert_eq!(failure, MutantScopeFailure::Rejected, "{rejection:?}");
        assert_eq!(failure.status(), MutantStatus::Invalid, "{rejection:?}");
    }

    // Pattern outcomes.
    #[rustfmt::skip]
    let outcomes = [
        (PatternOutcome::Match, normal(OracleValue::Pattern(PatternValue::Match { bindings: None }))),
        (PatternOutcome::NoMatch, normal(OracleValue::Pattern(PatternValue::NoMatch))),
        (PatternOutcome::Unknown, OracleSide::Unknown),
        (PatternOutcome::Error, OracleSide::Error),
    ];
    for (outcome, expected) in outcomes {
        let evaluation = complete(outcome, &[&[]]);
        assert_eq!(pattern_side(&evaluation, false), expected, "{outcome:?}");
    }

    // A comparison failure is an error slot, never a dropped one.
    let crash_side = OracleSide::SemanticCrash(crash);
    let complete_side = value(&[configuration("done", "1")]);
    let reject = declaration(Reject, Projection::State(StateProjection::WholeTerm));
    #[rustfmt::skip]
    let failures = [
        ("crash-rejected-by-policy", &reject, &complete_side, &crash_side),
        ("value-of-another-kind", &state(exit_stop(None)), &complete_side, &complete_side),
        ("empty-value", &state(StateProjection::WholeTerm), &complete_side, &value(&[])),
    ];
    for (id, declaration, baseline, mutant) in failures {
        assert!(
            compare_supplied(
                declaration.kind(),
                declaration.crash_policy(),
                baseline,
                mutant
            )
            .is_err(),
            "{id}"
        );
        assert_eq!(
            slot_outcome(declaration, baseline, mutant),
            OracleOutcome::Error,
            "{id}"
        );
    }
}

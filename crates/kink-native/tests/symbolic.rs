//! Live symbolic memory observations and path-level acceptance checks.

#[path = "../../../testdata/k/support.rs"]
mod support;

#[path = "../../../testdata/k/step_support.rs"]
mod step_support;

use std::{num::NonZeroUsize, time::Duration};

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::kore_sort;
use k_rust::kore::{ast::Pattern, codec, parser::parse_definition, walk::for_each_post_order};
use k_rust_backend::rule::Predicate;
use k_rust_backend::smt::{
    Exactness, NoSolver, Satisfiability, SmtError, SmtSolver, Validity, translation_exactness,
};
use k_rust_backend::stop::{Stop, Stoppable};
use k_rust_backend::substitution::Substitution;
use kink_native::bridge::{BridgeContext, BridgedPaths, paths_from_execution, paths_from_steps};
use kink_native::execution::{
    AdaptedExecution, AdaptedLeaf, ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile,
};
use kink_native::feasibility::{BackendRelations, LeafFeasibility};
use kink_native::report::{ReportInput, ReportResult, step3_report};
use kink_native::step_events::{ObservationDecider, StepEventSpec, StepObservation};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_pattern::{
    Atom, CollectionStop, Evaluation, EvaluationContext, EvaluationOptions, EventVocabulary,
    ExecutionTerminalKind, MatchMode, PathInput, PathStop, PatternArm, PatternOutcome, PatternPlan,
    PayloadClause, Relation, SearchPolicy, SymbolSorts, TermRelation, evaluate, evaluate_with,
};

/// The profile of this build (README section 9): the `z3` feature of kink-native.
const PROFILE: SolverProfile = SolverProfile::BUILD;

/// Selects the expected value of a profile table: `(no_z3, z3)` columns (README R8).
fn by_profile<T>(no_z3: T, z3: T) -> T {
    if cfg!(feature = "z3") { z3 } else { no_z3 }
}

/// SMT options for every backend in this file. k-rust's default 125 ms timeout makes a Z3
/// `unknown` depend on load (README R4); 4 s doubled twice (up to 28 s per query) keeps the
/// small fixture queries decided. A no-Z3 backend ignores them.
const BACKEND_OPTIONS: BackendOptions = BackendOptions {
    smt_timeout_ms: 4000,
    smt_retry_limit: 2,
};

fn backend(kore: &str, module: &str) -> Backend {
    Backend::new(kore, module, BACKEND_OPTIONS).expect("backend")
}

fn adapter() -> ExecutionAdapter {
    ExecutionAdapter::with_profile(PROFILE)
}

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
};

fn nat(name: &str) -> Pattern {
    support::var(name, "SortNat")
}
fn integer(name: &str) -> Pattern {
    support::var(name, "SortInt")
}
fn z() -> Pattern {
    support::app("Lblz", vec![])
}
fn s(value: Pattern) -> Pattern {
    support::app("Lbls", vec![value])
}
fn addr(value: Pattern) -> Pattern {
    support::app("Lbladdr", vec![value])
}
fn write(address: Pattern, value: Pattern) -> Pattern {
    support::app("Lblwrite", vec![address, value])
}
fn load(address: Pattern, value: Pattern) -> Pattern {
    support::app("Lblload", vec![address, value])
}
fn load_neg(address: Pattern, value: Pattern) -> Pattern {
    support::app("LblloadNeg", vec![address, value])
}
fn free(address: Pattern) -> Pattern {
    support::app("Lblfree", vec![address])
}
fn halt() -> Pattern {
    support::app("Lblhalt", vec![])
}
fn seq(operation: Pattern, rest: Pattern) -> Pattern {
    support::app("Lblseq", vec![operation, rest])
}
fn fork(left: Pattern, right: Pattern) -> Pattern {
    support::app("Lblfork", vec![left, right])
}

fn p1() -> Pattern {
    seq(
        write(addr(nat("X")), nat("V")),
        seq(load(addr(nat("X")), nat("W")), halt()),
    )
}
fn p2() -> Pattern {
    seq(
        write(addr(nat("X")), nat("V")),
        seq(free(addr(z())), seq(load(addr(nat("X")), nat("W")), halt())),
    )
}
fn p3() -> Pattern {
    seq(
        load(addr(nat("X")), nat("W")),
        seq(write(addr(nat("X")), nat("V")), halt()),
    )
}
fn p4() -> Pattern {
    fork(
        seq(write(addr(nat("X")), nat("V")), halt()),
        seq(load(addr(nat("X")), nat("W")), halt()),
    )
}
fn p5() -> Pattern {
    fork(p1(), seq(load(addr(nat("X")), nat("W")), halt()))
}
fn p6() -> Pattern {
    seq(
        write(addr(nat("X")), nat("V")),
        seq(load(addr(nat("Y")), nat("W")), halt()),
    )
}
fn p7() -> Pattern {
    seq(
        write(addr(z()), nat("V")),
        seq(load(addr(s(nat("Y"))), nat("W")), halt()),
    )
}
fn p8() -> Pattern {
    p1()
}
fn p9() -> Pattern {
    fork(
        p1(),
        seq(
            write(addr(nat("Y")), nat("V")),
            seq(load(addr(nat("Y")), nat("W")), halt()),
        ),
    )
}

fn g1() -> Pattern {
    seq(
        write(addr(integer("X")), integer("V")),
        seq(load(addr(integer("Y")), integer("W")), halt()),
    )
}
fn g2() -> Pattern {
    seq(
        write(addr(integer("X")), integer("V")),
        seq(load_neg(addr(integer("Y")), integer("W")), halt()),
    )
}
fn g3() -> Pattern {
    seq(
        write(addr(support::int(1)), integer("V")),
        seq(load(addr(support::int(1)), integer("W")), halt()),
    )
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Fixture {
    Sym,
    Guard,
    /// `symwrap.k`: symmem's write/load over an `anywhere`-collapsed address constructor.
    Wrap,
    /// `symowise.k`: an `owise` rule that no value of its symbolic subject reaches.
    Owise,
    /// `symensures.k`: an `ensures` that constrains payload variables after their events.
    Ensures,
    /// `symbottom.k`: guardedmem's unguarded write/load plus rules whose `ensures` leaves a
    /// state without successor (SYM-3B-02).
    Bottom,
    /// `symnarrow.k`: rules whose applicability to a symbolic `Int` depends on its value
    /// without a `requires`, and a `requires` over the uninterpreted `&Int` (SYM-3B-05).
    Narrow,
    /// `sympartial.k`: a `requires` over a partial function whose definedness k-rust 347f693e
    /// dropped (SYM-3B-05, README R18).
    Partial,
    /// A guarded partial right-hand side after write and load events.
    Division,
}

impl Fixture {
    fn name(self) -> &'static str {
        match self {
            Self::Sym => "symmem.k",
            Self::Guard => "guardedmem.k",
            Self::Wrap => "symwrap.k",
            Self::Owise => "symowise.k",
            Self::Ensures => "symensures.k",
            Self::Bottom => "symbottom.k",
            Self::Narrow => "symnarrow.k",
            Self::Partial => "sympartial.k",
            Self::Division => "guardeddiv.k",
        }
    }
    fn module(self) -> &'static str {
        match self {
            Self::Sym => "SYMMEM",
            Self::Guard => "GUARDEDMEM",
            Self::Wrap => "SYMWRAP",
            Self::Owise => "SYMOWISE",
            Self::Ensures => "SYMENSURES",
            Self::Bottom => "SYMBOTTOM",
            Self::Narrow => "SYMNARROW",
            Self::Partial => "SYMPARTIAL",
            Self::Division => "GUARDEDDIV",
        }
    }
}

struct Run {
    execution: AdaptedExecution,
    bridged: BridgedPaths,
    report_bridged: BridgedPaths,
    context: EvaluationContext,
    backend: Backend,
    state: Pattern,
}

fn observations(fixture: Fixture) -> Vec<StepEventSpec> {
    match fixture {
        Fixture::Sym => step_support::symmem(true),
        Fixture::Wrap | Fixture::Owise | Fixture::Ensures => {
            step_support::symmem(true).into_iter().take(2).collect()
        }
        Fixture::Guard => step_support::guardedmem(true),
        Fixture::Bottom | Fixture::Narrow | Fixture::Partial | Fixture::Division => {
            step_support::int_memory(true)
        }
    }
}

fn run_side(
    side: &ValidatedDefinition,
    fixture: Fixture,
    state: Pattern,
    budget: ExecutionBudget,
) -> (Run, EventVocabulary) {
    let mut backend = backend(&side.artifacts().definition_kore, fixture.module());
    let observation =
        StepObservation::new(&mut backend, observations(fixture)).expect("declarations validate");
    let vocabulary = observation.vocabulary().clone();
    let stepped = adapter()
        .execute_steps(&mut backend, &state, budget)
        .expect("execution adapts")
        .expect("steps decode");
    let sorts = SymbolSorts::from_definition(
        &parse_definition(&side.artifacts().definition_kore).expect("compiled KORE parses"),
    );
    let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
    let bridged = backend
        .with_solver(None, |definition, solver| {
            let decider = ObservationDecider::new(definition, solver, &state);
            Ok::<_, k_rust::backend::BackendError>(paths_from_steps(
                &BridgeContext {
                    test_id: "symbolic",
                    classify: &normal,
                    sorts: &sorts,
                },
                &stepped,
                &observation,
                &decider,
            ))
        })
        .expect("backend definition")
        .expect("execution bridges");
    let report_bridged = paths_from_execution(
        &stepped.adapted,
        &BridgeContext {
            test_id: "symbolic",
            classify: &normal,
            sorts: &sorts,
        },
    )
    .expect("state-slot bridge");
    (
        Run {
            execution: stepped.adapted,
            bridged,
            report_bridged,
            context: EvaluationContext {
                test_id: "symbolic".into(),
                bounds: budget.bounds(),
                vocabulary: vocabulary.clone(),
                symbol_sorts: sorts,
            },
            backend,
            state,
        },
        vocabulary,
    )
}

fn run(fixture: Fixture, program: Pattern, budget: ExecutionBudget) -> (Run, EventVocabulary) {
    run_state(fixture, support::initial_state(program, "SortProg"), budget)
}

/// `run` from an initial state that may carry a path condition.
fn run_state(fixture: Fixture, state: Pattern, budget: ExecutionBudget) -> (Run, EventVocabulary) {
    let validator = NativeValidator::bind(support::load(fixture.name()), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    run_side(&side, fixture, state, budget)
}

/// Stepped and unobserved execution keep identical leaves in backend order, including halt,
/// state, depth, trace, cause and diagnostics.
#[test]
fn observation_erasure_preserves_live_leaves() {
    let depth = ExecutionBudget {
        max_depth: Some(1),
        ..BUDGET
    };
    let breadth = ExecutionBudget {
        max_breadth: Some(NonZeroUsize::new(1).expect("nonzero")),
        ..BUDGET
    };
    let rows = [
        (
            "nd.k",
            "ND",
            "SortS",
            vec![
                ("start", support::app("Lblstart", vec![]), BUDGET),
                ("start-depth", support::app("Lblstart", vec![]), depth),
                ("start-breadth", support::app("Lblstart", vec![]), breadth),
            ],
        ),
        (
            "symmem.k",
            "SYMMEM",
            "SortProg",
            vec![
                ("P1", p1(), BUDGET),
                ("P2", p2(), BUDGET),
                ("P3", p3(), BUDGET),
                ("P4", p4(), BUDGET),
                ("P5", p5(), BUDGET),
                ("P6", p6(), BUDGET),
                ("P7", p7(), BUDGET),
                ("P8", p8(), depth),
                ("P9", p9(), breadth),
            ],
        ),
        (
            "guardedmem.k",
            "GUARDEDMEM",
            "SortProg",
            vec![
                ("G1", g1(), BUDGET),
                ("G2", g2(), BUDGET),
                ("G3", g3(), BUDGET),
            ],
        ),
    ];
    for (fixture, module, sort, programs) in rows {
        let validator = NativeValidator::bind(support::load(fixture), CompileOptions::default());
        let side = validator.compile_baseline().expect("fixture compiles");
        let adapter = adapter();
        let mut backend = backend(&side.artifacts().definition_kore, module);
        for (row, program, budget) in programs {
            let state = support::initial_state(program, sort);
            let stepped = adapter
                .execute_steps(&mut backend, &state, budget)
                .expect("observed execution")
                .expect("steps decode");
            let observed = &stepped.adapted;
            assert!(!observed.timed_out(), "{fixture} {row}: observed timeout");
            let unobserved = adapter
                .execute_unobserved(&mut backend, &state, budget)
                .expect("unobserved execution");
            let mut erased = observed.erased();
            for leaf in &mut erased {
                leaf.branch.clear();
            }
            assert!(!erased.is_empty(), "{fixture} {row}: no leaves");
            assert_eq!(erased, unobserved, "{fixture} {row}: observation erasure");
            assert!(
                observed
                    .erased()
                    .iter()
                    .all(|leaf| (leaf.depth == 0) == leaf.branch.is_empty()),
                "{fixture} {row}: exactly the leaves below the root have an identity"
            );
        }
    }
}

fn wl(vocabulary: &EventVocabulary, sort: &str, relation: Relation) -> PatternPlan {
    PatternPlan::new(
        vocabulary,
        vec![("A".into(), kore_sort(sort))],
        vec![PatternArm {
            atoms: vec![
                Atom {
                    constructor: "memoryWrite".into(),
                    payload: vec![PayloadClause {
                        position: 0,
                        mode: MatchMode::Bind,
                        variable: "A".into(),
                    }],
                },
                Atom {
                    constructor: "memoryLoad".into(),
                    payload: vec![PayloadClause {
                        position: 0,
                        mode: MatchMode::Use,
                        variable: "A".into(),
                    }],
                },
            ],
            relations: vec![relation],
        }],
        None,
    )
    .expect("plan")
}

fn wl_next(vocabulary: &EventVocabulary) -> PatternPlan {
    wl(vocabulary, "SortAddress", Relation::NextEvent)
}
fn wl_after(vocabulary: &EventVocabulary) -> PatternPlan {
    wl(vocabulary, "SortAddress", Relation::EventuallyAfter)
}
fn gwl_after(vocabulary: &EventVocabulary) -> PatternPlan {
    wl(vocabulary, "SortInt", Relation::EventuallyAfter)
}
fn w_only(vocabulary: &EventVocabulary) -> PatternPlan {
    PatternPlan::new(
        vocabulary,
        vec![("A".into(), kore_sort("SortAddress"))],
        vec![PatternArm {
            atoms: vec![Atom {
                constructor: "memoryWrite".into(),
                payload: vec![PayloadClause {
                    position: 0,
                    mode: MatchMode::Bind,
                    variable: "A".into(),
                }],
            }],
            relations: vec![],
        }],
        None,
    )
    .expect("plan")
}

fn outcome(run: &Run, plan: &PatternPlan) -> Evaluation {
    evaluate(
        &run.context,
        plan,
        &run.bridged.paths,
        &run.bridged.collection,
        None,
        EvaluationOptions {
            stable_path_keys: true,
            search_policy: SearchPolicy::Exhaustive,
            input_error: false,
        },
    )
    .expect("evaluation")
}

/// `outcome` with the observation decider built from the fixture's baseline.
fn decided(run: &mut Run, plan: &PatternPlan) -> Evaluation {
    run.backend
        .with_solver(None, |definition, solver| {
            let decider = BackendRelations::shared(definition, solver, &run.state);
            Ok::<_, k_rust::backend::BackendError>(evaluate_with(
                &run.context,
                plan,
                &run.bridged.paths,
                &run.bridged.collection,
                None,
                EvaluationOptions {
                    stable_path_keys: true,
                    search_policy: SearchPolicy::Exhaustive,
                    input_error: false,
                },
                &decider,
            ))
        })
        .expect("backend definition")
        .expect("evaluation")
}

#[test]
fn symmem_step_payloads_are_subject_terms() {
    let (run, _) = run(Fixture::Sym, p1(), BUDGET);
    assert_eq!(run.bridged.collection.stop, CollectionStop::SearchExhausted);
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert!(path.complete);
    assert_eq!(
        path.execution_terminal.as_ref().expect("terminal").state,
        support::initial_state(halt(), "SortProg")
    );
    assert_eq!(path.events.len(), 2);
    assert_eq!(path.events[0].constructor, "memoryWrite");
    assert_eq!(path.events[1].constructor, "memoryLoad");
    assert_eq!(path.events[0].payload, [addr(nat("X")), nat("V")]);
    assert_eq!(path.events[1].payload, [addr(nat("X")), nat("W")]);
}

#[test]
fn symmem_fork_keeps_siblings_apart() {
    let (run, _) = run(Fixture::Sym, p4(), BUDGET);
    assert_eq!(run.bridged.collection.stop, CollectionStop::SearchExhausted);
    let [left, right] = run.bridged.paths.as_slice() else {
        panic!("two paths")
    };
    assert!(left.complete && right.complete);
    assert_ne!(left.path_key, right.path_key);
    let constructors: Vec<_> = run
        .bridged
        .paths
        .iter()
        .map(|path| {
            path.events
                .iter()
                .map(|event| event.constructor.as_str())
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(constructors.contains(&vec!["memoryWrite"]));
    assert!(constructors.contains(&vec!["memoryLoad"]));
}

/// No-Z3 only: the Z3 build's G1/G2 values are rows of `profile_table_rows`. The one leaf is
/// `Indeterminate` at the first `requires`, which needs the solver this build lacks; its cause
/// says so, and the path is `SolverUnknown` (`BackendLimit` before k-rust exposed the cause,
/// KK-56/KK-57).
#[cfg(not(feature = "z3"))]
#[test]
fn solver_dependent_guard_is_unknown_without_z3() {
    let validator = NativeValidator::bind(support::load("guardedmem.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    let backend = backend(&side.artifacts().definition_kore, "GUARDEDMEM");
    assert!(!backend.capabilities().smt);
    for program in [g1(), g2()] {
        let (run, vocabulary) = run(Fixture::Guard, program, BUDGET);
        assert_eq!(
            run.execution
                .leaves()
                .iter()
                .map(|leaf| leaf.halt)
                .collect::<Vec<_>>(),
            [HaltClass::Indeterminate]
        );
        assert!(
            run.execution
                .leaves()
                .iter()
                .all(|leaf| leaf.cause.as_ref().is_some_and(|cause| matches!(
                    cause,
                    k_rust::backend::SearchFailureOutput::Requires { .. }
                ) && cause
                    .solver_unavailable()))
        );
        assert!(
            run.bridged
                .paths
                .iter()
                .all(|path| path.stop == PathStop::SolverUnknown)
        );
        let evaluation = outcome(&run, &gwl_after(&vocabulary));
        assert_eq!(evaluation.outcome, PatternOutcome::Unknown);
        assert_eq!(evaluation.failure, Some(PathStop::SolverUnknown));
    }
}

#[test]
fn ground_guard_is_decided_without_z3() {
    let (run, vocabulary) = run(Fixture::Guard, g3(), BUDGET);
    assert_eq!(
        run.execution
            .leaves()
            .iter()
            .map(|leaf| leaf.halt)
            .collect::<Vec<_>>(),
        [HaltClass::Stuck]
    );
    assert_eq!(run.bridged.collection.stop, CollectionStop::SearchExhausted);
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert!(path.complete);
    assert_eq!(
        outcome(&run, &gwl_after(&vocabulary)).outcome,
        PatternOutcome::Match
    );
}

#[test]
fn z3_shared_int_address_witness_carries_feasible_constraint() {
    let (mut run, vocabulary) = run(Fixture::Guard, g1(), BUDGET);
    let plan = gwl_after(&vocabulary);
    let stops: Vec<_> = run.bridged.paths.iter().map(|path| path.stop).collect();
    assert_eq!(
        stops,
        by_profile(vec![PathStop::SolverUnknown], vec![PathStop::Terminal; 3])
    );
    let plain = outcome(&run, &plan);
    assert_eq!(
        (plain.outcome, plain.failure),
        by_profile(
            (PatternOutcome::Unknown, Some(PathStop::SolverUnknown)),
            (PatternOutcome::Unknown, Some(PathStop::SolverUnknown))
        )
    );

    let evaluation = decided(&mut run, &plan);
    assert_eq!(
        (evaluation.outcome, evaluation.failure),
        by_profile(
            (PatternOutcome::Unknown, Some(PathStop::SolverUnknown)),
            (PatternOutcome::Match, None)
        )
    );
    assert_witness_paths(&run, &evaluation);
    if cfg!(feature = "z3") {
        assert!(evaluation.complete_coverage);
        assert_eq!(evaluation.primary_witness, Some(0));
        let [witness] = evaluation.witnesses.as_slice() else {
            panic!("one G1 witness: {evaluation:?}")
        };
        // README 6.4 puts the empty and write-only traces before this two-event trace.
        assert_eq!(witness.path_ordinal, 2);
        assert_eq!(witness.event_indices, [0, 1]);
        assert_eq!(witness.stop_reason, PathStop::Terminal);
        assert_eq!(witness.bindings.len(), 1);
        assert_eq!(witness.bindings[0].name, "A");
        assert_eq!(witness.bindings[0].term, integer("X"));
        assert_eq!(
            witness.assumptions,
            [TermRelation {
                left: integer("X"),
                right: integer("Y"),
            }]
        );
        let mut guarded_variables = Vec::new();
        for_each_post_order(&witness.path_predicate, |node| {
            if let Pattern::Application { symbol, arguments } = node
                && symbol.name == "Lbl'Unds-GT-Eqls'Int'Unds'"
            {
                assert_eq!(arguments.len(), 2);
                assert_eq!(arguments[1], support::int(0));
                guarded_variables.push(arguments[0].clone());
            }
        });
        assert_eq!(guarded_variables.len(), 2);
        assert!(guarded_variables.contains(&integer("X")));
        assert!(guarded_variables.contains(&integer("Y")));

        let report = step3_report(ReportInput {
            profile: PROFILE,
            test_id: "G1-GWL-after",
            budget: &BUDGET,
            backend_options: BACKEND_OPTIONS,
            result: ReportResult::Ok {
                execution: &run.execution,
                bridged: &run.report_bridged,
                evaluation: &evaluation,
            },
        });
        assert_eq!(report["profile"], "z3");
        assert_eq!(report["witnesses"].as_array().map(Vec::len), Some(1));
        assert_eq!(
            report["witnesses"][0]["assumptions"],
            serde_json::json!([{
                "left": codec::to_value(&integer("X")).expect("X encodes"),
                "right": codec::to_value(&integer("Y")).expect("Y encodes"),
            }])
        );
    } else {
        assert!(!evaluation.complete_coverage);
        assert_eq!(evaluation.primary_witness, None);
        assert!(evaluation.witnesses.is_empty());
    }
}

#[test]
fn z3_infeasible_shared_address_is_no_match() {
    let (mut run, vocabulary) = run(Fixture::Guard, g2(), BUDGET);
    let plan = gwl_after(&vocabulary);
    let stops: Vec<_> = run.bridged.paths.iter().map(|path| path.stop).collect();
    assert_eq!(
        stops,
        by_profile(vec![PathStop::SolverUnknown], vec![PathStop::Terminal; 3])
    );
    let plain = outcome(&run, &plan);
    assert_eq!(
        (plain.outcome, plain.failure),
        by_profile(
            (PatternOutcome::Unknown, Some(PathStop::SolverUnknown)),
            (PatternOutcome::Unknown, Some(PathStop::SolverUnknown))
        )
    );
    let evaluation = decided(&mut run, &plan);
    assert_eq!(
        (evaluation.outcome, evaluation.failure),
        by_profile(
            (PatternOutcome::Unknown, Some(PathStop::SolverUnknown)),
            (PatternOutcome::NoMatch, None)
        )
    );
    assert_eq!(evaluation.complete_coverage, cfg!(feature = "z3"));
    assert_eq!(evaluation.primary_witness, None);
    assert!(evaluation.witnesses.is_empty());
    assert_witness_paths(&run, &evaluation);
}

fn assert_both(
    run: &mut Run,
    plan: &PatternPlan,
    expected: PatternOutcome,
    failure: Option<PathStop>,
) -> Evaluation {
    let plain = outcome(run, plan);
    assert_eq!((plain.outcome, plain.failure), (expected, failure));
    let evaluation = decided(run, plan);
    assert_eq!(
        (evaluation.outcome, evaluation.failure),
        (expected, failure)
    );
    assert_witness_paths(run, &evaluation);
    for witness in &evaluation.witnesses {
        assert_eq!(witness.bindings.len(), 1);
        assert_eq!(witness.bindings[0].name, "A");
        assert_eq!(witness.bindings[0].term, addr(nat("X")));
        assert!(witness.assumptions.is_empty());
        assert_eq!(
            witness.path_predicate,
            Pattern::Top {
                sort: kore_sort("SortGeneratedTopCell")
            }
        );
    }
    evaluation
}

fn assert_witness_paths(run: &Run, evaluation: &Evaluation) {
    for witness in &evaluation.witnesses {
        let path = run
            .bridged
            .paths
            .iter()
            .find(|path| path.path_ordinal == witness.path_ordinal)
            .expect("witness path ordinal");
        assert!(path.path_key.is_some());
        assert_eq!(witness.path_key, path.path_key);
        assert!(path.stop.has_real_prefix());
        assert_eq!(witness.stop_reason, path.stop);
        assert_eq!(witness.path_predicate, path.path_predicate);
        assert_eq!(
            witness.events,
            witness
                .event_indices
                .iter()
                .map(|&index| path.events[index].clone())
                .collect::<Vec<_>>()
        );
    }
}

fn only_witness_path<'a>(run: &'a Run, evaluation: &Evaluation) -> &'a PathInput {
    let [witness] = evaluation.witnesses.as_slice() else {
        panic!("exactly one witness: {evaluation:?}")
    };
    run.bridged
        .paths
        .iter()
        .find(|path| path.path_ordinal == witness.path_ordinal)
        .expect("witness path")
}

#[test]
fn symbolic_write_then_load_matches_consecutive_and_separated() {
    let (mut first, vocabulary) = run(Fixture::Sym, p1(), BUDGET);
    for plan in [wl_next(&vocabulary), wl_after(&vocabulary)] {
        let evaluation = assert_both(&mut first, &plan, PatternOutcome::Match, None);
        assert_eq!(evaluation.witnesses.len(), 1);
        assert_eq!(evaluation.witnesses[0].event_indices, [0, 1]);
        assert_eq!(evaluation.witnesses[0].stop_reason, PathStop::Terminal);
    }

    let (mut separated, vocabulary) = run(Fixture::Sym, p2(), BUDGET);
    let evaluation = assert_both(
        &mut separated,
        &wl_next(&vocabulary),
        PatternOutcome::NoMatch,
        None,
    );
    assert!(evaluation.complete_coverage);
    assert!(evaluation.witnesses.is_empty());
    let evaluation = assert_both(
        &mut separated,
        &wl_after(&vocabulary),
        PatternOutcome::Match,
        None,
    );
    let path = only_witness_path(&separated, &evaluation);
    assert_eq!(evaluation.witnesses[0].event_indices, [0, 2]);
    assert_eq!(evaluation.witnesses[0].stop_reason, PathStop::Terminal);
    assert_eq!(path.events[1].constructor, "memoryFree");
}

#[test]
fn symbolic_reversed_order_does_not_match() {
    let (mut run, vocabulary) = run(Fixture::Sym, p3(), BUDGET);
    let evaluation = assert_both(
        &mut run,
        &wl_after(&vocabulary),
        PatternOutcome::NoMatch,
        None,
    );
    assert!(evaluation.complete_coverage);
    assert!(evaluation.witnesses.is_empty());
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert_eq!(path.stop, PathStop::Terminal);
    assert_eq!(path.events[0].constructor, "memoryLoad");
    assert_eq!(path.events[1].constructor, "memoryWrite");
}

#[test]
fn sibling_write_and_load_never_form_a_witness() {
    let (mut run, vocabulary) = run(Fixture::Sym, p4(), BUDGET);
    let evaluation = assert_both(
        &mut run,
        &wl_after(&vocabulary),
        PatternOutcome::NoMatch,
        None,
    );
    assert!(evaluation.complete_coverage);
    assert!(evaluation.witnesses.is_empty());
    assert_eq!(run.bridged.paths.len(), 2);
    assert!(
        run.bridged
            .paths
            .iter()
            .all(|path| path.complete && path.stop == PathStop::Terminal && path.events.len() == 1)
    );
    assert_ne!(run.bridged.paths[0].path_key, run.bridged.paths[1].path_key);
}

#[test]
fn witness_stays_on_its_own_sibling() {
    let (mut run, vocabulary) = run(Fixture::Sym, p5(), BUDGET);
    let evaluation = assert_both(
        &mut run,
        &wl_after(&vocabulary),
        PatternOutcome::Match,
        None,
    );
    let path = only_witness_path(&run, &evaluation);
    assert_eq!(evaluation.witnesses[0].event_indices, [0, 1]);
    assert_eq!(
        path.events
            .iter()
            .map(|event| event.constructor.as_str())
            .collect::<Vec<_>>(),
        ["memoryWrite", "memoryLoad"]
    );
    assert_eq!(path.stop, PathStop::Terminal);
    assert_eq!(run.bridged.paths.len(), 2);
    let other = run
        .bridged
        .paths
        .iter()
        .find(|other| other.path_key != path.path_key)
        .expect("other sibling");
    assert_eq!(other.stop, PathStop::Terminal);
    assert_eq!(other.events.len(), 1);
    assert_eq!(other.events[0].constructor, "memoryLoad");
}

#[test]
fn shared_symbolic_address_binds_one_term() {
    let (mut run, vocabulary) = run(Fixture::Sym, p1(), BUDGET);
    let evaluation = assert_both(
        &mut run,
        &wl_after(&vocabulary),
        PatternOutcome::Match,
        None,
    );
    let path = only_witness_path(&run, &evaluation);
    let witness = &evaluation.witnesses[0];
    assert_eq!(witness.bindings.len(), 1);
    assert_eq!(witness.bindings[0].name, "A");
    assert_eq!(witness.bindings[0].term, addr(nat("X")));
    assert!(witness.assumptions.is_empty());
    assert_eq!(
        witness.path_predicate,
        Pattern::Top {
            sort: kore_sort("SortGeneratedTopCell")
        }
    );
    assert_eq!(path.stop, PathStop::Terminal);
}

#[test]
fn distinct_symbolic_addresses_match_under_unifier_assumption() {
    let (mut run, vocabulary) = run(Fixture::Sym, p6(), BUDGET);
    let plan = wl_after(&vocabulary);
    let plain = outcome(&run, &plan);
    assert_eq!(
        (plain.outcome, plain.failure),
        (PatternOutcome::Unknown, Some(PathStop::SolverUnknown))
    );
    let evaluation = decided(&mut run, &plan);
    // Both profiles (SYM-3B-03): the binding `X = Y` is eliminated on the `\top` path, so the
    // relation query is empty and `Sat` needs no solver.
    assert_eq!(
        (evaluation.outcome, evaluation.failure),
        (PatternOutcome::Match, None)
    );
    assert_witness_paths(&run, &evaluation);
    let path = only_witness_path(&run, &evaluation);
    let witness = &evaluation.witnesses[0];
    assert_eq!(witness.event_indices, [0, 1]);
    assert_eq!(witness.bindings.len(), 1);
    assert_eq!(witness.bindings[0].name, "A");
    assert_eq!(witness.bindings[0].term, addr(nat("X")));
    assert_eq!(
        witness.assumptions,
        [TermRelation {
            left: nat("X"),
            right: nat("Y")
        }]
    );
    assert_eq!(
        witness.path_predicate,
        Pattern::Top {
            sort: kore_sort("SortGeneratedTopCell")
        }
    );
    assert_eq!(path.stop, PathStop::Terminal);
}

#[test]
fn clashing_symbolic_addresses_do_not_match() {
    let (mut run, vocabulary) = run(Fixture::Sym, p7(), BUDGET);
    let plan = wl_after(&vocabulary);
    let plain = outcome(&run, &plan);
    assert_eq!(
        (plain.outcome, plain.failure),
        (PatternOutcome::Unknown, Some(PathStop::SolverUnknown))
    );
    let evaluation = decided(&mut run, &plan);
    assert_eq!(
        (evaluation.outcome, evaluation.failure),
        (PatternOutcome::NoMatch, None)
    );
    assert!(evaluation.complete_coverage);
    assert!(evaluation.witnesses.is_empty());
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert_eq!(path.stop, PathStop::Terminal);
}

#[test]
fn symbolic_depth_bound_absence_is_unknown_depth_limit() {
    let (mut run, vocabulary) = run(
        Fixture::Sym,
        p8(),
        ExecutionBudget {
            max_depth: Some(1),
            ..BUDGET
        },
    );
    let [leaf] = run.execution.leaves() else {
        panic!("one leaf")
    };
    assert_eq!(
        (leaf.halt, leaf.feasibility),
        (HaltClass::DepthBound, LeafFeasibility::Syntactic)
    );
    let evaluation = assert_both(
        &mut run,
        &wl_after(&vocabulary),
        PatternOutcome::Unknown,
        Some(PathStop::DepthLimit),
    );
    assert!(evaluation.witnesses.is_empty());
    assert_eq!(run.bridged.paths[0].stop, PathStop::DepthLimit);
}

#[test]
fn depth_cut_prefix_still_witnesses() {
    let (mut run, vocabulary) = run(
        Fixture::Sym,
        p8(),
        ExecutionBudget {
            max_depth: Some(1),
            ..BUDGET
        },
    );
    let evaluation = assert_both(&mut run, &w_only(&vocabulary), PatternOutcome::Match, None);
    let path = only_witness_path(&run, &evaluation);
    assert_eq!(evaluation.witnesses[0].event_indices, [0]);
    assert_eq!(evaluation.witnesses[0].stop_reason, PathStop::DepthLimit);
    assert_eq!(path.stop, PathStop::DepthLimit);
    assert!(!path.complete);
}

/// README 6.4 merges the two identical bounded prefixes into one step-bridged path;
/// both raw leaves remain BreadthBound with Syntactic feasibility.
#[test]
fn breadth_bound_absence_is_unknown_branch_limit() {
    let (mut run, vocabulary) = run(
        Fixture::Sym,
        p9(),
        ExecutionBudget {
            max_breadth: Some(NonZeroUsize::new(1).expect("nonzero")),
            ..BUDGET
        },
    );
    assert_eq!(run.execution.leaves().len(), 2);
    assert!(
        run.execution
            .leaves()
            .iter()
            .all(|leaf| (leaf.halt, leaf.feasibility)
                == (HaltClass::BreadthBound, LeafFeasibility::Syntactic))
    );
    let evaluation = assert_both(
        &mut run,
        &wl_after(&vocabulary),
        PatternOutcome::Unknown,
        Some(PathStop::BranchLimit),
    );
    assert!(evaluation.witnesses.is_empty());
    assert_eq!(run.bridged.paths.len(), 1);
    assert!(
        run.bridged
            .paths
            .iter()
            .all(|path| path.stop == PathStop::BranchLimit
                && !path.complete
                && path.events.is_empty())
    );
}

// Report runs use the same program/plan rows as README section 6.1 and 6.2.
// Leave ample watchdog time so a collection stop is determined by the fixture.
const REPORT_BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(120),
    ..BUDGET
};

#[derive(Clone, Copy)]
struct ReportRow {
    id: &'static str,
    fixture: Fixture,
    program: fn() -> Pattern,
    plan: fn(&EventVocabulary) -> PatternPlan,
    budget: ExecutionBudget,
}

fn report_rows() -> [ReportRow; 15] {
    let depth = ExecutionBudget {
        max_depth: Some(1),
        ..REPORT_BUDGET
    };
    let breadth = ExecutionBudget {
        max_breadth: Some(NonZeroUsize::new(1).expect("nonzero")),
        ..REPORT_BUDGET
    };
    let row = |id, fixture, program, plan, budget| ReportRow {
        id,
        fixture,
        program,
        plan,
        budget,
    };
    [
        row("P1-WL-next", Fixture::Sym, p1, wl_next, REPORT_BUDGET),
        row("P1-WL-after", Fixture::Sym, p1, wl_after, REPORT_BUDGET),
        row("P2-WL-next", Fixture::Sym, p2, wl_next, REPORT_BUDGET),
        row("P2-WL-after", Fixture::Sym, p2, wl_after, REPORT_BUDGET),
        row("P3-WL-after", Fixture::Sym, p3, wl_after, REPORT_BUDGET),
        row("P4-WL-after", Fixture::Sym, p4, wl_after, REPORT_BUDGET),
        row("P5-WL-after", Fixture::Sym, p5, wl_after, REPORT_BUDGET),
        row("P6-WL-after", Fixture::Sym, p6, wl_after, REPORT_BUDGET),
        row("P7-WL-after", Fixture::Sym, p7, wl_after, REPORT_BUDGET),
        row("P8-WL-after", Fixture::Sym, p8, wl_after, depth),
        row("P8-W-only", Fixture::Sym, p8, w_only, depth),
        row("P9-WL-after", Fixture::Sym, p9, wl_after, breadth),
        row("G1-GWL-after", Fixture::Guard, g1, gwl_after, REPORT_BUDGET),
        row("G2-GWL-after", Fixture::Guard, g2, gwl_after, REPORT_BUDGET),
        row("G3-GWL-after", Fixture::Guard, g3, gwl_after, REPORT_BUDGET),
    ]
}

fn report_on_backend(row: ReportRow, side: &ValidatedDefinition, backend: &mut Backend) -> String {
    let observation =
        StepObservation::new(backend, observations(row.fixture)).expect("declarations validate");
    let vocabulary = observation.vocabulary().clone();
    let plan = (row.plan)(&vocabulary);
    let state = support::initial_state((row.program)(), "SortProg");
    let stepped = adapter()
        .execute_steps(backend, &state, row.budget)
        .expect("execution adapts")
        .expect("steps decode");
    let execution = &stepped.adapted;
    assert!(!execution.timed_out(), "{}: watchdog timed out", row.id);
    let sorts = SymbolSorts::from_definition(
        &parse_definition(&side.artifacts().definition_kore).expect("compiled KORE parses"),
    );
    let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
    let bridged = backend
        .with_solver(None, |definition, solver| {
            let decider = ObservationDecider::new(definition, solver, &state);
            Ok::<_, k_rust::backend::BackendError>(paths_from_steps(
                &BridgeContext {
                    test_id: row.id,
                    classify: &normal,
                    sorts: &sorts,
                },
                &stepped,
                &observation,
                &decider,
            ))
        })
        .expect("backend definition")
        .expect("execution bridges");
    assert_ne!(
        bridged.collection.stop,
        CollectionStop::TimeLimit,
        "{}: collection reached time limit",
        row.id
    );
    let context = EvaluationContext {
        test_id: row.id.into(),
        bounds: row.budget.bounds(),
        vocabulary,
        symbol_sorts: sorts,
    };
    let evaluation = backend
        .with_solver(None, |definition, solver| {
            let relations = BackendRelations::shared(definition, solver, &state);
            Ok::<_, k_rust::backend::BackendError>(evaluate_with(
                &context,
                &plan,
                &bridged.paths,
                &bridged.collection,
                None,
                EvaluationOptions {
                    stable_path_keys: true,
                    search_policy: SearchPolicy::Exhaustive,
                    input_error: false,
                },
                &relations,
            ))
        })
        .expect("backend definition")
        .expect("evaluation");
    let report_bridged = paths_from_execution(
        execution,
        &BridgeContext {
            test_id: row.id,
            classify: &normal,
            sorts: &context.symbol_sorts,
        },
    )
    .expect("state-slot report bridge");
    let report = step3_report(ReportInput {
        profile: PROFILE,
        test_id: row.id,
        budget: &row.budget,
        backend_options: BACKEND_OPTIONS,
        result: ReportResult::Ok {
            execution,
            bridged: &report_bridged,
            evaluation: &evaluation,
        },
    });
    serde_json::to_string(&report).expect("report JSON")
}

fn fresh_report(row: ReportRow, side: &ValidatedDefinition) -> String {
    let mut backend = backend(&side.artifacts().definition_kore, row.fixture.module());
    report_on_backend(row, side, &mut backend)
}

fn assert_identical_reports(row: ReportRow, baseline: &str, candidate: &str) {
    if baseline == candidate {
        return;
    }
    let baseline: serde_json::Value = serde_json::from_str(baseline).expect("baseline JSON");
    let candidate: serde_json::Value = serde_json::from_str(candidate).expect("candidate JSON");
    fn differences(
        path: &str,
        left: &serde_json::Value,
        right: &serde_json::Value,
        output: &mut Vec<String>,
    ) {
        match (left, right) {
            (serde_json::Value::Object(left), serde_json::Value::Object(right)) => {
                for key in left.keys().chain(right.keys()) {
                    let child = format!("{path}/{key}");
                    match (left.get(key), right.get(key)) {
                        (Some(a), Some(b)) => differences(&child, a, b, output),
                        (a, b) => output.push(format!("{child}: {a:?} != {b:?}")),
                    }
                }
            }
            (serde_json::Value::Array(left), serde_json::Value::Array(right)) => {
                for index in 0..left.len().max(right.len()) {
                    let child = format!("{path}/{index}");
                    match (left.get(index), right.get(index)) {
                        (Some(a), Some(b)) => differences(&child, a, b, output),
                        (a, b) => output.push(format!("{child}: {a:?} != {b:?}")),
                    }
                }
            }
            (a, b) if a != b => output.push(format!("{path}: {a} != {b}")),
            _ => {}
        }
    }
    let mut paths = Vec::new();
    differences("$", &baseline, &candidate, &mut paths);
    panic!(
        "{}: report bytes differ; JSON differences: {paths:?}",
        row.id
    );
}

#[test]
fn repeated_symbolic_runs_emit_identical_reports() {
    for fixture in [Fixture::Sym, Fixture::Guard] {
        let validator =
            NativeValidator::bind(support::load(fixture.name()), CompileOptions::default());
        let side = validator.compile_baseline().expect("fixture compiles");
        for row in report_rows()
            .into_iter()
            .filter(|row| row.fixture == fixture)
        {
            let baseline = fresh_report(row, &side);
            for _ in 1..3 {
                let candidate = fresh_report(row, &side);
                assert_identical_reports(row, &baseline, &candidate);
            }
        }
    }
}

#[test]
fn report_is_stable_across_backend_reuse() {
    let row = report_rows()
        .into_iter()
        .find(|row| row.id == "P5-WL-after")
        .expect("branching report row");
    let validator =
        NativeValidator::bind(support::load(row.fixture.name()), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    let fresh = fresh_report(row, &side);
    let mut backend = backend(&side.artifacts().definition_kore, row.fixture.module());
    let first = report_on_backend(row, &side, &mut backend);
    let second = report_on_backend(row, &side, &mut backend);
    assert_identical_reports(row, &fresh, &first);
    assert_identical_reports(row, &first, &second);
}

fn wrap(value: Pattern) -> Pattern {
    support::app("Lblwrap", vec![value])
}

/// Audit (SYM-3A-09): an `anywhere` equation makes `wrap` non-injective. k-rust 347f693e's
/// kompile still marked it `injective` and its unifier decomposed it; since k-rust KK-51..KK-53
/// the attribute is withheld and the unifier keeps `wrap(s(X)) = wrap(z)` as an equation,
/// because an equation can rewrite an instance of `wrap(s(X))`. `wrap(s(X))` against `wrap(z)`
/// is equal for `X = z`, so the backend decider must not call them unequal, and the write/load
/// pair must not be `no-match`.
#[test]
fn non_free_injective_symbol_does_not_prove_a_clash() {
    let program = |address: Pattern| {
        seq(
            write(wrap(address), nat("V")),
            seq(load(wrap(z()), nat("W")), halt()),
        )
    };
    // Precision loss (VI-03F, k-rust 4d80cea6): withheld value-production definedness
    // leaves the ground instance Unknown in both profiles.
    let (mut ground, vocabulary) = run(Fixture::Wrap, program(s(z())), BUDGET);
    let plan = wl_after(&vocabulary);
    assert_eq!(decided(&mut ground, &plan).outcome, PatternOutcome::Unknown);
    let (mut symbolic, vocabulary) = run(Fixture::Wrap, program(s(nat("X"))), BUDGET);
    let plan = wl_after(&vocabulary);
    // Precision loss (VI-03F, k-rust 4d80cea6): the symbolic run splits on wrap
    // definedness under Z3; without Z3 it stops before any event. Both are incomplete.
    let paths = &symbolic.bridged.paths;
    assert_eq!(paths.len(), by_profile(1, 2));
    assert_eq!(
        symbolic.bridged.collection.stop,
        CollectionStop::SolverUnknown
    );
    for (ordinal, path) in paths.iter().enumerate() {
        assert_eq!(path.path_key, Some(format!("leaf:{ordinal}")));
        assert!(!path.complete, "{path:?}");
        assert_eq!(path.stop, PathStop::SolverUnknown);
        assert_eq!(
            path.execution_stop,
            kink_pattern::ExecutionStop::SolverUnknown
        );
        assert!(path.execution_terminal.is_none());
    }
    assert!(paths[0].events.is_empty());
    if cfg!(feature = "z3") {
        let defined = Pattern::And {
            sort: kore_sort("SortGeneratedTopCell"),
            arguments: vec![wrap(s(nat("X"))), wrap(z())]
                .into_iter()
                .map(|argument| Pattern::Ceil {
                    operand_sort: Box::new(kore_sort("SortAddress")),
                    result_sort: kore_sort("SortGeneratedTopCell"),
                    argument: Box::new(argument),
                })
                .collect(),
        };
        assert_eq!(
            paths[0].path_predicate,
            Pattern::Not {
                sort: kore_sort("SortGeneratedTopCell"),
                argument: Box::new(defined.clone()),
            }
        );
        assert_eq!(paths[1].path_predicate, defined);
        assert_eq!(paths[1].events.len(), 2);
        assert_eq!(paths[1].events[0].constructor, "memoryWrite");
        assert_eq!(paths[1].events[1].constructor, "memoryLoad");
        assert_eq!(
            paths[1].events[0].payload,
            vec![wrap(s(nat("X"))), nat("V")]
        );
        assert_eq!(paths[1].events[1].payload, vec![wrap(z()), nat("W")]);
        assert!(
            paths[1]
                .events
                .iter()
                .all(|event| event.presence == kink_pattern::EventPresence::Certain)
        );
    } else {
        assert_eq!(
            paths[0].path_predicate,
            Pattern::Top {
                sort: kore_sort("SortGeneratedTopCell"),
            }
        );
    }
    // A clash below the free `addr` constructor (P7) is still proved.
    let (mut free, free_vocabulary) = run(Fixture::Sym, p7(), BUDGET);
    assert_eq!(
        decided(&mut free, &wl_after(&free_vocabulary)).outcome,
        PatternOutcome::NoMatch
    );
    let evaluation = decided(&mut symbolic, &plan);
    assert_eq!(
        evaluation.outcome,
        PatternOutcome::Unknown,
        "{evaluation:?}"
    );
    assert!(evaluation.witnesses.is_empty());
    assert_eq!(outcome(&symbolic, &plan).outcome, PatternOutcome::Unknown);
}

/// Audit (SYM-3A-09): leaf feasibility and the solver-free `Sat` assume every valuation of the
/// initial variables follows a clean no-Z3 path. `other` is `owise` below rules that cover
/// every `Nat`, so no value reaches the write/load events behind it; a symbolic subject must
/// not take `other` as if the higher-priority rules were refuted.
#[test]
fn owise_rule_is_not_taken_for_a_symbolic_subject() {
    let program = |selector: Pattern| {
        support::app(
            "Lblpick",
            vec![
                selector,
                seq(
                    write(addr(z()), nat("V")),
                    seq(load(addr(z()), nat("W")), halt()),
                ),
            ],
        )
    };
    for ground in [z(), s(z())] {
        let (mut run, vocabulary) = run(Fixture::Owise, program(ground), BUDGET);
        assert_eq!(
            decided(&mut run, &wl_after(&vocabulary)).outcome,
            PatternOutcome::NoMatch
        );
    }
    let (mut symbolic, vocabulary) = run(Fixture::Owise, program(nat("X")), BUDGET);
    // No-Z3: matching `z` or `s(_)` against `X` needs a narrowing condition, which `NoSolver`
    // cannot accept, so the priority group is undecided and the one leaf is `Indeterminate`.
    // Z3: narrowing is accepted; `zero` and `succ` each give a `Stuck` leaf on the ground
    // `halt` whose predicate keeps its narrowing condition (`X = z`, `X = s(_)`), and `other`
    // is not taken (k-rust refutes its remainder by the finite constructors of `Nat`). The
    // predicates are over `Nat`, which Z3 abstracts, so no exact `Sat` shows the leaves
    // feasible and they stay `SolverUnknown` (SYM-3B-02).
    let stops: Vec<_> = symbolic
        .bridged
        .paths
        .iter()
        .map(|path| path.stop)
        .collect();
    assert_eq!(
        stops,
        by_profile(
            vec![PathStop::SolverUnknown],
            vec![PathStop::SolverUnknown, PathStop::SolverUnknown]
        )
    );
    for path in &symbolic.bridged.paths {
        assert!(path.events.is_empty(), "{path:?}");
        if PROFILE == SolverProfile::Z3 {
            assert!(!matches!(path.path_predicate, Pattern::Top { .. }));
        }
    }
    let failure = PathStop::SolverUnknown;
    let plan = wl_after(&vocabulary);
    for evaluation in [decided(&mut symbolic, &plan), outcome(&symbolic, &plan)] {
        assert_eq!(
            evaluation.outcome,
            PatternOutcome::Unknown,
            "{evaluation:?}"
        );
        assert_eq!(evaluation.failure, Some(failure));
    }
}

/// Audit (SYM-3A-09): the solver-free `Sat` for witness assumptions needs the path predicate
/// to be exactly `\top`. `pin` pins `X = z` and `Y = s(z)` after the write/load events, so
/// `X = Y` is infeasible with the leaf predicate; k-rust keeps both equations in the leaf
/// predicate rather than substituting them away, so the leaf is `SolverUnknown` and the result
/// stays `unknown`. Instances with an undefined `pin` result have a separate `Trivial` leaf.
#[test]
fn ensures_constraint_keeps_a_later_witness_unknown() {
    let program = seq(
        write(addr(nat("X")), nat("V")),
        seq(
            load(addr(nat("Y")), nat("W")),
            support::app("Lblpin", vec![nat("X"), nat("Y"), halt()]),
        ),
    );
    let (mut run, vocabulary) = run(Fixture::Ensures, program, BUDGET);
    assert_eq!(run.execution.leaves()[0].halt, HaltClass::Trivial);
    let path = run.bridged.paths.last().expect("successor path");
    assert_eq!(path.stop, PathStop::SolverUnknown);
    assert!(!matches!(path.path_predicate, Pattern::Top { .. }));
    let evaluation = decided(&mut run, &wl_after(&vocabulary));
    assert_eq!(
        (evaluation.outcome, evaluation.failure),
        (PatternOutcome::Unknown, Some(PathStop::SolverUnknown))
    );
}

/// `symbottom.k`: write and load at address 1, then `stop(1)`, whose only rewrite `ensures`
/// `1 <Int 0`.
fn trivial_program() -> Pattern {
    seq(
        write(addr(support::int(1)), integer("V")),
        seq(
            load(addr(support::int(1)), integer("W")),
            support::app("Lblstop", vec![support::int(1)]),
        ),
    )
}
/// `symbottom.k`: write `X`, load `Y`, then `apart(X, Y)`, which `ensures X =/=Int Y`.
fn apart_program() -> Pattern {
    seq(
        write(addr(integer("X")), integer("V")),
        seq(
            load(addr(integer("Y")), integer("W")),
            support::app("Lblapart", vec![integer("X"), integer("Y")]),
        ),
    )
}
/// `symbottom.k`: G3's ground write/load under the initial path condition `1 = 2`.
fn vacuous_state() -> Pattern {
    let top = kore_sort("SortGeneratedTopCell");
    Pattern::And {
        sort: top.clone(),
        arguments: vec![
            support::initial_state(
                seq(
                    write(addr(support::int(1)), integer("V")),
                    seq(load(addr(support::int(1)), integer("W")), halt()),
                ),
                "SortProg",
            ),
            Pattern::Equals {
                operand_sort: Box::new(kore_sort("SortInt")),
                result_sort: top,
                left: Box::new(support::int(1)),
                right: Box::new(support::int(2)),
            },
        ],
    }
}

/// The halt, feasibility and state-slot bridged stop of each leaf, in backend order.
fn leaf_rows(run: &Run) -> Vec<(HaltClass, LeafFeasibility, PathStop)> {
    run.execution
        .leaves()
        .iter()
        .zip(&run.report_bridged.paths)
        .map(|(leaf, path)| (leaf.halt, leaf.feasibility, path.stop))
        .collect()
}

/// SYM-3B-02, README 3.1: `stop(1)`'s only rewrite is undefined, so k-rust reports the state
/// `stop(1)` itself as a `Trivial` leaf after the write and load. KK-66: a ground run of this
/// program performs the write and the load and then has no defined step, so the leaf is a
/// complete `UndefinedStep` path in both profiles. Its events are real and witness the match; the
/// undefined step emits no event.
#[test]
fn ground_undefined_step_prefix_witnesses_a_match() {
    let (mut run, vocabulary) = run(Fixture::Bottom, trivial_program(), BUDGET);
    let [leaf] = run.execution.leaves() else {
        panic!("one leaf")
    };
    assert_eq!((leaf.halt, leaf.branch.depth), (HaltClass::Trivial, 2));
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert_eq!(path.stop, PathStop::UndefinedStep);
    assert!(path.complete);
    let terminal = path.execution_terminal.as_ref().expect("terminal");
    assert_eq!(terminal.kind, ExecutionTerminalKind::UndefinedStep);
    assert!(terminal.state.free_variables().is_empty());
    assert_eq!(path.events.len(), 2);
    let plan = gwl_after(&vocabulary);
    let plain = outcome(&run, &plan);
    for evaluation in [plain, decided(&mut run, &plan)] {
        assert_eq!(
            (evaluation.outcome, evaluation.failure),
            (PatternOutcome::Match, None)
        );
        assert!(evaluation.complete_coverage);
        let [witness] = evaluation.witnesses.as_slice() else {
            panic!("one witness")
        };
        assert_eq!(witness.stop_reason, PathStop::UndefinedStep);
        assert_eq!(witness.bindings[0].term, support::int(1));
    }
}

/// SYM-3B-02, README 3.1: an initial state whose path condition is `\bottom` has no instance.
/// k-rust reports one `Vacuous` leaf at depth 0; the bridge discards it in both profiles, the
/// collection is an empty clean exhaustion, the result is `no-match` with complete coverage,
/// and the report lists the leaf under `discarded`.
#[test]
fn vacuous_initial_state_is_a_discarded_path() {
    let (mut run, vocabulary) = run_state(Fixture::Bottom, vacuous_state(), BUDGET);
    let [leaf] = run.execution.leaves() else {
        panic!("one leaf")
    };
    assert_eq!((leaf.halt, leaf.branch.depth), (HaltClass::Vacuous, 0));
    assert!(run.bridged.paths.is_empty());
    assert_eq!(run.bridged.collection.stop, CollectionStop::SearchExhausted);
    assert!(run.bridged.collection.empty_search_decision.is_some());
    let plan = gwl_after(&vocabulary);
    let evaluation = assert_both(&mut run, &plan, PatternOutcome::NoMatch, None);
    assert!(evaluation.complete_coverage);
    let report = step3_report(ReportInput {
        profile: PROFILE,
        test_id: "vacuous",
        budget: &BUDGET,
        backend_options: BACKEND_OPTIONS,
        result: ReportResult::Ok {
            execution: &run.execution,
            bridged: &run.report_bridged,
            evaluation: &evaluation,
        },
    });
    assert_eq!(report["outcome"], "no-match");
    assert_eq!(report["paths"], serde_json::json!([]));
    assert_eq!(
        report["discarded"],
        serde_json::json!([{ "key": "leaf:0", "halt": "vacuous", "reason": "vacuous" }])
    );
}

/// `apart` emits a `Trivial` leaf under `X = Y` before its stuck successor under `X =/=Int Y`
/// (KK-66). Z3 shows both feasible. The `Trivial` leaf is a complete undefined step: its instances
/// perform the write and the load, and then no defined step exists. With a shared address the
/// write/load pattern is a `match` on it under `X = Y`; with disjoint addresses every leaf is
/// complete and the result is `no-match`. Without Z3 neither leaf is shown feasible: `unknown`.
#[test]
fn apart_undefined_step_is_complete_evidence() {
    let disjoint = || {
        seq(
            write(addr(support::int(1)), integer("V")),
            seq(
                load(addr(support::int(2)), integer("W")),
                support::app("Lblapart", vec![integer("X"), integer("Y")]),
            ),
        )
    };
    for (id, program, z3_outcome) in [
        ("shared", apart_program(), PatternOutcome::Match),
        ("disjoint", disjoint(), PatternOutcome::NoMatch),
    ] {
        let (mut run, vocabulary) = run(Fixture::Bottom, program, BUDGET);
        assert_eq!(
            leaf_rows(&run),
            [
                (
                    HaltClass::Trivial,
                    by_profile(LeafFeasibility::Unknown, LeafFeasibility::Solver),
                    by_profile(PathStop::SolverUnknown, PathStop::UndefinedStep),
                ),
                (
                    HaltClass::Stuck,
                    by_profile(LeafFeasibility::Unknown, LeafFeasibility::Solver),
                    by_profile(PathStop::SolverUnknown, PathStop::Terminal),
                ),
            ],
            "{id}"
        );
        let undefined = run
            .bridged
            .paths
            .iter()
            .find(|path| path.path_predicate == run.report_bridged.paths[0].path_predicate)
            .expect("undefined leaf's canonical step path");
        assert_eq!(undefined.path_key.as_deref(), Some("leaf:1"), "{id}");
        assert_eq!(
            undefined.stop,
            by_profile(PathStop::SolverUnknown, PathStop::UndefinedStep),
            "{id}"
        );
        if cfg!(feature = "z3") {
            assert_eq!(
                undefined
                    .execution_terminal
                    .as_ref()
                    .expect("terminal")
                    .kind,
                ExecutionTerminalKind::UndefinedStep
            );
        }
        assert_eq!(undefined.events.len(), 2, "{id}");
        assert!(
            !matches!(undefined.path_predicate, Pattern::Top { .. }),
            "{id}"
        );
        let evaluation = decided(&mut run, &gwl_after(&vocabulary));
        assert_eq!(
            (evaluation.outcome, evaluation.failure),
            by_profile(
                (PatternOutcome::Unknown, Some(PathStop::SolverUnknown)),
                (z3_outcome, None)
            ),
            "{id}"
        );
        if evaluation.outcome == PatternOutcome::Match {
            assert!(
                evaluation
                    .witnesses
                    .iter()
                    .all(|witness| witness.stop_reason == PathStop::UndefinedStep),
                "{id}"
            );
        }
        let report = step3_report(ReportInput {
            profile: PROFILE,
            test_id: id,
            budget: &BUDGET,
            backend_options: BACKEND_OPTIONS,
            result: ReportResult::Ok {
                execution: &run.execution,
                bridged: &run.report_bridged,
                evaluation: &evaluation,
            },
        });
        let path = &report["paths"][0];
        assert_eq!(
            (&path["stop"], &path["complete"], &path["feasibility"]),
            (
                &serde_json::json!(by_profile("solver-unknown", "undefined-step")),
                &serde_json::json!(cfg!(feature = "z3")),
                &serde_json::json!(by_profile("unknown", "solver")),
            ),
            "{id}"
        );
    }
}

/// An undefined step commits no transition, so its rule appears in no event; k-rust names it on
/// the `Trivial` leaf instead (`ExecutionLeaf::rule_id`/`rule_label`). The adapter keeps it and the
/// report states it as the path's `undefined_rule`: the `stop` rule for the ground `stop(1)`,
/// whose `ensures` is refuted, and the `apart` rule for `apart(X, Y)` under `X = Y`, whose
/// `ensures` is carried. The id is the one the rule catalog gives the rule. The rule is named
/// whether or not the leaf is shown feasible, and every other path's `undefined_rule` is null.
#[test]
fn undefined_step_names_its_rule_in_the_report() {
    for (id, program, label) in [
        ("ground-stop", trivial_program(), "SYMBOTTOM.stop"),
        ("symbolic-apart", apart_program(), "SYMBOTTOM.apart"),
    ] {
        let (mut run, vocabulary) = run(Fixture::Bottom, program, BUDGET);
        let catalog_id = run
            .backend
            .rule_catalog(Some(Fixture::Bottom.module()))
            .expect("rule catalog")
            .into_iter()
            .find(|rule| rule.label.as_deref() == Some(label))
            .unwrap_or_else(|| panic!("{id}: {label} is in the catalog"))
            .id;
        let named = |leaf: &AdaptedLeaf| {
            leaf.undefined_rule
                .as_ref()
                .map(|rule| (rule.id.clone(), rule.label.clone()))
        };
        let leaves = run.execution.leaves().to_vec();
        assert_eq!(leaves[0].halt, HaltClass::Trivial, "{id}");
        assert_eq!(
            named(&leaves[0]),
            Some((catalog_id.clone(), Some(label.to_owned()))),
            "{id}"
        );
        assert!(
            leaves[1..].iter().all(|leaf| leaf.undefined_rule.is_none()),
            "{id}"
        );
        let evaluation = decided(&mut run, &gwl_after(&vocabulary));
        let report = step3_report(ReportInput {
            profile: PROFILE,
            test_id: id,
            budget: &BUDGET,
            backend_options: BACKEND_OPTIONS,
            result: ReportResult::Ok {
                execution: &run.execution,
                bridged: &run.report_bridged,
                evaluation: &evaluation,
            },
        });
        let paths = report["paths"].as_array().expect("paths");
        assert_eq!(paths.len(), leaves.len(), "{id}");
        assert_eq!(
            paths[0]["undefined_rule"],
            serde_json::json!({ "id": catalog_id, "label": label }),
            "{id}"
        );
        assert!(
            paths[1..]
                .iter()
                .all(|path| path["undefined_rule"].is_null()),
            "{id}"
        );
    }
}

/// `window(I)` at the root: undefined for `I >Int 5` and `I >=Int 10`, `halt` for `5 < I < 10`,
/// stuck for `I <=Int 5`. The undefined sub-case has no committed transition, so its path receives a canonical leaf key. With Z3 all three leaves are feasible and complete, so an absent pattern is
/// `no-match`; without Z3 the `requires` is undecided and the result is `unknown`.
#[test]
fn root_undefined_step_completes_an_absence() {
    let (mut run, vocabulary) = run(
        Fixture::Bottom,
        support::app("Lblwindow", vec![integer("I")]),
        BUDGET,
    );
    let complete = (
        HaltClass::Stuck,
        LeafFeasibility::Solver,
        PathStop::Terminal,
    );
    assert_eq!(
        leaf_rows(&run),
        by_profile(
            // Without a solver the `requires` is undecided: the step stops.
            vec![(
                HaltClass::Indeterminate,
                LeafFeasibility::Syntactic,
                PathStop::SolverUnknown
            )],
            vec![
                (
                    HaltClass::Trivial,
                    LeafFeasibility::Solver,
                    PathStop::UndefinedStep
                ),
                complete,
                complete,
            ]
        )
    );
    if cfg!(feature = "z3") {
        let undefined = run
            .bridged
            .paths
            .iter()
            .find(|path| path.path_predicate == run.report_bridged.paths[0].path_predicate)
            .expect("undefined leaf's canonical step path");
        assert_eq!(undefined.stop, PathStop::UndefinedStep);
        assert_eq!(
            undefined
                .execution_terminal
                .as_ref()
                .expect("terminal")
                .kind,
            ExecutionTerminalKind::UndefinedStep
        );
        assert_eq!(undefined.path_key.as_deref(), Some("leaf:2"));
    }
    let evaluation = decided(&mut run, &gwl_after(&vocabulary));
    assert_eq!(
        (evaluation.outcome, evaluation.failure),
        by_profile(
            (PatternOutcome::Unknown, Some(PathStop::SolverUnknown)),
            (PatternOutcome::NoMatch, None)
        )
    );
}

/// A guarded `/Int` result has no undefined-step leaf under Z3. Zero-denominator instances
/// stay in the rule remainder, while the defined instances reach `done`.
#[test]
fn guarded_division_covers_disjoint_and_shared_addresses() {
    use HaltClass::{Indeterminate, Stuck};
    use LeafFeasibility::{Solver, Syntactic};
    let program = |write_at, load_at| {
        seq(
            write(addr(support::int(write_at)), integer("V")),
            seq(
                load(addr(support::int(load_at)), integer("W")),
                support::app("Lbldivide", vec![support::int(10), integer("D")]),
            ),
        )
    };
    for (write_at, load_at, z3_outcome) in [
        (1, 2, PatternOutcome::NoMatch),
        (1, 1, PatternOutcome::Match),
    ] {
        let (mut run, vocabulary) = run(Fixture::Division, program(write_at, load_at), BUDGET);
        assert_eq!(
            leaf_rows(&run),
            by_profile(
                vec![(Indeterminate, Syntactic, PathStop::SolverUnknown)],
                vec![(Stuck, Solver, PathStop::Terminal); 2],
            )
        );
        assert!(
            run.execution
                .leaves()
                .iter()
                .all(|leaf| leaf.halt != HaltClass::Trivial)
        );
        let evaluation = decided(&mut run, &gwl_after(&vocabulary));
        assert_eq!(
            evaluation.outcome,
            by_profile(PatternOutcome::Unknown, z3_outcome)
        );
        assert_eq!(
            evaluation.failure,
            by_profile(Some(PathStop::SolverUnknown), None)
        );
    }
}

/// SYM-3B-02, README 3.1: under Z3, guardedmem's `requires` split G1 and G2 into `Stuck`
/// leaves whose predicates over `Int` translate exactly and are `Sat`. guardedmem has no
/// `ensures`, so every leaf is complete; G2's `loadNeg` remainder (`Y >=Int 0`) is a symbolic
/// `Stuck` leaf over `Int` variables, complete because its stuckness holds for every instance.
/// G2's only candidate needs `X = Y` with `X >=Int 0 ∧ Y <Int 0`, which Z3 refutes: `no-match`.
/// G1's candidate `X = Y` with `X >=Int 0 ∧ Y >=Int 0` is an exact solver `Sat` (SYM-3B-03):
/// `match`. Without Z3 both stay one `Indeterminate` leaf.
#[test]
fn constrained_and_remainder_stuck_leaves_complete_under_z3() {
    use HaltClass::{Indeterminate, Stuck};
    use LeafFeasibility::{Solver, Syntactic};
    let complete = (Stuck, Solver, PathStop::Terminal);
    for (program, decided) in [
        (g1(), (PatternOutcome::Match, None)),
        (g2(), (PatternOutcome::NoMatch, None)),
    ] {
        let (mut run, vocabulary) = run(Fixture::Guard, program, BUDGET);
        assert_eq!(
            leaf_rows(&run),
            by_profile(
                vec![(Indeterminate, Syntactic, PathStop::SolverUnknown)],
                vec![complete; 3]
            )
        );
        let evaluation = decided_outcome(&mut run, &gwl_after(&vocabulary));
        assert_eq!(
            evaluation,
            by_profile(
                (PatternOutcome::Unknown, Some(PathStop::SolverUnknown)),
                decided
            )
        );
        if PROFILE == SolverProfile::Z3 {
            let symbolic = run
                .bridged
                .paths
                .iter()
                .filter_map(|path| path.execution_terminal.as_ref())
                .filter(|terminal| !terminal.state.free_variables().is_empty())
                .count();
            // G2's `loadNeg` remainder keeps `Y` and `W` in its terminal term.
            assert_eq!(symbolic, usize::from(decided.0 == PatternOutcome::NoMatch));
            assert!(
                run.bridged
                    .paths
                    .iter()
                    .all(|path| !matches!(path.path_predicate, Pattern::Top { .. }))
            );
        }
    }
}

/// The backend decider's outcome and failure.
fn decided_outcome(run: &mut Run, plan: &PatternPlan) -> Status {
    let evaluation = decided(run, plan);
    (evaluation.outcome, evaluation.failure)
}

/// `symwrap.k`: write to `wrap(s(X))`, load from `wrap(z)`.
fn wrap_program() -> Pattern {
    seq(
        write(wrap(s(nat("X"))), nat("V")),
        seq(load(wrap(z()), nat("W")), halt()),
    )
}
/// `symowise.k`: a symbolic selector in front of a ground write/load pair.
fn owise_program() -> Pattern {
    support::app(
        "Lblpick",
        vec![
            nat("X"),
            seq(
                write(addr(z()), nat("V")),
                seq(load(addr(z()), nat("W")), halt()),
            ),
        ],
    )
}
/// `symensures.k`: `pin` constrains `X` and `Y` after the write/load pair.
fn ensures_program() -> Pattern {
    seq(
        write(addr(nat("X")), nat("V")),
        seq(
            load(addr(nat("Y")), nat("W")),
            support::app("Lblpin", vec![nat("X"), nat("Y"), halt()]),
        ),
    )
}

/// An expected status: outcome and, for `unknown`, its failure.
type Status = (PatternOutcome, Option<PathStop>);

/// One profile-table row: README 6.1, 6.2 and 6.3 programs with `(no_z3, z3)` columns for the
/// bridged path stops (in path order), plain `evaluate`, and `evaluate_with` using shared baseline relations.
struct ProfileRow {
    id: &'static str,
    fixture: Fixture,
    program: fn() -> Pattern,
    plan: fn(&EventVocabulary) -> PatternPlan,
    budget: ExecutionBudget,
    stops: (&'static [PathStop], &'static [PathStop]),
    structural: (Status, Status),
    decided: (Status, Status),
}

/// Every symbolic row in both profiles. Z3 stop semantics are decided (SYM-3B-02, README 3.1)
/// and so is when a solver `Sat` counts (SYM-3B-03, README 4.2); no Z3 cell is provisional.
#[test]
fn profile_table_rows() {
    use PathStop::{BranchLimit, DepthLimit, SolverUnknown, Terminal, UndefinedStep};
    use PatternOutcome::{Match, NoMatch, Unknown};
    let depth = ExecutionBudget {
        max_depth: Some(1),
        ..BUDGET
    };
    let breadth = ExecutionBudget {
        max_breadth: Some(NonZeroUsize::new(1).expect("nonzero")),
        ..BUDGET
    };
    let same = |status: Status| (status, status);
    let matched = same((Match, None));
    let absent = same((NoMatch, None));
    let rows = [
        ProfileRow {
            id: "P1-WL-next",
            fixture: Fixture::Sym,
            program: p1,
            plan: wl_next,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: matched,
            decided: matched,
        },
        ProfileRow {
            id: "P1-WL-after",
            fixture: Fixture::Sym,
            program: p1,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: matched,
            decided: matched,
        },
        ProfileRow {
            id: "P2-WL-next",
            fixture: Fixture::Sym,
            program: p2,
            plan: wl_next,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: absent,
            decided: absent,
        },
        ProfileRow {
            id: "P2-WL-after",
            fixture: Fixture::Sym,
            program: p2,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: matched,
            decided: matched,
        },
        ProfileRow {
            id: "P3-WL-after",
            fixture: Fixture::Sym,
            program: p3,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: absent,
            decided: absent,
        },
        ProfileRow {
            id: "P4-WL-after",
            fixture: Fixture::Sym,
            program: p4,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal, Terminal], &[Terminal, Terminal]),
            structural: absent,
            decided: absent,
        },
        ProfileRow {
            id: "P5-WL-after",
            fixture: Fixture::Sym,
            program: p5,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal, Terminal], &[Terminal, Terminal]),
            structural: matched,
            decided: matched,
        },
        ProfileRow {
            id: "P6-WL-after",
            fixture: Fixture::Sym,
            program: p6,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: same((Unknown, Some(SolverUnknown))),
            // SYM-3B-03: the eliminated binding `X = Y` leaves an empty relation query.
            decided: matched,
        },
        ProfileRow {
            id: "P7-WL-after",
            fixture: Fixture::Sym,
            program: p7,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: same((Unknown, Some(SolverUnknown))),
            decided: absent,
        },
        ProfileRow {
            id: "P8-WL-after",
            fixture: Fixture::Sym,
            program: p8,
            plan: wl_after,
            budget: depth,
            stops: (&[DepthLimit], &[DepthLimit]),
            structural: same((Unknown, Some(DepthLimit))),
            decided: same((Unknown, Some(DepthLimit))),
        },
        ProfileRow {
            id: "P8-W-only",
            fixture: Fixture::Sym,
            program: p8,
            plan: w_only,
            budget: depth,
            stops: (&[DepthLimit], &[DepthLimit]),
            structural: matched,
            decided: matched,
        },
        ProfileRow {
            id: "P9-WL-after",
            fixture: Fixture::Sym,
            program: p9,
            plan: wl_after,
            budget: breadth,
            // README 6.4 merges these exact duplicate bounded prefixes.
            stops: (&[BranchLimit], &[BranchLimit]),
            structural: same((Unknown, Some(BranchLimit))),
            decided: same((Unknown, Some(BranchLimit))),
        },
        // G1/G2 under Z3 (SYM-3B-02): Z3 decides the `requires`, giving three `Stuck` leaves
        // whose predicates translate exactly and are `Sat`; guardedmem has no `ensures`, so
        // they are complete (`constrained_and_remainder_stuck_leaves_complete_under_z3`). G1's
        // candidate `X = Y` is an exact solver `Sat` with its path predicate (SYM-3B-03): match.
        // G2's only candidate is `Unsat` with its path predicate: no-match.
        ProfileRow {
            id: "G1-GWL-after",
            fixture: Fixture::Guard,
            program: g1,
            plan: gwl_after,
            budget: BUDGET,
            stops: (&[SolverUnknown], &[Terminal, Terminal, Terminal]),
            structural: (
                (Unknown, Some(SolverUnknown)),
                (Unknown, Some(SolverUnknown)),
            ),
            decided: ((Unknown, Some(SolverUnknown)), (Match, None)),
        },
        ProfileRow {
            id: "G2-GWL-after",
            fixture: Fixture::Guard,
            program: g2,
            plan: gwl_after,
            budget: BUDGET,
            stops: (&[SolverUnknown], &[Terminal, Terminal, Terminal]),
            structural: (
                (Unknown, Some(SolverUnknown)),
                (Unknown, Some(SolverUnknown)),
            ),
            decided: ((Unknown, Some(SolverUnknown)), (NoMatch, None)),
        },
        ProfileRow {
            id: "G3-GWL-after",
            fixture: Fixture::Guard,
            program: g3,
            plan: gwl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: matched,
            decided: matched,
        },
        ProfileRow {
            // Precision loss (VI-03F, k-rust 4d80cea6): definedness remains undecided.
            id: "symwrap-WL-after",
            fixture: Fixture::Wrap,
            program: wrap_program,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[SolverUnknown], &[SolverUnknown, SolverUnknown]),
            structural: same((Unknown, Some(SolverUnknown))),
            decided: same((Unknown, Some(SolverUnknown))),
        },
        // Z3 (SYM-3B-02): narrowing gives two `Stuck` leaves on the ground `halt` whose
        // predicates (`X = z`, `X = s(_)`) are over `Nat`, which Z3 abstracts, so no exact `Sat`
        // shows them feasible: `SolverUnknown`.
        ProfileRow {
            id: "symowise-WL-after",
            fixture: Fixture::Owise,
            program: owise_program,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[SolverUnknown], &[SolverUnknown, SolverUnknown]),
            structural: (
                (Unknown, Some(SolverUnknown)),
                (Unknown, Some(SolverUnknown)),
            ),
            decided: (
                (Unknown, Some(SolverUnknown)),
                (Unknown, Some(SolverUnknown)),
            ),
        },
        ProfileRow {
            id: "symensures-WL-after",
            fixture: Fixture::Ensures,
            program: ensures_program,
            plan: wl_after,
            budget: BUDGET,
            stops: (
                &[SolverUnknown, SolverUnknown],
                &[SolverUnknown, SolverUnknown],
            ),
            structural: same((Unknown, Some(SolverUnknown))),
            decided: same((Unknown, Some(SolverUnknown))),
        },
        // KK-66: this ground `Trivial` leaf is a complete undefined step whose prefix matches.
        ProfileRow {
            id: "symbottom-trivial-GWL-after",
            fixture: Fixture::Bottom,
            program: trivial_program,
            plan: gwl_after,
            budget: BUDGET,
            stops: (&[UndefinedStep], &[UndefinedStep]),
            structural: matched,
            decided: matched,
        },
        // KK-66: under Z3 the feasible `Trivial` leaf is an undefined step, and the match under
        // `X = Y` needs the solver's relation decision; the stuck successor completes.
        ProfileRow {
            id: "symbottom-apart-GWL-after",
            fixture: Fixture::Bottom,
            program: apart_program,
            plan: gwl_after,
            budget: BUDGET,
            // README 6.4 breaks the equal-event trace tie by stop, Terminal first.
            stops: (&[SolverUnknown, SolverUnknown], &[Terminal, UndefinedStep]),
            structural: same((Unknown, Some(SolverUnknown))),
            decided: ((Unknown, Some(SolverUnknown)), (Match, None)),
        },
    ];
    let mut failures = Vec::new();
    for row in rows {
        let (mut run, vocabulary) = run(row.fixture, (row.program)(), row.budget);
        let plan = (row.plan)(&vocabulary);
        let stops: Vec<_> = run.bridged.paths.iter().map(|path| path.stop).collect();
        let plain = outcome(&run, &plan);
        let decided = decided(&mut run, &plan);
        assert_witness_paths(&run, &plain);
        assert_witness_paths(&run, &decided);
        let actual = (
            stops.as_slice(),
            (plain.outcome, plain.failure),
            (decided.outcome, decided.failure),
        );
        let expected = (
            by_profile(row.stops.0, row.stops.1),
            by_profile(row.structural.0, row.structural.1),
            by_profile(row.decided.0, row.decided.1),
        );
        if actual != expected {
            failures.push(format!(
                "{} ({}): expected {expected:?}, got {actual:?}",
                row.id,
                PROFILE.name()
            ));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// `evaluate_with` over `run`'s paths, once with shared [`BackendRelations`] over the build's solver
/// (Z3 in the Z3 build) and once over `NoSolver` on the same definition: the unifier alone.
fn decided_by_both(run: &mut Run, plan: &PatternPlan, paths: &[PathInput]) -> [Evaluation; 2] {
    let evaluate = |relations: &BackendRelations<'_>| {
        evaluate_with(
            &run.context,
            plan,
            paths,
            &run.bridged.collection,
            None,
            EvaluationOptions {
                stable_path_keys: true,
                search_policy: SearchPolicy::Exhaustive,
                input_error: false,
            },
            relations,
        )
        .expect("evaluation")
    };
    let state = run.state.clone();
    run.backend
        .with_solver(None, |definition, solver| {
            Ok::<_, k_rust::backend::BackendError>([
                evaluate(&BackendRelations::shared(definition, solver, &state)),
                evaluate(&BackendRelations::shared(definition, &NoSolver, &state)),
            ])
        })
        .expect("backend definition")
}

/// SYM-3B-03 differential check (README 4.3): on the free-constructor fragment the Z3 build
/// returns exactly the no-Z3 answers. Every symmem row of README 6.1 and `symwrap` has one
/// expected column that both builds assert, and within each build the decider over the build's
/// solver and the unifier-only decider (`NoSolver`) give identical evaluations over the same
/// paths, witnesses and assumptions included.
#[test]
fn z3_agrees_with_unifier_on_constructor_fragment() {
    use PathStop::{BranchLimit, DepthLimit, SolverUnknown};
    use PatternOutcome::{Match, NoMatch, Unknown};
    let depth = ExecutionBudget {
        max_depth: Some(1),
        ..BUDGET
    };
    let breadth = ExecutionBudget {
        max_breadth: Some(NonZeroUsize::new(1).expect("nonzero")),
        ..BUDGET
    };
    let x_is_y = || {
        vec![TermRelation {
            left: nat("X"),
            right: nat("Y"),
        }]
    };
    type Row = (
        &'static str,
        Fixture,
        Pattern,
        fn(&EventVocabulary) -> PatternPlan,
        ExecutionBudget,
        Status,
        // The assumptions of each witness, in witness order.
        Vec<Vec<TermRelation>>,
    );
    let rows: Vec<Row> = vec![
        (
            "P1-WL-next",
            Fixture::Sym,
            p1(),
            wl_next,
            BUDGET,
            (Match, None),
            vec![vec![]],
        ),
        (
            "P1-WL-after",
            Fixture::Sym,
            p1(),
            wl_after,
            BUDGET,
            (Match, None),
            vec![vec![]],
        ),
        (
            "P2-WL-next",
            Fixture::Sym,
            p2(),
            wl_next,
            BUDGET,
            (NoMatch, None),
            vec![],
        ),
        (
            "P2-WL-after",
            Fixture::Sym,
            p2(),
            wl_after,
            BUDGET,
            (Match, None),
            vec![vec![]],
        ),
        (
            "P3-WL-after",
            Fixture::Sym,
            p3(),
            wl_after,
            BUDGET,
            (NoMatch, None),
            vec![],
        ),
        (
            "P4-WL-after",
            Fixture::Sym,
            p4(),
            wl_after,
            BUDGET,
            (NoMatch, None),
            vec![],
        ),
        (
            "P5-WL-after",
            Fixture::Sym,
            p5(),
            wl_after,
            BUDGET,
            (Match, None),
            vec![vec![]],
        ),
        (
            "P6-WL-after",
            Fixture::Sym,
            p6(),
            wl_after,
            BUDGET,
            (Match, None),
            vec![x_is_y()],
        ),
        (
            "P7-WL-after",
            Fixture::Sym,
            p7(),
            wl_after,
            BUDGET,
            (NoMatch, None),
            vec![],
        ),
        (
            "P8-WL-after",
            Fixture::Sym,
            p8(),
            wl_after,
            depth,
            (Unknown, Some(DepthLimit)),
            vec![],
        ),
        (
            "P8-W-only",
            Fixture::Sym,
            p8(),
            w_only,
            depth,
            (Match, None),
            vec![vec![]],
        ),
        (
            "P9-WL-after",
            Fixture::Sym,
            p9(),
            wl_after,
            breadth,
            (Unknown, Some(BranchLimit)),
            vec![],
        ),
        // README 13.4: a non-free injective symbol is undecided in both builds.
        (
            "symwrap-WL-after",
            Fixture::Wrap,
            wrap_program(),
            wl_after,
            BUDGET,
            (Unknown, Some(SolverUnknown)),
            vec![],
        ),
    ];
    let mut failures = Vec::new();
    for (id, fixture, program, plan, budget, status, assumptions) in rows {
        let (mut run, vocabulary) = run(fixture, program, budget);
        let plan = plan(&vocabulary);
        let paths = run.bridged.paths.clone();
        let [solver, unifier] = decided_by_both(&mut run, &plan, &paths);
        assert_witness_paths(&run, &solver);
        let actual = (
            (solver.outcome, solver.failure),
            solver
                .witnesses
                .iter()
                .map(|witness| witness.assumptions.clone())
                .collect::<Vec<_>>(),
        );
        if actual != (status, assumptions.clone()) {
            failures.push(format!(
                "{id} ({}): expected {:?}, got {actual:?}",
                PROFILE.name(),
                (status, assumptions)
            ));
        }
        if solver != unifier {
            failures.push(format!(
                "{id} ({}): the solver decider gave {solver:?}, the unifier alone {unifier:?}",
                PROFILE.name()
            ));
        }
        if matches!(solver.outcome, NoMatch) && !solver.complete_coverage {
            failures.push(format!("{id}: no-match without complete coverage"));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// A solver that answers `Sat` to every query, as Z3 does for a query whose user-sort terms it
/// abstracts into unrelated constants.
struct AlwaysSat;

impl SmtSolver for AlwaysSat {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        Ok(Ok(Satisfiability::Sat))
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        _checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        Ok(Err(SmtError::Unavailable))
    }
}

/// SYM-3B-03 (README 4.2): a solver `Sat` counts only for an exactly translated relation
/// query. P6's one path is given the path predicate `X = s(Y)` over `Nat`; with the candidate's
/// assumption `X = Y` the relation query `X = s(Y) ∧ X = Y` has no instance (occurs check), but
/// Z3 abstracts `s(Y)` into an unrelated constant and may answer `Sat`. No decider (the build's
/// solver, `NoSolver`, or a solver answering `Sat` to everything) turns that into a witness:
/// the result is `unknown` with an indeterminate candidate.
#[test]
fn z3_sat_on_abstracted_query_is_not_a_witness() {
    let (mut run, vocabulary) = run(Fixture::Sym, p6(), BUDGET);
    let plan = wl_after(&vocabulary);
    let mut paths = run.bridged.paths.clone();
    let [path] = paths.as_mut_slice() else {
        panic!("one path")
    };
    assert!(path.stop.has_real_prefix());
    let abstracted = Pattern::Equals {
        operand_sort: Box::new(kore_sort("SortNat")),
        result_sort: kore_sort("SortGeneratedTopCell"),
        left: Box::new(nat("X")),
        right: Box::new(s(nat("Y"))),
    };
    path.path_predicate = abstracted.clone();
    let [solver, unifier] = decided_by_both(&mut run, &plan, &paths);
    let state = run.state.clone();
    let (always_sat, z3_answer) = run
        .backend
        .with_solver(None, |definition, solver| {
            let relations = BackendRelations::shared(definition, &AlwaysSat, &state);
            let evaluation = evaluate_with(
                &run.context,
                &plan,
                &paths,
                &run.bridged.collection,
                None,
                EvaluationOptions {
                    stable_path_keys: true,
                    search_policy: SearchPolicy::Exhaustive,
                    input_error: false,
                },
                &relations,
            )
            .expect("evaluation");
            // The build's own solver on the relation query as `feasible` sends it.
            let term = |pattern: &Pattern| {
                definition
                    .admit_unverified(pattern, &[])
                    .internalize_term()
                    .expect("term")
            };
            let query = [
                definition
                    .admit_unverified(&abstracted, &[])
                    .internalize_predicate()
                    .expect("predicate")
                    .0,
                Predicate::Equals(term(&nat("X")), term(&nat("Y"))),
            ];
            let answer = solver
                .is_sat(&query, &Substitution::new())
                .map_err(Stop::into_cause);
            Ok::<_, k_rust::backend::BackendError>((
                evaluation,
                (answer, translation_exactness(&query) == Exactness::Exact),
            ))
        })
        .expect("backend definition");
    // Z3 answers `Sat` for the abstracted query although it has no instance; `NoSolver` is
    // unavailable.
    assert!(!z3_answer.1, "the query abstracts a user-sort term");
    assert_eq!(
        z3_answer.0,
        Ok(by_profile(
            Err(SmtError::Unavailable),
            Ok(Satisfiability::Sat)
        ))
    );
    for (decider, evaluation) in [
        ("build", solver),
        ("no-solver", unifier),
        ("always-sat", always_sat),
    ] {
        assert_eq!(
            (evaluation.outcome, evaluation.failure),
            (PatternOutcome::Unknown, Some(PathStop::SolverUnknown)),
            "{decider}: {evaluation:?}"
        );
        assert!(evaluation.witnesses.is_empty(), "{decider}");
    }
    // The unmodified path still matches under every decider: the rule refuses only the
    // abstracted query.
    let paths = run.bridged.paths.clone();
    for evaluation in decided_by_both(&mut run, &plan, &paths) {
        assert_eq!(evaluation.outcome, PatternOutcome::Match);
    }
}

/// `seq(write(addr(X), V), seq(op, seq(load(addr(address), W), halt)))` over `Int`.
fn write_op_load(op: Pattern, address: Pattern) -> Pattern {
    seq(
        write(addr(integer("X")), integer("V")),
        seq(op, seq(load(addr(address), integer("W")), halt())),
    )
}

/// SYM-3B-05 (README R16): rules whose applicability to a symbolic `Int` depends on its value
/// without a `requires` do not make a symbolic `Stuck` leaf wrongly complete. With Z3, k-rust
/// narrows a repeated rule variable (`copy(A, A)` against `copy(X, Y)`), an `Int` literal
/// (`pin(0)`), a `Bool` literal (`flag(true)`) and a literal with an `owise` fallback
/// (`pick(0)`): each run has the narrowed path with both events under the equation and a path
/// under its negation, both complete, and WL-after is a match. Without Z3 the narrowing is an
/// `Indeterminate` leaf.
#[test]
fn value_dependent_rule_patterns_are_narrowed_not_stuck() {
    use HaltClass::{Indeterminate, Stuck};
    use LeafFeasibility::{Solver, Syntactic};
    let pick = |op: &str, argument: Pattern| support::app(op, vec![argument]);
    let programs = [
        (
            "copy",
            support::app("Lblcopy", vec![integer("X"), integer("Y")]),
            1,
        ),
        ("pin", pick("Lblpin", integer("X")), 1),
        ("flag", pick("Lblflag", support::var("B", "SortBool")), 1),
        ("pick", pick("Lblpick", integer("X")), 2),
    ];
    for (id, op, negated_depth) in programs {
        let (mut run, vocabulary) = run(Fixture::Narrow, write_op_load(op, integer("X")), BUDGET);
        let mut rows = leaf_rows(&run)
            .into_iter()
            .zip(run.execution.leaves().iter().map(|leaf| leaf.branch.depth))
            .collect::<Vec<_>>();
        rows.sort_by_key(|(_, depth)| *depth);
        let expected = by_profile(
            vec![((Indeterminate, Syntactic, PathStop::SolverUnknown), 1)],
            // The narrowed path has both events (depth 3); the negated one stops at the op
            // (depth 1), or, for `pick`, takes the `owise` rule to `halt` (depth 2).
            vec![
                ((Stuck, Solver, PathStop::Terminal), negated_depth),
                ((Stuck, Solver, PathStop::Terminal), 3),
            ],
        );
        assert_eq!(rows, expected, "{id}");
        if PROFILE == SolverProfile::Z3 {
            assert!(
                run.bridged
                    .paths
                    .iter()
                    .all(|path| !matches!(path.path_predicate, Pattern::Top { .. })),
                "{id}: both paths carry the narrowing condition or its negation"
            );
        }
        assert_eq!(
            decided_outcome(&mut run, &gwl_after(&vocabulary)),
            by_profile(
                (PatternOutcome::Unknown, Some(PathStop::SolverUnknown)),
                (PatternOutcome::Match, None)
            ),
            "{id}"
        );
    }
}

/// A `Stuck` halt holds for every instance of its state in both profiles (k-rust KK-54/KK-55),
/// so a feasible stuck leaf of a definition without `ensures` is complete even when its state
/// keeps variables of any inhabited sort. After the write, `seq(pin(1), P)` clashes with the
/// `pin(0)` rule at a rigid domain value, whatever the program `P` is: every instance is stuck
/// after the write event, and no load follows. Before, only the Z3 profile claimed this, and only
/// for `Int`/`Bool` variables; the leaf was `SolverUnknown` and the result `unknown`.
#[test]
fn symbolic_stuck_leaf_is_complete_in_both_profiles() {
    use HaltClass::Stuck;
    use LeafFeasibility::Syntactic;
    let program = seq(
        write(addr(integer("X")), integer("V")),
        seq(
            support::app("Lblpin", vec![support::int(1)]),
            support::var("P", "SortProg"),
        ),
    );
    let (mut run, vocabulary) = run(Fixture::Narrow, program, BUDGET);
    assert_eq!(leaf_rows(&run), [(Stuck, Syntactic, PathStop::Terminal)]);
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert!(path.complete);
    assert_eq!(path.events.len(), 1);
    let terminal = path.execution_terminal.as_ref().expect("terminal");
    assert!(!terminal.state.free_variables().is_empty());
    assert_eq!(run.bridged.collection.stop, CollectionStop::SearchExhausted);
    let plan = gwl_after(&vocabulary);
    let plain = outcome(&run, &plan);
    assert_eq!(
        (plain.outcome, plain.failure),
        (PatternOutcome::NoMatch, None)
    );
    assert_eq!(
        decided_outcome(&mut run, &plan),
        (PatternOutcome::NoMatch, None)
    );
}

/// SYM-3B-05 (README R19): `&Int` is `smtlib(andInt)`, which k-rust declares as an
/// uninterpreted SMT function, and k-rust 347f693e's `smt::translates_exactly` did not count
/// that. Z3 answers `Sat` for `X &Int 1 ==Int 2` although no integer satisfies it, so k-rust
/// takes `gate` under that condition, and the leaf after the load was `Solver`-feasible,
/// complete and a witness: WL-after was a wrong `match` (every instance is stuck at `gate`
/// after the write). `translates_exactly` now rejects `smtlib` symbols (k-rust KK-48), so that
/// leaf, and the remainder stuck at `gate` under the negated condition, are `SolverUnknown`, and
/// the result is `unknown`.
#[test]
fn uninterpreted_smt_function_does_not_make_a_path_feasible() {
    use HaltClass::{Indeterminate, Stuck};
    use LeafFeasibility::{Syntactic, Unknown};
    let gate = support::app("Lblgate", vec![integer("X")]);
    let (mut run, vocabulary) = run(Fixture::Narrow, write_op_load(gate, integer("X")), BUDGET);
    assert_eq!(
        leaf_rows(&run),
        by_profile(
            vec![(Indeterminate, Syntactic, PathStop::SolverUnknown)],
            vec![(Stuck, Unknown, PathStop::SolverUnknown); 2]
        )
    );
    let plan = gwl_after(&vocabulary);
    let failure = PathStop::SolverUnknown;
    assert_both(&mut run, &plan, PatternOutcome::Unknown, Some(failure));
}

/// SYM-3B-05 (README R18): `half(A)` `requires 10 /Int A ==Int 10 /Int A`. The ground
/// instance `X = 0` is stuck at `half` after the write, so WL-after with a load from address
/// `0` is `no-match` for it; every other instance loads from `0` but writes elsewhere. k-rust
/// 347f693e simplified the symbolic condition to `true` without its definedness `X =/=Int 0`,
/// so the symbolic run had one leaf after both events with predicate `\top`, and the backend
/// decider matched it under the assumption `X = 0` (a wrong `match`, in both profiles); K-in-K2
/// then withheld every real prefix of symbolic runs over rules with partial functions. The
/// condition now states `X =/=Int 0` (k-rust KK-45/KK-46). Without a solver the step is
/// `Indeterminate` for want of one (`SolverUnknown`). With Z3 it splits like the ground run:
/// `halt` after both events under `X =/=Int 0`, and a stuck remainder at `half` after the write
/// only under `X = 0`; both are exactly feasible and complete, and the only candidate needs
/// `X = 0` on the first path, which Z3 refutes: `no-match`.
#[test]
fn dropped_definedness_condition_is_not_a_witness() {
    use HaltClass::{Indeterminate, Stuck};
    use LeafFeasibility::{Solver, Syntactic};
    let (mut symbolic, vocabulary) = run(
        Fixture::Partial,
        write_op_load(support::app("Lblhalf", vec![integer("X")]), support::int(0)),
        BUDGET,
    );
    assert_eq!(
        leaf_rows(&symbolic),
        by_profile(
            vec![(Indeterminate, Syntactic, PathStop::SolverUnknown)],
            vec![(Stuck, Solver, PathStop::Terminal); 2]
        )
    );
    let events = symbolic
        .bridged
        .paths
        .iter()
        .map(|path| path.events.len())
        .collect::<Vec<_>>();
    assert_eq!(events, by_profile(vec![1], vec![2, 1]));
    assert!(
        symbolic
            .bridged
            .paths
            .iter()
            .all(|path| cfg!(not(feature = "z3"))
                || !matches!(path.path_predicate, Pattern::Top { .. })),
        "every Z3 leaf carries X =/=Int 0 or its negation"
    );
    let plan = gwl_after(&vocabulary);
    let plain = outcome(&symbolic, &plan);
    // Under Z3 the structural decider cannot relate `X` to `0`.
    assert_eq!(
        (plain.outcome, plain.failure),
        (PatternOutcome::Unknown, Some(PathStop::SolverUnknown))
    );
    assert_eq!(
        decided_outcome(&mut symbolic, &plan),
        by_profile(
            (PatternOutcome::Unknown, Some(PathStop::SolverUnknown)),
            (PatternOutcome::NoMatch, None)
        )
    );

    // The ground instance `X = 0` (values `5`) stops at `half` after the write only.
    let five = || support::int(5);
    let (mut ground, _) = run(
        Fixture::Partial,
        seq(
            write(addr(support::int(0)), five()),
            seq(
                support::app("Lblhalf", vec![support::int(0)]),
                seq(load(addr(support::int(0)), five()), halt()),
            ),
        ),
        BUDGET,
    );
    let [path] = ground.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert_eq!((path.events.len(), path.stop), (1, PathStop::Terminal));
    assert_both(&mut ground, &plan, PatternOutcome::NoMatch, None);
}

/// `halflet` requires `L <=Int L` for `L = #let Y = X #in 10 /Int Y`: true wherever it is
/// defined, and defined exactly when `X =/=Int 0`, like `half`'s condition. The portable build
/// parses the rule since k-rust KK-72. Since KK-71 the generated lambda is a partial function (its
/// body `10 /Int Y` is), so the condition keeps its definedness: without a solver the step is
/// `Indeterminate`, and with Z3 it splits into `halt` after both events under `X =/=Int 0` and a
/// stuck remainder at `halflet` after the write. Against the pre-KK-71 snapshot `78cd00ca` the
/// lambda was `total`, and the Z3 run was one stuck `halt` leaf after both events with no
/// condition (syntactically feasible), so the instances `X = 0` were claimed to reach `halt`.
///
/// Unlike `half`'s, the remainder predicate is `\not(X =/=Int 0 /\ 10 /Int X <=Int 10 /Int X)`:
/// k-rust does not fold `<=Int` of equal terms, and a predicate with the partial `/Int` has no
/// exact SMT translation, so the remainder is not shown feasible and stays `SolverUnknown`. So
/// the symbolic result is `unknown` in both profiles, never the wrong `match`. The ground
/// instance `X = 0` stops at `halflet` after the write: `no-match`.
#[test]
fn let_bound_partial_condition_keeps_its_definedness() {
    use HaltClass::{Indeterminate, Stuck};
    use LeafFeasibility::{Solver, Syntactic, Unknown};
    let (mut symbolic, vocabulary) = run(
        Fixture::Partial,
        write_op_load(
            support::app("Lblhalflet", vec![integer("X")]),
            support::int(0),
        ),
        BUDGET,
    );
    assert_eq!(
        leaf_rows(&symbolic),
        by_profile(
            vec![(Indeterminate, Syntactic, PathStop::SolverUnknown)],
            vec![
                (Stuck, Solver, PathStop::Terminal),
                (Stuck, Unknown, PathStop::SolverUnknown),
            ]
        )
    );
    let events = symbolic
        .bridged
        .paths
        .iter()
        .map(|path| path.events.len())
        .collect::<Vec<_>>();
    // README 6.4 orders the write-only remainder before the write/load trace.
    assert_eq!(events, by_profile(vec![1], vec![1, 2]));
    if cfg!(feature = "z3") {
        let nonzero = Pattern::Not {
            sort: kore_sort("SortGeneratedTopCell"),
            argument: Box::new(Pattern::Equals {
                operand_sort: Box::new(kore_sort("SortInt")),
                result_sort: kore_sort("SortGeneratedTopCell"),
                left: Box::new(integer("X")),
                right: Box::new(support::int(0)),
            }),
        };
        assert_eq!(symbolic.bridged.paths[1].path_predicate, nonzero);
    }
    let plan = gwl_after(&vocabulary);
    assert_both(
        &mut symbolic,
        &plan,
        PatternOutcome::Unknown,
        Some(PathStop::SolverUnknown),
    );

    let five = || support::int(5);
    let (mut ground, _) = run(
        Fixture::Partial,
        seq(
            write(addr(support::int(0)), five()),
            seq(
                support::app("Lblhalflet", vec![support::int(0)]),
                seq(load(addr(support::int(0)), five()), halt()),
            ),
        ),
        BUDGET,
    );
    let [path] = ground.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert_eq!((path.events.len(), path.stop), (1, PathStop::Terminal));
    assert_both(&mut ground, &plan, PatternOutcome::NoMatch, None);
}

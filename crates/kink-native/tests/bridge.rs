//! Observed execution over the shared `testdata/k` definitions, read through the bridge into
//! kink-pattern paths, and over an inline KORE definition that reaches every halt reason. The
//! exhaustive leaf mapping tables are unit tests in `src/bridge.rs`, because adapted
//! responses cannot be built outside the crate.

#[path = "../../../testdata/k/support.rs"]
mod support;

#[path = "../../../testdata/k/step_support.rs"]
mod step_support;

use std::{cell::RefCell, num::NonZeroUsize, time::Duration};

use k_rust::backend::{Backend, BackendOptions};
use k_rust::definition::AttributeKey;
use k_rust::kast::{Sort as KastSort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
use k_rust::kore::{ast::Pattern, parser::parse_definition};
use kink_native::bridge::{BridgeContext, BridgedPaths, paths_from_steps};
use kink_native::execution::{
    AdaptedExecution, ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile,
};
use kink_native::feasibility::{BackendRelations, TestInitialState};
use kink_native::step_events::{ObservationDecider, StepEventSpec, StepObservation};
use kink_native::{NativeValidator, ValidatedDefinition, equivalent_compilation};
use kink_patch::{Edit, InsertPosition, Patch, TermRef};
use kink_pattern::{
    Atom, CollectionStop, Constructor, EvaluationContext, EvaluationOptions, EventVocabulary,
    ExecutionTerminalKind, MatchMode, PathStop, PatternArm, PatternOutcome, PatternPlan,
    PayloadClause, SearchPolicy, SymbolSorts, evaluate, evaluate_with,
};

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
};

fn counter_validator() -> NativeValidator {
    NativeValidator::bind(support::load("counter.k"), CompileOptions::default())
}

fn z() -> Pattern {
    kore_application("Lblz", Vec::new(), Vec::new())
}

fn s(pattern: Pattern) -> Pattern {
    kore_application("Lbls", Vec::new(), vec![pattern])
}

/// `counter(z, s(s(s(z))))`: three increments, one path.
fn t1() -> Pattern {
    support::initial_state(
        kore_application("Lblcounter", Vec::new(), vec![z(), s(s(s(z())))]),
        "SortCounter",
    )
}

/// `choose(true)`: `branch` fires, `fallback` does not.
fn t2() -> Pattern {
    support::initial_state(
        kore_application(
            "Lblchoose",
            Vec::new(),
            vec![Pattern::DomainValue {
                sort: kore_sort("SortBool"),
                value: "true".into(),
            }],
        ),
        "SortControl",
    )
}

fn symbol_sorts(side: &ValidatedDefinition) -> SymbolSorts {
    SymbolSorts::from_definition(
        &parse_definition(&side.artifacts().definition_kore).expect("compiled KORE parses"),
    )
}

#[test]
fn deleting_first_equal_copy_has_equivalent_compilation() {
    let validator = NativeValidator::bind(
        support::load("duplicate_unlabelled.k"),
        CompileOptions::default(),
    );
    let baseline = validator
        .compile_baseline()
        .expect("duplicate source compiles");
    let mutant = validator
        .validate(
            &Patch::new(vec![Edit::DeleteSentence {
                at: kink_patch::SentenceRef::new("DUPLICATE_UNLABELLED", 0),
            }])
            .expect("patch"),
        )
        .expect("deletion compiles");
    assert!(equivalent_compilation(&baseline, &mutant).expect("KORE parses"));
}

#[test]
fn deleting_second_equal_copy_has_equivalent_compilation() {
    let validator = NativeValidator::bind(
        support::load("duplicate_unlabelled.k"),
        CompileOptions::default(),
    );
    let baseline = validator
        .compile_baseline()
        .expect("duplicate source compiles");
    let mutant = validator
        .validate(
            &Patch::new(vec![Edit::DeleteSentence {
                at: kink_patch::SentenceRef::new("DUPLICATE_UNLABELLED", 1),
            }])
            .expect("patch"),
        )
        .expect("deletion compiles");
    assert!(equivalent_compilation(&baseline, &mutant).expect("KORE parses"));
}

#[test]
fn inserting_anonymous_clone_has_equivalent_compilation() {
    let validator = NativeValidator::bind(support::load("unlabelled.k"), CompileOptions::default());
    let rule = kink_patch::SentenceRef::new("UNLABELLED", 2);
    let mut clone = validator.baseline().sentence(&rule).expect("rule").clone();
    for key in [
        AttributeKey::Label,
        AttributeKey::UniqueId,
        AttributeKey::Origin,
        AttributeKey::Location,
        AttributeKey::Source,
        AttributeKey::SourceId,
        AttributeKey::SentenceStartOffset,
        AttributeKey::SentenceEndOffset,
        AttributeKey::ContentStartLine,
        AttributeKey::ContentStartColumn,
        AttributeKey::ContentStartOffset,
    ] {
        clone.attributes_mut().remove(key.as_str());
    }
    let patch = Patch::new(vec![Edit::InsertSentence {
        position: InsertPosition::After(rule.clone()),
        ordinal: 0,
        sentence: clone,
    }])
    .expect("patch");
    let baseline = validator.compile_baseline().expect("baseline compiles");
    let mutant = validator
        .validate(&patch)
        .expect("anonymous clone compiles");
    assert!(equivalent_compilation(&baseline, &mutant).expect("KORE parses"));
}

/// One observed run of `state` on a compiled side.
struct Run {
    execution: AdaptedExecution,
    bridged: BridgedPaths,
    context: EvaluationContext,
    baseline_backend: Option<RefCell<Backend>>,
    initial_state: Pattern,
}

fn run(
    validator: &NativeValidator,
    side: &ValidatedDefinition,
    module: &str,
    specs: &[StepEventSpec],
    vocabulary: &EventVocabulary,
    state: &Pattern,
    budget: ExecutionBudget,
) -> Run {
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .expect("backend");
    let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute_steps(&mut backend, state, budget)
        .expect("execution adapts")
        .expect("step run");
    let baseline = validator.compile_baseline().expect("baseline compiles");
    let mut baseline_backend = Backend::new(
        &baseline.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .expect("baseline backend");
    let observation = StepObservation::new(&mut baseline_backend, specs.to_vec())
        .expect("step declarations validate");
    assert_eq!(observation.vocabulary(), vocabulary);
    let sorts = symbol_sorts(&baseline);
    let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
    let bridged = baseline_backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(state));
            Ok::<_, k_rust::backend::BackendError>(
                paths_from_steps(
                    &BridgeContext {
                        test_id: "t",
                        classify: &normal,
                        sorts: &sorts,
                    },
                    &execution,
                    &observation,
                    &decider,
                )
                .expect("steps bridge"),
            )
        })
        .expect("baseline decider");
    Run {
        execution: execution.adapted,
        bridged,
        context: EvaluationContext {
            test_id: "t".to_owned(),
            bounds: budget.bounds(),
            vocabulary: vocabulary.clone(),
            symbol_sorts: sorts,
        },
        baseline_backend: Some(RefCell::new(baseline_backend)),
        initial_state: state.clone(),
    }
}

/// Declares a whole transition over the ND fixture's configurations.
fn nd_event(constructor: &str, pre: &str, post: &str) -> StepEventSpec {
    StepEventSpec {
        constructor: constructor.into(),
        pre: support::k_config(support::app(pre, vec![]), "SortS", "R", "C"),
        post: Some(support::k_config(
            support::app(post, vec![]),
            "SortS",
            "R",
            "C2",
        )),
        payload: Vec::new(),
    }
}

fn vocabulary(constructors: &[(&str, &[&str])]) -> EventVocabulary {
    EventVocabulary::new(
        constructors
            .iter()
            .map(|(name, sorts)| Constructor {
                name: (*name).to_owned(),
                payload_sorts: sorts.iter().map(|sort| kore_sort(sort)).collect(),
            })
            .collect(),
    )
    .expect("vocabulary")
}

/// A one-atom plan over `constructor`, binding `C` to its first payload when it has one.
fn single_atom(
    vocabulary: &EventVocabulary,
    constructor: &str,
    payload: Option<&str>,
) -> PatternPlan {
    PatternPlan::new(
        vocabulary,
        payload
            .map(|sort| vec![("C".to_owned(), kore_sort(sort))])
            .unwrap_or_default(),
        vec![PatternArm {
            atoms: vec![Atom {
                constructor: constructor.to_owned(),
                payload: payload
                    .map(|_| {
                        vec![PayloadClause {
                            position: 0,
                            mode: MatchMode::Bind,
                            variable: "C".to_owned(),
                        }]
                    })
                    .unwrap_or_default(),
            }],
            relations: Vec::new(),
        }],
        None,
    )
    .expect("plan")
}

fn outcome(run: &Run, plan: &PatternPlan) -> kink_pattern::Evaluation {
    if let Some(backend) = &run.baseline_backend {
        return backend
            .borrow_mut()
            .with_solver(None, |definition, solver| {
                let relations = BackendRelations::shared(
                    definition,
                    solver,
                    TestInitialState::of_test(&run.initial_state),
                );
                Ok::<_, k_rust::backend::BackendError>(
                    evaluate_with(
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
                        &relations,
                    )
                    .expect("evaluation"),
                )
            })
            .expect("baseline relations");
    }
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

#[test]
fn deterministic_runs_are_complete_under_path_set() {
    let validator = counter_validator();
    let baseline = validator.compile_baseline().expect("counter.k compiles");
    let specs = vec![step_support::counter(true).remove(0)];
    let vocabulary = vocabulary(&[("increment", &[])]);
    let run = run(
        &validator,
        &baseline,
        "COUNTER",
        &specs,
        &vocabulary,
        &t1(),
        BUDGET,
    );
    assert!(
        run.execution
            .leaves()
            .iter()
            .all(|leaf| leaf.diagnostics.is_empty())
    );
    assert_eq!(run.bridged.collection.stop, CollectionStop::SearchExhausted);
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path");
    };
    assert!(path.complete);
    assert_eq!(path.events.len(), 3);
    let terminal = path.execution_terminal.as_ref().expect("terminal");
    assert_eq!(
        terminal.state,
        support::initial_state(
            kore_application("Lblcounter", Vec::new(), vec![s(s(s(z()))), z()]),
            "SortCounter",
        )
    );
    let result = outcome(&run, &single_atom(&vocabulary, "increment", None));
    assert_eq!(result.outcome, PatternOutcome::Match);
    assert!(result.complete_coverage);
    assert_eq!(result.witnesses.len(), 3);
}

/// Finding 7 of the migration design: the mutant whose `branch` never applies still ends in
/// `selected(true)`, through `fallback`. Both executions have the same trace. Each side
/// emits the same whole-transition event because fallback performs the same step.
#[test]
fn observed_counter_and_fallback_mutant_match_the_same_transition() {
    let validator = counter_validator();
    let baseline = validator.compile_baseline().expect("counter.k compiles");
    let at = TermRef::new(support::rule(validator.baseline(), "COUNTER.branch"), [1]);
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: validator.baseline().term(&at).expect("requires").clone(),
        at,
        replacement: Term::Token {
            token: "false".to_owned(),
            sort: KastSort::new("Bool"),
        },
    }])
    .expect("one edit");
    let mutant = validator.validate(&patch).expect("the mutant compiles");
    let specs = vec![step_support::counter(true).remove(1)];
    let vocabulary = vocabulary(&[("branchTaken", &[])]);
    let plan = single_atom(&vocabulary, "branchTaken", None);
    let sides = [
        (&baseline, PatternOutcome::Match),
        (&mutant, PatternOutcome::Match),
    ];
    let mut finals = Vec::new();
    for (side, expected) in sides {
        let run = run(
            &validator,
            side,
            "COUNTER",
            &specs,
            &vocabulary,
            &t2(),
            BUDGET,
        );
        assert_eq!(run.bridged.collection.stop, CollectionStop::SearchExhausted);
        let result = outcome(&run, &plan);
        assert_eq!(result.outcome, expected);
        assert!(result.complete_coverage);
        let [path] = run.bridged.paths.as_slice() else {
            panic!("one path");
        };
        finals.push(path.execution_terminal.clone().expect("terminal").state);
    }
    assert_eq!(finals[0], finals[1], "the final state does not change");
}

#[test]
fn domain_payloads_decode_through_kore_json() {
    let validator = counter_validator();
    let baseline = validator.compile_baseline().expect("counter.k compiles");
    let mut increment = step_support::counter(true).remove(0);
    increment.constructor = "incremented".into();
    increment.post = Some(support::var("After", "SortGeneratedTopCell"));
    increment.payload = vec!["After".into()];
    let specs = vec![increment];
    let vocabulary = vocabulary(&[("incremented", &["SortGeneratedTopCell"])]);
    let run = run(
        &validator,
        &baseline,
        "COUNTER",
        &specs,
        &vocabulary,
        &t1(),
        BUDGET,
    );
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path");
    };
    let last = path.events.last().expect("three increments");
    assert_eq!(
        last.payload,
        [path.execution_terminal.clone().expect("terminal").state],
        "the last increment's after-state is the final configuration"
    );
    let result = outcome(
        &run,
        &single_atom(&vocabulary, "incremented", Some("SortGeneratedTopCell")),
    );
    assert_eq!(result.outcome, PatternOutcome::Match);
    assert_eq!(result.witnesses.len(), 3);
    assert_eq!(result.witnesses[2].bindings[0].term, last.payload[0]);
}

/// PathSet keeps both paths that converge on `done`, so an absent event is decidable.
#[test]
fn converging_branches_reach_pattern_no_match_with_both_events() {
    let validator = NativeValidator::bind(support::load("nd.k"), CompileOptions::default());
    let baseline = validator.compile_baseline().expect("nd.k compiles");
    let start = support::initial_state(
        kore_application("Lblstart", Vec::new(), Vec::new()),
        "SortS",
    );
    let vocabulary = vocabulary(&[("left", &[]), ("right", &[]), ("spin", &[])]);
    let run = run(
        &validator,
        &baseline,
        "ND",
        &[
            nd_event("left", "Lblstart", "Lblmid1"),
            nd_event("right", "Lblstart", "Lblmid2"),
            nd_event("spin", "Lblspin", "Lblspin"),
        ],
        &vocabulary,
        &start,
        BUDGET,
    );
    assert_eq!(run.bridged.collection.stop, CollectionStop::SearchExhausted);
    assert_eq!(run.bridged.paths.len(), 2);
    let observed = run
        .bridged
        .paths
        .iter()
        .map(|path| {
            assert!(path.complete);
            assert_eq!(path.events.len(), 1);
            path.events[0].constructor.as_str()
        })
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(observed, ["left", "right"].into());
    let result = outcome(&run, &single_atom(&vocabulary, "spin", None));
    assert_eq!(result.outcome, PatternOutcome::NoMatch);
    assert!(result.complete_coverage);
}

#[test]
fn depth_bound_ground_absence_is_unknown() {
    let validator = NativeValidator::bind(support::load("nd.k"), CompileOptions::default());
    let baseline = validator.compile_baseline().expect("nd.k compiles");
    let start = support::initial_state(
        kore_application("Lblstart", Vec::new(), Vec::new()),
        "SortS",
    );
    let vocabulary = vocabulary(&[("left", &[]), ("right", &[]), ("l2", &[])]);
    let run = run(
        &validator,
        &baseline,
        "ND",
        &[
            nd_event("left", "Lblstart", "Lblmid1"),
            nd_event("right", "Lblstart", "Lblmid2"),
            nd_event("l2", "Lblmid1", "Lbldone"),
        ],
        &vocabulary,
        &start,
        ExecutionBudget {
            max_depth: Some(1),
            ..BUDGET
        },
    );
    assert_eq!(run.bridged.paths.len(), 2);
    assert!(
        run.execution
            .leaves()
            .iter()
            .all(|leaf| leaf.halt == HaltClass::DepthBound)
    );
    assert!(
        run.bridged
            .paths
            .iter()
            .all(|path| path.stop == PathStop::DepthLimit)
    );
    assert_eq!(run.bridged.collection.stop, CollectionStop::DepthLimit);
    let left = outcome(&run, &single_atom(&vocabulary, "left", None));
    assert_eq!(left.outcome, PatternOutcome::Match);
    assert!(
        left.witnesses
            .iter()
            .any(|witness| witness.stop_reason == PathStop::DepthLimit)
    );
    let l2 = outcome(&run, &single_atom(&vocabulary, "l2", None));
    assert_eq!(l2.outcome, PatternOutcome::Unknown);
    assert_eq!(l2.failure, Some(PathStop::DepthLimit));
}

#[test]
fn breadth_bound_ground_absence_is_unknown() {
    let validator = NativeValidator::bind(support::load("nd.k"), CompileOptions::default());
    let baseline = validator.compile_baseline().expect("nd.k compiles");
    let start = support::initial_state(
        kore_application("Lblstart", Vec::new(), Vec::new()),
        "SortS",
    );
    let vocabulary = vocabulary(&[("left", &[]), ("right", &[]), ("l2", &[])]);
    let run = run(
        &validator,
        &baseline,
        "ND",
        &[
            nd_event("left", "Lblstart", "Lblmid1"),
            nd_event("right", "Lblstart", "Lblmid2"),
            nd_event("l2", "Lblmid1", "Lbldone"),
        ],
        &vocabulary,
        &start,
        ExecutionBudget {
            max_breadth: Some(NonZeroUsize::new(1).unwrap()),
            ..BUDGET
        },
    );
    assert_eq!(run.execution.leaves().len(), 2);
    assert!(
        run.execution
            .leaves()
            .iter()
            .all(|leaf| leaf.halt == HaltClass::BreadthBound)
    );
    // Re-pin R0b deliverable 4 (finding A-11): a breadth-bound leaf's state was never
    // normalised, so its path stops at `BackendLimit`, which vouches for no real prefix (was
    // `BranchLimit`, which did). The transition into it may be undefined on every instance, so
    // neither its event nor its term is evidence: a pattern over that transition is Unknown, not
    // a Match.
    assert_eq!(run.bridged.collection.stop, CollectionStop::BackendLimit);
    assert!(
        run.bridged
            .paths
            .iter()
            .all(|path| !path.complete && !path.stop.has_real_prefix())
    );
    let l2 = outcome(&run, &single_atom(&vocabulary, "l2", None));
    assert_eq!(l2.outcome, PatternOutcome::Unknown);
    assert_eq!(l2.failure, Some(PathStop::BackendLimit));
    for event in ["left", "right"] {
        let present = outcome(&run, &single_atom(&vocabulary, event, None));
        assert_eq!(present.outcome, PatternOutcome::Unknown, "{event}");
    }
}

/// Critique C2: a nonterminating run is cancelled by the watchdog and reported as timed out;
/// its leaf states are not decoded.
#[test]
fn nonterminating_execution_is_timeout() {
    let validator = NativeValidator::bind(support::load("nd.k"), CompileOptions::default());
    let baseline = validator.compile_baseline().expect("nd.k compiles");
    let spin = support::initial_state(kore_application("Lblspin", Vec::new(), Vec::new()), "SortS");
    let vocabulary = vocabulary(&[("spin", &[])]);
    let run = run(
        &validator,
        &baseline,
        "ND",
        &[nd_event("spin", "Lblspin", "Lblspin")],
        &vocabulary,
        &spin,
        ExecutionBudget {
            time: Duration::from_millis(200),
            ..BUDGET
        },
    );
    assert!(run.execution.timed_out());
    assert!(
        run.execution
            .leaves()
            .iter()
            .all(|leaf| leaf.halt == HaltClass::Cancelled)
    );
    assert!(run.bridged.paths.is_empty());
    assert_eq!(run.bridged.collection.stop, CollectionStop::TimeLimit);
    let result = outcome(&run, &single_atom(&vocabulary, "spin", None));
    assert_eq!(result.outcome, PatternOutcome::Unknown);
}

/// VI-03F: cancellation before the solver operation starts may return a backend error.
/// A zero wall-clock budget is TimeLimit in both profiles, with no complete path.
#[test]
fn zero_budget_execution_is_timeout() {
    let validator = NativeValidator::bind(support::load("nd.k"), CompileOptions::default());
    let baseline = validator.compile_baseline().expect("nd.k compiles");
    let spin = support::initial_state(kore_application("Lblspin", Vec::new(), Vec::new()), "SortS");
    let vocabulary = vocabulary(&[("spin", &[])]);
    let run = run(
        &validator,
        &baseline,
        "ND",
        &[nd_event("spin", "Lblspin", "Lblspin")],
        &vocabulary,
        &spin,
        ExecutionBudget {
            time: Duration::ZERO,
            ..BUDGET
        },
    );
    assert!(run.execution.timed_out());
    assert!(run.bridged.paths.is_empty());
    assert_eq!(run.bridged.collection.stop, CollectionStop::TimeLimit);
}

/// The side of `undecided.k` on which the rule `label` applies: its `requires false` is
/// replaced with `true`.
fn enabled(validator: &NativeValidator, label: &str) -> ValidatedDefinition {
    let at = TermRef::new(support::rule(validator.baseline(), label), [1]);
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: validator.baseline().term(&at).expect("requires").clone(),
        at,
        replacement: Term::Token {
            token: "true".to_owned(),
            sort: KastSort::new("Bool"),
        },
    }])
    .expect("one edit");
    validator
        .validate(&patch)
        .expect("the enabled side compiles")
}

/// A carried `ensures`, vacuous successor or diagnosed path has an event but no witness.
#[test]
fn undecided_live_occurrences_are_no_witness() {
    let validator = NativeValidator::bind(support::load("undecided.k"), CompileOptions::default());
    let baseline = validator.compile_baseline().expect("undecided.k compiles");
    let slow = enabled(&validator, "UNDECIDED.slow");
    let program = |symbol| kore_application(symbol, Vec::new(), Vec::new());
    let tight = ExecutionBudget {
        max_simplification_iterations: 3,
        ..BUDGET
    };
    // (id, side, observed rule, initial state, budget, leaf halt, path stop)
    #[rustfmt::skip]
    let rows = [
        ("carried-ensures", &baseline, "UNDECIDED.carryAlways", support::initial_state(program("LblcarryAlways"), "SortS"), BUDGET, HaltClass::Stuck, PathStop::SolverUnknown),
        ("vacuous-successor", &baseline, "UNDECIDED.step", support::deferred_vacuous_state(program("Lblvacuous"), "SortS"), BUDGET, HaltClass::Vacuous, PathStop::SolverUnknown),
        ("diagnosed-run", &slow, "UNDECIDED.slow", support::initial_state(program("Lbldraining"), "SortS"), tight, HaltClass::Stuck, PathStop::BackendLimit),
    ];
    for (id, side, label, state, budget, halt, stop) in rows {
        let constructor = label.rsplit('.').next().expect("label").to_owned();
        let symbol = match id {
            "carried-ensures" => "LblcarryAlways",
            "vacuous-successor" => "Lblvacuous",
            "diagnosed-run" => "Lbldraining",
            _ => unreachable!(),
        };
        let specs = [StepEventSpec {
            constructor: constructor.clone(),
            pre: support::k_config(program(symbol), "SortS", "R", "C"),
            post: None,
            payload: Vec::new(),
        }];
        let vocabulary = vocabulary(&[(constructor.as_str(), &[])]);
        let run = run(
            &validator,
            side,
            "UNDECIDED",
            &specs,
            &vocabulary,
            &state,
            budget,
        );
        if id == "carried-ensures" {
            assert_eq!(run.execution.leaves()[0].halt, HaltClass::Trivial);
            assert_eq!(run.bridged.paths[0].stop, PathStop::SolverUnknown);
            assert!(run.bridged.paths[0].events.is_empty());
        }
        let leaf = run.execution.leaves().last().expect("one successor leaf");
        let diagnostics = leaf
            .diagnostics
            .iter()
            .chain(leaf.candidate_diagnostics.iter().flatten())
            .chain(leaf.remainder_diagnostics.iter());
        let diagnostics = diagnostics.collect::<Vec<_>>();
        assert_eq!(
            !diagnostics.is_empty(),
            stop == PathStop::BackendLimit,
            "{id}"
        );
        if id == "diagnosed-run" {
            assert!(
                diagnostics.iter().any(|diagnostic| matches!(
                    diagnostic,
                    k_rust::backend::BackendDiagnosticOutput::SimplificationBudgetExhausted {
                        limit: 3,
                        ..
                    }
                )),
                "{id}: expected budget exhaustion, got {diagnostics:?}"
            );
        }
        assert_eq!(leaf.halt, halt, "{id}");
        if id == "vacuous-successor" {
            assert!(
                run.bridged.paths.is_empty(),
                "{id}: refuted leaf is discarded"
            );
            assert_eq!(
                outcome(&run, &single_atom(&vocabulary, &constructor, None)).outcome,
                PatternOutcome::NoMatch,
                "{id}"
            );
            continue;
        }
        let path = run.bridged.paths.last().expect("one successor path");
        assert_eq!(
            path.events
                .iter()
                .map(|event| event.constructor.as_str())
                .collect::<Vec<_>>(),
            [constructor.as_str()],
            "{id}: a step left the declared pre-state"
        );
        assert!(!path.complete, "{id}");
        assert_eq!(path.stop, stop, "{id}");
        let result = outcome(&run, &single_atom(&vocabulary, &constructor, None));
        assert_eq!(result.outcome, PatternOutcome::Unknown, "{id}");
        assert!(result.witnesses.is_empty(), "{id}");
        assert_eq!(result.failure, Some(stop), "{id}");
    }
}

// ---------------------------------------------------------------- SO-09 close-out audits

/// Attack (a) of the k-rust 927b9ce6 intake (VI-03F deliverable 4, T-DIAG): a request cancelled
/// before its operation starts. With Z3, k-rust's entry poll answers `Err("Request cancelled")`
/// instead of leaves; without Z3 the run returns `Cancelled` leaves. Either way a zero
/// wall-clock budget is a timeout on every adapter entry point, never an adapter failure
/// (Error) and never a complete path, even for counter `t1`, which terminates in three steps:
/// the event-free run and the stepped run bridge to no path with collection `TimeLimit`, and
/// the unobserved run reports `timed_out`. Identical in both profiles.
#[test]
fn audit_so_prestart_cancel_is_timeout_on_every_adapter_run() {
    let validator = counter_validator();
    let baseline = validator.compile_baseline().expect("counter.k compiles");
    let zero = ExecutionBudget {
        time: Duration::ZERO,
        ..BUDGET
    };
    let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
    let mut backend = Backend::new(
        &baseline.artifacts().definition_kore,
        "COUNTER",
        BackendOptions::default(),
    )
    .expect("backend");
    let sorts = symbol_sorts(&baseline);
    let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
    let context = BridgeContext {
        test_id: "t1",
        classify: &normal,
        sorts: &sorts,
    };

    let execution = adapter
        .execute(&mut backend, &t1(), zero)
        .expect("a pre-start cancel is not an adapter failure");
    assert!(execution.timed_out());
    let bridged = kink_native::bridge::paths_from_execution(&execution, &context, &|_| true)
        .expect("a timed-out run bridges");
    assert!(bridged.paths.is_empty());
    assert_eq!(bridged.collection.stop, CollectionStop::TimeLimit);

    let specs = vec![step_support::counter(true).remove(0)];
    let stepped = adapter
        .execute_steps(&mut backend, &t1(), zero)
        .expect("a pre-start cancel is not an adapter failure")
        .expect("no step-run failure");
    assert!(stepped.adapted.timed_out());
    assert!(stepped.states.is_empty());
    let observation = StepObservation::new(&mut backend, specs).expect("declarations validate");
    let bridged = backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(&t1()));
            Ok::<_, k_rust::backend::BackendError>(
                paths_from_steps(&context, &stepped, &observation, &decider)
                    .expect("a timed-out run bridges"),
            )
        })
        .expect("decider");
    assert!(bridged.paths.is_empty());
    assert_eq!(bridged.collection.stop, CollectionStop::TimeLimit);

    let unobserved = adapter
        .execute_unobserved(&mut backend, &t1(), zero)
        .expect("a pre-start cancel is not an adapter failure");
    assert!(unobserved.timed_out);
}

/// Attack (c) of the k-rust 927b9ce6 intake (T-DIAG): a leaf carrying `RuleConditionFailed`
/// (new in k-rust 7d3d8e69) is never complete. `rulecondfail.k`'s `f(X) => 1 requires X
/// +Float 1.0 >Float 0.0`; the mutant writes the literal `1.0f`, so the condition's
/// `FLOAT.add` meets mismatched formats, the equation stays unapplied, and k-rust attaches
/// `RuleConditionFailed { failure: Builtin(MismatchedFloatFormats) }`. Measured in both
/// profiles: every mutant leaf of `run(2.0)` and `done(f(2.0))` carries it, every path of both
/// bridges is incomplete `BackendLimit` (collection `BackendLimit`), and no leaf is discarded.
/// The baseline's runs are complete (`halt`), so the difference is visible only as Unknown.
///
/// Re-pin R0a (finding E-10; k-rust 19f7b3d90, 3f0feebbc, `MismatchedFloatFormats` removed): at
/// 501f18b9 an execution evaluates binary32 `+Float` binary64 exactly and rounds once to binary64,
/// so the condition holds, `f` applies, no leaf carries `RuleConditionFailed`, and the mutant's
/// paths are complete `Terminal` leaves whose final states equal the baseline's (both `halt`):
/// the mutant agrees here, nothing distinguishes. The binary64 destination is k-rust's choice
/// (decision 1: R0b refuses comparisons that reference such hooks); `RuleConditionFailed`
/// handling stays pinned generically (any leaf diagnostic makes the path incomplete).
#[test]
fn audit_so_rule_condition_failed_leaf_is_never_complete() {
    use k_rust::backend::BackendDiagnosticOutput;
    let validator =
        NativeValidator::bind(support::load("rulecondfail.k"), CompileOptions::default());
    let at = TermRef::new(
        support::rule(validator.baseline(), "RULECONDFAIL.f"),
        [1, 0, 1],
    );
    let literal = validator.baseline().term(&at).expect("the literal").clone();
    assert_eq!(
        literal,
        Term::Token {
            token: "1.0".into(),
            sort: KastSort::new("Float"),
        }
    );
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: literal,
        at,
        replacement: Term::Token {
            token: "1.0f".into(),
            sort: KastSort::new("Float"),
        },
    }])
    .expect("patch");
    let baseline = validator
        .compile_baseline()
        .expect("rulecondfail.k compiles");
    let mutant = validator.validate(&patch).expect("the mutant compiles");
    let float = Pattern::DomainValue {
        sort: kore_sort("SortFloat"),
        value: "2.0".into(),
    };
    let programs = [
        kore_application("Lblrun", Vec::new(), vec![float.clone()]),
        kore_application(
            "Lbldone",
            Vec::new(),
            vec![kore_application("Lblf", Vec::new(), vec![float])],
        ),
    ];
    let sorts = symbol_sorts(&baseline);
    let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
    let mut finals = std::collections::BTreeMap::new();
    for (label, side) in [("baseline", &baseline), ("mutant", &mutant)] {
        for program in &programs {
            let state = support::initial_state(program.clone(), "SortProg");
            let mut backend = Backend::new(
                &side.artifacts().definition_kore,
                "RULECONDFAIL",
                BackendOptions::default(),
            )
            .expect("backend");
            let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
            let execution = adapter
                .execute(&mut backend, &state, BUDGET)
                .expect("execution adapts");
            let stepped = adapter
                .execute_steps(&mut backend, &state, BUDGET)
                .expect("execution adapts")
                .expect("step run");
            let failed = |leaf: &kink_native::execution::AdaptedLeaf| {
                leaf.diagnostics.iter().any(|diagnostic| {
                    matches!(
                        diagnostic,
                        BackendDiagnosticOutput::RuleConditionFailed { .. }
                    )
                })
            };
            let context = BridgeContext {
                test_id: "rcf",
                classify: &normal,
                sorts: &sorts,
            };
            let observation =
                StepObservation::new(&mut backend, Vec::new()).expect("no declaration");
            let (event_free, steps) = backend
                .with_solver(None, |definition, solver| {
                    let decider = ObservationDecider::new(
                        definition,
                        solver,
                        TestInitialState::of_test(&state),
                    );
                    Ok::<_, k_rust::backend::BackendError>((
                        kink_native::bridge::paths_from_execution(&execution, &context, &|term| {
                            decider.definition_independent(term)
                        })
                        .expect("bridges"),
                        paths_from_steps(&context, &stepped, &observation, &decider)
                            .expect("steps bridge"),
                    ))
                })
                .expect("decider");
            let rows = event_free
                .paths
                .iter()
                .chain(&steps.paths)
                .map(|path| (path.complete, path.stop))
                .collect::<Vec<_>>();
            eprintln!(
                "SO-09 (c) {label} {program:?}: leaves {:?}; paths {rows:?}; collections {:?} {:?}",
                execution
                    .leaves()
                    .iter()
                    .map(|leaf| (leaf.halt, failed(leaf)))
                    .collect::<Vec<_>>(),
                event_free.collection.stop,
                steps.collection.stop,
            );
            // Both sides alike at 501f18b9 (E-10): no RuleConditionFailed, no discard, every
            // path a complete terminal, the collections exhausted.
            assert!(
                !execution.leaves().iter().any(failed),
                "{label} {program:?}"
            );
            assert!(
                execution
                    .leaves()
                    .iter()
                    .all(|leaf| kink_native::bridge::discarded(leaf).is_none())
            );
            assert!(!rows.is_empty());
            assert!(
                rows.iter().all(|row| *row == (true, PathStop::Terminal)),
                "{label} {program:?}: {rows:?}"
            );
            assert_eq!(event_free.collection.stop, CollectionStop::SearchExhausted);
            assert_eq!(steps.collection.stop, CollectionStop::SearchExhausted);
            finals.insert(
                (label, format!("{program:?}")),
                event_free
                    .paths
                    .iter()
                    .map(|path| path.execution_terminal.clone().expect("terminal").state)
                    .collect::<Vec<_>>(),
            );
        }
    }
    for program in &programs {
        let program = format!("{program:?}");
        assert_eq!(
            finals[&("mutant", program.clone())],
            finals[&("baseline", program.clone())],
            "{program}: the mutant agrees"
        );
    }
}

/// Attack (f) of the k-rust 927b9ce6 intake (T-EXACT, T-DIAG): every `StopCause` and
/// `InsufficientStack` ends in a non-complete stop. The match below is exhaustive over
/// `StopCause` at 927b9ce6 (no wildcard: a new variant fails to compile here) and mirrors the
/// facade's `stopped_halt_reason` (`k-rust/src/backend/mod.rs`): a stopped leaf is `Cancelled`
/// (Cancelled), `Timeout` (Deadline) or `SimplificationError` (StackExhausted), and a failed
/// solver prelude fails the operation. Each published halt maps to an incomplete path stop or a
/// contract violation, never to a complete leaf; each cause that fails an operation, and
/// `DefinitionError::InsufficientStack` (a refused request, published as a `BackendError`),
/// is an adapter `Backend` failure or a declaration `Internalization` failure, never a value.
#[test]
fn audit_so_every_stop_cause_is_a_non_complete_stop() {
    use k_rust::backend::{BackendError, HaltReasonOutput};
    use k_rust_backend::stop::{PreludeFailure, StackLimit, StopCause};
    use k_rust_backend::timeout::StepTimeoutMode;
    use kink_native::bridge::halt_stop;
    use kink_native::execution::ExecutionAdapterFailure;
    use kink_native::step_events::StepObservationError;
    fn published(cause: &StopCause) -> Option<HaltReasonOutput> {
        match cause {
            StopCause::Cancelled => Some(HaltReasonOutput::Cancelled),
            StopCause::Deadline(_) => Some(HaltReasonOutput::Timeout),
            StopCause::StackExhausted(_) => Some(HaltReasonOutput::SimplificationError),
            StopCause::SolverPrelude(_) => None,
        }
    }
    let causes = [
        StopCause::Cancelled,
        StopCause::Deadline(StepTimeoutMode::Manual(Duration::from_millis(1))),
        StopCause::Deadline(StepTimeoutMode::MovingAverage(Duration::from_millis(1))),
        StopCause::StackExhausted(StackLimit::ThreadBudget(1)),
        StopCause::StackExhausted(StackLimit::ProcessBudget(1)),
        StopCause::SolverPrelude(PreludeFailure::Inconsistent),
        StopCause::SolverPrelude(PreludeFailure::Unknown("unknown".into())),
    ];
    for cause in causes {
        if let Some(output) = published(&cause) {
            let halt = HaltClass::from_output(output);
            match halt_stop(halt) {
                Ok(Some(stop)) => assert!(
                    !matches!(
                        stop,
                        PathStop::Terminal | PathStop::Stuck | PathStop::UndefinedStep
                    ),
                    "{cause:?}: {stop:?}"
                ),
                Ok(None) => panic!("{cause:?}: {halt:?} may be a complete leaf"),
                Err(_) => {}
            }
        }
        assert!(matches!(
            ExecutionAdapterFailure::from(cause.clone()),
            ExecutionAdapterFailure::Backend(_)
        ));
        assert!(matches!(
            StepObservationError::from(cause),
            StepObservationError::Internalization(_)
        ));
    }
    let refused = || BackendError::new("InsufficientStack { depth: 1, required: 2, limit: 1 }");
    assert!(matches!(
        ExecutionAdapterFailure::from(refused()),
        ExecutionAdapterFailure::Backend(_)
    ));
    assert!(matches!(
        StepObservationError::from(refused()),
        StepObservationError::Internalization(_)
    ));
}

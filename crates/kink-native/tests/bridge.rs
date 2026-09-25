//! Observed execution over the shared `testdata/k` definitions, read through the bridge into
//! kink-pattern paths, and over an inline KORE definition that reaches every halt reason. The
//! exhaustive leaf mapping tables are unit tests in `src/bridge.rs`, because adapted
//! responses cannot be built outside the crate.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kast::{Sort as KastSort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
use k_rust::kore::{ast::Pattern, parser::parse_definition};
use kink_native::bridge::{BridgeContext, BridgedPaths, paths_from_execution};
use kink_native::execution::{
    AdaptedExecution, ExecutionAdapter, ExecutionBudget, ExecutionRoute, HaltClass,
};
use kink_native::observation::{DomainEventSpec, PayloadSource};
use kink_native::{ManifestFailure, NativeValidator, ObservedRule, ValidatedDefinition};
use kink_patch::{Edit, Patch, TermRef};
use kink_pattern::{
    Atom, CollectionStop, Constructor, EvaluationContext, EvaluationOptions, EventVocabulary,
    ExecutionBounds, ExecutionTerminalKind, MatchMode, PathStop, PatternArm, PatternOutcome,
    PatternPlan, PayloadClause, SearchPolicy, SymbolSorts, evaluate,
};

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
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

fn position(validator: &NativeValidator, label: &str) -> (String, k_rust::definition::Location) {
    let at = support::rule(validator.baseline(), label);
    let attrs = validator
        .baseline()
        .sentence(&at)
        .expect("rule")
        .attributes();
    (
        attrs.source().expect("source").to_owned(),
        attrs.location().expect("location"),
    )
}

fn rule_applied(label: &str) -> ObservedRule {
    let fixture = if label.starts_with("UNDECIDED.") {
        "undecided.k"
    } else if label.starts_with("ND.") {
        "nd.k"
    } else {
        "counter.k"
    };
    let baseline = support::load(fixture);
    ObservedRule {
        rule: support::rule(&baseline, label),
        emit_rule_applied: true,
        domain_events: Vec::new(),
    }
}

#[test]
fn mutated_unlabelled_rule_is_observed_on_both_sides() {
    let validator = NativeValidator::bind(support::load("unlabelled.k"), CompileOptions::default());
    let rule = kink_patch::SentenceRef::new("UNLABELLED", 2);
    let at = TermRef::new(rule.clone(), [0, 1]);
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: validator.baseline().term(&at).expect("right side").clone(),
        at,
        replacement: Term::apply("c", vec![]),
    }])
    .expect("patch");
    let baseline = validator.compile_baseline().expect("baseline");
    let mutant = validator.validate(&patch).expect("mutant");
    let state = support::initial_state(kore_application("Lblx", Vec::new(), Vec::new()), "SortS");
    for side in [&baseline, &mutant] {
        let manifest = validator
            .observation_manifest(
                side,
                &[ObservedRule {
                    rule: rule.clone(),
                    emit_rule_applied: true,
                    domain_events: Vec::new(),
                }],
            )
            .expect("manifest");
        let mut backend = Backend::new(
            &side.artifacts().definition_kore,
            "UNLABELLED",
            BackendOptions::default(),
        )
        .expect("backend");
        let execution = ExecutionAdapter::new(manifest)
            .execute(&mut backend, &state, BUDGET)
            .expect("observed execute");
        assert!(execution.leaves().iter().any(|leaf| leaf.branch.events.iter().any(|event| matches!(event, kink_native::observation::NativeEvent::RuleApplied(applied) if applied.rule == rule))));
    }
}

#[test]
fn deleted_unlabelled_rule_is_left_out() {
    let validator = NativeValidator::bind(support::load("unlabelled.k"), CompileOptions::default());
    let rule = kink_patch::SentenceRef::new("UNLABELLED", 2);
    let deleted = validator
        .validate(&Patch::new(vec![Edit::DeleteSentence { at: rule.clone() }]).expect("patch"))
        .expect("mutant");
    let manifest = validator
        .observation_manifest(
            &deleted,
            &[ObservedRule {
                rule,
                emit_rule_applied: true,
                domain_events: Vec::new(),
            }],
        )
        .expect("manifest");
    assert!(manifest.rules().next().is_none());
}

#[test]
fn identical_unlabelled_rules_are_not_observable() {
    let validator = NativeValidator::bind(
        support::load("duplicate_unlabelled.k"),
        CompileOptions::default(),
    );
    let side = validator
        .compile_baseline()
        .expect("duplicate source compiles");
    let rules = [0, 1].map(|index| ObservedRule {
        rule: kink_patch::SentenceRef::new("DUPLICATE_UNLABELLED", index),
        emit_rule_applied: true,
        domain_events: Vec::new(),
    });
    assert!(matches!(
        validator.observation_manifest(&side, &rules),
        Err(ManifestFailure::Installation(
            kink_native::observation::ObservationFailure::DuplicateRuleIdentity(_)
        ))
    ));
}

/// One observed run of `state` on a compiled side.
struct Run {
    execution: AdaptedExecution,
    bridged: BridgedPaths,
    context: EvaluationContext,
}

fn run(
    validator: &NativeValidator,
    side: &ValidatedDefinition,
    module: &str,
    rules: &[ObservedRule],
    vocabulary: &EventVocabulary,
    state: &Pattern,
    budget: ExecutionBudget,
) -> Run {
    let manifest = validator
        .observation_manifest(side, rules)
        .expect("manifest installs");
    let selected_rules = manifest.rules().cloned().collect();
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .expect("backend");
    let execution = ExecutionAdapter::new(manifest)
        .execute(&mut backend, state, budget)
        .expect("execution adapts");
    let sorts = symbol_sorts(side);
    let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
    let bridged = paths_from_execution(
        &execution,
        &BridgeContext {
            test_id: "t",
            classify: &normal,
            sorts: &sorts,
        },
    )
    .expect("execution bridges");
    Run {
        execution,
        bridged,
        context: EvaluationContext {
            test_id: "t".to_owned(),
            bounds: ExecutionBounds {
                depth: None,
                time_ms: Some(u64::try_from(budget.time.as_millis()).expect("budget")),
                branches: None,
                results: None,
            },
            vocabulary: vocabulary.clone(),
            selected_rules,
            symbol_sorts: sorts,
        },
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

/// Pins kink's copy of the spellings, read from k-rust's private `halt_reason`
/// (`backend/mod.rs:984-1002` at the ledger pin). It reads no k-rust output; a moved spelling
/// fails the execution module's `every_halt_spelling_is_produced_live` instead, and a new one is noticed by neither.
#[test]
fn every_halt_reason_string_maps_to_exactly_one_class() {
    let spellings = [
        "cancelled",
        "stuck",
        "trivial",
        "vacuous",
        "branch",
        "cut-point",
        "terminal",
        "depth-bound",
        "breadth-bound",
        "indeterminate",
        "unsupported-hook",
        "simplification-error",
        "timeout",
    ];
    let mut classes = spellings
        .iter()
        .map(|spelling| {
            let class = HaltClass::parse(spelling).unwrap_or_else(|| panic!("{spelling}"));
            assert_eq!(class.spelling(), *spelling);
            class
        })
        .collect::<Vec<_>>();
    classes.sort();
    classes.dedup();
    assert_eq!(classes, HaltClass::ALL, "one class per spelling");
    for unknown in ["", "Stuck", "stuck ", "depth_bound", "terminal-rule"] {
        assert_eq!(HaltClass::parse(unknown), None, "{unknown:?}");
    }
}

#[test]
fn deterministic_runs_are_complete_by_single_path_witness() {
    let validator = counter_validator();
    let baseline = validator.compile_baseline().expect("counter.k compiles");
    let rules = [rule_applied("COUNTER.increment")];
    let vocabulary = vocabulary(&[("rule:COUNTER.increment", &[])]);
    let run = run(
        &validator,
        &baseline,
        "COUNTER",
        &rules,
        &vocabulary,
        &t1(),
        BUDGET,
    );
    assert_eq!(run.execution.route(), ExecutionRoute::SinglePath);
    assert!(run.execution.diagnostics().is_empty());
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
    let result = outcome(
        &run,
        &single_atom(&vocabulary, "rule:COUNTER.increment", None),
    );
    assert_eq!(result.outcome, PatternOutcome::Match);
    assert!(result.complete_coverage);
    assert_eq!(result.witnesses.len(), 3);
}

/// Finding 7 of the migration design: the mutant whose `branch` never applies still ends in
/// `selected(true)`, through `fallback`, so only the observed trace tells it apart. Each side
/// resolves `COUNTER.branch` to its own `UNIQUE_ID`.
#[test]
fn observed_counter_execution_matches_branch_and_its_fallback_mutant_does_not() {
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
    assert_ne!(
        baseline.rule_identity(
            &position(&validator, "COUNTER.branch").0,
            position(&validator, "COUNTER.branch").1
        ),
        mutant.rule_identity(
            &position(&validator, "COUNTER.branch").0,
            position(&validator, "COUNTER.branch").1
        )
    );
    let rules = [ObservedRule {
        rule: support::rule(validator.baseline(), "COUNTER.branch"),
        emit_rule_applied: false,
        domain_events: vec![DomainEventSpec {
            constructor: "branchTaken".to_owned(),
            payload: Vec::new(),
        }],
    }];
    let vocabulary = vocabulary(&[("branchTaken", &[])]);
    let plan = single_atom(&vocabulary, "branchTaken", None);
    let sides = [
        (&baseline, PatternOutcome::Match),
        (&mutant, PatternOutcome::NoMatch),
    ];
    let mut finals = Vec::new();
    for (side, expected) in sides {
        let run = run(
            &validator,
            side,
            "COUNTER",
            &rules,
            &vocabulary,
            &t2(),
            BUDGET,
        );
        assert_eq!(run.execution.route(), ExecutionRoute::SinglePath);
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
    let rules = [ObservedRule {
        rule: support::rule(validator.baseline(), "COUNTER.increment"),
        emit_rule_applied: false,
        domain_events: vec![DomainEventSpec {
            constructor: "incremented".to_owned(),
            payload: vec![PayloadSource::AfterState],
        }],
    }];
    let vocabulary = vocabulary(&[("incremented", &["SortGeneratedTopCell"])]);
    let run = run(
        &validator,
        &baseline,
        "COUNTER",
        &rules,
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

/// Critique C1: k-rust merges the two branches of `start` into one `done` leaf and keeps
/// only one branch's events, so neither observed rule may be reported absent.
#[test]
fn converging_branches_never_yield_pattern_no_match() {
    let validator = NativeValidator::bind(support::load("nd.k"), CompileOptions::default());
    let baseline = validator.compile_baseline().expect("nd.k compiles");
    let start = support::initial_state(
        kore_application("Lblstart", Vec::new(), Vec::new()),
        "SortS",
    );
    for label in ["ND.left", "ND.right"] {
        let constructor = format!("rule:{label}");
        let vocabulary = vocabulary(&[(constructor.as_str(), &[])]);
        let run = run(
            &validator,
            &baseline,
            "ND",
            &[rule_applied(label)],
            &vocabulary,
            &start,
            BUDGET,
        );
        assert_eq!(run.execution.route(), ExecutionRoute::ExploreAll, "{label}");
        assert_eq!(
            run.bridged.collection.stop,
            CollectionStop::ExhaustionUnrecorded,
            "{label}"
        );
        let result = outcome(&run, &single_atom(&vocabulary, &constructor, None));
        assert_ne!(result.outcome, PatternOutcome::NoMatch, "{label}");
        assert!(!result.complete_coverage, "{label}");
    }
}

/// Critique C2: a nonterminating run is cancelled by the watchdog and reported as timed out;
/// its leaf states are not decoded.
#[test]
fn nonterminating_execution_is_timeout() {
    let validator = NativeValidator::bind(support::load("nd.k"), CompileOptions::default());
    let baseline = validator.compile_baseline().expect("nd.k compiles");
    let spin = support::initial_state(kore_application("Lblspin", Vec::new(), Vec::new()), "SortS");
    let vocabulary = vocabulary(&[("rule:ND.spin", &[])]);
    let run = run(
        &validator,
        &baseline,
        "ND",
        &[],
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
    let result = outcome(&run, &single_atom(&vocabulary, "rule:ND.spin", None));
    assert_eq!(result.outcome, PatternOutcome::Unknown);
}

/// Critique C7: a mutant side omits an observed position only when the patch deleted
/// its baseline rule; a position outside the authored baseline is a declaration error.
#[test]
fn deleted_observed_rule_is_omitted_from_the_mutant_manifest() {
    let validator = counter_validator();
    let baseline = validator.compile_baseline().expect("counter.k compiles");
    let deleted = validator
        .validate(
            &Patch::new(vec![Edit::DeleteSentence {
                at: support::rule(validator.baseline(), "COUNTER.fallback"),
            }])
            .expect("one edit"),
        )
        .expect("the mutant without fallback compiles");
    let rules = [
        rule_applied("COUNTER.branch"),
        rule_applied("COUNTER.fallback"),
    ];
    let labels = |side: &ValidatedDefinition| {
        validator
            .observation_manifest(side, &rules)
            .expect("manifest")
            .rules()
            .cloned()
            .collect::<Vec<_>>()
    };
    assert_eq!(
        labels(&baseline),
        [
            support::rule(validator.baseline(), "COUNTER.branch"),
            support::rule(validator.baseline(), "COUNTER.fallback")
        ]
    );
    assert_eq!(
        labels(&deleted),
        [support::rule(validator.baseline(), "COUNTER.branch")]
    );
    assert_eq!(
        validator.observation_manifest(
            &baseline,
            &[ObservedRule {
                rule: kink_patch::SentenceRef::new("COUNTER", 999),
                emit_rule_applied: true,
                domain_events: Vec::new()
            }]
        ),
        Err(ManifestFailure::UnknownRule(kink_patch::SentenceRef::new(
            "COUNTER", 999
        )))
    );
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

/// Review P1 over live k-rust: each run applies its observed rule, so its one path carries
/// that rule's event, but the path may be infeasible (a carried `ensures`, a vacuous
/// successor) or the run collected a backend diagnostic. The event is no witness: the
/// pattern is `Unknown`, never `Match`.
#[test]
fn undecided_live_occurrences_are_no_witness() {
    let validator = NativeValidator::bind(support::load("undecided.k"), CompileOptions::default());
    let baseline = validator.compile_baseline().expect("undecided.k compiles");
    let slow = enabled(&validator, "UNDECIDED.slow");
    let program = |symbol| kore_application(symbol, Vec::new(), Vec::new());
    let tight = ExecutionBudget {
        max_simplification_iterations: 2,
        ..BUDGET
    };
    // (id, side, observed rule, initial state, budget, route, leaf halt, path stop)
    #[rustfmt::skip]
    let rows = [
        ("carried-ensures", &baseline, "UNDECIDED.carryAlways", support::initial_state(program("LblcarryAlways"), "SortS"), BUDGET, ExecutionRoute::SinglePath, HaltClass::Stuck, PathStop::SolverUnknown),
        ("vacuous-successor", &baseline, "UNDECIDED.step", support::deferred_vacuous_state(program("Lblvacuous"), "SortS"), BUDGET, ExecutionRoute::ExploreAll, HaltClass::Vacuous, PathStop::SolverUnknown),
        ("diagnosed-run", &slow, "UNDECIDED.slow", support::initial_state(program("Lbldraining"), "SortS"), tight, ExecutionRoute::ExploreAll, HaltClass::Stuck, PathStop::BackendLimit),
    ];
    for (id, side, label, state, budget, route, halt, stop) in rows {
        let constructor = format!("rule:{label}");
        let vocabulary = vocabulary(&[(constructor.as_str(), &[])]);
        let run = run(
            &validator,
            side,
            "UNDECIDED",
            &[rule_applied(label)],
            &vocabulary,
            &state,
            budget,
        );
        assert_eq!(run.execution.route(), route, "{id}");
        assert_eq!(
            !run.execution.diagnostics().is_empty(),
            stop == PathStop::BackendLimit,
            "{id}"
        );
        let [leaf] = run.execution.leaves() else {
            panic!("{id}: one leaf");
        };
        assert_eq!(leaf.halt, halt, "{id}");
        let [path] = run.bridged.paths.as_slice() else {
            panic!("{id}: one path");
        };
        assert_eq!(
            path.events
                .iter()
                .map(|event| event.constructor.as_str())
                .collect::<Vec<_>>(),
            [constructor.as_str()],
            "{id}: the rule applied"
        );
        assert!(!path.complete, "{id}");
        assert_eq!(path.stop, stop, "{id}");
        let result = outcome(&run, &single_atom(&vocabulary, &constructor, None));
        assert_eq!(result.outcome, PatternOutcome::Unknown, "{id}");
        assert!(result.witnesses.is_empty(), "{id}");
        assert_eq!(result.failure, Some(stop), "{id}");
    }
}

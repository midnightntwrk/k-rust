//! Observed execution over the shared `testdata/k` definitions, read through the bridge into
//! kink-pattern paths, and over an inline KORE definition that reaches every halt reason. The
//! exhaustive leaf mapping tables are unit tests in `src/bridge.rs`, because adapted
//! responses cannot be built outside the crate.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::{num::NonZeroUsize, time::Duration};

use k_rust::backend::{Backend, BackendOptions};
use k_rust::definition::AttributeKey;
use k_rust::kast::{Sort as KastSort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
use k_rust::kore::{ast::Pattern, parser::parse_definition};
use kink_native::bridge::{BridgeContext, BridgedPaths, paths_from_execution};
use kink_native::execution::{AdaptedExecution, ExecutionAdapter, ExecutionBudget, HaltClass};
use kink_native::observation::{DomainEventSpec, PayloadSource};
use kink_native::{
    ManifestFailure, NativeValidator, ObservedRule, ValidatedDefinition, equivalent_compilation,
};
use kink_patch::{Edit, InsertPosition, Patch, TermRef};
use kink_pattern::{
    Atom, AttributionUnknownReason, CollectionStop, Constructor, EvaluationContext,
    EvaluationOptions, EventAttribution, EventVocabulary, ExecutionTerminalKind, MatchMode,
    PathStop, PatternArm, PatternOutcome, PatternPlan, PayloadClause, SearchPolicy, SymbolSorts,
    evaluate,
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

#[test]
fn observed_rule_merged_with_unobserved_author_is_unknown() {
    let validator = NativeValidator::bind(support::load("unlabelled.k"), CompileOptions::default());
    let observed = kink_patch::SentenceRef::new("UNLABELLED", 0);
    let unobserved = kink_patch::SentenceRef::new("UNLABELLED", 2);
    let mut replacement = validator.baseline().sentence(&unobserved).unwrap().clone();
    *replacement.attributes_mut() = validator
        .baseline()
        .sentence(&observed)
        .unwrap()
        .attributes()
        .clone();
    let patch = Patch::new(vec![Edit::ReplaceSentence {
        at: observed.clone(),
        replacement,
    }])
    .unwrap();
    let baseline = validator.compile_baseline().unwrap();
    let mutant = validator
        .validate(&patch)
        .expect("equal-rule mutant compiles");
    let rules = [ObservedRule {
        rule: observed.clone(),
        emit_rule_applied: true,
        domain_events: Vec::new(),
    }];
    let vocabulary = vocabulary(&[("rule:UNLABELLED:0", &[])]);
    let plan = single_atom(&vocabulary, "rule:UNLABELLED:0", None);
    let state = support::initial_state(kore_application("Lblx", Vec::new(), Vec::new()), "SortS");
    let baseline_run = run(
        &validator,
        &baseline,
        "UNLABELLED",
        &rules,
        &vocabulary,
        &state,
        BUDGET,
    );
    assert_eq!(
        outcome(&baseline_run, &plan).outcome,
        PatternOutcome::NoMatch
    );
    let mutant_run = run(
        &validator,
        &mutant,
        "UNLABELLED",
        &rules,
        &vocabulary,
        &state,
        BUDGET,
    );
    let result = outcome(&mutant_run, &plan);
    assert_eq!(result.outcome, PatternOutcome::Unknown);
    assert!(result.witnesses.is_empty());
    let [path] = mutant_run.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert!(matches!(
        &path.events[0].attribution,
        EventAttribution::Unknown(AttributionUnknownReason::DifferentObservationSpecs { authors })
            if authors.len() == 2
    ));
}

#[test]
fn two_equal_observed_rules_with_same_spec_attribute_normally() {
    let validator = NativeValidator::bind(support::load("unlabelled.k"), CompileOptions::default());
    let observed = kink_patch::SentenceRef::new("UNLABELLED", 0);
    let other = kink_patch::SentenceRef::new("UNLABELLED", 2);
    let mut replacement = validator.baseline().sentence(&other).unwrap().clone();
    *replacement.attributes_mut() = validator
        .baseline()
        .sentence(&observed)
        .unwrap()
        .attributes()
        .clone();
    let side = validator
        .validate(
            &Patch::new(vec![Edit::ReplaceSentence {
                at: observed.clone(),
                replacement,
            }])
            .unwrap(),
        )
        .unwrap();
    let rules = [observed, other].map(|rule| ObservedRule {
        rule,
        emit_rule_applied: false,
        domain_events: vec![DomainEventSpec {
            constructor: "fired".into(),
            payload: Vec::new(),
        }],
    });
    let vocabulary = vocabulary(&[("fired", &[])]);
    let state = support::initial_state(kore_application("Lblx", Vec::new(), Vec::new()), "SortS");
    let execution = run(
        &validator,
        &side,
        "UNLABELLED",
        &rules,
        &vocabulary,
        &state,
        BUDGET,
    );
    let result = outcome(&execution, &single_atom(&vocabulary, "fired", None));
    assert_eq!(result.outcome, PatternOutcome::Match);
    let [path] = execution.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert!(matches!(
        path.events[0].attribution,
        EventAttribution::Certain
    ));
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
    assert!(!equivalent_compilation(&baseline, &mutant).expect("KORE parses"));
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
            bounds: budget.bounds(),
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

#[test]
fn deterministic_runs_are_complete_under_path_set() {
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

/// PathSet keeps both paths that converge on `done`, so an absent event is decidable.
#[test]
fn converging_branches_reach_pattern_no_match_with_both_events() {
    let validator = NativeValidator::bind(support::load("nd.k"), CompileOptions::default());
    let baseline = validator.compile_baseline().expect("nd.k compiles");
    let start = support::initial_state(
        kore_application("Lblstart", Vec::new(), Vec::new()),
        "SortS",
    );
    let vocabulary = vocabulary(&[
        ("rule:ND.left", &[]),
        ("rule:ND.right", &[]),
        ("rule:ND.spin", &[]),
    ]);
    let run = run(
        &validator,
        &baseline,
        "ND",
        &[
            rule_applied("ND.left"),
            rule_applied("ND.right"),
            rule_applied("ND.spin"),
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
    assert_eq!(observed, ["rule:ND.left", "rule:ND.right"].into());
    let result = outcome(&run, &single_atom(&vocabulary, "rule:ND.spin", None));
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
    let vocabulary = vocabulary(&[
        ("rule:ND.left", &[]),
        ("rule:ND.right", &[]),
        ("rule:ND.l2", &[]),
    ]);
    let run = run(
        &validator,
        &baseline,
        "ND",
        &[
            rule_applied("ND.left"),
            rule_applied("ND.right"),
            rule_applied("ND.l2"),
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
    let left = outcome(&run, &single_atom(&vocabulary, "rule:ND.left", None));
    assert_eq!(left.outcome, PatternOutcome::Match);
    assert!(
        left.witnesses
            .iter()
            .any(|witness| witness.stop_reason == PathStop::DepthLimit)
    );
    let l2 = outcome(&run, &single_atom(&vocabulary, "rule:ND.l2", None));
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
    let vocabulary = vocabulary(&[
        ("rule:ND.left", &[]),
        ("rule:ND.right", &[]),
        ("rule:ND.l2", &[]),
    ]);
    let run = run(
        &validator,
        &baseline,
        "ND",
        &[
            rule_applied("ND.left"),
            rule_applied("ND.right"),
            rule_applied("ND.l2"),
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
    assert_eq!(run.bridged.collection.stop, CollectionStop::BranchLimit);
    let l2 = outcome(&run, &single_atom(&vocabulary, "rule:ND.l2", None));
    assert_eq!(l2.outcome, PatternOutcome::Unknown);
    assert_eq!(l2.failure, Some(PathStop::BranchLimit));
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
        let [leaf] = run.execution.leaves() else {
            panic!("{id}: one leaf");
        };
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

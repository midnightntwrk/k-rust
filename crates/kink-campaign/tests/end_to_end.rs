//! Campaigns run end to end through kink-native over the shared `testdata/k` definitions.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions, SearchRequest};
use k_rust::kast::{Sort as KastSort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
use k_rust::kore::{ast::Pattern, codec, parser::parse_definition, walk};
use kink_campaign::{
    Campaign, CampaignFailureKind, CrashPolicy, ExecutionFailureKind, MutantScopeFailure,
    MutantStatus, OracleDeclaration, OracleOutcome, OracleSide, OracleValue, PatternValue,
    Projection, Rational, ScheduleMode, SideRun, StateProjection, TestCase, TestEvidence, TestPlan,
    TestRun, derive_mutant_report, run_campaign, state_side,
};
use kink_native::bridge::{BridgeContext, paths_from_execution, paths_from_search};
use kink_native::execution::{ExecutionAdapter, ExecutionBudget, ExecutionRoute};
use kink_native::observation::DomainEventSpec;
use kink_native::search::{SearchAdapter, SolverProfile};
use kink_native::{NativeValidator, ObservedRule};
use kink_patch::{Baseline, Edit, Patch, TermRef};
use kink_pattern::{
    Atom, Constructor, EventVocabulary, ExecutionTerminalKind, OriginMode, PatternArm, PatternPlan,
    SymbolSorts,
};
use serde_json::Value;

use OracleOutcome::{Agree, Distinguish};

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
};

/// Runs `body` with stack headroom for compilation and execution.
fn with_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 << 20)
        .spawn(body)
        .expect("test thread")
        .join()
        .expect("test thread does not panic");
}

fn constant(symbol: &str) -> Pattern {
    kore_application(symbol, Vec::new(), Vec::new())
}

fn z() -> Pattern {
    constant("Lblz")
}

fn s(pattern: Pattern) -> Pattern {
    kore_application("Lbls", Vec::new(), vec![pattern])
}

fn bool_value(value: &str) -> Pattern {
    Pattern::DomainValue {
        sort: kore_sort("SortBool"),
        value: value.into(),
    }
}

fn bool_token(value: &str) -> Term {
    Term::Token {
        token: value.to_owned(),
        sort: KastSort::new("Bool"),
    }
}

/// `counter(z, s(s(s(z))))`: three increments, one path.
fn counter_state() -> Pattern {
    support::initial_state(
        kore_application("Lblcounter", Vec::new(), vec![z(), s(s(s(z())))]),
        "SortCounter",
    )
}

/// `choose(true)`: `branch` fires, `fallback` does not.
fn choose_state() -> Pattern {
    support::initial_state(
        kore_application("Lblchoose", Vec::new(), vec![bool_value("true")]),
        "SortControl",
    )
}

fn vocabulary(names: &[&str]) -> EventVocabulary {
    EventVocabulary::new(
        names
            .iter()
            .map(|name| Constructor {
                name: (*name).to_owned(),
                payload_sorts: Vec::new(),
                origin_mode: OriginMode::EmittingSentence,
            })
            .collect(),
    )
    .expect("vocabulary")
}

/// A pattern oracle whose one atom is `constructor`.
fn occurs(vocabulary: &EventVocabulary, constructor: &str) -> OracleDeclaration {
    let plan = PatternPlan::new(
        vocabulary,
        Vec::new(),
        vec![PatternArm {
            atoms: vec![Atom {
                constructor: constructor.to_owned(),
                payload: Vec::new(),
            }],
            relations: Vec::new(),
        }],
        None,
    )
    .expect("plan");
    OracleDeclaration::new(
        CrashPolicy::CompareIdentity,
        Projection::Pattern {
            plan,
            with_bindings: false,
        },
    )
    .expect("pattern declaration")
}

fn whole_term(crash_policy: CrashPolicy) -> OracleDeclaration {
    OracleDeclaration::new(crash_policy, Projection::State(StateProjection::WholeTerm))
        .expect("final-result declaration")
}

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

/// Replaces the term at `path` of the rule `label` with `replacement`.
fn replace(baseline: &Baseline, label: &str, path: &[u32], replacement: Term) -> Patch {
    let at = TermRef::new(support::rule(baseline, label), path);
    Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("baseline term").clone(),
        at,
        replacement,
    }])
    .expect("one edit")
}

fn term_at(baseline: &Baseline, label: &str, path: &[u32]) -> Term {
    baseline
        .term(&TermRef::new(support::rule(baseline, label), path))
        .expect("baseline term")
        .clone()
}

fn outcomes(tests: &[TestPlan]) -> Vec<(&str, Vec<OracleOutcome>)> {
    tests
        .iter()
        .map(|test| match &test.run {
            TestRun::Compared(outcomes) => (test.test_id.as_str(), outcomes.clone()),
            TestRun::Failed(kind) => panic!("{}: failed {kind:?}", test.test_id),
        })
        .collect()
}

fn sides(evidence: &TestEvidence) -> &[OracleSide] {
    match &evidence.run {
        SideRun::Sides { route, sides } => {
            // Critique C1: every counter run is one complete path.
            assert_eq!(*route, ExecutionRoute::SinglePath, "{}", evidence.test_id);
            sides
        }
        SideRun::Failed(kind) => panic!("{}: failed {kind:?}", evidence.test_id),
    }
}

/// Plan row C5 and finding 7 of the migration design: one mutant is killed by its final
/// result, one by an execution pattern while its final result is unchanged, one survives,
/// and one is invalid and never runs. Observed rules resolve to each side's own
/// `UNIQUE_ID`: the increment mutant's mutated rule is still observed on `t1`.
#[test]
fn counter_campaign_kills_by_final_result_and_by_pattern_with_unchanged_final_result() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let vocabulary = vocabulary(&["rule:COUNTER.increment", "branchTaken"]);
        let observed_rules = [
            ObservedRule {
                label: "COUNTER.increment".to_owned(),
                emit_rule_applied: true,
                domain_events: Vec::new(),
            },
            ObservedRule {
                label: "COUNTER.branch".to_owned(),
                emit_rule_applied: false,
                domain_events: vec![DomainEventSpec {
                    constructor: "branchTaken".to_owned(),
                    payload: Vec::new(),
                }],
            },
        ];
        let tests = [
            TestCase {
                id: "t1".to_owned(),
                initial_state: counter_state(),
                oracles: vec![
                    whole_term(CrashPolicy::CompareIdentity),
                    occurs(&vocabulary, "rule:COUNTER.increment"),
                ],
            },
            TestCase {
                id: "t2".to_owned(),
                initial_state: choose_state(),
                oracles: vec![
                    whole_term(CrashPolicy::CompareIdentity),
                    occurs(&vocabulary, "branchTaken"),
                ],
            },
        ];
        let mutants = [
            // increment: counter(N, s(L)) => counter(N, L)
            replace(
                baseline,
                "COUNTER.increment",
                &[0, 1, 0],
                term_at(baseline, "COUNTER.increment", &[0, 1, 0, 0]),
            ),
            // branch: requires false; fallback still ends in selected(true).
            replace(baseline, "COUNTER.branch", &[1], bool_token("false")),
            // fallback: choose(B) => selected(true); it never fires on these tests.
            replace(baseline, "COUNTER.fallback", &[0, 1, 0], bool_token("true")),
            // k-rust rejects the unknown attribute.
            Patch::new(vec![Edit::AddAttribute {
                at: support::rule(baseline, "COUNTER.increment"),
                key: "foo".to_owned(),
                value: Value::String(String::new()),
            }])
            .expect("one edit"),
        ];
        let campaign = Campaign {
            validator: &validator,
            module: "COUNTER",
            observed_rules: &observed_rules,
            vocabulary: &vocabulary,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let run = run_campaign(&campaign, &mutants, ScheduleMode::Full).expect("admitted");

        let final_state = |program| {
            OracleSide::Normal(OracleValue::FinalResult(
                kink_campaign::FinalResult::WholeTerm([program].into_iter().collect()),
            ))
        };
        let matched =
            OracleSide::Normal(OracleValue::Pattern(PatternValue::Match { bindings: None }));
        let t1_final = support::initial_state(
            kore_application("Lblcounter", Vec::new(), vec![s(s(s(z()))), z()]),
            "SortCounter",
        );
        let t2_final = support::initial_state(
            kore_application("Lblselected", Vec::new(), vec![bool_value("true")]),
            "SortControl",
        );
        assert_eq!(
            sides(&run.baseline[0]),
            [final_state(t1_final), matched.clone()]
        );
        assert_eq!(
            sides(&run.baseline[1]),
            [final_state(t2_final.clone()), matched]
        );

        let statuses = run
            .mutants
            .iter()
            .map(|mutant| mutant.report.status)
            .collect::<Vec<_>>();
        use MutantStatus::{Invalid, Killed, Survived};
        assert_eq!(statuses, [Killed, Killed, Survived, Invalid]);
        #[rustfmt::skip]
        let expected: [&[(&str, Vec<OracleOutcome>)]; 3] = [
            &[("t1", vec![Distinguish, Agree]), ("t2", vec![Agree, Agree])],
            &[("t1", vec![Agree, Agree]), ("t2", vec![Agree, Distinguish])],
            &[("t1", vec![Agree, Agree]), ("t2", vec![Agree, Agree])],
        ];
        for (mutant, expected) in run.mutants.iter().zip(expected) {
            let id = mutant.plan.mutant_id;
            assert_eq!(outcomes(&mutant.plan.tests), expected, "{id:?}");
            assert_eq!(mutant.plan.mutant_failure, None, "{id:?}");
            for evidence in &mutant.evidence {
                sides(evidence);
            }
        }
        // The branch mutant ends where the baseline does, but branch never fires.
        assert_eq!(
            sides(&run.mutants[1].evidence[1]),
            [
                final_state(t2_final),
                OracleSide::Normal(OracleValue::Pattern(PatternValue::NoMatch))
            ]
        );
        let invalid = &run.mutants[3];
        assert_eq!(
            invalid.plan.mutant_failure,
            Some(MutantScopeFailure::Rejected)
        );
        assert!(invalid.plan.tests.is_empty());
        assert!(invalid.evidence.is_empty());
        assert!(invalid.report.executed_test_ids.is_empty());

        assert_eq!((run.score.killed, run.score.survived), (2, 1));
        assert_eq!(
            run.score.ratio,
            Some(Rational {
                numerator: 2,
                denominator: 3
            })
        );

        // Under first-kill, the killing prefix is t1 for the increment mutant and t2 for
        // the branch mutant, and every status is unchanged.
        let manifest = tests
            .iter()
            .map(|test| kink_campaign::ManifestTest {
                test_id: test.id.clone(),
                slot_count: test.oracles.len(),
            })
            .collect::<Vec<_>>();
        #[rustfmt::skip]
        let first_kill: [(&[&str], &[&str]); 4] = [
            (&["t1"], &["t1"]),
            (&["t1", "t2"], &["t2"]),
            (&["t1", "t2"], &[]),
            (&[], &[]),
        ];
        for (mutant, (executed, killing)) in run.mutants.iter().zip(first_kill) {
            let report = derive_mutant_report(&mutant.plan, &manifest, ScheduleMode::FirstKill)
                .expect("report");
            assert_eq!(report.status, mutant.report.status);
            assert_eq!(report.executed_test_ids, executed);
            assert_eq!(report.killing_test_ids, killing);
        }
    });
}

/// Critique C2 through the runner: a mutant that no longer terminates is stopped by the
/// watchdog, its test fails with `TimeLimit`, and the mutant is `Timeout`, never killed.
#[test]
fn nonterminating_mutant_is_a_timeout() {
    with_stack(|| {
        let validator = NativeValidator::bind(support::load("nd.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let vocabulary = vocabulary(&["unused"]);
        let tests = [TestCase {
            id: "mid1".to_owned(),
            initial_state: support::initial_state(constant("Lblmid1"), "SortS"),
            oracles: vec![whole_term(CrashPolicy::CompareIdentity)],
        }];
        // l2: mid1 => spin, and spin => spin forever.
        let spin = replace(
            baseline,
            "ND.l2",
            &[0, 1],
            term_at(baseline, "ND.spin", &[0, 1]),
        );
        let campaign = Campaign {
            validator: &validator,
            module: "ND",
            observed_rules: &[],
            vocabulary: &vocabulary,
            classify: &normal,
            tests: &tests,
            budget: ExecutionBudget {
                time: Duration::from_secs(2),
                ..BUDGET
            },
        };
        let run = run_campaign(&campaign, &[spin], ScheduleMode::Full).expect("admitted");
        sides(&run.baseline[0]);
        let [mutant] = run.mutants.as_slice() else {
            panic!("one mutant");
        };
        assert_eq!(
            mutant.plan.tests[0].run,
            TestRun::Failed(ExecutionFailureKind::TimeLimit)
        );
        assert_eq!(mutant.report.status, MutantStatus::Timeout);
        assert_eq!(run.score.denominator, 0);
    });
}

/// Whether `term` contains an application of `symbol`.
fn contains(term: &Pattern, symbol: &str) -> bool {
    matches!(term, Pattern::Application { symbol: head, .. } if head.name == symbol)
        || walk::children(term)
            .into_iter()
            .any(|child| contains(child, symbol))
}

/// Critique C6 and C7: the baseline gate runs before any mutant. A baseline crash its
/// declaration rejects fails admission, one it admits is a crash side carrying its
/// terminal term, and an observed label the baseline does not have is a declaration
/// error.
#[test]
fn baseline_admission_gates_crashes_and_unknown_labels() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let vocabulary = vocabulary(&["unused"]);
        let selected_is_a_crash = |term: &Pattern| {
            if contains(term, "Lblselected") {
                ExecutionTerminalKind::SemanticCrash
            } else {
                ExecutionTerminalKind::Normal
            }
        };
        let tests = |crash_policy| {
            [TestCase {
                id: "t2".to_owned(),
                initial_state: choose_state(),
                oracles: vec![whole_term(crash_policy)],
            }]
        };
        let rules = |label: &str| {
            [ObservedRule {
                label: label.to_owned(),
                emit_rule_applied: true,
                domain_events: Vec::new(),
            }]
        };
        let run = |crash_policy, observed: &[ObservedRule]| {
            let tests = tests(crash_policy);
            run_campaign(
                &Campaign {
                    validator: &validator,
                    module: "COUNTER",
                    observed_rules: observed,
                    vocabulary: &vocabulary,
                    classify: &selected_is_a_crash,
                    tests: &tests,
                    budget: BUDGET,
                },
                &[],
                ScheduleMode::Full,
            )
        };

        let rejected = run(CrashPolicy::Reject, &[]).expect_err("crash rejected");
        assert_eq!(rejected.kind(), CampaignFailureKind::BaselineOracleFailed);

        let unknown = run(CrashPolicy::CompareIdentity, &rules("COUNTER.nothing"))
            .expect_err("unknown label");
        assert_eq!(unknown.kind(), CampaignFailureKind::InvalidDeclaration);

        let admitted = run(CrashPolicy::CompareIdentity, &rules("COUNTER.branch"))
            .expect("a crash is admitted under CompareIdentity");
        let OracleSide::SemanticCrash(term) = &sides(&admitted.baseline[0])[0] else {
            panic!("a crash side");
        };
        assert!(contains(term, "Lblselected"));
        assert_eq!(admitted.score.denominator, 0);
    });
}

/// Review P1 through the runner, over `undecided.k`: an occurrence on a path whose
/// feasibility is undecided, or in a run that collected a backend diagnostic, is no witness,
/// so the pattern side is `Unknown`. A mutant that makes `carry` (a carried `ensures`) or
/// `slow` (a simplifier-budget diagnostic) apply is therefore not killed against the
/// baseline's complete absence, and a baseline whose only occurrence is undecided (a carried
/// `ensures`, a vacuous successor) is not admitted.
#[test]
fn undecided_occurrences_neither_kill_nor_pass_admission() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("undecided.k"), CompileOptions::default());
        let baseline = validator.baseline();
        // The vocabulary, test and observed rule of a pattern oracle over `label`'s event.
        let declared = |label: &str, initial_state| {
            let constructor = format!("rule:{label}");
            let vocabulary = vocabulary(&[constructor.as_str()]);
            let tests = [TestCase {
                id: "t".to_owned(),
                initial_state,
                oracles: vec![occurs(&vocabulary, &constructor)],
            }];
            (vocabulary, tests, [rule_applied(label)])
        };

        // (id, mutated rule, initial program, simplifier iterations)
        #[rustfmt::skip]
        let mutants = [
            ("carried-ensures-does-not-kill", "UNDECIDED.carry", "Lblcarry", 1000),
            ("diagnosed-run-does-not-kill", "UNDECIDED.slow", "Lbldraining", 2),
        ];
        for (id, label, symbol, iterations) in mutants {
            let (vocabulary, tests, observed) =
                declared(label, support::initial_state(constant(symbol), "SortS"));
            let run = run_campaign(
                &Campaign {
                    validator: &validator,
                    module: "UNDECIDED",
                    observed_rules: &observed,
                    vocabulary: &vocabulary,
                    classify: &normal,
                    tests: &tests,
                    budget: ExecutionBudget {
                        max_simplification_iterations: iterations,
                        ..BUDGET
                    },
                },
                &[replace(baseline, label, &[1], bool_token("true"))],
                ScheduleMode::Full,
            )
            .unwrap_or_else(|failure| panic!("{id}: {failure:?}"));
            assert_eq!(
                sides(&run.baseline[0]),
                [OracleSide::Normal(OracleValue::Pattern(
                    PatternValue::NoMatch
                ))],
                "{id}"
            );
            let [mutant] = run.mutants.as_slice() else {
                panic!("{id}: one mutant");
            };
            let SideRun::Sides { sides, .. } = &mutant.evidence[0].run else {
                panic!("{id}: the mutant ran");
            };
            assert_eq!(sides, &[OracleSide::Unknown], "{id}");
            assert_eq!(mutant.report.status, MutantStatus::Unknown, "{id}");
            assert!(mutant.report.killing_test_ids.is_empty(), "{id}");
            assert_eq!(run.score.killed, 0, "{id}");
        }

        // (id, observed rule, initial state)
        #[rustfmt::skip]
        let baselines = [
            ("carried-ensures-baseline-is-refused", "UNDECIDED.carryAlways", support::initial_state(constant("LblcarryAlways"), "SortS")),
            ("vacuous-baseline-is-refused", "UNDECIDED.step", support::deferred_vacuous_state(constant("Lblvacuous"), "SortS")),
        ];
        for (id, label, state) in baselines {
            let (vocabulary, tests, observed) = declared(label, state);
            let refused = run_campaign(
                &Campaign {
                    validator: &validator,
                    module: "UNDECIDED",
                    observed_rules: &observed,
                    vocabulary: &vocabulary,
                    classify: &normal,
                    tests: &tests,
                    budget: BUDGET,
                },
                &[],
                ScheduleMode::Full,
            )
            .expect_err(id);
            assert_eq!(
                refused.kind(),
                CampaignFailureKind::BaselineOracleFailed,
                "{id}"
            );
        }
    });
}

fn rule_applied(label: &str) -> ObservedRule {
    ObservedRule {
        label: label.to_owned(),
        emit_rule_applied: true,
        domain_events: Vec::new(),
    }
}

/// Review P2.1: a path search is never complete, so a state oracle over its paths is
/// `Unknown` even when every witness is a ground final state; the execution of the same
/// program is a value.
#[test]
fn search_paths_are_never_a_state_value() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let side = validator.compile_baseline().expect("baseline compiles");
        let manifest = validator
            .observation_manifest(&side, &[])
            .expect("manifest installs");
        let sorts = SymbolSorts::from_definition(
            &parse_definition(&side.artifacts().definition_kore).expect("compiled KORE parses"),
        );
        let context = BridgeContext {
            test_id: "t1",
            classify: &normal,
            sorts: &sorts,
        };
        let backend = || {
            Backend::new(
                &side.artifacts().definition_kore,
                "COUNTER",
                BackendOptions::default(),
            )
            .expect("backend")
        };
        let execution = ExecutionAdapter::new(manifest.clone())
            .execute(&mut backend(), &counter_state(), BUDGET)
            .expect("execution adapts");
        let search = SearchAdapter::new(SolverProfile::StructuredNoZ3Inference, manifest)
            .expect("no-Z3 profile")
            .search_paths(
                &mut backend(),
                SearchRequest {
                    state: codec::to_value(&counter_state()).expect("state encodes"),
                    ..SearchRequest::default()
                },
            )
            .expect("path search adapts");
        let executed = paths_from_execution(&execution, &context).expect("execution bridges");
        let searched = paths_from_search(&search, &context).expect("search bridges");
        // The search's one witness is the execution's complete ground terminal.
        let terminals = |bridged: &kink_native::bridge::BridgedPaths| {
            bridged
                .paths
                .iter()
                .map(|path| (path.complete, path.execution_terminal.clone()))
                .collect::<Vec<_>>()
        };
        assert_eq!(terminals(&searched), terminals(&executed));
        let projection = StateProjection::WholeTerm;
        assert!(matches!(
            state_side(&projection, &executed),
            OracleSide::Normal(_)
        ));
        assert_eq!(state_side(&projection, &searched), OracleSide::Unknown);
    });
}

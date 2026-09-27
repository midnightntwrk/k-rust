//! Campaigns run end to end through kink-native over the shared `testdata/k` definitions.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::time::Duration;

use k_rust::definition::AttributeKey;
use k_rust::kast::{Sort as KastSort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
use k_rust::kore::{ast::Pattern, walk};
use kink_campaign::{
    Campaign, CampaignFailureKind, CampaignRun, CrashPolicy, ExecutionFailureKind,
    MutantScopeFailure, MutantStatus, OracleDeclaration, OracleOutcome, OracleSide, OracleValue,
    PatternValue, Projection, Rational, ScheduleMode, SideRun, StateProjection, Tally, TestCase,
    TestEvidence, TestPlan, TestRun, derive_mutant_report, run_campaign, tally,
};
use kink_native::execution::ExecutionBudget;
use kink_native::observation::{DomainEventSpec, PayloadSource};
use kink_native::{NativeValidator, ObservedRule};
use kink_patch::{
    Baseline, CandidateFailureKind, CandidateGeneration, Claim, Discovery, Edit, InsertPosition,
    Patch, SelectionPolicy, SentenceOrigin, SiteSelector, TermRef, Withdrawal, derive_sites,
    select,
};
use kink_pattern::{
    Atom, Constructor, EventVocabulary, ExecutionTerminalKind, MatchMode, PatternArm, PatternPlan,
    PayloadClause, Relation,
};
use serde_json::Value;

use OracleOutcome::{Agree, Distinguish};

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
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

/// The mutant that replaces the term at `path` of the rule `label` with `replacement`,
/// at that term as its site.
fn replace(baseline: &Baseline, label: &str, path: &[u32], replacement: Term) -> (TermRef, Patch) {
    let at = TermRef::new(support::rule(baseline, label), path);
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("baseline term").clone(),
        at: at.clone(),
        replacement,
    }])
    .expect("one edit");
    (at, patch)
}

/// The generation whose candidates are exactly `mutants`' patches, through the real path:
/// each mutant's site declared by its rule's label and its path (an exhaustive derivation),
/// the derivations united, selected `Each` and folded with each site's patch. The
/// candidates come in site order, and the generation is scored when it has one.
fn generation<'b>(baseline: &'b Baseline, mutants: &[(TermRef, Patch)]) -> CandidateGeneration<'b> {
    let derive = |clauses: &[SiteSelector]| derive_sites(baseline, "site", clauses);
    let nothing = Discovery::empty(baseline, false, false);
    let discovery = mutants
        .iter()
        .map(|(site, _)| {
            let label = baseline
                .sentence(&site.sentence)
                .and_then(|rule| rule.attributes().string(AttributeKey::Label))
                .expect("a labelled rule");
            derive(&[
                SiteSelector::RuleLabel(label.to_owned()),
                SiteSelector::Path(site.path.0.clone()),
            ])
        })
        .try_fold(nothing, |all, next| all.union(&next.expect("no bindings")))
        .expect("one baseline and shape");
    assert!(discovery.exhaustive(), "declared by clauses");
    assert_eq!(
        discovery.tuples().len(),
        mutants.len(),
        "one site per mutant"
    );
    select(&discovery, SelectionPolicy::Each, mutants.len().max(1))
        .expect("selection")
        .fold("test", |origin| {
            let (_, patch) = mutants
                .iter()
                .find(|(site, _)| origin.site_tuple == [site.clone()])
                .expect("a mutant's site");
            patch.clone()
        })
        .expect("every patch edits its site's rule")
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
            TestRun::SkippedAfterKill => panic!("{}: skipped", test.test_id),
        })
        .collect()
}

fn sides(evidence: &TestEvidence) -> &[OracleSide] {
    match &evidence.run {
        SideRun::Sides { sides } => sides,
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
                rule: support::rule(baseline, "COUNTER.increment"),
                emit_rule_applied: true,
                domain_events: Vec::new(),
            },
            ObservedRule {
                rule: support::rule(baseline, "COUNTER.branch"),
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
        // In site order: increment's body, then its right-hand side, branch and fallback.
        let mutants = [
            // k-rust rejects the unknown attribute.
            (
                TermRef::new(support::rule(baseline, "COUNTER.increment"), [0]),
                Patch::new(vec![Edit::AddAttribute {
                    at: support::rule(baseline, "COUNTER.increment"),
                    key: "foo".to_owned(),
                    value: Value::String(String::new()),
                }])
                .expect("one edit"),
            ),
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
        let generation = generation(baseline, &mutants);
        let run = run_campaign(&campaign, &generation, ScheduleMode::Full).expect("admitted");

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
        assert_eq!(statuses, [Invalid, Killed, Killed, Survived]);
        #[rustfmt::skip]
        let expected: [&[(&str, Vec<OracleOutcome>)]; 3] = [
            &[("t1", vec![Distinguish, Agree]), ("t2", vec![Agree, Agree])],
            &[("t1", vec![Agree, Agree]), ("t2", vec![Agree, Distinguish])],
            &[("t1", vec![Agree, Agree]), ("t2", vec![Agree, Agree])],
        ];
        for (mutant, expected) in run.mutants[1..].iter().zip(expected) {
            let id = mutant.plan.mutant_id;
            assert_eq!(outcomes(&mutant.plan.tests), expected, "{id:?}");
            assert_eq!(mutant.plan.mutant_failure, None, "{id:?}");
            for evidence in &mutant.evidence {
                sides(evidence);
            }
        }
        // The branch mutant ends where the baseline does, but branch never fires.
        assert_eq!(
            sides(&run.mutants[2].evidence[1]),
            [
                final_state(t2_final),
                OracleSide::Normal(OracleValue::Pattern(PatternValue::NoMatch))
            ]
        );
        let invalid = &run.mutants[0];
        assert_eq!(
            invalid.plan.mutant_failure,
            Some(MutantScopeFailure::Rejected)
        );
        assert!(invalid.plan.tests.is_empty());
        assert!(invalid.evidence.is_empty());
        assert!(invalid.report.executed_test_ids.is_empty());

        let score = run.score.expect("a complete generation is scored");
        assert_eq!((score.killed, score.survived), (2, 1));
        let counts = tally(&generation, &run).expect("matching generation");
        assert_eq!(
            (counts.killed, counts.survived),
            (score.killed, score.survived)
        );
        assert_eq!(
            score.ratio,
            Some(Rational {
                numerator: 2,
                denominator: 3
            })
        );

        // Under first-kill, the killing prefix is t1 for the increment mutant and t2 for
        // the branch mutant, and every status is unchanged. The runner stops the increment
        // mutant after t1, and the reports are the ones derived from running every test.
        let stopped =
            run_campaign(&campaign, &generation, ScheduleMode::FirstKill).expect("admitted");
        assert_eq!(stopped.baseline, run.baseline);
        assert_eq!(stopped.score, run.score);
        let increment = &stopped.mutants[1];
        assert_eq!(increment.plan.tests[0], run.mutants[1].plan.tests[0]);
        assert_eq!(increment.plan.tests[1].test_id, "t2");
        assert_eq!(increment.plan.tests[1].run, TestRun::SkippedAfterKill);
        assert_eq!(increment.evidence, run.mutants[1].evidence[..1]);
        for (index, (stopped, full)) in stopped.mutants.iter().zip(&run.mutants).enumerate() {
            if index != 1 {
                assert_eq!(stopped.plan, full.plan, "{index}");
                assert_eq!(stopped.evidence, full.evidence, "{index}");
            }
        }
        let manifest = tests
            .iter()
            .map(|test| kink_campaign::ManifestTest {
                test_id: test.id.clone(),
                slot_count: test.oracles.len(),
            })
            .collect::<Vec<_>>();
        #[rustfmt::skip]
        let first_kill: [(&[&str], &[&str]); 4] = [
            (&[], &[]),
            (&["t1"], &["t1"]),
            (&["t1", "t2"], &["t2"]),
            (&["t1", "t2"], &[]),
        ];
        for ((mutant, stopped), (executed, killing)) in
            run.mutants.iter().zip(&stopped.mutants).zip(first_kill)
        {
            let report = derive_mutant_report(&mutant.plan, &manifest, ScheduleMode::FirstKill)
                .expect("report");
            assert_eq!(report.status, mutant.report.status);
            assert_eq!(report.executed_test_ids, executed);
            assert_eq!(report.killing_test_ids, killing);
            assert_eq!(stopped.report, report);
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
        let generation = generation(baseline, &[spin]);
        let run = run_campaign(&campaign, &generation, ScheduleMode::Full).expect("admitted");
        sides(&run.baseline[0]);
        let [mutant] = run.mutants.as_slice() else {
            panic!("one mutant");
        };
        assert_eq!(
            mutant.plan.tests[0].run,
            TestRun::Failed(ExecutionFailureKind::TimeLimit)
        );
        assert_eq!(mutant.report.status, MutantStatus::Timeout);
        assert_eq!(run.score.map(|score| score.denominator), Some(0));
        assert_eq!(
            tally(&generation, &run),
            Some(Tally {
                timeout: 1,
                ..Tally::default()
            })
        );
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
/// terminal term, and an observed position outside the baseline is a declaration
/// error.
#[test]
fn baseline_admission_gates_crashes_and_unknown_rules() {
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
                rule: if label == "COUNTER.nothing" {
                    kink_patch::SentenceRef::new("COUNTER", 999)
                } else {
                    support::rule(validator.baseline(), label)
                },
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
                &generation(validator.baseline(), &[]),
                ScheduleMode::Full,
            )
        };

        let rejected = run(CrashPolicy::Reject, &[]).expect_err("crash rejected");
        assert_eq!(rejected.kind(), CampaignFailureKind::BaselineOracleFailed);

        let unknown =
            run(CrashPolicy::CompareIdentity, &rules("COUNTER.nothing")).expect_err("unknown rule");
        assert_eq!(unknown.kind(), CampaignFailureKind::InvalidDeclaration);

        let admitted = run(CrashPolicy::CompareIdentity, &rules("COUNTER.branch"))
            .expect("a crash is admitted under CompareIdentity");
        let OracleSide::SemanticCrash(term) = &sides(&admitted.baseline[0])[0] else {
            panic!("a crash side");
        };
        assert!(contains(term, "Lblselected"));
        // A generation with no candidates claims no score, not one over zero mutants.
        assert_eq!(admitted.score, None);
    });
}

/// Review P1 through the runner, over `undecided.k`: an occurrence on a path whose
/// feasibility is undecided, or in a run that collected a backend diagnostic, is no witness,
/// so the pattern side is `Unknown`. A mutant that makes `carry` (a carried `ensures`) or
/// `slow` (a simplifier-budget diagnostic) apply is therefore not killed against the
/// baseline's complete absence. A carried `ensures` baseline is not admitted. A vacuous
/// successor has no instance and is discarded, so its baseline has complete absence.
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
            ("diagnosed-run-does-not-kill", "UNDECIDED.slow", "Lbldraining", 3),
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
                &generation(
                    baseline,
                    &[replace(baseline, label, &[1], bool_token("true"))],
                ),
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
            assert_eq!(run.score.map(|score| score.killed), Some(0), "{id}");
        }

        // (id, observed rule, initial state, expected baseline outcome)
        #[rustfmt::skip]
        let baselines = [
            ("carried-ensures-baseline-is-refused", "UNDECIDED.carryAlways", support::initial_state(constant("LblcarryAlways"), "SortS"), false),
            ("vacuous-baseline-has-complete-absence", "UNDECIDED.step", support::deferred_vacuous_state(constant("Lblvacuous"), "SortS"), true),
        ];
        for (id, label, state, admitted) in baselines {
            let (vocabulary, tests, observed) = declared(label, state);
            let result = run_campaign(
                &Campaign {
                    validator: &validator,
                    module: "UNDECIDED",
                    observed_rules: &observed,
                    vocabulary: &vocabulary,
                    classify: &normal,
                    tests: &tests,
                    budget: BUDGET,
                },
                &generation(baseline, &[]),
                ScheduleMode::Full,
            );
            if admitted {
                let run = result.expect(id);
                assert_eq!(
                    sides(&run.baseline[0]),
                    [OracleSide::Normal(OracleValue::Pattern(
                        PatternValue::NoMatch
                    ))],
                    "{id}"
                );
                assert!(run.mutants.is_empty(), "{id}");
            } else {
                assert_eq!(
                    result.expect_err(id).kind(),
                    CampaignFailureKind::BaselineOracleFailed,
                    "{id}"
                );
            }
        }
    });
}

/// KK-66: dropping `requires I2 =/=Int 0` from guardeddiv's `divide` makes `divide(10, 0)` an
/// undefined step, since its right-hand side `10 /Int 0` is undefined. The baseline is stuck on
/// that term, so the exit-stop oracle distinguishes the classes `Stuck` and `UndefinedStep` and
/// kills the mutant. The final result is the same term, and the write/load prefix is real on both
/// sides, so those oracles agree. A nonzero divisor agrees everywhere.
#[test]
fn dropping_a_division_guard_is_killed_by_its_undefined_step() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("guardeddiv.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let int = |value: &str| Pattern::DomainValue {
            sort: kore_sort("SortInt"),
            value: value.into(),
        };
        let app = |symbol: &str, arguments| kore_application(symbol, Vec::new(), arguments);
        let program = |divisor: &str| {
            let op = |symbol| app(symbol, vec![app("Lbladdr", vec![int("1")]), int("0")]);
            support::initial_state(
                app(
                    "Lblseq",
                    vec![
                        op("Lblwrite"),
                        app(
                            "Lblseq",
                            vec![
                                op("Lblload"),
                                app("Lbldivide", vec![int("10"), int(divisor)]),
                            ],
                        ),
                    ],
                ),
                "SortProg",
            )
        };
        let vocabulary = vocabulary(&["rule:GUARDEDDIV.load"]);
        let observed = [ObservedRule {
            rule: support::rule(baseline, "GUARDEDDIV.load"),
            emit_rule_applied: true,
            domain_events: Vec::new(),
        }];
        let exit_stop = OracleDeclaration::new(
            CrashPolicy::CompareIdentity,
            Projection::State(StateProjection::ExitStop {
                exit_code_cell: None,
            }),
        )
        .expect("exit-stop declaration");
        let tests = ["0", "2"].map(|divisor| TestCase {
            id: format!("divide-by-{divisor}"),
            initial_state: program(divisor),
            oracles: vec![
                exit_stop.clone(),
                whole_term(CrashPolicy::CompareIdentity),
                occurs(&vocabulary, "rule:GUARDEDDIV.load"),
            ],
        });
        // A configuration that still holds `divide` did not finish.
        let classify = |term: &Pattern| {
            if contains(term, "Lbldivide") {
                ExecutionTerminalKind::Stuck
            } else {
                ExecutionTerminalKind::Normal
            }
        };
        let run = run_campaign(
            &Campaign {
                validator: &validator,
                module: "GUARDEDDIV",
                observed_rules: &observed,
                vocabulary: &vocabulary,
                classify: &classify,
                tests: &tests,
                budget: BUDGET,
            },
            &generation(
                baseline,
                &[replace(
                    baseline,
                    "GUARDEDDIV.divide",
                    &[1],
                    bool_token("true"),
                )],
            ),
            ScheduleMode::Full,
        )
        .expect("admitted");
        let class = |class| {
            OracleSide::Normal(OracleValue::ExitStop(
                [kink_campaign::ExitStop { class, code: None }].into(),
            ))
        };
        use kink_campaign::TerminalClass::{Normal, Stuck, UndefinedStep};
        assert_eq!(sides(&run.baseline[0])[0], class(Stuck));
        assert_eq!(sides(&run.baseline[1])[0], class(Normal));
        let [mutant] = run.mutants.as_slice() else {
            panic!("one mutant");
        };
        assert_eq!(sides(&mutant.evidence[0])[0], class(UndefinedStep));
        assert_eq!(
            sides(&mutant.evidence[0])[1..],
            sides(&run.baseline[0])[1..]
        );
        assert_eq!(
            outcomes(&mutant.plan.tests),
            [
                ("divide-by-0", vec![Distinguish, Agree, Agree]),
                ("divide-by-2", vec![Agree, Agree, Agree]),
            ]
        );
        assert_eq!(mutant.report.status, MutantStatus::Killed);
        assert_eq!(mutant.report.killing_test_ids, ["divide-by-0"]);
    });
}

fn rule_applied(label: &str) -> ObservedRule {
    ObservedRule {
        rule: support::rule(
            &support::load(if label.starts_with("UNDECIDED.") {
                "undecided.k"
            } else {
                "counter.k"
            }),
            label,
        ),
        emit_rule_applied: true,
        domain_events: Vec::new(),
    }
}

#[test]
fn selected_function_equation_is_infrastructure_failure() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("undecided.k"), CompileOptions::default());
        let observed = [ObservedRule {
            rule: kink_patch::SentenceRef::new("UNDECIDED", 0),
            emit_rule_applied: true,
            domain_events: Vec::new(),
        }];
        let vocabulary = vocabulary(&["equation"]);
        let tests = [TestCase {
            id: "equation".to_owned(),
            initial_state: support::initial_state(
                kore_application(
                    "LblisZero",
                    Vec::new(),
                    vec![kore_application("Lblz", Vec::new(), Vec::new())],
                ),
                "SortBool",
            ),
            oracles: vec![whole_term(CrashPolicy::CompareIdentity)],
        }];
        let failure = run_campaign(
            &Campaign {
                validator: &validator,
                module: "UNDECIDED",
                observed_rules: &observed,
                vocabulary: &vocabulary,
                classify: &|_| ExecutionTerminalKind::Normal,
                tests: &tests,
                budget: BUDGET,
            },
            &generation(validator.baseline(), &[]),
            ScheduleMode::Full,
        )
        .expect_err("equation filter is refused");
        assert_eq!(failure.kind(), CampaignFailureKind::BaselineError);
    });
}

#[test]
fn anonymous_clone_of_observed_rule_is_equivalent() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let rule = support::rule(baseline, "COUNTER.increment");
        let mut clone = baseline.sentence(&rule).expect("rule").clone();
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
        let generation = generation(baseline, &[(TermRef::new(rule.clone(), [0]), patch)]);
        let observed = [ObservedRule {
            rule,
            emit_rule_applied: true,
            domain_events: Vec::new(),
        }];
        let tests = [TestCase {
            id: "increment".into(),
            initial_state: counter_state(),
            oracles: vec![whole_term(CrashPolicy::CompareIdentity)],
        }];
        let vocabulary = vocabulary(&[]);
        let run = run_campaign(
            &Campaign {
                validator: &validator,
                module: "COUNTER",
                observed_rules: &observed,
                vocabulary: &vocabulary,
                classify: &normal,
                tests: &tests,
                budget: BUDGET,
            },
            &generation,
            ScheduleMode::Full,
        )
        .expect("campaign");
        assert_eq!(run.mutants.len(), 1);
        assert_eq!(
            run.mutants[0].plan.mutant_failure,
            Some(MutantScopeFailure::EquivalentCompilation)
        );
        assert!(run.mutants[0].plan.tests.is_empty());
        assert_eq!(run.mutants[0].report.status, MutantStatus::Equivalent);
        let score = run.score.expect("complete generation is counted");
        assert_eq!(score.denominator, 0);
        assert_eq!(score.ratio, None);
        assert_eq!(tally(&generation, &run).expect("tally").equivalent, 1);
    });
}

#[test]
fn deleting_either_equal_copy_is_equivalent() {
    with_stack(|| {
        let validator = NativeValidator::bind(
            support::load("duplicate_unlabelled.k"),
            CompileOptions::default(),
        );
        let baseline = validator.baseline();
        let discovered = derive_sites(baseline, "equal copies", &[SiteSelector::Path(vec![0])])
            .expect("body sites");
        assert_eq!(discovered.tuples().len(), 2);
        let generation = select(&discovered, SelectionPolicy::Each, 2)
            .expect("select both")
            .fold("delete equal copy", |origin| {
                Patch::new(vec![Edit::DeleteSentence {
                    at: origin.site_tuple[0].sentence.clone(),
                }])
                .expect("deletion patch")
            })
            .expect("both deletion patches apply");
        let tests = [TestCase {
            id: "terminal y".into(),
            initial_state: support::initial_state(constant("Lbly"), "SortS"),
            oracles: vec![whole_term(CrashPolicy::CompareIdentity)],
        }];
        let vocabulary = vocabulary(&[]);
        let run = run_campaign(
            &Campaign {
                validator: &validator,
                module: "DUPLICATE'Unds'UNLABELLED",
                observed_rules: &[],
                vocabulary: &vocabulary,
                classify: &normal,
                tests: &tests,
                budget: BUDGET,
            },
            &generation,
            ScheduleMode::Full,
        )
        .expect("campaign");
        assert_eq!(run.mutants.len(), 2);
        for mutant in &run.mutants {
            assert_eq!(mutant.report.status, MutantStatus::Equivalent);
            assert_eq!(
                mutant.plan.mutant_failure,
                Some(MutantScopeFailure::EquivalentCompilation)
            );
            assert!(mutant.plan.tests.is_empty());
        }
        assert_eq!(run.score.expect("scored").denominator, 0);
        assert_eq!(tally(&generation, &run).expect("tally").equivalent, 2);
    });
}

#[test]
fn merged_observed_and_unobserved_authors_do_not_kill() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("unlabelled.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let observed_rule = kink_patch::SentenceRef::new("UNLABELLED", 0);
        let unobserved_rule = kink_patch::SentenceRef::new("UNLABELLED", 2);
        let mut replacement = baseline.sentence(&unobserved_rule).expect("C").clone();
        *replacement.attributes_mut() = baseline
            .sentence(&observed_rule)
            .expect("A")
            .attributes()
            .clone();
        let discovered = derive_sites(
            baseline,
            "A body",
            &[SiteSelector::Head { label: "a".into() }],
        )
        .expect("A site");
        assert_eq!(discovered.tuples().len(), 1);
        let generation = select(&discovered, SelectionPolicy::Each, 1)
            .expect("select A")
            .fold("merge with C", |_| {
                Patch::new(vec![Edit::ReplaceSentence {
                    at: observed_rule.clone(),
                    replacement: replacement.clone(),
                }])
                .expect("replacement patch")
            })
            .expect("replacement applies");
        let vocabulary = vocabulary(&["rule:UNLABELLED:0"]);
        let observed = [ObservedRule {
            rule: observed_rule,
            emit_rule_applied: true,
            domain_events: Vec::new(),
        }];
        let tests = [TestCase {
            id: "C fires".into(),
            initial_state: support::initial_state(constant("Lblx"), "SortS"),
            oracles: vec![occurs(&vocabulary, "rule:UNLABELLED:0")],
        }];
        let run = run_campaign(
            &Campaign {
                validator: &validator,
                module: "UNLABELLED",
                observed_rules: &observed,
                vocabulary: &vocabulary,
                classify: &normal,
                tests: &tests,
                budget: BUDGET,
            },
            &generation,
            ScheduleMode::Full,
        )
        .expect("campaign");
        assert_eq!(run.mutants.len(), 1);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Unknown);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());
        assert_eq!(
            outcomes(&run.mutants[0].plan.tests),
            [("C fires", vec![OracleOutcome::Unknown])]
        );
    });
}

/// Review P2.2 (plan row C4): the same folded mutant of `branch`'s `requires` is run and
/// survives in every row, but only a complete generation is scored. A non-exhaustive
/// (supplied, or narrowed by a closure) discovery gives an incomplete generation, and a
/// cardinality mismatch a failed one with no candidates; neither has a score. A complete
/// generation with no candidates, because nothing was selected or its one origin's patch
/// changes nothing, has no score either, rather than one over zero mutants.
#[test]
fn incomplete_and_failed_generations_are_not_scored() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let vocabulary = vocabulary(&["unused"]);
        let tests = [TestCase {
            id: "t2".to_owned(),
            initial_state: choose_state(),
            oracles: vec![whole_term(CrashPolicy::CompareIdentity)],
        }];
        let campaign = Campaign {
            validator: &validator,
            module: "COUNTER",
            observed_rules: &[],
            vocabulary: &vocabulary,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let exhaustive = derive_sites(
            baseline,
            "requires",
            &[
                SiteSelector::RuleLabel("COUNTER.branch".to_owned()),
                SiteSelector::Path(vec![1]),
            ],
        )
        .expect("no bindings");
        assert_eq!(exhaustive.tuples().len(), 1);
        let partial = Discovery::supplied(baseline, exhaustive.tuples().to_vec(), false, false)
            .expect("derived sites are known");
        let nothing = Discovery::empty(baseline, false, false);
        // Every `requires`, narrowed by a closure to `branch`'s: `fallback`'s is dropped by
        // code, not by a declared clause.
        let narrowed = derive_sites(baseline, "requires", &[SiteSelector::Path(vec![1])])
            .expect("no bindings")
            .filter(|tuple| tuple.sites[0].at == exhaustive.tuples()[0].sites[0].at);
        let mismatch = SelectionPolicy::Exact {
            expected_tuple_count: 2,
            expected_tuple_arity: 1,
        };
        // (id, discovery, policy, patch changes nothing, generation failure, mutant count, score, tally)
        #[rustfmt::skip]
        let rows = [
            ("complete-is-scored", &exhaustive, SelectionPolicy::Each, false, None, 1, Some((0, 1)), Tally { survived: 1, ..Tally::default() }),
            ("non-exhaustive-discovery-is-not-scored", &partial, SelectionPolicy::Each, false, Some(CandidateFailureKind::IncompleteGeneration), 1, None, Tally { survived: 1, ..Tally::default() }),
            ("closure-narrowed-discovery-is-not-scored", &narrowed, SelectionPolicy::Each, false, Some(CandidateFailureKind::IncompleteGeneration), 1, None, Tally { survived: 1, ..Tally::default() }),
            ("cardinality-mismatch-is-not-scored", &exhaustive, mismatch, false, Some(CandidateFailureKind::CardinalityMismatch), 0, None, Tally::default()),
            ("empty-selection-is-not-scored", &nothing, SelectionPolicy::Each, false, None, 0, None, Tally::default()),
            ("every-origin-rejected-is-not-scored", &exhaustive, SelectionPolicy::Each, true, None, 0, None, Tally { rejected_origins: 1, ..Tally::default() }),
        ];
        for (id, discovery, policy, no_change, failure, mutants, expected, counts) in rows {
            // requires B  =>  requires false: fallback still ends in selected(true).
            let generation = select(discovery, policy, 4)
                .unwrap_or_else(|failure| panic!("{id}: {failure}"))
                .fold("requires-false", |origin| {
                    let at = origin.site_tuple[0].clone();
                    let expected = baseline.term(&at).expect("requires").clone();
                    Patch::new(vec![Edit::ReplaceTerm {
                        replacement: if no_change {
                            expected.clone()
                        } else {
                            bool_token("false")
                        },
                        expected,
                        at,
                    }])
                    .expect("one edit")
                })
                .unwrap_or_else(|failure| panic!("{id}: {failure}"));
            assert_eq!(generation.failure(), failure, "{id}");
            let run = run_campaign(&campaign, &generation, ScheduleMode::Full)
                .unwrap_or_else(|failure| panic!("{id}: {failure:?}"));
            assert_eq!(run.mutants.len(), mutants, "{id}");
            assert_eq!(tally(&generation, &run), Some(counts), "{id}");
            for mutant in &run.mutants {
                assert_eq!(mutant.report.status, MutantStatus::Survived, "{id}");
            }
            assert_eq!(
                run.score.map(|score| (score.killed, score.survived)),
                expected,
                "{id}"
            );
        }
    });
}

/// A campaign runs only a generation derived from its validator's own baseline. One derived
/// from another load of the same file, or from an equal clone, is refused before anything
/// compiles, whatever it would score.
#[test]
fn a_generation_of_another_baseline_is_refused() {
    let validator = NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
    let vocabulary = vocabulary(&["unused"]);
    let tests = [TestCase {
        id: "t2".to_owned(),
        initial_state: choose_state(),
        oracles: vec![whole_term(CrashPolicy::CompareIdentity)],
    }];
    let campaign = Campaign {
        validator: &validator,
        module: "COUNTER",
        observed_rules: &[],
        vocabulary: &vocabulary,
        classify: &normal,
        tests: &tests,
        budget: BUDGET,
    };
    let reloaded = support::load("counter.k");
    let cloned = validator.baseline().clone();
    for (id, other) in [("reloaded", &reloaded), ("cloned", &cloned)] {
        let mutant = replace(other, "COUNTER.branch", &[1], bool_token("false"));
        let generation = generation(other, &[mutant]);
        assert!(generation.scored(), "{id}");
        assert_eq!(
            run_campaign(&campaign, &generation, ScheduleMode::Full)
                .expect_err(id)
                .kind(),
            CampaignFailureKind::ForeignGeneration,
            "{id}"
        );
    }
}

/// A tally needs the generation's full candidate sequence.
#[test]
fn tally_rejects_a_run_with_fewer_mutants_than_candidates() {
    let baseline = support::load("counter.k");
    let mutant = replace(&baseline, "COUNTER.branch", &[1], bool_token("false"));
    let generation = generation(&baseline, &[mutant]);
    assert_eq!(generation.candidates().len(), 1);
    let run = CampaignRun {
        baseline: Vec::new(),
        mutants: Vec::new(),
        score: None,
    };
    assert_eq!(tally(&generation, &run), None);
}

/// The write-then-load campaign of the attribute-trust probes over `file`: its validator,
/// vocabulary, observed `write` and `load` rules, and the pattern oracle "a load from the
/// address written before".
struct ClaimCampaign {
    validator: NativeValidator,
    vocabulary: EventVocabulary,
    observed_rules: Vec<ObservedRule>,
    oracle: OracleDeclaration,
}

impl ClaimCampaign {
    fn load(file: &str) -> Self {
        let baseline =
            support::load_path(&std::path::Path::new(support::DIR).join(file), "SYMPARTIAL");
        let validator = NativeValidator::bind(baseline, CompileOptions::default());
        let vocabulary = EventVocabulary::new(
            ["memoryWrite", "memoryLoad"]
                .map(|name| Constructor {
                    name: name.to_owned(),
                    payload_sorts: vec![kore_sort("SortInt"), kore_sort("SortInt")],
                })
                .to_vec(),
        )
        .expect("vocabulary");
        let observed_rules = [
            ("SYMPARTIAL.write", "memoryWrite"),
            ("SYMPARTIAL.load", "memoryLoad"),
        ]
        .map(|(label, constructor)| ObservedRule {
            rule: support::rule(validator.baseline(), label),
            emit_rule_applied: false,
            domain_events: vec![DomainEventSpec {
                constructor: constructor.to_owned(),
                payload: [1, 2].map(PayloadSource::BindingValue).to_vec(),
            }],
        })
        .to_vec();
        let atom = |constructor: &str, mode| Atom {
            constructor: constructor.to_owned(),
            payload: vec![PayloadClause {
                position: 0,
                mode,
                variable: "A".to_owned(),
            }],
        };
        let plan = PatternPlan::new(
            &vocabulary,
            vec![("A".to_owned(), kore_sort("SortInt"))],
            vec![PatternArm {
                atoms: vec![
                    atom("memoryWrite", MatchMode::Bind),
                    atom("memoryLoad", MatchMode::Use),
                ],
                relations: vec![Relation::EventuallyAfter],
            }],
            None,
        )
        .expect("write then load plan");
        let oracle = OracleDeclaration::new(
            CrashPolicy::CompareIdentity,
            Projection::Pattern {
                plan,
                with_bindings: false,
            },
        )
        .expect("pattern oracle");
        Self {
            validator,
            vocabulary,
            observed_rules,
            oracle,
        }
    }

    fn baseline(&self) -> &Baseline {
        self.validator.baseline()
    }

    /// `write(addr(1), 5) ; half(argument) ; load(addr(1), 5)`, as test `id`.
    fn test(&self, id: &str, argument: Pattern) -> TestCase {
        let app = support::app;
        let program = app(
            "Lblseq",
            vec![
                app(
                    "Lblwrite",
                    vec![app("Lbladdr", vec![support::int(1)]), support::int(5)],
                ),
                app(
                    "Lblseq",
                    vec![
                        app("Lblhalf", vec![argument]),
                        app(
                            "Lblseq",
                            vec![
                                app(
                                    "Lblload",
                                    vec![app("Lbladdr", vec![support::int(1)]), support::int(5)],
                                ),
                                app("Lblhalt", vec![]),
                            ],
                        ),
                    ],
                ),
            ],
        );
        TestCase {
            id: id.to_owned(),
            initial_state: support::initial_state(program, "SortProg"),
            oracles: vec![self.oracle.clone()],
        }
    }

    /// The symbolic test over `X:Nat`, and the ground tests over `z` and `s(z)`.
    fn tests(&self) -> [TestCase; 3] {
        [
            self.test("X", support::var("X", "SortNat")),
            self.test("z", z()),
            self.test("s(z)", s(z())),
        ]
    }

    fn run(&self, tests: &[TestCase], mutants: &[(TermRef, Patch)]) -> CampaignRun {
        let generation = generation(self.baseline(), mutants);
        assert_eq!(
            generation.candidates().len(),
            mutants.len(),
            "{:?}",
            generation.dispositions()
        );
        run_campaign(
            &Campaign {
                validator: &self.validator,
                module: "SYMPARTIAL",
                observed_rules: &self.observed_rules,
                vocabulary: &self.vocabulary,
                classify: &normal,
                tests,
                budget: BUDGET,
            },
            &generation,
            ScheduleMode::Full,
        )
        .expect("the campaign runs")
    }

    /// The single-site literal mutant `d() => value`.
    fn d(&self, value: &str) -> (TermRef, Patch) {
        replace(
            self.baseline(),
            "SYMPARTIAL.d",
            &[0, 1],
            Term::Token {
                token: value.to_owned(),
                sort: KastSort::new("Int"),
            },
        )
    }

    /// The claims a withdrawal lists, by the symbol or rule label of their sentence.
    fn names(&self, claims: &[Claim]) -> Vec<(String, String)> {
        claims
            .iter()
            .map(|claim| {
                let SentenceOrigin::Baseline(at) = &claim.origin else {
                    panic!("a baseline claim");
                };
                let sentence = self.baseline().sentence(at).expect("a baseline sentence");
                let name = match sentence {
                    k_rust::definition::Sentence::Production {
                        label: Some(label), ..
                    } => label.name.clone(),
                    sentence => sentence
                        .attributes()
                        .string(AttributeKey::Label)
                        .expect("a labelled rule")
                        .to_owned(),
                };
                (name, claim.key.clone())
            })
            .collect()
    }
}

fn pattern(value: PatternValue) -> OracleSide {
    OracleSide::Normal(OracleValue::Pattern(value))
}

fn matched() -> OracleSide {
    pattern(PatternValue::Match { bindings: None })
}

fn unmatched() -> OracleSide {
    pattern(PatternValue::NoMatch)
}

/// The sides of every test of a run, `None` for a test that did not run.
fn test_sides(
    evidence: &[TestEvidence],
) -> Vec<(&str, Result<&[OracleSide], ExecutionFailureKind>)> {
    evidence
        .iter()
        .map(|evidence| {
            (
                evidence.test_id.as_str(),
                match &evidence.run {
                    SideRun::Sides { sides } => Ok(sides.as_slice()),
                    SideRun::Failed(kind) => Err(*kind),
                },
            )
        })
        .collect()
}

/// Probe 3 through the campaign: the literal mutant `d() => 0` is behaviourally equal to the
/// baseline on every instance (both stop at `half`), yet under the inherited `total` of f and
/// d the symbolic test matched and killed it. Its patch changes d's equation, which f's
/// equations mention, so both claims are withdrawn from the definition its symbolic test runs
/// on, and that side is `Unknown`: the mutant is not killed. Its ground tests run on the patched
/// definition as written and agree with the baseline.
#[test]
fn probe3_symbolic_test_does_not_kill_an_equivalent_mutant() {
    with_stack(|| {
        let campaign = ClaimCampaign::load("symbolic-claim-mutation.k");
        let run = campaign.run(&campaign.tests(), &[campaign.d("0")]);
        let no_match = [unmatched()];
        assert_eq!(
            test_sides(&run.baseline),
            [
                ("X", Ok(&no_match[..])),
                ("z", Ok(&no_match[..])),
                ("s(z)", Ok(&no_match[..]))
            ]
        );
        let [mutant] = run.mutants.as_slice() else {
            panic!("one mutant");
        };
        assert_eq!(
            test_sides(&mutant.evidence),
            [
                ("X", Ok(&[OracleSide::Unknown][..])),
                ("z", Ok(&no_match[..])),
                ("s(z)", Ok(&no_match[..]))
            ]
        );
        assert_eq!(mutant.report.status, MutantStatus::Unknown);
        assert!(mutant.report.killing_test_ids.is_empty());
        let claims = &mutant.report.claims;
        assert_eq!(claims, &mutant.plan.claims);
        assert_eq!(
            campaign.names(&claims.withdrawn),
            [
                ("f".to_owned(), "total".to_owned()),
                ("d".to_owned(), "total".to_owned())
            ]
        );
        assert!(claims.trusted());
        assert!(claims.patch().is_some());

        // Ground campaigns are unchanged: both sides stop at `half`, the mutant survives, and
        // with no symbolic test nothing is withdrawn.
        for test in campaign.tests().into_iter().skip(1) {
            let run = campaign.run(std::slice::from_ref(&test), &[campaign.d("0")]);
            assert_eq!(
                test_sides(&run.baseline),
                [(test.id.as_str(), Ok(&no_match[..]))]
            );
            let mutant = &run.mutants[0];
            assert_eq!(
                test_sides(&mutant.evidence),
                [(test.id.as_str(), Ok(&no_match[..]))]
            );
            assert_eq!(mutant.report.status, MutantStatus::Survived, "{}", test.id);
            assert_eq!(mutant.report.claims, Withdrawal::default());
        }
    });
}

/// Probe 2 through the campaign: the baseline loads on every instance and the mutant
/// `d() => 0` on none, yet under the inherited claims the symbolic test matched on both sides
/// and spared it. Withdrawn, its symbolic side is `Unknown`: it does not survive the symbolic
/// test, and its ground tests kill it. The literal mutant `d() => 2` keeps every instance
/// loading; withdrawal must not turn its symbolic side into a no-match and a kill.
#[test]
fn probe2_symbolic_test_does_not_spare_a_killed_mutant() {
    with_stack(|| {
        let campaign = ClaimCampaign::load("symbolic-claim-survivor.k");
        let [symbolic, zero, one] = campaign.tests();
        let matches = [matched()];

        let run = campaign.run(std::slice::from_ref(&symbolic), &[campaign.d("0")]);
        assert_eq!(test_sides(&run.baseline), [("X", Ok(&matches[..]))]);
        let mutant = &run.mutants[0];
        assert_eq!(
            test_sides(&mutant.evidence),
            [("X", Ok(&[OracleSide::Unknown][..]))]
        );
        assert_eq!(mutant.report.status, MutantStatus::Unknown);
        assert_eq!(
            campaign.names(&mutant.report.claims.withdrawn),
            [
                ("f".to_owned(), "total".to_owned()),
                ("d".to_owned(), "total".to_owned())
            ]
        );

        let tests = [symbolic, zero, one];
        let run = campaign.run(&tests, &[campaign.d("0")]);
        let mutant = &run.mutants[0];
        let no_match = [unmatched()];
        assert_eq!(
            test_sides(&mutant.evidence),
            [
                ("X", Ok(&[OracleSide::Unknown][..])),
                ("z", Ok(&no_match[..])),
                ("s(z)", Ok(&no_match[..]))
            ]
        );
        assert_eq!(mutant.report.status, MutantStatus::Killed);
        assert_eq!(mutant.report.killing_test_ids, ["z", "s(z)"]);

        let run = campaign.run(&tests, &[campaign.d("2")]);
        let mutant = &run.mutants[0];
        assert_eq!(
            test_sides(&mutant.evidence),
            [
                ("X", Ok(&[OracleSide::Unknown][..])),
                ("z", Ok(&matches[..])),
                ("s(z)", Ok(&matches[..]))
            ]
        );
        assert_eq!(mutant.report.status, MutantStatus::Unknown);
    });
}

/// The baseline's `f(I)` equation asserts a tautology; the mutant asserts `I > 0`.
/// At `I = 0` the mutant stops before the load. In the Z3 profile, before claim support
/// included equation `ensures`, the symbolic-only campaign survived because the `I > 0`
/// path was a feasible match. Its instance at zero was a ground kill. The portable profile
/// already returned Unknown, but now both profiles name the unsupported claim explicitly.
#[test]
fn equation_ensures_mutation_makes_symbolic_test_unknown_but_keeps_ground_kill() {
    with_stack(|| {
        let campaign = ClaimCampaign::load("symbolic-equation-ensures.k");
        let baseline = campaign.baseline();
        let i = baseline
            .term(&TermRef::new(
                support::rule(baseline, "SYMPARTIAL.f"),
                [2, 0],
            ))
            .expect("I in the equation ensures")
            .clone();
        let mutation = replace(
            baseline,
            "SYMPARTIAL.f",
            &[2],
            Term::Apply {
                label: k_rust::kast::Label::new("_>Int_"),
                arguments: vec![
                    i,
                    Term::Token {
                        token: "0".to_owned(),
                        sort: KastSort::new("Int"),
                    },
                ],
            },
        );
        let tests = [
            campaign.test("X", support::var("X", "SortInt")),
            campaign.test("0", support::int(0)),
            campaign.test("1", support::int(1)),
        ];
        let run = campaign.run(&tests, std::slice::from_ref(&mutation));
        let matches = [matched()];
        assert_eq!(
            test_sides(&run.baseline),
            [
                ("X", Ok(&matches[..])),
                ("0", Ok(&matches[..])),
                ("1", Ok(&matches[..]))
            ]
        );
        let mutant = &run.mutants[0];
        assert_eq!(
            test_sides(&mutant.evidence),
            [
                ("X", Err(ExecutionFailureKind::UnsupportedClaims)),
                ("0", Ok(&[unmatched()][..])),
                ("1", Ok(&matches[..]))
            ]
        );
        assert_eq!(mutant.report.status, MutantStatus::Killed);
        assert_eq!(mutant.report.killing_test_ids, ["0"]);
        assert!(mutant.report.claims.withdrawn.is_empty());
        assert_eq!(
            campaign.names(&mutant.report.claims.unsupported),
            [("SYMPARTIAL.f".to_owned(), "ensures".to_owned())]
        );
        assert!(!mutant.report.claims.trusted());

        let symbolic = campaign.run(&tests[..1], std::slice::from_ref(&mutation));
        assert_eq!(symbolic.mutants[0].report.status, MutantStatus::Unknown);
    });
}

/// A mutant of a rewrite rule no claim rests on withdraws nothing, and its symbolic test runs
/// on its patched definition and keeps its verdict: `load` never fires, so no instance loads.
/// A mutant that adds `preserves-definedness` to `half` asserts a claim nobody supports:
/// withdrawing it would undo the mutant, so its symbolic test does not run, while its ground
/// tests still do.
#[test]
fn unrelated_and_claim_asserting_mutants() {
    with_stack(|| {
        let campaign = ClaimCampaign::load("symbolic-claim-survivor.k");
        let baseline = campaign.baseline();
        let load_never = replace(baseline, "SYMPARTIAL.load", &[1], bool_token("false"));
        let half = support::rule(baseline, "SYMPARTIAL.half");
        let asserted = (
            TermRef::new(half.clone(), [1]),
            Patch::new(vec![Edit::AddAttribute {
                at: half.clone(),
                key: "preserves-definedness".to_owned(),
                value: Value::String(String::new()),
            }])
            .expect("one edit"),
        );
        let run = campaign.run(&campaign.tests(), &[load_never, asserted]);
        let [unrelated, asserting] = run.mutants.as_slice() else {
            panic!("two mutants");
        };
        let no_match = [unmatched()];
        assert_eq!(
            test_sides(&unrelated.evidence),
            [
                ("X", Ok(&no_match[..])),
                ("z", Ok(&no_match[..])),
                ("s(z)", Ok(&no_match[..]))
            ]
        );
        assert_eq!(unrelated.report.claims, Withdrawal::default());
        assert_eq!(unrelated.report.status, MutantStatus::Killed);
        assert_eq!(unrelated.report.killing_test_ids, ["X", "z", "s(z)"]);

        let matches = [matched()];
        assert_eq!(
            test_sides(&asserting.evidence),
            [
                ("X", Err(ExecutionFailureKind::UnsupportedClaims)),
                ("z", Ok(&matches[..])),
                ("s(z)", Ok(&matches[..]))
            ]
        );
        assert_eq!(
            outcomes_or_failures(&asserting.plan.tests)[0],
            TestRun::Failed(ExecutionFailureKind::UnsupportedClaims)
        );
        assert_eq!(asserting.report.status, MutantStatus::Unknown);
        let claims = &asserting.report.claims;
        assert_eq!(
            campaign.names(&claims.unsupported),
            [(
                "SYMPARTIAL.half".to_owned(),
                "preserves-definedness".to_owned()
            )]
        );
        assert!(!claims.trusted());
    });
}

fn outcomes_or_failures(tests: &[TestPlan]) -> Vec<TestRun> {
    tests.iter().map(|test| test.run.clone()).collect()
}

//! CS-07: selection changes scheduling only; coverage and schedule are regenerated on replay.
#[path = "../../../testdata/k/step_support.rs"]
mod step_support;
#[path = "../../../testdata/k/support.rs"]
mod support;

mod representative;

use std::{
    collections::{BTreeMap, BTreeSet},
    time::Duration,
};

use k_rust::{
    definition::{AttributeKey, Sentence},
    kast::{Sort as KastSort, Term},
    kompile::CompileOptions,
    kore::ast::Pattern,
};
use kink_campaign::selection::{CompiledEdit, coverage_selected};
use kink_campaign::{
    Campaign, CampaignFailureKind, CampaignOptions, Coupled, CrashPolicy, ManifestInput,
    ManifestTest, MutantId, MutantPlan, MutantSelection, MutantStatus, OperatorId,
    OracleDeclaration, OracleOutcome, Projection, ReplayDeclaration, ReplayOutcome, ReplayRefusal,
    ScheduleMode, Sel, SelectionPolicy, StateProjection, TestCase, TestPlan, TestRun,
    campaign_manifest, campaign_report, derive_mutant_report, replay, run_campaign_with,
};
use kink_native::{
    NativeValidator,
    coverage::TestCoverage,
    execution::ExecutionBudget,
    step_events::{StepEventSpec, StepObservation},
};
use kink_patch::{
    Baseline, CandidateGeneration, ClaimSupport, Discovery, Edit, InsertPosition, POSITION_KEYS,
    Patch, SelectionPolicy as CandidatePolicy, SiteSelector, TermRef, Withdrawal, canonical_json,
    derive_sites, select,
};
use kink_pattern::{
    Atom, EventVocabulary, ExecutionTerminalKind, MatchMode, PatternArm, PatternPlan,
    PayloadClause, Relation,
};
use serde_json::json;

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
};
const PRIORITIZE: SelectionPolicy = SelectionPolicy::Prioritize(Sel {
    coupled: Coupled::Union,
});

fn with_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 << 20)
        .spawn(body)
        .expect("test thread")
        .join()
        .expect("test thread does not panic");
}
fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}
fn bool_token(value: &str) -> Term {
    Term::Token {
        token: value.into(),
        sort: KastSort::new("Bool"),
    }
}
fn z() -> Pattern {
    support::app("Lblz", vec![])
}
fn s(p: Pattern) -> Pattern {
    support::app("Lbls", vec![p])
}
fn counter_state() -> Pattern {
    support::initial_state(
        support::app("Lblcounter", vec![z(), s(s(s(z())))]),
        "SortCounter",
    )
}
fn choose_state() -> Pattern {
    support::initial_state(
        support::app(
            "Lblchoose",
            vec![Pattern::DomainValue {
                sort: k_rust::kompile::initial_configuration::kore_sort("SortBool"),
                value: "true".into(),
            }],
        ),
        "SortControl",
    )
}
fn whole_term() -> OracleDeclaration {
    OracleDeclaration::new(
        CrashPolicy::CompareIdentity,
        Projection::State(StateProjection::WholeTerm),
    )
    .expect("state oracle")
}
fn occurs(vocabulary: &EventVocabulary, constructor: &str) -> OracleDeclaration {
    let plan = PatternPlan::new(
        vocabulary,
        vec![],
        vec![PatternArm {
            atoms: vec![Atom {
                constructor: constructor.into(),
                payload: vec![],
            }],
            relations: vec![],
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
    .expect("pattern oracle")
}
fn replace(b: &Baseline, label: &str, path: &[u32], replacement: Term) -> Patch {
    let at = TermRef::new(support::rule(b, label), path.to_vec());
    Patch::new(vec![Edit::ReplaceTerm {
        expected: b.term(&at).expect("term").clone(),
        at,
        replacement,
    }])
    .expect("patch")
}
fn fixed<'a>(b: &'a Baseline, label: &str, path: &[u32], patch: &Patch) -> CandidateGeneration<'a> {
    let discovery = derive_sites(
        b,
        "site",
        &[
            SiteSelector::RuleLabel(label.into()),
            SiteSelector::Path(path.to_vec()),
        ],
    )
    .expect("sites");
    let discovery = Discovery::empty(b, false, false)
        .union(&discovery)
        .expect("one baseline");
    select(&discovery, CandidatePolicy::Each, 1)
        .expect("candidate selection")
        .fold("selection-test", |_| patch.clone())
        .expect("fold")
}
fn branch_generation(b: &Baseline) -> CandidateGeneration<'_> {
    let patch = replace(b, "COUNTER.branch", &[1], bool_token("false"));
    fixed(b, "COUNTER.branch", &[1], &patch)
}
fn two_tests() -> Vec<TestCase> {
    vec![
        TestCase {
            id: "t1".into(),
            initial_state: counter_state(),
            oracles: vec![whole_term()],
        },
        TestCase {
            id: "t2".into(),
            initial_state: choose_state(),
            oracles: vec![whole_term()],
        },
    ]
}
fn counter_campaign<'a>(
    validator: &'a NativeValidator,
    specs: &'a [StepEventSpec],
    tests: &'a [TestCase],
    budget: ExecutionBudget,
) -> Campaign<'a> {
    Campaign {
        validator,
        module: "COUNTER",
        observation: specs,
        classify: &normal,
        tests,
        budget,
    }
}
fn options(schedule: ScheduleMode) -> CampaignOptions {
    CampaignOptions {
        schedule,
        selection: PRIORITIZE,
        share_evidence: true,
    }
}

/// H1: the two baseline final terms differ; reversing the runs must preserve the pairing.
#[test]
fn reversed_test_order_pairs_evidence_by_test_id() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let specs = step_support::counter(true);
        let tests = two_tests();
        let campaign = counter_campaign(&validator, &specs, &tests, BUDGET);
        let generation = branch_generation(validator.baseline());
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let run =
                run_campaign_with(&campaign, &generation, &options(schedule)).expect("campaign");
            let m = &run.mutants[0];
            assert_ne!(run.baseline[0].run, run.baseline[1].run);
            assert_eq!(
                m.plan.selection.as_ref().expect("selection").order,
                ["t2", "t1"]
            );
            assert_eq!(
                m.plan
                    .tests
                    .iter()
                    .map(|t| t.test_id.as_str())
                    .collect::<Vec<_>>(),
                ["t2", "t1"]
            );
            assert_eq!(
                m.report.status,
                MutantStatus::Survived,
                "STOP H1: equivalent behaviour was killed"
            );
            assert!(m.report.killing_test_ids.is_empty());
            assert_eq!(m.report.executed_test_ids, ["t2", "t1"]);
            eprintln!(
                "CS07_SELECTION H1 {schedule:?} selected=1 total=2 order={:?}",
                m.plan.selection.as_ref().unwrap().order
            );
        }
    });
}

fn complete_coverage() -> TestCoverage {
    TestCoverage {
        test_id: "uncovered".into(),
        complete: true,
        rule_ids: BTreeSet::new(),
        sentences: BTreeSet::new(),
        unmapped: BTreeMap::new(),
    }
}
fn assert_global(validator: &NativeValidator, patch: &Patch, row: &str) {
    let baseline = validator.compile_baseline().expect("baseline compile");
    let side = validator.validate(patch).expect("mutant compile");
    let edit = CompiledEdit::between(&baseline, &side);
    assert!(edit.global, "{row} must select every test");
    assert!(coverage_selected(
        &complete_coverage(),
        &edit,
        Coupled::Union,
        &[]
    ));
    assert!(coverage_selected(
        &complete_coverage(),
        &edit,
        Coupled::AllSites,
        &[]
    ));
    eprintln!("CS07_GLOBAL {row} removed={:?}", edit.removed_rule_ids);
}

#[test]
fn equations_insertions_and_production_attributes_are_global() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("guardedeq.k"), CompileOptions::default());
        let equation = replace(
            validator.baseline(),
            "GUARDEDEQ.norm",
            &[0, 1],
            Term::Token {
                token: "0".into(),
                sort: KastSort::new("Int"),
            },
        );
        assert_global(&validator, &equation, "equation");

        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let at = support::rule(validator.baseline(), "COUNTER.branch");
        let mut inserted = validator.baseline().sentence(&at).expect("rule").clone();
        for key in POSITION_KEYS
            .into_iter()
            .chain([AttributeKey::Label, AttributeKey::UniqueId])
        {
            inserted.attributes_mut().remove(key.as_str());
        }
        if let Sentence::Rule { requires, .. } = &mut inserted {
            *requires = bool_token("false");
        } else {
            panic!("rule");
        }
        let insertion = Patch::new(vec![Edit::InsertSentence {
            position: InsertPosition::After(at),
            ordinal: 0,
            sentence: inserted,
        }])
        .expect("insertion");
        assert_global(&validator, &insertion, "inserted rule");
        let compiled = validator.compile_baseline().expect("baseline");
        let added = validator.validate(&insertion).expect("inserted side");
        assert!(
            CompiledEdit::between(&compiled, &added)
                .removed_rule_ids
                .is_empty()
        );

        let validator =
            NativeValidator::bind(support::load("strictheat.k"), CompileOptions::default());
        let production = validator
            .baseline()
            .authored_sentences()
            .find_map(|(at, sentence)| match sentence {
                Sentence::Production {
                    label: Some(label), ..
                } if label.name == "add" => Some(at),
                _ => None,
            })
            .expect("strict add production");
        let strict = validator
            .baseline()
            .sentence(&production)
            .unwrap()
            .attributes()
            .get("strict")
            .expect("strict")
            .clone();
        let attr = Patch::new(vec![Edit::RemoveAttribute {
            at: production,
            key: "strict".into(),
            expected: strict,
        }])
        .expect("production attribute");
        assert_global(&validator, &attr, "production attribute");
    });
}

#[test]
fn incomplete_baseline_is_selected_without_covering_the_edit() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let specs = step_support::counter(true);
        let vocabulary = StepObservation::vocabulary_of(&specs).expect("vocabulary");
        let tests = vec![
            TestCase {
                id: "terminal".into(),
                initial_state: support::initial_state(
                    support::app(
                        "Lblselected",
                        vec![Pattern::DomainValue {
                            sort: k_rust::kompile::initial_configuration::kore_sort("SortBool"),
                            value: "true".into(),
                        }],
                    ),
                    "SortControl",
                ),
                oracles: vec![whole_term()],
            },
            TestCase {
                id: "depth-bound".into(),
                initial_state: counter_state(),
                oracles: vec![occurs(&vocabulary, "increment")],
            },
        ];
        let budget = ExecutionBudget {
            max_depth: Some(1),
            ..BUDGET
        };
        let generation = branch_generation(validator.baseline());
        let campaign = counter_campaign(&validator, &specs, &tests, budget);
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let run = run_campaign_with(&campaign, &generation, &options(schedule))
                .expect("witness admits bounded baseline");
            assert!(run.baseline_coverage[0].complete);
            assert!(!run.baseline_coverage[1].complete);
            let selected = run.mutants[0].plan.selection.as_ref().expect("selection");
            assert!(!selected.global);
            assert!(
                run.baseline_coverage[1]
                    .rule_ids
                    .is_disjoint(&selected.removed_rule_ids)
            );
            assert_eq!(selected.order, ["depth-bound", "terminal"]);
            assert_eq!(
                run.mutants[0].report.executed_test_ids,
                ["depth-bound", "terminal"]
            );
            eprintln!("CS07_SELECTION incomplete {schedule:?} selected=1 total=2");
        }
    });
}

#[test]
fn empty_selection_runs_every_test_in_manifest_order() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let specs = step_support::counter(true);
        let tests = [
            TestCase {
                id: "first".into(),
                initial_state: counter_state(),
                oracles: vec![whole_term()],
            },
            TestCase {
                id: "second".into(),
                initial_state: support::initial_state(
                    support::app("Lblcounter", vec![z(), s(z())]),
                    "SortCounter",
                ),
                oracles: vec![whole_term()],
            },
        ];
        let generation = branch_generation(validator.baseline());
        let campaign = counter_campaign(&validator, &specs, &tests, BUDGET);
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let run =
                run_campaign_with(&campaign, &generation, &options(schedule)).expect("campaign");
            let selection = run.mutants[0].plan.selection.as_ref().expect("selection");
            assert!(!selection.global);
            for coverage in &run.baseline_coverage {
                assert!(coverage.complete);
                assert!(coverage.rule_ids.is_disjoint(&selection.removed_rule_ids));
            }
            assert_eq!(selection.order, ["first", "second"]);
            assert!(selection.deselected.is_empty());
            assert_eq!(run.mutants[0].report.executed_test_ids, ["first", "second"]);
            assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
            eprintln!("CS07_SELECTION empty {schedule:?} selected=2 total=2 fallback=true");
        }
    });
}

fn replay_generation(b: &Baseline, killing: bool) -> CandidateGeneration<'_> {
    let path: &[u32] = if killing { &[0, 1, 0] } else { &[1] };
    let patch = replace(b, "COUNTER.branch", path, bool_token("false"));
    fixed(b, "COUNTER.branch", path, &patch)
}

#[test]
fn prioritize_replay_recomputes_coverage_and_order_in_both_schedules() {
    with_stack(|| {
        for killing in [false, true] {
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let validator =
                    NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
                let specs = step_support::counter(true);
                let vocabulary = StepObservation::vocabulary_of(&specs).expect("vocabulary");
                let mut tests = two_tests();
                tests[1].oracles.push(occurs(&vocabulary, "branchTaken"));
                let campaign = counter_campaign(&validator, &specs, &tests, BUDGET);
                let generation = replay_generation(validator.baseline(), killing);
                let manifest = campaign_manifest(&ManifestInput {
                    campaign: &campaign,
                    generation: &generation,
                    schedule,
                    selection: PRIORITIZE,
                    operators: &[kink_campaign::ManifestOperator::Code(OperatorId {
                        id: "selection-test",
                        version: 1,
                        policy: CandidatePolicy::Each,
                    })],
                    classifier: "all-normal",
                })
                .expect("manifest");
                let run = run_campaign_with(&campaign, &generation, &options(schedule))
                    .expect("campaign");
                assert_eq!(
                    run.mutants[0].report.status,
                    if killing {
                        MutantStatus::Killed
                    } else {
                        MutantStatus::Survived
                    }
                );
                if killing && schedule == ScheduleMode::FirstKill {
                    assert_eq!(run.mutants[0].report.killing_test_ids, ["t2"]);
                    assert_eq!(run.mutants[0].report.skipped_test_ids, ["t1"]);
                }
                let report =
                    campaign_report(&manifest, &campaign, &generation, &run).expect("report");
                let artifact = manifest.baseline_input().text();
                let mut declaration = ReplayDeclaration {
                    module: "COUNTER",
                    observation: &specs,
                    classify: &normal,
                    classifier: "all-normal",
                    tests: &tests,
                    budget: BUDGET,
                    schedule,
                    selection: PRIORITIZE,
                    operators: &[kink_campaign::ReplayOperator::Code {
                        id: "selection-test",
                        version: 1,
                        policy: CandidatePolicy::Each,
                        select: &|b| Ok(replay_generation(b, killing)),
                    }],
                };
                assert_eq!(
                    replay(&report.text(), artifact, &declaration),
                    ReplayOutcome::Reproduced
                );
                assert_eq!(
                    report.value()["manifest"]["selection"],
                    json!({"prioritize":{"key":"compiled-rule-ids","coupled":"union","coverage":"kink/coverage/v1"}})
                );
                assert_eq!(
                    report.value()["mutants"][0]["selection"]["order"],
                    json!(["t2", "t1"])
                );
                assert_eq!(
                    report.value()["mutants"][0]["selection"]["deselected"],
                    json!([])
                );
                let mut changed = report.value().clone();
                changed["coverage"][0]["complete"] = json!(!run.baseline_coverage[0].complete);
                assert!(
                    matches!(replay(&canonical_json(&changed), artifact, &declaration), ReplayOutcome::Diverged {pointer, ..} if pointer == "/coverage/0/complete")
                );
                changed = report.value().clone();
                changed["mutants"][0]["selection"]["order"] = json!(["t1", "t2"]);
                assert!(
                    matches!(replay(&canonical_json(&changed), artifact, &declaration), ReplayOutcome::Diverged {pointer, ..} if pointer == "/mutants/0/selection/order/0")
                );
                declaration.selection = SelectionPolicy::None;
                assert_eq!(
                    replay(&report.text(), artifact, &declaration),
                    ReplayOutcome::Refused(ReplayRefusal::Declaration)
                );
                declaration.selection = SelectionPolicy::Prioritize(Sel {
                    coupled: Coupled::AllSites,
                });
                assert_eq!(
                    replay(&report.text(), artifact, &declaration),
                    ReplayOutcome::Refused(ReplayRefusal::Declaration)
                );
            }
        }
    });
}

/// H2 uses the existing A5 claim fixture; d's literal patch withdraws total from f and d.
#[test]
fn symbolic_test_uses_the_claim_withdrawn_side_for_its_removed_ids() {
    with_stack(|| {
        let validator = NativeValidator::bind(
            support::load_path(
                &std::path::Path::new(support::DIR).join("symbolic-claim-survivor.k"),
                "SYMPARTIAL",
            ),
            CompileOptions::default(),
        );
        let specs = step_support::guardedmem(true)[..2].to_vec();
        let vocabulary = StepObservation::vocabulary_of(&specs).expect("vocabulary");
        let atom = |constructor: &str, mode| Atom {
            constructor: constructor.into(),
            payload: vec![PayloadClause {
                position: 0,
                mode,
                variable: "A".into(),
            }],
        };
        let plan = PatternPlan::new(
            &vocabulary,
            vec![(
                "A".into(),
                k_rust::kompile::initial_configuration::kore_sort("SortInt"),
            )],
            vec![PatternArm {
                atoms: vec![
                    atom("memoryWrite", MatchMode::Bind),
                    atom("memoryLoad", MatchMode::Use),
                ],
                relations: vec![Relation::EventuallyAfter],
            }],
            None,
        )
        .expect("write-load plan");
        let oracle = OracleDeclaration::new(
            CrashPolicy::CompareIdentity,
            Projection::Pattern {
                plan,
                with_bindings: false,
            },
        )
        .expect("oracle");
        let address = || support::app("Lbladdr", vec![support::int(1)]);
        let program = support::app(
            "Lblseq",
            vec![
                support::app("Lblwrite", vec![address(), support::int(5)]),
                support::app(
                    "Lblseq",
                    vec![
                        support::app("Lblhalf", vec![support::var("X", "SortNat")]),
                        support::app(
                            "Lblseq",
                            vec![
                                support::app("Lblload", vec![address(), support::int(5)]),
                                support::app("Lblhalt", vec![]),
                            ],
                        ),
                    ],
                ),
            ],
        );
        let tests = [TestCase {
            id: "X".into(),
            initial_state: support::initial_state(program, "SortProg"),
            oracles: vec![oracle],
        }];
        let patch = replace(
            validator.baseline(),
            "SYMPARTIAL.d",
            &[0, 1],
            Term::Token {
                token: "2".into(),
                sort: KastSort::new("Int"),
            },
        );
        let generation = fixed(validator.baseline(), "SYMPARTIAL.d", &[0, 1], &patch);
        let claims = ClaimSupport::new(validator.baseline())
            .withdraw(validator.baseline(), &patch)
            .expect("withdrawal");
        assert_eq!(claims.withdrawn.len(), 2);
        let baseline = validator.compile_baseline().expect("baseline");
        let patched = validator.validate(&patch).expect("patched");
        let withdrawn = validator
            .validate(claims.patch().expect("withdrawn patch"))
            .expect("withdrawn side");
        assert_ne!(
            patched.kore_sha256(),
            withdrawn.kore_sha256(),
            "the actual symbolic side differs"
        );
        let patched_diff = CompiledEdit::between(&baseline, &patched);
        let withdrawn_diff = CompiledEdit::between(&baseline, &withdrawn);
        let campaign = Campaign {
            validator: &validator,
            module: "SYMPARTIAL",
            observation: &specs,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let run = run_campaign_with(&campaign, &generation, &options(schedule))
                .expect("symbolic baseline has write-load witness");
            let m = &run.mutants[0];
            assert_eq!(m.plan.claims, claims);
            let selection = m.plan.selection.as_ref().expect("selection");
            assert_eq!(selection.removed_rule_ids, withdrawn_diff.removed_rule_ids);
            assert_eq!(selection.global, withdrawn_diff.global);
            assert!(selection.global);
            assert_eq!(selection.order, ["X"]);
            assert_eq!(m.report.status, MutantStatus::Unknown);
            assert!(m.report.killing_test_ids.is_empty());
            eprintln!(
                "CS07_H2 fixture=symbolic-claim-survivor.k {schedule:?} selected=1 total=1 patched_removed={:?} withdrawn_removed={:?} equal_ids={} withdrawn_global={}",
                patched_diff.removed_rule_ids,
                withdrawn_diff.removed_rule_ids,
                patched_diff.removed_rule_ids == withdrawn_diff.removed_rule_ids,
                withdrawn_diff.global
            );
        }
    });
}

fn supplied_plan() -> (MutantPlan, Vec<ManifestTest>) {
    let manifest = vec![
        ManifestTest {
            test_id: "t1".into(),
            slot_count: 1,
        },
        ManifestTest {
            test_id: "t2".into(),
            slot_count: 2,
        },
    ];
    let plan = MutantPlan {
        mutant_id: MutantId(0),
        tests: vec![
            TestPlan {
                test_id: "t2".into(),
                run: TestRun::Compared(vec![OracleOutcome::Agree; 2]),
            },
            TestPlan {
                test_id: "t1".into(),
                run: TestRun::Compared(vec![OracleOutcome::Agree]),
            },
        ],
        mutant_failure: None,
        claims: Withdrawal::default(),
        selection: Some(MutantSelection {
            policy: PRIORITIZE,
            order: vec!["t2".into(), "t1".into()],
            deselected: vec![],
            global: false,
            removed_rule_ids: BTreeSet::new(),
        }),
    };
    (plan, manifest)
}
fn invalid(plan: &MutantPlan, manifest: &[ManifestTest], schedule: ScheduleMode) {
    assert_eq!(
        derive_mutant_report(plan, manifest, schedule)
            .expect_err("malformed schedule must be refused")
            .kind(),
        CampaignFailureKind::InvalidManifest
    );
}
#[test]
fn plan_accepts_only_the_recorded_prioritize_permutation_and_keeps_skip_guards() {
    for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
        let (plan, manifest) = supplied_plan();
        let report = derive_mutant_report(&plan, &manifest, schedule).expect("valid permutation");
        assert_eq!(report.status, MutantStatus::Survived);
        assert_eq!(report.executed_test_ids, ["t2", "t1"]);
        let mut changed = plan.clone();
        changed.selection = None;
        invalid(&changed, &manifest, schedule);
        let mut changed = plan.clone();
        changed.selection.as_mut().unwrap().policy = SelectionPolicy::None;
        invalid(&changed, &manifest, schedule);
        for order in [
            vec!["t1", "t2"],
            vec!["t2", "t2"],
            vec!["t2"],
            vec!["t2", "unknown"],
        ] {
            let mut changed = plan.clone();
            changed.selection.as_mut().unwrap().order =
                order.into_iter().map(str::to_owned).collect();
            invalid(&changed, &manifest, schedule);
        }
        let mut changed = plan.clone();
        changed.tests.swap(0, 1);
        invalid(&changed, &manifest, schedule);
        let mut changed = plan.clone();
        changed.tests[0].run = TestRun::Compared(vec![OracleOutcome::Agree]);
        invalid(&changed, &manifest, schedule);
        let mut changed = plan.clone();
        changed
            .selection
            .as_mut()
            .unwrap()
            .deselected
            .push("t1".into());
        invalid(&changed, &manifest, schedule);
        let mut changed = plan.clone();
        changed.tests[0].run = TestRun::SkippedAfterKill;
        assert_eq!(
            derive_mutant_report(&changed, &manifest, schedule)
                .expect_err("skip before kill")
                .kind(),
            CampaignFailureKind::FabricatedSkip
        );
    }
    let (mut plan, manifest) = supplied_plan();
    plan.tests[0].run = TestRun::Compared(vec![OracleOutcome::Distinguish, OracleOutcome::Agree]);
    plan.tests[1].run = TestRun::SkippedAfterKill;
    let report = derive_mutant_report(&plan, &manifest, ScheduleMode::FirstKill)
        .expect("recorded suffix skip after kill");
    assert_eq!(report.status, MutantStatus::Killed);
    assert_eq!(report.killing_test_ids, ["t2"]);
    assert_eq!(report.executed_test_ids, ["t2"]);
    assert_eq!(report.skipped_test_ids, ["t1"]);
    assert_eq!(
        derive_mutant_report(&plan, &manifest, ScheduleMode::Full)
            .expect_err("full cannot skip")
            .kind(),
        CampaignFailureKind::FabricatedSkip
    );
}

// ---------------------------------------------------------------- Theorem 2 over the representative set
//
// Until flow F-01 this file ran a copy of every campaign fixture of end_to_end.rs,
// coupled.rs and report.rs through the comparison below (119 tests). F-01 runs the
// representative set (representative/mod.rs) through the same check instead; the
// originals still run in their own files.

/// Fails if a fixture fired a wall-clock bound: Theorem 2 assumes none fires.
fn cs07_no_time_bound(run: &kink_campaign::CampaignRun) {
    use kink_campaign::{
        ExecutionFailureKind, MutantScopeFailure, OracleOutcome, OracleSide, SideRun, TestRun,
    };
    let evidence = run
        .baseline
        .iter()
        .chain(run.mutants.iter().flat_map(|mutant| mutant.evidence.iter()));
    for test in evidence {
        match &test.run {
            SideRun::Failed(ExecutionFailureKind::TimeLimit) => {
                panic!("CS07 STOP: fixture fired a wall-clock bound")
            }
            SideRun::Sides { sides } => assert!(
                !sides.contains(&OracleSide::Timeout),
                "CS07 STOP: fixture fired a wall-clock bound"
            ),
            SideRun::Failed(_) => {}
        }
    }
    for mutant in &run.mutants {
        assert_ne!(
            mutant.plan.mutant_failure,
            Some(MutantScopeFailure::LoweringTimeLimit),
            "CS07 STOP: lowering wall-clock bound"
        );
        for test in &mutant.plan.tests {
            match &test.run {
                TestRun::Failed(ExecutionFailureKind::TimeLimit) => {
                    panic!("CS07 STOP: fixture fired a wall-clock bound")
                }
                TestRun::Compared(outcomes) => assert!(
                    !outcomes.contains(&OracleOutcome::Timeout),
                    "CS07 STOP: fixture fired a wall-clock bound"
                ),
                _ => {}
            }
        }
    }
}

/// CS-07 Theorem 2 (README 5.4 as corrected): under Prioritize, with either coupled
/// rule, every mutant keeps its `none` status and the score is unchanged; in Full its
/// killing set is equal, in FirstKill it is non-empty iff it is under `none` and a subset
/// of the Full killing set. The check of the replaced copy suites, over a list of
/// generations.
fn cs07_check_theorem(
    name: &str,
    campaign: &Campaign<'_>,
    generations: &[CandidateGeneration<'_>],
    none_full: &kink_campaign::CampaignRun,
    none_first: &kink_campaign::CampaignRun,
) {
    cs07_no_time_bound(none_full);
    cs07_no_time_bound(none_first);
    for coupled in [Coupled::Union, Coupled::AllSites] {
        let policy = SelectionPolicy::Prioritize(Sel { coupled });
        for (schedule, none) in [
            (ScheduleMode::Full, none_full),
            (ScheduleMode::FirstKill, none_first),
        ] {
            let prioritized = kink_campaign::run_campaign_multi(
                campaign,
                generations,
                &CampaignOptions {
                    schedule,
                    selection: policy,
                    share_evidence: true,
                },
            )
            .expect("CS07 Theorem 2: an admitted none fixture stays admitted");
            cs07_no_time_bound(&prioritized);
            assert_eq!(
                none.mutants.len(),
                prioritized.mutants.len(),
                "{name}: candidate count"
            );
            assert_eq!(none.score, prioritized.score, "{name}: score");
            for ((original, mutant), full) in none
                .mutants
                .iter()
                .zip(&prioritized.mutants)
                .zip(&none_full.mutants)
            {
                if coupled == Coupled::Union && schedule == ScheduleMode::Full {
                    let (selected, order) = if let Some(selection) = &mutant.plan.selection {
                        (
                            cs07_selected_count(
                                campaign,
                                generations,
                                &prioritized,
                                mutant,
                                coupled,
                            ),
                            selection.order.as_slice(),
                        )
                    } else {
                        (0, &[][..])
                    };
                    eprintln!(
                        "CS07_FIXTURE {name} {} {:?} {coupled:?} {schedule:?} selected={}/{} order={:?} failure={:?}",
                        campaign.module,
                        mutant.report.mutant_id,
                        selected,
                        campaign.tests.len(),
                        order,
                        mutant.plan.mutant_failure
                    );
                }
                assert_eq!(
                    original.report.mutant_id, mutant.report.mutant_id,
                    "{name}: candidate pairing"
                );
                assert_eq!(
                    original.report.status, mutant.report.status,
                    "{name}/{coupled:?}/{schedule:?}: Theorem 2 status"
                );
                let kills = mutant
                    .report
                    .killing_test_ids
                    .iter()
                    .collect::<BTreeSet<_>>();
                let original_kills = original
                    .report
                    .killing_test_ids
                    .iter()
                    .collect::<BTreeSet<_>>();
                let full_kills = full.report.killing_test_ids.iter().collect::<BTreeSet<_>>();
                if schedule == ScheduleMode::Full {
                    assert_eq!(
                        original_kills, kills,
                        "{name}/{coupled:?}: Full killing set"
                    );
                } else {
                    assert_eq!(
                        original_kills.is_empty(),
                        kills.is_empty(),
                        "{name}/{coupled:?}: FirstKill existence"
                    );
                    assert!(
                        kills.is_subset(&full_kills),
                        "{name}/{coupled:?}: FirstKill killing subset"
                    );
                }
            }
        }
    }
}

/// How many tests coverage selects for `mutant` (all of them for a global edit or an
/// empty selection), recomputed from its compiled sides: the CS07_FIXTURE record.
fn cs07_selected_count(
    campaign: &Campaign<'_>,
    generations: &[CandidateGeneration<'_>],
    run: &kink_campaign::CampaignRun,
    mutant: &kink_campaign::MutantRun,
    coupled: Coupled,
) -> usize {
    let selection = mutant.plan.selection.as_ref().expect("selection");
    if selection.global {
        return campaign.tests.len();
    }
    let baseline = campaign.validator.compile_baseline().expect("baseline");
    let authors = kink_native::coverage::RuleAuthors::of(&baseline);
    let patch = &generations
        .iter()
        .flat_map(CandidateGeneration::candidates)
        .nth(mutant.report.mutant_id.0)
        .expect("candidate")
        .patch;
    let patched = campaign.validator.validate(patch).expect("patched");
    let withdrawn = mutant
        .plan
        .claims
        .patch()
        .map(|patch| campaign.validator.validate(patch).expect("withdrawn"));
    let mut selected = 0;
    for test in campaign.tests {
        let side = if test.initial_state.variable_occurrences().is_empty() {
            &patched
        } else {
            withdrawn.as_ref().unwrap_or(&patched)
        };
        let edit = CompiledEdit::between(&baseline, side);
        let groups = patch
            .written_sentences()
            .iter()
            .map(|at| {
                authors
                    .ids_of(at)
                    .filter(|id| edit.removed_rule_ids.contains(*id))
                    .map(str::to_owned)
                    .collect::<BTreeSet<_>>()
            })
            .collect::<Vec<_>>();
        let coverage = run
            .baseline_coverage
            .iter()
            .find(|coverage| coverage.test_id == test.id)
            .expect("coverage");
        selected += usize::from(coverage_selected(coverage, &edit, coupled, &groups));
    }
    if selected == 0 {
        campaign.tests.len()
    } else {
        selected
    }
}

/// F-01: Prioritize keeps every `none` status and killing set (Theorem 2) on every case
/// of the representative set, in both schedules and under both coupled rules; each case
/// also keeps what its original test pins. A case that fires a wall-clock bound by design
/// is run but not compared, as CS-07 excluded it.
#[test]
fn prioritize_preserves_every_representative_campaign() {
    with_stack(|| {
        let mut coverage = representative::Coverage::default();
        representative::representative_set(&mut |case| {
            eprintln!("F01_SELECTION_CASE {}", case.name);
            let none = |schedule| {
                kink_campaign::run_campaign_multi(
                    &case.campaign,
                    &case.generations,
                    &CampaignOptions {
                        schedule,
                        selection: SelectionPolicy::None,
                        share_evidence: true,
                    },
                )
            };
            let full = none(ScheduleMode::Full);
            let first = none(ScheduleMode::FirstKill);
            representative::check_expected(case, &full, &first);
            coverage.record(case, &full);
            if let (Ok(full), Ok(first)) = (&full, &first)
                && !case.wall_clock_bound
            {
                cs07_check_theorem(&case.name, &case.campaign, &case.generations, full, first);
            }
        });
        coverage.assert_complete();
    });
}

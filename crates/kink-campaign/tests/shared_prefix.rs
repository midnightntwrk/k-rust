//! Shared-prefix campaign pattern sides equal the reference on the same compiled sides.

#[path = "../../../testdata/k/support.rs"]
mod support;

#[path = "../../../testdata/k/step_support.rs"]
mod step_support;

use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::definition::AttributeKey;
use k_rust::kast::{Sort as KastSort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
use k_rust::kore::{ast::Pattern, parser::parse_definition};
use kink_campaign::{
    Campaign, CampaignRun, CrashPolicy, OracleDeclaration, Projection, ScheduleMode,
    StateProjection, TestCase, run_campaign,
};
use kink_campaign::{
    MutantStatus, OracleSide, OracleValue, PatternValue, Projection as OracleProjection, SideRun,
    pattern_side,
};
use kink_native::NativeValidator;
use kink_native::bridge::{BridgeContext, paths_from_steps, tree_from_steps};
use kink_native::execution::{ExecutionAdapter, ExecutionBudget, SolverProfile};
use kink_native::feasibility::{BackendRelations, TestInitialState};
use kink_native::step_events::{ObservationDecider, StepEventSpec, StepObservation};
use kink_patch::{
    Baseline, CandidateGeneration, Discovery, Edit, Patch, SelectionPolicy, SiteSelector, TermRef,
    derive_sites, select,
};
use kink_pattern::{
    Atom, EvaluationContext, EvaluationOptions, EventVocabulary, ExecutionTerminalKind,
    MonitorOptions, PatternArm, PatternOutcome, PatternPlan, Relation, SearchPolicy, SymbolSorts,
    TreeOptions, evaluate_tree_with_stats, evaluate_with,
};

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
};

fn with_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 << 20)
        .spawn(body)
        .expect("test thread")
        .join()
        .expect("test thread does not panic");
}

fn app(symbol: &str, arguments: Vec<Pattern>) -> Pattern {
    kore_application(symbol, Vec::new(), arguments)
}

fn counter_state() -> Pattern {
    let z = || app("Lblz", vec![]);
    let s = |p| app("Lbls", vec![p]);
    support::initial_state(app("Lblcounter", vec![z(), s(s(s(z())))]), "SortCounter")
}

fn choose_state() -> Pattern {
    support::initial_state(
        app(
            "Lblchoose",
            vec![Pattern::DomainValue {
                sort: kore_sort("SortBool"),
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
    .expect("final-result declaration")
}

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

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

/// One mutant: the term at `path` of the rule labelled `rule` replaced by `replacement`.
fn generation<'b>(
    baseline: &'b Baseline,
    rule: &str,
    path: &[u32],
    replacement: Term,
) -> CandidateGeneration<'b> {
    let at = TermRef::new(support::rule(baseline, rule), path);
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("site term").clone(),
        at: at.clone(),
        replacement,
    }])
    .expect("one edit");
    let label = baseline
        .sentence(&at.sentence)
        .and_then(|rule| rule.attributes().string(AttributeKey::Label))
        .expect("labelled")
        .to_owned();
    let discovery = derive_sites(
        baseline,
        "site",
        &[
            SiteSelector::RuleLabel(label),
            SiteSelector::Path(path.to_vec()),
        ],
    )
    .expect("sites");
    let all = Discovery::empty(baseline, false, false)
        .union(&discovery)
        .expect("one baseline");
    select(&all, SelectionPolicy::Each, 1)
        .expect("selection")
        .fold("mutant", |_| patch.clone())
        .expect("fold")
}

/// `branch: requires false`, at its condition as its site.
fn branch_false(baseline: &Baseline) -> CandidateGeneration<'_> {
    generation(
        baseline,
        "COUNTER.branch",
        &[1],
        Term::Token {
            token: "false".to_owned(),
            sort: KastSort::new("Bool"),
        },
    )
}

/// CS-06 review 1's mutant: `COUNTER.increment` at `[0, 1, 0]` replaced by its own child.
fn increment_child(baseline: &Baseline) -> CandidateGeneration<'_> {
    let at = TermRef::new(support::rule(baseline, "COUNTER.increment"), [0, 1, 0, 0]);
    let child = baseline.term(&at).expect("child term").clone();
    generation(baseline, "COUNTER.increment", &[0, 1, 0], child)
}

fn tests(vocabulary: &EventVocabulary) -> Vec<TestCase> {
    vec![
        TestCase {
            id: "t1".to_owned(),
            initial_state: counter_state(),
            oracles: vec![whole_term(), occurs(vocabulary, "increment")],
        },
        TestCase {
            id: "t2".to_owned(),
            initial_state: choose_state(),
            oracles: vec![whole_term()],
        },
    ]
}

fn run(
    validator: &NativeValidator,
    specs: &[StepEventSpec],
    tests: &[TestCase],
    generation: &CandidateGeneration<'_>,
    schedule: ScheduleMode,
) -> CampaignRun {
    run_campaign(
        &Campaign {
            validator,
            module: "COUNTER",
            observation: specs,
            classify: &normal,
            tests,
            budget: BUDGET,
        },
        generation,
        schedule,
    )
    .expect("campaign")
}

/// The reference evaluation of one slot on one side, and what the bare shared-prefix
/// evaluator with the default monitor cap gives on the same side.
struct ReferenceSide {
    side: OracleSide,
    capped: PatternOutcome,
    overflowed: bool,
}

/// Slot `slot` of `test` on the baseline and on the generation's single mutant: each side's
/// stepped run bridged by `paths_from_steps` and evaluated by `evaluate_with` with one
/// baseline-owned decider, as `step_sides` did before CS-06.
fn reference_sides(
    validator: &NativeValidator,
    specs: &[StepEventSpec],
    test: &TestCase,
    slot: usize,
    generation: &CandidateGeneration<'_>,
) -> Vec<ReferenceSide> {
    let baseline = validator.compile_baseline().expect("baseline");
    let mut shared = Backend::from_definition(
        parse_definition(&baseline.artifacts().definition_kore).expect("KORE"),
        "COUNTER",
        BackendOptions::default(),
    )
    .expect("shared backend");
    let observation = StepObservation::new(&mut shared, specs.to_vec()).expect("observation");
    let patched = validator
        .validate(&generation.candidates()[0].patch)
        .expect("mutant");
    let context = EvaluationContext {
        test_id: test.id.clone(),
        bounds: BUDGET.bounds(),
        vocabulary: StepObservation::vocabulary_of(specs).expect("vocabulary"),
        symbol_sorts: SymbolSorts::from_definition(
            &parse_definition(&baseline.artifacts().definition_kore).expect("KORE"),
        ),
    };
    let options = EvaluationOptions {
        stable_path_keys: true,
        search_policy: SearchPolicy::Exhaustive,
        input_error: false,
    };
    let OracleProjection::Pattern {
        plan,
        with_bindings,
    } = test.oracles[slot].projection()
    else {
        panic!("pattern slot")
    };
    let mut expected = Vec::new();
    for side in [&baseline, &patched] {
        let mut backend = Backend::from_definition(
            parse_definition(&side.artifacts().definition_kore).expect("KORE"),
            "COUNTER",
            BackendOptions::default(),
        )
        .expect("backend");
        let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
            .execute_steps(&mut backend, &test.initial_state, BUDGET)
            .expect("adapter")
            .expect("steps");
        let value = shared
            .with_solver(None, |definition, solver| {
                let decider = ObservationDecider::new(
                    definition,
                    solver,
                    TestInitialState::of_test(&test.initial_state),
                );
                let relations = BackendRelations::shared(
                    definition,
                    solver,
                    TestInitialState::of_test(&test.initial_state),
                );
                let bridge = BridgeContext {
                    test_id: &test.id,
                    classify: &normal,
                    sorts: &context.symbol_sorts,
                };
                let paths = paths_from_steps(&bridge, &execution, &observation, &decider)
                    .expect("reference paths");
                let side = pattern_side(
                    &evaluate_with(
                        &context,
                        plan,
                        &paths.paths,
                        &paths.collection,
                        None,
                        options,
                        &relations,
                    ),
                    *with_bindings,
                );
                let tree =
                    tree_from_steps(&bridge, &execution, &observation, &decider).expect("tree");
                let (capped, stats) = evaluate_tree_with_stats(
                    &context,
                    plan,
                    &tree.tree,
                    &tree.collection,
                    None,
                    TreeOptions {
                        evaluation: options,
                        monitor: MonitorOptions::default(),
                    },
                    &relations,
                )
                .expect("tree evaluation");
                Ok::<_, k_rust::backend::BackendError>(ReferenceSide {
                    side,
                    capped: capped.outcome,
                    overflowed: stats.overflowed,
                })
            })
            .expect("shared decider");
        expected.push(value);
    }
    expected
}

/// The campaign's slot sides on the baseline and on mutant 0, for test `test`.
fn campaign_sides(campaign: &CampaignRun, test: usize, slot: usize) -> [OracleSide; 2] {
    let SideRun::Sides { sides: baseline } = &campaign.baseline[test].run else {
        panic!("baseline sides")
    };
    let evidence = campaign.mutants[0]
        .evidence
        .iter()
        .find(|evidence| evidence.test_id == campaign.baseline[test].test_id)
        .expect("the test ran on the mutant");
    let SideRun::Sides { sides: mutant } = &evidence.run else {
        panic!("mutant sides")
    };
    [baseline[slot].clone(), mutant[slot].clone()]
}

/// Baseline and patched sides are compared with one baseline-owned decider, with both
/// schedules. A state-only test follows the pattern test to exercise cache lifetime.
#[test]
fn campaign_pattern_sides_equal_the_reference_in_both_schedules() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let specs = step_support::counter(true);
        let vocabulary = StepObservation::vocabulary_of(&specs).expect("vocabulary");
        let tests = tests(&vocabulary);
        let generation = branch_false(validator.baseline());
        let expected = reference_sides(&validator, &specs, &tests[0], 1, &generation);
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let campaign = run(&validator, &specs, &tests, &generation, schedule);
            let [baseline, mutant] = campaign_sides(&campaign, 0, 1);
            assert_eq!(baseline, expected[0].side);
            assert_eq!(mutant, expected[1].side);
            assert_eq!(campaign.baseline_coverage.len(), tests.len());
        }
    });
}

/// A plan of one arm `increment`, with an arm without atoms inserted in front of it after
/// `PatternPlan::new` (its fields are public and nothing on the campaign path re-validates).
fn empty_arm_plan(vocabulary: &EventVocabulary) -> OracleDeclaration {
    let Projection::Pattern { mut plan, .. } = occurs(vocabulary, "increment").projection().clone()
    else {
        panic!("pattern")
    };
    plan.arms.insert(
        0,
        PatternArm {
            atoms: Vec::new(),
            relations: Vec::new(),
        },
    );
    OracleDeclaration::new(
        CrashPolicy::CompareIdentity,
        Projection::Pattern {
            plan,
            with_bindings: false,
        },
    )
    .expect("the campaign API accepts the edited plan")
}

/// CS-06 review 1, critical: on a plan edited after validation (an arm without atoms) the
/// shared-prefix monitor and `evaluate_with` disagree, and at b3a1fab the campaign killed a
/// mutant the reference leaves `Survived`. The campaign must keep the reference sides, status
/// and killing tests in both schedules, alone and next to a plain test.
#[test]
fn an_edited_plan_keeps_the_reference_sides_and_verdict() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let specs = step_support::counter(true);
        let vocabulary = StepObservation::vocabulary_of(&specs).expect("vocabulary");
        let generation = increment_child(validator.baseline());
        let edited = TestCase {
            id: "empty-arm".to_owned(),
            initial_state: counter_state(),
            oracles: vec![empty_arm_plan(&vocabulary)],
        };
        let plain = TestCase {
            id: "plain".to_owned(),
            initial_state: counter_state(),
            oracles: vec![occurs(&vocabulary, "increment")],
        };
        let expected = reference_sides(&validator, &specs, &edited, 0, &generation);
        let matched =
            OracleSide::Normal(OracleValue::Pattern(PatternValue::Match { bindings: None }));
        assert_eq!(expected[0].side, matched, "reference baseline side");
        assert_eq!(expected[1].side, matched, "reference mutant side");
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let alone = run(
                &validator,
                &specs,
                std::slice::from_ref(&edited),
                &generation,
                schedule,
            );
            let [baseline, mutant] = campaign_sides(&alone, 0, 0);
            assert_eq!(baseline, expected[0].side, "{schedule:?} baseline");
            assert_eq!(mutant, expected[1].side, "{schedule:?} mutant");
            assert_eq!(
                alone.mutants[0].report.status,
                MutantStatus::Survived,
                "{schedule:?}"
            );
            assert!(
                alone.mutants[0].report.killing_test_ids.is_empty(),
                "{schedule:?}"
            );

            let both = run(
                &validator,
                &specs,
                &[edited.clone(), plain.clone()],
                &generation,
                schedule,
            );
            assert_eq!(
                both.mutants[0].report.status,
                MutantStatus::Killed,
                "{schedule:?}"
            );
            assert_eq!(
                both.mutants[0].report.killing_test_ids,
                vec!["plain".to_owned()],
                "{schedule:?}"
            );
            let [baseline, mutant] = campaign_sides(&both, 0, 0);
            assert_eq!(
                baseline, expected[0].side,
                "{schedule:?} baseline, two tests"
            );
            assert_eq!(mutant, expected[1].side, "{schedule:?} mutant, two tests");
        }
    });
}

fn counter_of(steps: usize) -> Pattern {
    let mut remaining = app("Lblz", vec![]);
    for _ in 0..steps {
        remaining = app("Lbls", vec![remaining]);
    }
    support::initial_state(
        app("Lblcounter", vec![app("Lblz", vec![]), remaining]),
        "SortCounter",
    )
}

/// `increment EventuallyAfter increment EventuallyAfter increment EventuallyAfter
/// branchTaken`: never complete on a counter run, with k + C(k, 2) + C(k, 3) live partials
/// after k increments (4,525 at k = 30, above `DEFAULT_PARTIAL_CAP`).
fn partial_heavy(vocabulary: &EventVocabulary) -> OracleDeclaration {
    let atom = |constructor: &str| Atom {
        constructor: constructor.to_owned(),
        payload: Vec::new(),
    };
    let plan = PatternPlan::new(
        vocabulary,
        Vec::new(),
        vec![PatternArm {
            atoms: vec![
                atom("increment"),
                atom("increment"),
                atom("increment"),
                atom("branchTaken"),
            ],
            relations: vec![Relation::EventuallyAfter; 3],
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

/// CS-06 review 1, minor: the campaign bounds the monitor's live partials, and an overflow
/// never reaches a side. The bare capped evaluator overflows here and is `Unknown`; the
/// campaign's sides are the reference's `NoMatch` (a baseline `Unknown` would refuse the
/// campaign), in both schedules.
#[test]
fn a_monitor_cap_overflow_keeps_the_reference_sides() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let specs = step_support::counter(true);
        let vocabulary = StepObservation::vocabulary_of(&specs).expect("vocabulary");
        let generation = branch_false(validator.baseline());
        let test = TestCase {
            id: "partials".to_owned(),
            initial_state: counter_of(30),
            oracles: vec![partial_heavy(&vocabulary)],
        };
        let expected = reference_sides(&validator, &specs, &test, 0, &generation);
        let no_match = OracleSide::Normal(OracleValue::Pattern(PatternValue::NoMatch));
        for side in &expected {
            assert_eq!(side.side, no_match, "reference side");
            assert!(side.overflowed, "the default cap overflows");
            assert_eq!(side.capped, PatternOutcome::Unknown, "capped evaluator");
        }
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let campaign = run(
                &validator,
                &specs,
                std::slice::from_ref(&test),
                &generation,
                schedule,
            );
            let [baseline, mutant] = campaign_sides(&campaign, 0, 0);
            assert_eq!(baseline, no_match, "{schedule:?} baseline");
            assert_eq!(mutant, no_match, "{schedule:?} mutant");
            assert_eq!(
                campaign.mutants[0].report.status,
                MutantStatus::Survived,
                "{schedule:?}"
            );
        }
    });
}

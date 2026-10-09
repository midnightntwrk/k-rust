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
use kink_campaign::{Projection as OracleProjection, SideRun, pattern_side};
use kink_native::NativeValidator;
use kink_native::bridge::{BridgeContext, paths_from_steps};
use kink_native::execution::{ExecutionAdapter, ExecutionBudget, SolverProfile};
use kink_native::feasibility::{BackendRelations, TestInitialState};
use kink_native::step_events::{ObservationDecider, StepEventSpec, StepObservation};
use kink_patch::{
    Baseline, CandidateGeneration, Discovery, Edit, Patch, SelectionPolicy, SiteSelector, TermRef,
    derive_sites, select,
};
use kink_pattern::{
    Atom, EvaluationContext, EvaluationOptions, EventVocabulary, ExecutionTerminalKind, PatternArm,
    PatternPlan, SearchPolicy, SymbolSorts, evaluate_with,
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

/// `branch: requires false`, at its condition as its site.
fn generation(baseline: &Baseline) -> CandidateGeneration<'_> {
    let at = TermRef::new(support::rule(baseline, "COUNTER.branch"), [1]);
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("condition").clone(),
        at: at.clone(),
        replacement: Term::Token {
            token: "false".to_owned(),
            sort: KastSort::new("Bool"),
        },
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
        &[SiteSelector::RuleLabel(label), SiteSelector::Path(vec![1])],
    )
    .expect("sites");
    let all = Discovery::empty(baseline, false, false)
        .union(&discovery)
        .expect("one baseline");
    select(&all, SelectionPolicy::Each, 1)
        .expect("selection")
        .fold("branch-false", |_| patch.clone())
        .expect("fold")
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
        &generation(validator.baseline()),
        schedule,
    )
    .expect("campaign")
}

/// Baseline and patched sides are compared with one baseline-owned decider, with both
/// schedules. A state-only test follows the pattern test to exercise cache lifetime.
#[test]
fn campaign_pattern_sides_equal_the_reference_in_both_schedules() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let baseline = validator.compile_baseline().expect("baseline");
        let specs = step_support::counter(true);
        let vocabulary = StepObservation::vocabulary_of(&specs).expect("vocabulary");
        let tests = tests(&vocabulary);
        let mut shared = Backend::from_definition(
            parse_definition(&baseline.artifacts().definition_kore).expect("KORE"),
            "COUNTER",
            BackendOptions::default(),
        )
        .expect("shared backend");
        let observation = StepObservation::new(&mut shared, specs.clone()).expect("observation");
        let generation = generation(validator.baseline());
        let patched = validator
            .validate(&generation.candidates()[0].patch)
            .expect("mutant");
        let context = EvaluationContext {
            test_id: tests[0].id.clone(),
            bounds: BUDGET.bounds(),
            vocabulary: vocabulary.clone(),
            symbol_sorts: SymbolSorts::from_definition(
                &parse_definition(&baseline.artifacts().definition_kore).expect("KORE"),
            ),
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
                .execute_steps(&mut backend, &tests[0].initial_state, BUDGET)
                .expect("adapter")
                .expect("steps");
            let value = shared
                .with_solver(None, |definition, solver| {
                    let decider = ObservationDecider::new(
                        definition,
                        solver,
                        TestInitialState::of_test(&tests[0].initial_state),
                    );
                    let relations = BackendRelations::shared(
                        definition,
                        solver,
                        TestInitialState::of_test(&tests[0].initial_state),
                    );
                    let paths = paths_from_steps(
                        &BridgeContext {
                            test_id: &tests[0].id,
                            classify: &normal,
                            sorts: &context.symbol_sorts,
                        },
                        &execution,
                        &observation,
                        &decider,
                    )
                    .expect("reference paths");
                    let OracleProjection::Pattern {
                        plan,
                        with_bindings,
                    } = tests[0].oracles[1].projection()
                    else {
                        panic!("pattern")
                    };
                    Ok::<_, k_rust::backend::BackendError>(pattern_side(
                        &evaluate_with(
                            &context,
                            plan,
                            &paths.paths,
                            &paths.collection,
                            None,
                            EvaluationOptions {
                                stable_path_keys: true,
                                search_policy: SearchPolicy::Exhaustive,
                                input_error: false,
                            },
                            &relations,
                        ),
                        *with_bindings,
                    ))
                })
                .expect("shared decider");
            expected.push(value);
        }
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let campaign = run(&validator, &specs, &tests, schedule);
            let SideRun::Sides { sides } = &campaign.baseline[0].run else {
                panic!("baseline sides")
            };
            assert_eq!(sides[1], expected[0]);
            let SideRun::Sides { sides } = &campaign.mutants[0].evidence[0].run else {
                panic!("mutant sides")
            };
            assert_eq!(sides[1], expected[1]);
            assert_eq!(campaign.baseline_coverage.len(), tests.len());
        }
    });
}

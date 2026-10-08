//! `CampaignRun::baseline_coverage`: the rule coverage of the baseline runs a campaign already
//! makes, in manifest order (corpus-scale CS-03, README section 4.5). It is recorded only: no
//! status, killing test or score depends on it.

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
use kink_native::coverage::{RuleAuthors, TestCoverage, coverage_digest};
use kink_native::execution::{ExecutionAdapter, ExecutionBudget, SolverProfile};
use kink_native::step_events::{StepEventSpec, StepObservation};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::{
    Baseline, CandidateGeneration, Discovery, Edit, Patch, SelectionPolicy, SentenceRef,
    SiteSelector, TermRef, derive_sites, select,
};
use kink_pattern::{Atom, EventVocabulary, ExecutionTerminalKind, PatternArm, PatternPlan};

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

/// The coverage of `test`'s observed run on a fresh backend of `side`.
fn direct(side: &ValidatedDefinition, test: &TestCase) -> TestCoverage {
    let mut backend = Backend::from_definition(
        parse_definition(&side.artifacts().definition_kore).expect("KORE"),
        "COUNTER",
        BackendOptions::default(),
    )
    .expect("backend");
    let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute(&mut backend, &test.initial_state, BUDGET)
        .expect("run");
    TestCoverage::of_execution(&test.id, &execution, &RuleAuthors::of(side))
}

/// One coverage entry per test, in manifest order, equal to a direct computation from the
/// same test's run (the stepped run of t1 included), in both schedules; reordering the tests
/// reorders the entries and changes nothing else.
#[test]
fn campaign_run_records_baseline_coverage_in_manifest_order() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let side = validator.compile_baseline().expect("baseline");
        let specs = step_support::counter(true);
        let vocabulary = StepObservation::vocabulary_of(&specs).expect("vocabulary");
        let tests = tests(&vocabulary);
        let full = run(&validator, &specs, &tests, ScheduleMode::Full);
        let first_kill = run(&validator, &specs, &tests, ScheduleMode::FirstKill);
        assert_eq!(
            full.baseline_coverage
                .iter()
                .map(|coverage| coverage.test_id.as_str())
                .collect::<Vec<_>>(),
            ["t1", "t2"]
        );
        assert_eq!(full.baseline_coverage, first_kill.baseline_coverage);
        for (test, coverage) in tests.iter().zip(&full.baseline_coverage) {
            assert_eq!(coverage, &direct(&side, test), "{}", test.id);
            assert!(coverage.complete, "{}", test.id);
            assert!(coverage.unmapped.is_empty(), "{}", test.id);
        }
        assert_eq!(
            full.baseline_coverage[0].sentences,
            [SentenceRef::new("COUNTER", 0)].into_iter().collect()
        );
        assert_eq!(
            full.baseline_coverage[1].sentences,
            [SentenceRef::new("COUNTER", 1)].into_iter().collect()
        );
        eprintln!(
            "CAMPAIGN_COVERAGE_DIGEST {}",
            coverage_digest(&full.baseline_coverage)
        );

        let reversed = tests.iter().rev().cloned().collect::<Vec<_>>();
        let reordered = run(&validator, &specs, &reversed, ScheduleMode::Full);
        assert_eq!(
            reordered.baseline_coverage,
            full.baseline_coverage
                .iter()
                .rev()
                .cloned()
                .collect::<Vec<_>>()
        );
        assert_eq!(
            reordered
                .mutants
                .iter()
                .map(|mutant| mutant.report.status)
                .collect::<Vec<_>>(),
            full.mutants
                .iter()
                .map(|mutant| mutant.report.status)
                .collect::<Vec<_>>()
        );
    });
}

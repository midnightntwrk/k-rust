//! Campaign relation decisions over observed memory payloads.

#[path = "../../../testdata/k/support.rs"]
mod support;

#[path = "../../../testdata/k/step_support.rs"]
mod step_support;

use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kast::Term;
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::kore_sort;
use k_rust::kore::{ast::Pattern, parser::parse_definition};
use kink_campaign::{
    Campaign, CampaignFailureKind, CrashPolicy, OracleDeclaration, OracleOutcome, OracleSide,
    OracleValue, PatternValue, Projection, ScheduleMode, SideRun, TestCase, TestRun, run_campaign,
};
use kink_native::NativeValidator;
use kink_native::execution::{
    ExecutionAdapter, ExecutionAdapterFailure, ExecutionBudget, SolverProfile,
};
use kink_native::step_events::StepObservation;
use kink_patch::{Edit, Patch, SelectionPolicy, SiteSelector, TermRef, derive_sites, select};
use kink_pattern::{
    Atom, EventVocabulary, ExecutionTerminalKind, MatchMode, PatternArm, PatternPlan,
    PayloadClause, Relation,
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

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

fn app(symbol: &str, args: Vec<Pattern>) -> Pattern {
    support::app(&format!("Lbl{symbol}"), args)
}

fn state(write_address: Pattern, load_address: Pattern) -> Pattern {
    support::initial_state(
        app(
            "seq",
            vec![
                app(
                    "write",
                    vec![write_address, app("s", vec![app("z", vec![])])],
                ),
                app(
                    "seq",
                    vec![
                        app("load", vec![load_address, app("s", vec![app("z", vec![])])]),
                        app("halt", vec![]),
                    ],
                ),
            ],
        ),
        "SortProg",
    )
}

fn wl_after(vocabulary: &EventVocabulary) -> OracleDeclaration {
    let plan = PatternPlan::new(
        vocabulary,
        vec![("A".into(), kore_sort("SortAddress"))],
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
            relations: vec![Relation::EventuallyAfter],
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
    .expect("oracle")
}

#[test]
fn opaque_payloads_do_not_decide_a_pattern() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("opaquemem.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let site = TermRef::new(support::rule(baseline, "OPAQUEMEM.write"), [0, 1]);
        let continuation = baseline.term(&site).expect("write continuation").clone();
        let address = baseline
            .term(&TermRef::new(site.sentence.clone(), [0, 0, 0, 0]))
            .expect("write address")
            .clone();
        let value = baseline
            .term(&TermRef::new(site.sentence.clone(), [0, 0, 0, 1]))
            .expect("write value")
            .clone();
        let patch = Patch::new(vec![Edit::ReplaceTerm {
            at: site.clone(),
            expected: continuation.clone(),
            replacement: Term::apply(
                "seq",
                vec![Term::apply("load", vec![address, value]), continuation],
            ),
        }])
        .expect("one edit");
        let discovery = derive_sites(
            baseline,
            "write-continuation",
            &[
                SiteSelector::RuleLabel("OPAQUEMEM.write".into()),
                SiteSelector::Path(site.path.0.clone()),
            ],
        )
        .expect("one exact site");
        assert!(discovery.exhaustive());
        let generation = select(
            &discovery,
            SelectionPolicy::Exact {
                expected_tuple_count: 1,
                expected_tuple_arity: 1,
            },
            1,
        )
        .expect("selection")
        .fold("repeat-written-address", |_| patch.clone())
        .expect("candidate");
        assert!(generation.scored());
        assert_eq!(generation.candidates().len(), 1);

        let specs = step_support::symmem(false)[..2].to_vec();
        let vocabulary = StepObservation::vocabulary_of(&specs).expect("vocabulary");
        let oracle = wl_after(&vocabulary);
        let z = app("z", vec![]);
        let opaque = TestCase {
            id: "opaque".into(),
            initial_state: state(app("opaque", vec![z.clone()]), app("addr", vec![z.clone()])),
            oracles: vec![oracle.clone()],
        };
        let campaign = |tests| Campaign {
            validator: &validator,
            module: "OPAQUEMEM",
            observation: &specs,
            classify: &normal,
            tests,
            budget: BUDGET,
        };
        let opaque_tests = [opaque];
        let failure = run_campaign(&campaign(&opaque_tests), &generation, ScheduleMode::Full)
            .expect_err("opaque relation is undecided");
        assert_eq!(failure.kind(), CampaignFailureKind::BaselineOracleFailed);

        let clash = TestCase {
            id: "clash".into(),
            initial_state: state(
                app("addr", vec![z.clone()]),
                app("addr", vec![app("s", vec![z])]),
            ),
            oracles: vec![oracle],
        };
        let clash_tests = [clash];
        let run = run_campaign(&campaign(&clash_tests), &generation, ScheduleMode::Full)
            .expect("constructor clash is decided");
        assert_eq!(
            run.baseline[0].run,
            SideRun::Sides {
                sides: vec![OracleSide::Normal(OracleValue::Pattern(
                    PatternValue::NoMatch
                ))],
            }
        );
        assert_eq!(run.mutants.len(), 1);
        assert_eq!(
            run.mutants[0].plan.tests[0].run,
            TestRun::Compared(vec![OracleOutcome::Distinguish])
        );
        assert_eq!(
            run.mutants[0].report.status,
            kink_campaign::MutantStatus::Killed
        );
        assert_eq!(run.mutants[0].report.killing_test_ids, ["clash"]);
    });
}

#[test]
fn campaign_runs_in_the_build_solver_profile() {
    with_stack(|| {
        let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
        let compiled = validator.compile_baseline().expect("baseline compiles");
        let parsed =
            parse_definition(&compiled.artifacts().definition_kore).expect("definition parses");
        let mut backend =
            Backend::from_definition(parsed, "SYMMEM", BackendOptions::default()).expect("backend");
        assert_eq!(SolverProfile::of(&backend), SolverProfile::BUILD);
        let other = if SolverProfile::BUILD == SolverProfile::NoZ3 {
            SolverProfile::Z3
        } else {
            SolverProfile::NoZ3
        };
        let adapter = ExecutionAdapter::with_profile(other);
        let z = app("z", vec![]);
        let initial_state = state(app("addr", vec![z.clone()]), app("addr", vec![z]));
        assert_eq!(
            adapter.execute(&mut backend, &initial_state, BUDGET),
            Err(ExecutionAdapterFailure::SolverProfileMismatch)
        );
    });
}

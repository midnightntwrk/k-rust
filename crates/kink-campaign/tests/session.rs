//! `BaselineSession` and `run_campaign_multi_with` (flow F-12, README 6.3): a per-command,
//! in-memory memo of live baseline runs.
//!
//! The session must change nothing but the number of live baseline runs: every call through it
//! returns the `CampaignRun` (or the `CampaignFailure`) a fresh call returns; a campaign over
//! another validator is refused before anything runs; observation, pattern-oracle and symbolic
//! campaigns, and a campaign with another classifier, run live and leave the session untouched;
//! a refused (time-limited) baseline is reused as refused; any change of a key component misses.

#[path = "../../../testdata/k/support.rs"]
mod support;

#[path = "../../../testdata/k/step_support.rs"]
mod step_support;

use std::time::Duration;

use k_rust::definition::AttributeKey;
use k_rust::kast::{Sort as KastSort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
use k_rust::kore::ast::Pattern;
use kink_campaign::{
    BaselineSession, Campaign, CampaignFailure, CampaignFailureKind, CampaignOptions, CampaignRun,
    CrashPolicy, OracleDeclaration, Projection, ScheduleMode, SelectionPolicy as Selection,
    StateProjection, TestCase, run_campaign_multi, run_campaign_multi_with,
};
use kink_native::NativeValidator;
use kink_native::execution::ExecutionBudget;
use kink_native::step_events::{StepEventSpec, StepObservation};
use kink_patch::{
    Baseline, CandidateGeneration, Discovery, Edit, Patch, SelectionPolicy, SiteSelector, TermRef,
    derive_sites, select,
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

fn z() -> Pattern {
    app("Lblz", vec![])
}

fn s(nat: Pattern) -> Pattern {
    app("Lbls", vec![nat])
}

fn counter_state(steps: usize) -> Pattern {
    let mut left = z();
    for _ in 0..steps {
        left = s(left);
    }
    support::initial_state(app("Lblcounter", vec![z(), left]), "SortCounter")
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

fn state(projection: StateProjection) -> OracleDeclaration {
    OracleDeclaration::new(CrashPolicy::Reject, Projection::State(projection)).expect("declaration")
}

/// kink-flow's two fixed oracles: the exit stop without an exit-code cell, then the whole term.
fn flow_oracles() -> Vec<OracleDeclaration> {
    vec![
        state(StateProjection::ExitStop {
            exit_code_cell: None,
        }),
        state(StateProjection::WholeTerm),
    ]
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

fn stuck(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Stuck
}

fn test(id: &str, initial_state: Pattern) -> TestCase {
    TestCase {
        id: id.to_owned(),
        initial_state,
        oracles: flow_oracles(),
    }
}

/// The two concrete tests: `t1` ends after three increments, `t2` takes `branch`.
fn tests() -> Vec<TestCase> {
    vec![test("t1", counter_state(3)), test("t2", choose_state())]
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

fn options(schedule: ScheduleMode, share_evidence: bool) -> CampaignOptions {
    CampaignOptions {
        schedule,
        selection: Selection::None,
        share_evidence,
    }
}

/// A classifier as a campaign holds it. The session binds one such reference: a campaign
/// memoises only with the very same reference (the same function through another reference may
/// have another vtable copy, which only misses).
type Classify = dyn Fn(&Pattern) -> ExecutionTerminalKind;

/// A campaign's inputs other than the validator, so one test can vary each of them.
struct Inputs<'a> {
    module: &'a str,
    observation: &'a [StepEventSpec],
    classify: &'a Classify,
    tests: &'a [TestCase],
    budget: ExecutionBudget,
}

impl<'a> Inputs<'a> {
    fn new(tests: &'a [TestCase], classify: &'a Classify) -> Self {
        Self {
            module: "COUNTER",
            observation: &[],
            classify,
            tests,
            budget: BUDGET,
        }
    }

    fn campaign(&self, validator: &'a NativeValidator) -> Campaign<'a> {
        Campaign {
            validator,
            module: self.module,
            observation: self.observation,
            classify: self.classify,
            tests: self.tests,
            budget: self.budget,
        }
    }
}

/// A fresh call (`run_campaign_multi`) and a call through `session`.
fn both(
    validator: &NativeValidator,
    inputs: &Inputs<'_>,
    options: &CampaignOptions,
    session: &mut BaselineSession<'_>,
) -> (
    Result<CampaignRun, CampaignFailure>,
    Result<CampaignRun, CampaignFailure>,
) {
    let generation = generation(validator.baseline());
    let campaign = inputs.campaign(validator);
    let fresh = run_campaign_multi(&campaign, std::slice::from_ref(&generation), options);
    let shared = run_campaign_multi_with(
        &campaign,
        std::slice::from_ref(&generation),
        options,
        session,
    );
    (fresh, shared)
}

fn counts(session: &BaselineSession<'_>) -> (usize, usize, usize) {
    (
        session.live_runs(),
        session.reused_runs(),
        session.stored_runs(),
    )
}

fn validator() -> NativeValidator {
    NativeValidator::bind(support::load("counter.k"), CompileOptions::default())
}

/// Two calls through one session give the runs two fresh calls give (stop rule 2: a hit's
/// evidence equals a live run of the same test in a fresh call), the second with no live
/// baseline run; so do a reordered call and a call over a subset. In both schedules, with and
/// without evidence sharing.
#[test]
fn calls_through_one_session_equal_fresh_calls_and_reuse_each_baseline() {
    with_stack(|| {
        let classify: &Classify = &normal;
        let validator = validator();
        let tests = tests();
        let reversed = tests.iter().rev().cloned().collect::<Vec<_>>();
        let subset = vec![tests[1].clone()];
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            for share in [false, true] {
                let options = options(schedule, share);
                let mut session = BaselineSession::new(&validator, classify);
                assert_eq!(counts(&session), (0, 0, 0));
                let (fresh, first) = both(
                    &validator,
                    &Inputs::new(&tests, classify),
                    &options,
                    &mut session,
                );
                let fresh = fresh.expect("fresh call");
                assert_eq!(first.expect("first call"), fresh, "{schedule:?} {share}");
                assert_eq!(counts(&session), (2, 0, 2), "first call runs both live");
                let (fresh_again, second) = both(
                    &validator,
                    &Inputs::new(&tests, classify),
                    &options,
                    &mut session,
                );
                assert_eq!(fresh_again.expect("fresh call"), fresh);
                assert_eq!(second.expect("second call"), fresh, "{schedule:?} {share}");
                assert_eq!(counts(&session), (2, 2, 2), "second call reuses both");
                let (fresh, third) = both(
                    &validator,
                    &Inputs::new(&reversed, classify),
                    &options,
                    &mut session,
                );
                assert_eq!(third.expect("reversed"), fresh.expect("fresh reversed"));
                assert_eq!(counts(&session), (2, 4, 2));
                let (fresh, fourth) = both(
                    &validator,
                    &Inputs::new(&subset, classify),
                    &options,
                    &mut session,
                );
                assert_eq!(fourth.expect("subset"), fresh.expect("fresh subset"));
                assert_eq!(counts(&session), (2, 5, 2));
            }
        }
    });
}

/// A session belongs to one validator: a campaign over another one, even an equal clone, is
/// refused before anything runs, and the session stays empty.
#[test]
fn a_campaign_over_another_validator_is_refused() {
    with_stack(|| {
        let classify: &Classify = &normal;
        let validator = validator();
        let clone = validator.clone();
        let other =
            NativeValidator::bind(support::load("counter_bytwo.k"), CompileOptions::default());
        let tests = tests();
        let generation = generation(validator.baseline());
        let mut session = BaselineSession::new(&validator, classify);
        // The session records its validator's compiled baseline and compile options.
        let compiled = validator.compile_baseline().expect("baseline");
        assert_eq!(
            session.compiled_baseline(),
            Some((compiled.kore_sha256(), compiled.compile_options()))
        );
        let inputs = Inputs::new(&tests, classify);
        for foreign in [&clone, &other] {
            let foreign_generation = generation_of(foreign);
            let failure = run_campaign_multi_with(
                &inputs.campaign(foreign),
                std::slice::from_ref(&foreign_generation),
                &options(ScheduleMode::FirstKill, false),
                &mut session,
            )
            .expect_err("another validator is refused");
            assert_eq!(failure.kind(), CampaignFailureKind::InvalidDeclaration);
            assert_eq!(counts(&session), (0, 0, 0));
        }
        // The session's own validator still runs.
        run_campaign_multi_with(
            &inputs.campaign(&validator),
            std::slice::from_ref(&generation),
            &options(ScheduleMode::FirstKill, false),
            &mut session,
        )
        .expect("own validator");
        assert_eq!(counts(&session), (2, 0, 2));
    });
}

/// The generation of `validator`'s own baseline: counter_bytwo has no `branch` rule, so it gets
/// the empty generation.
fn generation_of(validator: &NativeValidator) -> CandidateGeneration<'_> {
    let baseline = validator.baseline();
    if baseline
        .authored_sentences()
        .any(|(_, sentence)| sentence.attributes().string(AttributeKey::Label) == Some("branch"))
    {
        return generation(baseline);
    }
    select(
        &Discovery::empty(baseline, false, false),
        SelectionPolicy::Each,
        1,
    )
    .expect("selection")
    .fold("none", |_| -> Patch { unreachable!("no site") })
    .expect("fold")
}

/// The session memoises only kink-flow's setting: no observation, no pattern oracle, concrete
/// tests and the session's own classifier. Any other campaign runs live (it equals the fresh
/// call) and leaves the session untouched.
#[test]
fn observation_pattern_symbolic_and_foreign_classifier_campaigns_are_not_memoised() {
    with_stack(|| {
        let classify: &Classify = &normal;
        let validator = validator();
        let specs = step_support::counter(true);
        let vocabulary = StepObservation::vocabulary_of(&specs).expect("vocabulary");
        let plain = tests();
        let mut patterned = tests();
        patterned[0].oracles.push(occurs(&vocabulary, "increment"));
        let mut symbolic = tests();
        symbolic[0].initial_state = support::initial_state(
            app("Lblcounter", vec![support::var("N", "SortNat"), z()]),
            "SortCounter",
        );
        let observed = Inputs {
            observation: &specs,
            ..Inputs::new(&plain, classify)
        };
        let observed_with_pattern = Inputs {
            observation: &specs,
            ..Inputs::new(&patterned, classify)
        };
        let pattern_only = Inputs::new(&patterned, classify);
        let symbolic = Inputs::new(&symbolic, classify);
        let foreign_classifier = Inputs {
            classify: &stuck,
            ..Inputs::new(&plain, classify)
        };
        let cases: [(&str, &Inputs<'_>); 5] = [
            ("observation", &observed),
            ("observation and pattern oracle", &observed_with_pattern),
            ("pattern oracle", &pattern_only),
            ("symbolic test", &symbolic),
            ("another classifier", &foreign_classifier),
        ];
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let options = options(schedule, false);
            let mut session = BaselineSession::new(&validator, classify);
            for (name, inputs) in cases {
                for _ in 0..2 {
                    let (fresh, shared) = both(&validator, inputs, &options, &mut session);
                    assert_eq!(shared, fresh, "{name} {schedule:?}");
                    assert_eq!(counts(&session), (0, 0, 0), "{name} is not memoised");
                }
            }
        }
    });
}

/// A baseline stopped by its time budget is stored like any other run and reused as refused:
/// the second call through the session fails as the fresh call does, with no live run.
#[test]
fn a_time_limited_baseline_is_reused_as_refused() {
    with_stack(|| {
        let classify: &Classify = &normal;
        let validator = validator();
        let tests = tests();
        let expired = Inputs {
            budget: ExecutionBudget {
                time: Duration::ZERO,
                ..BUDGET
            },
            ..Inputs::new(&tests, classify)
        };
        let options = options(ScheduleMode::FirstKill, false);
        let mut session = BaselineSession::new(&validator, classify);
        let (fresh, first) = both(&validator, &expired, &options, &mut session);
        let fresh = fresh.expect_err("an expired budget refuses the baseline");
        assert_eq!(first.expect_err("refused through the session"), fresh);
        assert_eq!(counts(&session), (2, 0, 2));
        let (_, second) = both(&validator, &expired, &options, &mut session);
        assert_eq!(second.expect_err("reused as refused"), fresh);
        assert_eq!(counts(&session), (2, 2, 2));
        // The same tests under the full budget are other keys: they run live and are admitted.
        let (fresh, admitted) = both(
            &validator,
            &Inputs::new(&tests, classify),
            &options,
            &mut session,
        );
        assert_eq!(admitted.expect("admitted"), fresh.expect("fresh"));
        assert_eq!(counts(&session), (4, 2, 4));
    });
}

/// Every key component is an input of the baseline run: changing the budget, the oracle
/// declarations, the initial state under the same test id or the test id misses, runs live,
/// and gives the fresh call's run. (counter.k has one executable module; the module component
/// is pinned by the runner's unit test `a_session_key_holds_the_module`.)
#[test]
fn a_changed_key_component_misses() {
    with_stack(|| {
        let classify: &Classify = &normal;
        let validator = validator();
        let tests = tests();
        let options = options(ScheduleMode::FirstKill, false);
        let mut session = BaselineSession::new(&validator, classify);
        let (_, first) = both(
            &validator,
            &Inputs::new(&tests, classify),
            &options,
            &mut session,
        );
        first.expect("first call");
        assert_eq!(counts(&session), (2, 0, 2));

        let depth = Inputs {
            budget: ExecutionBudget {
                max_depth: Some(100),
                ..BUDGET
            },
            ..Inputs::new(&tests, classify)
        };
        let mut exit_only = tests.clone();
        for test in &mut exit_only {
            test.oracles.truncate(1);
        }
        let mut other_state = tests.clone();
        other_state[0].initial_state = counter_state(1);
        let mut renamed = tests.clone();
        renamed[1].id = "t2-renamed".into();
        let cases: [(&str, Inputs<'_>, usize); 4] = [
            ("budget", depth, 2),
            ("oracles", Inputs::new(&exit_only, classify), 2),
            ("initial state", Inputs::new(&other_state, classify), 1),
            ("test id", Inputs::new(&renamed, classify), 1),
        ];
        for (name, inputs, misses) in cases {
            let (live, reused, stored) = counts(&session);
            let (fresh, shared) = both(&validator, &inputs, &options, &mut session);
            assert_eq!(shared, fresh, "{name}");
            assert_eq!(
                counts(&session),
                (live + misses, reused + 2 - misses, stored + misses),
                "{name}"
            );
            // The same inputs again: every baseline is now a hit.
            let (fresh, shared) = both(&validator, &inputs, &options, &mut session);
            assert_eq!(shared, fresh, "{name} again");
            assert_eq!(
                counts(&session),
                (live + misses, reused + 4 - misses, stored + misses),
                "{name} again"
            );
        }
    });
}

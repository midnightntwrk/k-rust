//! End-to-end symmem and guardedmem campaigns for exact-site and coupled operators.

#[path = "../../../testdata/k/support.rs"]
mod support;

#[path = "../../../testdata/k/step_support.rs"]
mod step_support;

use std::time::Duration;

use k_rust::definition::AttributeKey;
use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::kore_sort;
use k_rust::kore::ast::Pattern;
use kink_campaign::{
    Campaign, CampaignFailureKind, CrashPolicy, FinalResult, MutantStatus, OracleDeclaration,
    OracleOutcome, OracleSide, OracleValue, PatternValue, Projection, Rational, ScheduleMode,
    SideRun, StateProjection, TestCase, TestRun, derive_mutant_report, run_campaign, tally,
};
use kink_native::NativeValidator;
use kink_native::execution::ExecutionBudget;
use kink_native::feasibility::TestInitialState;
use kink_native::step_events::{StepEventSpec, StepObservation};
use kink_patch::{
    Baseline, CandidateDisposition, CandidateGeneration, Edit, InsertPosition, Patch,
    SelectionPolicy, SiteSelector, TermRef, derive_sites, select,
};
use kink_pattern::{
    Atom, EventVocabulary, ExecutionTerminalKind, MatchMode, PatternArm, PatternPlan,
    PayloadClause, Relation,
};

use OracleOutcome::{Agree as A, Distinguish as D, Unknown as U};

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

fn app(symbol: &str, args: Vec<Pattern>) -> Pattern {
    support::app(&format!("Lbl{symbol}"), args)
}

fn nat(name: &str) -> Pattern {
    support::var(name, "SortNat")
}

fn z() -> Pattern {
    app("z", vec![])
}

fn addr(n: Pattern) -> Pattern {
    app("addr", vec![n])
}

fn state(
    write_address: Pattern,
    write_value: Pattern,
    load_address: Pattern,
    load_value: Pattern,
) -> Pattern {
    support::initial_state(
        app(
            "seq",
            vec![
                app("write", vec![write_address, write_value]),
                app(
                    "seq",
                    vec![
                        app("load", vec![load_address, load_value]),
                        app("halt", vec![]),
                    ],
                ),
            ],
        ),
        "SortProg",
    )
}

fn pattern(
    vocabulary: &EventVocabulary,
    first: &str,
    second: &str,
    relation: Relation,
) -> OracleDeclaration {
    pattern_with_sort(vocabulary, first, second, relation, "SortAddress")
}

fn pattern_with_sort(
    vocabulary: &EventVocabulary,
    first: &str,
    second: &str,
    relation: Relation,
    sort: &str,
) -> OracleDeclaration {
    let plan = PatternPlan::new(
        vocabulary,
        vec![("A".into(), kore_sort(sort))],
        vec![PatternArm {
            atoms: vec![first, second]
                .into_iter()
                .map(|constructor| Atom {
                    constructor: constructor.into(),
                    payload: vec![PayloadClause {
                        position: 0,
                        mode: if constructor == first {
                            MatchMode::Bind
                        } else {
                            MatchMode::Use
                        },
                        variable: "A".into(),
                    }],
                })
                .collect(),
            relations: vec![relation],
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

fn tests(vocabulary: &EventVocabulary) -> Vec<TestCase> {
    let oracles = vec![
        OracleDeclaration::new(
            CrashPolicy::CompareIdentity,
            Projection::State(StateProjection::WholeTerm),
        )
        .expect("final"),
        pattern(vocabulary, "memoryWrite", "memoryLoad", Relation::NextEvent),
        pattern(
            vocabulary,
            "memoryWrite",
            "memoryLoad",
            Relation::EventuallyAfter,
        ),
        pattern(vocabulary, "memoryLoad", "memoryFree", Relation::NextEvent),
    ];
    let ground = state(
        addr(z()),
        app("s", vec![z()]),
        addr(z()),
        app("s", vec![z()]),
    );
    let shared = state(addr(nat("X")), nat("V"), addr(nat("X")), nat("W"));
    let distinct = state(addr(nat("X")), nat("V"), addr(nat("Y")), nat("W"));
    let clash = state(
        addr(z()),
        nat("V"),
        addr(app("s", vec![nat("Y")])),
        nat("W"),
    );
    [
        ("ground-shared", ground),
        ("sym-shared", shared),
        ("sym-distinct", distinct),
        ("sym-clash", clash),
    ]
    .into_iter()
    .map(|(id, program)| TestCase {
        id: id.into(),
        initial_state: program,
        oracles: oracles.clone(),
    })
    .collect()
}

struct Symmem {
    validator: NativeValidator,
    vocabulary: EventVocabulary,
    observation: Vec<StepEventSpec>,
    tests: Vec<TestCase>,
}

impl Symmem {
    fn new() -> Self {
        let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
        let observation = step_support::symmem(true);
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        let tests = tests(&vocabulary);
        Self {
            validator,
            vocabulary,
            observation,
            tests,
        }
    }

    fn campaign<'a>(&'a self, tests: &'a [TestCase]) -> Campaign<'a> {
        Campaign {
            validator: &self.validator,
            module: "SYMMEM",
            observation: &self.observation,
            classify: &normal,
            tests,
            budget: BUDGET,
        }
    }
}

struct Guarded {
    validator: NativeValidator,
    vocabulary: EventVocabulary,
    observation: Vec<StepEventSpec>,
    tests: Vec<TestCase>,
}

impl Guarded {
    fn new() -> Self {
        let validator =
            NativeValidator::bind(support::load("guardedmem.k"), CompileOptions::default());
        let observation = step_support::guardedmem(true);
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        let oracles = vec![
            OracleDeclaration::new(
                CrashPolicy::CompareIdentity,
                Projection::State(StateProjection::WholeTerm),
            )
            .expect("final"),
            pattern_with_sort(
                &vocabulary,
                "memoryWrite",
                "memoryLoad",
                Relation::EventuallyAfter,
                "SortInt",
            ),
        ];
        let guarded_state = |write_address: Pattern, load_address: Pattern| {
            state(
                addr(write_address),
                support::var("V", "SortInt"),
                addr(load_address),
                support::var("W", "SortInt"),
            )
        };
        let tests = [
            (
                "sym-guarded",
                guarded_state(support::var("X", "SortInt"), support::var("Y", "SortInt")),
            ),
            (
                "ground-guarded",
                guarded_state(support::int(1), support::int(1)),
            ),
        ]
        .into_iter()
        .map(|(id, initial_state)| TestCase {
            id: id.into(),
            initial_state,
            oracles: oracles.clone(),
        })
        .collect();
        Self {
            validator,
            vocabulary,
            observation,
            tests,
        }
    }

    fn campaign<'a>(&'a self, tests: &'a [TestCase]) -> Campaign<'a> {
        Campaign {
            validator: &self.validator,
            module: "GUARDEDMEM",
            observation: &self.observation,
            classify: &normal,
            tests,
            budget: BUDGET,
        }
    }
}

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

fn term(baseline: &Baseline, rule: &str, path: &[u32]) -> Term {
    baseline
        .term(&TermRef::new(support::rule(baseline, rule), path))
        .expect("term")
        .clone()
}

fn exact(count: usize, arity: usize) -> SelectionPolicy {
    SelectionPolicy::Exact {
        expected_tuple_count: count,
        expected_tuple_arity: arity,
    }
}

fn release_after_write(baseline: &Baseline) -> CandidateGeneration<'_> {
    let discovery = derive_sites(
        baseline,
        "write-continuation",
        &[
            SiteSelector::RuleLabel("SYMMEM.write".into()),
            SiteSelector::Path(vec![0, 1]),
        ],
    )
    .expect("site");
    assert!(discovery.exhaustive());
    let generation = select(&discovery, exact(1, 1), 1)
        .expect("selection")
        .fold("release-after-write", |origin| {
            let at = origin.discovery_tuples[0].sites[0].at.clone();
            let address = term(baseline, "SYMMEM.write", &[0, 0, 0, 0]);
            let continuation = baseline.term(&at).expect("continuation").clone();
            Patch::new(vec![Edit::ReplaceTerm {
                at,
                expected: continuation.clone(),
                replacement: Term::apply(
                    "seq",
                    vec![Term::apply("free", vec![address]), continuation],
                ),
            }])
            .expect("patch")
        })
        .expect("generation");
    assert!(generation.scored());
    assert_eq!(generation.candidates().len(), 1);
    generation
}

fn coupled(baseline: &Baseline, value: bool) -> CandidateGeneration<'_> {
    coupled_with_stale_load(baseline, value, false)
}

fn coupled_with_stale_load(
    baseline: &Baseline,
    value: bool,
    stale_load: bool,
) -> CandidateGeneration<'_> {
    let path = if value {
        vec![0, 0, 0, 1]
    } else {
        vec![0, 0, 0, 0]
    };
    let binding = if value { "V" } else { "A" };
    let sort = if value { "Nat" } else { "Address" };
    let derive = |role: &str, rule: &str| {
        derive_sites(
            baseline,
            role,
            &[
                SiteSelector::RuleLabel(rule.into()),
                SiteSelector::Path(path.clone()),
                SiteSelector::Sort(Sort::new(sort)),
                SiteSelector::Bind(binding.into()),
            ],
        )
        .expect("site")
    };
    let discovery = derive("write", "SYMMEM.write")
        .join(&derive("load", "SYMMEM.load"), false)
        .expect("join");
    assert!(discovery.exhaustive());
    let operator = if value {
        "coupled-value-representation"
    } else {
        "release-after-access"
    };
    let generation = select(&discovery, exact(1, 2), 1)
        .expect("selection")
        .fold(operator, |origin| {
            let tuple = &origin.discovery_tuples[0];
            let bound = tuple.bindings.get(binding).expect("binding").clone();
            Patch::new(
                tuple
                    .sites
                    .iter()
                    .map(|site| {
                        let at = if value {
                            site.at.clone()
                        } else {
                            TermRef::new(site.at.sentence.clone(), [0, 1])
                        };
                        let expected = if stale_load
                            && at.sentence == support::rule(baseline, "SYMMEM.load")
                        {
                            Term::apply("halt", vec![])
                        } else {
                            baseline.term(&at).expect("term").clone()
                        };
                        let replacement = if value {
                            Term::apply("s", vec![bound.clone()])
                        } else {
                            Term::apply(
                                "seq",
                                vec![Term::apply("free", vec![bound.clone()]), expected.clone()],
                            )
                        };
                        Edit::ReplaceTerm {
                            at,
                            expected,
                            replacement,
                        }
                    })
                    .collect(),
            )
            .expect("patch")
        })
        .expect("generation");
    if !stale_load {
        assert!(generation.scored());
        assert_eq!(generation.candidates().len(), 1);
    }
    generation
}

fn inverted_load_sign(baseline: &Baseline) -> CandidateGeneration<'_> {
    let derive = |role: &str, rule: &str| {
        derive_sites(
            baseline,
            role,
            &[
                SiteSelector::RuleLabel(rule.into()),
                SiteSelector::Path(vec![0, 0, 0, 0, 0]),
                SiteSelector::Sort(Sort::new("Int")),
                SiteSelector::Bind("A".into()),
            ],
        )
        .expect("site")
    };
    let discovery = derive("load", "GUARDEDMEM.load")
        .join(&derive("load-fault", "GUARDEDMEM.loadFault"), false)
        .expect("join");
    assert!(discovery.exhaustive());
    let generation = select(&discovery, exact(1, 2), 1)
        .expect("selection")
        .fold("inverted-load-sign", |origin| {
            Patch::new(
                origin.discovery_tuples[0]
                    .sites
                    .iter()
                    .map(|site| {
                        let other =
                            if site.at.sentence == support::rule(baseline, "GUARDEDMEM.load") {
                                "GUARDEDMEM.loadFault"
                            } else {
                                "GUARDEDMEM.load"
                            };
                        let at = TermRef::new(site.at.sentence.clone(), [1]);
                        Edit::ReplaceTerm {
                            expected: baseline.term(&at).expect("requires").clone(),
                            replacement: term(baseline, other, &[1]),
                            at,
                        }
                    })
                    .collect(),
            )
            .expect("patch")
        })
        .expect("generation");
    assert!(generation.scored());
    assert_eq!(generation.candidates().len(), 1);
    generation
}

fn outcomes(run: &kink_campaign::CampaignRun) -> Vec<Vec<OracleOutcome>> {
    let [mutant] = run.mutants.as_slice() else {
        panic!("one mutant")
    };
    mutant
        .plan
        .tests
        .iter()
        .map(|test| match &test.run {
            TestRun::Compared(row) => row.clone(),
            other => panic!("{}: {other:?}", test.test_id),
        })
        .collect()
}

fn assert_baseline(run: &kink_campaign::CampaignRun) {
    let halt = support::initial_state(app("halt", vec![]), "SortProg");
    let expected_patterns = [
        [true, true, false],
        [true, true, false],
        [true, true, false],
        [false, false, false],
    ];
    assert_eq!(run.baseline.len(), expected_patterns.len());
    for (evidence, row) in run.baseline.iter().zip(expected_patterns) {
        let SideRun::Sides { sides } = &evidence.run else {
            panic!("baseline failed: {evidence:?}")
        };
        assert_eq!(sides.len(), 4);
        assert_eq!(
            sides[0],
            OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(
                [halt.clone()].into()
            ))),
            "{} final",
            evidence.test_id
        );
        for (slot, matched) in sides[1..].iter().zip(row) {
            let expected = if matched {
                PatternValue::Match { bindings: None }
            } else {
                PatternValue::NoMatch
            };
            assert_eq!(
                *slot,
                OracleSide::Normal(OracleValue::Pattern(expected)),
                "{} pattern",
                evidence.test_id
            );
        }
    }
}

#[test]
fn single_site_release_is_killed_by_its_trace() {
    with_stack(|| {
        for whole in [true, false] {
            let mut fixture = Symmem::new();
            fixture.observation = step_support::symmem(whole);
            let generation = release_after_write(fixture.validator.baseline());
            let run = run_campaign(
                &fixture.campaign(&fixture.tests),
                &generation,
                ScheduleMode::Full,
            )
            .expect("campaign");
            assert_baseline(&run);
            assert_eq!(
                outcomes(&run),
                vec![
                    if whole {
                        vec![A, D, D, A]
                    } else {
                        vec![A, D, A, A]
                    },
                    if whole {
                        vec![A, D, D, A]
                    } else {
                        vec![A, D, A, A]
                    },
                    if whole {
                        vec![A, D, D, A]
                    } else {
                        vec![A, D, A, A]
                    },
                    vec![A, A, A, A]
                ]
            );
            let mutant = &run.mutants[0];
            assert_eq!(mutant.report.status, MutantStatus::Killed);
            assert_eq!(
                mutant.report.killing_test_ids,
                ["ground-shared", "sym-shared", "sym-distinct"]
            );
            assert_eq!(mutant.operator, "release-after-write");
            assert_eq!(
                mutant.written_sentences,
                [support::rule(fixture.validator.baseline(), "SYMMEM.write")]
            );
        }
    });
}

#[test]
fn coupled_release_is_one_mutant_killed_by_its_trace() {
    with_stack(|| {
        for whole in [true, false] {
            let mut fixture = Symmem::new();
            fixture.observation = step_support::symmem(whole);
            let baseline = fixture.validator.baseline();
            let generation = coupled(baseline, false);
            assert_eq!(generation.candidates()[0].patch.edits().len(), 2);
            let run = run_campaign(
                &fixture.campaign(&fixture.tests),
                &generation,
                ScheduleMode::Full,
            )
            .expect("campaign");
            assert_baseline(&run);
            assert_eq!(run.mutants.len(), 1);
            assert_eq!(
                outcomes(&run),
                vec![
                    if whole {
                        vec![A, D, D, A]
                    } else {
                        vec![A, D, A, D]
                    },
                    if whole {
                        vec![A, D, D, A]
                    } else {
                        vec![A, D, A, D]
                    },
                    if whole {
                        vec![A, D, D, A]
                    } else {
                        vec![A, D, A, D]
                    },
                    if whole {
                        vec![A, A, A, A]
                    } else {
                        vec![A, A, A, D]
                    }
                ]
            );
            let mutant = &run.mutants[0];
            assert_eq!(mutant.report.status, MutantStatus::Killed);
            assert_eq!(
                mutant.report.killing_test_ids,
                if whole {
                    vec!["ground-shared", "sym-shared", "sym-distinct"]
                } else {
                    vec!["ground-shared", "sym-shared", "sym-distinct", "sym-clash"]
                }
            );
            assert_eq!(mutant.operator, "release-after-access");
            assert_eq!(
                mutant.written_sentences,
                [
                    support::rule(baseline, "SYMMEM.write"),
                    support::rule(baseline, "SYMMEM.load")
                ]
            );
            let score = run.score.expect("scored");
            assert_eq!(
                (score.killed, score.survived, score.ratio),
                (
                    1,
                    0,
                    Some(Rational {
                        numerator: 1,
                        denominator: 1
                    })
                )
            );
            let count = tally(&generation, &run).expect("tally");
            assert_eq!((count.killed, count.rejected_origins), (1, 0));
            assert!(outcomes(&run).iter().all(|row| row[0] == A));
        }
    });
}

#[test]
fn coherent_value_representation_is_not_killed() {
    with_stack(|| {
        let fixture = Symmem::new();
        let generation = coupled(fixture.validator.baseline(), true);
        let run = run_campaign(
            &fixture.campaign(&fixture.tests),
            &generation,
            ScheduleMode::Full,
        )
        .expect("campaign");
        assert_baseline(&run);
        assert_eq!(
            outcomes(&run),
            vec![
                vec![A, A, A, A],
                vec![U, U, U, U],
                vec![U, U, U, U],
                vec![U, U, U, U]
            ]
        );
        assert_eq!(run.mutants[0].report.status, MutantStatus::Unknown);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());
        assert_eq!(run.mutants[0].operator, "coupled-value-representation");
        let ground = &fixture.tests[..1];
        let ground_run = run_campaign(&fixture.campaign(ground), &generation, ScheduleMode::Full)
            .expect("ground campaign");
        assert_eq!(outcomes(&ground_run), vec![vec![A, A, A, A]]);
        assert_eq!(ground_run.mutants[0].report.status, MutantStatus::Survived);
        assert!(ground_run.mutants[0].report.killing_test_ids.is_empty());
    });
}

#[test]
fn stale_coupled_edit_publishes_no_mutant() {
    with_stack(|| {
        let fixture = Symmem::new();
        let generation = coupled_with_stale_load(fixture.validator.baseline(), false, true);
        assert!(matches!(
            generation.dispositions(),
            [CandidateDisposition::Rejected(_)]
        ));
        assert!(generation.candidates().is_empty());
        assert!(!generation.scored());

        let run = run_campaign(
            &fixture.campaign(&fixture.tests),
            &generation,
            ScheduleMode::Full,
        )
        .expect("baseline campaign");
        assert!(run.mutants.is_empty());
        assert_eq!(run.score, None);
        assert_eq!(tally(&generation, &run).expect("tally").rejected_origins, 1);
    });
}

#[test]
fn bounded_mutant_evidence_kills_only_by_a_match() {
    with_stack(|| {
        for whole in [true, false] {
            let mut fixture = Symmem::new();
            fixture.observation = step_support::symmem(whole);
            let baseline = fixture.validator.baseline();
            let coupled_generation = coupled(baseline, false);
            let single_generation = release_after_write(baseline);
            for (depth, generation, expected, status) in [
                (
                    3,
                    &coupled_generation,
                    if whole {
                        vec![U, U, U, U]
                    } else {
                        vec![U, U, A, U]
                    },
                    MutantStatus::Unknown,
                ),
                (
                    3,
                    &single_generation,
                    if whole {
                        vec![U, U, U, U]
                    } else {
                        vec![U, U, A, U]
                    },
                    MutantStatus::Unknown,
                ),
                (
                    4,
                    &coupled_generation,
                    if whole {
                        vec![U, U, U, U]
                    } else {
                        vec![U, U, A, D]
                    },
                    if whole {
                        MutantStatus::Unknown
                    } else {
                        MutantStatus::Killed
                    },
                ),
                (
                    4,
                    &single_generation,
                    if whole {
                        vec![A, D, D, A]
                    } else {
                        vec![A, D, A, A]
                    },
                    MutantStatus::Killed,
                ),
            ] {
                let mut campaign = fixture.campaign(&fixture.tests[..1]);
                campaign.budget.max_depth = Some(depth);
                let full = run_campaign(&campaign, generation, ScheduleMode::Full)
                    .expect("bounded baseline admitted");
                let stopped = run_campaign(&campaign, generation, ScheduleMode::FirstKill)
                    .expect("bounded FirstKill");
                assert_eq!(
                    outcomes(&full),
                    vec![expected],
                    "depth {depth}, whole={whole}"
                );
                assert_eq!(full.mutants[0].report.status, status);
                assert_eq!(stopped, full);
                assert_eq!(
                    full.mutants[0].report.killing_test_ids,
                    if status == MutantStatus::Killed {
                        vec!["ground-shared"]
                    } else {
                        vec![]
                    }
                );
            }
        }
    });
}

#[test]
fn first_kill_stops_the_coupled_mutant_after_its_first_kill() {
    with_stack(|| {
        let fixture = Symmem::new();
        let generation = coupled(fixture.validator.baseline(), false);
        let campaign = fixture.campaign(&fixture.tests);
        let full = run_campaign(&campaign, &generation, ScheduleMode::Full).expect("full");
        let stopped =
            run_campaign(&campaign, &generation, ScheduleMode::FirstKill).expect("first kill");
        let mutant = &stopped.mutants[0];
        assert_eq!(mutant.plan.tests[0], full.mutants[0].plan.tests[0]);
        assert!(
            mutant.plan.tests[1..]
                .iter()
                .all(|test| test.run == TestRun::SkippedAfterKill)
        );
        assert_eq!(mutant.evidence, full.mutants[0].evidence[..1]);
        assert_eq!(mutant.report.executed_test_ids, ["ground-shared"]);
        assert_eq!(mutant.report.killing_test_ids, ["ground-shared"]);
        assert_eq!(
            mutant.report.skipped_test_ids,
            ["sym-shared", "sym-distinct", "sym-clash"]
        );
        assert_eq!(mutant.report.status, MutantStatus::Killed);
        let manifest = fixture
            .tests
            .iter()
            .map(|test| kink_campaign::ManifestTest {
                test_id: test.id.clone(),
                slot_count: test.oracles.len(),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            mutant.report,
            derive_mutant_report(&full.mutants[0].plan, &manifest, ScheduleMode::FirstKill)
                .expect("derived report")
        );
    });
}

#[test]
fn repeated_coupled_campaigns_are_identical() {
    with_stack(|| {
        let fixture = Symmem::new();
        let generation = coupled(fixture.validator.baseline(), false);
        let campaign = fixture.campaign(&fixture.tests);
        let first = run_campaign(&campaign, &generation, ScheduleMode::Full).expect("first");
        let second = run_campaign(&campaign, &generation, ScheduleMode::Full).expect("second");
        assert_eq!(first, second);

        let fresh_fixture = Symmem::new();
        let fresh_generation = coupled(fresh_fixture.validator.baseline(), false);
        let fresh = run_campaign(
            &fresh_fixture.campaign(&fresh_fixture.tests),
            &fresh_generation,
            ScheduleMode::Full,
        )
        .expect("fresh");
        assert_eq!(
            first.mutants[0].report.status,
            fresh.mutants[0].report.status
        );
        assert_eq!(outcomes(&first), outcomes(&fresh));
        assert_eq!(first.baseline, fresh.baseline);
        assert_eq!(first.mutants[0].evidence, fresh.mutants[0].evidence);
    });
}

#[test]
fn inverted_load_sign_is_killed_by_a_solver_unsat() {
    with_stack(|| {
        let fixture = Guarded::new();
        let generation = inverted_load_sign(fixture.validator.baseline());
        assert_eq!(generation.candidates()[0].patch.edits().len(), 2);
        let campaign = fixture.campaign(&fixture.tests);
        let full = run_campaign(&campaign, &generation, ScheduleMode::Full);
        if cfg!(feature = "z3") {
            let full = full.expect("Z3 admits the symbolic baseline");
            let SideRun::Sides { sides } = &full.baseline[0].run else {
                panic!("symbolic baseline failed: {:?}", full.baseline[0]);
            };
            let terminal = |symbol| support::initial_state(app(symbol, vec![]), "SortProg");
            assert_eq!(
                sides,
                &vec![
                    OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(
                        [terminal("halt"), terminal("fault")].into()
                    ))),
                    OracleSide::Normal(OracleValue::Pattern(PatternValue::Match {
                        bindings: None
                    })),
                ]
            );
            assert_eq!(outcomes(&full), vec![vec![A, D], vec![D, D]]);
            assert_eq!(full.mutants[0].report.status, MutantStatus::Killed);
            assert_eq!(
                full.mutants[0].report.killing_test_ids,
                ["sym-guarded", "ground-guarded"]
            );

            let stopped =
                run_campaign(&campaign, &generation, ScheduleMode::FirstKill).expect("first kill");
            let mutant = &stopped.mutants[0];
            assert_eq!(mutant.report.status, MutantStatus::Killed);
            assert_eq!(mutant.report.executed_test_ids, ["sym-guarded"]);
            assert_eq!(mutant.report.killing_test_ids, ["sym-guarded"]);
            assert_eq!(mutant.plan.tests[1].run, TestRun::SkippedAfterKill);
        } else {
            assert_eq!(
                full.expect_err("symbolic baseline remains undecided")
                    .kind(),
                CampaignFailureKind::BaselineOracleFailed
            );
            let ground = run_campaign(
                &fixture.campaign(&fixture.tests[1..]),
                &generation,
                ScheduleMode::Full,
            )
            .expect("ground baseline admitted");
            assert_eq!(outcomes(&ground), vec![vec![D, D]]);
            assert_eq!(ground.mutants[0].report.status, MutantStatus::Killed);
            assert_eq!(
                ground.mutants[0].report.killing_test_ids,
                ["ground-guarded"]
            );
        }
    });
}

// ---------------------------------------------------------------- CPL-09 audit attacks
//
// README section 12, attacks A1-A6. Step declarations preserve the subjects of these
// historical audits: execution-identical mutations survive or fail closed, while declared
// execution differences can distinguish.

/// A one-candidate generation whose patch is `patch`, selected as one tuple of the exact
/// `sites` (rule label and path each; an unconstrained join when there are several), so that
/// the patch may write every listed rule.
fn fixed<'b>(
    baseline: &'b Baseline,
    sites: &[(&str, &[u32])],
    operator: &str,
    patch: &Patch,
) -> CandidateGeneration<'b> {
    let discovery = sites
        .iter()
        .map(|(rule, path)| {
            derive_sites(
                baseline,
                operator,
                &[
                    SiteSelector::RuleLabel((*rule).into()),
                    SiteSelector::Path(path.to_vec()),
                ],
            )
            .expect("site")
        })
        .reduce(|left, right| left.join(&right, false).expect("join"))
        .expect("at least one site");
    assert!(discovery.exhaustive());
    let generation = select(&discovery, exact(1, sites.len()), 1)
        .expect("selection")
        .fold(operator, |_| patch.clone())
        .expect("generation");
    assert!(generation.scored());
    assert_eq!(generation.candidates().len(), 1);
    generation
}

/// Renames every occurrence of the variable `from` to `to` and of `to` to `from`; returns the
/// number of renamed occurrences.
fn swap_names(term: &mut Term, from: &str, to: &str) -> usize {
    match term {
        Term::Variable { name, .. } if name == from => {
            *name = to.into();
            1
        }
        Term::Variable { name, .. } if name == to => {
            *name = from.into();
            1
        }
        Term::Rewrite { left, right } => swap_names(left, from, to) + swap_names(right, from, to),
        Term::As { pattern, alias } => swap_names(pattern, from, to) + swap_names(alias, from, to),
        Term::Sequence(items) => items
            .iter_mut()
            .map(|item| swap_names(item, from, to))
            .sum(),
        Term::Apply { arguments, .. } => arguments
            .iter_mut()
            .map(|argument| swap_names(argument, from, to))
            .sum(),
        Term::Annotated { term, .. } => swap_names(term, from, to),
        _ => 0,
    }
}

/// The edit that applies `swap_names(from, to)` to the term at `path` of `rule`.
fn renamed(baseline: &Baseline, rule: &str, path: &[u32], from: &str, to: &str) -> Edit {
    let at = TermRef::new(support::rule(baseline, rule), path);
    let expected = baseline.term(&at).expect("term").clone();
    let mut replacement = expected.clone();
    assert!(
        swap_names(&mut replacement, from, to) > 0,
        "{rule} {path:?}"
    );
    Edit::ReplaceTerm {
        at,
        expected,
        replacement,
    }
}

/// One atom of `constructor` binding `variable` at payload `position`.
fn binds(
    vocabulary: &EventVocabulary,
    constructor: &str,
    position: usize,
    variable: &str,
    sort: &str,
    with_bindings: bool,
) -> OracleDeclaration {
    let plan = PatternPlan::new(
        vocabulary,
        vec![(variable.into(), kore_sort(sort))],
        vec![PatternArm {
            atoms: vec![Atom {
                constructor: constructor.into(),
                payload: vec![PayloadClause {
                    position,
                    mode: MatchMode::Bind,
                    variable: variable.into(),
                }],
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
            with_bindings,
        },
    )
    .expect("oracle")
}

/// Audit A1 (ticket KS-T02, resolved by content anchoring). Exchanging the operations of
/// `SYMMEM.write` and `SYMMEM.load` leaves the rewrite system unchanged and moves only the
/// source positions that observation is attached to. Each moved content is anchored to the
/// baseline observation of the same content, so every event matches the baseline's and the
/// mutant survives. It is not `Equivalent`: `equivalent_compilation` compares rule order, and
/// kink tries same-priority rules in declaration order (decision KS-D4; ticket KS-T05).
#[test]
fn audit_a1_relabel_swap_is_not_killed() {
    with_stack(|| {
        let fixture = Symmem::new();
        let baseline = fixture.validator.baseline();
        let op = |rule| {
            let at = TermRef::new(support::rule(baseline, rule), [0, 0, 0]);
            let term = baseline.term(&at).expect("operation").clone();
            (at, term)
        };
        let (write_at, write_op) = op("SYMMEM.write");
        let (load_at, load_op) = op("SYMMEM.load");
        let patch = Patch::new(vec![
            Edit::ReplaceTerm {
                at: write_at,
                expected: write_op.clone(),
                replacement: load_op.clone(),
            },
            Edit::ReplaceTerm {
                at: load_at,
                expected: load_op,
                replacement: write_op,
            },
        ])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("SYMMEM.write", &[0, 0, 0]), ("SYMMEM.load", &[0, 0, 0])],
            "relabel-swap",
            &patch,
        );
        let run = run_campaign(
            &fixture.campaign(&fixture.tests),
            &generation,
            ScheduleMode::Full,
        )
        .expect("campaign");
        assert_baseline(&run);
        assert_eq!(outcomes(&run), vec![vec![A, A, A, A]; 4]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());
    });
}

/// Deleting the observed `SYMMEM.write` and inserting an unlabelled copy of it at the end of
/// the module moves the content to a new source position. The copy is anchored to the
/// baseline observation of `SYMMEM.write` (before anchoring, the deleted position was left out
/// of the mutant manifest and the trace killed the mutant), so the mutant survives.
#[test]
fn reinserted_observed_rule_is_not_killed() {
    with_stack(|| {
        let fixture = Symmem::new();
        let baseline = fixture.validator.baseline();
        let write = support::rule(baseline, "SYMMEM.write");
        let mut copy = baseline.sentence(&write).expect("rule").clone();
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
            copy.attributes_mut().remove(key.as_str());
        }
        let patch = Patch::new(vec![
            Edit::DeleteSentence { at: write.clone() },
            Edit::InsertSentence {
                position: InsertPosition::ModuleEnd(write.module.clone()),
                ordinal: 0,
                sentence: copy,
            },
        ])
        .expect("patch");
        let generation = fixed(baseline, &[("SYMMEM.write", &[0])], "reinsert", &patch);
        let run = run_campaign(
            &fixture.campaign(&fixture.tests),
            &generation,
            ScheduleMode::Full,
        )
        .expect("campaign");
        assert_baseline(&run);
        assert_eq!(outcomes(&run), vec![vec![A, A, A, A]; 4]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());
    });
}

/// Audit A2. Renaming `V` to `U` changes no pre-state, so no slot distinguishes.
#[test]
fn audit_a2_renamed_payload_variable_is_not_killed() {
    with_stack(|| {
        let fixture = Symmem::new();
        let baseline = fixture.validator.baseline();
        let patch = Patch::new(vec![
            renamed(baseline, "SYMMEM.write", &[0, 0, 0, 1], "V", "U"),
            renamed(baseline, "SYMMEM.load", &[0, 0, 0, 1], "V", "U"),
        ])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[
                ("SYMMEM.write", &[0, 0, 0, 1]),
                ("SYMMEM.load", &[0, 0, 0, 1]),
            ],
            "rename-value",
            &patch,
        );
        let run = run_campaign(
            &fixture.campaign(&fixture.tests),
            &generation,
            ScheduleMode::Full,
        )
        .expect("campaign");
        assert_baseline(&run);
        let mutant = &run.mutants[0];
        assert_eq!(outcomes(&run), vec![vec![A, A, A, A]; 4]);
        assert_eq!(mutant.report.status, MutantStatus::Survived);
        assert!(mutant.report.killing_test_ids.is_empty());
    });
}

/// Audit A3 (ticket CPL-T04, resolved in CPL-03), end to end. (1) A `with_bindings` plan over
/// a symbolic symmem test binds `addr(X)`: the baseline side is `Unknown` and the campaign is
/// refused. (2) guardedmem: the mutant's `load` also writes `A *Int 0`, so its binding set
/// `{0, Y *Int 0}` equals the baseline's `{0}` on every instance while differing as terms. It
/// must not be killed: in the Z3 profile the slot is `Unknown` (it was `Distinguish` before
/// CPL-03); in the no-Z3 profile the symbolic baseline is not admitted.
#[test]
fn audit_a3_symbolic_binding_sets_do_not_kill() {
    with_stack(|| {
        let fixture = Symmem::new();
        let generation = coupled(fixture.validator.baseline(), false);
        let bound = [TestCase {
            id: "sym-shared-bindings".into(),
            initial_state: fixture.tests[1].initial_state.clone(),
            oracles: vec![binds(
                &fixture.vocabulary,
                "memoryWrite",
                0,
                "A",
                "SortAddress",
                true,
            )],
        }];
        let failure = run_campaign(&fixture.campaign(&bound), &generation, ScheduleMode::Full)
            .expect_err("a symbolic binding set is not a baseline value");
        assert_eq!(failure.kind(), CampaignFailureKind::BaselineOracleFailed);

        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let load = support::rule(baseline, "GUARDEDMEM.load");
        let continuation = TermRef::new(load.clone(), [0, 1]);
        let p = baseline.term(&continuation).expect("P").clone();
        let a = term(baseline, "GUARDEDMEM.load", &[0, 0, 0, 0, 0]);
        let v = term(baseline, "GUARDEDMEM.load", &[0, 0, 0, 1]);
        let zero_address = Term::apply(
            "_*Int_",
            vec![
                a,
                Term::Token {
                    token: "0".into(),
                    sort: Sort::new("Int"),
                },
            ],
        );
        let patch = Patch::new(vec![Edit::ReplaceTerm {
            at: continuation,
            expected: p.clone(),
            replacement: Term::apply(
                "seq",
                vec![
                    Term::apply("write", vec![Term::apply("addr", vec![zero_address]), v]),
                    p,
                ],
            ),
        }])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("GUARDEDMEM.load", &[0, 1])],
            "write-zero-on-load",
            &patch,
        );
        let tests = [TestCase {
            id: "sym-zero-write".into(),
            initial_state: state(
                addr(support::int(0)),
                support::var("V", "SortInt"),
                addr(support::var("Y", "SortInt")),
                support::var("W", "SortInt"),
            ),
            oracles: vec![
                guarded.tests[0].oracles[0].clone(),
                binds(&guarded.vocabulary, "memoryWrite", 0, "A", "SortInt", true),
            ],
        }];
        let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full);
        if cfg!(feature = "z3") {
            // Without the CPL-03 guard this slot is `Distinguish` and the mutant `Killed`.
            let run = run.expect("Z3 admits the symbolic baseline");
            assert_eq!(outcomes(&run), vec![vec![A, U]]);
            assert_eq!(run.mutants[0].report.status, MutantStatus::Unknown);
        } else {
            assert_eq!(
                run.expect_err("no-Z3 leaves the guarded baseline undecided")
                    .kind(),
                CampaignFailureKind::BaselineOracleFailed
            );
        }
    });
}

/// Audit A4 (R1, retired for campaigns by CPL-05). `opaquemem.k` is refused in
/// `relations.rs`. Two distinct domain values of the non-builtin sort `Address` never reach a
/// relation: k-rust refuses to internalize a domain value of a sort without domain values, so
/// the baseline run fails and the campaign is refused (`BaselineError`) before any mutant runs.
/// (Were they admitted, `BackendRelations` counts only canonical `Int`/`Bool`/`String` values
/// as distinct, so the relation would be undecided.)
#[test]
fn audit_a4_distinct_non_builtin_domain_values_do_not_decide() {
    with_stack(|| {
        let fixture = Symmem::new();
        let generation = coupled(fixture.validator.baseline(), false);
        let dv = |value: &str| Pattern::DomainValue {
            sort: kore_sort("SortAddress"),
            value: value.into(),
        };
        let one = app("s", vec![z()]);
        let tests = [TestCase {
            id: "dv-addresses".into(),
            initial_state: state(dv("a"), one.clone(), dv("b"), one),
            oracles: fixture.tests[0].oracles.clone(),
        }];
        let result = run_campaign(&fixture.campaign(&tests), &generation, ScheduleMode::Full);
        let failure = result.expect_err("no baseline value");
        assert_eq!(failure.kind(), CampaignFailureKind::BaselineError);
    });
}

/// Audit A5 (ticket CPL-T08). `d() => 2` keeps `f` total on every instance, but withdrawal
/// removes `total` from `f` and `d` on the side the symbolic test runs on, which can then carry
/// a definedness case the compiled mutant lacks. No state or pattern slot of that side may
/// distinguish: every slot of the symbolic test is `Unknown` in both profiles.
#[test]
fn audit_a5_withdrawn_claims_do_not_kill() {
    with_stack(|| {
        let validator = NativeValidator::bind(
            support::load_path(
                &std::path::Path::new(support::DIR).join("symbolic-claim-survivor.k"),
                "SYMPARTIAL",
            ),
            CompileOptions::default(),
        );
        let baseline = validator.baseline();
        let observation = step_support::int_memory(true);
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        let program = |argument: Pattern| {
            let one = || app("addr", vec![support::int(1)]);
            support::initial_state(
                app(
                    "seq",
                    vec![
                        app("write", vec![one(), support::int(5)]),
                        app(
                            "seq",
                            vec![
                                app("half", vec![argument]),
                                app(
                                    "seq",
                                    vec![
                                        app("load", vec![one(), support::int(5)]),
                                        app("halt", vec![]),
                                    ],
                                ),
                            ],
                        ),
                    ],
                ),
                "SortProg",
            )
        };
        let oracles = vec![
            OracleDeclaration::new(
                CrashPolicy::CompareIdentity,
                Projection::State(StateProjection::WholeTerm),
            )
            .expect("final"),
            OracleDeclaration::new(
                CrashPolicy::CompareIdentity,
                Projection::State(StateProjection::ExitStop {
                    exit_code_cell: None,
                }),
            )
            .expect("exit"),
            pattern_with_sort(
                &vocabulary,
                "memoryWrite",
                "memoryLoad",
                Relation::EventuallyAfter,
                "SortInt",
            ),
        ];
        let tests = [TestCase {
            id: "X".into(),
            initial_state: program(nat("X")),
            oracles,
        }];
        let at = TermRef::new(support::rule(baseline, "SYMPARTIAL.d"), [0, 1]);
        let patch = Patch::new(vec![Edit::ReplaceTerm {
            expected: baseline.term(&at).expect("d body").clone(),
            replacement: Term::Token {
                token: "2".into(),
                sort: Sort::new("Int"),
            },
            at,
        }])
        .expect("patch");
        let generation = fixed(baseline, &[("SYMPARTIAL.d", &[0, 1])], "literal-d", &patch);
        let run = run_campaign(
            &Campaign {
                validator: &validator,
                module: "SYMPARTIAL",
                observation: &observation,
                classify: &normal,
                tests: &tests,
                budget: BUDGET,
            },
            &generation,
            ScheduleMode::Full,
        )
        .expect("campaign");
        let mutant = &run.mutants[0];
        assert_eq!(mutant.report.claims.withdrawn.len(), 2, "total on f and d");
        assert_eq!(outcomes(&run), vec![vec![U, U, U]]);
        assert_eq!(mutant.report.status, MutantStatus::Unknown);
        assert!(mutant.report.killing_test_ids.is_empty());
    });
}

/// Audit A6. CPL-T01 is resolved by pre-state payloads: execution-identical changes
/// survive, while row 1b still kills C where its execution differs.
#[test]
fn audit_a6_name_kept_meaning_change_is_not_killed() {
    with_stack(|| {
        let fixture = Symmem::new();
        let generation = coupled(fixture.validator.baseline(), true);
        let valued = [TestCase {
            id: "ground-shared-value".into(),
            initial_state: fixture.tests[0].initial_state.clone(),
            oracles: vec![binds(
                &fixture.vocabulary,
                "memoryWrite",
                1,
                "V",
                "SortNat",
                true,
            )],
        }];
        let run = run_campaign(&fixture.campaign(&valued), &generation, ScheduleMode::Full)
            .expect("campaign");
        assert_eq!(outcomes(&run), vec![vec![A]]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());

        let zero_valued = [TestCase {
            id: "ground-zero-value".into(),
            initial_state: state(addr(z()), z(), addr(z()), z()),
            oracles: vec![
                fixture.tests[0].oracles[0].clone(),
                binds(&fixture.vocabulary, "memoryWrite", 1, "V", "SortNat", true),
            ],
        }];
        let run = run_campaign(
            &fixture.campaign(&zero_valued),
            &generation,
            ScheduleMode::Full,
        )
        .expect("campaign");
        assert_eq!(outcomes(&run), vec![vec![D, D]]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(
            run.mutants[0].report.killing_test_ids,
            ["ground-zero-value"]
        );

        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let patch = Patch::new(vec![
            renamed(baseline, "GUARDEDMEM.write", &[0], "A", "V"),
            renamed(baseline, "GUARDEDMEM.write", &[1], "A", "V"),
        ])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("GUARDEDMEM.write", &[0])],
            "swap-names",
            &patch,
        );
        let tests = [TestCase {
            id: "ground-distinct-values".into(),
            initial_state: state(
                addr(support::int(1)),
                support::int(5),
                addr(support::int(1)),
                support::int(7),
            ),
            oracles: guarded.tests[1].oracles.clone(),
        }];
        let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full)
            .expect("campaign");
        assert_eq!(outcomes(&run), vec![vec![A, A]]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());
    });
}

/// An unmatched, well-formed declaration contributes no event on either side.
#[test]
fn unmatched_declaration_is_absent_not_an_error() {
    with_stack(|| {
        let mut fixture = Symmem::new();
        fixture.observation = vec![StepEventSpec {
            constructor: "memoryWrite".into(),
            pre: support::k_config(
                app(
                    "seq",
                    vec![app("free", vec![addr(z())]), app("halt", vec![])],
                ),
                "SortProg",
                "R",
                "C",
            ),
            post: Some(support::k_config(
                app("halt", vec![]),
                "SortProg",
                "R",
                "C2",
            )),
            payload: vec![],
        }];
        fixture.vocabulary =
            StepObservation::vocabulary_of(&fixture.observation).expect("vocabulary");
        let plan = PatternPlan::new(
            &fixture.vocabulary,
            vec![],
            vec![PatternArm {
                atoms: vec![Atom {
                    constructor: "memoryWrite".into(),
                    payload: vec![],
                }],
                relations: vec![],
            }],
            None,
        )
        .expect("plan");
        let tests = [case(
            "unmatched",
            fixture.tests[0].initial_state.clone(),
            &[OracleDeclaration::new(
                CrashPolicy::CompareIdentity,
                Projection::Pattern {
                    plan,
                    with_bindings: false,
                },
            )
            .expect("oracle")],
        )];
        let patch = Patch::new(vec![renamed(
            fixture.validator.baseline(),
            "SYMMEM.write",
            &[0],
            "A",
            "B",
        )])
        .expect("patch");
        let generation = fixed(
            fixture.validator.baseline(),
            &[("SYMMEM.write", &[0])],
            "alpha-rename",
            &patch,
        );
        let run = run_campaign(&fixture.campaign(&tests), &generation, ScheduleMode::Full)
            .expect("campaign");
        assert_eq!(
            run.baseline[0].run,
            SideRun::Sides {
                sides: vec![OracleSide::Normal(OracleValue::Pattern(
                    PatternValue::NoMatch
                ))]
            }
        );
        assert_survived(&run, &[vec![A]]);
    });
}

// ---------------------------------------------------------------- KS-07 audit attacks
//
// Kill-soundness README section 12, attacks AS1-AS7, plus the constructions the KS-07 audit
// added (section 15). Each test pins the measured status in both profiles; execution-identical
// constructions have no distinguishing pattern slot.

fn int_token(value: i64) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::new("Int"),
    }
}

/// The edit that replaces the term at `path` of `rule` by `replacement`.
fn replaced(baseline: &Baseline, rule: &str, path: &[u32], replacement: Term) -> Edit {
    let at = TermRef::new(support::rule(baseline, rule), path);
    Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("term").clone(),
        replacement,
        at,
    }
}

/// An insertable copy of the rule `label`: no label, identity or source-position attributes.
fn unlabelled_copy(baseline: &Baseline, label: &str) -> k_rust::definition::Sentence {
    let mut copy = baseline
        .sentence(&support::rule(baseline, label))
        .expect("rule")
        .clone();
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
        copy.attributes_mut().remove(key.as_str());
    }
    copy
}

/// `write(addr(write_address), write_value); load(addr(load_address), load_value); halt`.
fn int_program(
    write_address: i64,
    write_value: i64,
    load_address: Pattern,
    load_value: i64,
) -> Pattern {
    state(
        addr(support::int(write_address)),
        support::int(write_value),
        addr(load_address),
        support::int(load_value),
    )
}

fn whole_term() -> OracleDeclaration {
    OracleDeclaration::new(
        CrashPolicy::CompareIdentity,
        Projection::State(StateProjection::WholeTerm),
    )
    .expect("final")
}

fn case(id: &str, initial_state: Pattern, oracles: &[OracleDeclaration]) -> TestCase {
    TestCase {
        id: id.into(),
        initial_state,
        oracles: oracles.to_vec(),
    }
}

/// `guardedeq.k` observed like guardedmem: `write` and `load` with address and value payloads.
struct GuardedEq {
    validator: NativeValidator,
    vocabulary: EventVocabulary,
    observation: Vec<StepEventSpec>,
}

impl GuardedEq {
    fn new() -> Self {
        let validator =
            NativeValidator::bind(support::load("guardedeq.k"), CompileOptions::default());
        let observation = step_support::int_memory(true);
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        Self {
            validator,
            vocabulary,
            observation,
        }
    }

    fn campaign<'a>(&'a self, tests: &'a [TestCase]) -> Campaign<'a> {
        Campaign {
            validator: &self.validator,
            module: "GUARDEDEQ",
            observation: &self.observation,
            classify: &normal,
            tests,
            budget: BUDGET,
        }
    }

    /// Final state, `GWL-after`, the write's value, the load's value (both `with_bindings`),
    /// and whether a load was observed.
    fn oracles(&self) -> Vec<OracleDeclaration> {
        vec![
            whole_term(),
            pattern_with_sort(
                &self.vocabulary,
                "memoryWrite",
                "memoryLoad",
                Relation::EventuallyAfter,
                "SortInt",
            ),
            binds(&self.vocabulary, "memoryWrite", 1, "V", "SortInt", true),
            binds(&self.vocabulary, "memoryLoad", 1, "V", "SortInt", true),
            binds(&self.vocabulary, "memoryLoad", 0, "A", "SortInt", false),
        ]
    }
}

fn assert_survived(run: &kink_campaign::CampaignRun, expected: &[Vec<OracleOutcome>]) {
    assert_eq!(outcomes(run), expected);
    assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
    assert!(run.mutants[0].report.killing_test_ids.is_empty());
}

/// AS1. Swapping the names `A` and `V` throughout `GUARDEDMEM.load` (body and `requires`) is
/// an alpha-renaming: every pre-state is the baseline's, so no slot distinguishes. The ground
/// row runs in both profiles; the symbolic guardedmem tests need Z3 to admit the baseline.
#[test]
fn audit_ks_as1_load_side_alpha_swap_is_not_killed() {
    with_stack(|| {
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let patch = Patch::new(vec![
            renamed(baseline, "GUARDEDMEM.load", &[0], "A", "V"),
            renamed(baseline, "GUARDEDMEM.load", &[1], "A", "V"),
        ])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("GUARDEDMEM.load", &[0])],
            "swap-load-names",
            &patch,
        );
        let ground = [case(
            "ground-distinct-values",
            int_program(1, 5, support::int(1), 7),
            &guarded.tests[1].oracles,
        )];
        let run = run_campaign(&guarded.campaign(&ground), &generation, ScheduleMode::Full)
            .expect("ground campaign");
        assert_survived(&run, &[vec![A, A]]);
        let run = run_campaign(
            &guarded.campaign(&guarded.tests),
            &generation,
            ScheduleMode::Full,
        );
        if cfg!(feature = "z3") {
            assert_survived(
                &run.expect("Z3 admits the symbolic baseline"),
                &vec![vec![A, A]; 2],
            );
        } else {
            assert_eq!(
                run.expect_err("no-Z3 leaves the guarded baseline undecided")
                    .kind(),
                CampaignFailureKind::BaselineOracleFailed
            );
        }
    });
}

/// AS2: equivalent guards give Agree or Unknown only. Under W with Z3, successor substitution makes the write binding Unknown; P survives.
#[test]
fn audit_ks_as2_requires_rephrasing_is_not_killed() {
    with_stack(|| {
        for whole in [true, false] {
            let mut fixture = GuardedEq::new();
            fixture.observation = step_support::int_memory(whole);
            let baseline = fixture.validator.baseline();
            let a = term(baseline, "GUARDEDEQ.write", &[0, 0, 0, 0, 0]);
            let patch = Patch::new(vec![replaced(
                baseline,
                "GUARDEDEQ.write",
                &[1],
                Term::apply("_==Int_", vec![a, int_token(1)]),
            )])
            .expect("patch");
            let generation = fixed(
                baseline,
                &[("GUARDEDEQ.write", &[1])],
                "equality-guard",
                &patch,
            );
            let x = || support::var("X", "SortInt");
            let symbolic = state(addr(x()), support::int(5), addr(x()), support::int(7));
            let oracles = fixture.oracles();
            let tests = [
                case("sym-eq", symbolic.clone(), &oracles),
                case("ground-eq", int_program(1, 5, support::int(1), 7), &oracles),
            ];
            let run = run_campaign(&fixture.campaign(&tests), &generation, ScheduleMode::Full);
            if cfg!(feature = "z3") {
                let run = run.expect("Z3 admits the symbolic baseline");
                assert_eq!(
                    outcomes(&run),
                    vec![
                        if whole {
                            vec![A, A, U, A, A]
                        } else {
                            vec![A; 5]
                        },
                        vec![A; 5]
                    ]
                );
                assert_eq!(
                    run.mutants[0].report.status,
                    if whole {
                        MutantStatus::Unknown
                    } else {
                        MutantStatus::Survived
                    }
                );
                assert!(run.mutants[0].report.killing_test_ids.is_empty());
            } else {
                assert_eq!(
                    run.expect_err("no-Z3 leaves the symbolic guard undecided")
                        .kind(),
                    CampaignFailureKind::BaselineOracleFailed
                );
                let run = run_campaign(
                    &fixture.campaign(&tests[1..]),
                    &generation,
                    ScheduleMode::Full,
                )
                .expect("ground campaign");
                assert_survived(&run, &[vec![A; 5]]);
            }
            let bound = [case(
                "sym-eq-address",
                symbolic,
                &[binds(
                    &fixture.vocabulary,
                    "memoryLoad",
                    0,
                    "A",
                    "SortInt",
                    true,
                )],
            )];
            let failure = run_campaign(&fixture.campaign(&bound), &generation, ScheduleMode::Full)
                .expect_err("a symbolic address is not a baseline value");
            assert_eq!(failure.kind(), CampaignFailureKind::BaselineOracleFailed);
        }
    });
}

/// AS3 (KS-R3). A patch cannot write the configuration layout that step declaration shapes
/// depend on. Loading expands `configuration` into generated sentences (the `generatedTop`
/// production and the init rules carry no location and are not authored); the only authored
/// non-rule sentence of symmem is the `<k>` cell production. Sites are rule term positions
/// only, and a generation refuses an edit of a sentence that holds no site
/// (`UnauthorizedEdit`), so no mutant of a campaign can shift a declared path.
#[test]
fn audit_ks_as3_configuration_layout_is_not_writable() {
    with_stack(|| {
        use k_rust::definition::Sentence;
        let fixture = Symmem::new();
        let baseline = fixture.validator.baseline();
        let authored = baseline
            .authored_sentences()
            .filter(|(at, _)| at.module == "SYMMEM")
            .collect::<Vec<_>>();
        assert!(
            authored
                .iter()
                .all(|(_, sentence)| !matches!(sentence, Sentence::Configuration { .. }))
        );
        let productions = authored
            .iter()
            .filter(|(_, sentence)| !matches!(sentence, Sentence::Rule { .. }))
            .collect::<Vec<_>>();
        let [(cell, Sentence::Production { label, .. })] = productions.as_slice() else {
            panic!("one authored non-rule sentence, the <k> cell: {productions:?}")
        };
        assert_eq!(label.as_ref().map(|label| label.name.as_str()), Some("<k>"));
        let discovery = derive_sites(
            baseline,
            "configuration",
            &[
                SiteSelector::RuleLabel("SYMMEM.write".into()),
                SiteSelector::Path(vec![0]),
            ],
        )
        .expect("site");
        let failure = select(&discovery, exact(1, 1), 1)
            .expect("selection")
            .fold("configuration", |_| {
                Patch::new(vec![Edit::AddAttribute {
                    at: cell.clone(),
                    key: "audit".into(),
                    value: serde_json::Value::String(String::new()),
                }])
                .expect("patch")
            })
            .expect_err("an edit outside the origin's sentences");
        assert_eq!(
            failure.kind(),
            kink_patch::CandidateFailureKind::UnauthorizedEdit
        );
    });
}

/// AS4. A `with_bindings` plan is admitted only for a ground baseline value.
/// S1 distinguishes those values under W because its write no longer reaches P;
/// P preserves the original binding values; every symbolic value
/// (`sym-shared`, `sym-distinct`, and `sym-clash`'s value `V`) is refused on the baseline, as
/// A3 row 1. Same in both profiles.
#[test]
fn audit_ks_as4_symbolic_before_terms_are_not_binding_values() {
    with_stack(|| {
        for whole in [true, false] {
            let mut fixture = Symmem::new();
            fixture.observation = step_support::symmem(whole);
            let generation = release_after_write(fixture.validator.baseline());
            for (test, position, admitted) in [
                (0, 0, true),
                (0, 1, true),
                (1, 0, false),
                (1, 1, false),
                (2, 0, false),
                (2, 1, false),
                (3, 0, true),
                (3, 1, false),
            ] {
                let (variable, sort) = [("A", "SortAddress"), ("V", "SortNat")][position];
                let bound = [case(
                    &fixture.tests[test].id,
                    fixture.tests[test].initial_state.clone(),
                    &[binds(
                        &fixture.vocabulary,
                        "memoryWrite",
                        position,
                        variable,
                        sort,
                        true,
                    )],
                )];
                let run = run_campaign(&fixture.campaign(&bound), &generation, ScheduleMode::Full);
                if admitted {
                    let run = run.expect("ground binding admitted");
                    assert_eq!(outcomes(&run), vec![vec![if whole { D } else { A }]]);
                    assert_eq!(
                        run.mutants[0].report.status,
                        if whole {
                            MutantStatus::Killed
                        } else {
                            MutantStatus::Survived
                        }
                    );
                } else {
                    assert_eq!(
                        run.expect_err("symbolic binding refused").kind(),
                        CampaignFailureKind::BaselineOracleFailed,
                        "{} {position}",
                        fixture.tests[test].id
                    );
                }
            }
        }
    });
}

/// AS5: splitting the write guard preserves every declared step observation and survives.
#[test]
fn audit_so_as5_guard_split_is_not_killed() {
    with_stack(|| {
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let write = support::rule(baseline, "GUARDEDMEM.write");
        let a = term(baseline, "GUARDEDMEM.write", &[0, 0, 0, 0, 0]);
        let mut zero = unlabelled_copy(baseline, "GUARDEDMEM.write");
        if let k_rust::definition::Sentence::Rule { requires, .. } = &mut zero {
            *requires = Term::apply("_==Int_", vec![a.clone(), int_token(0)]);
        }
        let patch = Patch::new(vec![
            replaced(
                baseline,
                "GUARDEDMEM.write",
                &[1],
                Term::apply("_>Int_", vec![a, int_token(0)]),
            ),
            Edit::InsertSentence {
                position: InsertPosition::After(write),
                ordinal: 0,
                sentence: zero,
            },
        ])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("GUARDEDMEM.write", &[1])],
            "guard-split",
            &patch,
        );
        let oracles = &guarded.tests[1].oracles;
        let tests = [
            case(
                "ground-zero",
                int_program(0, 5, support::int(0), 7),
                oracles,
            ),
            case("ground-one", int_program(1, 5, support::int(1), 7), oracles),
        ];
        let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full)
            .expect("campaign");
        assert_eq!(outcomes(&run), vec![vec![A, A], vec![A, A]]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());
    });
}

/// Priority shadowing and a same-priority twin preserve the declared observations; both survive.
#[test]
fn audit_so_priority_shadowing_is_not_killed() {
    with_stack(|| {
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let write = support::rule(baseline, "GUARDEDMEM.write");
        let oracles = &guarded.tests[1].oracles;
        let tests = [
            case(
                "ground-zero",
                int_program(0, 5, support::int(0), 7),
                oracles,
            ),
            case("ground-one", int_program(1, 5, support::int(1), 7), oracles),
        ];
        let insert = |sentence| {
            Patch::new(vec![Edit::InsertSentence {
                position: InsertPosition::After(write.clone()),
                ordinal: 0,
                sentence,
            }])
            .expect("patch")
        };

        let mut shadow = unlabelled_copy(baseline, "GUARDEDMEM.write");
        shadow.attributes_mut().set(
            AttributeKey::Priority,
            serde_json::Value::String("40".into()),
        );
        let generation = fixed(
            baseline,
            &[("GUARDEDMEM.write", &[0])],
            "shadow",
            &insert(shadow),
        );
        let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full)
            .expect("campaign");
        assert_eq!(outcomes(&run), vec![vec![A, A]; 2]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());

        let a = term(baseline, "GUARDEDMEM.write", &[0, 0, 0, 0, 0]);
        let mut twin = unlabelled_copy(baseline, "GUARDEDMEM.write");
        if let k_rust::definition::Sentence::Rule { requires, .. } = &mut twin {
            *requires = Term::apply("_<=Int_", vec![int_token(0), a]);
        }
        let generation = fixed(
            baseline,
            &[("GUARDEDMEM.write", &[0])],
            "twin",
            &insert(twin),
        );
        let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full)
            .expect("campaign");
        assert_survived(&run, &vec![vec![A, A]; 2]);
    });
}

/// Moved content preserves the executions and every declared observation, including after rephrasing the guard.
#[test]
fn audit_so_moved_unobserved_content_is_not_killed() {
    with_stack(|| {
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let field = |rule: &str, path: &[u32]| term(baseline, rule, path);
        let oracles = [
            guarded.tests[1].oracles[0].clone(),
            guarded.tests[1].oracles[1].clone(),
            binds(&guarded.vocabulary, "memoryWrite", 0, "A", "SortInt", false),
        ];
        let tests = [
            case(
                "ground-negative",
                int_program(-1, 5, support::int(1), 7),
                &oracles,
            ),
            case(
                "ground-one",
                int_program(1, 5, support::int(1), 7),
                &oracles,
            ),
        ];
        let a = field("GUARDEDMEM.write", &[0, 0, 0, 0, 0]);
        for (rephrased, expected, changed) in [
            (false, vec![vec![A, A, A]; 2], false),
            (true, vec![vec![A, A, A], vec![A, A, A]], true),
        ] {
            let write_guard = if rephrased {
                Term::apply("_<=Int_", vec![int_token(0), a.clone()])
            } else {
                field("GUARDEDMEM.write", &[1])
            };
            let patch = Patch::new(vec![
                replaced(
                    baseline,
                    "GUARDEDMEM.write",
                    &[0],
                    field("GUARDEDMEM.writeFault", &[0]),
                ),
                replaced(
                    baseline,
                    "GUARDEDMEM.write",
                    &[1],
                    field("GUARDEDMEM.writeFault", &[1]),
                ),
                replaced(
                    baseline,
                    "GUARDEDMEM.writeFault",
                    &[0],
                    field("GUARDEDMEM.write", &[0]),
                ),
                replaced(baseline, "GUARDEDMEM.writeFault", &[1], write_guard),
            ])
            .expect("patch");
            let generation = fixed(
                baseline,
                &[("GUARDEDMEM.write", &[0]), ("GUARDEDMEM.writeFault", &[0])],
                "swap-with-unobserved",
                &patch,
            );
            let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full)
                .expect("campaign");
            if changed {
                assert_eq!(outcomes(&run), expected);
                assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
                assert!(run.mutants[0].report.killing_test_ids.is_empty());
            } else {
                assert_survived(&run, &expected);
            }
        }
    });
}

/// AS6 (KS-R2, ticket KS-T08). `guardedeq.k`'s observed `load` runs on the remainder of the
/// higher-priority `loadZero` guard; the mutant writes that guard `0 ==Int A` instead of
/// `A ==Int 0`, which changes only the syntax of the remainder's path condition. With Z3 the
/// symbolic test's value binding and load presence agree on every branch: Survived. Without
/// Z3 the symbolic guard is undecided and the baseline is refused.
#[test]
fn audit_ks_as6_remainder_restriction_is_not_killed() {
    with_stack(|| {
        let fixture = GuardedEq::new();
        let baseline = fixture.validator.baseline();
        let a = term(baseline, "GUARDEDEQ.loadZero", &[0, 0, 0, 0, 0]);
        let patch = Patch::new(vec![replaced(
            baseline,
            "GUARDEDEQ.loadZero",
            &[1],
            Term::apply("_==Int_", vec![int_token(0), a]),
        )])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("GUARDEDEQ.loadZero", &[1])],
            "flip-equality",
            &patch,
        );
        let oracles = fixture.oracles();
        let tests = [case(
            "sym-remainder",
            int_program(1, 5, support::var("Y", "SortInt"), 7),
            &[oracles[0].clone(), oracles[3].clone(), oracles[4].clone()],
        )];
        let run = run_campaign(&fixture.campaign(&tests), &generation, ScheduleMode::Full);
        if cfg!(feature = "z3") {
            assert_survived(
                &run.expect("Z3 admits the symbolic baseline"),
                &[vec![A, A, A]],
            );
        } else {
            assert_eq!(
                run.expect_err("no-Z3 leaves the remainder undecided")
                    .kind(),
                CampaignFailureKind::BaselineOracleFailed
            );
        }
    });
}

/// AS7: duplicate rule identities leave pattern slots Unknown; the ground final state kills. Claim withdrawal, moved content and alpha renaming preserve the declared values.
#[test]
fn audit_ks_as7_anchoring_fails_closed() {
    with_stack(|| {
        // (a)
        let fixture = Symmem::new();
        let baseline = fixture.validator.baseline();
        let patch = Patch::new(vec![replaced(
            baseline,
            "SYMMEM.load",
            &[0, 0, 0],
            term(baseline, "SYMMEM.write", &[0, 0, 0]),
        )])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("SYMMEM.load", &[0, 0, 0])],
            "load-as-write",
            &patch,
        );
        let run = run_campaign(
            &fixture.campaign(&fixture.tests),
            &generation,
            ScheduleMode::Full,
        )
        .expect("campaign");
        let mutant = &run.mutants[0];
        assert_eq!(mutant.plan.mutant_failure, None);
        assert_eq!(mutant.report.status, MutantStatus::Killed);
        assert_eq!(
            outcomes(&run),
            vec![vec![D, U, U, U], vec![U; 4], vec![U; 4], vec![U; 4]]
        );
        assert_eq!(mutant.report.killing_test_ids, ["ground-shared"]);
        let side = fixture.validator.validate(&patch).expect("mutant");
        let mut backend = k_rust::backend::Backend::new(
            &side.artifacts().definition_kore,
            "SYMMEM",
            k_rust::backend::BackendOptions::default(),
        )
        .expect("backend");
        let adapter = kink_native::execution::ExecutionAdapter::with_profile(
            kink_native::execution::SolverProfile::BUILD,
        );
        let execution = adapter
            .execute(&mut backend, &fixture.tests[0].initial_state, BUDGET)
            .expect("event-free execution");
        let parsed = k_rust::kore::parser::parse_definition(&side.artifacts().definition_kore)
            .expect("KORE");
        let sorts = kink_pattern::SymbolSorts::from_definition(&parsed);
        let bridged = backend
            .with_solver(None, |definition, solver| {
                let decider = kink_native::step_events::ObservationDecider::new(
                    definition,
                    solver,
                    TestInitialState::of_test(&fixture.tests[0].initial_state),
                );
                Ok::<_, k_rust::backend::BackendError>(kink_native::bridge::paths_from_execution(
                    &execution,
                    &kink_native::bridge::BridgeContext {
                        test_id: "ground-shared",
                        classify: &normal,
                        sorts: &sorts,
                    },
                    &|term| decider.definition_independent(term),
                ))
            })
            .expect("backend definition")
            .expect("leaf ordinal paths");
        assert!(bridged.paths.iter().all(|path| path.events.is_empty()));
        assert_eq!(bridged.paths.len(), execution.leaves().len());
        for (ordinal, path) in bridged.paths.iter().enumerate() {
            assert_eq!(path.path_key, Some(format!("leaf:{ordinal}")));
        }
        assert!(matches!(
            adapter
                .execute_steps(&mut backend, &fixture.tests[0].initial_state, BUDGET)
                .expect("execution"),
            Err(kink_native::execution::StepRunFailure::AmbiguousRule(_))
        ));

        // (b)
        let eq = GuardedEq::new();
        let baseline = eq.validator.baseline();
        let x = term(baseline, "GUARDEDEQ.norm", &[0, 1]);
        let patch = Patch::new(vec![replaced(
            baseline,
            "GUARDEDEQ.norm",
            &[0, 1],
            Term::apply("_+Int_", vec![x, int_token(0)]),
        )])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("GUARDEDEQ.norm", &[0, 1])],
            "norm-plus-zero",
            &patch,
        );
        let oracles = eq.oracles();
        let oracles = [oracles[0].clone(), oracles[1].clone(), oracles[3].clone()];
        let tests = [
            case(
                "ground-norm",
                int_program(1, 5, support::int(1), 7),
                &oracles,
            ),
            case(
                "sym-norm",
                int_program(1, 5, support::var("Y", "SortInt"), 7),
                &oracles,
            ),
        ];
        let run = run_campaign(&eq.campaign(&tests), &generation, ScheduleMode::Full);
        if cfg!(feature = "z3") {
            let run = run.expect("Z3 admits the symbolic baseline");
            assert_survived(&run, &vec![vec![A, A, A]; 2]);
            let claims = &run.mutants[0].report.claims;
            let load = support::rule(baseline, "GUARDEDEQ.load");
            assert!(claims.withdrawn.iter().any(|claim| {
                claim.key == "preserves-definedness"
                    && claim.origin == kink_patch::SentenceOrigin::Baseline(load.clone())
            }));
        } else {
            assert_eq!(
                run.expect_err("no-Z3 leaves the symbolic guard undecided")
                    .kind(),
                CampaignFailureKind::BaselineOracleFailed
            );
            let run = run_campaign(&eq.campaign(&tests[..1]), &generation, ScheduleMode::Full)
                .expect("ground campaign");
            assert_survived(&run, &[vec![A, A, A]]);
        }

        // (c)
        let baseline = fixture.validator.baseline();
        let body = |rule| {
            let at = TermRef::new(support::rule(baseline, rule), [0]);
            let body = baseline.term(&at).expect("body").clone();
            (at, body)
        };
        let (write_at, write_body) = body("SYMMEM.write");
        let (load_at, load_body) = body("SYMMEM.load");
        let mut renamed_write = write_body.clone();
        assert!(swap_names(&mut renamed_write, "V", "U") > 0);
        for moved_write in [write_body.clone(), renamed_write] {
            let patch = Patch::new(vec![
                Edit::ReplaceTerm {
                    at: write_at.clone(),
                    expected: write_body.clone(),
                    replacement: load_body.clone(),
                },
                Edit::ReplaceTerm {
                    at: load_at.clone(),
                    expected: load_body.clone(),
                    replacement: moved_write,
                },
            ])
            .expect("patch");
            let generation = fixed(
                baseline,
                &[("SYMMEM.write", &[0]), ("SYMMEM.load", &[0])],
                "swap-bodies",
                &patch,
            );
            let campaign = fixture.campaign(&fixture.tests);
            let full = run_campaign(&campaign, &generation, ScheduleMode::Full).expect("full");
            let stopped =
                run_campaign(&campaign, &generation, ScheduleMode::FirstKill).expect("first kill");
            assert_survived(&full, &vec![vec![A, A, A, A]; 4]);
            assert_eq!(stopped.mutants[0].plan, full.mutants[0].plan);
            let manifest = fixture
                .tests
                .iter()
                .map(|test| kink_campaign::ManifestTest {
                    test_id: test.id.clone(),
                    slot_count: test.oracles.len(),
                })
                .collect::<Vec<_>>();
            assert_eq!(
                stopped.mutants[0].report,
                derive_mutant_report(&full.mutants[0].plan, &manifest, ScheduleMode::FirstKill)
                    .expect("derived report")
            );
            assert_eq!(stopped.mutants[0].report.status, MutantStatus::Survived);
        }
    });
}

// ---------------------------------------------------------------- EI-04 execution audit fixtures

fn ei_guard_split(baseline: &Baseline) -> Vec<Edit> {
    let write = support::rule(baseline, "GUARDEDMEM.write");
    let a = term(baseline, "GUARDEDMEM.write", &[0, 0, 0, 0, 0]);
    let mut zero = unlabelled_copy(baseline, "GUARDEDMEM.write");
    if let k_rust::definition::Sentence::Rule { requires, .. } = &mut zero {
        *requires = Term::apply("_==Int_", vec![a.clone(), int_token(0)]);
    }
    vec![
        replaced(
            baseline,
            "GUARDEDMEM.write",
            &[1],
            Term::apply("_>Int_", vec![a, int_token(0)]),
        ),
        Edit::InsertSentence {
            position: InsertPosition::After(write),
            ordinal: 0,
            sentence: zero,
        },
    ]
}

/// G on a fault continuation has identical configurations and declared observations, so this test survives.
#[test]
fn audit_so_g_fault_tail_is_not_killed() {
    with_stack(|| {
        let fixture = Guarded::new();
        let generation = inverted_load_sign(fixture.validator.baseline());
        let program = support::initial_state(
            app(
                "seq",
                vec![
                    app("write", vec![addr(support::int(1)), support::int(5)]),
                    app(
                        "seq",
                        vec![
                            app("load", vec![addr(support::int(1)), support::int(7)]),
                            app("fault", vec![]),
                        ],
                    ),
                ],
            ),
            "SortProg",
        );
        let tests = [case(
            "ground-fault-tail",
            program,
            &fixture.tests[1].oracles,
        )];
        let run = run_campaign(&fixture.campaign(&tests), &generation, ScheduleMode::Full)
            .expect("campaign");
        assert_eq!(outcomes(&run), vec![vec![A, A]]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());
    });
}

/// Different leaf partitions of the same instances preserve the repeated-write value. The no-Z3 symbolic baseline is refused.
#[test]
fn audit_so_symbolic_guard_split_is_not_killed() {
    with_stack(|| {
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let patch = Patch::new(ei_guard_split(baseline)).expect("patch");
        let generation = fixed(
            baseline,
            &[("GUARDEDMEM.write", &[1])],
            "guard-split",
            &patch,
        );
        let plan = PatternPlan::new(
            &guarded.vocabulary,
            vec![("A".into(), kore_sort("SortInt"))],
            vec![PatternArm {
                atoms: [MatchMode::Bind, MatchMode::Use]
                    .into_iter()
                    .map(|mode| Atom {
                        constructor: "memoryWrite".into(),
                        payload: vec![PayloadClause {
                            position: 0,
                            mode,
                            variable: "A".into(),
                        }],
                    })
                    .collect(),
                relations: vec![Relation::EventuallyAfter],
            }],
            None,
        )
        .expect("plan");
        let repeated = OracleDeclaration::new(
            CrashPolicy::CompareIdentity,
            Projection::Pattern {
                plan,
                with_bindings: false,
            },
        )
        .expect("oracle");
        let oracles = [guarded.tests[1].oracles[0].clone(), repeated];
        let program = |x: Pattern| {
            support::initial_state(
                app(
                    "seq",
                    vec![
                        app("write", vec![addr(support::int(0)), support::int(5)]),
                        app(
                            "seq",
                            vec![
                                app("write", vec![addr(x.clone()), support::int(6)]),
                                app(
                                    "seq",
                                    vec![
                                        app("load", vec![addr(x), support::int(7)]),
                                        app("halt", vec![]),
                                    ],
                                ),
                            ],
                        ),
                    ],
                ),
                "SortProg",
            )
        };
        for (id, initial) in [
            ("ground-zero", program(support::int(0))),
            ("sym-x", program(support::var("X", "SortInt"))),
        ] {
            let tests = [case(id, initial, &oracles)];
            let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full);
            if id == "sym-x" && !cfg!(feature = "z3") {
                assert_eq!(
                    run.expect_err("symbolic baseline refused").kind(),
                    CampaignFailureKind::BaselineOracleFailed
                );
            } else {
                let run = run.expect("baseline admitted");
                assert_eq!(outcomes(&run), vec![vec![A, A]], "{id}");
                assert_eq!(run.mutants[0].report.status, MutantStatus::Survived, "{id}");
                assert!(run.mutants[0].report.killing_test_ids.is_empty());
            }
        }
    });
}

/// Shadowing preserves observations on symbolic and ground addresses. The no-Z3 symbolic baseline is refused.
#[test]
fn audit_so_symbolic_priority_shadowing_is_not_killed() {
    with_stack(|| {
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let write = support::rule(baseline, "GUARDEDMEM.write");
        let mut shadow = unlabelled_copy(baseline, "GUARDEDMEM.write");
        shadow.attributes_mut().set(
            AttributeKey::Priority,
            serde_json::Value::String("40".into()),
        );
        let patch = Patch::new(vec![Edit::InsertSentence {
            position: InsertPosition::After(write),
            ordinal: 0,
            sentence: shadow,
        }])
        .expect("patch");
        let generation = fixed(baseline, &[("GUARDEDMEM.write", &[0])], "shadow", &patch);
        let y = || support::var("Y", "SortInt");
        let oracles = &guarded.tests[1].oracles;
        let tests = [
            case(
                "sym-same",
                state(addr(y()), support::int(5), addr(y()), support::int(7)),
                oracles,
            ),
            case(
                "ground-zero",
                int_program(0, 5, support::int(0), 7),
                oracles,
            ),
        ];
        let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full);
        if cfg!(feature = "z3") {
            let run = run.expect("Z3 admits symbolic baseline");
            assert_eq!(outcomes(&run), vec![vec![A, A], vec![A, A]]);
            assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
            assert!(run.mutants[0].report.killing_test_ids.is_empty());
        } else {
            assert_eq!(
                run.expect_err("symbolic baseline refused").kind(),
                CampaignFailureKind::BaselineOracleFailed
            );
            let ground = run_campaign(
                &guarded.campaign(&tests[1..]),
                &generation,
                ScheduleMode::Full,
            )
            .expect("ground baseline admitted");
            assert_eq!(outcomes(&ground), vec![vec![A, A]]);
            assert_eq!(ground.mutants[0].report.status, MutantStatus::Survived);
            assert!(ground.mutants[0].report.killing_test_ids.is_empty());
        }
    });
}

/// AS5 plus a load-value stutter changes execution but preserves the address-only declared pattern; no slot distinguishes.
#[test]
fn audit_so_unobserved_difference_is_not_observed() {
    with_stack(|| {
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let load = support::rule(baseline, "GUARDEDMEM.load");
        let tests = [
            case(
                "ground-zero",
                int_program(0, 5, support::int(0), 7),
                &guarded.tests[1].oracles,
            ),
            case(
                "ground-one",
                int_program(1, 5, support::int(1), 7),
                &guarded.tests[1].oracles,
            ),
        ];
        let left = term(baseline, "GUARDEDMEM.load", &[0, 0]);
        let v = term(baseline, "GUARDEDMEM.load", &[0, 0, 0, 1]);
        let right = ei_substitute(
            &left,
            &v,
            &Term::apply("_+Int_", vec![v.clone(), int_token(1)]),
        );
        let mut bump = unlabelled_copy(baseline, "GUARDEDMEM.load");
        if let k_rust::definition::Sentence::Rule { body, requires, .. } = &mut bump {
            *body = Term::Rewrite {
                left: Box::new(left),
                right: Box::new(right),
            };
            *requires = Term::apply("_==Int_", vec![v, int_token(7)]);
        }
        bump.attributes_mut().set(
            AttributeKey::Priority,
            serde_json::Value::String("40".into()),
        );
        let mut edits = ei_guard_split(baseline);
        edits.push(Edit::InsertSentence {
            position: InsertPosition::After(load),
            ordinal: 0,
            sentence: bump,
        });
        let patch = Patch::new(edits).expect("patch");
        let generation = fixed(
            baseline,
            &[("GUARDEDMEM.write", &[1]), ("GUARDEDMEM.load", &[1])],
            "as5+bump",
            &patch,
        );
        let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full)
            .expect("campaign");
        assert_eq!(outcomes(&run), vec![vec![A, A], vec![A, A]]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());
    });
}

fn ei_substitute(term: &Term, from: &Term, to: &Term) -> Term {
    if term == from {
        return to.clone();
    }
    match term {
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments
                .iter()
                .map(|argument| ei_substitute(argument, from, to))
                .collect(),
        },
        Term::Annotated { term, metadata } => Term::Annotated {
            term: Box::new(ei_substitute(term, from, to)),
            metadata: metadata.clone(),
        },
        other => other.clone(),
    }
}

// ---------------------------------------------------------------- EI-05 audit attacks
//
// Execution-identity README section 12, attacks AT1-AT14, plus the constructions the EI-05
// audit added (README section 15). Each test pins the measured status in both profiles.

/// An integer-memory fixture with declarations over its own configuration transitions.
struct EiMemory {
    validator: NativeValidator,
    vocabulary: EventVocabulary,
    observation: Vec<StepEventSpec>,
    module: String,
}

impl EiMemory {
    fn new(file: &str) -> Self {
        let validator = NativeValidator::bind(support::load(file), CompileOptions::default());
        let module = file.strip_suffix(".k").expect("a .k file").to_uppercase();
        let observation = if file == "freshgen.k" {
            step_support::freshgen(true)
        } else {
            step_support::int_memory(true)
        };
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        Self {
            validator,
            vocabulary,
            observation,
            module,
        }
    }

    fn campaign<'a>(&'a self, tests: &'a [TestCase]) -> Campaign<'a> {
        Campaign {
            validator: &self.validator,
            module: &self.module,
            observation: &self.observation,
            classify: &normal,
            tests,
            budget: BUDGET,
        }
    }

    /// `GWL-after`: a write, then eventually a load at the same address.
    fn gwl_after(&self) -> OracleDeclaration {
        pattern_with_sort(
            &self.vocabulary,
            "memoryWrite",
            "memoryLoad",
            Relation::EventuallyAfter,
            "SortInt",
        )
    }

    fn rule(&self, label: &str) -> String {
        format!("{}.{label}", self.module)
    }
}

/// Two `constructor` events in a row at one address (bound, then used).
fn ei_repeated(vocabulary: &EventVocabulary, constructor: &str) -> OracleDeclaration {
    let plan = PatternPlan::new(
        vocabulary,
        vec![("A".into(), kore_sort("SortInt"))],
        vec![PatternArm {
            atoms: [MatchMode::Bind, MatchMode::Use]
                .into_iter()
                .map(|mode| Atom {
                    constructor: constructor.into(),
                    payload: vec![PayloadClause {
                        position: 0,
                        mode,
                        variable: "A".into(),
                    }],
                })
                .collect(),
            relations: vec![Relation::NextEvent],
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

/// An unobserved copy of `label` with `priority(40)`, so it shadows `label`.
fn ei_shadow(baseline: &Baseline, label: &str) -> k_rust::definition::Sentence {
    let mut shadow = unlabelled_copy(baseline, label);
    shadow.attributes_mut().set(
        AttributeKey::Priority,
        serde_json::Value::String("40".into()),
    );
    shadow
}

/// `true` or `false` as a `Bool` condition.
fn ei_bool(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::new("Bool"),
    }
}

fn ei_program(operations: Vec<Pattern>, last: Pattern) -> Pattern {
    let program = operations
        .into_iter()
        .rev()
        .fold(last, |rest, operation| app("seq", vec![operation, rest]));
    support::initial_state(program, "SortProg")
}

/// AT1: freshgen observes its stamped continuation. Renaming an existential outside the payload preserves both declared values.
/// The two definitions execute identically, so the result does not rest on names being renamed
/// apart: under variable identity the renamed existential is minted from the request's counter
/// on both sides (printed `Ex-hVar'Ques'T-bN` against `Ex-hVar'Ques'U-bN`), and freshgen's existential rules
/// no longer switch off the initial variables.
#[test]
fn audit_so_at1_existential_rename_is_not_killed() {
    with_stack(|| {
        let fresh = EiMemory::new("freshgen.k");
        let baseline = fresh.validator.baseline();
        let write_label = fresh.rule("write");
        let oracles = [whole_term(), fresh.gwl_after()];
        let tests = [
            case(
                "ground-zero",
                int_program(0, 5, support::int(0), 7),
                &oracles,
            ),
            case(
                "ground-one",
                int_program(1, 5, support::int(1), 7),
                &oracles,
            ),
        ];
        for rename in [false, true] {
            let a = term(baseline, &write_label, &[0, 0, 0, 0, 0]);
            let mut zero = unlabelled_copy(baseline, &write_label);
            if let k_rust::definition::Sentence::Rule { requires, body, .. } = &mut zero {
                *requires = Term::apply("_==Int_", vec![a.clone(), int_token(0)]);
                if rename {
                    assert_eq!(swap_names(body, "?T", "?U"), 1);
                }
            }
            let patch = Patch::new(vec![
                replaced(
                    baseline,
                    &write_label,
                    &[1],
                    Term::apply("_>Int_", vec![a, int_token(0)]),
                ),
                Edit::InsertSentence {
                    position: InsertPosition::After(support::rule(baseline, &write_label)),
                    ordinal: 0,
                    sentence: zero,
                },
            ])
            .expect("patch");
            let generation = fixed(baseline, &[(&write_label, &[1])], "guard-split", &patch);
            let run = run_campaign(&fresh.campaign(&tests), &generation, ScheduleMode::Full)
                .expect("campaign");
            assert_eq!(
                outcomes(&run),
                vec![vec![A, A], vec![A, A]],
                "rename {rename}"
            );
            assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
            assert!(run.mutants[0].report.killing_test_ids.is_empty());
        }
    });
}

/// AT2: the declaration observes a write transition without binding its function residue. Shadowing and the residue equation preserve the observed value.
#[test]
fn audit_so_at2_function_residue_is_not_killed() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("residue.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let observation = residue_observation(true);
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        let occurs = OracleDeclaration::new(
            CrashPolicy::CompareIdentity,
            Projection::Pattern {
                plan: PatternPlan::new(
                    &vocabulary,
                    vec![],
                    vec![PatternArm {
                        atoms: vec![Atom {
                            constructor: "memoryWrite".into(),
                            payload: vec![],
                        }],
                        relations: vec![],
                    }],
                    None,
                )
                .expect("plan"),
                with_bindings: false,
            },
        )
        .expect("oracle");
        // f(1) => 5
        let mut equation = unlabelled_copy(baseline, "RESIDUE.f");
        if let k_rust::definition::Sentence::Rule { body, .. } = &mut equation {
            *body = Term::Rewrite {
                left: Box::new(Term::apply("f", vec![int_token(1)])),
                right: Box::new(int_token(5)),
            };
        }
        let program = ei_program(
            vec![
                app("write", vec![app("f", vec![support::int(1)])]),
                app("load", vec![support::int(5)]),
            ],
            app("halt", vec![]),
        );
        let tests = [case("residue", program, &[whole_term(), occurs])];
        let campaign = Campaign {
            validator: &validator,
            module: "RESIDUE",
            observation: &observation,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        for with_equation in [false, true] {
            let mut edits = vec![Edit::InsertSentence {
                position: InsertPosition::After(support::rule(baseline, "RESIDUE.write")),
                ordinal: 0,
                sentence: ei_shadow(baseline, "RESIDUE.write"),
            }];
            let mut sites: Vec<(&str, &[u32])> = vec![("RESIDUE.write", &[0])];
            if with_equation {
                edits.push(Edit::InsertSentence {
                    position: InsertPosition::After(support::rule(baseline, "RESIDUE.f")),
                    ordinal: 0,
                    sentence: equation.clone(),
                });
                sites.push(("RESIDUE.f", &[0]));
            }
            let patch = Patch::new(edits).expect("patch");
            let generation = fixed(baseline, &sites, "residue", &patch);
            let run = run_campaign(&campaign, &generation, ScheduleMode::Full).expect("campaign");
            assert_eq!(outcomes(&run), vec![vec![A, A]], "equation {with_equation}");
            assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
            assert!(run.mutants[0].report.killing_test_ids.is_empty());
        }
    });
}

/// AT3 (breadth bound). A priority-40 unobserved copy of symmem's `left` removes the `right`
/// branch of a fork. Unbounded, the mutant direction has no witness and the baseline's `right`
/// path, whose second state is a `load` where every mutant state is a `write`, is the witness
/// (`Clash`): a real difference, killed. With `max_breadth` 1 the baseline is BreadthBound and
/// is refused, in both profiles. A pattern `Distinguish` needs a complete `NoMatch` side, and a
/// complete side covers, so `NotCovering` cannot arise from a campaign; the kink-native row d7
/// pins it.
#[test]
fn audit_ei_at3_breadth_bounded_baseline_is_refused() {
    with_stack(|| {
        let fixture = Symmem::new();
        let baseline = fixture.validator.baseline();
        let patch = Patch::new(vec![Edit::InsertSentence {
            position: InsertPosition::After(support::rule(baseline, "SYMMEM.left")),
            ordinal: 0,
            sentence: ei_shadow(baseline, "SYMMEM.left"),
        }])
        .expect("patch");
        let generation = fixed(baseline, &[("SYMMEM.left", &[0])], "left-only", &patch);
        let program = support::initial_state(
            app(
                "fork",
                vec![
                    app(
                        "seq",
                        vec![app("write", vec![addr(z()), z()]), app("halt", vec![])],
                    ),
                    app(
                        "seq",
                        vec![app("load", vec![addr(z()), z()]), app("halt", vec![])],
                    ),
                ],
            ),
            "SortProg",
        );
        let oracles = [binds(
            &fixture.vocabulary,
            "memoryLoad",
            0,
            "A",
            "SortAddress",
            false,
        )];
        let tests = [case("fork", program, &oracles)];
        let run = run_campaign(&fixture.campaign(&tests), &generation, ScheduleMode::Full)
            .expect("campaign");
        assert_eq!(outcomes(&run), vec![vec![D]]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(run.mutants[0].report.killing_test_ids, ["fork"]);
        let mut bounded = fixture.campaign(&tests);
        bounded.budget.max_breadth = std::num::NonZeroUsize::new(1);
        assert_eq!(
            run_campaign(&bounded, &generation, ScheduleMode::Full)
                .expect_err("breadth-bounded baseline")
                .kind(),
            CampaignFailureKind::BaselineOracleFailed
        );
    });
}

/// AT5 (withdrawn side, Remainder positions; EI-R6, EI-R7). guardedeq's `norm(X) => X +Int 1`
/// makes `load`'s guard false and withdraws `preserves-definedness` from `load`, so the symbolic
/// test runs on the withdrawn side. Its stuck leaf (1 position after a Remainder entry, which
/// adds none) is shorter than both baseline paths (2 positions): `Length`, `Length`, and no
/// `SignatureDiffers` (Z3). The ground test is killed by its final state (the state shortcut).
/// Without Z3 the symbolic baseline is refused.
#[test]
fn audit_ei_at5_withdrawn_remainder_path_is_proved_by_length() {
    with_stack(|| {
        let eq = GuardedEq::new();
        let baseline = eq.validator.baseline();
        let x = term(baseline, "GUARDEDEQ.norm", &[0, 1]);
        let patch = Patch::new(vec![replaced(
            baseline,
            "GUARDEDEQ.norm",
            &[0, 1],
            Term::apply("_+Int_", vec![x, int_token(1)]),
        )])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("GUARDEDEQ.norm", &[0, 1])],
            "norm-plus-one",
            &patch,
        );
        let oracles = eq.oracles();
        let oracles = [oracles[0].clone(), oracles[1].clone(), oracles[3].clone()];
        let tests = [
            case(
                "sym-norm",
                int_program(1, 5, support::var("Y", "SortInt"), 7),
                &oracles,
            ),
            case(
                "ground-norm",
                int_program(1, 5, support::int(1), 7),
                &oracles,
            ),
        ];
        let run = run_campaign(&eq.campaign(&tests), &generation, ScheduleMode::Full);
        if cfg!(feature = "z3") {
            let run = run.expect("Z3 admits the symbolic baseline");
            assert_eq!(outcomes(&run), vec![vec![U, D, A], vec![D, D, D]]);
            assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
            assert_eq!(
                run.mutants[0].report.killing_test_ids,
                ["sym-norm", "ground-norm"]
            );
        } else {
            assert_eq!(
                run.expect_err("no-Z3 leaves the symbolic guard undecided")
                    .kind(),
                CampaignFailureKind::BaselineOracleFailed
            );
            let run = run_campaign(&eq.campaign(&tests[1..]), &generation, ScheduleMode::Full)
                .expect("ground campaign");
            assert_eq!(outcomes(&run), vec![vec![D, D, D]]);
            assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
        }
    });
}

/// AT6 (a real difference). A same-priority unobserved copy of `GUARDEDMEM.write` whose
/// right-hand side loads before continuing adds a path with two loads in a row. The final
/// result agrees; the repeated-load pattern distinguishes, and the mutant's second path is
/// longer than the baseline's complete path (`Length`). The kill is kept in both profiles.
#[test]
fn audit_ei_at6_changed_duplicate_keeps_its_kill() {
    with_stack(|| {
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let mut copy = unlabelled_copy(baseline, "GUARDEDMEM.write");
        if let k_rust::definition::Sentence::Rule { body, .. } = &mut copy {
            // seq(write(addr(A), V), P) => seq(load(addr(A), V), P)
            let field = |path: &[u32]| term(baseline, "GUARDEDMEM.write", path);
            *body = Term::Rewrite {
                left: Box::new(field(&[0, 0])),
                right: Box::new(Term::apply(
                    "seq",
                    vec![
                        Term::apply("load", vec![field(&[0, 0, 0, 0]), field(&[0, 0, 0, 1])]),
                        field(&[0, 1]),
                    ],
                )),
            };
        }
        let patch = Patch::new(vec![Edit::InsertSentence {
            position: InsertPosition::After(support::rule(baseline, "GUARDEDMEM.write")),
            ordinal: 0,
            sentence: copy,
        }])
        .expect("patch");
        let generation = fixed(baseline, &[("GUARDEDMEM.write", &[0])], "duplicate", &patch);
        let oracles = [
            guarded.tests[1].oracles[0].clone(),
            ei_repeated(&guarded.vocabulary, "memoryLoad"),
        ];
        let tests = [case(
            "ground-one",
            int_program(1, 5, support::int(1), 7),
            &oracles,
        )];
        let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full)
            .expect("campaign");
        assert_eq!(outcomes(&run), vec![vec![A, D]]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(run.mutants[0].report.killing_test_ids, ["ground-one"]);
    });
}

/// AT7: committed effects stay outside step observations under SO-D5; the effect-only difference survives.
#[test]
fn audit_so_at7_effect_only_difference_is_not_killed() {
    with_stack(|| {
        let fixture = EiMemory::new("effectmem.k");
        let baseline = fixture.validator.baseline();
        let logged = fixture.rule("writeLogged");
        let patch = Patch::new(vec![Edit::InsertSentence {
            position: InsertPosition::After(support::rule(baseline, &logged)),
            ordinal: 0,
            sentence: ei_shadow(baseline, &logged),
        }])
        .expect("patch");
        let generation = fixed(baseline, &[(&logged, &[0])], "logged", &patch);
        let oracles = [whole_term(), fixture.gwl_after()];
        let tests = [case(
            "ground-one",
            int_program(1, 5, support::int(1), 7),
            &oracles,
        )];
        let run = run_campaign(&fixture.campaign(&tests), &generation, ScheduleMode::Full)
            .expect("campaign");
        assert_eq!(outcomes(&run), vec![vec![A, A]]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());
    });
}

/// AT8: terminal classes stay outside step events under SO-D5. WholeTerm and the declared trace agree for Stuck versus an undefined step.
#[test]
fn audit_so_at8_stuck_against_undefined_step_is_not_killed() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("guardeddiv.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let observation = step_support::int_memory(true);
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        let patch = Patch::new(vec![
            replaced(baseline, "GUARDEDDIV.divide", &[1], ei_bool(true)),
            Edit::InsertSentence {
                position: InsertPosition::After(support::rule(baseline, "GUARDEDDIV.write")),
                ordinal: 0,
                sentence: ei_shadow(baseline, "GUARDEDDIV.write"),
            },
        ])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("GUARDEDDIV.divide", &[1]), ("GUARDEDDIV.write", &[0])],
            "unguarded-divide",
            &patch,
        );
        let program = |divisor: i64| {
            ei_program(
                vec![
                    app("write", vec![addr(support::int(1)), support::int(5)]),
                    app("load", vec![addr(support::int(1)), support::int(7)]),
                ],
                app("divide", vec![support::int(1), support::int(divisor)]),
            )
        };
        let oracles = [
            whole_term(),
            pattern_with_sort(
                &vocabulary,
                "memoryWrite",
                "memoryLoad",
                Relation::EventuallyAfter,
                "SortInt",
            ),
        ];
        let tests = [
            case("div-zero", program(0), &oracles),
            case("div-one", program(1), &oracles),
        ];
        let campaign = Campaign {
            validator: &validator,
            module: "GUARDEDDIV",
            observation: &observation,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let run = run_campaign(&campaign, &generation, ScheduleMode::Full).expect("campaign");
        assert_eq!(outcomes(&run), vec![vec![A, A], vec![A, A]]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        assert!(run.mutants[0].report.killing_test_ids.is_empty());
    });
}

/// AT10: claim withdrawal and shadowing preserve the declared observation. The no-Z3 symbolic baseline is refused.
#[test]
fn audit_so_at10_withdrawn_rule_competition_is_not_killed() {
    with_stack(|| {
        let eq = GuardedEq::new();
        let baseline = eq.validator.baseline();
        let x = term(baseline, "GUARDEDEQ.norm", &[0, 1]);
        let patch = Patch::new(vec![
            replaced(
                baseline,
                "GUARDEDEQ.norm",
                &[0, 1],
                Term::apply("_+Int_", vec![x, int_token(0)]),
            ),
            Edit::InsertSentence {
                position: InsertPosition::After(support::rule(baseline, "GUARDEDEQ.write")),
                ordinal: 0,
                sentence: ei_shadow(baseline, "GUARDEDEQ.write"),
            },
        ])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("GUARDEDEQ.norm", &[0, 1]), ("GUARDEDEQ.write", &[0])],
            "withdraw-and-shadow",
            &patch,
        );
        let oracles = eq.oracles();
        let oracles = [oracles[0].clone(), oracles[1].clone()];
        let tests = [
            case(
                "sym-load",
                int_program(1, 5, support::var("Y", "SortInt"), 7),
                &oracles,
            ),
            case(
                "ground-one",
                int_program(1, 5, support::int(1), 7),
                &oracles,
            ),
        ];
        let run = run_campaign(&eq.campaign(&tests), &generation, ScheduleMode::Full);
        if cfg!(feature = "z3") {
            let run = run.expect("Z3 admits the symbolic baseline");
            assert_eq!(outcomes(&run), vec![vec![A, A], vec![A, A]]);
            assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
            assert!(run.mutants[0].report.killing_test_ids.is_empty());
            assert!(!run.mutants[0].report.claims.withdrawn.is_empty());
        } else {
            assert_eq!(
                run.expect_err("no-Z3 leaves the symbolic guard undecided")
                    .kind(),
                CampaignFailureKind::BaselineOracleFailed
            );
            let run = run_campaign(&eq.campaign(&tests[1..]), &generation, ScheduleMode::Full)
                .expect("ground campaign");
            assert_eq!(outcomes(&run), vec![vec![A, A]]);
            assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        }
    });
}

/// AT11: a simplification headed by a constructor is Invalid; an anywhere axiom changes the signature, making every pattern slot Unknown.
/// Precision loss (VI-03F, k-rust 4d80cea6): the anywhere variant is [[U,U,U]] in both profiles because value-production definedness is withheld; status stays Unknown.
#[test]
fn audit_ei_at11_constructor_lemma_is_refused() {
    with_stack(|| {
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let mut lemma = unlabelled_copy(baseline, "GUARDEDMEM.write");
        if let k_rust::definition::Sentence::Rule { body, requires, .. } = &mut lemma {
            *body = Term::Rewrite {
                left: Box::new(Term::apply("addr", vec![int_token(0)])),
                right: Box::new(Term::apply("addr", vec![int_token(1)])),
            };
            *requires = ei_bool(true);
        }
        let oracles = [
            guarded.tests[1].oracles[0].clone(),
            guarded.tests[1].oracles[1].clone(),
            binds(&guarded.vocabulary, "memoryWrite", 0, "A", "SortInt", true),
        ];
        let tests = [case(
            "ground-zero",
            int_program(0, 5, support::int(0), 7),
            &oracles,
        )];
        for (key, status) in [
            (AttributeKey::Simplification, MutantStatus::Invalid),
            (AttributeKey::Anywhere, MutantStatus::Unknown),
        ] {
            let mut sentence = lemma.clone();
            sentence
                .attributes_mut()
                .set(key, serde_json::Value::String(String::new()));
            let patch = Patch::new(vec![Edit::InsertSentence {
                position: InsertPosition::After(support::rule(baseline, "GUARDEDMEM.write")),
                ordinal: 0,
                sentence,
            }])
            .expect("patch");
            let generation = fixed(baseline, &[("GUARDEDMEM.write", &[0])], "lemma", &patch);
            let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full)
                .expect("campaign");
            let mutant = &run.mutants[0];
            assert_eq!(mutant.report.status, status, "{key:?}");
            assert!(mutant.report.killing_test_ids.is_empty());
            if status == MutantStatus::Invalid {
                assert_eq!(
                    mutant.plan.mutant_failure,
                    Some(kink_campaign::MutantScopeFailure::Rejected)
                );
            } else {
                assert_eq!(outcomes(&run), vec![vec![U, U, U]]);
            }
        }
    });
}

/// FirstKill equals Full for surviving competition constructions and stops G at its first actual killing test. Competition slots agree or stay Unknown.
#[test]
fn audit_so_at13_first_kill_equals_full() {
    with_stack(|| {
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let oracles = &guarded.tests[1].oracles;
        let fault_tail = ei_program(
            vec![
                app("write", vec![addr(support::int(1)), support::int(5)]),
                app("load", vec![addr(support::int(1)), support::int(7)]),
            ],
            app("fault", vec![]),
        );
        let tests = [
            case("ground-fault-tail", fault_tail, oracles),
            case(
                "ground-zero",
                int_program(0, 5, support::int(0), 7),
                oracles,
            ),
            case("ground-one", int_program(1, 5, support::int(1), 7), oracles),
        ];
        let split = Patch::new(ei_guard_split(baseline)).expect("patch");
        let shadow = Patch::new(vec![Edit::InsertSentence {
            position: InsertPosition::After(support::rule(baseline, "GUARDEDMEM.write")),
            ordinal: 0,
            sentence: ei_shadow(baseline, "GUARDEDMEM.write"),
        }])
        .expect("patch");
        let rows = [
            (
                fixed(
                    baseline,
                    &[("GUARDEDMEM.write", &[1])],
                    "guard-split",
                    &split,
                ),
                vec![vec![A, A]; 3],
                MutantStatus::Survived,
                3,
            ),
            (
                fixed(baseline, &[("GUARDEDMEM.write", &[0])], "shadow", &shadow),
                vec![vec![A, A]; 3],
                MutantStatus::Survived,
                3,
            ),
            (
                inverted_load_sign(baseline),
                vec![vec![A, A], vec![D, D], vec![D, D]],
                MutantStatus::Killed,
                2,
            ),
        ];
        let manifest = tests
            .iter()
            .map(|test| kink_campaign::ManifestTest {
                test_id: test.id.clone(),
                slot_count: test.oracles.len(),
            })
            .collect::<Vec<_>>();
        let campaign = guarded.campaign(&tests);
        for (generation, expected, status, executed) in rows {
            let full = run_campaign(&campaign, &generation, ScheduleMode::Full).expect("full");
            let stopped =
                run_campaign(&campaign, &generation, ScheduleMode::FirstKill).expect("first kill");
            assert_eq!(outcomes(&full), expected);
            let (full, stopped) = (&full.mutants[0], &stopped.mutants[0]);
            assert_eq!(full.report.status, status);
            assert_eq!(stopped.plan.tests[..executed], full.plan.tests[..executed]);
            assert!(
                stopped.plan.tests[executed..]
                    .iter()
                    .all(|test| test.run == TestRun::SkippedAfterKill)
            );
            assert_eq!(stopped.evidence, full.evidence[..executed]);
            assert_eq!(
                stopped.report,
                derive_mutant_report(&full.plan, &manifest, ScheduleMode::FirstKill)
                    .expect("derived report")
            );
        }
    });
}

/// Variable identity (VI-04; EI-05 pinned the opposite): the stable variables are the test's
/// initial variables, read verbatim, whatever their spelling. G's sym-guarded test with `X1`, `Y1`, `V1`, `W1`
/// for `X`, `Y`, `V`, `W` keeps G's pattern
/// kill (Z3), and FirstKill stops at it. Before VI-04 names ending in a digit were never
/// stable (a mint could print as one), so the pattern slot was Unknown
/// (`[[A,U],[D,D]]`, killed by ground-guarded only). Without Z3 the symbolic baseline is
/// refused, as for G.
#[test]
fn audit_vi_digit_suffixed_initial_names_are_stable() {
    with_stack(|| {
        let fixture = Guarded::new();
        let generation = inverted_load_sign(fixture.validator.baseline());
        let int = |name: &str| support::var(name, "SortInt");
        let tests = [
            case(
                "sym-guarded-1",
                state(addr(int("X1")), int("V1"), addr(int("Y1")), int("W1")),
                &fixture.tests[0].oracles,
            ),
            fixture.tests[1].clone(),
        ];
        let run = run_campaign(&fixture.campaign(&tests), &generation, ScheduleMode::Full);
        if cfg!(feature = "z3") {
            let run = run.expect("Z3 admits the symbolic baseline");
            assert_eq!(outcomes(&run), vec![vec![A, D], vec![D, D]]);
            assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
            assert_eq!(
                run.mutants[0].report.killing_test_ids,
                ["sym-guarded-1", "ground-guarded"]
            );
            let first = run_campaign(
                &fixture.campaign(&tests),
                &generation,
                ScheduleMode::FirstKill,
            )
            .expect("Z3 admits the symbolic baseline");
            assert_eq!(first.mutants[0].report.status, MutantStatus::Killed);
            assert_eq!(first.mutants[0].report.killing_test_ids, ["sym-guarded-1"]);
        } else {
            assert_eq!(
                run.expect_err("symbolic baseline remains undecided").kind(),
                CampaignFailureKind::BaselineOracleFailed
            );
        }
    });
}

/// EI-05: the state-oracle side of the EI-02b name conflation. conflate.k's `go` narrows
/// `X:Box` to `c(I)` with a fresh `I`, which k-rust printed as `ExVarI<n>` before variable
/// identity; with the initial variables named `ExVarI0` and `ExVarI1`, two feasible baseline
/// leaves were then decided Unsat on their read state and could be discarded. Under
/// variable identity the mint is printed apart from every initial name, so no such leaf is
/// Unsat and the Unsat discard is sound (ticket EI-T02 (iii), closed). The baseline is still
/// refused, for either naming and in both profiles, because narrowing also leaves a remainder
/// leaf (`not exists I. X = c(I)`) whose feasibility is Unknown, so the state slot is
/// incomplete (the mutant merges `goPos` and `goNeg` into one unguarded rule).
#[test]
fn audit_ei_conflated_names_leave_the_state_slot_refused() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("conflate.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let patch = Patch::new(vec![
            replaced(baseline, "CONFLATE.goPos", &[1], ei_bool(true)),
            Edit::DeleteSentence {
                at: support::rule(baseline, "CONFLATE.goNeg"),
            },
        ])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("CONFLATE.goPos", &[1]), ("CONFLATE.goNeg", &[1])],
            "merge",
            &patch,
        );
        for (a, b) in [("A", "B"), ("ExVarI0", "ExVarI1")] {
            let program = ei_program(
                vec![
                    app("check", vec![support::var(a, "SortInt")]),
                    app("check2", vec![support::var(b, "SortInt")]),
                    app("go", vec![support::var("X", "SortBox")]),
                ],
                app("done", vec![]),
            );
            let tests = [case("conflate", program, &[whole_term()])];
            let campaign = Campaign {
                validator: &validator,
                module: "CONFLATE",
                observation: &[],
                classify: &normal,
                tests: &tests,
                budget: BUDGET,
            };
            assert_eq!(
                run_campaign(&campaign, &generation, ScheduleMode::Full)
                    .expect_err("incomplete symbolic baseline")
                    .kind(),
                CampaignFailureKind::BaselineOracleFailed,
                "names {a}, {b}"
            );
        }
    });
}

/// VI-05: the alpha-equivalent `go` rule renames `I` to `K` after eight or nine burns.
/// Each narrowing retains a binding that makes leaf feasibility Unknown, so both ground
/// tests are refused in both profiles. With the binding-elimination counterfactual this
/// was Killed at nine burns before VI and is Survived under VI
/// (variable-identity/prototype/own-best/elim.log). A future SE-T01 packet must re-pin
/// this test and must never make either burn count Killed.
#[test]
fn audit_vi_fresh_counter_collision_is_not_killed() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("conflate3.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let patch =
            Patch::new(vec![renamed(baseline, "CONFLATE3.go", &[0], "I", "K")]).expect("patch");
        let generation = fixed(baseline, &[("CONFLATE3.go", &[0])], "rename", &patch);
        for burns in [8usize, 9] {
            let mut operations = vec![app("new1", vec![])];
            operations.extend((0..burns).map(|_| app("burnNew", vec![])));
            operations.push(app("new2", vec![]));
            let program = ei_program(operations, app("done", vec![]));
            assert!(program.free_variables().is_empty());
            let tests = [case("collide", program, &[whole_term()])];
            let campaign = Campaign {
                validator: &validator,
                module: "CONFLATE3",
                observation: &[],
                classify: &normal,
                tests: &tests,
                budget: BUDGET,
            };
            assert_eq!(
                run_campaign(&campaign, &generation, ScheduleMode::Full)
                    .expect_err("incomplete ground baseline")
                    .kind(),
                CampaignFailureKind::BaselineOracleFailed,
                "burns {burns}"
            );
        }
    });
}

/// VI-AT1: `EI-bM0-b1` is read as the variable `EI-bM0-b1` (k-rust v2 decoded it to the
/// forged scope candidate `EI!M0!1`; under v3 no read name contains `!`).
/// The two-constructor baseline and existential mutant denote the same relation.
/// Under Z3, narrowing the user-sort variable leaves both baseline leaves Unknown,
/// so admission refuses the baseline; without Z3 it is refused as well.
/// The campaign never returns a CampaignRun or kills the mutant.
/// The leaf and invalid-name checks are pinned in name_identity.rs.
#[test]
fn audit_vi_scope_names_do_not_capture_stable_variables() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("scopeforge.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let x = so_var("X", "Ab");
        let y = so_var("?Y", "Ab");
        let patch = Patch::new(vec![
            replaced(
                baseline,
                "SCOPEFORGE.startA",
                &[0],
                Term::Rewrite {
                    left: Box::new(Term::apply("start", vec![x.clone()])),
                    right: Box::new(Term::apply("pair", vec![x.clone(), y.clone()])),
                },
            ),
            replaced(
                baseline,
                "SCOPEFORGE.startA",
                &[2],
                Term::apply("_=/=K_", vec![y, x]),
            ),
            Edit::DeleteSentence {
                at: support::rule(baseline, "SCOPEFORGE.startB"),
            },
        ])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("SCOPEFORGE.startA", &[0]), ("SCOPEFORGE.startB", &[0])],
            "scope-forgery",
            &patch,
        );
        let observation = [StepEventSpec {
            constructor: "startPair".into(),
            pre: support::k_config(
                app("start", vec![support::var("X", "SortAb")]),
                "SortProg",
                "R",
                "C",
            ),
            post: Some(support::k_config(
                app(
                    "pair",
                    vec![support::var("Y", "SortAb"), support::var("Z", "SortAb")],
                ),
                "SortPair",
                "R",
                "C2",
            )),
            payload: vec!["Y".into()],
        }];
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        let tests = [case(
            "scope-forgery",
            support::initial_state(
                app("start", vec![support::var("EI-bM0-b1", "SortAb")]),
                "SortProg",
            ),
            &[binds(&vocabulary, "startPair", 0, "A", "SortAb", true)],
        )];
        let campaign = Campaign {
            validator: &validator,
            module: "SCOPEFORGE",
            observation: &observation,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        assert_eq!(
            run_campaign(&campaign, &generation, ScheduleMode::Full)
                .expect_err("undecided narrowing refuses the baseline in both profiles")
                .kind(),
            CampaignFailureKind::BaselineOracleFailed,
        );
    });
}

// ---------------------------------------------------------------- TB-01: unbound equations (AT12)

/// `unbound.k` with one `finish` step declaration per `run*` and `pass` rule, binding the
/// value under `done`.
struct Unbound {
    validator: NativeValidator,
    observation: Vec<StepEventSpec>,
    vocabulary: EventVocabulary,
}

impl Unbound {
    fn new() -> Self {
        let validator =
            NativeValidator::bind(support::load("unbound.k"), CompileOptions::default());
        let observation = ["LblrunRes", "LblrunReq", "LblrunPart", "Lblpass"]
            .into_iter()
            .map(|symbol| StepEventSpec {
                constructor: "finish".into(),
                pre: support::k_config(
                    support::app(symbol, vec![support::var("I", "SortInt")]),
                    "SortProg",
                    "R",
                    "C",
                ),
                post: Some(support::k_config(
                    app("done", vec![support::var("V", "SortInt")]),
                    "SortProg",
                    "R",
                    "C2",
                )),
                payload: vec!["V".into()],
            })
            .collect::<Vec<_>>();
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        Self {
            validator,
            observation,
            vocabulary,
        }
    }
}

/// One AT12 campaign's result: refused, or run with its per-test outcome vectors and status.
#[derive(Clone, Debug, PartialEq, Eq)]
enum UnboundAudit {
    Refused(CampaignFailureKind),
    Ran(Vec<Vec<OracleOutcome>>, MutantStatus),
}

/// The initial states of one AT12 audit, by test id: the call reached by a rule (`run`,
/// `runX(arg)` rewrites to `done(call(arg))`), written in the initial state and bound by a rule
/// (`pass`), written under the free constructor `done` that no rule rewrites (`stuck`), alone
/// in the `k` cell through the `Int` injection (`bare`), and the symbolic `run` and `stuck`
/// with the argument an `Int` variable `N`.
fn unbound_states(call: &str, run: &str, argument: i64) -> Vec<(&'static str, Pattern)> {
    let call_of = |argument: Pattern| app(call, vec![argument]);
    let n = || support::var("N", "SortInt");
    let program = |program: Pattern| support::initial_state(program, "SortProg");
    vec![
        ("run", program(app(run, vec![support::int(argument)]))),
        (
            "pass",
            program(app("pass", vec![call_of(support::int(argument))])),
        ),
        (
            "stuck",
            program(app("done", vec![call_of(support::int(argument))])),
        ),
        (
            "bare",
            support::initial_state(call_of(support::int(argument)), "SortInt"),
        ),
        ("sym-run", program(app(run, vec![n()]))),
        ("sym-stuck", program(app("done", vec![call_of(n())]))),
    ]
}

/// Runs each (state, oracle) of `expected` as its own one-test campaign in Full and FirstKill
/// (a baseline refusal of one test would hide the others) and checks the result. The oracles
/// are `whole` (the final state) and `bind` (the value under `done` bound by `finish`, with
/// bindings). TV-01 pins every row after guarding definition-dependent terminal values.
/// A refusal means the baseline slot is Unknown; neither profile may kill any row.
fn unbound_audit(
    operator: &str,
    patch: &Patch,
    site: &str,
    states: &[(&str, Pattern)],
    expected: &[(&str, &str, Option<UnboundAudit>)],
) {
    let fixture = Unbound::new();
    let generation = fixed(
        fixture.validator.baseline(),
        &[(site, &[0])],
        operator,
        patch,
    );
    let oracle = |name: &str| match name {
        "whole" => whole_term(),
        "bind" => binds(&fixture.vocabulary, "finish", 0, "V", "SortInt", true),
        _ => unreachable!("{name}"),
    };
    assert_eq!(expected.len(), 2 * states.len());
    for (id, oracle_name, expected) in expected {
        let state = &states
            .iter()
            .find(|(state_id, _)| state_id == id)
            .expect("state")
            .1;
        let tests = [case(id, state.clone(), &[oracle(oracle_name)])];
        let campaign = Campaign {
            validator: &fixture.validator,
            module: "UNBOUND",
            observation: &fixture.observation,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let actual = match run_campaign(&campaign, &generation, mode) {
                Ok(run) => {
                    if run.mutants[0].report.status != MutantStatus::Killed {
                        assert!(run.mutants[0].report.killing_test_ids.is_empty());
                    }
                    UnboundAudit::Ran(outcomes(&run), run.mutants[0].report.status)
                }
                Err(error) => UnboundAudit::Refused(error.kind()),
            };
            match expected {
                Some(expected) => {
                    assert_eq!(&actual, expected, "{operator} {id} {oracle_name} {mode:?}");
                }
                None => assert!(
                    !matches!(actual, UnboundAudit::Ran(_, MutantStatus::Killed)),
                    "{operator} {id} {oracle_name} {mode:?}: an equation k-rust leaves unused \
                     kills: {actual:?}"
                ),
            }
        }
    }
}

const REFUSED: Option<UnboundAudit> = Some(UnboundAudit::Refused(
    CampaignFailureKind::BaselineOracleFailed,
));

/// AT12 (a), unbound result variable: `fres(X) => Y requires Y ==Int X +Int 1` against
/// `fres(X) => X +Int 1`, semantically the same function. k-rust 927b9ce6 never uses an
/// instance of the baseline equation: the call is kept with an `UndecidedCondition`
/// (`UnboundResultVariables`) diagnostic, which the bridge maps to `BackendLimit`. Every
/// baseline state slot and pattern slot is therefore Unknown and the campaign is refused,
/// in both profiles, for every state; in `run` and `pass` the step that binds the partial
/// call also leaves the remainder `not ceil(fres(3))`.
#[test]
fn audit_vi_unbound_result_equation_is_not_killed() {
    with_stack(|| {
        let fixture = Unbound::new();
        let baseline = fixture.validator.baseline();
        let patch = Patch::new(vec![
            replaced(
                baseline,
                "UNBOUND.fres",
                &[0, 1],
                term(baseline, "UNBOUND.fres", &[1, 1]),
            ),
            replaced(baseline, "UNBOUND.fres", &[1], ei_bool(true)),
        ])
        .expect("patch");
        let states = unbound_states("fres", "runRes", 3);
        let expected = states
            .iter()
            .flat_map(|(id, _)| [(*id, "whole", REFUSED), (*id, "bind", REFUSED)])
            .collect::<Vec<_>>();
        unbound_audit("unbound-result", &patch, "UNBOUND.fres", &states, &expected);
    });
}

/// AT12 (b), requires-only variable: `freq(X) => 1 requires Z >Int X` against `freq(X) => 1`.
/// kompile accepts the rule. Read as an axiom closed over `Z` the equation makes `freq(3) = 1`,
/// but for a ground argument the condition is contingent, so k-rust keeps the call without a
/// diagnostic (k-rust `simplify.rs:1171-1184, 1240-1242, 1264-1271`). Where a rule binds the
/// call (`run`, `pass`) the step also leaves the remainder `not ceil(freq(3))`, whose
/// feasibility is Unknown, so the baseline is refused. Where no rule touches it (`stuck`,
/// `bare`), the baseline leaf is the ground `done(freq(3))` (or `freq(3)`), stuck, with no
/// predicate, which the bridge previously took as a decided terminal; the mutant's leaf is `done(1)`
/// (`1`), so the final-state slot was Distinguish and the mutant Killed, in both profiles and
/// both schedules (TB-01, TV01-NEEDED; K-TERMINAL-CONSTRUCTOR). TV-01 makes those
/// terminals incomplete (`SolverUnknown`), so both slots are Unknown and refused.
/// The binding slot moves from Agree to Unknown because even an event-free terminal
/// must be definition-independent. Every state is now refused in both profiles and schedules.
#[test]
fn audit_vi_unbound_requires_only_equation_is_not_killed() {
    with_stack(|| {
        let fixture = Unbound::new();
        let baseline = fixture.validator.baseline();
        let patch = Patch::new(vec![replaced(
            baseline,
            "UNBOUND.freq",
            &[1],
            ei_bool(true),
        )])
        .expect("patch");
        let states = unbound_states("freq", "runReq", 3);

        let expected = [
            ("run", "whole", REFUSED),
            ("run", "bind", REFUSED),
            ("pass", "whole", REFUSED),
            ("pass", "bind", REFUSED),
            ("stuck", "whole", REFUSED),
            ("stuck", "bind", REFUSED),
            ("bare", "whole", REFUSED),
            ("bare", "bind", REFUSED),
            ("sym-run", "whole", REFUSED),
            ("sym-run", "bind", REFUSED),
            ("sym-stuck", "whole", REFUSED),
            ("sym-stuck", "bind", REFUSED),
        ];
        unbound_audit("requires-only", &patch, "UNBOUND.freq", &states, &expected);
    });
}

/// AT12 (c), K-TERMINAL-CONSTRUCTOR: `part` is a partial function with the one equation
/// `part(0) => 7`; the mutant adds `part(1) => 7`. The two definitions agree on every input the
/// baseline defines, and the baseline leaves `part(1)` unspecified, so a baseline model with
/// `part(1) = 7` exists and no test can show a difference. The rows are as for (b): `run` and
/// `pass` are refused (remainder `not ceil(part(1))`), symbolic states are refused, and `stuck`
/// and `bare` keep the ground call `done(part(1))` against the mutant's `done(7)`, which was
/// Distinguish and Killed in both profiles and both schedules (TB-01, TV01-NEEDED).
/// TV-01 makes the kept call an incomplete terminal, so the whole slot moves to Unknown,
/// and the binding slot moves from Agree to Unknown; every row is refused in both profiles
/// and schedules, as in (b).
#[test]
fn audit_vi_unbound_partial_function_is_not_killed() {
    with_stack(|| {
        let fixture = Unbound::new();
        let baseline = fixture.validator.baseline();
        let mut added = unlabelled_copy(baseline, "UNBOUND.part");
        if let k_rust::definition::Sentence::Rule { body, .. } = &mut added {
            *body = Term::Rewrite {
                left: Box::new(Term::apply("part", vec![int_token(1)])),
                right: Box::new(term(baseline, "UNBOUND.part", &[0, 1])),
            };
        }
        let patch = Patch::new(vec![Edit::InsertSentence {
            position: InsertPosition::After(support::rule(baseline, "UNBOUND.part")),
            ordinal: 0,
            sentence: added,
        }])
        .expect("patch");
        let states = unbound_states("part", "runPart", 1);

        let expected = [
            ("run", "whole", REFUSED),
            ("run", "bind", REFUSED),
            ("pass", "whole", REFUSED),
            ("pass", "bind", REFUSED),
            ("stuck", "whole", REFUSED),
            ("stuck", "bind", REFUSED),
            ("bare", "whole", REFUSED),
            ("bare", "bind", REFUSED),
            ("sym-run", "whole", REFUSED),
            ("sym-run", "bind", REFUSED),
            ("sym-stuck", "whole", REFUSED),
            ("sym-stuck", "bind", REFUSED),
        ];
        unbound_audit(
            "partial-equation",
            &patch,
            "UNBOUND.part",
            &states,
            &expected,
        );
    });
}

// ---------------------------------------------------------------- TV-01 review 2: kept calls in the mutant

/// `unbound.k (TV01TERMINAL)` with one `finish` declaration from `mk` to `done(V)`.
struct Tv01Terminal {
    validator: NativeValidator,
    observation: Vec<StepEventSpec>,
    vocabulary: EventVocabulary,
}

impl Tv01Terminal {
    fn new() -> Self {
        let validator = NativeValidator::bind(
            support::load_path(
                &std::path::Path::new(support::DIR).join("unbound.k"),
                "TV01TERMINAL",
            ),
            CompileOptions::default(),
        );
        let observation = vec![StepEventSpec {
            constructor: "finish".into(),
            pre: support::k_config(app("mk", vec![]), "SortProg", "R", "C"),
            post: Some(support::k_config(
                app("done", vec![support::var("V", "SortVal")]),
                "SortProg",
                "R",
                "C2",
            )),
            payload: vec!["V".into()],
        }];
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        Self {
            validator,
            observation,
            vocabulary,
        }
    }
}

/// `Normal` for a terminal that holds `done`, `Stuck` otherwise: a terminal-class oracle that
/// tells a stuck `check(part(0))` from `done(7)`.
fn tv01_classify(term: &Pattern) -> ExecutionTerminalKind {
    let mut done = false;
    k_rust::kore::walk::for_each_post_order(term, |node| {
        if let Pattern::Application { symbol, .. } = node {
            done |= symbol.name == "Lbldone";
        }
    });
    if done {
        ExecutionTerminalKind::Normal
    } else {
        ExecutionTerminalKind::Stuck
    }
}

fn tv01_int_val(value: Pattern) -> Pattern {
    k_rust::kompile::initial_configuration::kore_application(
        "inj",
        vec![kore_sort("SortInt"), kore_sort("SortVal")],
        vec![value],
    )
}

/// The review's initial states, by id. `argument` is the call's argument (`0`, or the `Int`
/// variable `N` for the `sym-*` states).
fn tv01_states() -> Vec<(&'static str, Pattern)> {
    let part = |argument: Pattern| app("part", vec![argument]);
    let zero = || support::int(0);
    let n = || support::var("N", "SortInt");
    let program = |program: Pattern| support::initial_state(program, "SortProg");
    let parsed = |kore: &str| {
        program(k_rust::kore::parser::parse_pattern(kore).expect("the review program parses"))
    };
    const PART0: &str = r#"inj{SortInt{}, SortKItem{}}(Lblpart{}(\dv{SortInt{}}("0")))"#;
    vec![
        (
            "inj",
            program(app("done", vec![tv01_int_val(part(zero()))])),
        ),
        (
            "ctor",
            program(app("done", vec![app("wrap", vec![part(zero())])])),
        ),
        ("code", program(app("code", vec![part(zero())]))),
        (
            "list",
            parsed(&format!("Lblhold{{}}(LblListItem{{}}({PART0}))")),
        ),
        (
            "map",
            parsed(&format!(
                r#"Lblkeep{{}}(Lbl'UndsPipe'-'-GT-Unds'{{}}(inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("1")), {PART0}))"#
            )),
        ),
        ("class", program(app("check", vec![part(zero())]))),
        ("owise-rule", program(app("sel", vec![part(zero())]))),
        (
            "owise-fn",
            program(app(
                "done",
                vec![tv01_int_val(app("fsel", vec![part(zero())]))],
            )),
        ),
        ("mk", program(app("mk", vec![]))),
        (
            "sym-inj",
            program(app("done", vec![tv01_int_val(part(n()))])),
        ),
        ("sym-class", program(app("check", vec![part(n())]))),
        ("sym-owise", program(app("sel", vec![part(n())]))),
    ]
}

/// One review campaign's result: refused, or each test's run (as printed) and the status.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Tv01Audit {
    Refused(CampaignFailureKind),
    Ran(Vec<String>, MutantStatus),
}

/// Runs each (state, oracle) row as its own one-test campaign in Full and FirstKill, prints
/// the measured result, and returns it. The oracles: `whole` (final state), `path` (the
/// argument of the top program constructor), `exit` (terminal class through `tv01_classify`),
/// `code` (terminal class and the `Int` under `code`), `bind` (the value `finish` binds).
fn tv01_audit(
    label: &str,
    patch: &Patch,
    rows: &[(&str, &str)],
) -> Vec<((String, String, ScheduleMode), Tv01Audit)> {
    let fixture = Tv01Terminal::new();
    let generation = fixed(
        fixture.validator.baseline(),
        &[("TV01TERMINAL.part", &[0])],
        label,
        patch,
    );
    let state_oracle = |projection| {
        OracleDeclaration::new(CrashPolicy::CompareIdentity, Projection::State(projection))
            .expect("oracle")
    };
    let oracle = |name: &str| match name {
        "whole" => whole_term(),
        "path" => state_oracle(StateProjection::TermPaths(vec![vec![0, 0, 0, 0, 0]])),
        "exit" => state_oracle(StateProjection::ExitStop {
            exit_code_cell: None,
        }),
        "code" => state_oracle(StateProjection::ExitStop {
            exit_code_cell: Some("Lblcode".into()),
        }),
        "bind" => binds(&fixture.vocabulary, "finish", 0, "V", "SortVal", true),
        _ => unreachable!("{name}"),
    };
    let states = tv01_states();
    let mut measured = Vec::new();
    for (id, oracle_name) in rows {
        let state = &states
            .iter()
            .find(|(state_id, _)| state_id == id)
            .expect("state")
            .1;
        let tests = [case(id, state.clone(), &[oracle(oracle_name)])];
        let campaign = Campaign {
            validator: &fixture.validator,
            module: "TV01TERMINAL",
            observation: &fixture.observation,
            classify: &tv01_classify,
            tests: &tests,
            budget: BUDGET,
        };
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let actual = match run_campaign(&campaign, &generation, mode) {
                Ok(run) => {
                    let [mutant] = run.mutants.as_slice() else {
                        panic!("one mutant")
                    };
                    if mutant.report.status != MutantStatus::Killed {
                        assert!(mutant.report.killing_test_ids.is_empty());
                    }
                    Tv01Audit::Ran(
                        mutant
                            .plan
                            .tests
                            .iter()
                            .map(|test| format!("{:?}", test.run))
                            .collect(),
                        mutant.report.status,
                    )
                }
                Err(error) => Tv01Audit::Refused(error.kind()),
            };
            eprintln!("TV01-REVIEW {label} {id} {oracle_name} {mode:?}: {actual:?}");
            measured.push((((*id).to_owned(), (*oracle_name).to_owned(), mode), actual));
        }
    }
    measured
}

const TV01_ROWS: [(&str, &str); 25] = [
    ("inj", "whole"),
    ("inj", "path"),
    ("inj", "exit"),
    ("ctor", "whole"),
    ("ctor", "path"),
    ("code", "whole"),
    ("code", "code"),
    ("list", "whole"),
    ("list", "path"),
    ("map", "whole"),
    ("class", "whole"),
    ("class", "exit"),
    ("owise-rule", "whole"),
    ("owise-rule", "exit"),
    ("owise-fn", "whole"),
    ("owise-fn", "path"),
    ("mk", "whole"),
    ("mk", "bind"),
    ("mk", "exit"),
    ("sym-inj", "whole"),
    ("sym-inj", "exit"),
    ("sym-class", "whole"),
    ("sym-class", "exit"),
    ("sym-owise", "whole"),
    ("sym-owise", "exit"),
];

/// TV-01 review 2: the mutant keeps a call the baseline evaluates. `part(0) => 7` gets
/// `requires false`, so the mutant leaves `part(0)` unevaluated wherever the baseline has `7`.
/// A model of the mutant with `part(0) = 7` behaves exactly as the baseline, so no row may be
/// Killed in either profile or schedule: the call under an injection, a free constructor, the
/// exit-code constructor, a list and a map; the call deciding whether `check(7)` applies
/// (stuck against `done`, through the terminal class); the call against an owise rule and an
/// owise equation (an owise that fired past the undecided match would give `done(0)`, a
/// constructor term, against the baseline's `done(7)`); a rule that writes the call, with its
/// binding; the same with a symbolic argument. Without the independence check the ground
/// `inj`, `ctor` and `owise-fn` mutant leaves are complete terminals holding the call (kink-native
/// `trust_base.rs` `review_kept_calls_are_terminals_only_for_a_lying_caller`), against the
/// baseline's `done(7)`: Distinguish.
///
/// Measured in both profiles and both schedules: every ground row except `list` and `map` runs
/// `[[Unknown]]`, Unknown; `list`, `map` and every `sym-*` row are refused
/// (`BaselineOracleFailed`: a collection is not a free constructor, and a symbolic terminal is
/// not a value). The control below kills.
#[test]
fn audit_vi_tv01_review_mutant_kept_calls_are_not_killed() {
    with_stack(|| {
        let fixture = Tv01Terminal::new();
        let baseline = fixture.validator.baseline();
        let patch = Patch::new(vec![replaced(
            baseline,
            "TV01TERMINAL.part",
            &[1],
            ei_bool(false),
        )])
        .expect("patch");
        let measured = tv01_audit("tv01-disable", &patch, &TV01_ROWS);
        for ((id, oracle_name, mode), actual) in &measured {
            assert!(
                !matches!(actual, Tv01Audit::Ran(_, MutantStatus::Killed)),
                "{id} {oracle_name} {mode:?}: a kept call kills: {actual:?}"
            );
        }
        // The probe is live: the ground injection row reaches a comparison.
        assert!(
            measured
                .iter()
                .any(|((id, oracle_name, _), actual)| id == "inj"
                    && oracle_name == "whole"
                    && matches!(actual, Tv01Audit::Ran(..))),
            "the inj whole row never ran"
        );
    });
}

/// TV-01 review 2 control: the same rows against a real difference, `part(0) => 8`. The
/// ground rows whose baseline and mutant values are constructor terms must still kill, so the
/// review campaign above is not vacuous.
#[test]
fn audit_vi_tv01_review_real_difference_still_kills() {
    with_stack(|| {
        let fixture = Tv01Terminal::new();
        let baseline = fixture.validator.baseline();
        let patch = Patch::new(vec![replaced(
            baseline,
            "TV01TERMINAL.part",
            &[0, 1],
            int_token(8),
        )])
        .expect("patch");
        let measured = tv01_audit(
            "tv01-control",
            &patch,
            &[("inj", "whole"), ("ctor", "whole"), ("mk", "bind")],
        );
        for ((id, oracle_name, mode), actual) in &measured {
            if id == "inj" || id == "ctor" {
                assert!(
                    matches!(actual, Tv01Audit::Ran(_, MutantStatus::Killed)),
                    "{id} {oracle_name} {mode:?}: control does not kill: {actual:?}"
                );
            }
        }
    });
}

// ---------------------------------------------------------------- TV-01 fix 1: identity injections

/// `inj{From,To}(value)` written by a test.
fn tv01_inj(from: &str, to: &str, value: Pattern) -> Pattern {
    k_rust::kompile::initial_configuration::kore_application(
        "inj",
        vec![kore_sort(from), kore_sort(to)],
        vec![value],
    )
}

/// Runs the baseline rule `<rule>(7) => done(7)` (`check`, or `sel` with its owise rule
/// `sel(_) => done(0)`) against the mutant `<rule>(X) => done(7) requires X <op> 7` on each
/// (state, oracle) row, as its own one-test campaign in Full and FirstKill. The oracles are
/// those of `tv01_audit` plus `fire`, a step event from `check(X)` to `done(V)` binding `V`.
fn tv01_fix1_audit(
    label: &str,
    rule: &str,
    op: &str,
    rows: &[(&str, &str)],
) -> Vec<((String, String, ScheduleMode), Tv01Audit)> {
    let fixture = Tv01Terminal::new();
    let baseline = fixture.validator.baseline();
    let rule = format!("TV01TERMINAL.{rule}");
    let patch = Patch::new(vec![
        replaced(baseline, &rule, &[0, 0, 0], so_var("X", "Int")),
        replaced(
            baseline,
            &rule,
            &[1],
            Term::apply(op, vec![so_var("X", "Int"), int_token(7)]),
        ),
    ])
    .expect("patch");
    let generation = fixed(baseline, &[(rule.as_str(), &[0])], label, &patch);
    let observation = vec![StepEventSpec {
        constructor: "fire".into(),
        pre: support::k_config(
            app("check", vec![support::var("X", "SortInt")]),
            "SortProg",
            "R",
            "C",
        ),
        post: Some(support::k_config(
            app("done", vec![support::var("V", "SortVal")]),
            "SortProg",
            "R",
            "C2",
        )),
        payload: vec!["V".into()],
    }];
    let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
    let state_oracle = |projection| {
        OracleDeclaration::new(CrashPolicy::CompareIdentity, Projection::State(projection))
            .expect("oracle")
    };
    let oracle = |name: &str| match name {
        "whole" => whole_term(),
        "path" => state_oracle(StateProjection::TermPaths(vec![vec![0, 0, 0, 0, 0]])),
        "exit" => state_oracle(StateProjection::ExitStop {
            exit_code_cell: None,
        }),
        "fire" => binds(&vocabulary, "fire", 0, "V", "SortVal", false),
        "fire-bind" => binds(&vocabulary, "fire", 0, "V", "SortVal", true),
        _ => unreachable!("{name}"),
    };
    let program = |program: Pattern| support::initial_state(program, "SortProg");
    let states = [
        (
            "inj-same",
            program(app(
                "check",
                vec![tv01_inj("SortInt", "SortInt", support::int(7))],
            )),
        ),
        (
            "inj-same-done",
            program(app(
                "done",
                vec![tv01_inj(
                    "SortInt",
                    "SortVal",
                    tv01_inj("SortInt", "SortInt", support::int(7)),
                )],
            )),
        ),
        ("plain7", program(app("check", vec![support::int(7)]))),
        ("plain3", program(app("check", vec![support::int(3)]))),
        (
            "sel-inj-same",
            program(app(
                "sel",
                vec![tv01_inj("SortInt", "SortInt", support::int(7))],
            )),
        ),
        ("sel-plain7", program(app("sel", vec![support::int(7)]))),
        ("sel-plain3", program(app("sel", vec![support::int(3)]))),
    ];
    let mut measured = Vec::new();
    for (id, oracle_name) in rows {
        let state = &states
            .iter()
            .find(|(state_id, _)| state_id == id)
            .expect("state")
            .1;
        let tests = [case(id, state.clone(), &[oracle(oracle_name)])];
        let campaign = Campaign {
            validator: &fixture.validator,
            module: "TV01TERMINAL",
            observation: &observation,
            classify: &tv01_classify,
            tests: &tests,
            budget: BUDGET,
        };
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let actual = match run_campaign(&campaign, &generation, mode) {
                Ok(run) => {
                    let [mutant] = run.mutants.as_slice() else {
                        panic!("one mutant")
                    };
                    if mutant.report.status != MutantStatus::Killed {
                        assert!(mutant.report.killing_test_ids.is_empty());
                    }
                    Tv01Audit::Ran(
                        mutant
                            .plan
                            .tests
                            .iter()
                            .map(|test| format!("{:?}", test.run))
                            .collect(),
                        mutant.report.status,
                    )
                }
                Err(error) => Tv01Audit::Refused(error.kind()),
            };
            eprintln!("TV01-FIX1 {label} {id} {oracle_name} {mode:?}: {actual:?}");
            measured.push((((*id).to_owned(), (*oracle_name).to_owned(), mode), actual));
        }
    }
    measured
}

const TV01_FIX1_ROWS: [(&str, &str); 13] = [
    ("inj-same", "whole"),
    ("inj-same", "path"),
    ("inj-same", "exit"),
    ("inj-same", "fire"),
    ("inj-same", "fire-bind"),
    ("inj-same-done", "whole"),
    ("inj-same-done", "path"),
    ("plain7", "whole"),
    ("plain7", "exit"),
    ("plain7", "fire"),
    ("plain3", "whole"),
    ("plain3", "exit"),
    ("plain3", "fire"),
];

/// TV-01 fix 1 (review R1-F1): `check(X) => done(7) requires X ==K 7` is the baseline's
/// `check(7) => done(7)` on every `Int`. A test-written identity injection
/// `check(inj{SortInt,SortInt}(7))` is not k-rust normal form (k-rust never builds `inj{S,S}`),
/// and the baseline matcher leaves it stuck while the mutant's `==K` reaches `done(7)`. Before
/// the fix the stuck baseline term was a decided terminal (the decider admitted every `inj`):
/// Compared([Distinguish]), Killed, in both profiles and schedules. A terminal is a value only
/// if each injection in it is strict (proper subsort, arity 1), well sorted and not nested,
/// so no row may be Killed. The canonical tests `check(7)` and `check(3)` agree.
///
/// Measured in both profiles and both schedules: every `inj-same*` row is refused
/// (`BaselineOracleFailed`: the test input holds a non-canonical injection, and the baseline
/// side's stuck terminal is not a value); every `plain*` row runs `[[Agree]]`, Survived.
#[test]
fn audit_vi_tv01_fix1_identity_injection_is_not_killed() {
    with_stack(|| {
        let measured = tv01_fix1_audit("tv01-fix1-eqk", "check", "_==K_", &TV01_FIX1_ROWS);
        for ((id, oracle_name, mode), actual) in &measured {
            assert!(
                !matches!(actual, Tv01Audit::Ran(_, MutantStatus::Killed)),
                "{id} {oracle_name} {mode:?}: an identity injection kills: {actual:?}"
            );
            let expected = if id.starts_with("inj-same") {
                Tv01Audit::Refused(CampaignFailureKind::BaselineOracleFailed)
            } else {
                Tv01Audit::Ran(vec!["Compared([Agree])".into()], MutantStatus::Survived)
            };
            assert_eq!(actual, &expected, "{id} {oracle_name} {mode:?}");
        }
    });
}

/// TV-01 fix 1: the same construction against an owise rule, which the terminal rule alone
/// does not cover. On `sel(inj{SortInt,SortInt}(7))` the baseline's `sel(7)` does not match the
/// non-canonical argument, so its owise rule gives the constructor term `done(0)`, while the
/// mutant `sel(X) => done(7) requires X ==K 7` gives `done(7)`: two decided terminals that
/// differ although the definitions agree on every `Int` (`inj{S,S}(x) = x`). Only refusing the
/// non-canonical test input closes it. The canonical tests agree.
///
/// Measured in both profiles and both schedules: `sel-inj-same` is refused
/// (`BaselineOracleFailed`); `sel-plain7` and `sel-plain3` run `[[Agree]]`, Survived.
#[test]
fn audit_vi_tv01_fix1_identity_injection_against_owise_is_not_killed() {
    with_stack(|| {
        let measured = tv01_fix1_audit(
            "tv01-fix1-sel",
            "sel",
            "_==K_",
            &[
                ("sel-inj-same", "whole"),
                ("sel-inj-same", "exit"),
                ("sel-plain7", "whole"),
                ("sel-plain3", "whole"),
            ],
        );
        for ((id, oracle_name, mode), actual) in &measured {
            assert!(
                !matches!(actual, Tv01Audit::Ran(_, MutantStatus::Killed)),
                "{id} {oracle_name} {mode:?}: an identity injection kills: {actual:?}"
            );
            let expected = if id == "sel-inj-same" {
                Tv01Audit::Refused(CampaignFailureKind::BaselineOracleFailed)
            } else {
                Tv01Audit::Ran(vec!["Compared([Agree])".into()], MutantStatus::Survived)
            };
            assert_eq!(actual, &expected, "{id} {oracle_name} {mode:?}");
        }
    });
}

/// TV-01 fix 1 control: with `requires X =/=K 7` the mutant really differs on `check(7)`, so
/// the canonical rows still kill and the construction above is live.
#[test]
fn audit_vi_tv01_fix1_real_difference_still_kills() {
    with_stack(|| {
        let mut measured = tv01_fix1_audit(
            "tv01-fix1-control",
            "check",
            "_=/=K_",
            &[("plain7", "whole"), ("plain7", "exit")],
        );
        measured.extend(tv01_fix1_audit(
            "tv01-fix1-sel-control",
            "sel",
            "_=/=K_",
            &[("sel-plain7", "whole"), ("sel-plain3", "whole")],
        ));
        for ((id, oracle_name, mode), actual) in &measured {
            assert!(
                matches!(actual, Tv01Audit::Ran(_, MutantStatus::Killed)),
                "{id} {oracle_name} {mode:?}: control does not kill: {actual:?}"
            );
        }
    });
}

// ---------------------------------------------------------------- State-observation coverage and granularity audits

fn so_var(name: &str, sort: &str) -> Term {
    Term::Variable {
        name: name.into(),
        sort: Some(Sort::new(sort)),
    }
}

fn so_guarded_tests(guarded: &Guarded) -> Vec<TestCase> {
    vec![
        case(
            "ground-zero",
            int_program(0, 5, support::int(0), 7),
            &guarded.tests[1].oracles,
        ),
        case(
            "ground-one",
            int_program(1, 5, support::int(1), 7),
            &guarded.tests[1].oracles,
        ),
    ]
}

/// J1: AS5 plus an unlabelled priority-40 write copy 5 -> 6 (a stutter through a write pre-state).
#[test]
fn audit_so_j1_write_stutter() {
    with_stack(|| {
        for whole in [true, false] {
            let mut guarded = Guarded::new();
            guarded.observation = step_support::guardedmem(whole);
            let baseline = guarded.validator.baseline();
            let write = support::rule(baseline, "GUARDEDMEM.write");
            let tests = so_guarded_tests(&guarded);
            let left = term(baseline, "GUARDEDMEM.write", &[0, 0]);
            let v = term(baseline, "GUARDEDMEM.write", &[0, 0, 0, 1]);
            let right = ei_substitute(
                &left,
                &v,
                &Term::apply("_+Int_", vec![v.clone(), int_token(1)]),
            );
            let mut bump = unlabelled_copy(baseline, "GUARDEDMEM.write");
            if let k_rust::definition::Sentence::Rule { body, requires, .. } = &mut bump {
                *body = Term::Rewrite {
                    left: Box::new(left),
                    right: Box::new(right),
                };
                *requires = Term::apply("_==Int_", vec![v, int_token(5)]);
            }
            bump.attributes_mut().set(
                AttributeKey::Priority,
                serde_json::Value::String("40".into()),
            );
            let mut edits = ei_guard_split(baseline);
            edits.push(Edit::InsertSentence {
                position: InsertPosition::After(write),
                ordinal: 1,
                sentence: bump,
            });
            let patch = Patch::new(edits).expect("patch");
            let generation = fixed(baseline, &[("GUARDEDMEM.write", &[1])], "j1", &patch);
            let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full)
                .expect("campaign");
            assert_survived(&run, &[vec![A, A], vec![A, A]]);
        }
    });
}

/// Co-located: the AS5 zero copy rewrites write into a load of the written value.
#[test]
fn audit_so_colocated() {
    with_stack(|| {
        for whole in [true, false] {
            let mut guarded = Guarded::new();
            guarded.observation = step_support::guardedmem(whole);
            let baseline = guarded.validator.baseline();
            let tests = so_guarded_tests(&guarded);
            let mut edits = ei_guard_split(baseline);
            let Edit::InsertSentence { sentence, .. } = &mut edits[1] else {
                panic!("insert")
            };
            if let k_rust::definition::Sentence::Rule { body, .. } = sentence {
                let field = |path: &[u32]| term(baseline, "GUARDEDMEM.write", path);
                *body = Term::Rewrite {
                    left: Box::new(field(&[0, 0])),
                    right: Box::new(Term::apply(
                        "seq",
                        vec![
                            Term::apply("load", vec![field(&[0, 0, 0, 0]), field(&[0, 0, 0, 1])]),
                            field(&[0, 1]),
                        ],
                    )),
                };
            }
            let patch = Patch::new(edits).expect("patch");
            let generation = fixed(baseline, &[("GUARDEDMEM.write", &[1])], "colocated", &patch);
            let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full)
                .expect("campaign");
            assert_eq!(
                outcomes(&run),
                if whole {
                    vec![vec![A, D], vec![A, A]]
                } else {
                    vec![vec![A, A]; 2]
                }
            );
            assert_eq!(
                run.mutants[0].report.status,
                if whole {
                    MutantStatus::Killed
                } else {
                    MutantStatus::Survived
                }
            );
            assert_eq!(
                run.mutants[0].report.killing_test_ids,
                if whole { vec!["ground-zero"] } else { vec![] }
            );
        }
    });
}

/// Fused bump: the zero copy consumes the write and bumps the following load in one step.
#[test]
fn audit_so_fused_bump() {
    with_stack(|| {
        for whole in [true, false] {
            let mut guarded = Guarded::new();
            guarded.observation = step_support::guardedmem(whole);
            let baseline = guarded.validator.baseline();
            let tests = so_guarded_tests(&guarded);
            let mut edits = ei_guard_split(baseline);
            let Edit::InsertSentence { sentence, .. } = &mut edits[1] else {
                panic!("insert")
            };
            if let k_rust::definition::Sentence::Rule { body, .. } = sentence {
                let field = |path: &[u32]| term(baseline, "GUARDEDMEM.write", path);
                let load = |value: Term| {
                    Term::apply(
                        "load",
                        vec![Term::apply("addr", vec![so_var("FB", "Int")]), value],
                    )
                };
                *body = Term::Rewrite {
                    left: Box::new(Term::apply(
                        "seq",
                        vec![
                            field(&[0, 0, 0]),
                            Term::apply(
                                "seq",
                                vec![load(so_var("FW", "Int")), so_var("FQ", "Prog")],
                            ),
                        ],
                    )),
                    right: Box::new(Term::apply(
                        "seq",
                        vec![
                            load(Term::apply(
                                "_+Int_",
                                vec![so_var("FW", "Int"), int_token(1)],
                            )),
                            so_var("FQ", "Prog"),
                        ],
                    )),
                };
            }
            let patch = Patch::new(edits).expect("patch");
            let generation = fixed(
                baseline,
                &[("GUARDEDMEM.write", &[1])],
                "fused-bump",
                &patch,
            );
            let run = run_campaign(&guarded.campaign(&tests), &generation, ScheduleMode::Full)
                .expect("campaign");
            assert_eq!(
                outcomes(&run),
                if whole {
                    vec![vec![A, D], vec![A, A]]
                } else {
                    vec![vec![A, A]; 2]
                }
            );
            assert_eq!(
                run.mutants[0].report.status,
                if whole {
                    MutantStatus::Killed
                } else {
                    MutantStatus::Survived
                }
            );
            assert_eq!(
                run.mutants[0].report.killing_test_ids,
                if whole { vec!["ground-zero"] } else { vec![] }
            );
        }
    });
}

/// Fork detour: an unobserved priority-40 copy of symmem's write goes to fork(P, P).
#[test]
fn audit_so_fork_detour() {
    with_stack(|| {
        for whole in [true, false] {
            let mut fixture = Symmem::new();
            fixture.observation = step_support::symmem(whole);
            let baseline = fixture.validator.baseline();
            let write = support::rule(baseline, "SYMMEM.write");
            let left = term(baseline, "SYMMEM.write", &[0, 0]);
            let p = term(baseline, "SYMMEM.write", &[0, 1]);
            let mut shadow = unlabelled_copy(baseline, "SYMMEM.write");
            if let k_rust::definition::Sentence::Rule { body, .. } = &mut shadow {
                *body = Term::Rewrite {
                    left: Box::new(left),
                    right: Box::new(Term::apply("fork", vec![p.clone(), p])),
                };
            }
            shadow.attributes_mut().set(
                AttributeKey::Priority,
                serde_json::Value::String("40".into()),
            );
            let patch = Patch::new(vec![Edit::InsertSentence {
                position: InsertPosition::After(write),
                ordinal: 0,
                sentence: shadow,
            }])
            .expect("patch");
            let generation = fixed(baseline, &[("SYMMEM.write", &[0])], "forkdetour", &patch);
            let run = run_campaign(
                &fixture.campaign(&fixture.tests),
                &generation,
                ScheduleMode::Full,
            )
            .expect("campaign");
            assert_eq!(
                outcomes(&run),
                if whole {
                    vec![
                        vec![A, D, D, A],
                        vec![A, D, D, A],
                        vec![A, D, D, A],
                        vec![A, A, A, A],
                    ]
                } else {
                    vec![vec![A; 4]; 4]
                }
            );
            assert_eq!(
                run.mutants[0].report.status,
                if whole {
                    MutantStatus::Killed
                } else {
                    MutantStatus::Survived
                }
            );
            let kills = if whole {
                vec!["ground-shared", "sym-shared", "sym-distinct"]
            } else {
                vec![]
            };
            assert_eq!(run.mutants[0].report.killing_test_ids, kills);
        }
    });
}

/// Release after load: `SYMMEM.load` continues with `free(A)`.
#[test]
fn audit_so_release_after_load() {
    with_stack(|| {
        for whole in [true, false] {
            let mut fixture = Symmem::new();
            fixture.observation = step_support::symmem(whole);
            let baseline = fixture.validator.baseline();
            let address = term(baseline, "SYMMEM.load", &[0, 0, 0, 0]);
            let p = term(baseline, "SYMMEM.load", &[0, 1]);
            let patch = Patch::new(vec![replaced(
                baseline,
                "SYMMEM.load",
                &[0, 1],
                Term::apply("seq", vec![Term::apply("free", vec![address]), p]),
            )])
            .expect("patch");
            let generation = fixed(
                baseline,
                &[("SYMMEM.load", &[0, 1])],
                "releaseafterload",
                &patch,
            );
            let run = run_campaign(
                &fixture.campaign(&fixture.tests),
                &generation,
                ScheduleMode::Full,
            )
            .expect("campaign");
            assert_eq!(
                outcomes(&run),
                if whole {
                    vec![
                        vec![A, D, D, A],
                        vec![A, D, D, A],
                        vec![A, D, D, A],
                        vec![A, A, A, A],
                    ]
                } else {
                    vec![vec![A, A, A, D]; 4]
                }
            );
            assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
            let kills = if whole {
                vec!["ground-shared", "sym-shared", "sym-distinct"]
            } else {
                vec!["ground-shared", "sym-shared", "sym-distinct", "sym-clash"]
            };
            assert_eq!(run.mutants[0].report.killing_test_ids, kills);
        }
    });
}

/// K': K's write edit plus an inserted unobserved priority-40 load-then-free copy.
#[test]
fn audit_so_k_prime() {
    with_stack(|| {
        for whole in [true, false] {
            let mut fixture = Symmem::new();
            fixture.observation = step_support::symmem(whole);
            let baseline = fixture.validator.baseline();
            let address = term(baseline, "SYMMEM.write", &[0, 0, 0, 0]);
            let continuation = term(baseline, "SYMMEM.write", &[0, 1]);
            let write_edit = replaced(
                baseline,
                "SYMMEM.write",
                &[0, 1],
                Term::apply(
                    "seq",
                    vec![Term::apply("free", vec![address]), continuation],
                ),
            );
            let mut copy = unlabelled_copy(baseline, "SYMMEM.load");
            if let k_rust::definition::Sentence::Rule { body, .. } = &mut copy {
                let field = |path: &[u32]| term(baseline, "SYMMEM.load", path);
                *body = Term::Rewrite {
                    left: Box::new(field(&[0, 0])),
                    right: Box::new(Term::apply(
                        "seq",
                        vec![
                            Term::apply("free", vec![field(&[0, 0, 0, 0])]),
                            field(&[0, 1]),
                        ],
                    )),
                };
            }
            copy.attributes_mut().set(
                AttributeKey::Priority,
                serde_json::Value::String("40".into()),
            );
            let patch = Patch::new(vec![
                write_edit,
                Edit::InsertSentence {
                    position: InsertPosition::After(support::rule(baseline, "SYMMEM.load")),
                    ordinal: 0,
                    sentence: copy,
                },
            ])
            .expect("patch");
            let generation = fixed(
                baseline,
                &[("SYMMEM.write", &[0, 1]), ("SYMMEM.load", &[0])],
                "k-prime",
                &patch,
            );
            let run = run_campaign(
                &fixture.campaign(&fixture.tests),
                &generation,
                ScheduleMode::Full,
            )
            .expect("campaign");
            assert_eq!(
                outcomes(&run),
                if whole {
                    vec![
                        vec![A, D, D, A],
                        vec![A, D, D, A],
                        vec![A, D, D, A],
                        vec![A, A, A, A],
                    ]
                } else {
                    vec![
                        vec![A, D, A, D],
                        vec![A, D, A, D],
                        vec![A, D, A, D],
                        vec![A, A, A, D],
                    ]
                }
            );
            assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
            let kills = if whole {
                vec!["ground-shared", "sym-shared", "sym-distinct"]
            } else {
                vec!["ground-shared", "sym-shared", "sym-distinct", "sym-clash"]
            };
            assert_eq!(run.mutants[0].report.killing_test_ids, kills);
            let mut campaign = fixture.campaign(&fixture.tests[..1]);
            campaign.budget.max_depth = Some(4);
            let bounded =
                run_campaign(&campaign, &generation, ScheduleMode::Full).expect("bounded campaign");
            assert_eq!(
                outcomes(&bounded),
                vec![if whole { vec![U; 4] } else { vec![U, U, A, D] }]
            );
            assert_eq!(
                bounded.mutants[0].report.status,
                if whole {
                    MutantStatus::Unknown
                } else {
                    MutantStatus::Killed
                }
            );
            let original = coupled(baseline, false);
            let original_run = run_campaign(
                &fixture.campaign(&fixture.tests),
                &original,
                ScheduleMode::Full,
            )
            .expect("K campaign");
            assert_eq!(outcomes(&run), outcomes(&original_run));
            let compiled = fixture.validator.compile_baseline().expect("baseline");
            let k = fixture
                .validator
                .validate(&original.candidates()[0].patch)
                .expect("K");
            let k_prime = fixture.validator.validate(&patch).expect("K prime");
            for test in &fixture.tests {
                assert_eq!(
                    pattern_paths(
                        &compiled,
                        &k,
                        "SYMMEM",
                        &test.initial_state,
                        &fixture.observation,
                    ),
                    pattern_paths(
                        &compiled,
                        &k_prime,
                        "SYMMEM",
                        &test.initial_state,
                        &fixture.observation,
                    )
                );
            }
        }
    });
}

/// G': the right-hand sides of load and loadFault exchanged (G's rewrite relation).
#[test]
fn audit_so_g_prime() {
    with_stack(|| {
        for whole in [true, false] {
            let mut fixture = Guarded::new();
            fixture.observation = step_support::guardedmem(whole);
            let baseline = fixture.validator.baseline();
            let load_body = term(baseline, "GUARDEDMEM.load", &[0]);
            let fault_body = term(baseline, "GUARDEDMEM.loadFault", &[0]);
            let patch = Patch::new(vec![
                replaced(baseline, "GUARDEDMEM.load", &[0], fault_body),
                replaced(baseline, "GUARDEDMEM.loadFault", &[0], load_body),
            ])
            .expect("patch");
            let generation = fixed(
                baseline,
                &[("GUARDEDMEM.load", &[0]), ("GUARDEDMEM.loadFault", &[0])],
                "g-prime",
                &patch,
            );
            let full = run_campaign(
                &fixture.campaign(&fixture.tests),
                &generation,
                ScheduleMode::Full,
            );
            if cfg!(feature = "z3") {
                let full = full.expect("Z3 admits symbolic baseline");
                assert_eq!(
                    outcomes(&full),
                    if whole {
                        vec![vec![A, D], vec![D, D]]
                    } else {
                        vec![vec![A, A], vec![D, A]]
                    }
                );
                assert_eq!(full.mutants[0].report.status, MutantStatus::Killed);
                assert_eq!(
                    full.mutants[0].report.killing_test_ids,
                    if whole {
                        vec!["sym-guarded", "ground-guarded"]
                    } else {
                        vec!["ground-guarded"]
                    }
                );
            } else {
                assert_eq!(
                    full.expect_err("symbolic baseline refused").kind(),
                    CampaignFailureKind::BaselineOracleFailed
                );
            }
            let ground = run_campaign(
                &fixture.campaign(&fixture.tests[1..]),
                &generation,
                ScheduleMode::Full,
            )
            .expect("ground");
            assert_eq!(
                outcomes(&ground),
                vec![if whole { vec![D, D] } else { vec![D, A] }]
            );
            assert_eq!(ground.mutants[0].report.status, MutantStatus::Killed);
            assert_eq!(
                ground.mutants[0].report.killing_test_ids,
                ["ground-guarded"]
            );
            let original = inverted_load_sign(baseline);
            let compiled = fixture.validator.compile_baseline().expect("baseline");
            let g = fixture
                .validator
                .validate(&original.candidates()[0].patch)
                .expect("G");
            let g_prime = fixture.validator.validate(&patch).expect("G prime");
            let tests = if cfg!(feature = "z3") {
                &fixture.tests[..]
            } else {
                &fixture.tests[1..]
            };
            for test in tests {
                assert_eq!(
                    pattern_paths(
                        &compiled,
                        &g,
                        "GUARDEDMEM",
                        &test.initial_state,
                        &fixture.observation,
                    ),
                    pattern_paths(
                        &compiled,
                        &g_prime,
                        "GUARDEDMEM",
                        &test.initial_state,
                        &fixture.observation,
                    )
                );
            }
        }
    });
}

/// A symmem mutant with one dead existential rule (never fires on these tests): identical
/// executions, and both sides decide alike. Before variable identity the rule's existential
/// variable switched off the initial variables for the whole pair (the pair existentials
/// flag), so the symbolic tests were `[A,U,U,A]` and the mutant Unknown; under the contract no
/// mint re-binds an initial name, the flag is gone, and they are `[A,A,A,A]`, Survived.
#[test]
fn audit_so_dead_existential_rule_is_not_killed() {
    with_stack(|| {
        for whole in [true, false] {
            let mut fixture = Symmem::new();
            fixture.observation = step_support::symmem(whole);
            let baseline = fixture.validator.baseline();
            let free = support::rule(baseline, "SYMMEM.free");
            let mut dead = unlabelled_copy(baseline, "SYMMEM.free");
            if let k_rust::definition::Sentence::Rule { body, .. } = &mut dead {
                let field = |path: &[u32]| term(baseline, "SYMMEM.free", path);
                *body = Term::Rewrite {
                    left: Box::new(field(&[0, 0])),
                    right: Box::new(Term::apply(
                        "seq",
                        vec![
                            Term::apply("write", vec![field(&[0, 0, 0, 0]), so_var("?E", "Nat")]),
                            field(&[0, 1]),
                        ],
                    )),
                };
            }
            dead.attributes_mut().set(
                AttributeKey::Priority,
                serde_json::Value::String("40".into()),
            );
            let patch = Patch::new(vec![Edit::InsertSentence {
                position: InsertPosition::After(free),
                ordinal: 0,
                sentence: dead,
            }])
            .expect("patch");
            let generation = fixed(
                baseline,
                &[("SYMMEM.free", &[0])],
                "dead-existential",
                &patch,
            );
            let run = run_campaign(
                &fixture.campaign(&fixture.tests),
                &generation,
                ScheduleMode::Full,
            )
            .expect("campaign");
            assert_eq!(
                outcomes(&run),
                vec![
                    vec![A, A, A, A],
                    vec![A, A, A, A],
                    vec![A, A, A, A],
                    vec![A, A, A, A]
                ]
            );
            assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
            let kills = Vec::<&str>::new();
            assert_eq!(run.mutants[0].report.killing_test_ids, kills);
            let compiled = fixture.validator.compile_baseline().expect("baseline");
            let mutant = fixture.validator.validate(&patch).expect("mutant");
            for test in &fixture.tests {
                assert_eq!(
                    pattern_paths(
                        &compiled,
                        &compiled,
                        "SYMMEM",
                        &test.initial_state,
                        &fixture.observation,
                    ),
                    pattern_paths(
                        &compiled,
                        &mutant,
                        "SYMMEM",
                        &test.initial_state,
                        &fixture.observation,
                    )
                );
            }
        }
    });
}

/// Both sides' traces are classified in the compiled baseline's definition and solver.
fn pattern_paths(
    baseline: &kink_native::ValidatedDefinition,
    side: &kink_native::ValidatedDefinition,
    module: &str,
    initial: &Pattern,
    specs: &[StepEventSpec],
) -> Vec<kink_pattern::PathInput> {
    use k_rust::backend::{Backend, BackendOptions};
    use kink_native::bridge::{BridgeContext, paths_from_steps};
    use kink_native::execution::{ExecutionAdapter, SolverProfile};
    use kink_native::step_events::ObservationDecider;
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .expect("side backend");
    let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute_steps(&mut backend, initial, BUDGET)
        .expect("execution")
        .expect("stepped run");
    let mut backend = Backend::new(
        &baseline.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .expect("baseline backend");
    let observation =
        StepObservation::new(&mut backend, specs.to_vec()).expect("valid declarations");
    let parsed = k_rust::kore::parser::parse_definition(&baseline.artifacts().definition_kore)
        .expect("KORE");
    let sorts = kink_pattern::SymbolSorts::from_definition(&parsed);
    backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(initial));
            Ok::<_, k_rust::backend::BackendError>(
                paths_from_steps(
                    &BridgeContext {
                        test_id: "identity",
                        classify: &normal,
                        sorts: &sorts,
                    },
                    &execution,
                    &observation,
                    &decider,
                )
                .expect("bridge")
                .paths,
            )
        })
        .expect("shared decider")
}

/// Each declaration must emit a Certain event on at least one baseline execution.
fn assert_baseline_emissions(
    validator: &NativeValidator,
    module: &str,
    specs: &[StepEventSpec],
    states: &[Pattern],
) {
    let baseline = validator.compile_baseline().expect("baseline");
    for spec in specs {
        assert!(
            states.iter().any(|state| {
                pattern_paths(
                    &baseline,
                    &baseline,
                    module,
                    state,
                    std::slice::from_ref(spec),
                )
                .iter()
                .any(|path| {
                    path.events
                        .iter()
                        .any(|event| event.presence == kink_pattern::EventPresence::Certain)
                })
            }),
            "{module} declaration {spec:?} never emits"
        );
    }
}

#[test]
fn every_fixture_declaration_emits_on_its_baseline() {
    with_stack(|| {
        for whole in [true, false] {
            let symmem = Symmem::new();
            let free = support::initial_state(
                app(
                    "seq",
                    vec![app("free", vec![addr(z())]), app("halt", vec![])],
                ),
                "SortProg",
            );
            assert_baseline_emissions(
                &symmem.validator,
                "SYMMEM",
                &step_support::symmem(whole),
                &[symmem.tests[0].initial_state.clone(), free],
            );
            let guarded = Guarded::new();
            let negative_load = ei_program(
                vec![app(
                    "loadNeg",
                    vec![addr(support::int(-1)), support::int(7)],
                )],
                app("halt", vec![]),
            );
            assert_baseline_emissions(
                &guarded.validator,
                "GUARDEDMEM",
                &step_support::guardedmem(whole),
                &[int_program(1, 5, support::int(1), 7), negative_load],
            );
            for (file, module) in [
                ("symbolic-claim-survivor.k", "SYMPARTIAL"),
                ("guardedeq.k", "GUARDEDEQ"),
                ("effectmem.k", "EFFECTMEM"),
                ("guardeddiv.k", "GUARDEDDIV"),
            ] {
                let definition =
                    support::load_path(&std::path::Path::new(support::DIR).join(file), module);
                let validator = NativeValidator::bind(definition, CompileOptions::default());
                assert_baseline_emissions(
                    &validator,
                    module,
                    &step_support::int_memory(whole),
                    &[int_program(1, 5, support::int(1), 7)],
                );
            }
            let fresh = EiMemory::new("freshgen.k");
            assert_baseline_emissions(
                &fresh.validator,
                "FRESHGEN",
                &step_support::freshgen(whole),
                &[int_program(1, 5, support::int(1), 7)],
            );
            let residue =
                NativeValidator::bind(support::load("residue.k"), CompileOptions::default());
            assert_baseline_emissions(
                &residue,
                "RESIDUE",
                &residue_observation(whole),
                &[ei_program(
                    vec![
                        app("write", vec![support::int(1)]),
                        app("load", vec![support::int(5)]),
                    ],
                    app("halt", vec![]),
                )],
            );
        }
    });
}

fn residue_observation(whole: bool) -> Vec<StepEventSpec> {
    vec![StepEventSpec {
        constructor: "memoryWrite".into(),
        pre: support::k_config(
            app(
                "seq",
                vec![
                    app("write", vec![support::var("X", "SortInt")]),
                    support::var("P", "SortProg"),
                ],
            ),
            "SortProg",
            "R",
            "C",
        ),
        post: whole
            .then(|| support::k_config(support::var("P", "SortProg"), "SortProg", "R", "C2")),
        payload: vec![],
    }]
}

// ------------------------------------------------------------- VI-06: variable-identity audit
//
// README 12 as amended by README 16 (k-rust 927b9ce6, VARIABLE_IDENTITY 3): names are read
// verbatim and printed injectively, and one counter per request skips every request spelling.
// So a test's initial variable is one variable whatever it is spelled, and no spelling can
// make a mint, a rule variable or a scope name one of the test's variables. Each attack runs
// a campaign under the neutral naming and under forged namings, and asserts that the naming
// changes nothing; the neutral result is pinned with its measured value.

/// A campaign's result reduced to what a naming must not change.
#[derive(Debug, PartialEq)]
enum ViResult {
    Refused(CampaignFailureKind),
    Ran {
        tests: Vec<(String, TestRun)>,
        status: MutantStatus,
        killing: Vec<String>,
    },
}

impl ViResult {
    fn of(
        campaign: &Campaign<'_>,
        generation: &CandidateGeneration<'_>,
        mode: ScheduleMode,
    ) -> Self {
        match run_campaign(campaign, generation, mode) {
            Err(failure) => Self::Refused(failure.kind()),
            Ok(run) => {
                let [mutant] = run.mutants.as_slice() else {
                    panic!("one mutant")
                };
                Self::Ran {
                    tests: mutant
                        .plan
                        .tests
                        .iter()
                        .map(|test| (test.test_id.clone(), test.run.clone()))
                        .collect(),
                    status: mutant.report.status,
                    killing: mutant.report.killing_test_ids.clone(),
                }
            }
        }
    }

    fn killed(&self) -> bool {
        matches!(
            self,
            Self::Ran {
                status: MutantStatus::Killed,
                ..
            }
        )
    }

    /// Every Killed result has a declared slot that distinguishes on its killing test.
    fn assert_justified(&self, context: &str) {
        let Self::Ran {
            tests,
            status: MutantStatus::Killed,
            killing,
        } = self
        else {
            return;
        };
        for id in killing {
            let run = tests
                .iter()
                .find(|(test, _)| test == id)
                .map(|(_, run)| run);
            // Pattern slots use the shared decider and exact variable identities (VI-1..VI-5).
            let distinguished = matches!(run, Some(TestRun::Compared(row)) if row.contains(&D));
            assert!(distinguished, "{context}: {id} kills unjustified: {self:?}");
        }
    }
}

/// `pattern` with each free element variable named in `renaming` renamed (KORE JSON level, so
/// the spelling reaches k-rust exactly as written).
fn vi_renamed(pattern: &Pattern, renaming: &[(&str, &str)]) -> Pattern {
    fn walk(value: &mut serde_json::Value, renaming: &[(&str, &str)]) {
        match value {
            serde_json::Value::Object(map) => {
                if map.get("tag").and_then(serde_json::Value::as_str) == Some("EVar")
                    && let Some(serde_json::Value::String(name)) = map.get_mut("name")
                    && let Some((_, to)) = renaming.iter().find(|(from, _)| from == name)
                {
                    *name = (*to).to_owned();
                }
                map.values_mut().for_each(|value| walk(value, renaming));
            }
            serde_json::Value::Array(items) => {
                items.iter_mut().for_each(|value| walk(value, renaming));
            }
            _ => {}
        }
    }
    let mut value = k_rust::kore::codec::to_value(pattern).expect("pattern encodes");
    walk(&mut value, renaming);
    let renamed = k_rust::kore::codec::from_value(&value).expect("pattern decodes");
    let expected = pattern
        .free_variables()
        .into_iter()
        .map(|variable| {
            renaming
                .iter()
                .find(|(from, _)| *from == variable.name)
                .map_or(variable.name.clone(), |(_, to)| (*to).to_owned())
        })
        .collect::<std::collections::BTreeSet<_>>();
    let actual = renamed
        .free_variables()
        .into_iter()
        .map(|variable| variable.name)
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(actual, expected, "every free variable renamed once");
    renamed
}

/// The free element variable names of `tests`, in a fixed order.
fn vi_free_names(tests: &[TestCase]) -> Vec<String> {
    tests
        .iter()
        .flat_map(|test| test.initial_state.free_variables())
        .map(|variable| variable.name)
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect()
}

/// The namings of `tests` that give its free variables the spellings of `spellings`, one per
/// rotation: rotation `r` names the `i`-th variable `spellings[(i + r) % spellings.len()]`.
fn vi_rotations(tests: &[TestCase], spellings: &[&str]) -> Vec<Vec<TestCase>> {
    let names = vi_free_names(tests);
    assert!(names.len() <= spellings.len(), "{names:?}");
    (0..spellings.len())
        .map(|rotation| {
            let renaming = names
                .iter()
                .enumerate()
                .map(|(index, name)| {
                    (
                        name.as_str(),
                        spellings[(index + rotation) % spellings.len()],
                    )
                })
                .collect::<Vec<_>>();
            tests
                .iter()
                .map(|test| TestCase {
                    initial_state: vi_renamed(&test.initial_state, &renaming),
                    ..test.clone()
                })
                .collect()
        })
        .collect()
}

/// Runs `generation` under `tests` and under every naming of `namings`, Full and FirstKill:
/// each naming gives exactly the neutral result, which is returned (Full, FirstKill).
fn vi_naming_invariant(
    context: &str,
    campaign: &dyn Fn(&[TestCase]) -> ViResult,
    tests: &[TestCase],
    namings: &[Vec<TestCase>],
) -> ViResult {
    let neutral = campaign(tests);
    neutral.assert_justified(context);
    for naming in namings {
        let names = vi_free_names(naming);
        let forged = campaign(naming);
        forged.assert_justified(context);
        assert_eq!(forged, neutral, "{context}: naming {names:?}");
    }
    neutral
}

/// The A2 campaign (symmem `V` renamed `U` in write and load): every naming survives.
fn vi_symmem_rename(fixture: &Symmem, tests: &[TestCase], mode: ScheduleMode) -> ViResult {
    let baseline = fixture.validator.baseline();
    let patch = Patch::new(vec![
        renamed(baseline, "SYMMEM.write", &[0, 0, 0, 1], "V", "U"),
        renamed(baseline, "SYMMEM.load", &[0, 0, 0, 1], "V", "U"),
    ])
    .expect("patch");
    let generation = fixed(
        baseline,
        &[
            ("SYMMEM.write", &[0, 0, 0, 1]),
            ("SYMMEM.load", &[0, 0, 0, 1]),
        ],
        "rename-value",
        &patch,
    );
    ViResult::of(&fixture.campaign(tests), &generation, mode)
}

/// The symmem A2 survival, `[[A,A,A,A]; 4]`, in both profiles and schedules.
fn vi_symmem_survives(result: &ViResult) {
    let ViResult::Ran {
        tests,
        status,
        killing,
    } = result
    else {
        panic!("symmem A2 runs: {result:?}")
    };
    assert_eq!(
        tests.iter().map(|(_, run)| run.clone()).collect::<Vec<_>>(),
        vec![TestRun::Compared(vec![A, A, A, A]); 4]
    );
    assert_eq!(*status, MutantStatus::Survived);
    assert!(killing.is_empty());
}

/// G (`inverted_load_sign`) on its symbolic and ground tests: Z3 Killed by both, with G's
/// pattern difference on the symbolic test; no-Z3 refuses the symbolic baseline.
fn vi_guarded_g_pinned(result: &ViResult, mode: ScheduleMode) {
    if cfg!(feature = "z3") {
        let ViResult::Ran {
            status, killing, ..
        } = result
        else {
            panic!("Z3 admits G: {result:?}")
        };
        assert_eq!(*status, MutantStatus::Killed);
        let expected: &[&str] = if mode == ScheduleMode::Full {
            &["sym-guarded", "ground-guarded"]
        } else {
            &["sym-guarded"]
        };
        assert_eq!(killing, expected);
    } else {
        assert_eq!(
            *result,
            ViResult::Refused(CampaignFailureKind::BaselineOracleFailed)
        );
    }
}

/// The repeated-write guard split of `audit_so_symbolic_guard_split_is_not_killed` on `sym-x`.
fn vi_guard_split_tests(guarded: &Guarded) -> Vec<TestCase> {
    let plan = PatternPlan::new(
        &guarded.vocabulary,
        vec![("A".into(), kore_sort("SortInt"))],
        vec![PatternArm {
            atoms: [MatchMode::Bind, MatchMode::Use]
                .into_iter()
                .map(|mode| Atom {
                    constructor: "memoryWrite".into(),
                    payload: vec![PayloadClause {
                        position: 0,
                        mode,
                        variable: "A".into(),
                    }],
                })
                .collect(),
            relations: vec![Relation::EventuallyAfter],
        }],
        None,
    )
    .expect("plan");
    let repeated = OracleDeclaration::new(
        CrashPolicy::CompareIdentity,
        Projection::Pattern {
            plan,
            with_bindings: false,
        },
    )
    .expect("oracle");
    let x = support::var("X", "SortInt");
    let program = support::initial_state(
        app(
            "seq",
            vec![
                app("write", vec![addr(support::int(0)), support::int(5)]),
                app(
                    "seq",
                    vec![
                        app("write", vec![addr(x.clone()), support::int(6)]),
                        app(
                            "seq",
                            vec![
                                app("load", vec![addr(x), support::int(7)]),
                                app("halt", vec![]),
                            ],
                        ),
                    ],
                ),
            ],
        ),
        "SortProg",
    );
    vec![case(
        "sym-x",
        program,
        &[guarded.tests[1].oracles[0].clone(), repeated],
    )]
}

/// Z3 `[[A,A]]` Survived; no-Z3 refuses the symbolic baseline.
fn vi_guard_split_pinned(result: &ViResult) {
    if cfg!(feature = "z3") {
        assert_eq!(
            *result,
            ViResult::Ran {
                tests: vec![("sym-x".into(), TestRun::Compared(vec![A, A]))],
                status: MutantStatus::Survived,
                killing: vec![],
            }
        );
    } else {
        assert_eq!(
            *result,
            ViResult::Refused(CampaignFailureKind::BaselineOracleFailed)
        );
    }
}

const VI_OLD_MINT_SPELLINGS: [&str; 5] = [
    "ExVarI0",
    "ExVarI10",
    "RuleVarX",
    "X'Bang'apart1",
    "Var'Ques'X0",
];

const VI_NEW_MINT_SPELLINGS: [&str; 5] = [
    "Ex-hVarI-b0",
    "Ex-hFrame-b0",
    "X-bapart0",
    "Ex-hVar'Ques'T-b0",
    "Rule-hVarA",
];

/// VI-AT2: initial names spelled like pre-VI mints (`ExVarI0`, `ExVarI10`, `RuleVarX`,
/// `X'Bang'apart1`, `Var'Ques'X0`) are ordinary variables. The symmem A2 rename survives and
/// G keeps its declared pattern kill (Z3; refused without Z3) under every rotation of those
/// spellings, Full and FirstKill, exactly as under the neutral names. Leaf rows (every Unsat
/// and discard) are pinned per fixture in kink-native `audit_vi.rs`.
#[test]
fn audit_vi_at2_old_mint_spellings_keep_every_campaign_result() {
    with_stack(|| {
        let symmem = Symmem::new();
        let guarded = Guarded::new();
        let g = inverted_load_sign(guarded.validator.baseline());
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let result = vi_naming_invariant(
                "AT2 symmem A2",
                &|tests| vi_symmem_rename(&symmem, tests, mode),
                &symmem.tests,
                &vi_rotations(&symmem.tests, &VI_OLD_MINT_SPELLINGS),
            );
            vi_symmem_survives(&result);
            let result = vi_naming_invariant(
                "AT2 G",
                &|tests| ViResult::of(&guarded.campaign(tests), &g, mode),
                &guarded.tests,
                &vi_rotations(&guarded.tests, &VI_OLD_MINT_SPELLINGS),
            );
            vi_guarded_g_pinned(&result, mode);
        }
    });
}

/// VI-AT3: initial names spelled like v3 printed mints (`Ex-hVarI-b0`, `Ex-hFrame-b0`,
/// `X-bapart0`, `Ex-hVar'Ques'T-b0`, `Rule-hVarA`) are read as those variables and never
/// re-minted: symmem A2 survives, G keeps its pattern kill (Z3), and the symbolic guard split
/// survives (Z3; refused without Z3), as under the neutral names. kink-native `audit_vi.rs`
/// pins the leaves next to narrowing that mints `Ex#VarI!N`.
#[test]
fn audit_vi_at3_new_mint_spellings_keep_every_campaign_result() {
    with_stack(|| {
        let symmem = Symmem::new();
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let g = inverted_load_sign(baseline);
        let split = Patch::new(ei_guard_split(baseline)).expect("patch");
        let split = fixed(
            baseline,
            &[("GUARDEDMEM.write", &[1])],
            "guard-split",
            &split,
        );
        let split_tests = vi_guard_split_tests(&guarded);
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let result = vi_naming_invariant(
                "AT3 symmem A2",
                &|tests| vi_symmem_rename(&symmem, tests, mode),
                &symmem.tests,
                &vi_rotations(&symmem.tests, &VI_NEW_MINT_SPELLINGS),
            );
            vi_symmem_survives(&result);
            let result = vi_naming_invariant(
                "AT3 G",
                &|tests| ViResult::of(&guarded.campaign(tests), &g, mode),
                &guarded.tests,
                &vi_rotations(&guarded.tests, &VI_NEW_MINT_SPELLINGS),
            );
            vi_guarded_g_pinned(&result, mode);
            let result = vi_naming_invariant(
                "AT3 guard split",
                &|tests| ViResult::of(&guarded.campaign(tests), &split, mode),
                &split_tests,
                &vi_rotations(&split_tests, &VI_NEW_MINT_SPELLINGS),
            );
            vi_guard_split_pinned(&result);
        }
    });
}

/// VI-AT4: `X-1` (outside v2's decoding image, refused there) is an ordinary variable under
/// v3, like `a-x` and `EI-bB0-u2e-0-b1`: the symmem A2 rename and the symbolic guard split
/// keep the neutral run's result, never a kill.
#[test]
fn audit_vi_at4_hyphenated_names_are_ordinary_variables() {
    with_stack(|| {
        let symmem = Symmem::new();
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let split = Patch::new(ei_guard_split(baseline)).expect("patch");
        let split = fixed(
            baseline,
            &[("GUARDEDMEM.write", &[1])],
            "guard-split",
            &split,
        );
        let split_tests = vi_guard_split_tests(&guarded);
        let spellings = ["X-1", "a-x", "EI-bB0-u2e-0-b1", "Y-1"];
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let result = vi_naming_invariant(
                "AT4 symmem A2",
                &|tests| vi_symmem_rename(&symmem, tests, mode),
                &symmem.tests,
                &vi_rotations(&symmem.tests, &spellings),
            );
            vi_symmem_survives(&result);
            assert!(!result.killed());
            let result = vi_naming_invariant(
                "AT4 guard split",
                &|tests| ViResult::of(&guarded.campaign(tests), &split, mode),
                &split_tests,
                &vi_rotations(&split_tests, &spellings),
            );
            vi_guard_split_pinned(&result);
            assert!(!result.killed());
        }
    });
}

/// freshgen's AT1 guard split: `write` keeps `A >Int 0`, and an inserted copy takes
/// `A ==Int 0`; with `rename` the copy's existential is `?U` instead of `?T`.
fn vi_freshgen_split(fresh: &EiMemory, rename: bool) -> Patch {
    let baseline = fresh.validator.baseline();
    let write_label = fresh.rule("write");
    let a = term(baseline, &write_label, &[0, 0, 0, 0, 0]);
    let mut zero = unlabelled_copy(baseline, &write_label);
    if let k_rust::definition::Sentence::Rule { requires, body, .. } = &mut zero {
        *requires = Term::apply("_==Int_", vec![a.clone(), int_token(0)]);
        if rename {
            assert_eq!(swap_names(body, "?T", "?U"), 1);
        }
    }
    Patch::new(vec![
        replaced(
            baseline,
            &write_label,
            &[1],
            Term::apply("_>Int_", vec![a, int_token(0)]),
        ),
        Edit::InsertSentence {
            position: InsertPosition::After(support::rule(baseline, &write_label)),
            ordinal: 0,
            sentence: zero,
        },
    ])
    .expect("patch")
}

/// freshgen's `write(addr(X), 5); write(addr(Y), 6); load(addr(X), 7); halt`: `?T` is minted
/// twice on every path that does not fault.
fn vi_freshgen_two_writes(fresh: &EiMemory) -> Vec<TestCase> {
    let int = |name: &str| support::var(name, "SortInt");
    let program = support::initial_state(
        app(
            "seq",
            vec![
                app("write", vec![addr(int("X")), support::int(5)]),
                app(
                    "seq",
                    vec![
                        app("write", vec![addr(int("Y")), support::int(6)]),
                        app(
                            "seq",
                            vec![
                                app("load", vec![addr(int("X")), support::int(7)]),
                                app("halt", vec![]),
                            ],
                        ),
                    ],
                ),
            ],
        ),
        "SortProg",
    );
    vec![case(
        "sym-two-writes",
        program,
        &[whole_term(), fresh.gwl_after()],
    )]
}

/// The namings of `vi_freshgen_two_writes`: initial variables spelled like the printed `?T`
/// and `?U` mints (`Ex-hVar'Ques'T-b0` is `Ex#Var'Ques'T!0` printed), which the request's
/// counter must skip.
fn vi_freshgen_namings(tests: &[TestCase]) -> Vec<Vec<TestCase>> {
    [
        [("X", "X"), ("Y", "Ex-hVar'Ques'T-b0")],
        [("X", "Ex-hVar'Ques'T-b0"), ("Y", "Ex-hVar'Ques'T-b1")],
        [("X", "Ex-hVar'Ques'U-b0"), ("Y", "Ex-hVar'Ques'T-b2")],
        [("X", "Ex-hVar'Ques'T-b1"), ("Y", "Ex-hVar'Ques'U-b1")],
    ]
    .iter()
    .map(|renaming| {
        tests
            .iter()
            .map(|test| TestCase {
                initial_state: vi_renamed(&test.initial_state, renaming),
                ..test.clone()
            })
            .collect()
    })
    .collect()
}

/// The measured freshgen two-write result of both split mutants: Z3 `[[A,A]]` Survived;
/// no-Z3 refuses the symbolic baseline.
fn vi_freshgen_pinned(result: &ViResult) {
    if cfg!(feature = "z3") {
        assert_eq!(
            *result,
            ViResult::Ran {
                tests: vec![("sym-two-writes".into(), TestRun::Compared(vec![A, A]))],
                status: MutantStatus::Survived,
                killing: vec![],
            }
        );
    } else {
        assert_eq!(
            *result,
            ViResult::Refused(CampaignFailureKind::BaselineOracleFailed)
        );
    }
}

/// VI-AT5: freshgen's existential `?T` is minted twice on one path (two writes), and leaves
/// the state each time (`stamp` drops it). With initial variables spelled like those mints,
/// or like the renamed copy's `?U` mints, the counter skips their spellings, so the stable set
/// is still the test's initial variables and no Clash or Equal identifies a mint with one: the
/// AT1 rename split keeps the neutral result in both schedules, never a kill.
#[test]
fn audit_vi_at5_reused_existential_keeps_initial_variables_stable() {
    with_stack(|| {
        let fresh = EiMemory::new("freshgen.k");
        let baseline = fresh.validator.baseline();
        let write_label = fresh.rule("write");
        let patch = vi_freshgen_split(&fresh, true);
        let generation = fixed(baseline, &[(&write_label, &[1])], "guard-split", &patch);
        let tests = vi_freshgen_two_writes(&fresh);
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let result = vi_naming_invariant(
                "AT5 freshgen rename split",
                &|tests| ViResult::of(&fresh.campaign(tests), &generation, mode),
                &tests,
                &vi_freshgen_namings(&tests),
            );
            vi_freshgen_pinned(&result);
            assert!(!result.killed());
        }
    });
}

/// VI-AT6: the guard split adds a branch whose rule mints `?T` too. The request's one counter
/// is shared by every branch, so the mutant's later mints carry other counters than the
/// baseline's (kink-native `audit_vi.rs` measures the shift). Minted names are never compared
/// across requests, so the shift kills nothing: the split survives under every naming, as
/// under the neutral one, in both schedules.
#[test]
fn audit_vi_at6_counter_shift_is_not_a_kill() {
    with_stack(|| {
        let fresh = EiMemory::new("freshgen.k");
        let baseline = fresh.validator.baseline();
        let write_label = fresh.rule("write");
        let patch = vi_freshgen_split(&fresh, false);
        let generation = fixed(baseline, &[(&write_label, &[1])], "guard-split", &patch);
        let tests = vi_freshgen_two_writes(&fresh);
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let result = vi_naming_invariant(
                "AT6 freshgen split",
                &|tests| ViResult::of(&fresh.campaign(tests), &generation, mode),
                &tests,
                &vi_freshgen_namings(&tests),
            );
            vi_freshgen_pinned(&result);
            assert!(!result.killed());
        }
    });
}

/// conflate's `go` rules with their variable `I` renamed to `to` in both `goPos` and `goNeg`.
fn vi_conflate_go_renamed(baseline: &Baseline, to: &str) -> Patch {
    Patch::new(vec![
        renamed(baseline, "CONFLATE.goPos", &[0], "I", to),
        renamed(baseline, "CONFLATE.goPos", &[1], "I", to),
        renamed(baseline, "CONFLATE.goNeg", &[0], "I", to),
        renamed(baseline, "CONFLATE.goNeg", &[1], "I", to),
    ])
    .expect("patch")
}

/// VI-AT10 (KK-82 review R1-1): a test whose path condition names `Rule-hVarI` (the printed
/// spelling of conflate's rule variable `Rule#VarI`, which `go` narrows) is read as an
/// ordinary variable that no rule variable is. Against the alpha-renamed mutant (`I` to `K`)
/// the campaign result equals the neutral naming's in both schedules: refused, because the
/// narrowing remainder leaf is Unknown (as `audit_ei_conflated_names_leave_the_state_slot_refused`),
/// never a kill. kink-native `audit_vi.rs` pins the leaves.
#[test]
fn audit_vi_at10_forged_rule_variable_in_the_path_condition_is_not_killed() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("conflate.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let patch = vi_conflate_go_renamed(baseline, "K");
        let generation = fixed(
            baseline,
            &[
                ("CONFLATE.goPos", &[0]),
                ("CONFLATE.goPos", &[1]),
                ("CONFLATE.goNeg", &[0]),
                ("CONFLATE.goNeg", &[1]),
            ],
            "rename",
            &patch,
        );
        let program = ei_program(
            vec![
                app("check", vec![support::var("N", "SortInt")]),
                app("go", vec![support::var("X", "SortBox")]),
            ],
            app("done", vec![]),
        );
        let tests = [case("forged-rule-variable", program, &[whole_term()])];
        let namings = ["Rule-hVarI", "Rule-hI", "Rule-hVarK", "Eq-hVarI"]
            .iter()
            .map(|name| {
                vec![TestCase {
                    initial_state: vi_renamed(&tests[0].initial_state, &[("N", name)]),
                    ..tests[0].clone()
                }]
            })
            .collect::<Vec<_>>();
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let result = vi_naming_invariant(
                "AT10 conflate",
                &|tests| {
                    ViResult::of(
                        &Campaign {
                            validator: &validator,
                            module: "CONFLATE",
                            observation: &[],
                            classify: &normal,
                            tests,
                            budget: BUDGET,
                        },
                        &generation,
                        mode,
                    )
                },
                &tests,
                &namings,
            );
            assert_eq!(
                result,
                ViResult::Refused(CampaignFailureKind::BaselineOracleFailed)
            );
        }
    });
}

/// VI-AT11 (KK-82 review R1-2): a mutant definition whose rule variable or right-hand-side
/// existential is renamed to a forged spelling (`Rule-hA`, `A-b0`; `?X-b0`) compiles and loads
/// as an ordinary alpha-rename: k-rust reads its KORE variable verbatim and marks it like any
/// other. Each forged rename gives exactly the neutral alpha-rename's result in both
/// schedules, never a kill: guardedmem's `write` (`A` renamed, G's tests) survives, and
/// freshgen's renamed existential in the AT1 split survives (ground tests).
#[test]
fn audit_vi_at11_forged_names_in_a_mutant_definition_are_ordinary() {
    with_stack(|| {
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let rename = |to: &str| {
            let patch = Patch::new(vec![
                renamed(baseline, "GUARDEDMEM.write", &[0], "A", to),
                renamed(baseline, "GUARDEDMEM.write", &[1], "A", to),
            ])
            .expect("patch");
            fixed(
                baseline,
                &[("GUARDEDMEM.write", &[0]), ("GUARDEDMEM.write", &[1])],
                "rename",
                &patch,
            )
        };
        let fresh = EiMemory::new("freshgen.k");
        let fresh_baseline = fresh.validator.baseline();
        let write_label = fresh.rule("write");
        let existential = |to: &str| {
            let mut patch = vi_freshgen_split(&fresh, false);
            let mut edits = patch.edits().to_vec();
            let Edit::InsertSentence { sentence, .. } = &mut edits[1] else {
                panic!("inserted copy")
            };
            let k_rust::definition::Sentence::Rule { body, .. } = sentence else {
                panic!("rule")
            };
            assert_eq!(swap_names(body, "?T", to), 1);
            patch = Patch::new(edits).expect("patch");
            fixed(
                fresh_baseline,
                &[(&write_label, &[1])],
                "guard-split",
                &patch,
            )
        };
        let ground = [
            case(
                "ground-zero",
                int_program(0, 5, support::int(0), 7),
                &[whole_term(), fresh.gwl_after()],
            ),
            case(
                "ground-one",
                int_program(1, 5, support::int(1), 7),
                &[whole_term(), fresh.gwl_after()],
            ),
        ];
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let neutral = ViResult::of(&guarded.campaign(&guarded.tests), &rename("B"), mode);
            let expected_rows = if cfg!(feature = "z3") {
                Some(vec![TestRun::Compared(vec![A, A]); 2])
            } else {
                None
            };
            match (&neutral, &expected_rows) {
                (ViResult::Ran { tests, status, .. }, Some(rows)) => {
                    assert_eq!(
                        tests.iter().map(|(_, run)| run.clone()).collect::<Vec<_>>(),
                        *rows
                    );
                    assert_eq!(*status, MutantStatus::Survived);
                }
                (ViResult::Refused(kind), None) => {
                    assert_eq!(*kind, CampaignFailureKind::BaselineOracleFailed);
                }
                other => panic!("guardedmem alpha-rename: {other:?}"),
            }
            for forged in ["Rule-hA", "A-b0", "Ex-hA-b0"] {
                let result = ViResult::of(&guarded.campaign(&guarded.tests), &rename(forged), mode);
                assert_eq!(result, neutral, "guardedmem write renamed to {forged}");
                assert!(!result.killed());
            }
            let neutral = ViResult::of(&fresh.campaign(&ground), &existential("?U"), mode);
            assert_eq!(
                neutral,
                ViResult::Ran {
                    tests: vec![
                        ("ground-zero".into(), TestRun::Compared(vec![A, A])),
                        ("ground-one".into(), TestRun::Compared(vec![A, A])),
                    ],
                    status: MutantStatus::Survived,
                    killing: vec![],
                }
            );
            for forged in ["?X-b0", "?Rule-hT", "?Ex-hVar'Ques'T-b0"] {
                let result = ViResult::of(&fresh.campaign(&ground), &existential(forged), mode);
                assert_eq!(result, neutral, "freshgen existential renamed to {forged}");
            }
        }
    });
}

/// VI-AT8: a test whose state holds set variables spelled like printed marked set variables
/// (`@Rule-hM`, `@Rule#M` printed) is admitted, and its run stops at an Indeterminate leaf
/// (kink-native `audit_vi.rs`), so the baseline's slots are incomplete: the campaign is
/// refused against the A2 rename and against K, in both schedules, never a kill.
#[test]
fn audit_vi_at8_set_variable_in_a_test_is_not_killed() {
    with_stack(|| {
        let symmem = Symmem::new();
        let set = |name: &str| {
            Pattern::Variable(k_rust::kore::ast::Variable {
                kind: k_rust::kore::ast::VariableKind::Set,
                name: name.into(),
                sort: kore_sort("SortNat"),
            })
        };
        let tests = [case(
            "sym-set",
            state(addr(nat("X")), set("@Rule-hM"), addr(nat("X")), set("@M")),
            &symmem.tests[1].oracles,
        )];
        let k = coupled(symmem.validator.baseline(), false);
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            for result in [
                vi_symmem_rename(&symmem, &tests, mode),
                ViResult::of(&symmem.campaign(&tests), &k, mode),
            ] {
                assert_eq!(
                    result,
                    ViResult::Refused(CampaignFailureKind::BaselineOracleFailed)
                );
            }
        }
    });
}

/// VI-06 deliverable 6: `symwraptotal.k` keeps symwrap's non-injective `wrap` (the `anywhere`
/// rule `wrap(s(z)) => wrap(z)`) with a functional claim. The mutant deletes that rule, so
/// `wrap(s(z))` and `wrap(z)` are equal on the baseline and unrelated on the mutant; a
/// decision that treated `wrap` as free would make the mutant's write/load pair `no-match`
/// and kill. Measured, Full and FirstKill, both profiles: the symbolic test's baseline is
/// refused, the ground test is `[[U,U]]` Unknown; never Killed.
#[test]
fn audit_vi_symwrap_total_head_is_not_killed() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("symwraptotal.k"), CompileOptions::default());
        // symwrap has no `free`: only the write and load declarations.
        let mut observation = step_support::symmem(true);
        observation.retain(|spec| spec.constructor != "memoryFree");
        let vocabulary = StepObservation::vocabulary_of(&observation).expect("vocabulary");
        let baseline = validator.baseline();
        let patch = Patch::new(vec![Edit::DeleteSentence {
            at: support::rule(baseline, "SYMWRAPTOTAL.collapse"),
        }])
        .expect("patch");
        let generation = fixed(
            baseline,
            &[("SYMWRAPTOTAL.collapse", &[0])],
            "delete-collapse",
            &patch,
        );
        let wrap = |value: Pattern| app("wrap", vec![value]);
        let oracles = [
            whole_term(),
            pattern(
                &vocabulary,
                "memoryWrite",
                "memoryLoad",
                Relation::EventuallyAfter,
            ),
        ];
        let tests = [
            case(
                "sym-wrap",
                state(
                    wrap(app("s", vec![nat("X")])),
                    nat("V"),
                    wrap(z()),
                    nat("W"),
                ),
                &oracles,
            ),
            case(
                "ground-wrap",
                state(wrap(app("s", vec![z()])), nat("V"), wrap(z()), nat("W")),
                &oracles,
            ),
        ];
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            for test in &tests {
                let campaign = Campaign {
                    validator: &validator,
                    module: "SYMWRAPTOTAL",
                    observation: &observation,
                    classify: &normal,
                    tests: std::slice::from_ref(test),
                    budget: BUDGET,
                };
                let result = ViResult::of(&campaign, &generation, mode);
                assert!(!result.killed(), "{}: {result:?}", test.id);
                let expected = if test.id == "sym-wrap" {
                    ViResult::Refused(CampaignFailureKind::BaselineOracleFailed)
                } else {
                    ViResult::Ran {
                        tests: vec![("ground-wrap".into(), TestRun::Compared(vec![U, U]))],
                        status: MutantStatus::Unknown,
                        killing: vec![],
                    }
                };
                assert_eq!(result, expected, "{} {mode:?}", test.id);
            }
        }
    });
}

/// SO-AT1 keeps canonical identity; at v3, symbolic shadowing is a predicate-phrasing case.
/// Its value-level Agree/Survived pin is audit_so_symbolic_priority_shadowing_is_not_killed.
#[test]
fn audit_so_identical_executions_keep_canonical_paths() {
    with_stack(|| {
        fn identical(campaign: &Campaign<'_>, patch: &Patch, label: &str) {
            let baseline = campaign.validator.compile_baseline().expect("baseline");
            let mutant = campaign.validator.validate(patch).expect("mutant");
            for test in campaign.tests {
                assert_eq!(
                    pattern_paths(
                        &baseline,
                        &baseline,
                        campaign.module,
                        &test.initial_state,
                        campaign.observation
                    ),
                    pattern_paths(
                        &baseline,
                        &mutant,
                        campaign.module,
                        &test.initial_state,
                        campaign.observation
                    ),
                    "{label} {}",
                    test.id
                );
            }
        }
        let fixture = Symmem::new();
        let baseline = fixture.validator.baseline();
        let write = support::rule(baseline, "SYMMEM.write");
        let op = |rule| term(baseline, rule, &[0, 0, 0]);
        let relabel = Patch::new(vec![
            replaced(baseline, "SYMMEM.write", &[0, 0, 0], op("SYMMEM.load")),
            replaced(baseline, "SYMMEM.load", &[0, 0, 0], op("SYMMEM.write")),
        ])
        .expect("relabel");
        let reinsert = Patch::new(vec![
            Edit::DeleteSentence { at: write.clone() },
            Edit::InsertSentence {
                position: InsertPosition::ModuleEnd(write.module.clone()),
                ordinal: 0,
                sentence: unlabelled_copy(baseline, "SYMMEM.write"),
            },
        ])
        .expect("reinsert");
        let alpha = Patch::new(vec![
            renamed(baseline, "SYMMEM.write", &[0, 0, 0, 1], "V", "U"),
            renamed(baseline, "SYMMEM.load", &[0, 0, 0, 1], "V", "U"),
        ])
        .expect("alpha");
        for (label, patch) in [
            ("relabel", relabel),
            ("reinsert", reinsert),
            ("alpha", alpha),
        ] {
            identical(&fixture.campaign(&fixture.tests), &patch, label);
        }
        let guarded = Guarded::new();
        let baseline = guarded.validator.baseline();
        let a = term(baseline, "GUARDEDMEM.write", &[0, 0, 0, 0, 0]);
        for rephrased in [false, true] {
            let guard = if rephrased {
                Term::apply("_<=Int_", vec![int_token(0), a.clone()])
            } else {
                term(baseline, "GUARDEDMEM.write", &[1])
            };
            let patch = Patch::new(vec![
                replaced(
                    baseline,
                    "GUARDEDMEM.write",
                    &[0],
                    term(baseline, "GUARDEDMEM.writeFault", &[0]),
                ),
                replaced(
                    baseline,
                    "GUARDEDMEM.write",
                    &[1],
                    term(baseline, "GUARDEDMEM.writeFault", &[1]),
                ),
                replaced(
                    baseline,
                    "GUARDEDMEM.writeFault",
                    &[0],
                    term(baseline, "GUARDEDMEM.write", &[0]),
                ),
                replaced(baseline, "GUARDEDMEM.writeFault", &[1], guard),
            ])
            .expect("moved content");
            // The existing moved-content audit uses these ground instances.
            let tests = [
                case(
                    "ground-negative",
                    int_program(-1, 5, support::int(1), 7),
                    &guarded.tests[1].oracles,
                ),
                case(
                    "ground-one",
                    int_program(1, 5, support::int(1), 7),
                    &guarded.tests[1].oracles,
                ),
            ];
            identical(
                &guarded.campaign(&tests),
                &patch,
                if rephrased {
                    "moved-rephrased"
                } else {
                    "moved"
                },
            );
        }
        let shadow = Patch::new(vec![Edit::InsertSentence {
            position: InsertPosition::After(support::rule(baseline, "GUARDEDMEM.write")),
            ordinal: 0,
            sentence: ei_shadow(baseline, "GUARDEDMEM.write"),
        }])
        .expect("shadow");
        let tests = [
            case(
                "sym-same",
                state(
                    addr(support::var("Y", "SortInt")),
                    support::int(5),
                    addr(support::var("Y", "SortInt")),
                    support::int(7),
                ),
                &guarded.tests[1].oracles,
            ),
            case(
                "ground-zero",
                int_program(0, 5, support::int(0), 7),
                &guarded.tests[1].oracles,
            ),
        ];
        let compiled = guarded.validator.compile_baseline().expect("baseline");
        let mutant = guarded.validator.validate(&shadow).expect("mutant");
        let left = pattern_paths(
            &compiled,
            &compiled,
            "GUARDEDMEM",
            &tests[0].initial_state,
            &guarded.observation,
        );
        let right = pattern_paths(
            &compiled,
            &mutant,
            "GUARDEDMEM",
            &tests[0].initial_state,
            &guarded.observation,
        );
        if cfg!(feature = "z3") {
            assert_eq!(left.len(), 2);
            assert_eq!(right.len(), 2);
            let predicate = |symbol| Pattern::Equals {
                operand_sort: Box::new(kore_sort("SortBool")),
                result_sort: kore_sort("SortGeneratedTopCell"),
                left: Box::new(Pattern::DomainValue {
                    sort: kore_sort("SortBool"),
                    value: "true".into(),
                }),
                right: Box::new(support::app(
                    symbol,
                    vec![support::var("Y", "SortInt"), support::int(0)],
                )),
            };
            assert_eq!(left[0].path_predicate, predicate("Lbl'Unds-LT-'Int'Unds'"));
            assert_eq!(
                right[0].path_predicate,
                Pattern::Not {
                    sort: kore_sort("SortGeneratedTopCell"),
                    argument: Box::new(predicate("Lbl'Unds-GT-Eqls'Int'Unds'")),
                }
            );
            assert_eq!(
                left[0]
                    .execution_terminal
                    .as_ref()
                    .expect("fault terminal")
                    .state,
                support::initial_state(app("fault", vec![]), "SortProg")
            );
            assert!(left[0].events.is_empty());
            // Compare the remaining fields without normalizing either actual path.
            let mut expected = left.clone();
            expected[0].path_predicate = right[0].path_predicate.clone();
            assert_eq!(
                expected, right,
                "only the fault-leaf predicate phrasing differs"
            );
        } else {
            assert_eq!(left, right);
            assert_eq!(left.len(), 1);
            assert_eq!(
                left[0].path_predicate,
                Pattern::Top {
                    sort: kore_sort("SortGeneratedTopCell"),
                }
            );
            assert_eq!(left[0].stop, kink_pattern::PathStop::SolverUnknown);
            assert!(!left[0].complete);
            assert!(left[0].execution_terminal.is_none());
            assert!(left[0].events.is_empty());
        }
        identical(&guarded.campaign(&tests[1..]), &shadow, "ground-shadow");
        let mut lemma = unlabelled_copy(baseline, "GUARDEDMEM.write");
        if let k_rust::definition::Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        } = &mut lemma
        {
            *body = Term::Rewrite {
                left: Box::new(Term::apply("_+Int_", vec![a.clone(), int_token(0)])),
                right: Box::new(a),
            };
            *requires = ei_bool(true);
            *ensures = ei_bool(true);
        } else {
            panic!("rule");
        }
        lemma.attributes_mut().set(
            AttributeKey::SmtLemma,
            serde_json::Value::String(String::new()),
        );
        let dead_lemma = Patch::new(vec![Edit::InsertSentence {
            position: InsertPosition::ModuleEnd(support::rule(baseline, "GUARDEDMEM.write").module),
            ordinal: 0,
            sentence: lemma,
        }])
        .expect("dead lemma");
        identical(
            &guarded.campaign(&guarded.tests),
            &dead_lemma,
            "dead-smt-lemma",
        );
    });
}

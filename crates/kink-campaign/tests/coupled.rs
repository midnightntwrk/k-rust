//! End-to-end symmem and guardedmem campaigns for exact-site and coupled operators.

#[path = "../../../testdata/k/support.rs"]
mod support;

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
use kink_native::execution::ExecutionBudget;
use kink_native::observation::{DomainEventSpec, PayloadSource};
use kink_native::{NativeValidator, ObservedRule};
use kink_patch::{
    Baseline, CandidateDisposition, CandidateGeneration, Edit, InsertPosition, Patch,
    SelectionPolicy, SiteSelector, TermRef, derive_sites, select,
};
use kink_pattern::{
    Atom, Constructor, EventVocabulary, ExecutionTerminalKind, MatchMode, PatternArm, PatternPlan,
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

fn observed(
    baseline: &Baseline,
    label: &str,
    constructor: &str,
    paths: &[Vec<u32>],
) -> ObservedRule {
    ObservedRule {
        rule: support::rule(baseline, label),
        emit_rule_applied: false,
        domain_events: vec![DomainEventSpec {
            constructor: constructor.into(),
            payload: paths
                .iter()
                .cloned()
                .map(PayloadSource::BeforeTerm)
                .collect(),
        }],
    }
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
    observed: Vec<ObservedRule>,
    tests: Vec<TestCase>,
}

impl Symmem {
    fn new() -> Self {
        let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let vocabulary = EventVocabulary::new(vec![
            Constructor {
                name: "memoryWrite".into(),
                payload_sorts: vec![kore_sort("SortAddress"), kore_sort("SortNat")],
            },
            Constructor {
                name: "memoryLoad".into(),
                payload_sorts: vec![kore_sort("SortAddress"), kore_sort("SortNat")],
            },
            Constructor {
                name: "memoryFree".into(),
                payload_sorts: vec![kore_sort("SortAddress")],
            },
        ])
        .expect("vocabulary");
        let observed = vec![
            observed(
                baseline,
                "SYMMEM.write",
                "memoryWrite",
                &[support::k_head(&[0, 0]), support::k_head(&[0, 1])],
            ),
            observed(
                baseline,
                "SYMMEM.load",
                "memoryLoad",
                &[support::k_head(&[0, 0]), support::k_head(&[0, 1])],
            ),
            observed(
                baseline,
                "SYMMEM.free",
                "memoryFree",
                &[support::k_head(&[0, 0])],
            ),
        ];
        let tests = tests(&vocabulary);
        Self {
            validator,
            vocabulary,
            observed,
            tests,
        }
    }

    fn campaign<'a>(&'a self, tests: &'a [TestCase]) -> Campaign<'a> {
        Campaign {
            validator: &self.validator,
            module: "SYMMEM",
            observed_rules: &self.observed,
            vocabulary: &self.vocabulary,
            classify: &normal,
            tests,
            budget: BUDGET,
        }
    }
}

struct Guarded {
    validator: NativeValidator,
    vocabulary: EventVocabulary,
    observed: Vec<ObservedRule>,
    tests: Vec<TestCase>,
}

impl Guarded {
    fn new() -> Self {
        let validator =
            NativeValidator::bind(support::load("guardedmem.k"), CompileOptions::default());
        let baseline = validator.baseline();
        let vocabulary = EventVocabulary::new(vec![
            Constructor {
                name: "memoryWrite".into(),
                payload_sorts: vec![kore_sort("SortInt"), kore_sort("SortInt")],
            },
            Constructor {
                name: "memoryLoad".into(),
                payload_sorts: vec![kore_sort("SortInt"), kore_sort("SortInt")],
            },
        ])
        .expect("vocabulary");
        let observed = vec![
            observed(
                baseline,
                "GUARDEDMEM.write",
                "memoryWrite",
                &[support::k_head(&[0, 0, 0]), support::k_head(&[0, 1])],
            ),
            observed(
                baseline,
                "GUARDEDMEM.load",
                "memoryLoad",
                &[support::k_head(&[0, 0, 0]), support::k_head(&[0, 1])],
            ),
            observed(
                baseline,
                "GUARDEDMEM.loadNeg",
                "memoryLoad",
                &[support::k_head(&[0, 0, 0]), support::k_head(&[0, 1])],
            ),
        ];
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
            observed,
            tests,
        }
    }

    fn campaign<'a>(&'a self, tests: &'a [TestCase]) -> Campaign<'a> {
        Campaign {
            validator: &self.validator,
            module: "GUARDEDMEM",
            observed_rules: &self.observed,
            vocabulary: &self.vocabulary,
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
        let fixture = Symmem::new();
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
                vec![A, D, A, A],
                vec![A, D, A, A],
                vec![A, D, A, A],
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
    });
}

#[test]
fn coupled_release_is_one_mutant_killed_by_its_trace() {
    with_stack(|| {
        let fixture = Symmem::new();
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
                vec![A, D, A, D],
                vec![A, D, A, D],
                vec![A, D, A, D],
                vec![A, A, A, D]
            ]
        );
        let mutant = &run.mutants[0];
        assert_eq!(mutant.report.status, MutantStatus::Killed);
        assert_eq!(
            mutant.report.killing_test_ids,
            ["ground-shared", "sym-shared", "sym-distinct", "sym-clash"]
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
        let fixture = Symmem::new();
        let baseline = fixture.validator.baseline();
        let coupled_generation = coupled(baseline, false);
        let single_generation = release_after_write(baseline);
        for (depth, generation, expected, status) in [
            (
                3,
                &coupled_generation,
                vec![U, U, A, U],
                MutantStatus::Unknown,
            ),
            (
                3,
                &single_generation,
                vec![U, U, A, U],
                MutantStatus::Unknown,
            ),
            (
                4,
                &coupled_generation,
                vec![U, U, A, D],
                MutantStatus::Killed,
            ),
        ] {
            let mut campaign = fixture.campaign(&fixture.tests[..1]);
            campaign.budget.max_depth = Some(depth);
            let run = run_campaign(&campaign, generation, ScheduleMode::Full)
                .expect("bounded baseline admitted");
            assert_eq!(outcomes(&run), vec![expected], "depth {depth}");
            assert_eq!(run.mutants[0].report.status, status, "depth {depth}");
            assert_eq!(
                run.mutants[0].report.killing_test_ids.is_empty(),
                depth == 3
            );
            if depth == 4 {
                assert_eq!(run.mutants[0].report.killing_test_ids, ["ground-shared"]);
                let TestRun::Compared(slots) = &run.mutants[0].plan.tests[0].run else {
                    panic!("expected compared slots")
                };
                assert_eq!(slots.iter().filter(|slot| **slot == D).count(), 1);
                assert_eq!(slots[3], D);
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
// README section 12, attacks A1-A6. With pre-state payloads (KS-04) A2 and A6, and with
// content anchoring (KS-06) A1, are no longer execution-identical kills or unknowns: their
// execution-identical mutants survive. Every other attack must end in a refusal, `Unknown`
// or survival, never in a kill of an execution-identical mutant.

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
        let vocabulary = EventVocabulary::new(
            ["memoryWrite", "memoryLoad"]
                .map(|name| Constructor {
                    name: name.into(),
                    payload_sorts: vec![kore_sort("SortInt"), kore_sort("SortInt")],
                })
                .to_vec(),
        )
        .expect("vocabulary");
        let observed = vec![
            observed(
                baseline,
                "SYMPARTIAL.write",
                "memoryWrite",
                &[support::k_head(&[0, 0, 0]), support::k_head(&[0, 1])],
            ),
            observed(
                baseline,
                "SYMPARTIAL.load",
                "memoryLoad",
                &[support::k_head(&[0, 0, 0]), support::k_head(&[0, 1])],
            ),
        ];
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

#[test]
fn missing_before_term_on_a_mutant_is_unknown() {
    with_stack(|| {
        let mut fixture = Symmem::new();
        fixture.observed[0].domain_events[0].payload = vec![
            PayloadSource::BeforeTerm(support::k_head(&[0, 0])),
            PayloadSource::BeforeTerm(support::k_head(&[0, 1, 0])),
        ];
        let baseline = fixture.validator.baseline();
        let discovery = derive_sites(
            baseline,
            "load-continuation",
            &[
                SiteSelector::RuleLabel("SYMMEM.load".into()),
                SiteSelector::Path(vec![0, 1]),
            ],
        )
        .expect("site");
        assert!(discovery.exhaustive());
        let generation = select(&discovery, exact(1, 1), 1)
            .expect("selection")
            .fold("load-writes-zero", |origin| {
                let at = origin.discovery_tuples[0].sites[0].at.clone();
                let continuation = baseline.term(&at).expect("continuation").clone();
                let address = term(baseline, "SYMMEM.load", &[0, 0, 0, 0]);
                Patch::new(vec![Edit::ReplaceTerm {
                    at,
                    expected: continuation.clone(),
                    replacement: Term::apply(
                        "seq",
                        vec![
                            Term::apply("write", vec![address, Term::apply("z", vec![])]),
                            continuation,
                        ],
                    ),
                }])
                .expect("patch")
            })
            .expect("generation");
        let tests = [fixture.tests[0].clone()];
        let run = run_campaign(&fixture.campaign(&tests), &generation, ScheduleMode::Full)
            .expect("baseline admitted");
        assert_eq!(run.baseline.len(), 1);
        assert!(matches!(run.baseline[0].run, SideRun::Sides { .. }));
        let [mutant] = run.mutants.as_slice() else {
            panic!("one mutant")
        };
        assert_eq!(mutant.plan.tests.len(), 1);
        assert_eq!(
            mutant.plan.tests[0].run,
            TestRun::Failed(kink_campaign::ExecutionFailureKind::UnresolvedObservation)
        );
        assert_eq!(mutant.report.status, MutantStatus::Unknown);
        assert!(mutant.report.killing_test_ids.is_empty());
    });
}

#[test]
fn before_term_missing_on_the_baseline_is_refused() {
    with_stack(|| {
        let mut fixture = Symmem::new();
        fixture.observed[0].domain_events[0].payload =
            vec![PayloadSource::BeforeTerm(support::k_head(&[0, 5]))];
        let generation = release_after_write(fixture.validator.baseline());
        let tests = [fixture.tests[0].clone()];
        let failure = run_campaign(&fixture.campaign(&tests), &generation, ScheduleMode::Full)
            .expect_err("missing baseline path");
        assert_eq!(failure.kind(), CampaignFailureKind::BaselineError);
    });
}

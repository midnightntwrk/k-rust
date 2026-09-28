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

// ---------------------------------------------------------------- KS-07 audit attacks
//
// Kill-soundness README section 12, attacks AS1-AS7, plus the constructions the KS-07 audit
// added (section 15). Each test pins the measured status in both profiles. A test whose name
// ends in `_until_ticket_ks_tNN` pins a kill of an execution-identical run that the ticket
// tracks; no other test here asserts such a kill.

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
    observed: Vec<ObservedRule>,
}

impl GuardedEq {
    fn new() -> Self {
        let validator =
            NativeValidator::bind(support::load("guardedeq.k"), CompileOptions::default());
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
        let observed = [
            ("GUARDEDEQ.write", "memoryWrite"),
            ("GUARDEDEQ.load", "memoryLoad"),
        ]
        .map(|(label, constructor)| {
            observed(
                baseline,
                label,
                constructor,
                &[support::k_head(&[0, 0, 0]), support::k_head(&[0, 1])],
            )
        })
        .to_vec();
        Self {
            validator,
            vocabulary,
            observed,
        }
    }

    fn campaign<'a>(&'a self, tests: &'a [TestCase]) -> Campaign<'a> {
        Campaign {
            validator: &self.validator,
            module: "GUARDEDEQ",
            observed_rules: &self.observed,
            vocabulary: &self.vocabulary,
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

/// AS2 (KS-R2, ticket KS-T08). `guardedeq.k` states `write`'s guard as the range
/// `A >=Int 1 andBool A <=Int 1`; the mutant states it as `A ==Int 1`. On the symbolic test
/// (Z3) every slot agrees, value bindings included: no syntactic difference of the pre-states
/// reaches a payload. A `with_bindings` plan over the symbolic load address is refused on the
/// baseline in both profiles. Without Z3 the symbolic baseline is undecided and only the
/// ground test runs.
#[test]
fn audit_ks_as2_requires_rephrasing_is_not_killed() {
    with_stack(|| {
        let fixture = GuardedEq::new();
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
            assert_survived(
                &run.expect("Z3 admits the symbolic baseline"),
                &[vec![A; 5], vec![A; 5]],
            );
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
    });
}

/// AS3 (KS-R3). A patch cannot write the configuration layout that `BeforeTerm` paths
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

/// AS4. A `with_bindings` plan over a `BeforeTerm` payload is admitted only where the baseline
/// value is ground: the write address and value of `ground-shared` and the ground address
/// `addr(z)` of `sym-clash` survive S1 (whose write is unchanged); every symbolic value
/// (`sym-shared`, `sym-distinct`, and `sym-clash`'s value `V`) is refused on the baseline, as
/// A3 row 1. Same in both profiles.
#[test]
fn audit_ks_as4_symbolic_before_terms_are_not_binding_values() {
    with_stack(|| {
        let fixture = Symmem::new();
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
                assert_survived(&run.expect("ground binding admitted"), &[vec![A]]);
            } else {
                assert_eq!(
                    run.expect_err("symbolic binding refused").kind(),
                    CampaignFailureKind::BaselineOracleFailed,
                    "{} {position}",
                    fixture.tests[test].id
                );
            }
        }
    });
}

/// AS5 (KS-R4, ticket KS-T04). Guard split: `GUARDEDMEM.write`'s guard narrowed to `A >Int 0`
/// and an unobserved copy with `A ==Int 0` inserted. The rewrite relation is the baseline's,
/// but on address 0 the unobserved copy fires where the observed `write` did, so `GWL-after`
/// distinguishes an execution-identical run. Pinned Killed until KS-T04; both profiles.
#[test]
fn audit_ks_as5_guard_split_is_killed_until_ticket_ks_t04() {
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
        assert_eq!(outcomes(&run), vec![vec![A, D], vec![A, A]]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(run.mutants[0].report.killing_test_ids, ["ground-zero"]);
    });
}

/// New in KS-07 (ticket KS-T04, widened). Priority shadowing edits no observed rule: an
/// unobserved copy of `GUARDEDMEM.write` with `priority(40)` is inserted. `write` is unchanged
/// and anchored, but it never fires again, so `GWL-after` distinguishes on every address while
/// the rewrite relation is the baseline's. Pinned Killed until KS-T04. The same copy at the
/// default priority, with its guard written `0 <=Int A`, survives (row 2).
#[test]
fn audit_ks_priority_shadowing_is_killed_until_ticket_ks_t04() {
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
        assert_eq!(outcomes(&run), vec![vec![A, D]; 2]);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(
            run.mutants[0].report.killing_test_ids,
            ["ground-zero", "ground-one"]
        );

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

/// New in KS-07 (ticket KS-T04). Exchanging the bodies and guards of the observed
/// `GUARDEDMEM.write` and the unobserved `writeFault` survives: `write`'s content is anchored
/// and consumes its source position, so the moved `writeFault` content stays unobserved
/// (row 1). If the moved `write` content is also rephrased (`0 <=Int A`), nothing is anchored:
/// the `write` position now holds `writeFault`'s content and positionally carries
/// `memoryWrite`, while the rephrased `write` content is unobserved. The rewrite relation is
/// the baseline's; both tests distinguish (row 2). Pinned Killed until KS-T04.
#[test]
fn audit_ks_moved_unobserved_content_is_killed_until_ticket_ks_t04() {
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
        for (rephrased, expected, killed) in [
            (false, vec![vec![A, A, A]; 2], false),
            (true, vec![vec![A, A, D], vec![A, D, D]], true),
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
            if killed {
                assert_eq!(outcomes(&run), expected);
                assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
                assert_eq!(
                    run.mutants[0].report.killing_test_ids,
                    ["ground-negative", "ground-one"]
                );
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

/// AS7 (KS-R5), anchoring internals. (a) Replacing `SYMMEM.load`'s operation by `write` makes
/// two observed positions compile to one identity: the manifest refuses it as `Ambiguous` and
/// the mutant is `Error`, not a kill. (b) Rewriting `norm(X) => X` as `X +Int 0` in
/// `guardedeq.k` withdraws `total` from `norm` and `preserves-definedness` from the observed
/// `load` on the symbolic side; there `load`'s axiom differs from the baseline's, so it is
/// resolved by position, and the withdrawn side's anchored manifest equals its positional one.
/// Ground (patched side) and symbolic (withdrawn side) tests agree on every slot (Z3; without
/// Z3 only the ground test is admitted). (c) `FirstKill` equals `Full` on A1, and on A1 with
/// `V` renamed to `U` in the moved `write` content (anchored modulo alpha): both survive.
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
        assert_eq!(
            mutant.plan.mutant_failure,
            Some(kink_campaign::MutantScopeFailure::Infrastructure)
        );
        assert_eq!(mutant.report.status, MutantStatus::Error);
        let compiled = fixture.validator.compile_baseline().expect("baseline");
        let side = fixture.validator.validate(&patch).expect("mutant");
        assert!(matches!(
            fixture
                .validator
                .observation_manifest_anchored(&compiled, &side, &fixture.observed),
            Err(kink_native::ManifestFailure::Identity {
                error: kink_native::IdentityError::Ambiguous,
                ..
            })
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
            let withdrawn = eq
                .validator
                .validate(claims.patch().expect("withdrawing patch"))
                .expect("withdrawn side");
            let compiled = eq.validator.compile_baseline().expect("baseline");
            assert_eq!(
                eq.validator
                    .observation_manifest_anchored(&compiled, &withdrawn, &eq.observed)
                    .expect("anchored"),
                eq.validator
                    .observation_manifest(&withdrawn, &eq.observed)
                    .expect("positional")
            );
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

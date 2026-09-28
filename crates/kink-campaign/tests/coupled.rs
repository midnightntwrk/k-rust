//! End-to-end symmem campaigns for exact-site and coupled operators.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::time::Duration;

use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::kore_sort;
use k_rust::kore::ast::Pattern;
use kink_campaign::{
    Campaign, CrashPolicy, FinalResult, MutantStatus, OracleDeclaration, OracleOutcome, OracleSide,
    OracleValue, PatternValue, Projection, Rational, ScheduleMode, SideRun, StateProjection,
    TestCase, TestRun, run_campaign, tally,
};
use kink_native::execution::ExecutionBudget;
use kink_native::observation::{DomainEventSpec, PayloadSource};
use kink_native::{NativeValidator, ObservedRule};
use kink_patch::{
    Baseline, CandidateGeneration, Edit, Patch, SelectionPolicy, SiteSelector, TermRef,
    derive_sites, select,
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

fn observed(baseline: &Baseline, label: &str, constructor: &str, names: &[&str]) -> ObservedRule {
    ObservedRule {
        rule: support::rule(baseline, label),
        emit_rule_applied: false,
        domain_events: vec![DomainEventSpec {
            constructor: constructor.into(),
            payload: names
                .iter()
                .map(|name| PayloadSource::BindingValueNamed(format!("RuleVar{name}")))
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
    let plan = PatternPlan::new(
        vocabulary,
        vec![("A".into(), kore_sort("SortAddress"))],
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
            observed(baseline, "SYMMEM.write", "memoryWrite", &["A", "V"]),
            observed(baseline, "SYMMEM.load", "memoryLoad", &["A", "V"]),
            observed(baseline, "SYMMEM.free", "memoryFree", &["A"]),
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
                        let expected = baseline.term(&at).expect("term").clone();
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

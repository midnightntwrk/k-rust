//! Report fixtures copied from end_to_end.rs and coupled.rs.
#[path = "../../../testdata/k/step_support.rs"]
mod step_support;
#[path = "../../../testdata/k/support.rs"]
mod support;
use k_rust::{
    definition::AttributeKey,
    kast::{Sort as KastSort, Term},
    kompile::{
        CompileOptions,
        initial_configuration::{kore_application, kore_sort},
    },
    kore::ast::Pattern,
};
use kink_campaign::{
    Campaign, CampaignReport, CampaignRun, CrashPolicy, ManifestInput, OperatorId,
    OracleDeclaration, Projection, ReportError, ScheduleMode, StateProjection, TestCase, TestRun,
    campaign_manifest, campaign_report, run_campaign,
};
use kink_native::{NativeValidator, execution::ExecutionBudget, step_events::StepObservation};
use kink_patch::{
    Baseline, CandidateGeneration, Claim, Discovery, Edit, InsertPosition, POSITION_KEYS, Patch,
    SelectionPolicy, SentenceOrigin, SiteSelector, TermRef, derive_sites, select,
};
use kink_pattern::{
    Atom, EventVocabulary, ExecutionTerminalKind, MatchMode, PatternArm, PatternPlan,
    PayloadClause, Relation,
};
use serde_json::{Value, json};
use std::time::Duration;
const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
};
fn constant(symbol: &str) -> Pattern {
    kore_application(symbol, Vec::new(), Vec::new())
}

fn z() -> Pattern {
    constant("Lblz")
}

fn s(pattern: Pattern) -> Pattern {
    kore_application("Lbls", Vec::new(), vec![pattern])
}

fn bool_value(value: &str) -> Pattern {
    Pattern::DomainValue {
        sort: kore_sort("SortBool"),
        value: value.into(),
    }
}

fn bool_token(value: &str) -> Term {
    Term::Token {
        token: value.to_owned(),
        sort: KastSort::new("Bool"),
    }
}

fn counter_state() -> Pattern {
    support::initial_state(
        kore_application("Lblcounter", Vec::new(), vec![z(), s(s(s(z())))]),
        "SortCounter",
    )
}

fn choose_state() -> Pattern {
    support::initial_state(
        kore_application("Lblchoose", Vec::new(), vec![bool_value("true")]),
        "SortControl",
    )
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

fn whole_term(crash_policy: CrashPolicy) -> OracleDeclaration {
    OracleDeclaration::new(crash_policy, Projection::State(StateProjection::WholeTerm))
        .expect("final-result declaration")
}

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

fn replace(baseline: &Baseline, label: &str, path: &[u32], replacement: Term) -> (TermRef, Patch) {
    let at = TermRef::new(support::rule(baseline, label), path);
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("baseline term").clone(),
        at: at.clone(),
        replacement,
    }])
    .expect("one edit");
    (at, patch)
}

fn generation<'b>(baseline: &'b Baseline, mutants: &[(TermRef, Patch)]) -> CandidateGeneration<'b> {
    let derive = |clauses: &[SiteSelector]| derive_sites(baseline, "site", clauses);
    let nothing = Discovery::empty(baseline, false, false);
    let discovery = mutants
        .iter()
        .map(|(site, _)| {
            let label = baseline
                .sentence(&site.sentence)
                .and_then(|rule| rule.attributes().string(AttributeKey::Label))
                .expect("a labelled rule");
            derive(&[
                SiteSelector::RuleLabel(label.to_owned()),
                SiteSelector::Path(site.path.0.clone()),
            ])
        })
        .try_fold(nothing, |all, next| all.union(&next.expect("no bindings")))
        .expect("one baseline and shape");
    assert!(discovery.exhaustive(), "declared by clauses");
    assert_eq!(
        discovery.tuples().len(),
        mutants.len(),
        "one site per mutant"
    );
    select(&discovery, SelectionPolicy::Each, mutants.len().max(1))
        .expect("selection")
        .fold("test", |origin| {
            let (_, patch) = mutants
                .iter()
                .find(|(site, _)| origin.site_tuple == [site.clone()])
                .expect("a mutant's site");
            patch.clone()
        })
        .expect("every patch edits its site's rule")
}

fn term_at(baseline: &Baseline, label: &str, path: &[u32]) -> Term {
    baseline
        .term(&TermRef::new(support::rule(baseline, label), path))
        .expect("baseline term")
        .clone()
}

fn counter_tests(specs: &[kink_native::step_events::StepEventSpec]) -> Vec<TestCase> {
    let vocabulary = StepObservation::vocabulary_of(specs).unwrap();
    vec![
        TestCase {
            id: "t1".into(),
            initial_state: counter_state(),
            oracles: vec![
                whole_term(CrashPolicy::CompareIdentity),
                occurs(&vocabulary, "increment"),
            ],
        },
        TestCase {
            id: "t2".into(),
            initial_state: choose_state(),
            oracles: vec![
                whole_term(CrashPolicy::CompareIdentity),
                occurs(&vocabulary, "branchTaken"),
            ],
        },
    ]
}
fn counter_generation(baseline: &Baseline) -> CandidateGeneration<'_> {
    let mutants = [
        (
            TermRef::new(support::rule(baseline, "COUNTER.increment"), [0]),
            Patch::new(vec![Edit::AddAttribute {
                at: support::rule(baseline, "COUNTER.increment"),
                key: "foo".into(),
                value: json!(""),
            }])
            .unwrap(),
        ),
        replace(
            baseline,
            "COUNTER.increment",
            &[0, 1, 0],
            term_at(baseline, "COUNTER.increment", &[0, 1, 0, 0]),
        ),
        replace(baseline, "COUNTER.branch", &[1], bool_token("false")),
        replace(baseline, "COUNTER.fallback", &[0, 1, 0], bool_token("true")),
    ];
    generation(baseline, &mutants)
}
mod symmem {
    use super::*;
    use k_rust::kast::Sort;
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

    fn exact(count: usize, arity: usize) -> SelectionPolicy {
        SelectionPolicy::Exact {
            expected_tuple_count: count,
            expected_tuple_arity: arity,
        }
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
                                    vec![
                                        Term::apply("free", vec![bound.clone()]),
                                        expected.clone(),
                                    ],
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

    pub(super) fn declaration() -> (Vec<kink_native::step_events::StepEventSpec>, Vec<TestCase>) {
        let specs = step_support::symmem(true);
        let vocabulary = StepObservation::vocabulary_of(&specs).unwrap();
        let tests = tests(&vocabulary);
        (specs, tests)
    }
    pub(super) fn generation(b: &Baseline) -> CandidateGeneration<'_> {
        coupled(b, false)
    }
}

fn with_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap();
}
fn keys(value: &Value, expected: &[&str]) {
    let actual = value
        .as_object()
        .unwrap()
        .keys()
        .map(String::as_str)
        .collect::<Vec<_>>();
    let mut expected = expected.to_vec();
    expected.sort();
    assert_eq!(actual, expected);
}
fn array(value: &Value) -> &[Value] {
    value.as_array().unwrap()
}
fn check_side_run(value: &Value) {
    if value.get("failed").is_some() {
        keys(value, &["failed"]);
        return;
    }
    keys(value, &["sides"]);
    for side in array(&value["sides"]) {
        if side.is_string() {
            assert!(matches!(
                side.as_str().unwrap(),
                "timeout" | "unknown" | "error"
            ));
            continue;
        }
        if side.get("semantic-crash").is_some() {
            keys(side, &["semantic-crash"]);
            continue;
        }
        keys(side, &["normal"]);
        let value = &side["normal"];
        if value.get("whole-term").is_some() {
            keys(value, &["whole-term"]);
        } else if value.get("exit-stop").is_some() {
            keys(value, &["exit-stop"]);
            for stop in array(&value["exit-stop"]) {
                keys(stop, &["class", "code"]);
            }
        } else if value.get("term-paths").is_some() {
            keys(value, &["term-paths"]);
            for paths in array(&value["term-paths"]) {
                for path in array(paths) {
                    keys(path, &["path", "term"]);
                }
            }
        } else {
            keys(value, &["pattern"]);
            if value["pattern"].is_object() {
                keys(&value["pattern"], &["match"]);
                if !value["pattern"]["match"].is_null() {
                    for tuple in array(&value["pattern"]["match"]) {
                        for binding in array(tuple) {
                            keys(binding, &["name", "term"]);
                        }
                    }
                }
            } else {
                assert_eq!(value["pattern"], "no-match");
            }
        }
    }
}
fn check_report(report: &CampaignReport) {
    let v = report.value();
    keys(
        v,
        &[
            "schema",
            "version",
            "manifest_sha256",
            "manifest",
            "baseline",
            "coverage",
            "origins",
            "mutants",
            "summary",
        ],
    );
    assert_eq!(v["schema"], "kink-campaign-report");
    assert_eq!(v["version"], 3);
    for baseline in array(&v["baseline"]) {
        keys(baseline, &["test_id", "run"]);
        check_side_run(&baseline["run"]);
    }
    for origin in array(&v["origins"]) {
        keys(
            origin,
            &[
                "operator",
                "ordinal",
                "site_tuple",
                "discovery_tuples",
                "disposition",
            ],
        );
        for site in array(&origin["site_tuple"]) {
            keys(site, &["module", "index", "path"]);
        }
        keys(
            &origin["disposition"],
            &[if origin["disposition"].get("mutant").is_some() {
                "mutant"
            } else {
                "rejected"
            }],
        );
        for tuple in array(&origin["discovery_tuples"]) {
            keys(tuple, &["sites", "bindings"]);
            for site in array(&tuple["sites"]) {
                keys(site, &["role", "module", "index", "path"]);
            }
            for binding in array(&tuple["bindings"]) {
                keys(binding, &["name", "term"]);
            }
        }
    }
    for mutant in array(&v["mutants"]) {
        keys(
            mutant,
            &[
                "mutant_id",
                "operator",
                "origins",
                "patch_sha256",
                "canonical_patch",
                "affected_sentences",
                "inserted_sentences",
                "diff",
                "status",
                "mutant_failure",
                "executed_test_ids",
                "killing_test_ids",
                "skipped_test_ids",
                "tests",
                "claims",
                "selection",
            ],
        );
        for sentence in array(&mutant["affected_sentences"]) {
            keys(
                sentence,
                &[
                    "module",
                    "index",
                    "label",
                    "source",
                    "location",
                    "old_fingerprint",
                    "new_fingerprint",
                ],
            );
        }
        for sentence in array(&mutant["inserted_sentences"]) {
            keys(sentence, &["module", "index", "fingerprint"]);
        }
        for diff in array(&mutant["diff"]) {
            keys(
                diff,
                &["op", "sentence", "path", "position", "key", "old", "new"],
            );
        }
        for test in array(&mutant["tests"]) {
            keys(test, &["test_id", "run", "mutant"]);
            let run = &test["run"];
            if run.is_string() {
                assert_eq!(run, "skipped-after-kill");
                assert!(test["mutant"].is_null());
            } else {
                keys(
                    run,
                    &[if run.get("compared").is_some() {
                        "compared"
                    } else {
                        "failed"
                    }],
                );
            }
            if !test["mutant"].is_null() {
                check_side_run(&test["mutant"]);
            }
        }
        keys(&mutant["claims"], &["withdrawn", "unsupported"]);
        for kind in ["withdrawn", "unsupported"] {
            for claim in array(&mutant["claims"][kind]) {
                keys(claim, &["origin", "key", "value"]);
                if let Some(at) = claim["origin"].get("baseline") {
                    keys(&claim["origin"], &["baseline"]);
                    keys(at, &["module", "index"]);
                } else {
                    keys(&claim["origin"], &["inserted"]);
                }
            }
        }
    }
    keys(&v["summary"], &["tally", "score", "per_operator"]);
    keys(
        &v["summary"]["tally"],
        &[
            "killed",
            "survived",
            "equivalent",
            "invalid",
            "timeout",
            "unknown",
            "error",
            "rejected_origins",
        ],
    );
    if !v["summary"]["score"].is_null() {
        keys(
            &v["summary"]["score"],
            &["killed", "survived", "denominator", "ratio"],
        );
        if !v["summary"]["score"]["ratio"].is_null() {
            keys(
                &v["summary"]["score"]["ratio"],
                &["numerator", "denominator"],
            );
        }
    }
    fn walk(v: &Value, parent: &str) {
        match v {
            Value::Object(obj) => {
                for (key, value) in obj {
                    if key.ends_with("_ms") {
                        assert!(matches!(
                            (parent, key.as_str()),
                            ("budget", "time_ms") | ("backend_options", "smt_timeout_ms")
                        ));
                    }
                    walk(value, key);
                }
            }
            Value::Array(a) => {
                for v in a {
                    walk(v, parent);
                }
            }
            Value::String(s) => {
                assert!(!std::path::Path::new(s).is_absolute(), "absolute path: {s}")
            }
            _ => {}
        }
    }
    walk(v, "");
    assert!(!report.text().contains(env!("CARGO_MANIFEST_DIR")));
    assert_eq!(report.text(), kink_patch::canonical_json(v));
    assert_eq!(
        v["manifest"]["profile"],
        if cfg!(feature = "z3") { "z3" } else { "no-z3" }
    );
}
fn build(
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    schedule: ScheduleMode,
    operator: &str,
    policy: SelectionPolicy,
) -> (CampaignReport, CampaignRun) {
    let manifest = campaign_manifest(&ManifestInput {
        campaign,
        generation,
        schedule,
        selection: kink_campaign::SelectionPolicy::None,
        operators: &[kink_campaign::ManifestOperator::Code(OperatorId {
            id: operator,
            version: 1,
            policy,
        })],
        classifier: "normal",
    })
    .unwrap();
    let run = run_campaign(campaign, generation, schedule).unwrap();
    let report = campaign_report(&manifest, campaign, generation, &run).unwrap();
    check_report(&report);
    (report, run)
}
fn kebab(value: impl std::fmt::Debug) -> String {
    let mut s = String::new();
    for (i, c) in format!("{value:?}").chars().enumerate() {
        if i > 0 && c.is_uppercase() {
            s.push('-');
        }
        s.extend(c.to_lowercase());
    }
    s
}
fn check_run(report: &CampaignReport, run: &CampaignRun) {
    for (recorded, mutant) in array(&report.value()["mutants"]).iter().zip(&run.mutants) {
        assert_eq!(recorded["status"], kebab(mutant.report.status));
        assert_eq!(
            recorded["executed_test_ids"],
            json!(mutant.report.executed_test_ids)
        );
        assert_eq!(
            recorded["killing_test_ids"],
            json!(mutant.report.killing_test_ids)
        );
        assert_eq!(
            recorded["skipped_test_ids"],
            json!(mutant.report.skipped_test_ids)
        );
        for (test, plan) in array(&recorded["tests"]).iter().zip(&mutant.plan.tests) {
            assert_eq!(test["test_id"], plan.test_id);
            match &plan.run {
                TestRun::Compared(outcomes) => assert_eq!(
                    test["run"]["compared"],
                    json!(outcomes.iter().map(kebab).collect::<Vec<_>>())
                ),
                TestRun::Failed(f) => assert_eq!(test["run"], json!({"failed":kebab(f)})),
                TestRun::SkippedAfterKill => {
                    assert_eq!(test["run"], "skipped-after-kill");
                    assert!(test["mutant"].is_null());
                }
            }
            assert_eq!(
                test["mutant"].is_null(),
                !mutant.evidence.iter().any(|e| e.test_id == plan.test_id)
            );
        }
    }
}
#[test]
fn counter_reports_are_identical_and_match_runs_in_both_schedules() {
    with_stack(|| {
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let mut outputs = Vec::new();
            for _ in 0..2 {
                let validator =
                    NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
                let specs = step_support::counter(true);
                let tests = counter_tests(&specs);
                let generation = counter_generation(validator.baseline());
                let campaign = Campaign {
                    validator: &validator,
                    module: "COUNTER",
                    observation: &specs,
                    classify: &normal,
                    tests: &tests,
                    budget: BUDGET,
                };
                let (report, run) = build(
                    &campaign,
                    &generation,
                    schedule,
                    "test",
                    SelectionPolicy::Each,
                );
                check_run(&report, &run);
                assert_eq!(report.value()["mutants"][1]["status"], "killed");
                assert_eq!(
                    report.value()["mutants"][1]["tests"][0]["run"],
                    json!({"compared":["distinguish","distinguish"]})
                );
                let affected = &report.value()["mutants"][1]["affected_sentences"][0];
                assert_eq!(
                    affected["old_fingerprint"],
                    "54fe0f8ab4a2960043bf920269631e53512f3777f1a35c10da9db9a0812cc935"
                );
                assert_ne!(affected["old_fingerprint"], affected["new_fingerprint"]);
                assert_eq!(affected["label"], "COUNTER.increment");
                assert_eq!(affected["source"], "counter.k");
                assert_eq!(array(&affected["location"]).len(), 4);
                for key in POSITION_KEYS {
                    assert!(
                        !report.value()["mutants"][1]["diff"]
                            .to_string()
                            .contains(key.as_str())
                    );
                }
                if schedule == ScheduleMode::FirstKill {
                    assert_eq!(
                        report.value()["mutants"][1]["tests"][1]["run"],
                        "skipped-after-kill"
                    );
                    assert!(report.value()["mutants"][1]["tests"][1]["mutant"].is_null());
                }
                outputs.push(report.text());
                let manifest = campaign_manifest(&ManifestInput {
                    campaign: &campaign,
                    generation: &generation,
                    schedule,
                    selection: kink_campaign::SelectionPolicy::None,
                    operators: &[kink_campaign::ManifestOperator::Code(OperatorId {
                        id: "test",
                        version: 1,
                        policy: SelectionPolicy::Each,
                    })],
                    classifier: "normal",
                })
                .unwrap();
                let mut short = run.clone();
                short.mutants.pop();
                assert_eq!(
                    campaign_report(&manifest, &campaign, &generation, &short).unwrap_err(),
                    ReportError::MutantCountMismatch
                );
                let changed = altered_counter_generation(validator.baseline(), &generation);
                assert_eq!(
                    campaign_report(&manifest, &campaign, &changed, &run).unwrap_err(),
                    ReportError::ManifestMismatch
                );
                let different = generation_one(
                    validator.baseline(),
                    "COUNTER.increment",
                    bool_token("false"),
                );
                let (_, other_run) = build(
                    &campaign,
                    &different,
                    schedule,
                    "test",
                    SelectionPolicy::Each,
                );
                assert_eq!(
                    campaign_report(&manifest, &campaign, &different, &other_run).unwrap_err(),
                    ReportError::ManifestMismatch
                );
            }
            assert_eq!(
                outputs[0], outputs[1],
                "STOP: independent counter reports differ"
            );
            if schedule == ScheduleMode::Full {
                std::fs::write(
                    std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!(
                        "si03-counter-report-{}.json",
                        if cfg!(feature = "z3") { "z3" } else { "no-z3" }
                    )),
                    &outputs[0],
                )
                .unwrap();
            }
        }
    });
}
fn altered_counter_generation<'a>(
    b: &'a Baseline,
    original: &CandidateGeneration<'_>,
) -> CandidateGeneration<'a> {
    let mutants = original
        .candidates()
        .iter()
        .enumerate()
        .map(|(id, candidate)| {
            let patch = if id == 0 {
                Patch::new(vec![Edit::AddAttribute {
                    at: support::rule(b, "COUNTER.increment"),
                    key: "bar".into(),
                    value: json!(""),
                }])
                .unwrap()
            } else {
                candidate.patch.clone()
            };
            (candidate.origins[0].site_tuple[0].clone(), patch)
        })
        .collect::<Vec<_>>();
    generation(b, &mutants)
}
fn generation_one<'a>(
    baseline: &'a Baseline,
    label: &str,
    replacement: Term,
) -> CandidateGeneration<'a> {
    generation(baseline, &[replace(baseline, label, &[1], replacement)])
}
#[test]
fn coupled_reports_are_identical_and_keep_two_edits_in_one_mutant() {
    with_stack(|| {
        let mut outputs = Vec::new();
        for _ in 0..2 {
            let validator =
                NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
            let (specs, tests) = symmem::declaration();
            let generation = symmem::generation(validator.baseline());
            let campaign = Campaign {
                validator: &validator,
                module: "SYMMEM",
                observation: &specs,
                classify: &normal,
                tests: &tests,
                budget: BUDGET,
            };
            let (report, run) = build(
                &campaign,
                &generation,
                ScheduleMode::Full,
                "release-after-access",
                SelectionPolicy::Exact {
                    expected_tuple_count: 1,
                    expected_tuple_arity: 2,
                },
            );
            check_run(&report, &run);
            assert_eq!(array(&report.value()["mutants"]).len(), 1);
            let mutant = &report.value()["mutants"][0];
            assert_eq!(mutant["status"], "killed");
            assert_eq!(array(&mutant["affected_sentences"]).len(), 2);
            assert_eq!(array(&mutant["diff"]).len(), 2);
            outputs.push(report.text());
        }
        assert_eq!(
            outputs[0], outputs[1],
            "STOP: independent coupled reports differ"
        );
    });
}
#[test]
fn no_change_origin_is_reported_as_rejected() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let b = validator.baseline();
        let generation = generation_one(
            b,
            "COUNTER.increment",
            term_at(b, "COUNTER.increment", &[1]),
        );
        let specs = step_support::counter(true);
        let tests = counter_tests(&specs);
        let campaign = Campaign {
            validator: &validator,
            module: "COUNTER",
            observation: &specs,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let (report, _) = build(
            &campaign,
            &generation,
            ScheduleMode::Full,
            "test",
            SelectionPolicy::Each,
        );
        assert_eq!(
            report.value()["origins"][0]["disposition"],
            json!({"rejected":"no-change"})
        );
        assert!(array(&report.value()["mutants"]).is_empty());
        assert!(report.value()["summary"]["score"].is_null());
    });
}
#[test]
fn equivalent_clone_has_inserted_sentence_and_equivalent_failure() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let b = validator.baseline();
        let at = support::rule(b, "COUNTER.increment");
        let mut clone = b.sentence(&at).unwrap().clone();
        for key in POSITION_KEYS
            .into_iter()
            .chain([AttributeKey::Label, AttributeKey::UniqueId])
        {
            clone.attributes_mut().remove(key.as_str());
        }
        let patch = Patch::new(vec![Edit::InsertSentence {
            position: InsertPosition::After(at.clone()),
            ordinal: 0,
            sentence: clone,
        }])
        .unwrap();
        let generation = generation(b, &[(TermRef::new(at, [0]), patch)]);
        let specs = step_support::counter(true);
        let tests = [TestCase {
            id: "increment".into(),
            initial_state: counter_state(),
            oracles: vec![whole_term(CrashPolicy::CompareIdentity)],
        }];
        let campaign = Campaign {
            validator: &validator,
            module: "COUNTER",
            observation: &specs,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let (report, _) = build(
            &campaign,
            &generation,
            ScheduleMode::Full,
            "test",
            SelectionPolicy::Each,
        );
        let m = &report.value()["mutants"][0];
        assert_eq!(m["status"], "equivalent");
        assert_eq!(m["mutant_failure"], "equivalent-compilation");
        assert_eq!(array(&m["inserted_sentences"]).len(), 1);
        assert!(array(&m["affected_sentences"]).is_empty());
        assert!(m["diff"][0]["old"].is_null());
        assert!(m["diff"][0]["sentence"].is_null());
        for key in POSITION_KEYS {
            assert!(!m["diff"][0]["new"].to_string().contains(key.as_str()));
        }
    });
}

#[test]
fn sentence_and_attribute_diffs_use_normalized_baseline_content() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let b = validator.baseline();
        let at = support::rule(b, "COUNTER.fallback");
        let original = b.sentence(&at).unwrap();
        let priority = original.attributes().get("priority").unwrap().clone();
        let mut replacement = original.clone();
        if let k_rust::definition::Sentence::Rule { requires, .. } = &mut replacement {
            *requires = bool_token("false");
        } else {
            panic!("rule");
        }
        let cases = [
            (
                Edit::ReplaceSentence {
                    at: at.clone(),
                    replacement: replacement.clone(),
                },
                json!(
                    serde_json::from_str::<Value>(
                        &kink_patch::fingerprint_payload(original).unwrap()
                    )
                    .unwrap()
                ),
                json!(
                    serde_json::from_str::<Value>(
                        &kink_patch::fingerprint_payload(&replacement).unwrap()
                    )
                    .unwrap()
                ),
            ),
            (
                Edit::DeleteSentence { at: at.clone() },
                serde_json::from_str::<Value>(&kink_patch::fingerprint_payload(original).unwrap())
                    .unwrap(),
                Value::Null,
            ),
            (
                Edit::RemoveAttribute {
                    at: at.clone(),
                    key: "priority".into(),
                    expected: priority.clone(),
                },
                priority.clone(),
                Value::Null,
            ),
            (
                Edit::ReplaceAttribute {
                    at: at.clone(),
                    key: "priority".into(),
                    expected: priority.clone(),
                    replacement: json!("60"),
                },
                priority,
                json!("60"),
            ),
        ];
        let specs = step_support::counter(true);
        let tests = counter_tests(&specs);
        let campaign = Campaign {
            validator: &validator,
            module: "COUNTER",
            observation: &specs,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        for (edit, old, new) in cases {
            let patch = Patch::new(vec![edit]).unwrap();
            let generation = generation(b, &[(TermRef::new(at.clone(), [0]), patch)]);
            let (report, _) = build(
                &campaign,
                &generation,
                ScheduleMode::Full,
                "test",
                SelectionPolicy::Each,
            );
            let mutant = &report.value()["mutants"][0];
            let diff = &mutant["diff"][0];
            assert_eq!(diff["old"], old);
            assert_eq!(diff["new"], new);
            assert_eq!(
                diff["sentence"],
                json!({"module":at.module,"index":at.index})
            );
            assert!(diff["path"].is_null());
            assert!(diff["position"].is_null());
            assert_eq!(
                mutant["affected_sentences"][0]["new_fingerprint"].is_null(),
                diff["op"] == "delete-sentence"
            );
            for key in POSITION_KEYS {
                assert!(!diff.to_string().contains(key.as_str()));
            }
        }
    });
}

/// Exercise every side and claim object with supplied evidence; this is a serialization
/// test and does not claim that these deliberately combined sides came from execution.
#[test]
fn supplied_evidence_and_claims_keep_their_exact_schema() {
    with_stack(|| {
        use kink_campaign::{
            ExecutionFailureKind, ExitStop, FinalResult, OracleOutcome, OracleSide, OracleValue,
            PatternValue, SideRun, TerminalClass,
        };
        use std::collections::BTreeSet;
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let b = validator.baseline();
        let generation = generation_one(b, "COUNTER.increment", bool_token("false"));
        let specs = step_support::counter(true);
        let tests = counter_tests(&specs);
        let campaign = Campaign {
            validator: &validator,
            module: "COUNTER",
            observation: &specs,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let manifest = campaign_manifest(&ManifestInput {
            campaign: &campaign,
            generation: &generation,
            schedule: ScheduleMode::Full,
            selection: kink_campaign::SelectionPolicy::None,
            operators: &[kink_campaign::ManifestOperator::Code(OperatorId {
                id: "test",
                version: 1,
                policy: SelectionPolicy::Each,
            })],
            classifier: "normal",
        })
        .unwrap();
        let mut run = run_campaign(&campaign, &generation, ScheduleMode::Full).unwrap();
        let witness = kink_pattern::Binding {
            name: "A".into(),
            term: z(),
        };
        let sides = vec![
            OracleSide::Normal(OracleValue::ExitStop(
                [ExitStop {
                    class: TerminalClass::UndefinedStep,
                    code: None,
                }]
                .into(),
            )),
            OracleSide::Normal(OracleValue::FinalResult(FinalResult::TermPaths(
                [vec![(vec![0], z())]].into(),
            ))),
            OracleSide::Normal(OracleValue::Pattern(PatternValue::Match {
                bindings: Some(BTreeSet::from([vec![witness]])),
            })),
            OracleSide::Normal(OracleValue::Pattern(PatternValue::Match { bindings: None })),
            OracleSide::SemanticCrash(z()),
            OracleSide::Timeout,
            OracleSide::Unknown,
            OracleSide::Error,
        ];
        run.baseline[0].run = SideRun::Sides {
            sides: sides.clone(),
        };
        run.baseline[1].run = SideRun::Failed(ExecutionFailureKind::TimeLimit);
        let m = &mut run.mutants[0];
        m.plan.tests[0].run = TestRun::Compared(vec![OracleOutcome::Unknown]);
        m.plan.tests[1].run = TestRun::Failed(ExecutionFailureKind::UnsupportedClaims);
        m.evidence[0].run = SideRun::Sides { sides };
        m.evidence[1].run = SideRun::Failed(ExecutionFailureKind::UnsupportedClaims);
        m.plan.claims.withdrawn.push(Claim {
            origin: SentenceOrigin::Baseline(support::rule(b, "COUNTER.increment")),
            key: "total".into(),
            value: json!(""),
        });
        m.plan.claims.unsupported.push(Claim {
            origin: SentenceOrigin::Inserted { edit: 0 },
            key: "functional".into(),
            value: json!(""),
        });
        let report = campaign_report(&manifest, &campaign, &generation, &run).unwrap();
        check_report(&report);
        assert_eq!(
            report.value()["mutants"][0]["claims"]["unsupported"][0]["origin"],
            json!({"inserted":0})
        );
        let recorded = &report.value()["baseline"][0]["run"]["sides"];
        assert_eq!(
            recorded[0],
            json!({"normal":{"exit-stop":[{"class":"undefined-step","code":null}]}})
        );
        assert_eq!(recorded[2]["normal"]["pattern"]["match"][0][0]["name"], "A");
        assert_eq!(
            recorded[4],
            json!({"semantic-crash":k_rust::kore::codec::to_value(&z()).unwrap()})
        );
        assert_eq!(recorded[5], "timeout");
        assert_eq!(recorded[6], "unknown");
        assert_eq!(recorded[7], "error");
    });
}

//! Replay fixtures copied from end_to_end.rs and coupled.rs.
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
    Campaign, CampaignReport, CrashPolicy, ManifestInput, MutantId, OperatorId, OracleDeclaration,
    Projection, ReplayDeclaration, ReplayOutcome, ReplayRefusal, ScheduleMode, StateProjection,
    TestCase, campaign_manifest, campaign_report, replay, run_campaign,
};
use kink_native::{NativeValidator, execution::ExecutionBudget, step_events::StepObservation};
use kink_patch::{
    Baseline, CAMPAIGN_MANIFEST_DOMAIN, CandidateFailure, CandidateGeneration, Discovery, Edit,
    InsertPosition, POSITION_KEYS, Patch, SelectionPolicy, SemanticInput, SiteSelector, TermRef,
    canonical_json, derive_sites, payload_digest, select,
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

    pub(super) fn generation(
        baseline: &Baseline,
    ) -> Result<CandidateGeneration<'_>, CandidateFailure> {
        let derive = |role: &str, rule: &str| {
            derive_sites(
                baseline,
                role,
                &[
                    SiteSelector::RuleLabel(rule.into()),
                    SiteSelector::Path(vec![0, 0, 0, 0]),
                    SiteSelector::Sort(Sort::new("Address")),
                    SiteSelector::Bind("A".into()),
                ],
            )
        };
        let discovery =
            derive("write", "SYMMEM.write")?.join(&derive("load", "SYMMEM.load")?, false)?;
        select(
            &discovery,
            SelectionPolicy::Exact {
                expected_tuple_count: 1,
                expected_tuple_arity: 2,
            },
            1,
        )?
        .fold("release-after-access", |origin| {
            let tuple = &origin.discovery_tuples[0];
            let bound = tuple.bindings.get("A").expect("binding").clone();
            Patch::new(
                tuple
                    .sites
                    .iter()
                    .map(|site| {
                        let at = TermRef::new(site.at.sentence.clone(), [0, 1]);
                        let expected = baseline.term(&at).expect("term").clone();
                        let replacement = Term::apply(
                            "seq",
                            vec![Term::apply("free", vec![bound.clone()]), expected.clone()],
                        );
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
    }

    pub(super) fn declaration() -> (Vec<kink_native::step_events::StepEventSpec>, Vec<TestCase>) {
        let specs = step_support::symmem(true);
        let vocabulary = StepObservation::vocabulary_of(&specs).unwrap();
        let tests = tests(&vocabulary);
        (specs, tests)
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
fn select_counter(b: &Baseline) -> Result<CandidateGeneration<'_>, CandidateFailure> {
    Ok(counter_generation(b))
}
fn select_coupled(b: &Baseline) -> Result<CandidateGeneration<'_>, CandidateFailure> {
    symmem::generation(b)
}
fn select_equivalent(b: &Baseline) -> Result<CandidateGeneration<'_>, CandidateFailure> {
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
    Ok(generation(b, &[(TermRef::new(at, [0]), patch)]))
}
fn counter_declaration<'a>(
    specs: &'a [kink_native::step_events::StepEventSpec],
    tests: &'a [TestCase],
    schedule: ScheduleMode,
) -> ReplayDeclaration<'a> {
    ReplayDeclaration {
        module: "COUNTER",
        observation: specs,
        classify: &normal,
        classifier: "normal",
        tests,
        budget: BUDGET,
        schedule,
        selection: kink_campaign::SelectionPolicy::None,
        operator: OperatorId {
            id: "test",
            version: 1,
            policy: SelectionPolicy::Each,
        },
        select: &select_counter,
    }
}
fn coupled_declaration<'a>(
    specs: &'a [kink_native::step_events::StepEventSpec],
    tests: &'a [TestCase],
) -> ReplayDeclaration<'a> {
    ReplayDeclaration {
        module: "SYMMEM",
        observation: specs,
        classify: &normal,
        classifier: "normal",
        tests,
        budget: BUDGET,
        schedule: ScheduleMode::Full,
        selection: kink_campaign::SelectionPolicy::None,
        operator: OperatorId {
            id: "release-after-access",
            version: 1,
            policy: SelectionPolicy::Exact {
                expected_tuple_count: 1,
                expected_tuple_arity: 2,
            },
        },
        select: &select_coupled,
    }
}
fn build(file: &str, declaration: &ReplayDeclaration<'_>) -> (CampaignReport, String) {
    let validator = NativeValidator::bind(support::load(file), CompileOptions::default());
    let campaign = Campaign {
        validator: &validator,
        module: declaration.module,
        observation: declaration.observation,
        classify: declaration.classify,
        tests: declaration.tests,
        budget: declaration.budget,
    };
    let generation = (declaration.select)(validator.baseline()).unwrap();
    let manifest = campaign_manifest(&ManifestInput {
        campaign: &campaign,
        generation: &generation,
        schedule: declaration.schedule,
        selection: kink_campaign::SelectionPolicy::None,
        operator: OperatorId {
            id: declaration.operator.id,
            version: declaration.operator.version,
            policy: declaration.operator.policy,
        },
        classifier: declaration.classifier,
    })
    .unwrap();
    let run = run_campaign(&campaign, &generation, declaration.schedule).unwrap();
    let report = campaign_report(&manifest, &campaign, &generation, &run).unwrap();
    assert_no_time_bound(report.value());
    (report, manifest.baseline_input().text().to_owned())
}
fn assert_no_time_bound(value: &Value) {
    match value {
        Value::String(s) => assert!(
            !matches!(s.as_str(), "timeout" | "time-limit"),
            "STOP: fired time bound"
        ),
        Value::Array(a) => a.iter().for_each(assert_no_time_bound),
        Value::Object(o) => o.values().for_each(assert_no_time_bound),
        _ => (),
    }
}
fn reproduced(name: &str, report: &str, artifact: &str, declaration: &ReplayDeclaration<'_>) {
    let start = std::time::Instant::now();
    let result = replay(report, artifact, declaration);
    assert_eq!(
        result,
        ReplayOutcome::Reproduced,
        "STOP: {name}: {result:?}"
    );
    let line = format!(
        "{name}: {result:?}; debug replay seconds = {:.6}\n",
        start.elapsed().as_secs_f64()
    );
    std::fs::write(
        std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!(
            "si04-{name}-{}.txt",
            if cfg!(feature = "z3") { "z3" } else { "no-z3" }
        )),
        line,
    )
    .unwrap();
}
fn rehash_manifest(report: &mut Value) {
    report["manifest_sha256"] = json!(
        payload_digest(
            CAMPAIGN_MANIFEST_DOMAIN,
            canonical_json(&report["manifest"]).as_bytes()
        )
        .to_string()
    );
}
#[test]
fn counter_reproduces_in_full_and_first_kill_and_from_files() {
    with_stack(|| {
        let specs = step_support::counter(true);
        let tests = counter_tests(&specs);
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let declaration = counter_declaration(&specs, &tests, schedule);
            let (report, artifact) = build("counter.k", &declaration);
            assert_eq!(report.value()["mutants"][1]["status"], "killed");
            let name = if schedule == ScheduleMode::Full {
                "counter-full"
            } else {
                "counter-first-kill"
            };
            reproduced(name, &report.text(), &artifact, &declaration);
            if schedule == ScheduleMode::Full {
                let root = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"));
                let report_path =
                    root.join(format!("counter-report-{}.json", cfg!(feature = "z3")));
                let artifact_path =
                    root.join(format!("counter-artifact-{}.json", cfg!(feature = "z3")));
                std::fs::write(&report_path, report.text()).unwrap();
                std::fs::write(&artifact_path, artifact).unwrap();
                reproduced(
                    "counter-file",
                    &std::fs::read_to_string(report_path).unwrap(),
                    &std::fs::read_to_string(artifact_path).unwrap(),
                    &declaration,
                );
            }
        }
    });
}
#[test]
fn coupled_protected_kill_reproduces_and_reversed_edits_are_refused() {
    with_stack(|| {
        let (specs, tests) = symmem::declaration();
        let declaration = coupled_declaration(&specs, &tests);
        let (report, artifact) = build("symmem.k", &declaration);
        assert_eq!(report.value()["mutants"][0]["status"], "killed");
        reproduced("coupled", &report.text(), &artifact, &declaration);
        let mut changed = report.value().clone();
        changed["mutants"][0]["canonical_patch"]["edits"]
            .as_array_mut()
            .unwrap()
            .reverse();
        assert_eq!(
            replay(&canonical_json(&changed), &artifact, &declaration),
            ReplayOutcome::Refused(ReplayRefusal::PatchDecode(MutantId(0)))
        );
    });
}
#[test]
fn equivalent_clone_reproduces() {
    with_stack(|| {
        let specs = step_support::counter(true);
        let tests = [TestCase {
            id: "increment".into(),
            initial_state: counter_state(),
            oracles: vec![whole_term(CrashPolicy::CompareIdentity)],
        }];
        let mut declaration = counter_declaration(&specs, &tests, ScheduleMode::Full);
        declaration.select = &select_equivalent;
        let (report, artifact) = build("counter.k", &declaration);
        assert_eq!(report.value()["mutants"][0]["status"], "equivalent");
        reproduced("equivalent", &report.text(), &artifact, &declaration);
    });
}
#[test]
fn counter_tampers_are_refused_or_diverge_before_any_verdict() {
    with_stack(|| {
        let specs = step_support::counter(true);
        let tests = counter_tests(&specs);
        let mut declaration = counter_declaration(&specs, &tests, ScheduleMode::Full);
        let (report, artifact) = build("counter.k", &declaration);
        let original = report.value();
        let mut changed = original.clone();
        changed["mutants"][2]["canonical_patch"]["edits"][0]["replacement"]["term"]["token"] =
            json!("falsE");
        assert!(matches!(
            replay(&canonical_json(&changed), &artifact, &declaration),
            ReplayOutcome::Refused(
                ReplayRefusal::PatchDecode(MutantId(2)) | ReplayRefusal::PatchDigest(MutantId(2))
            )
        ));

        let token_changed = artifact.replacen("\"token\":\"true\"", "\"token\":\"false\"", 1);
        assert_ne!(token_changed, artifact);
        assert!(
            SemanticInput::read(&token_changed).is_ok(),
            "a valid changed artifact"
        );
        assert_eq!(
            replay(&report.text(), &token_changed, &declaration),
            ReplayOutcome::Refused(ReplayRefusal::BaselineDigest)
        );

        let root = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("si04-variant");
        std::fs::create_dir_all(&root).unwrap();
        let path = root.join("counter.k");
        let source = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/k/counter.k"),
        )
        .unwrap();
        let source = source.replace("counter(s(N), L)", "counter(s(s(N)), L)");
        std::fs::write(&path, source).unwrap();
        let variant = SemanticInput::of(&support::load_path(&path, "COUNTER")).unwrap();
        changed = original.clone();
        changed["manifest"]["baseline"]["semantic_input_sha256"] =
            json!(variant.digest().to_string());
        rehash_manifest(&mut changed);
        assert!(matches!(
            replay(&canonical_json(&changed), variant.text(), &declaration),
            ReplayOutcome::Refused(ReplayRefusal::Stale(_) | ReplayRefusal::MutantDigest(_))
        ));

        changed = original.clone();
        changed["mutants"][1]["status"] = json!("survived");
        assert_eq!(
            replay(&canonical_json(&changed), &artifact, &declaration),
            ReplayOutcome::Diverged {
                pointer: "/mutants/1/status".into(),
                mutants: vec![MutantId(1)]
            }
        );

        changed = original.clone();
        changed["manifest"]["k_rust"]["revision"] = json!("different");
        rehash_manifest(&mut changed);
        assert_eq!(
            replay(&canonical_json(&changed), &artifact, &declaration),
            ReplayOutcome::Refused(ReplayRefusal::Environment("k_rust.revision".into()))
        );
        changed = original.clone();
        changed["manifest"]["profile"] = json!(if cfg!(feature = "z3") { "no-z3" } else { "z3" });
        rehash_manifest(&mut changed);
        assert_eq!(
            replay(&canonical_json(&changed), &artifact, &declaration),
            ReplayOutcome::Refused(ReplayRefusal::Environment("profile".into()))
        );
        changed = original.clone();
        changed["manifest"]["budget"]["max_depth"] = json!(1);
        rehash_manifest(&mut changed);
        assert_eq!(
            replay(&canonical_json(&changed), &artifact, &declaration),
            ReplayOutcome::Refused(ReplayRefusal::Declaration)
        );
        declaration.operator.version = 2;
        assert_eq!(
            replay(&report.text(), &artifact, &declaration),
            ReplayOutcome::Refused(ReplayRefusal::Declaration)
        );
        let (coupled_specs, coupled_tests) = symmem::declaration();
        let coupled = coupled_declaration(&coupled_specs, &coupled_tests);
        assert!(matches!(
            replay(&report.text(), &artifact, &coupled),
            ReplayOutcome::Refused(_)
        ));
    });
}

#[test]
fn malformed_reports_and_digest_mismatches_fail_in_check_order() {
    with_stack(|| {
        let specs = step_support::counter(true);
        let tests = counter_tests(&specs);
        let declaration = counter_declaration(&specs, &tests, ScheduleMode::Full);
        let (report, artifact) = build("counter.k", &declaration);
        for text in ["{", "null", "[]", "{}"] {
            assert_eq!(
                replay(text, "invalid artifact", &declaration),
                ReplayOutcome::Refused(ReplayRefusal::Schema)
            );
        }
        let mut changed = report.value().clone();
        changed["version"] = json!(3);
        assert_eq!(
            replay(&canonical_json(&changed), "invalid artifact", &declaration),
            ReplayOutcome::Refused(ReplayRefusal::Schema)
        );
        changed = report.value().clone();
        changed["manifest"]["profile"] = json!("foreign");
        assert_eq!(
            replay(&canonical_json(&changed), "invalid artifact", &declaration),
            ReplayOutcome::Refused(ReplayRefusal::ManifestDigest)
        );
        rehash_manifest(&mut changed);
        assert_eq!(
            replay(&canonical_json(&changed), "invalid artifact", &declaration),
            ReplayOutcome::Refused(ReplayRefusal::Environment("profile".into()))
        );
        changed = report.value().clone();
        changed["manifest"]["baseline"]["semantic_input_sha256"] =
            json!(kink_patch::sha256(b"{}").to_string());
        rehash_manifest(&mut changed);
        assert!(matches!(
            replay(&canonical_json(&changed), "{}", &declaration),
            ReplayOutcome::Refused(ReplayRefusal::Artifact(_))
        ));
        for key in ["structure_sha256", "kore_sha256"] {
            changed = report.value().clone();
            changed["manifest"]["mutants"][1][key] = json!("0".repeat(64));
            rehash_manifest(&mut changed);
            assert_eq!(
                replay(&canonical_json(&changed), &artifact, &declaration),
                ReplayOutcome::Refused(ReplayRefusal::MutantDigest(MutantId(1)))
            );
        }
        changed = report.value().clone();
        changed["manifest"]["mutants"][0]["validation"]["detail"] = json!("other");
        rehash_manifest(&mut changed);
        assert_eq!(
            replay(&canonical_json(&changed), &artifact, &declaration),
            ReplayOutcome::Refused(ReplayRefusal::MutantDigest(MutantId(0)))
        );
    });
}

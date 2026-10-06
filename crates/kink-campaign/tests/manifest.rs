//! Manifest fixtures copied from end_to_end.rs and coupled.rs; no campaign executes.
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
    Campaign, CampaignManifest, CrashPolicy, ManifestError, ManifestInput, OperatorId,
    OracleDeclaration, Projection, ScheduleMode, StateProjection, TestCase, campaign_manifest,
};
use kink_native::{NativeValidator, execution::ExecutionBudget, step_events::StepObservation};
use kink_patch::{
    Baseline, CandidateGeneration, Discovery, Edit, Patch, SelectionPolicy, SiteSelector, TermRef,
    derive_sites, select,
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
fn check_manifest(manifest: &CampaignManifest) {
    let value = manifest.value();
    keys(
        value,
        &[
            "schema",
            "version",
            "k_rust",
            "kink",
            "profile",
            "compile_options",
            "backend_options",
            "budget",
            "schedule",
            "module",
            "classifier",
            "operator",
            "baseline",
            "tests",
            "observation_sha256",
            "generation",
            "mutants",
        ],
    );
    keys(
        &value["k_rust"],
        &["revision", "provenance_format", "provenance_version"],
    );
    keys(
        &value["kink"],
        &["fingerprint", "canonical_patch", "compiled_kore"],
    );
    keys(
        &value["backend_options"],
        &["smt_timeout_ms", "smt_retry_limit"],
    );
    keys(
        &value["budget"],
        &[
            "time_ms",
            "max_simplification_iterations",
            "max_depth",
            "max_breadth",
        ],
    );
    keys(&value["operator"], &["id", "version", "policy"]);
    if value["operator"]["policy"].is_object() {
        keys(&value["operator"]["policy"], &["exact"]);
        keys(&value["operator"]["policy"]["exact"], &["tuples", "arity"]);
    }
    keys(
        &value["baseline"],
        &[
            "semantic_input_sha256",
            "artifact",
            "structure_sha256",
            "kore_sha256",
        ],
    );
    keys(&value["tests"], &["count", "sha256"]);
    keys(
        &value["generation"],
        &[
            "origins",
            "rejected_origins",
            "completeness",
            "failure",
            "scored",
        ],
    );
    for mutant in value["mutants"].as_array().unwrap() {
        keys(
            mutant,
            &[
                "mutant_id",
                "patch_sha256",
                "semantic_input_sha256",
                "structure_sha256",
                "kore_sha256",
                "validation",
            ],
        );
        keys(&mutant["validation"], &["outcome", "stage", "detail"]);
    }
    assert_eq!(value["schema"], "kink-campaign-manifest");
    assert_eq!(value["version"], 1);
    assert_eq!(
        value["profile"],
        if cfg!(feature = "z3") { "z3" } else { "no-z3" }
    );
    assert_eq!(
        value["baseline"]["semantic_input_sha256"],
        manifest.baseline_input().digest().to_string()
    );
    assert_eq!(
        value["baseline"]["artifact"],
        format!("semantic-input/{}.json", manifest.baseline_input().digest())
    );
    assert_eq!(
        manifest.digest(),
        kink_patch::payload_digest(
            kink_patch::CAMPAIGN_MANIFEST_DOMAIN,
            manifest.text().as_bytes()
        )
    );
    assert!(!manifest.text().contains(env!("CARGO_MANIFEST_DIR")));
    assert!(
        !manifest
            .baseline_input()
            .text()
            .contains(env!("CARGO_MANIFEST_DIR"))
    );
    fn walk(value: &Value, parent: &str) {
        match value {
            Value::Object(object) => {
                for (key, value) in object {
                    if key.ends_with("_ms") {
                        assert!(matches!(
                            (parent, key.as_str()),
                            ("budget", "time_ms") | ("backend_options", "smt_timeout_ms")
                        ));
                    }
                    walk(value, key);
                }
            }
            Value::Array(array) => {
                for value in array {
                    walk(value, parent);
                }
            }
            Value::String(text)
                if matches!(
                    parent,
                    "logical" | "artifact" | "org.kframework.attributes.Source"
                ) =>
            {
                assert!(
                    !std::path::Path::new(text).is_absolute(),
                    "absolute path: {text}"
                )
            }
            _ => {}
        }
    }
    walk(value, "");
    let artifact: Value = serde_json::from_str(manifest.baseline_input().text()).unwrap();
    walk(&artifact, "");
}
fn build<'a>(
    campaign: &'a Campaign<'a>,
    generation: &'a CandidateGeneration<'a>,
    version: u32,
) -> Result<CampaignManifest, ManifestError> {
    campaign_manifest(&ManifestInput {
        campaign,
        generation,
        schedule: ScheduleMode::Full,
        operator: OperatorId {
            id: "test",
            version,
            policy: SelectionPolicy::Each,
        },
        classifier: "normal",
    })
}
fn different_keys(a: &Value, b: &Value) -> Vec<String> {
    a.as_object()
        .unwrap()
        .keys()
        .filter(|key| a[*key] != b[*key])
        .cloned()
        .collect()
}

#[test]
fn counter_manifest_is_deterministic_and_declaration_changes_are_local() {
    let mut outputs = Vec::new();
    for _ in 0..2 {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let specs = step_support::counter(true);
        let tests = counter_tests(&specs);
        let generation = counter_generation(validator.baseline());
        let mut campaign = Campaign {
            validator: &validator,
            module: "COUNTER",
            observation: &specs,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let original = build(&campaign, &generation, 1).unwrap();
        check_manifest(&original);
        assert_eq!(
            original.value()["baseline"]["semantic_input_sha256"],
            "f997509eac63f303e54f078c721ca0e2bf9f7d780b82f60c88b39cfda9accb3d"
        );
        assert_eq!(
            original.value()["baseline"]["structure_sha256"],
            "4af7e670c3bdec82d0997ef284611fcff09d1ae538546dbea4abc9f047013373"
        );
        let mutants = original.value()["mutants"].as_array().unwrap();
        assert_eq!(mutants.len(), 4);
        assert_eq!(
            mutants[0]["validation"],
            json!({"outcome":"rejected","stage":"compilation","detail":"definition checks"})
        );
        for mutant in &mutants[1..] {
            assert_eq!(
                mutant["validation"],
                json!({"outcome":"compiled","stage":null,"detail":null})
            );
        }
        for (candidate, recorded) in generation.candidates().iter().zip(mutants) {
            let decoded =
                Patch::from_canonical_json(&candidate.patch.canonical_json().unwrap()).unwrap();
            assert_eq!(decoded, candidate.patch);
            assert_eq!(
                recorded["patch_sha256"],
                decoded.digest().unwrap().to_string()
            );
        }
        let changed_version = build(&campaign, &generation, 2).unwrap();
        assert_eq!(
            different_keys(original.value(), changed_version.value()),
            ["operator"]
        );
        campaign.budget.max_depth = Some(123);
        let changed_budget = build(&campaign, &generation, 1).unwrap();
        assert_eq!(
            different_keys(original.value(), changed_budget.value()),
            ["budget"]
        );
        campaign.budget = BUDGET;
        let mut changed_tests = tests.clone();
        changed_tests[0].initial_state = choose_state();
        campaign.tests = &changed_tests;
        let changed_state = build(&campaign, &generation, 1).unwrap();
        assert_eq!(
            different_keys(original.value(), changed_state.value()),
            ["tests"]
        );
        assert_eq!(
            different_keys(&original.value()["tests"], &changed_state.value()["tests"]),
            ["sha256"]
        );
        outputs.push(original.text());
    }
    assert_eq!(outputs[0], outputs[1]);
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "si02-counter-manifest-{}.json",
        if cfg!(feature = "z3") { "z3" } else { "no-z3" }
    ));
    std::fs::write(path, &outputs[0]).unwrap();
}

#[test]
fn coupled_manifest_is_deterministic() {
    let mut outputs = Vec::new();
    for _ in 0..2 {
        let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
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
        let manifest = campaign_manifest(&ManifestInput {
            campaign: &campaign,
            generation: &generation,
            schedule: ScheduleMode::Full,
            operator: OperatorId {
                id: "release-after-access",
                version: 1,
                policy: SelectionPolicy::Exact {
                    expected_tuple_count: 1,
                    expected_tuple_arity: 2,
                },
            },
            classifier: "normal",
        })
        .unwrap();
        check_manifest(&manifest);
        assert_eq!(
            manifest.value()["baseline"]["semantic_input_sha256"],
            "a554dcedd4b0bd2dcdfb65edfd24b207de4899acc68e26345caf5175e869cad3"
        );
        assert_eq!(
            manifest.value()["baseline"]["structure_sha256"],
            "87957ecd07877afe84beee0893c4aa7fbe3e0e714e0b4cb453604da7ce485f58"
        );
        assert_eq!(manifest.value()["mutants"].as_array().unwrap().len(), 1);
        let patch = &generation.candidates()[0].patch;
        assert_eq!(patch.edits().len(), 2);
        assert_eq!(
            Patch::from_canonical_json(&patch.canonical_json().unwrap()).unwrap(),
            *patch
        );
        outputs.push(manifest.text());
    }
    assert_eq!(outputs[0], outputs[1]);
}

#[test]
fn foreign_generation_operator_mismatch_and_nondefault_options_are_refused() {
    let first = NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
    let second = NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
    let specs = step_support::counter(true);
    let tests = counter_tests(&specs);
    let generation = counter_generation(first.baseline());
    let campaign = Campaign {
        validator: &second,
        module: "COUNTER",
        observation: &specs,
        classify: &normal,
        tests: &tests,
        budget: BUDGET,
    };
    assert_eq!(
        build(&campaign, &generation, 1).unwrap_err(),
        ManifestError::ForeignGeneration
    );
    let campaign = Campaign {
        validator: &first,
        ..campaign
    };
    let input = ManifestInput {
        campaign: &campaign,
        generation: &generation,
        schedule: ScheduleMode::Full,
        operator: OperatorId {
            id: "other",
            version: 1,
            policy: SelectionPolicy::Each,
        },
        classifier: "normal",
    };
    assert_eq!(
        campaign_manifest(&input).unwrap_err(),
        ManifestError::OperatorMismatch
    );
    let validator = NativeValidator::bind(
        support::load("counter.k"),
        CompileOptions {
            kore_width: 80,
            ..CompileOptions::default()
        },
    );
    let generation = counter_generation(validator.baseline());
    let campaign = Campaign {
        validator: &validator,
        ..campaign
    };
    assert_eq!(
        build(&campaign, &generation, 1).unwrap_err(),
        ManifestError::NonDefaultCompileOptions
    );
}

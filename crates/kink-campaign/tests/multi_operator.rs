//! Multi-operator scheduling, data replay and record-only declaration census.
#[path = "../../../testdata/k/step_support.rs"]
mod step_support;
#[path = "../../../testdata/k/support.rs"]
mod support;
use k_rust::{builtin, kompile::CompileOptions, kore::ast::Pattern, outer::ResolvedSource};
use kink_campaign::*;
use kink_native::{
    NativeValidator, declaration_census, execution::ExecutionBudget, step_events::StepObservation,
};
use kink_patch::{
    Action, Baseline, CAMPAIGN_MANIFEST_DOMAIN, CandidateFailure, CandidateGeneration,
    ClaimSupport, Clause, Edit, OperatorSpec, Patch, SiteSelector, Universe, canonical_json,
    catalogue_v1, derive_sites, generate, payload_digest, resolve_universe, select,
};
use kink_pattern::{Atom, ExecutionTerminalKind, PatternArm, PatternPlan};
use serde_json::{Value, json};
use std::{path::Path, time::Duration};
const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: Some(32),
    max_breadth: None,
};
fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}
fn with_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}
fn code(b: &Baseline) -> Result<CandidateGeneration<'_>, CandidateFailure> {
    let discovery = derive_sites(
        b,
        "site",
        &[
            SiteSelector::RuleLabel("COUNTER.increment".into()),
            SiteSelector::Path(vec![0]),
        ],
    )?;
    select(&discovery, kink_patch::SelectionPolicy::Each, 1)?.fold("code", |_| {
        Patch::new(vec![Edit::AddAttribute {
            at: support::rule(b, "COUNTER.increment"),
            key: "foo".into(),
            value: json!(""),
        }])
        .unwrap()
    })
}
fn code_id() -> ManifestOperator<'static> {
    ManifestOperator::Code(OperatorId {
        id: "code",
        version: 1,
        policy: kink_patch::SelectionPolicy::Each,
    })
}
fn counter_tests(events: &[kink_native::step_events::StepEventSpec]) -> Vec<TestCase> {
    let vocabulary = StepObservation::vocabulary_of(events).unwrap();
    let pattern = |name: &str| {
        OracleDeclaration::new(
            CrashPolicy::CompareIdentity,
            Projection::Pattern {
                plan: PatternPlan::new(
                    &vocabulary,
                    vec![],
                    vec![PatternArm {
                        atoms: vec![Atom {
                            constructor: name.into(),
                            payload: vec![],
                        }],
                        relations: vec![],
                    }],
                    None,
                )
                .unwrap(),
                with_bindings: false,
            },
        )
        .unwrap()
    };
    let z = || support::app("Lblz", vec![]);
    let s = |x| support::app("Lbls", vec![x]);
    vec![
        TestCase {
            id: "counter".into(),
            initial_state: support::initial_state(
                support::app("Lblcounter", vec![z(), s(s(s(z())))]),
                "SortCounter",
            ),
            oracles: vec![pattern("increment")],
        },
        TestCase {
            id: "choose".into(),
            initial_state: support::initial_state(
                support::app(
                    "Lblchoose",
                    vec![Pattern::DomainValue {
                        sort: k_rust::kompile::initial_configuration::kore_sort("SortBool"),
                        value: "true".into(),
                    }],
                ),
                "SortControl",
            ),
            oracles: vec![pattern("branchTaken")],
        },
    ]
}
fn census_baseline(value: &Value) {
    for mutant in value["mutants"].as_array().unwrap() {
        assert_eq!(
            mutant["census"],
            if mutant["validation"]["outcome"] == "compiled" {
                json!("baseline")
            } else {
                Value::Null
            },
            "STOP: compiled declaration census differs: {mutant}"
        );
    }
}
fn no_timeout(value: &Value) {
    match value {
        Value::String(s) => assert!(
            !matches!(s.as_str(), "timeout" | "time-limit"),
            "STOP: time bound fired"
        ),
        Value::Array(a) => a.iter().for_each(no_timeout),
        Value::Object(o) => o.values().for_each(no_timeout),
        _ => (),
    }
}
#[test]
fn mixed_generations_equal_single_runs_and_replay_manifest_specs() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let events = step_support::counter(true);
        let tests = counter_tests(&events);
        let campaign = Campaign {
            validator: &validator,
            module: "COUNTER",
            observation: &events,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let universe = resolve_universe(validator.baseline(), &Universe::v1());
        let specs: Vec<_> = catalogue_v1()
            .into_iter()
            .filter(|s| matches!(s.id(), "cond-true" | "cond-false" | "delete-rule"))
            .collect();
        assert_eq!(specs.len(), 3);
        let mut generations: Vec<_> = specs
            .iter()
            .map(|s| generate(validator.baseline(), &universe, s, usize::MAX).unwrap())
            .collect();
        generations.push(code(validator.baseline()).unwrap());
        let mut operators: Vec<_> = specs.iter().map(ManifestOperator::Spec).collect();
        operators.push(code_id());
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let options = CampaignOptions {
                schedule,
                selection: SelectionPolicy::None,
                share_evidence: true,
            };
            let run = run_campaign_multi(&campaign, &generations, &options).unwrap();
            assert!(generations.iter().all(CandidateGeneration::scored));
            assert!(run.score.is_some());
            for (id, mutant) in run.mutants.iter().enumerate() {
                assert_eq!(mutant.report.mutant_id, MutantId(id));
            }
            let manifest = campaign_manifest_multi(&MultiManifestInput {
                campaign: &campaign,
                generations: &generations,
                operators: &operators,
                universe: Some(&universe),
                schedule,
                selection: SelectionPolicy::None,
                classifier: "normal",
            })
            .unwrap();
            assert_eq!(manifest.value()["admission"]["verdict"], "natural");
            census_baseline(manifest.value());
            let report = campaign_report_multi(&manifest, &campaign, &generations, &run).unwrap();
            no_timeout(report.value());
            let mut offset = 0;
            for (index, generation) in generations.iter().enumerate() {
                let alone = run_campaign(&campaign, generation, schedule).unwrap();
                for (local, mutant) in alone.mutants.iter().enumerate() {
                    let multi = &run.mutants[offset + local];
                    assert_eq!(
                        multi.report.status, mutant.report.status,
                        "STOP: multi status differs"
                    );
                    assert_eq!(
                        multi.report.killing_test_ids, mutant.report.killing_test_ids,
                        "STOP: multi killing tests differ"
                    );
                }
                assert_eq!(report.value()["summary"]["per_operator"][index]["score"], {
                    let single_manifest = campaign_manifest(&ManifestInput {
                        campaign: &campaign,
                        generation,
                        schedule,
                        selection: SelectionPolicy::None,
                        operators: &operators[index..index + 1],
                        classifier: "normal",
                    })
                    .unwrap();
                    let single =
                        campaign_report(&single_manifest, &campaign, generation, &alone).unwrap();
                    let singleton_run =
                        run_campaign_multi(&campaign, std::slice::from_ref(generation), &options)
                            .unwrap();
                    let multi_single = campaign_report_multi(
                        &single_manifest,
                        &campaign,
                        std::slice::from_ref(generation),
                        &singleton_run,
                    )
                    .unwrap();
                    assert_eq!(single.text(), multi_single.text());
                    single.value()["summary"]["score"].clone()
                });
                offset += generation.candidates().len();
            }
            let decoded: Vec<_> = manifest.value()["operators"].as_array().unwrap()[..3]
                .iter()
                .map(|op| OperatorSpec::from_canonical_json(&canonical_json(&op["spec"])).unwrap())
                .collect();
            let mut replay_ops: Vec<_> = decoded
                .iter()
                .map(|spec| ReplayOperator::Spec {
                    spec,
                    cap: usize::MAX,
                })
                .collect();
            replay_ops.push(ReplayOperator::Code {
                id: "code",
                version: 1,
                policy: kink_patch::SelectionPolicy::Each,
                select: &code,
            });
            let declaration = ReplayDeclaration {
                module: "COUNTER",
                observation: &events,
                classify: &normal,
                classifier: "normal",
                tests: &tests,
                budget: BUDGET,
                schedule,
                selection: SelectionPolicy::None,
                operators: &replay_ops,
            };
            assert_eq!(
                replay(
                    &report.text(),
                    manifest.baseline_input().text(),
                    &declaration
                ),
                ReplayOutcome::Reproduced,
                "STOP: untampered replay"
            );
            for row in 0..5 {
                let mut changed = report.value().clone();
                match row {
                    0 => changed["manifest"]["operators"][0]["spec"]["version"] = json!(2),
                    1 => changed["manifest"]["universe"]["excluded"]
                        .as_array_mut()
                        .unwrap()
                        .push(json!({"module":"COUNTER","index":0,"reason":"untyped"})),
                    2 => {
                        changed["manifest"]["admission"]["declarations"]["verdict"] =
                            json!("flagged")
                    }
                    3 => changed["manifest"]["mutants"][0]["operator"] = json!(3),
                    _ => changed["manifest"]["operators"]
                        .as_array_mut()
                        .unwrap()
                        .swap(0, 1),
                }
                changed["manifest_sha256"] = json!(
                    payload_digest(
                        CAMPAIGN_MANIFEST_DOMAIN,
                        canonical_json(&changed["manifest"]).as_bytes()
                    )
                    .to_string()
                );
                assert_eq!(
                    replay(
                        &canonical_json(&changed),
                        manifest.baseline_input().text(),
                        &declaration
                    ),
                    ReplayOutcome::Refused(ReplayRefusal::Declaration),
                    "tamper row {row}"
                );
            }
            if schedule == ScheduleMode::Full {
                println!("CS09_EXAMPLE_MANIFEST {}", manifest.text());
            }
        }
    });
}

#[test]
fn empty_capped_and_foreign_generations_do_not_claim_global_scores() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let events = step_support::counter(true);
        let tests = counter_tests(&events);
        let campaign = Campaign {
            validator: &validator,
            module: "COUNTER",
            observation: &events,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let universe = resolve_universe(validator.baseline(), &Universe::v1());
        let delete = catalogue_v1()
            .into_iter()
            .find(|s| s.id() == "delete-rule")
            .unwrap();
        let empty = OperatorSpec::new(
            "empty",
            "1",
            1,
            vec![Clause::Head {
                label: "absent".into(),
            }],
            Action::DeleteRule,
        )
        .unwrap();
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let options = CampaignOptions {
                schedule,
                selection: SelectionPolicy::None,
                share_evidence: true,
            };
            for extra in [
                generate(validator.baseline(), &universe, &empty, usize::MAX).unwrap(),
                generate(validator.baseline(), &universe, &delete, 1).unwrap(),
            ] {
                let generations = [code(validator.baseline()).unwrap(), extra];
                assert!(
                    run_campaign_multi(&campaign, &generations, &options)
                        .unwrap()
                        .score
                        .is_none()
                );
            }
            let foreign = support::load("counter.k");
            let generation = code(&foreign).unwrap();
            assert_eq!(
                run_campaign_multi(&campaign, &[generation], &options)
                    .unwrap_err()
                    .kind(),
                CampaignFailureKind::ForeignGeneration
            );
        }
    });
}

#[test]
fn flagged_census_records_without_refusing_the_campaign() {
    with_stack(|| {
        let validator = NativeValidator::bind(support::load("t13owk.k"), CompileOptions::default());
        let tests = [TestCase {
            id: "start".into(),
            initial_state: support::initial_state(
                support::app("Lblstart", vec![support::int(1)]),
                "SortProg",
            ),
            oracles: vec![
                OracleDeclaration::new(
                    CrashPolicy::CompareIdentity,
                    Projection::State(StateProjection::WholeTerm),
                )
                .unwrap(),
            ],
        }];
        let campaign = Campaign {
            validator: &validator,
            module: "T13OWK",
            observation: &[],
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let universe = resolve_universe(validator.baseline(), &Universe::v1());
        let spec = catalogue_v1()
            .into_iter()
            .find(|s| s.id() == "drop-owise")
            .unwrap();
        let generations = [generate(validator.baseline(), &universe, &spec, usize::MAX).unwrap()];
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let manifest = campaign_manifest_multi(&MultiManifestInput {
                campaign: &campaign,
                generations: &generations,
                operators: &[ManifestOperator::Spec(&spec)],
                universe: Some(&universe),
                schedule,
                selection: SelectionPolicy::None,
                classifier: "normal",
            })
            .unwrap();
            assert_eq!(manifest.value()["admission"]["verdict"], "flagged");
            census_baseline(manifest.value());
            // Re-pin R0a (finding E-13): at 927b9ce6 the flagged baseline ran (`addB`, INT.add
            // declared with result Bool, evaluated to Stuck `done(7)`) and the campaign was
            // reported. At 501f18b9 k-rust leaves an ill-sorted hook result unevaluated
            // (UnsupportedHookUnevaluated INT.add), so the baseline leaf is Indeterminate and the
            // baseline oracle refuses the campaign. The census still records without refusing:
            // the refusal is the baseline oracle's, not the census's.
            let refused = run_campaign_multi(
                &campaign,
                &generations,
                &CampaignOptions {
                    schedule,
                    selection: SelectionPolicy::None,
                    share_evidence: true,
                },
            )
            .expect_err("the baseline oracle refuses the undefined baseline");
            assert_eq!(
                refused.kind(),
                CampaignFailureKind::BaselineOracleFailed,
                "{schedule:?}"
            );
        }
    });
}

fn catalogue_census_for_fixture(name: &str, specs: &[OperatorSpec]) -> usize {
    let mut compiled = 0;
    let text = std::fs::read_to_string(Path::new(support::DIR).join(name)).unwrap();
    let module = text
        .lines()
        .filter_map(|l| l.trim().strip_prefix("module "))
        .next_back()
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .to_owned();
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("{required} is not embedded"))
    };
    let baseline = Baseline::load(
        ResolvedSource::new(name, text),
        &module,
        None,
        &mut resolver,
        &support::options(),
    )
    .unwrap_or_else(|error| panic!("CS-08 fixture {name} did not load: {error}"));
    let validator = NativeValidator::bind(baseline, CompileOptions::default());
    let Ok(baseline) = validator.compile_baseline() else {
        return 0;
    };
    let _ = declaration_census(&baseline).unwrap();
    let universe = resolve_universe(validator.baseline(), &Universe::v1());
    let generations = specs
        .iter()
        .map(|spec| generate(validator.baseline(), &universe, spec, usize::MAX).unwrap())
        .collect::<Vec<_>>();
    let operators = specs.iter().map(ManifestOperator::Spec).collect::<Vec<_>>();
    let campaign = Campaign {
        validator: &validator,
        module: &module,
        observation: &[],
        classify: &normal,
        tests: &[],
        budget: BUDGET,
    };
    for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
        let manifest = campaign_manifest_multi(&MultiManifestInput {
            campaign: &campaign,
            generations: &generations,
            operators: &operators,
            universe: Some(&universe),
            schedule,
            selection: SelectionPolicy::None,
            classifier: "normal",
        })
        .unwrap();
        census_baseline(manifest.value());
        if schedule == ScheduleMode::Full {
            compiled += manifest.value()["mutants"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|m| m["validation"]["outcome"] == "compiled")
                .count();
        }
    }
    println!("CS09_SWEEP_DEFINITION {name}");
    compiled
}

/// Milestone gate only (README, Gate): every catalogue mutant of every fixture, compiled
/// in both schedules. The per-commit gate runs
/// `compiled_catalogue_sweep_over_named_fixtures_preserves_the_baseline_declaration_census`.
#[test]
#[ignore = "milestone"]
fn compiled_catalogue_sweep_preserves_the_baseline_declaration_census() {
    with_stack(|| {
        let mut names: Vec<_> = std::fs::read_dir(support::DIR)
            .unwrap()
            .map(|e| e.unwrap().file_name().into_string().unwrap())
            .filter(|n| n.ends_with(".k"))
            .collect();
        names.sort();
        println!("CS09_SWEEP_FIXTURES {}", names.len());
        let specs = catalogue_v1();
        let compiled = std::thread::scope(|scope| {
            let handles = names
                .chunks(names.len().div_ceil(4).max(1))
                .map(|chunk| {
                    let specs = &specs;
                    std::thread::Builder::new()
                        .stack_size(16 * 1024 * 1024)
                        .spawn_scoped(scope, move || {
                            chunk
                                .iter()
                                .map(|name| catalogue_census_for_fixture(name, specs))
                                .sum::<usize>()
                        })
                        .unwrap()
                })
                .collect::<Vec<_>>();
            handles
                .into_iter()
                .map(|h| h.join().unwrap())
                .sum::<usize>()
        });
        assert!(compiled > 0);
        println!("CS09_SWEEP_COMPILED {compiled}");
    });
}

/// The fixtures of the per-commit catalogue sweep (flow F-01): counter.k (EI-D2=b),
/// guardedmem.k (G) and symmem.k, the coupled-capable store-and-load fixture whose
/// release-after-access mutant (K) writes two rules.
const NAMED_SWEEP_FIXTURES: [&str; 3] = ["counter.k", "guardedmem.k", "symmem.k"];

/// The per-commit variant of the milestone sweep: the full catalogue over the named
/// fixtures, each of which must compile some mutant.
#[test]
fn compiled_catalogue_sweep_over_named_fixtures_preserves_the_baseline_declaration_census() {
    with_stack(|| {
        let specs = catalogue_v1();
        let mut compiled = 0;
        for name in NAMED_SWEEP_FIXTURES {
            let count = catalogue_census_for_fixture(name, &specs);
            assert!(count > 0, "{name} compiles no catalogue mutant");
            compiled += count;
        }
        println!("CS09_SWEEP_NAMED_COMPILED {compiled}");
    });
}

#[test]
fn claim_withdrawn_side_is_recorded_as_baseline_census() {
    with_stack(|| {
        let validator = NativeValidator::bind(
            support::load_path(
                &Path::new(support::DIR).join("symbolic-claim-mutation.k"),
                "SYMPARTIAL",
            ),
            CompileOptions::default(),
        );
        let tests = [TestCase {
            id: "symbolic".into(),
            initial_state: support::initial_state(
                support::app(
                    "Lblseq",
                    vec![
                        support::app("Lblhalf", vec![support::var("X", "SortNat")]),
                        support::app("Lblhalt", vec![]),
                    ],
                ),
                "SortProg",
            ),
            oracles: vec![
                OracleDeclaration::new(
                    CrashPolicy::CompareIdentity,
                    Projection::State(StateProjection::WholeTerm),
                )
                .unwrap(),
            ],
        }];
        let campaign = Campaign {
            validator: &validator,
            module: "SYMPARTIAL",
            observation: &[],
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let universe = resolve_universe(validator.baseline(), &Universe::v1());
        let spec = OperatorSpec::new(
            "claim",
            "offset",
            1,
            vec![
                Clause::RuleLabel("SYMPARTIAL.d".into()),
                Clause::TokenOfSort {
                    sort: k_rust::kast::Sort::new("Int"),
                },
            ],
            Action::IntOffset(1),
        )
        .unwrap();
        let generation = generate(validator.baseline(), &universe, &spec, usize::MAX).unwrap();
        assert!(!generation.candidates().is_empty());
        let support = ClaimSupport::new(validator.baseline());
        for candidate in generation.candidates() {
            let withdrawal = support
                .withdraw(validator.baseline(), &candidate.patch)
                .unwrap();
            assert!(withdrawal.trusted());
            assert!(!withdrawal.withdrawn.is_empty());
            let side = validator.validate(withdrawal.patch().unwrap()).unwrap();
            assert_eq!(
                declaration_census(&side).unwrap(),
                declaration_census(&validator.compile_baseline().unwrap()).unwrap()
            );
        }
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let manifest = campaign_manifest_multi(&MultiManifestInput {
                campaign: &campaign,
                generations: std::slice::from_ref(&generation),
                operators: &[ManifestOperator::Spec(&spec)],
                universe: Some(&universe),
                schedule,
                selection: SelectionPolicy::None,
                classifier: "normal",
            })
            .unwrap();
            census_baseline(manifest.value());
        }
    });
}

//! CS-10 evidence sharing: its own tests (E2 identical patches with `same_as`, and a
//! duplicate spec across generations), and one differential test (flow F-01) that runs
//! the representative campaign set (`representative/mod.rs`) with sharing on and off in
//! both schedules, comparing complete typed runs and canonical report bytes. Until F-01
//! this file ran a copy of every campaign fixture of coupled.rs, end_to_end.rs,
//! replay.rs, report.rs and multi_operator.rs through the same comparison (127 tests);
//! the originals still run in their own files.
#[path = "../../../testdata/k/step_support.rs"]
mod step_support;
#[path = "../../../testdata/k/support.rs"]
mod support;

mod representative;

use kink_campaign::*;
use kink_patch::{CandidateGeneration, canonical_json};

/// Runs `generations` with evidence sharing on and off in Full and FirstKill. The
/// complete results must be equal, and so must the canonical report bytes when the
/// campaign is admitted. Returns the shared runs, Full first.
fn compare_sharing(
    campaign: &Campaign<'_>,
    generations: &[CandidateGeneration<'_>],
    options: &CampaignOptions,
) -> [Result<CampaignRun, CampaignFailure>; 2] {
    [ScheduleMode::Full, ScheduleMode::FirstKill].map(|schedule| {
        let mut on = options.clone();
        on.schedule = schedule;
        on.share_evidence = true;
        let mut off = on.clone();
        off.share_evidence = false;
        let shared = kink_campaign::run_campaign_multi(campaign, generations, &on);
        let separate = kink_campaign::run_campaign_multi(campaign, generations, &off);
        assert_eq!(shared, separate, "STOP: sharing changed the complete run");
        if let (Ok(shared), Ok(separate)) = (&shared, &separate) {
            // Code operator declarations suffice here: candidate identities are unchanged,
            // and this checks serialization as well as the complete typed evidence.
            let operators = generations
                .iter()
                .map(|generation| {
                    ManifestOperator::Code(OperatorId {
                        id: generation
                            .candidates()
                            .first()
                            .map_or("empty", |c| &c.operator),
                        version: 1,
                        policy: kink_patch::SelectionPolicy::Each,
                    })
                })
                .collect::<Vec<_>>();
            let manifest = campaign_manifest_multi(&MultiManifestInput {
                campaign,
                generations,
                schedule,
                selection: options.selection,
                operators: &operators,
                classifier: "dedup-fixture",
                universe: None,
            })
            .expect("fixture manifest");
            let a = campaign_report_multi(&manifest, campaign, generations, shared)
                .expect("shared report");
            let b = campaign_report_multi(&manifest, campaign, generations, separate)
                .expect("separate report");
            assert_eq!(a.text(), b.text(), "STOP: sharing changed report bytes");
        }
        shared
    })
}

fn run_campaign(
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    schedule: ScheduleMode,
) -> Result<CampaignRun, CampaignFailure> {
    run_campaign_with(
        campaign,
        generation,
        &CampaignOptions {
            schedule,
            selection: SelectionPolicy::None,
            share_evidence: true,
        },
    )
}

fn run_campaign_with(
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    options: &CampaignOptions,
) -> Result<CampaignRun, CampaignFailure> {
    run_campaign_multi(campaign, std::slice::from_ref(generation), options)
}

/// The runner facade of the own tests: every call is compared by [`compare_sharing`].
fn run_campaign_multi(
    campaign: &Campaign<'_>,
    generations: &[CandidateGeneration<'_>],
    options: &CampaignOptions,
) -> Result<CampaignRun, CampaignFailure> {
    let [full, first_kill] = compare_sharing(campaign, generations, options);
    match options.schedule {
        ScheduleMode::Full => full,
        ScheduleMode::FirstKill => first_kill,
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

fn normal(_: &k_rust::kore::ast::Pattern) -> kink_pattern::ExecutionTerminalKind {
    kink_pattern::ExecutionTerminalKind::Normal
}

fn duplicate_generation(
    baseline: &kink_patch::Baseline,
) -> Result<CandidateGeneration<'_>, kink_patch::CandidateFailure> {
    use k_rust::{
        definition::Sentence,
        kast::{Sort, Term},
    };
    use kink_patch::{Discovery, Edit, Patch, SiteSelector, TermRef, derive_sites, select};
    let mut discovery = Discovery::empty(baseline, false, false);
    for path in [vec![0], vec![1]] {
        discovery = discovery.union(&derive_sites(
            baseline,
            "site",
            &[
                SiteSelector::RuleLabel("COUNTER.branch".into()),
                SiteSelector::Path(path),
            ],
        )?)?;
    }
    let at = support::rule(baseline, "COUNTER.branch");
    let term_at = TermRef::new(at.clone(), [1]);
    let false_term = Term::Token {
        token: "false".into(),
        sort: Sort::new("Bool"),
    };
    let mut replacement = baseline.sentence(&at).unwrap().clone();
    let Sentence::Rule { requires, .. } = &mut replacement else {
        panic!("rule");
    };
    *requires = false_term.clone();
    select(&discovery, kink_patch::SelectionPolicy::Each, 2)?.fold("duplicates", |origin| {
        Patch::new(vec![if origin.site_tuple[0].path.0 == [0] {
            Edit::ReplaceSentence {
                at: at.clone(),
                replacement: replacement.clone(),
            }
        } else {
            Edit::ReplaceTerm {
                at: term_at.clone(),
                expected: baseline.term(&term_at).unwrap().clone(),
                replacement: false_term.clone(),
            }
        }])
        .unwrap()
    })
}

fn counter_test() -> TestCase {
    TestCase {
        id: "choose".into(),
        initial_state: support::initial_state(
            support::app(
                "Lblchoose",
                vec![k_rust::kore::ast::Pattern::DomainValue {
                    sort: k_rust::kompile::initial_configuration::kore_sort("SortBool"),
                    value: "true".into(),
                }],
            ),
            "SortControl",
        ),
        oracles: vec![
            OracleDeclaration::new(
                CrashPolicy::CompareIdentity,
                Projection::State(StateProjection::WholeTerm),
            )
            .unwrap(),
        ],
    }
}

const BUDGET: kink_native::execution::ExecutionBudget = kink_native::execution::ExecutionBudget {
    time: std::time::Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: Some(32),
    max_breadth: None,
};

#[test]
fn distinct_term_and_sentence_patches_share_structure_and_replay_same_as() {
    with_stack(|| {
        let validator = kink_native::NativeValidator::bind(
            support::load("counter.k"),
            k_rust::kompile::CompileOptions::default(),
        );
        let tests = [counter_test()];
        let campaign = Campaign {
            validator: &validator,
            module: "COUNTER",
            observation: &[],
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let generation = duplicate_generation(validator.baseline()).unwrap();
        assert_eq!(generation.candidates().len(), 2);
        assert_ne!(
            generation.candidates()[0].patch,
            generation.candidates()[1].patch
        );
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let operators = [ManifestOperator::Code(OperatorId {
                id: "duplicates",
                version: 1,
                policy: kink_patch::SelectionPolicy::Each,
            })];
            let manifest = campaign_manifest(&ManifestInput {
                campaign: &campaign,
                generation: &generation,
                schedule,
                selection: SelectionPolicy::None,
                operators: &operators,
                classifier: "normal",
            })
            .unwrap();
            let mutants = manifest.value()["mutants"].as_array().unwrap();
            assert_eq!(mutants[0]["same_as"], serde_json::Value::Null);
            assert_eq!(mutants[1]["same_as"], 0);
            for key in ["structure_sha256", "kore_sha256"] {
                assert!(mutants[0][key].is_string());
                assert_eq!(mutants[0][key], mutants[1][key]);
            }
            assert_ne!(mutants[0]["patch_sha256"], mutants[1]["patch_sha256"]);
            let run = run_campaign(&campaign, &generation, schedule).unwrap();
            assert_eq!(run.mutants[0].report.status, run.mutants[1].report.status);
            assert_eq!(run.score.unwrap().denominator, 1);
            let report = campaign_report(&manifest, &campaign, &generation, &run).unwrap();
            let declaration = ReplayDeclaration {
                module: "COUNTER",
                observation: &[],
                classify: &normal,
                classifier: "normal",
                tests: &tests,
                budget: BUDGET,
                schedule,
                selection: SelectionPolicy::None,
                operators: &[ReplayOperator::Code {
                    id: "duplicates",
                    version: 1,
                    policy: kink_patch::SelectionPolicy::Each,
                    select: &duplicate_generation,
                }],
            };
            assert_eq!(
                replay(
                    &report.text(),
                    manifest.baseline_input().text(),
                    &declaration
                ),
                ReplayOutcome::Reproduced
            );
            for tamper in [serde_json::Value::Null, serde_json::json!(1)] {
                let mut changed = report.value().clone();
                changed["manifest"]["mutants"][1]["same_as"] = tamper;
                changed["manifest_sha256"] = serde_json::json!(
                    kink_patch::payload_digest(
                        kink_patch::CAMPAIGN_MANIFEST_DOMAIN,
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
                    ReplayOutcome::Refused(ReplayRefusal::Declaration)
                );
            }
        }
    });
}

#[test]
fn duplicate_spec_across_generations_counts_once_in_global_score() {
    with_stack(|| {
        let validator = kink_native::NativeValidator::bind(
            support::load("counter.k"),
            k_rust::kompile::CompileOptions::default(),
        );
        let tests = [counter_test()];
        let campaign = Campaign {
            validator: &validator,
            module: "COUNTER",
            observation: &[],
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let universe =
            kink_patch::resolve_universe(validator.baseline(), &kink_patch::Universe::v1());
        let spec = kink_patch::catalogue_v1()
            .into_iter()
            .find(|s| s.id() == "cond-false")
            .unwrap();
        let generations = [
            kink_patch::generate(validator.baseline(), &universe, &spec, usize::MAX).unwrap(),
            kink_patch::generate(validator.baseline(), &universe, &spec, usize::MAX).unwrap(),
        ];
        let count = generations[0].candidates().len();
        assert!(count > 0);
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let options = CampaignOptions {
                schedule,
                selection: SelectionPolicy::None,
                share_evidence: true,
            };
            let alone = run_campaign_with(&campaign, &generations[0], &options).unwrap();
            let duplicated = run_campaign_multi(&campaign, &generations, &options).unwrap();
            assert_eq!(duplicated.score, alone.score);
            let manifest = campaign_manifest_multi(&MultiManifestInput {
                campaign: &campaign,
                generations: &generations,
                schedule,
                selection: SelectionPolicy::None,
                operators: &[ManifestOperator::Spec(&spec), ManifestOperator::Spec(&spec)],
                classifier: "normal",
                universe: Some(&universe),
            })
            .unwrap();
            for i in 0..count {
                assert_eq!(manifest.value()["mutants"][count + i]["same_as"], i);
                assert_eq!(
                    duplicated.mutants[i].report.status,
                    duplicated.mutants[count + i].report.status
                );
            }
            let report =
                campaign_report_multi(&manifest, &campaign, &generations, &duplicated).unwrap();
            assert_eq!(
                report.value()["summary"]["score"],
                serde_json::json!({ "denominator": alone.score.unwrap().denominator, "killed": alone.score.unwrap().killed, "ratio": alone.score.unwrap().ratio.map(|r| serde_json::json!({"numerator": r.numerator, "denominator": r.denominator})), "survived": alone.score.unwrap().survived })
            );
        }
    });
}

/// F-01: evidence sharing changes no complete run and no report byte of any case of the
/// representative set, in either schedule, and each case keeps what its original test
/// pins.
#[test]
fn sharing_preserves_every_representative_campaign() {
    with_stack(|| {
        let mut coverage = representative::Coverage::default();
        representative::representative_set(&mut |case| {
            eprintln!("F01_DEDUP_CASE {}", case.name);
            let [full, first_kill] = compare_sharing(
                &case.campaign,
                &case.generations,
                &CampaignOptions {
                    schedule: ScheduleMode::Full,
                    selection: SelectionPolicy::None,
                    share_evidence: true,
                },
            );
            representative::check_expected(case, &full, &first_kill);
            coverage.record(case, &full);
        });
        coverage.assert_complete();
    });
}

//! Dry-run structure costs and explicitly declared, unscored samples.
#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::{kompile::CompileOptions, kore::ast::Pattern};
use kink_campaign::*;
use kink_native::{NativeValidator, execution::ExecutionBudget};
use kink_patch::{
    Action, CAMPAIGN_MANIFEST_DOMAIN, CandidateDisposition, CandidateFailureKind, Clause,
    Completeness, OperatorSpec, PatchFailureKind, Universe, apply, canonical_json, catalogue_v1,
    generate, payload_digest, resolve_universe, structure_sha256,
};
use kink_pattern::ExecutionTerminalKind;
use serde_json::{Value, json};
use std::{collections::BTreeSet, time::Duration};

const EXECUTION_BUDGET: ExecutionBudget = ExecutionBudget {
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

fn delete_rule() -> OperatorSpec {
    catalogue_v1()
        .into_iter()
        .find(|spec| spec.id() == "delete-rule")
        .unwrap()
}

fn no_timeout(value: &Value) {
    match value {
        Value::String(value) => assert!(
            !matches!(value.as_str(), "timeout" | "time-limit"),
            "STOP: time bound fired"
        ),
        Value::Array(values) => values.iter().for_each(no_timeout),
        Value::Object(values) => values.values().for_each(no_timeout),
        _ => (),
    }
}

#[test]
fn deterministic_plan_counts_populations_rejections_and_global_structures() {
    with_stack(|| {
        let first = support::load("counter.k");
        let second = support::load("counter.k");
        let first_universe = resolve_universe(&first, &Universe::v1());
        let second_universe = resolve_universe(&second, &Universe::v1());
        let delete = delete_rule();
        let rejected = OperatorSpec::new(
            "no-change",
            "absent-attribute",
            1,
            vec![
                Clause::RuleLabel("COUNTER.increment".into()),
                Clause::Path(vec![0]),
            ],
            Action::RemoveAttribute {
                key: "absent".into(),
            },
        )
        .unwrap();
        let specs = [delete.clone(), delete, rejected];
        let budget = BudgetMutants {
            per_spec_max: 2,
            total_max: 3,
            seed: vec![0, 1, 254, 255],
        };
        for sample in [None, Some(&budget)] {
            let plan = campaign_plan(&first, &first_universe, &specs, sample);
            assert_eq!(
                plan.text().unwrap(),
                campaign_plan(&second, &second_universe, &specs, sample)
                    .text()
                    .unwrap()
            );
            let limits = sample.map(|b| (b.per_spec_max, b.total_max, b.seed.as_slice()));
            let inputs = specs.iter().map(|s| (s, usize::MAX)).collect::<Vec<_>>();
            let generations =
                OperatorSpec::generate_all(&first, &first_universe, &inputs, limits).unwrap();
            let mut global_structures = BTreeSet::new();
            let mut per_operator_structures = 0;
            for ((spec, generation), row) in specs
                .iter()
                .zip(&generations)
                .zip(plan.value().unwrap()["operators"].as_array().unwrap())
            {
                let full = generate(&first, &first_universe, spec, usize::MAX).unwrap();
                let origins = json!(
                    full.selected_origins()
                        .iter()
                        .map(|origin| json!(origin.site_tuple.iter().map(|at| {
                            json!({"module":at.sentence.module,"index":at.sentence.index,"path":at.path.0})
                        }).collect::<Vec<_>>()))
                        .collect::<Vec<_>>()
                );
                let population_sha256 =
                    payload_digest("kink/population/v1", canonical_json(&origins).as_bytes());
                assert_eq!(
                    spec.population(&first, &first_universe).unwrap(),
                    (full.selected_origins().len() as u64, population_sha256)
                );
                let structures = generation
                    .candidates()
                    .iter()
                    .map(|candidate| {
                        structure_sha256(apply(&first, &candidate.patch).unwrap().definition())
                            .unwrap()
                    })
                    .collect::<BTreeSet<_>>();
                let rejected_origins = generation
                    .dispositions()
                    .iter()
                    .filter(|d| matches!(d, CandidateDisposition::Rejected(_)))
                    .count();
                assert_eq!(
                    row,
                    &json!({
                        "spec_sha256":spec.digest().to_string(),
                        "population":full.selected_origins().len(),
                        "population_sha256":population_sha256.to_string(),
                        "origins":generation.selected_origins().len(),
                        "rejected_origins":rejected_origins,
                        "candidates":generation.candidates().len(),
                        "distinct_structures":structures.len(),
                    })
                );
                per_operator_structures += structures.len();
                global_structures.extend(structures);
            }
            assert_eq!(plan.value().unwrap()["schema"], "kink-campaign-plan");
            assert_eq!(plan.value().unwrap()["version"], 1);
            assert_eq!(
                plan.value().unwrap()["compilations"],
                global_structures.len()
            );
            if sample.is_none() {
                assert!(global_structures.len() < per_operator_structures);
                let rejected = &generations[2];
                assert!(!rejected.selected_origins().is_empty());
                assert!(rejected.candidates().is_empty());
                assert!(rejected.dispositions().iter().all(|disposition| {
                    matches!(disposition, CandidateDisposition::Rejected(failure)
                        if failure.kind() == PatchFailureKind::NoChange)
                }));
            }
        }
    });
}

#[test]
fn sampled_campaigns_remain_unscored_and_replay_requires_the_declared_budget() {
    with_stack(|| {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let tests = [TestCase {
            id: "counter".into(),
            initial_state: support::initial_state(
                support::app(
                    "Lblcounter",
                    vec![
                        support::app("Lblz", vec![]),
                        support::app("Lbls", vec![support::app("Lblz", vec![])]),
                    ],
                ),
                "SortCounter",
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
            module: "COUNTER",
            observation: &[],
            classify: &normal,
            tests: &tests,
            budget: EXECUTION_BUDGET,
        };
        let universe = resolve_universe(validator.baseline(), &Universe::v1());
        let specs = [delete_rule(), delete_rule()];
        let budget = BudgetMutants {
            per_spec_max: 2,
            total_max: 2,
            seed: vec![0, 1, 254, 255],
        };
        let inputs = specs.iter().map(|s| (s, usize::MAX)).collect::<Vec<_>>();
        let generations = OperatorSpec::generate_all(
            validator.baseline(),
            &universe,
            &inputs,
            Some((budget.per_spec_max, budget.total_max, &budget.seed)),
        )
        .unwrap();
        assert_eq!(
            generations
                .iter()
                .map(|g| g.selected_origins().len())
                .sum::<usize>(),
            2
        );
        for generation in &generations {
            assert_eq!(generation.completeness(), Completeness::Incomplete);
            assert_eq!(generation.failure(), Some(CandidateFailureKind::Sampled));
            assert!(!generation.scored(), "STOP: sampled generation scored");
        }
        let operators = specs.iter().map(ManifestOperator::Spec).collect::<Vec<_>>();
        let replay_operators = specs
            .iter()
            .map(|spec| ReplayOperator::Spec {
                spec,
                cap: usize::MAX,
            })
            .collect::<Vec<_>>();
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let run = run_campaign_multi(
                &campaign,
                &generations,
                &CampaignOptions {
                    schedule,
                    selection: SelectionPolicy::None,
                    share_evidence: true,
                },
            )
            .unwrap();
            assert!(run.score.is_none(), "STOP: sampled campaign scored");
            let manifest = campaign_manifest_multi_with_budget(
                &MultiManifestInput {
                    campaign: &campaign,
                    generations: &generations,
                    operators: &operators,
                    universe: Some(&universe),
                    schedule,
                    selection: SelectionPolicy::None,
                    classifier: "normal",
                },
                Some(&budget),
            )
            .unwrap();
            assert_eq!(
                manifest.value()["budget_mutants"],
                json!({"per_spec_max":2,"total_max":2,"seed":"0001feff"})
            );
            for ((operator, generation), spec) in manifest.value()["operators"]
                .as_array()
                .unwrap()
                .iter()
                .zip(&generations)
                .zip(&specs)
            {
                let (population, digest) =
                    spec.population(validator.baseline(), &universe).unwrap();
                assert_eq!(operator["population"], population);
                assert_eq!(operator["population_sha256"], digest.to_string());
                assert!(population > generation.selected_origins().len() as u64);
                assert_eq!(operator["generation"]["failure"], "sampled");
                assert_eq!(operator["generation"]["scored"], false);
                assert_eq!(
                    operator["sampling"],
                    json!({
                        "seed":"0001feff", "size":generation.selected_origins().len(),
                        "population":operator["population"],
                    })
                );
            }
            let report = campaign_report_multi(&manifest, &campaign, &generations, &run).unwrap();
            no_timeout(report.value());
            assert!(report.value()["summary"]["score"].is_null());
            for (index, row) in report.value()["summary"]["per_operator"]
                .as_array()
                .unwrap()
                .iter()
                .enumerate()
            {
                assert!(row["score"].is_null());
                let tally = row["tally"].as_object().unwrap();
                let total: u64 = tally
                    .iter()
                    .filter(|(key, _)| key.as_str() != "rejected_origins")
                    .map(|(_, count)| count.as_u64().unwrap())
                    .sum();
                assert_eq!(total, generations[index].candidates().len() as u64);
            }
            let declaration = ReplayDeclaration {
                module: "COUNTER",
                observation: &[],
                classify: &normal,
                classifier: "normal",
                tests: &tests,
                budget: EXECUTION_BUDGET,
                schedule,
                selection: SelectionPolicy::None,
                operators: &replay_operators,
            };
            let artifact = manifest.baseline_input().text();
            assert_eq!(
                replay_with_budget(&report.text(), artifact, &declaration, Some(&budget)),
                ReplayOutcome::Reproduced,
                "STOP: sampled replay differs"
            );
            for row in 0..5 {
                let mut changed = report.value().clone();
                match row {
                    0 => changed["manifest"]["budget_mutants"]["seed"] = json!("01"),
                    1 => changed["manifest"]["operators"][0]["sampling"]["seed"] = json!("01"),
                    2 => changed["manifest"]["operators"][0]["sampling"]["size"] = json!(99),
                    3 => changed["manifest"]["operators"][0]["sampling"]["population"] = json!(99),
                    _ => {
                        changed["manifest"]["operators"][0]["population_sha256"] =
                            json!("00".repeat(32))
                    }
                }
                changed["manifest_sha256"] = json!(
                    payload_digest(
                        CAMPAIGN_MANIFEST_DOMAIN,
                        canonical_json(&changed["manifest"]).as_bytes(),
                    )
                    .to_string()
                );
                assert_eq!(
                    replay_with_budget(
                        &canonical_json(&changed),
                        artifact,
                        &declaration,
                        Some(&budget)
                    ),
                    ReplayOutcome::Refused(ReplayRefusal::Declaration),
                    "tamper row {row}"
                );
            }
            assert_eq!(
                replay(&report.text(), artifact, &declaration),
                ReplayOutcome::Refused(ReplayRefusal::Declaration)
            );
            let mismatched = BudgetMutants {
                total_max: 3,
                ..budget.clone()
            };
            assert_eq!(
                replay_with_budget(&report.text(), artifact, &declaration, Some(&mismatched)),
                ReplayOutcome::Refused(ReplayRefusal::Declaration)
            );
        }
    });
}

//! Re-pin L1-3 deliverable 3: compiling ahead changes nothing a campaign reports. A campaign of
//! two generations of structurally equal patches (every later candidate `same_as` the first)
//! runs with 1, 2 and 5 compile workers in Full and FirstKill: the complete typed runs, the
//! canonical manifest bytes and the canonical report bytes must be equal. Every case of the
//! representative campaign set (`representative/mod.rs`, flow F-01) runs through the same
//! comparison in `representative_set.rs` (test-gate TG-C).
#[path = "../../../testdata/k/step_support.rs"]
mod step_support;
#[path = "../../../testdata/k/support.rs"]
mod support;

use kink_campaign::*;
use kink_patch::CandidateGeneration;

const WORKERS: [usize; 3] = [1, 2, 5];

/// Runs `generations` with every count of [`WORKERS`] in Full and FirstKill and requires equal
/// complete runs, manifests and reports. Returns the 1-worker runs, Full first.
fn compare_workers(
    campaign: &Campaign<'_>,
    generations: &[CandidateGeneration<'_>],
) -> [Result<CampaignRun, CampaignFailure>; 2] {
    if campaign.validator.compile_workers(2) < 2 {
        // Review L1-3-1 D3: one CPU, or a memory allowance too small for two workers.
        eprintln!(
            "this host allows one compile worker: every worker count runs the sequential path, \
             so the comparison is vacuous here"
        );
    }
    [ScheduleMode::Full, ScheduleMode::FirstKill].map(|schedule| {
        let runs = WORKERS.map(|compile_workers| {
            run_campaign_multi(
                campaign,
                generations,
                &CampaignOptions {
                    schedule,
                    selection: SelectionPolicy::None,
                    share_evidence: true,
                    run: RunOptions::default(),
                    compile_workers,
                },
            )
        });
        for (workers, run) in WORKERS.iter().zip(&runs).skip(1) {
            assert_eq!(
                run, &runs[0],
                "STOP: {workers} compile workers changed the complete run"
            );
        }
        if let Ok(sequential) = &runs[0] {
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
            let manifest = || {
                campaign_manifest_multi(&MultiManifestInput {
                    campaign,
                    generations,
                    schedule,
                    selection: SelectionPolicy::None,
                    operators: &operators,
                    classifier: "compile-workers-fixture",
                    universe: None,
                })
                .expect("fixture manifest")
            };
            let reference = manifest();
            let report = campaign_report_multi(&reference, campaign, generations, sequential)
                .expect("1-worker report")
                .text();
            for (workers, run) in WORKERS.iter().zip(&runs).skip(1) {
                let again = manifest();
                assert_eq!(
                    again.text(),
                    reference.text(),
                    "STOP: manifest bytes ({workers} workers)"
                );
                let run = run.as_ref().expect("an admitted run");
                assert_eq!(
                    campaign_report_multi(&again, campaign, generations, run)
                        .expect("report")
                        .text(),
                    report,
                    "STOP: {workers} compile workers changed the report bytes"
                );
            }
        }
        let [first, ..] = runs;
        first
    })
}

fn with_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap();
}

/// Two generations of the same pair of patches on `COUNTER.branch`: its requires clause replaced
/// by `false` once as a sentence, once as a term. The four candidates have one structure.
fn duplicates(baseline: &kink_patch::Baseline) -> Vec<CandidateGeneration<'_>> {
    use k_rust::{
        definition::Sentence,
        kast::{Sort, Term},
    };
    use kink_patch::{Discovery, Edit, Patch, SiteSelector, TermRef, derive_sites, select};
    let mut discovery = Discovery::empty(baseline, false, false);
    for path in [vec![0], vec![1]] {
        discovery = discovery
            .union(
                &derive_sites(
                    baseline,
                    "site",
                    &[
                        SiteSelector::RuleLabel("COUNTER.branch".into()),
                        SiteSelector::Path(path),
                    ],
                )
                .unwrap(),
            )
            .unwrap();
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
    let generation = || {
        select(&discovery, kink_patch::SelectionPolicy::Each, 2)
            .unwrap()
            .fold("duplicates", |origin| {
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
            .unwrap()
    };
    vec![generation(), generation()]
}

mod kink_tier {
    use super::*;

    /// The duplicates campaign under every worker count; its 1-worker Full run pairs every later
    /// candidate with the first. The representative set's cases are compared in
    /// `representative_set.rs`, which also requires the minimum this comparison had over the set
    /// (two campaigns with several candidates, one candidate refused before any test).
    #[test]
    #[ignore = "kink"]
    fn compile_workers_preserve_a_campaign_of_structurally_equal_patches() {
        with_stack(|| {
            let validator = kink_native::NativeValidator::bind(
                support::load("counter.k"),
                k_rust::kompile::CompileOptions::default(),
            );
            let tests = ["true", "false"].map(|value| TestCase {
                id: format!("choose-{value}"),
                initial_state: support::initial_state(
                    support::app(
                        "Lblchoose",
                        vec![k_rust::kore::ast::Pattern::DomainValue {
                            sort: k_rust::kompile::initial_configuration::kore_sort("SortBool"),
                            value: value.into(),
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
            });
            let campaign = Campaign {
                validator: &validator,
                module: "COUNTER",
                observation: &[],
                classify: &|_| kink_pattern::ExecutionTerminalKind::Normal,
                tests: &tests,
                budget: kink_native::execution::ExecutionBudget {
                    time: std::time::Duration::from_secs(30),
                    max_simplification_iterations: 1000,
                    max_depth: Some(32),
                    max_breadth: None,
                },
            };
            let generations = duplicates(validator.baseline());
            let [full, _] = compare_workers(&campaign, &generations);
            let same_as = full
                .expect("the duplicates campaign")
                .mutants
                .iter()
                .map(|mutant| mutant.same_as)
                .collect::<Vec<_>>();
            assert_eq!(
                same_as,
                [
                    None,
                    Some(MutantId(0)),
                    Some(MutantId(0)),
                    Some(MutantId(0))
                ]
            );
        });
    }
}

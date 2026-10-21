//! Re-pin L1-2 (ANALYSIS.md section 4 decision 6, finding A-15's test): the one-sided kill's
//! differential. A work-bound mutant run kills one-sidedly when its explored part holds a clean,
//! ground, stuck final configuration whose projection the baseline's complete set lacks
//! (kink-campaign `OneSided`). The rule never needs the unbounded run, so this test runs it: for
//! every mutation and every program on which the mutant's unbounded run compares (each slot
//! `agree` or `distinguish`), it re-runs the mutant under work budgets below the run's own work
//! `w` (`w - 1`, `w / 2`, `w / 4`, ... down to 1, or only the first two in the gate) with the rule
//! on, and fails unless every slot of every bounded run is the unbounded run's outcome or
//! `unknown`. So every one-sided kill agrees with the two-sided verdict, and no one-sided kill
//! occurs where the unbounded run agrees. It also checks that each bounded run did end at its
//! work budget, and counts the one-sided kills (a `distinguish` whose mutant side is `unknown`).
//!
//! Pairs whose unbounded run does not compare (re-pin L1-2-fix-1, L1-2 review minor 2) are run
//! too. When that run finished without a bound (no timeout, every leaf stuck, an undefined step
//! or vacuous), the same ladder runs, every bounded slot must be `unknown` or `distinguish`, and
//! every one-sided kill must be explained: the unbounded run is unknown only because of a
//! contradicted claim or a terminal that is not a value on a leaf other than the killing one
//! (`testdata/k/one_sided_support.rs`; the per-path principle, root README "What a kill
//! trusts"); anything else fails the test. Any other undecided pair (a timeout, a depth bound) is
//! re-run once under the manifest's own work budget, when it sets one (kink-flow's run), and must
//! not kill there: its unbounded run is itself bounded, so nothing can explain a kill.
//!
//! The campaign is kink-flow's: the fixed oracles (exit stop without a cell, whole term), the
//! all-normal classifier, state-set result runs, and the work budget `Calibrated { factor: 0,
//! floor: b }`, i.e. `max_work = b` on every mutant run.
//!
//! Both are `#[ignore]`d for their cost (every run compiles its mutant) and run and recorded in the
//! L1-2 and L1-2-fix-1 handoffs; the gate runs the exhaustive differential of the fixture `testdata/k/l1/onesided.k`
//! (kink-campaign `tests/one_sided.rs`), where one-sided kills do occur:
//! - the flow corpus (every `testdata/flow` manifest and its mutation lists), budgets `w - 1` and
//!   `w / 2` (about three minutes; at L1-2: 129 pairs compared, 174 bounded runs, 5 one-sided
//!   kills, all on pairs the unbounded run distinguishes);
//! - `examples/imp` and its 21 mutations, the whole halving ladder (about twelve minutes; at L1-2:
//!   136 pairs compared, 703 bounded runs, 25 one-sided kills on 23 of the 47 distinguished
//!   pairs, none on the 89 agreeing ones; the 11 pairs whose unbounded run hits `max_depth` are
//!   re-run under the manifest's `work_factor` and kill none).
//!
//! In the gate, `a_work_bound_mutant_run_kills_one_sidedly_through_the_flow` runs the rule end to
//! end through `kink-flow run` on a corpus built from that fixture: kink-flow turns the rule on,
//! reports the kill with `sides: null`, and caches it under the work budget's outcome key.

#[path = "../../../testdata/k/one_sided_support.rs"]
mod one_sided_support;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::Duration;

use kink_campaign::{
    BaselineSession, Campaign, CampaignOptions, MutantId, OneSided, OracleOutcome, OracleSide,
    RunOptions, ScheduleMode, SideRun, TestCase, TestRun, WorkBudget, run_campaign_multi_with,
};
use kink_corpus::runner::all_normal;
use kink_flow::search::{ProgramOrder, RunOptions as SearchOptions, run};
use kink_flow::{
    admit::admit,
    manifest::FlowManifest,
    mutation::{MutationList, resolve},
    results::{execution_budget, fixed_oracles},
};
use kink_native::execution::{HaltClass, ResultModality};
use kink_patch::{ClaimSupport, Withdrawal};
use serde_json::Value;

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Every manifest under `testdata/flow` (nested directories included), in path order.
fn flow_manifests() -> Vec<PathBuf> {
    let mut manifests = Vec::new();
    let mut pending = vec![repository().join("testdata/flow")];
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                pending.push(path);
            } else if path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("FLOW") && name.ends_with(".toml"))
            {
                manifests.push(path);
            }
        }
    }
    manifests.sort();
    manifests
}

/// The mutation lists beside `manifest` (`MUTATIONS*.toml`), in path order.
fn mutation_lists(manifest: &Path) -> Vec<PathBuf> {
    let mut lists = std::fs::read_dir(manifest.parent().unwrap())
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("MUTATIONS") && name.ends_with(".toml"))
        })
        .collect::<Vec<_>>();
    lists.sort();
    lists
}

/// Which budgets below a run's work `w` are tried.
#[derive(Clone, Copy)]
enum Ladder {
    /// `w - 1` and `w / 2`.
    Short,
    /// `w - 1`, then `w / 2`, `w / 4`, ... down to 1.
    Halving,
}

impl Ladder {
    fn budgets(self, work: u64) -> Vec<u64> {
        let mut budgets = BTreeSet::new();
        budgets.insert(work - 1);
        let mut budget = work / 2;
        while budget > 0 {
            budgets.insert(budget);
            if matches!(self, Self::Short) {
                break;
            }
            budget /= 2;
        }
        budgets.into_iter().rev().collect()
    }
}

#[derive(Debug, Default)]
struct Tally {
    /// Mutations whose claim-free mutant ran its tests.
    mutants: usize,
    /// (mutation, program) pairs whose unbounded mutant run compared, with its work.
    compared: usize,
    /// (mutation, program) pairs whose unbounded run distinguished on some slot.
    distinguished: usize,
    /// (mutation, program) pairs whose unbounded run agreed on every slot.
    agreed: usize,
    /// Pairs the unbounded run did not compare (timeout, unknown, failure), with its census. A
    /// pair whose unbounded run finished without a bound runs the ladder (`unclean`); every other
    /// one is re-run once under the manifest's own work budget, when it sets one (kink-flow's run).
    undecided: Vec<String>,
    /// Undecided pairs whose unbounded run finished without a bound, and so ran the ladder.
    unclean: Vec<String>,
    /// One-sided kills on an `unclean` pair, each with its explanation (offending and killing
    /// leaves of the unbounded run).
    explained: Vec<String>,
    /// One-sided kills on an undecided pair, which no two-sided verdict confirms.
    unconfirmed: Vec<String>,
    /// Bounded runs made.
    bounded_runs: usize,
    /// Every one-sided kill: (mutation, program, budget, work, slot).
    one_sided_kills: Vec<String>,
    /// The distinguished pairs some bounded run killed one-sidedly.
    killed_one_sidedly: BTreeSet<String>,
    /// Every bounded slot that was neither the unbounded outcome nor `unknown`, and every bounded
    /// run that did not end at its work budget.
    failed: Vec<String>,
}

const fn options(work: WorkBudget) -> CampaignOptions {
    CampaignOptions {
        schedule: ScheduleMode::Full,
        selection: kink_campaign::SelectionPolicy::None,
        share_evidence: true,
        run: RunOptions {
            result_modality: ResultModality::StateSet,
            work,
            one_sided: OneSided::NoCrashClassifier,
        },
        compile_workers: 1,
    }
}

trait Kills {
    fn kills_by_distinguish(&self) -> bool;
}

impl Kills for TestRun {
    fn kills_by_distinguish(&self) -> bool {
        matches!(self, Self::Compared(outcomes) if outcomes.contains(&OracleOutcome::Distinguish))
    }
}

fn mutant_sides<'a>(run: &'a kink_campaign::CampaignRun, test: &str) -> Option<&'a [OracleSide]> {
    let evidence = run.mutants[0]
        .evidence
        .iter()
        .find(|evidence| evidence.test_id == test)?;
    match &evidence.run {
        SideRun::Sides { sides } => Some(sides),
        SideRun::Failed(_) => None,
    }
}

fn differential(manifest_path: &Path, time: Option<Duration>, ladder: Ladder, tally: &mut Tally) {
    let manifest = FlowManifest::read(manifest_path).unwrap();
    let admission = admit(&manifest);
    let Some(spec) = admission.spec.as_ref() else {
        return;
    };
    let label = manifest_path
        .strip_prefix(repository())
        .unwrap_or(manifest_path)
        .display()
        .to_string();
    let mut budget = execution_budget(manifest.budget);
    if let Some(time) = time {
        budget.time = time;
    }
    let tests = admission
        .programs
        .iter()
        .filter_map(|program| {
            let test = program.outcome.as_ref().ok()?;
            Some(TestCase {
                id: program.id.clone(),
                initial_state: test.initial_state.clone(),
                oracles: fixed_oracles(),
            })
        })
        .collect::<Vec<_>>();
    if tests.is_empty() {
        return;
    }
    let module = k_rust::kast::identifier::encode(&manifest.spec.main_module);
    let campaign = |tests| Campaign {
        validator: &spec.validator,
        module: &module,
        observation: &[],
        classify: &all_normal,
        tests,
        budget,
    };
    let baseline = spec.validator.baseline();
    let mut session = BaselineSession::new(&spec.validator);
    let mut digests = BTreeSet::new();
    for list in mutation_lists(manifest_path) {
        for mutation in MutationList::read(&list).unwrap().mutations {
            let Ok(mutation) = resolve(&manifest, &spec.loaded, &mutation) else {
                continue;
            };
            if !digests.insert(mutation.digest) {
                continue;
            }
            let Ok(generation) = mutation.generation(baseline) else {
                continue;
            };
            let generations = std::slice::from_ref(&generation);
            // The two-sided verdicts: every program, no work budget.
            let Ok(reference) = run_campaign_multi_with(
                &campaign(&tests),
                generations,
                &options(WorkBudget::Unbounded),
                &mut session,
            ) else {
                // The baseline is refused: the flow does not compare this manifest.
                return;
            };
            let [mutant] = reference.mutants.as_slice() else {
                panic!("{label}: one mutant");
            };
            if mutant.plan.mutant_failure.is_some() {
                continue;
            }
            tally.mutants += 1;
            let works = tests
                .iter()
                .map(|test| {
                    session
                        .last_call()
                        .mutant_run(MutantId(0), &test.id)
                        .and_then(|recording| recording.census.work)
                })
                .collect::<Vec<_>>();
            let censuses = tests
                .iter()
                .map(|test| {
                    session
                        .last_call()
                        .mutant_run(MutantId(0), &test.id)
                        .map(|recording| recording.census.clone())
                })
                .collect::<Vec<_>>();
            for (((test, plan), work), census) in tests
                .iter()
                .zip(&mutant.plan.tests)
                .zip(works)
                .zip(censuses)
            {
                assert_eq!(plan.test_id, test.id);
                let pair = format!("{label} {} {}", mutation.id, test.id);
                let decided = match (&plan.run, work) {
                    (TestRun::Compared(expected), Some(work)) if work > 0 => expected
                        .iter()
                        .all(|outcome| {
                            matches!(outcome, OracleOutcome::Agree | OracleOutcome::Distinguish)
                        })
                        .then_some((expected, work)),
                    _ => None,
                };
                let Some((expected, work)) = decided else {
                    let finished = census.as_ref().and_then(|census| {
                        (census.stop == kink_campaign::RunStop::Finished
                            && census.leaves.keys().all(|halt| {
                                matches!(
                                    halt,
                                    HaltClass::Stuck | HaltClass::Trivial | HaltClass::Vacuous
                                )
                            }))
                        .then_some(census.work?)
                        .filter(|work| *work > 0)
                    });
                    tally.undecided.push(format!(
                        "{pair}: {:?}; census {:?}",
                        plan.run,
                        census.map(|census| (census.leaves, census.deepest, census.work))
                    ));
                    if let Some(work) = finished {
                        tally.unclean.push(pair.clone());
                        let compiled = ClaimSupport::new(baseline)
                            .withdraw(baseline, &mutation.patch)
                            .ok()
                            .filter(Withdrawal::trusted)
                            .and_then(|withdrawal| {
                                spec.validator
                                    .validate(withdrawal.patch().unwrap_or(&mutation.patch))
                                    .ok()
                            })
                            .expect("a mutant that ran its tests builds claim-free");
                        for limit in ladder.budgets(work) {
                            let bounded = run_campaign_multi_with(
                                &campaign(std::slice::from_ref(test)),
                                generations,
                                &options(WorkBudget::Calibrated {
                                    factor: 0,
                                    floor: limit,
                                }),
                                &mut session,
                            )
                            .unwrap();
                            tally.bounded_runs += 1;
                            let at = format!("{pair} budget {limit} (work {work})");
                            let TestRun::Compared(outcomes) = &bounded.mutants[0].plan.tests[0].run
                            else {
                                continue;
                            };
                            for (slot, outcome) in outcomes.iter().enumerate() {
                                match outcome {
                                    OracleOutcome::Unknown => {}
                                    OracleOutcome::Distinguish => {
                                        match one_sided_support::explain_one_sided_kill(
                                            &compiled,
                                            &module,
                                            &test.initial_state,
                                            budget,
                                            limit,
                                            (&plan.run, slot),
                                            &all_normal,
                                        ) {
                                            Ok(explanation) => {
                                                tally.one_sided_kills.push(format!(
                                                    "{at} slot {slot} (unclean)"
                                                ));
                                                tally.explained.push(format!(
                                                    "{at} slot {slot}: {explanation:?}"
                                                ));
                                            }
                                            Err(why) => tally
                                                .failed
                                                .push(format!("{at} slot {slot}: unexplained: {why}")),
                                        }
                                    }
                                    other => tally.failed.push(format!(
                                        "{at} slot {slot}: {other:?} beside an unclean unbounded run"
                                    )),
                                }
                            }
                        }
                        continue;
                    }
                    let WorkBudget::Calibrated { .. } = manifest.budget.work() else {
                        continue;
                    };
                    let bounded = run_campaign_multi_with(
                        &campaign(std::slice::from_ref(test)),
                        generations,
                        &options(manifest.budget.work()),
                        &mut session,
                    )
                    .unwrap();
                    if bounded.mutants[0].plan.tests[0].run.kills_by_distinguish() {
                        tally.unconfirmed.push(format!(
                            "{pair}: {:?}",
                            bounded.mutants[0].plan.tests[0].run
                        ));
                    }
                    continue;
                };
                tally.compared += 1;
                if expected.contains(&OracleOutcome::Distinguish) {
                    tally.distinguished += 1;
                } else {
                    tally.agreed += 1;
                }
                let one = std::slice::from_ref(test);
                for limit in ladder.budgets(work) {
                    let bounded = run_campaign_multi_with(
                        &campaign(one),
                        generations,
                        &options(WorkBudget::Calibrated {
                            factor: 0,
                            floor: limit,
                        }),
                        &mut session,
                    )
                    .unwrap();
                    tally.bounded_runs += 1;
                    let at = format!("{pair} budget {limit} (work {work})");
                    let census = session
                        .last_call()
                        .mutant_run(MutantId(0), &test.id)
                        .map(|recording| recording.census.clone());
                    if census
                        .as_ref()
                        .is_none_or(|census| census.leaves.get(&HaltClass::WorkBound) != Some(&1))
                    {
                        tally
                            .failed
                            .push(format!("{at}: not work-bound: {census:?}"));
                        continue;
                    }
                    let TestRun::Compared(outcomes) = &bounded.mutants[0].plan.tests[0].run else {
                        tally
                            .failed
                            .push(format!("{at}: {:?}", bounded.mutants[0].plan.tests[0].run));
                        continue;
                    };
                    let sides = mutant_sides(&bounded, &test.id);
                    for (slot, (outcome, expected)) in outcomes.iter().zip(expected).enumerate() {
                        if outcome != expected && *outcome != OracleOutcome::Unknown {
                            tally.failed.push(format!(
                                "{at} slot {slot}: {outcome:?}, unbounded {expected:?}"
                            ));
                        }
                        if *outcome == OracleOutcome::Distinguish {
                            if sides.and_then(|sides| sides.get(slot)) != Some(&OracleSide::Unknown)
                            {
                                tally.failed.push(format!(
                                    "{at} slot {slot}: a bounded side that is a value"
                                ));
                            }
                            tally.one_sided_kills.push(format!("{at} slot {slot}"));
                            tally.killed_one_sidedly.insert(pair.clone());
                        }
                    }
                }
            }
        }
    }
}

mod heavy {
    use super::*;

    #[test]
    // Formerly ignored as "about three minutes: run on demand, recorded in the L1-2 handoff".
    #[ignore = "heavy"]
    fn every_one_sided_kill_on_the_flow_corpus_agrees_with_the_unbounded_verdict() {
        let tally = std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(|| {
                let mut tally = Tally::default();
                for manifest in flow_manifests() {
                    differential(&manifest, None, Ladder::Short, &mut tally);
                }
                tally
            })
            .unwrap()
            .join()
            .unwrap();
        eprintln!("ONE-SIDED-FLOW {tally:#?}");
        assert!(tally.failed.is_empty(), "{:#?}", tally.failed);
        assert!(tally.mutants >= 45, "{}", tally.mutants);
        assert!(tally.compared >= 100, "{}", tally.compared);
        assert!(tally.agreed > 0 && tally.distinguished > 0, "{tally:#?}");
        assert!(tally.unconfirmed.is_empty(), "{:#?}", tally.unconfirmed);
    }

    #[test]
    // Formerly ignored as "about twelve minutes: run on demand, recorded in the L1-2 handoff".
    #[ignore = "heavy"]
    fn every_one_sided_kill_on_imp_agrees_with_the_unbounded_verdict() {
        // A mutant that loops builds deep terms: run on a big stack, as kink-flow does.
        let tally = std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(|| {
                let mut tally = Tally::default();
                differential(
                    &repository().join("examples/imp/FLOW.toml"),
                    Some(Duration::from_secs(60)),
                    Ladder::Halving,
                    &mut tally,
                );
                tally
            })
            .unwrap()
            .join()
            .unwrap();
        eprintln!("ONE-SIDED-IMP {tally:#?}");
        assert!(tally.failed.is_empty(), "{:#?}", tally.failed);
        assert_eq!(tally.mutants, 21);
        assert!(tally.unconfirmed.is_empty(), "{:#?}", tally.unconfirmed);
    }
}

/// The corpus of `testdata/k/l1/onesided.k` with one program, `start(12000)`, and one mutation,
/// early's 7 becomes 8 and late's 2 becomes 3: its early final configuration `done(12008)` is not
/// the baseline's, and its loop is half as long again, so with `work_factor = 1` its run (about
/// 36000 states) passes `W + 10000` (the baseline's 24000 states plus the floor) and ends at the
/// budget after the early branch has finished.
fn one_sided_corpus(work_factor: Option<u64>) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-one-sided-{}", std::process::id()))
        .join(work_factor.map_or_else(|| "unbounded".to_owned(), |f| format!("factor-{f}")));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::copy(
        repository().join("testdata/k/l1/onesided.k"),
        dir.join("onesided.k"),
    )
    .unwrap();
    let budget = work_factor.map_or_else(String::new, |f| format!("work_factor = {f}\n"));
    std::fs::write(
        dir.join("FLOW.toml"),
        format!(
            "[spec]\nentry = \"onesided.k\"\nmain_module = \"ONESIDED\"\n\
             syntax_module = \"ONESIDED-SYNTAX\"\n\n[budget]\ntime_ms = 60000\n{budget}\n\
             [[program]]\nid = \"start\"\ntext = \"start(12000)\"\n"
        ),
    )
    .unwrap();
    std::fs::write(
        dir.join("MUTATIONS.toml"),
        "[[mutation]]\nid = \"early-and-longer\"\nnote = \"another early result, a longer loop\"\n\n\
         [[mutation.edit]]\nrule = \"early\"\nfind = \"N +Int 7\"\nreplace = \"N +Int 8\"\n\n\
         [[mutation.edit]]\nrule = \"late\"\nfind = \"N *Int 2\"\nreplace = \"N *Int 3\"\n",
    )
    .unwrap();
    dir.join("FLOW.toml")
}

fn search(manifest: &Path) -> Value {
    let (document, ok) = run(
        &FlowManifest::read(manifest).unwrap(),
        &MutationList::read(&manifest.with_file_name("MUTATIONS.toml")).unwrap(),
        &SearchOptions {
            only: Vec::new(),
            cache: None,
            order: ProgramOrder::Corpus,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
        },
    );
    assert!(ok, "{document:#}");
    document
}

/// The mutation's status and killer, and its executed entry: outcome, the two slots' outcomes,
/// the whole-term slot's sides, and whether it was cached.
fn entry(document: &Value) -> (Value, Value, Value, Value, Value, Value, Value) {
    let mutation = &document["mutations"][0];
    let [executed] = mutation["executed"].as_array().unwrap().as_slice() else {
        panic!("one executed entry: {mutation:#}")
    };
    (
        mutation["status"].clone(),
        mutation["killer"].clone(),
        executed["outcome"].clone(),
        executed["slots"]["exit-stop"]["outcome"].clone(),
        executed["slots"]["whole-term"]["outcome"].clone(),
        executed["slots"]["whole-term"]["sides"].clone(),
        executed["cached"].clone(),
    )
}

mod kink_tier {
    use super::*;

    #[test]
    #[ignore = "kink"]
    fn a_work_bound_mutant_run_kills_one_sidedly_through_the_flow() {
        let document = std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(|| {
                let bounded = one_sided_corpus(Some(1));
                let first = search(&bounded);
                let second = search(&bounded);
                let unbounded = search(&one_sided_corpus(None));
                (first, second, unbounded)
            })
            .unwrap()
            .join()
            .unwrap();
        let (first, second, unbounded) = document;
        let killed = |cached: bool, sides_null: bool, exit_stop: &str| {
            let (status, killer, outcome, exit, whole, sides, was_cached) = entry(if cached {
                &second
            } else if sides_null {
                &first
            } else {
                &unbounded
            });
            assert_eq!(
                (status, killer, outcome, was_cached),
                (
                    Value::from("killed"),
                    Value::from("start"),
                    Value::from("distinguish"),
                    Value::from(cached)
                )
            );
            if !cached {
                assert_eq!(
                    (exit, whole),
                    (Value::from(exit_stop), Value::from("distinguish"))
                );
                assert_eq!(sides.is_null(), sides_null, "{sides:#}");
            }
        };
        // Under the budget: the exit stop (normal, no code) is the baseline's, so that slot is
        // unknown; the whole term distinguishes one-sidedly, with no mutant value to show.
        killed(false, true, "unknown");
        // The re-run takes the killed outcome from tier 1 (keyed with the work budget).
        killed(true, true, "unknown");
        // Without a budget the mutant's run is complete and both slots compare.
        killed(false, false, "agree");
    }
}

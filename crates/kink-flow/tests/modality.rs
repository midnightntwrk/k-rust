//! Re-pin lane 1 (L1-1), decision 3 and finding A-01: the kink-side modality differential over
//! the corpus. Every result run of kink is a state set (kink-native `ExecutionAdapter::execute`);
//! a kill rests on the premise that a complete state set has exactly the distinct final
//! configurations of the path set of the same request, which k-rust tests with its own
//! differential. This test checks it on kink's corpus, for every admitted program of every
//! `testdata/flow` manifest (and, `#[ignore]`d for its cost, of `examples/imp`):
//!
//! - the raw runs (no replacement of a state set by its path set): equal timeout; where both
//!   finish, equal deduplicated final (`Stuck`) configurations, equal undefined-step and vacuous
//!   leaves as sets of (halt, depth, state), an incomplete leaf in one exactly when in the other,
//!   a diagnostic in one exactly when in the other, and equal bridged state-slot inputs (the
//!   collection stop and the set of terminals with their values);
//! - the rule coverage: equal from both runs, and equal to what a stepped path set's branches
//!   name (the reading before L1-1);
//! - the campaign runner itself, with `RunOptions::result_modality` `PathSet` and `StateSet`:
//!   equal baseline evidence (every state side) and equal baseline coverage.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use k_rust::kore::{ast::Pattern, codec, parser::parse_definition};
use kink_campaign::{
    Campaign, CampaignOptions, RunOptions, ScheduleMode, TestCase, run_campaign_multi,
};
use kink_corpus::{admission::input_backend, runner::all_normal};
use kink_flow::{
    admit::admit,
    manifest::FlowManifest,
    results::{execution_budget, fixed_oracles},
};
use kink_native::bridge::{BridgeContext, paths_from_execution_values};
use kink_native::coverage::{RuleAuthors, TestCoverage};
use kink_native::execution::{
    AdaptedExecution, ExecutionAdapter, ExecutionBudget, HaltClass, ResultModality, ResultRun,
    SolverProfile,
};
use kink_native::feasibility::TestInitialState;
use kink_native::step_events::ObservationDecider;
use kink_patch::{Discovery, Patch, SelectionPolicy, select};
use kink_pattern::SymbolSorts;

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Every manifest of `testdata/flow`, in path order.
fn flow_manifests() -> Vec<PathBuf> {
    let mut manifests = Vec::new();
    let root = repository().join("testdata/flow");
    let mut fixtures = std::fs::read_dir(&root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.is_dir())
        .collect::<Vec<_>>();
    fixtures.sort();
    for fixture in fixtures {
        let mut files = std::fs::read_dir(&fixture)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.starts_with("FLOW") && name.ends_with(".toml"))
            })
            .collect::<Vec<_>>();
        files.sort();
        manifests.extend(files);
    }
    manifests
}

/// A leaf as the differential compares it: its halt, its depth (for undefined steps and vacuous
/// leaves only) and its state's canonical text.
type LeafKey = (String, Option<u64>, String);

fn key(execution: &AdaptedExecution, halts: &[HaltClass], depth: bool) -> BTreeSet<LeafKey> {
    execution
        .leaves()
        .iter()
        .filter(|leaf| halts.contains(&leaf.halt))
        .map(|leaf| {
            let state = codec::from_value(&leaf.branch.state)
                .map(|state: Pattern| state.to_string())
                .unwrap_or_else(|_| leaf.branch.state.to_string());
            (
                format!("{:?}", leaf.halt),
                depth.then_some(leaf.branch.depth),
                state,
            )
        })
        .collect()
}

fn incomplete(execution: &AdaptedExecution) -> bool {
    execution.leaves().iter().any(|leaf| {
        !matches!(
            leaf.halt,
            HaltClass::Stuck | HaltClass::Trivial | HaltClass::Vacuous
        )
    })
}

fn diagnosed(execution: &AdaptedExecution) -> bool {
    execution.leaves().iter().any(|leaf| {
        !leaf.diagnostics.is_empty()
            || !leaf.remainder_diagnostics.is_empty()
            || leaf
                .candidate_diagnostics
                .iter()
                .any(|list| !list.is_empty())
    })
}

/// What the differential found for one manifest.
#[derive(Default)]
struct Tally {
    compared: usize,
    timed_out_both: usize,
    /// Programs the state set finished and the path set did not (time bound).
    faster: Vec<String>,
    /// Programs whose state set had to be replaced by its path set (an undefined step, a
    /// vacuous leaf or a contradicted claim).
    replaced: Vec<String>,
    /// Programs a run of which the adapter refused, with the failures (never compared).
    failed: Vec<String>,
}

/// The differential over every admitted program of `manifest_path`, each run under the
/// manifest's budget, with its time bound raised to `time` when given (so that a program near
/// the bound does not time out in one run and not in the other).
fn differential(manifest_path: &Path, time: Option<std::time::Duration>) -> Tally {
    let mut tally = Tally::default();
    let manifest = FlowManifest::read(manifest_path).unwrap();
    let admission = admit(&manifest);
    let Some(spec) = admission.spec.as_ref() else {
        return tally;
    };
    let mut budget = execution_budget(manifest.budget);
    if let Some(time) = time {
        budget.time = budget.time.max(time);
    }
    let sorts = SymbolSorts::from_definition(
        &parse_definition(&spec.compiled.artifacts().definition_kore).unwrap(),
    );
    let authors = RuleAuthors::of(&spec.compiled);
    let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
    let mut tests = Vec::new();
    for program in &admission.programs {
        let Ok(test) = &program.outcome else {
            continue;
        };
        let id = format!("{} {}", manifest_path.display(), program.id);
        let mut backend = input_backend(&spec.compiled, &manifest.spec.main_module).unwrap();
        let run = |backend: &mut _, modality| {
            adapter.execute_once(
                backend,
                &test.initial_state,
                budget,
                ResultRun {
                    modality,
                    max_work: None,
                },
            )
        };
        let (path_set, state_set) = match (
            run(&mut backend, ResultModality::PathSet),
            run(&mut backend, ResultModality::StateSet),
        ) {
            (Ok(path_set), Ok(state_set)) => (path_set, state_set),
            (path_set, state_set) => {
                tally.failed.push(format!(
                    "{id}: {:?} / {:?}",
                    path_set.err(),
                    state_set.err()
                ));
                continue;
            }
        };
        assert_eq!(path_set.modality(), ResultModality::PathSet, "{id}");
        assert_eq!(state_set.modality(), ResultModality::StateSet, "{id}");
        tests.push(TestCase {
            id: program.id.clone(),
            initial_state: test.initial_state.clone(),
            oracles: fixed_oracles(),
        });
        match (path_set.timed_out(), state_set.timed_out()) {
            (true, true) => {
                tally.timed_out_both += 1;
                continue;
            }
            (true, false) => {
                tally.faster.push(id);
                continue;
            }
            (false, true) => panic!("{id}: the state set timed out where the path set did not"),
            (false, false) => {}
        }
        tally.compared += 1;
        assert_eq!(
            key(&path_set, &[HaltClass::Stuck], false),
            key(&state_set, &[HaltClass::Stuck], false),
            "{id}: deduplicated final configurations"
        );
        let undefined = [HaltClass::Trivial, HaltClass::Vacuous];
        assert_eq!(
            key(&path_set, &undefined, true),
            key(&state_set, &undefined, true),
            "{id}: undefined-step and vacuous leaves as sets"
        );
        if !key(&state_set, &undefined, true).is_empty()
            || state_set
                .leaves()
                .iter()
                .any(|leaf| leaf.contradicted_total.is_some())
        {
            tally.replaced.push(id.clone());
        }
        assert_eq!(incomplete(&path_set), incomplete(&state_set), "{id}");
        assert_eq!(diagnosed(&path_set), diagnosed(&state_set), "{id}");
        assert_eq!(
            path_set.stack_stops() == 0,
            state_set.stack_stops() == 0,
            "{id}"
        );
        // The state-slot inputs: the bridged terminals and how the collection stopped.
        let bridged = |backend: &mut k_rust::backend::Backend, execution: &AdaptedExecution| {
            backend
                .with_solver(None, |definition, solver| {
                    let decider = ObservationDecider::new(
                        definition,
                        solver,
                        TestInitialState::of_test(&test.initial_state),
                    );
                    Ok::<_, k_rust::backend::BackendError>(
                        paths_from_execution_values(
                            execution,
                            &BridgeContext {
                                test_id: &program.id,
                                classify: &all_normal,
                                sorts: &sorts,
                            },
                            &|term| decider.terminal_value(term),
                        )
                        .map(|bridged| {
                            let terminals = bridged
                                .paths
                                .iter()
                                .map(|path| {
                                    (
                                        path.complete,
                                        format!("{:?}", path.stop),
                                        path.execution_terminal
                                            .as_ref()
                                            .map(|terminal| format!("{terminal:?}")),
                                    )
                                })
                                .collect::<BTreeSet<_>>();
                            (format!("{:?}", bridged.collection.stop), terminals)
                        }),
                    )
                })
                .unwrap()
        };
        assert_eq!(
            bridged(&mut backend, &path_set),
            bridged(&mut backend, &state_set),
            "{id}: state-slot inputs"
        );
        // Rule coverage: equal from both runs, and equal to what a stepped path set's branches
        // name.
        let coverage = |execution: &AdaptedExecution| {
            let coverage = TestCoverage::of_execution(&program.id, execution, &authors);
            (coverage.complete, coverage.rule_ids, coverage.sentences)
        };
        assert_eq!(coverage(&path_set), coverage(&state_set), "{id}: coverage");
        if let Ok(Ok(stepped)) = adapter.execute_steps(&mut backend, &test.initial_state, budget)
            && !stepped.adapted.timed_out()
        {
            let branches = TestCoverage::of_branches(&program.id, &stepped.adapted, &authors);
            assert_eq!(
                branches.rule_ids,
                coverage(&state_set).1,
                "{id}: coverage from k-rust and from the branches"
            );
        }
    }
    // The campaign runner under both modalities: equal baseline evidence and coverage.
    if !tests.is_empty() {
        let discovery = Discovery::empty(spec.validator.baseline(), false, false);
        let generation = select(&discovery, SelectionPolicy::Each, 1)
            .unwrap()
            .fold("baseline-only", |_| -> Patch {
                unreachable!("no fold call")
            })
            .unwrap();
        let module = k_rust::kast::identifier::encode(&manifest.spec.main_module);
        let campaign = Campaign {
            validator: &spec.validator,
            module: &module,
            observation: &[],
            classify: &all_normal,
            tests: &tests,
            budget,
        };
        let evidence = |result_modality| {
            run_campaign_multi(
                &campaign,
                std::slice::from_ref(&generation),
                &CampaignOptions {
                    schedule: ScheduleMode::Full,
                    selection: kink_campaign::SelectionPolicy::None,
                    share_evidence: true,
                    run: RunOptions {
                        result_modality,
                        ..RunOptions::default()
                    },
                },
            )
            .map(|run| {
                (
                    run.baseline,
                    run.baseline_coverage
                        .into_iter()
                        .map(|coverage| (coverage.complete, coverage.rule_ids))
                        .collect::<Vec<_>>(),
                )
            })
            .map_err(|failure| failure.to_string())
        };
        let (path_set, state_set) = (
            evidence(ResultModality::PathSet),
            evidence(ResultModality::StateSet),
        );
        // A campaign refused for a baseline that timed out under the path set and finished under
        // the state set is the faster case, counted above.
        if tally.faster.is_empty() {
            if let (Ok(path_set), Ok(state_set)) = (&path_set, &state_set) {
                for ((path, state), test) in path_set.0.iter().zip(&state_set.0).zip(&tests) {
                    assert_eq!(
                        path,
                        state,
                        "{} {}: campaign baseline evidence",
                        manifest_path.display(),
                        test.id
                    );
                }
            }
            assert_eq!(
                path_set,
                state_set,
                "{}: campaign baseline evidence",
                manifest_path.display()
            );
        }
    }
    tally
}

#[test]
fn state_set_results_equal_path_set_results_over_the_flow_corpus() {
    let mut compared = 0;
    let mut replaced = Vec::new();
    let mut failed = Vec::new();
    for manifest in flow_manifests() {
        let tally = differential(&manifest, None);
        failed.extend(tally.failed);
        assert!(
            tally.faster.is_empty(),
            "{}: a state set finished where the path set timed out: {:?}",
            manifest.display(),
            tally.faster
        );
        compared += tally.compared;
        replaced.extend(tally.replaced);
    }
    eprintln!("MODALITY compared={compared} replaced={replaced:?} failed={failed:?}");
    assert!(failed.is_empty(), "{failed:?}");
    assert!(compared >= 30, "{compared}");
}

/// The same differential over the IMP corpus (`examples/imp`), every run with a one-minute time
/// bound: about a minute in all, so run on demand (`cargo test -p kink-flow --test modality -- --ignored`); its result is recorded
/// in the re-pin L1-1 handoff.
#[test]
#[ignore = "minutes: run on demand, recorded in the L1-1 handoff"]
fn state_set_results_equal_path_set_results_over_imp() {
    // collatz runs close to IMP's own 10 s bound: give every run a minute.
    let tally = differential(
        &repository().join("examples/imp/FLOW.toml"),
        Some(std::time::Duration::from_secs(60)),
    );
    eprintln!(
        "MODALITY-IMP compared={} timed_out_both={} faster={:?} replaced={:?} failed={:?}",
        tally.compared, tally.timed_out_both, tally.faster, tally.replaced, tally.failed
    );
    assert!(tally.failed.is_empty(), "{:?}", tally.failed);
    assert!(tally.faster.is_empty(), "{:?}", tally.faster);
    // Every program of the corpus, collatz included, finishes within the minute.
    assert_eq!(tally.compared, 7);
}

/// Keeps the import of `ExecutionBudget` honest: the differential runs each program under its
/// manifest's own budget, which has no breadth bound (a breadth bound is where the two
/// modalities may legitimately differ, k-rust docs/backend-port.md).
#[test]
fn the_corpus_budget_has_no_breadth_bound() {
    for manifest in flow_manifests() {
        let budget: ExecutionBudget =
            execution_budget(FlowManifest::read(&manifest).unwrap().budget);
        assert_eq!(budget.max_breadth, None, "{}", manifest.display());
    }
}

//! Re-pin lane 1 (L1-1, strengthened in L1-1-fix-1), decision 3 and finding A-01: the kink-side
//! modality differential. Every result run of kink is a state set (kink-native
//! `ExecutionAdapter::execute`); a kill rests on the premise that a complete state set has exactly
//! the distinct final configurations of the path set of the same request, which k-rust tests with
//! its own differential. This test checks it on kink's own inputs, on the baseline AND on every
//! mutant, and fails the gate on any difference it does not name:
//!
//! - the flow corpus: every admitted program of every `testdata/flow` manifest (nested ones
//!   included), on the baseline and on the claim-free mutant of every mutation of every
//!   `MUTATIONS*.toml` beside the manifest that resolves and compiles;
//! - the converging fixtures of `testdata/k/l1` (the L1-1 review's shapes), where k-rust's merge
//!   really happens on the mutant side, with a classifier that reads crashes;
//! - `#[ignore]`d for its cost, `examples/imp` and its mutants.
//!
//! For each (side, program) it compares the raw runs (no replacement of a state set by its path
//! set) under the side's budget:
//!
//! - equal timeout (a state set that finishes where the path set timed out is counted, never
//!   compared; the reverse fails);
//! - the complete leaves as sets of (terminal class, depth for undefined steps and vacuous leaves,
//!   configuration): the class of a stuck leaf is the classifier's (normal, stuck, crash), so the
//!   deduplicated finals and their terminal classes are equal;
//! - the bounded and other incomplete leaves as sets of (halt, configuration): equal, except that
//!   a path-set leaf the state set lacks must be one k-rust documents as absorbed (an earlier
//!   stuck leaf of the same configuration stands for it; k-rust `docs/backend-port.md`, "Final
//!   search depth cuts"), which is counted and reported (kink-campaign
//!   `tests/state_set_routes.rs`, route 3);
//! - a diagnostic in one exactly when in the other, a stack stop in one exactly when in the other;
//! - the bridged state-slot inputs (each path's completeness, stop and classified terminal, and
//!   the collection stop) as sets: equal, or, where a leaf was absorbed, equal complete terminals
//!   and the state set's paths a subset of the path set's;
//! - the rule coverage from both runs, reached and fired ids and sentences, and on the flow
//!   corpus's and the fixtures' baselines k-rust's applied rewrite rules equal to what a stepped
//!   path set's branches name (the reading before L1-1).
//!
//! On the flow corpus it also runs the campaign runner over the baseline and every mutation with
//! `RunOptions::result_modality` `PathSet` and `StateSet`, and asserts equal baseline evidence,
//! baseline coverage and, mutant by mutant, equal status, killers and plan: the corpus classifies
//! every terminal normal and no corpus leaf is absorbed, so none of the three state-set-only kill
//! routes can apply, and a verdict that depends on the modality fails the gate.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::Duration;

use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kore::{ast::Pattern, codec, parser::parse_definition, walk};
use kink_campaign::{
    Campaign, CampaignOptions, RunOptions, ScheduleMode, TestCase, run_campaign_multi,
};
use kink_corpus::{admission::input_backend, runner::all_normal};
use kink_flow::{
    admit::admit,
    manifest::FlowManifest,
    mutation::{MutationList, resolve},
    results::{execution_budget, fixed_oracles},
};
use kink_native::bridge::{BridgeContext, paths_from_execution_values};
use kink_native::coverage::{RuleAuthors, TestCoverage};
use kink_native::execution::{
    AdaptedExecution, AdaptedLeaf, ExecutionAdapter, ExecutionBudget, HaltClass, ResultModality,
    ResultRun, SolverProfile,
};
use kink_native::feasibility::TestInitialState;
use kink_native::step_events::ObservationDecider;
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::{
    Baseline, ClaimSupport, Discovery, Edit, Patch, SelectionPolicy, SentenceRef, TermRef, select,
};
use kink_pattern::{ExecutionTerminalKind, SymbolSorts};

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

type Classifier = dyn Fn(&Pattern) -> ExecutionTerminalKind;

fn state_text(leaf: &AdaptedLeaf) -> String {
    codec::from_value(&leaf.branch.state)
        .map(|state: Pattern| state.to_string())
        .unwrap_or_else(|_| leaf.branch.state.to_string())
}

/// A complete leaf as the differential compares it: its terminal class (a stuck leaf's is the
/// classifier's), its depth for undefined steps and vacuous leaves, and its configuration.
type CompleteKey = (String, Option<u64>, String);

/// The complete leaves of `execution`, and its other leaves as (halt, configuration).
fn leaf_sets(
    execution: &AdaptedExecution,
    classify: &Classifier,
) -> (BTreeSet<CompleteKey>, BTreeSet<(String, String)>) {
    let (mut complete, mut bounded) = (BTreeSet::new(), BTreeSet::new());
    for leaf in execution.leaves() {
        let state = state_text(leaf);
        match leaf.halt {
            HaltClass::Stuck => {
                let class = codec::from_value(&leaf.branch.state)
                    .map(|term: Pattern| format!("{:?}", classify(&term)))
                    .unwrap_or_else(|_| "undecodable".into());
                complete.insert((class, None, state));
            }
            HaltClass::Trivial | HaltClass::Vacuous => {
                complete.insert((format!("{:?}", leaf.halt), Some(leaf.branch.depth), state));
            }
            other => {
                bounded.insert((format!("{other:?}"), state));
            }
        }
    }
    (complete, bounded)
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

/// What the differential found.
#[derive(Debug, Default)]
struct Tally {
    /// (side, program) pairs compared, and how many of them on a mutant side.
    compared: usize,
    compared_on_mutants: usize,
    /// Mutant sides run.
    mutants: usize,
    /// Mutations that resolve but have no claim-free compiled mutant (never run).
    not_built: Vec<String>,
    timed_out_both: usize,
    /// Pairs the state set finished and the path set did not (time bound): not compared.
    faster: Vec<String>,
    /// Pairs whose state set has fewer leaves than the path set: k-rust's merge happened.
    merged: Vec<String>,
    merged_on_mutants: Vec<String>,
    /// Pairs whose state set kink replaces by its path set (an undefined step, a vacuous leaf or
    /// a contradicted claim).
    replaced: Vec<String>,
    /// Pairs where an earlier stuck leaf absorbed a later bounded leaf of its configuration.
    absorbed: Vec<String>,
    /// Pairs a run of which the adapter refused, with the failures (never compared).
    failed: Vec<String>,
    /// Mutant verdicts of the campaign runner compared under both modalities.
    campaign_verdicts: usize,
}

impl Tally {
    fn extend(&mut self, other: Self) {
        self.compared += other.compared;
        self.compared_on_mutants += other.compared_on_mutants;
        self.mutants += other.mutants;
        self.not_built.extend(other.not_built);
        self.timed_out_both += other.timed_out_both;
        self.faster.extend(other.faster);
        self.merged.extend(other.merged);
        self.merged_on_mutants.extend(other.merged_on_mutants);
        self.replaced.extend(other.replaced);
        self.absorbed.extend(other.absorbed);
        self.failed.extend(other.failed);
        self.campaign_verdicts += other.campaign_verdicts;
    }

    /// Whether this side's runs had a documented difference: one the time bound let only the
    /// state set finish, or an absorbed leaf.
    fn documented(&self) -> usize {
        self.faster.len() + self.absorbed.len()
    }
}

/// One compiled side to compare.
struct Side<'a> {
    label: String,
    compiled: &'a ValidatedDefinition,
    mutant: bool,
    /// Also compare the coverage with a stepped path set's branches (baselines only; off on IMP,
    /// where `primes`' observed path set runs out of a 24 GiB scope).
    stepped: bool,
}

/// The differential of every program of `programs` on `side`; see the module documentation.
fn compare_side(
    side: &Side<'_>,
    main_module: &str,
    programs: &[(String, Pattern)],
    budget: ExecutionBudget,
    classify: &Classifier,
    tally: &mut Tally,
) {
    let sorts = SymbolSorts::from_definition(
        &parse_definition(&side.compiled.artifacts().definition_kore).unwrap(),
    );
    let authors = RuleAuthors::of(side.compiled);
    let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
    let mut backend = input_backend(side.compiled, main_module).unwrap();
    for (program, state) in programs {
        let id = format!("{} {program}", side.label);
        let run = |backend: &mut _, modality| {
            adapter.execute_once(
                backend,
                state,
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
        tally.compared_on_mutants += usize::from(side.mutant);
        if state_set.leaves().len() < path_set.leaves().len() {
            tally.merged.push(id.clone());
            if side.mutant {
                tally.merged_on_mutants.push(id.clone());
            }
        }
        let (path_complete, path_bounded) = leaf_sets(&path_set, classify);
        let (state_complete, state_bounded) = leaf_sets(&state_set, classify);
        assert_eq!(
            path_complete, state_complete,
            "{id}: deduplicated complete leaves and their terminal classes"
        );
        assert!(
            state_bounded.is_subset(&path_bounded),
            "{id}: a bounded state-set leaf the path set lacks: {:?}",
            state_bounded.difference(&path_bounded).collect::<Vec<_>>()
        );
        let stuck = state_complete
            .iter()
            .filter(|(_, depth, _)| depth.is_none())
            .map(|(_, _, state)| state)
            .collect::<BTreeSet<_>>();
        let absorbed = path_bounded.difference(&state_bounded).collect::<Vec<_>>();
        for (halt, state) in &absorbed {
            assert!(
                stuck.contains(state),
                "{id}: the state set dropped a {halt} leaf whose configuration no stuck leaf \
                 decides: {state}"
            );
        }
        if !absorbed.is_empty() {
            tally.absorbed.push(id.clone());
        }
        if state_set.leaves().iter().any(|leaf| {
            matches!(leaf.halt, HaltClass::Trivial | HaltClass::Vacuous)
                || leaf.contradicted_total.is_some()
        }) {
            tally.replaced.push(id.clone());
        }
        assert_eq!(diagnosed(&path_set), diagnosed(&state_set), "{id}");
        assert_eq!(
            path_set.stack_stops() == 0,
            state_set.stack_stops() == 0,
            "{id}"
        );
        // The state-slot inputs: the bridged paths with their classified terminals, and how the
        // collection stopped.
        let bridged = |backend: &mut k_rust::backend::Backend, execution: &AdaptedExecution| {
            backend
                .with_solver(None, |definition, solver| {
                    let decider = ObservationDecider::new(
                        definition,
                        solver,
                        TestInitialState::of_test(state),
                    );
                    Ok::<_, k_rust::backend::BackendError>(
                        paths_from_execution_values(
                            execution,
                            &BridgeContext {
                                test_id: program,
                                classify,
                                sorts: &sorts,
                            },
                            &|term| decider.terminal_value(term),
                        )
                        .map(|bridged| {
                            let paths = bridged
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
                            (format!("{:?}", bridged.collection.stop), paths)
                        })
                        .map_err(|failure| format!("{failure:?}")),
                    )
                })
                .unwrap()
        };
        let (path_bridged, state_bridged) = (
            bridged(&mut backend, &path_set),
            bridged(&mut backend, &state_set),
        );
        if absorbed.is_empty() {
            assert_eq!(path_bridged, state_bridged, "{id}: state-slot inputs");
        } else {
            let (Ok((_, path_paths)), Ok((_, state_paths))) = (&path_bridged, &state_bridged)
            else {
                panic!("{id}: bridging {path_bridged:?} / {state_bridged:?}");
            };
            let complete = |paths: &BTreeSet<(bool, String, Option<String>)>| {
                paths
                    .iter()
                    .filter(|(complete, _, _)| *complete)
                    .cloned()
                    .collect::<BTreeSet<_>>()
            };
            assert_eq!(
                complete(path_paths),
                complete(state_paths),
                "{id}: complete terminals"
            );
            assert!(state_paths.is_subset(path_paths), "{id}: state-slot inputs");
        }
        // Rule coverage: equal from both runs, reached and fired (re-pin L2-1-tail, review
        // L2-1-1 D5: the fired set orders kink-campaign's right-hand-side edits and kink-flow's
        // programs, and is the results document's `fired_by`), and on a baseline k-rust's
        // applied rewrite rules equal what a stepped path set's branches name (an independent
        // check of k-rust's coverage, which re-pin L2-1 kept when it retired
        // `TestCoverage::of_branches`).
        let coverage = |execution: &AdaptedExecution| {
            let coverage = TestCoverage::of_execution(program, execution, &authors);
            (
                coverage.complete,
                (coverage.rule_ids, coverage.applied_ids),
                (coverage.sentences, coverage.applied_sentences),
            )
        };
        let (path_coverage, state_coverage) = (coverage(&path_set), coverage(&state_set));
        if absorbed.is_empty() {
            assert_eq!(path_coverage, state_coverage, "{id}: coverage");
        } else {
            // The coverage of a run is complete when the run is: only the path set is cut.
            assert_eq!(
                (path_coverage.0, state_coverage.0),
                (false, true),
                "{id}: coverage completeness"
            );
            assert_eq!(
                (&path_coverage.1, &path_coverage.2),
                (&state_coverage.1, &state_coverage.2),
                "{id}: coverage"
            );
        }
        if side.stepped
            && let Ok(Ok(stepped)) = adapter.execute_steps(&mut backend, state, budget)
            && !stepped.adapted.timed_out()
        {
            let branches = stepped
                .adapted
                .leaves()
                .iter()
                .flat_map(|leaf| {
                    leaf.branch
                        .identity
                        .iter()
                        .map(|transition| transition.rule.as_str())
                        .chain(leaf.undefined_rule.iter().map(|rule| rule.id.as_str()))
                })
                .flat_map(|ids| ids.split(','))
                .filter(|id| !id.is_empty())
                .map(str::to_owned)
                .collect::<BTreeSet<_>>();
            assert_eq!(
                Some(&branches),
                state_set
                    .coverage()
                    .map(|coverage| &coverage.applied_rewrites),
                "{id}: coverage from k-rust and from the branches"
            );
        }
    }
}

/// The differential over one flow manifest: its baseline and every mutant of the mutation lists
/// beside it, each program under the manifest's budget. `baseline_time` raises the baseline runs'
/// time bound (so that a program near the bound does not time out in one run and not in the
/// other); `stepped` compares the baseline's coverage with its stepped path set's branches;
/// `mutant_time` caps the time bound of the mutant runs and of the campaign (a mutant
/// that loops forever then costs that long, not the manifest's bound; a run cut by it is counted,
/// never compared); `campaign` also compares the campaign runner's verdicts under both
/// modalities.
fn differential(
    manifest_path: &Path,
    baseline_time: Option<Duration>,
    stepped: bool,
    mutant_time: Option<Duration>,
    campaign: bool,
) -> Tally {
    let mut tally = Tally::default();
    let manifest = FlowManifest::read(manifest_path).unwrap();
    let admission = admit(&manifest);
    let Some(spec) = admission.spec.as_ref() else {
        return tally;
    };
    let label = manifest_path
        .strip_prefix(repository())
        .unwrap_or(manifest_path)
        .display()
        .to_string();
    let budget = execution_budget(manifest.budget);
    let programs = admission
        .programs
        .iter()
        .filter_map(|program| {
            let test = program.outcome.as_ref().ok()?;
            Some((program.id.clone(), test.initial_state.clone()))
        })
        .collect::<Vec<_>>();
    let mut baseline_budget = budget;
    if let Some(time) = baseline_time {
        baseline_budget.time = baseline_budget.time.max(time);
    }
    let mut budget = budget;
    if let Some(time) = mutant_time {
        budget.time = budget.time.min(time);
    }
    compare_side(
        &Side {
            label: label.clone(),
            compiled: &spec.compiled,
            mutant: false,
            stepped,
        },
        &manifest.spec.main_module,
        &programs,
        baseline_budget,
        &all_normal,
        &mut tally,
    );
    let baseline_documented = tally.documented();
    // The mutants: every mutation that resolves, once per patch, built claim-free as every
    // kink-flow run builds it (kink-patch `ClaimSupport::withdraw`).
    let baseline = spec.validator.baseline();
    let support = ClaimSupport::new(baseline);
    let mut resolved = Vec::new();
    let mut digests = BTreeSet::new();
    for list in mutation_lists(manifest_path) {
        for mutation in MutationList::read(&list).unwrap().mutations {
            let Ok(mutation) = resolve(&manifest, &spec.loaded, &mutation) else {
                continue;
            };
            if digests.insert(mutation.digest) {
                resolved.push(mutation);
            }
        }
    }
    let mut documented_mutants = BTreeSet::new();
    for mutation in &resolved {
        let mutant_label = format!("{label} mutant {}", mutation.id);
        let built = support
            .withdraw(baseline, &mutation.patch)
            .ok()
            .filter(kink_patch::Withdrawal::trusted)
            .and_then(|withdrawal| {
                spec.validator
                    .validate(withdrawal.patch().unwrap_or(&mutation.patch))
                    .ok()
            });
        let Some(compiled) = built else {
            tally.not_built.push(mutant_label);
            continue;
        };
        tally.mutants += 1;
        let before = tally.documented();
        compare_side(
            &Side {
                label: mutant_label,
                compiled: &compiled,
                mutant: true,
                stepped: false,
            },
            &manifest.spec.main_module,
            &programs,
            budget,
            &all_normal,
            &mut tally,
        );
        if tally.documented() != before {
            documented_mutants.insert(mutation.id.clone());
        }
    }
    if !campaign || programs.is_empty() || baseline_documented != 0 {
        return tally;
    }
    // The campaign runner under both modalities: equal baseline evidence and coverage, and equal
    // verdicts for every mutant whose runs the raw differential compared without a documented
    // difference.
    let tests = programs
        .iter()
        .map(|(id, state)| TestCase {
            id: id.clone(),
            initial_state: state.clone(),
            oracles: fixed_oracles(),
        })
        .collect::<Vec<_>>();
    let discovery = Discovery::empty(baseline, false, false);
    let mut generations = vec![
        select(&discovery, SelectionPolicy::Each, 1)
            .unwrap()
            .fold("baseline-only", |_| -> Patch {
                unreachable!("no fold call")
            })
            .unwrap(),
    ];
    // One candidate per generation, so the campaign's mutants follow this list.
    let mut generated = Vec::new();
    for mutation in &resolved {
        if let Ok(generation) = mutation.generation(baseline) {
            generations.push(generation);
            generated.push(mutation.id.clone());
        }
    }
    let module = k_rust::kast::identifier::encode(&manifest.spec.main_module);
    let campaign = Campaign {
        validator: &spec.validator,
        module: &module,
        observation: &[],
        classify: &all_normal,
        tests: &tests,
        budget,
    };
    let verdicts = |result_modality| {
        run_campaign_multi(
            &campaign,
            &generations,
            &CampaignOptions {
                schedule: ScheduleMode::Full,
                selection: kink_campaign::SelectionPolicy::None,
                share_evidence: true,
                run: RunOptions {
                    result_modality,
                    ..RunOptions::default()
                },
                compile_workers: 1,
            },
        )
        .map(|run| {
            (
                run.baseline,
                run.baseline_coverage
                    .into_iter()
                    .map(|coverage| (coverage.complete, coverage.rule_ids, coverage.applied_ids))
                    .collect::<Vec<_>>(),
                run.mutants
                    .into_iter()
                    .map(|mutant| {
                        (
                            format!("{:?}", mutant.report.status),
                            mutant.report.killing_test_ids,
                            format!("{:?}", mutant.plan),
                        )
                    })
                    .collect::<Vec<_>>(),
            )
        })
        .map_err(|failure| failure.to_string())
    };
    let (path_set, state_set) = (
        verdicts(ResultModality::PathSet),
        verdicts(ResultModality::StateSet),
    );
    match (&path_set, &state_set) {
        (Ok(path_set), Ok(state_set)) => {
            assert_eq!(
                path_set.0, state_set.0,
                "{label}: campaign baseline evidence"
            );
            assert_eq!(
                path_set.1, state_set.1,
                "{label}: campaign baseline coverage"
            );
            assert_eq!(
                path_set.2.len(),
                generated.len(),
                "{label}: one mutant each"
            );
            assert_eq!(
                state_set.2.len(),
                generated.len(),
                "{label}: one mutant each"
            );
            for ((path, state), id) in path_set.2.iter().zip(&state_set.2).zip(&generated) {
                if !documented_mutants.contains(id) {
                    assert_eq!(path, state, "{label} {id}: campaign verdict");
                    tally.campaign_verdicts += 1;
                }
            }
        }
        _ => assert_eq!(path_set, state_set, "{label}: campaign"),
    }
    tally
}

#[test]
fn state_set_results_equal_path_set_results_over_the_flow_corpus_and_its_mutants() {
    let mut all = Tally::default();
    for manifest in flow_manifests() {
        // Every corpus program ends in milliseconds; a mutant that loops is cut after 3 s.
        let tally = differential(&manifest, None, true, Some(Duration::from_secs(3)), true);
        assert!(
            tally.faster.is_empty(),
            "{}: a state set finished where the path set timed out: {:?}",
            manifest.display(),
            tally.faster
        );
        all.extend(tally);
    }
    eprintln!("MODALITY {all:#?}");
    assert!(all.failed.is_empty(), "{:?}", all.failed);
    // No absorption on the corpus: every bounded leaf of a path set is one of the state set's.
    assert!(all.absorbed.is_empty(), "{:?}", all.absorbed);
    assert!(all.compared >= 250, "{}", all.compared);
    assert!(all.mutants >= 60, "{}", all.mutants);
    assert!(
        all.compared_on_mutants >= 200,
        "{}",
        all.compared_on_mutants
    );
    assert!(all.campaign_verdicts >= 50, "{}", all.campaign_verdicts);
    // register/double is where the baseline's own merge happens (L1-1 review 1 minor 4).
    assert!(
        all.merged
            .iter()
            .any(|id| id == "testdata/flow/register/FLOW.toml double"),
        "{:?}",
        all.merged
    );
}

/// The patch that replaces `rule`'s only Int token `from` by `to`.
fn replace_token(baseline: &Baseline, rule: &str, from: &str, to: &str) -> Patch {
    fn tokens(
        baseline: &Baseline,
        at: &SentenceRef,
        path: &mut Vec<u32>,
        token: &str,
    ) -> Vec<TermRef> {
        let here = TermRef::new(at.clone(), path.as_slice());
        let Some(term) = baseline.term(&here) else {
            return Vec::new();
        };
        let mut found = Vec::new();
        if matches!(term.unannotated(), Term::Token { token: t, .. } if t == token) {
            found.push(here);
        }
        for index in 0.. {
            path.push(index);
            if baseline
                .term(&TermRef::new(at.clone(), path.as_slice()))
                .is_none()
            {
                path.pop();
                break;
            }
            found.extend(tokens(baseline, at, path, token));
            path.pop();
        }
        found
    }
    let sentence = support::rule(baseline, rule);
    let [at] = (0..3)
        .flat_map(|part| tokens(baseline, &sentence, &mut vec![part], from))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap_or_else(|found: Vec<_>| panic!("{rule}: {} tokens {from}", found.len()));
    Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).unwrap().clone(),
        at,
        replacement: Term::Token {
            token: to.into(),
            sort: Sort::new("Int"),
        },
    }])
    .unwrap()
}

fn contains(term: &Pattern, symbol: &str) -> bool {
    matches!(term, Pattern::Application { symbol: head, .. } if head.name == symbol)
        || walk::children(term)
            .into_iter()
            .any(|child| contains(child, symbol))
}

/// conv.k's classifier: a configuration holding `crash(_)` is a semantic crash.
fn crash_is_a_crash(term: &Pattern) -> ExecutionTerminalKind {
    if contains(term, "Lblcrash") {
        ExecutionTerminalKind::SemanticCrash
    } else {
        ExecutionTerminalKind::Normal
    }
}

/// One converging fixture of `testdata/k/l1`: file, module, start symbol, classifier, mutations
/// (rule, token, replacement) and depth bound.
type Fixture = (
    &'static str,
    &'static str,
    &'static str,
    &'static Classifier,
    &'static [(&'static str, &'static str, &'static str)],
    Option<u64>,
);

const FIXTURES: [Fixture; 4] = [
    (
        "conv",
        "CONV",
        "Lbla",
        &crash_is_a_crash,
        &[("CONV.mc", "1", "2"), ("CONV.mc", "1", "0")],
        None,
    ),
    ("convz", "CONVZ", "Lbla", &crash_is_a_crash, &[], None),
    (
        "absorb",
        "ABSORB",
        "Lbls",
        &all_normal,
        &[("ABSORB.start", "1", "2")],
        Some(4),
    ),
    (
        "absorb",
        "ABSORB",
        "Lbls",
        &all_normal,
        &[("ABSORB.start", "1", "2")],
        None,
    ),
];

/// The converging fixtures of `testdata/k/l1` (L1-1 review 1 minors 1-4), baseline and mutants:
/// conv.k (two paths to one crash configuration; mutants `mc: 1 -> 2`, still converging, and
/// `mc: 1 -> 0`, converging undefined steps), convz.k, and absorb.k with and without a depth bound
/// that cuts one of two paths to one stuck configuration (mutant `start: 1 -> 2`). k-rust's merge
/// happens on the mutant side, the terminal classes include crashes, and the absorbed depth bound
/// is the one documented difference.
#[test]
fn state_set_results_equal_path_set_results_on_converging_fixtures() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut tally = Tally::default();
            for (name, module, start, classify, mutations, max_depth) in FIXTURES {
                let validator = NativeValidator::bind(
                    support::load_path(
                        &Path::new(support::DIR).join(format!("l1/{name}.k")),
                        module,
                    ),
                    CompileOptions::default(),
                );
                let budget = ExecutionBudget {
                    time: Duration::from_secs(20),
                    max_simplification_iterations: 10_000,
                    max_depth,
                    max_breadth: None,
                };
                let programs = vec![(
                    format!("{start}(3)"),
                    support::initial_state(support::app(start, vec![support::int(3)]), "SortProg"),
                )];
                let label = format!("{name} max_depth {max_depth:?}");
                let baseline = validator.compile_baseline().unwrap();
                compare_side(
                    &Side {
                        label: label.clone(),
                        compiled: &baseline,
                        mutant: false,
                        stepped: true,
                    },
                    module,
                    &programs,
                    budget,
                    classify,
                    &mut tally,
                );
                for (rule, from, to) in mutations {
                    let mutant = validator
                        .validate(&replace_token(validator.baseline(), rule, from, to))
                        .unwrap();
                    tally.mutants += 1;
                    compare_side(
                        &Side {
                            label: format!("{label} mutant {rule} {from}->{to}"),
                            compiled: &mutant,
                            mutant: true,
                            stepped: false,
                        },
                        module,
                        &programs,
                        budget,
                        classify,
                        &mut tally,
                    );
                }
            }
            eprintln!("MODALITY-L1 {tally:#?}");
            assert!(tally.failed.is_empty(), "{:?}", tally.failed);
            assert!(tally.faster.is_empty(), "{:?}", tally.faster);
            assert_eq!((tally.compared, tally.compared_on_mutants), (8, 4));
            // The merge happens on both conv mutants' sides.
            for mutant in [
                "conv max_depth None mutant CONV.mc 1->2 Lbla(3)",
                "conv max_depth None mutant CONV.mc 1->0 Lbla(3)",
            ] {
                assert!(
                    tally.merged_on_mutants.iter().any(|id| id == mutant),
                    "{mutant}: {:?}",
                    tally.merged_on_mutants
                );
            }
            // The absorbed depth bound, on the baseline and on the mutant, and nowhere else.
            assert_eq!(
                tally.absorbed,
                [
                    "absorb max_depth Some(4) Lbls(3)",
                    "absorb max_depth Some(4) mutant ABSORB.start 1->2 Lbls(3)",
                ]
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// The same differential over the IMP corpus (`examples/imp`) and its 21 mutants. Baseline runs
/// get a one-minute time bound (collatz's path set takes about 35 s), mutant runs the manifest's
/// 10 s: a mutant program that times out as a path set is counted, not compared. The baselines'
/// stepped coverage check is off (`primes`' observed path set runs out of a 24 GiB scope). About
/// 6 minutes and 7 GiB (the path sets): run on demand under a memory scope
/// (`cargo test -p kink-flow --test modality -- --ignored`); its result is recorded in the re-pin
/// L1-1-fix-1 handoff.
#[test]
#[ignore = "minutes and gigabytes: run on demand, recorded in the L1-1-fix-1 handoff"]
fn state_set_results_equal_path_set_results_over_imp_and_its_mutants() {
    // A mutant that loops builds deep terms: run on a big stack, as kink-flow does.
    let tally = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            differential(
                &repository().join("examples/imp/FLOW.toml"),
                Some(Duration::from_secs(60)),
                false,
                None,
                false,
            )
        })
        .unwrap()
        .join()
        .unwrap();
    eprintln!("MODALITY-IMP {tally:#?}");
    assert!(tally.failed.is_empty(), "{:?}", tally.failed);
    assert!(tally.absorbed.is_empty(), "{:?}", tally.absorbed);
    assert_eq!(tally.mutants, 21);
    // Every baseline program, collatz included, finishes within the minute.
    assert!(
        tally.faster.iter().all(|id| id.contains(" mutant ")),
        "{:?}",
        tally.faster
    );
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

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
//! For each (side, program) it compares the two result runs (kink-native `execute_result` under
//! each modality, which since fz26 KINK-PATHSET-FALLBACK is the run k-rust answers) under the
//! side's budget:
//!
//! - equal timeout (a state set that finishes where the path set timed out is counted, never
//!   compared; the reverse fails);
//! - the complete leaves as sets of (terminal class, depth for undefined steps and vacuous leaves,
//!   configuration, and for those the rule an undefined step names and the `total` claim a leaf
//!   contradicts): the class of a stuck leaf is the classifier's (normal, stuck, crash), so the
//!   deduplicated finals and their terminal classes are equal, and kink's exclusions read the
//!   same rules and claims on either run;
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
//! On the flow corpus every mutant run is bounded by depth, not by the clock: a mutant that loops
//! forever reaches the same depth bound under both modalities on any host, so its runs are
//! compared, where a wall-clock cut raced the depth bound under load and flipped the result
//! (re-pin L1-3-tail, review L1-3-fix-2-1 P2).
//!
//! On the flow corpus it also runs the campaign runner over the baseline and every mutation with
//! `RunOptions::result_modality` `PathSet` and `StateSet`, and asserts equal baseline evidence,
//! baseline coverage and, mutant by mutant, equal status, killers and plan: the corpus classifies
//! every terminal normal and no corpus leaf is absorbed, so none of the three state-set-only kill
//! routes can apply, and a verdict that depends on the modality fails the gate.
//!
//! The flow corpus runs as one kink-tier test per specification (test-gate TG-F; until then one
//! test over every manifest), each compiling a mutant once for every manifest of its
//! specification; a light test checks that these tests cover every manifest and that their
//! minimums add up to the corpus minimums the one test asserted. The converging fixtures run in
//! the kink tier, IMP in the heavy tier.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::{BTreeMap, BTreeSet};
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
use kink_native::bridge::{BridgeContext, paths_from_execution_existing};
use kink_native::coverage::{RuleAuthors, TestCoverage};
use kink_native::execution::{
    AdaptedExecution, AdaptedLeaf, ExecutionAdapter, ExecutionBudget, HaltClass, ResultModality,
    ResultRun, SolverProfile,
};
use kink_native::feasibility::TestInitialState;
use kink_native::step_events::ObservationDecider;
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::{
    Baseline, ClaimSupport, Discovery, Edit, Patch, SelectionPolicy, SentenceRef, Sha256Digest,
    TermRef, select,
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
/// classifier's), its depth for undefined steps and vacuous leaves, its configuration, and for
/// those the rule an undefined step names (`undefined_rule`) and the `total` claim the leaf
/// contradicts (`contradicted_total`), which kink's exclusions read. k-rust's leaf of an
/// undefined step names the step's rule from its own configuration, the same on every path; a
/// leaf of a remainder its own normalization refutes names the rule that produced its parent,
/// which under a state set is the witness path's (k-rust `docs/backend-port.md`), but such a
/// remainder needs a symbolic state the solver misjudges, which no input here has.
type CompleteKey = (String, Option<u64>, String, Option<String>, Option<String>);

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
                complete.insert((class, None, state, None, None));
            }
            HaltClass::Trivial | HaltClass::Vacuous => {
                complete.insert((
                    format!("{:?}", leaf.halt),
                    Some(leaf.branch.depth),
                    state,
                    leaf.undefined_rule.as_ref().map(|rule| rule.id.clone()),
                    leaf.contradicted_total
                        .as_ref()
                        .map(|claim| format!("{claim:?}")),
                ));
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
    /// Pairs whose state set has an undefined step, a vacuous leaf or a contradicted claim on a
    /// leaf: the runs kink replaced by their path sets before fz26 KINK-PATHSET-FALLBACK.
    undefined: Vec<String>,
    /// Pairs where an earlier stuck leaf absorbed a later bounded leaf of its configuration.
    absorbed: Vec<String>,
    /// Pairs a run of which the adapter refused, with the failures (never compared).
    failed: Vec<String>,
    /// Mutant pairs at least one run of which the time bound cut.
    mutant_timeouts: Vec<String>,
    /// Mutant pairs a run of which stopped at the differential's own depth bound
    /// ([`CORPUS_MUTANT_DEPTH`]), below the manifest's: compared as bounded runs.
    capped: Vec<String>,
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
        self.undefined.extend(other.undefined);
        self.absorbed.extend(other.absorbed);
        self.failed.extend(other.failed);
        self.mutant_timeouts.extend(other.mutant_timeouts);
        self.capped.extend(other.capped);
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
    /// The side's depth bound is the differential's own, below the manifest's.
    capped: bool,
}

/// The claim-free compiled mutants of a specification, by (specification digest, patch digest);
/// `None` for a mutation that resolves but has no claim-free compiled mutant.
type Mutants = BTreeMap<(Sha256Digest, Sha256Digest), Option<ValidatedDefinition>>;

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
            adapter.execute_result(
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
        if side.mutant && (path_set.timed_out() || state_set.timed_out()) {
            tally.mutant_timeouts.push(id.clone());
        }
        if side.mutant
            && side.capped
            && [&path_set, &state_set].iter().any(|run| {
                run.leaves()
                    .iter()
                    .any(|leaf| leaf.halt == HaltClass::DepthBound)
            })
        {
            tally.capped.push(id.clone());
        }
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
            .filter(|(_, depth, ..)| depth.is_none())
            .map(|(_, _, state, ..)| state)
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
            tally.undefined.push(id.clone());
        }
        assert_eq!(diagnosed(&path_set), diagnosed(&state_set), "{id}");
        assert_eq!(
            path_set.stack_stops() == 0,
            state_set.stack_stops() == 0,
            "{id}"
        );
        // The state-slot inputs: the bridged paths with their classified terminals, and how the
        // collection stopped, read as the runner's state slots read them: terminal values, and the
        // existence of an undefined step's pre-step configuration (kink27 R3-UNDEF-BRIDGE).
        let bridged = |backend: &mut k_rust::backend::Backend, execution: &AdaptedExecution| {
            backend
                .with_solver(None, |definition, solver| {
                    let decider = ObservationDecider::new(
                        definition,
                        solver,
                        TestInitialState::of_test(state),
                    );
                    Ok::<_, k_rust::backend::BackendError>(
                        paths_from_execution_existing(
                            execution,
                            &BridgeContext {
                                test_id: program,
                                classify,
                                sorts: &sorts,
                            },
                            &|term| decider.terminal_value(term),
                            &|term| decider.configuration_exists(term),
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
/// `mutant_depth` bounds the mutant runs and the campaign by depth instead of by time: their
/// depth bound becomes the smaller of the manifest's and `mutant_depth`, and their time bound
/// [`MUTANT_BACKSTOP`], which only stops a run that hangs (a mutant that loops forever then
/// reaches the same depth under both modalities and is compared, on any host); `campaign` also
/// compares the campaign runner's verdicts under both modalities.
fn differential(
    manifest_path: &Path,
    baseline_time: Option<Duration>,
    stepped: bool,
    mutant_depth: Option<u64>,
    campaign: bool,
    mutants: &mut Mutants,
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
    let mut capped = false;
    if let Some(depth) = mutant_depth {
        let manifest_depth = budget.max_depth.unwrap_or(u64::MAX);
        capped = depth < manifest_depth;
        budget.max_depth = Some(depth.min(manifest_depth));
        budget.time = MUTANT_BACKSTOP;
    }
    compare_side(
        &Side {
            label: label.clone(),
            compiled: &spec.compiled,
            mutant: false,
            stepped,
            capped: false,
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
    let spec_digest = kink_flow::digest::spec_digest(&manifest, &spec.loaded.files);
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
        // A manifest of the same specification (an equal specification digest: the same load
        // and the same source files) has the same mutant: it is compiled once per
        // specification.
        let built = mutants
            .entry((spec_digest, mutation.digest))
            .or_insert_with(|| {
                support
                    .withdraw(baseline, &mutation.patch)
                    .ok()
                    .filter(kink_patch::Withdrawal::trusted)
                    .and_then(|withdrawal| {
                        spec.validator
                            .validate(withdrawal.patch().unwrap_or(&mutation.patch))
                            .ok()
                    })
            });
        let Some(compiled) = built.as_ref() else {
            tally.not_built.push(mutant_label);
            continue;
        };
        tally.mutants += 1;
        let before = tally.documented();
        compare_side(
            &Side {
                label: mutant_label,
                compiled,
                mutant: true,
                stepped: false,
                capped,
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

/// The depth bound of the corpus differential's mutant runs, where the manifest's is deeper
/// (re-pin L1-3-tail, review L1-3-fix-2-1 P2). Every run of the corpus that ends, on the baseline
/// and on every mutant, ends within 3,001 steps (loop `FLOW-cost.toml`'s `slow`, measured for
/// L1-3-tail), so a run cut by this bound is one that does not end within 10,000 steps: a mutant
/// that loops. Under the 3 s wall-clock cut it replaced, such a run was cut by whichever of the
/// clock and the manifest's depth bound (100,000) came first, which the host's load decided:
/// `countdown-escapes` on `countdown` reaches depth 100,000 in about 2.5 s, so one modality
/// timed out and the other did not, in either direction (main and L1-3-fix-2 alike, 1 run in 4).
const CORPUS_MUTANT_DEPTH: u64 = 10_000;

/// The time bound of a depth-bounded mutant run: it never decides a run of the corpus (the
/// slowest one, `countdown-escapes` on `slow`, reaches [`CORPUS_MUTANT_DEPTH`] in well under a
/// second), it only stops a run that hangs, and the corpus test fails when it fires.
const MUTANT_BACKSTOP: Duration = Duration::from_secs(600);

/// What the differential of one specification directory of `testdata/flow` must at least
/// compare.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Minimums {
    compared: usize,
    compared_on_mutants: usize,
    mutants: usize,
    campaign_verdicts: usize,
}

const fn at_least(
    compared: usize,
    compared_on_mutants: usize,
    mutants: usize,
    campaign_verdicts: usize,
) -> Minimums {
    Minimums {
        compared,
        compared_on_mutants,
        mutants,
        campaign_verdicts,
    }
}

impl Minimums {
    fn of(tally: &Tally) -> Self {
        at_least(
            tally.compared,
            tally.compared_on_mutants,
            tally.mutants,
            tally.campaign_verdicts,
        )
    }

    fn covers(&self, minimums: &Self) -> bool {
        self.compared >= minimums.compared
            && self.compared_on_mutants >= minimums.compared_on_mutants
            && self.mutants >= minimums.mutants
            && self.campaign_verdicts >= minimums.campaign_verdicts
    }
}

/// The minimums of the whole flow corpus, which one corpus test asserted until test-gate TG-F
/// split it into one test per specification directory: the minimums of [`CORPUS`] sum to at
/// least these.
const CORPUS_MINIMUMS: Minimums = at_least(250, 200, 60, 50);

/// Every specification of `testdata/flow`: its directory and the manifests of that directory
/// that use it, with what its differential compared at test-gate TG-F as its minimums (compared
/// pairs, of them on mutants, mutants, campaign verdicts). Loop's baseline pairs under its
/// 500 ms manifests are the only ones the clock may leave uncompared (both timed out): its
/// minimum of compared pairs is 9 below the 29 compared; every other minimum is what was
/// compared.
const CORPUS: [(&str, &[&str], Minimums); 27] = [
    ("bytes-map", &["FLOW.toml"], at_least(1, 0, 0, 0)),
    (
        "calc",
        &["FLOW-bad-program.toml", "FLOW.toml"],
        at_least(42, 36, 12, 14),
    ),
    ("collections/cellmap", &["FLOW.toml"], at_least(6, 4, 2, 2)),
    ("collections/collenv", &["FLOW.toml"], at_least(9, 6, 2, 2)),
    ("collections/collimp", &["FLOW.toml"], at_least(8, 6, 3, 3)),
    (
        "collections/collstore",
        &["FLOW.toml"],
        at_least(90, 81, 9, 0),
    ),
    ("compile-error", &["FLOW.toml"], at_least(0, 0, 0, 0)),
    // fz26 KINK-PATHSET-FALLBACK, S9 (no minimum: they are there for `tests/work_budget.rs` and
    // `tests/fuzz.rs`). Listed but not run by a differential test: their programs are 2^14
    // converging paths, whose path sets the work budget or (on the unguarded baseline) the 500 ms
    // bound cuts by design, so a path set would time out where the state set finishes.
    ("diamonds", &["FLOW.toml"], at_least(0, 0, 0, 0)),
    ("diamonds/unguarded", &["FLOW.toml"], at_least(0, 0, 0, 0)),
    ("divide", &["FLOW.toml"], at_least(4, 2, 1, 1)),
    (
        "loop",
        &[
            "FLOW-cost.toml",
            "FLOW-depth.toml",
            "FLOW-search.toml",
            "FLOW-timeout.toml",
            "FLOW.toml",
        ],
        at_least(20, 20, 10, 8),
    ),
    ("macro", &["FLOW.toml"], at_least(6, 4, 2, 3)),
    ("map-store", &["FLOW.toml"], at_least(5, 4, 4, 4)),
    ("markdown", &["FLOW.toml"], at_least(28, 24, 6, 6)),
    ("markdown", &["FLOW-view.toml"], at_least(28, 24, 6, 6)),
    ("overlap", &["FLOW.toml"], at_least(3, 2, 2, 2)),
    ("register", &["FLOW.toml"], at_least(15, 12, 4, 4)),
    // fz26 KINK-BASELINE-FINDINGS: the seven repros whose baselines have findings (no minimum:
    // they are there for the baseline gate, `tests/findings.rs`).
    ("findings/diamond", &["FLOW.toml"], at_least(0, 0, 0, 0)),
    ("findings/r3-modov", &["FLOW.toml"], at_least(0, 0, 0, 0)),
    ("findings/r3-plainq", &["FLOW.toml"], at_least(0, 0, 0, 0)),
    (
        "findings/r3-propagate",
        &["FLOW.toml"],
        at_least(0, 0, 0, 0),
    ),
    ("findings/r4-empty", &["FLOW.toml"], at_least(0, 0, 0, 0)),
    ("findings/r4-hookite", &["FLOW.toml"], at_least(0, 0, 0, 0)),
    (
        "findings/r4-partnorule",
        &["FLOW.toml"],
        at_least(0, 0, 0, 0),
    ),
    // fz26 P7-KINKFLOW T3a: TRIAL2's IMP fixtures for `kink-flow fuzz` (no minimum: they are
    // there for `tests/fuzz.rs`). fuzz/imp is listed but not run by a differential test: it is
    // kink/examples/imp's IMP with seven of its mutations, whose path sets over `primes` took
    // more than 19 CPU minutes without finishing (examples/imp is not in this corpus either).
    ("fuzz/imp", &["FLOW.toml"], at_least(0, 0, 0, 0)),
    ("fuzz/impu", &["FLOW.toml"], at_least(0, 0, 0, 0)),
    ("twin", &["FLOW.toml"], at_least(3, 2, 2, 2)),
];

/// The specification directory of a flow manifest, relative to `testdata/flow`, and the
/// manifest's file name.
fn specification_of(manifest: &Path) -> (String, String) {
    (
        manifest
            .parent()
            .unwrap()
            .strip_prefix(repository().join("testdata/flow"))
            .unwrap()
            .display()
            .to_string(),
        manifest.file_name().unwrap().to_str().unwrap().to_owned(),
    )
}

/// The differential over the manifests `manifests` of the specification directory `name` of
/// `testdata/flow`, each mutant compiled once for all of them, against their [`CORPUS`]
/// minimums.
fn corpus_specification(name: &str, manifests: &[&str]) -> Tally {
    let (_, _, minimums) = CORPUS
        .iter()
        .find(|(dir, files, _)| *dir == name && *files == manifests)
        .unwrap_or_else(|| panic!("{name} {manifests:?} is not in CORPUS"));
    let dir = repository().join("testdata/flow").join(name);
    let name = format!("{name} {manifests:?}");
    let manifests = manifests
        .iter()
        .map(|file| dir.join(file))
        .collect::<Vec<_>>();
    let mut all = Tally::default();
    let mut mutants = Mutants::new();
    for manifest in manifests {
        // Every corpus program ends in milliseconds; a mutant that loops is cut at depth
        // CORPUS_MUTANT_DEPTH, never by the clock.
        let tally = differential(
            &manifest,
            None,
            true,
            Some(CORPUS_MUTANT_DEPTH),
            true,
            &mut mutants,
        );
        assert!(
            tally.faster.is_empty(),
            "{}: a state set finished where the path set timed out: {:?}",
            manifest.display(),
            tally.faster
        );
        all.extend(tally);
    }
    eprintln!("MODALITY {name} {all:#?}");
    assert!(all.failed.is_empty(), "{name}: {:?}", all.failed);
    // The depth bound decides every mutant run, never the clock: the comparison does not depend
    // on the host's speed.
    assert!(
        all.mutant_timeouts.is_empty(),
        "{name}: {:?}",
        all.mutant_timeouts
    );
    // No absorption on the corpus: every bounded leaf of a path set is one of the state set's.
    assert!(all.absorbed.is_empty(), "{name}: {:?}", all.absorbed);
    let found = Minimums::of(&all);
    assert!(
        found.covers(minimums),
        "{name}: compared {found:?}, at least {minimums:?}"
    );
    all
}

/// The corpus tests below cover every specification directory of `testdata/flow`, and their
/// minimums sum to the corpus minimums of the one corpus test they replace (test-gate TG-F): a
/// new manifest directory fails here until it has its test.
#[test]
fn the_corpus_tests_cover_every_flow_specification_and_the_corpus_minimums() {
    let found = flow_manifests()
        .iter()
        .map(|manifest| specification_of(manifest))
        .collect::<Vec<_>>();
    let listed = CORPUS
        .iter()
        .flat_map(|(dir, files, _)| {
            files
                .iter()
                .map(|file| ((*dir).to_owned(), (*file).to_owned()))
        })
        .collect::<Vec<_>>();
    // Each manifest in exactly one specification test.
    assert_eq!(
        listed.iter().collect::<BTreeSet<_>>(),
        found.iter().collect::<BTreeSet<_>>()
    );
    assert_eq!(listed.len(), found.len(), "a manifest listed twice");
    let sum = CORPUS
        .iter()
        .fold(Minimums::default(), |sum, (_, _, minimums)| {
            at_least(
                sum.compared + minimums.compared,
                sum.compared_on_mutants + minimums.compared_on_mutants,
                sum.mutants + minimums.mutants,
                sum.campaign_verdicts + minimums.campaign_verdicts,
            )
        });
    assert!(
        sum.covers(&CORPUS_MINIMUMS),
        "{sum:?} against {CORPUS_MINIMUMS:?}"
    );
}

/// State-set results equal path-set results over the flow corpus and its mutants: one test per
/// specification directory of `testdata/flow` (until test-gate TG-F one test,
/// `state_set_results_equal_path_set_results_over_the_flow_corpus_and_its_mutants`).
mod kink_tier {
    use super::*;

    #[test]
    #[ignore = "kink"]
    fn modality_on_bytes_map() {
        corpus_specification("bytes-map", &["FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_calc() {
        corpus_specification("calc", &["FLOW-bad-program.toml", "FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_cellmap() {
        corpus_specification("collections/cellmap", &["FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_collenv() {
        corpus_specification("collections/collenv", &["FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_collimp() {
        corpus_specification("collections/collimp", &["FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_collstore() {
        corpus_specification("collections/collstore", &["FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_compile_error() {
        corpus_specification("compile-error", &["FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_divide() {
        corpus_specification("divide", &["FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_loop() {
        corpus_specification(
            "loop",
            &[
                "FLOW-cost.toml",
                "FLOW-depth.toml",
                "FLOW-search.toml",
                "FLOW-timeout.toml",
                "FLOW.toml",
            ],
        );
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_macro() {
        corpus_specification("macro", &["FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_map_store() {
        corpus_specification("map-store", &["FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_markdown() {
        corpus_specification("markdown", &["FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_markdown_view() {
        corpus_specification("markdown", &["FLOW-view.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_overlap() {
        corpus_specification("overlap", &["FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_register() {
        let all = corpus_specification("register", &["FLOW.toml"]);
        // register/double is where the baseline's own merge happens (L1-1 review 1 minor 4).
        assert!(
            all.merged
                .iter()
                .any(|id| id == "testdata/flow/register/FLOW.toml double"),
            "{:?}",
            all.merged
        );
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_twin() {
        corpus_specification("twin", &["FLOW.toml"]);
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_the_findings_repros() {
        for name in [
            "findings/diamond",
            "findings/r3-modov",
            "findings/r3-plainq",
            "findings/r3-propagate",
            "findings/r4-empty",
            "findings/r4-hookite",
            "findings/r4-partnorule",
        ] {
            corpus_specification(name, &["FLOW.toml"]);
        }
    }

    #[test]
    #[ignore = "kink"]
    fn modality_on_the_fuzz_corpus_u() {
        corpus_specification("fuzz/impu", &["FLOW.toml"]);
    }

    /// The converging fixtures of `testdata/k/l1` (L1-1 review 1 minors 1-4), baseline and mutants:
    /// conv.k (two paths to one crash configuration; mutants `mc: 1 -> 2`, still converging, and
    /// `mc: 1 -> 0`, converging undefined steps), convz.k, and absorb.k with and without a depth bound
    /// that cuts one of two paths to one stuck configuration (mutant `start: 1 -> 2`). k-rust's merge
    /// happens on the mutant side, the terminal classes include crashes, and the absorbed depth bound
    /// is the one documented difference.
    #[test]
    #[ignore = "kink"]
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
                        support::initial_state(
                            support::app(start, vec![support::int(3)]),
                            "SortProg",
                        ),
                    )];
                    let label = format!("{name} max_depth {max_depth:?}");
                    let baseline = validator.compile_baseline().unwrap();
                    compare_side(
                        &Side {
                            label: label.clone(),
                            compiled: &baseline,
                            mutant: false,
                            stepped: true,
                            capped: false,
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
                                capped: false,
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

mod heavy {
    use super::*;

    /// The same differential over the IMP corpus (`examples/imp`) and its 21 mutants. Baseline runs
    /// get a one-minute time bound (collatz's path set takes about 35 s), mutant runs the manifest's
    /// 10 s: a mutant program that times out as a path set is counted, not compared. The baselines'
    /// stepped coverage check is off (`primes`' observed path set runs out of a 24 GiB scope). About
    /// 6 minutes and 7 GiB (the path sets): run on demand under a memory scope
    /// (`cargo test -p kink-flow --test modality -- --ignored`); its result is recorded in the re-pin
    /// L1-1-fix-1 handoff.
    #[test]
    // Formerly ignored as "minutes and gigabytes: run on demand, recorded in the L1-1-fix-1 handoff".
    #[ignore = "heavy"]
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
                    &mut Mutants::new(),
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

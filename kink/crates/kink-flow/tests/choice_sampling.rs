//! kink27 R2-CHOICE-SAMPLING: the premise every kill rests on, that a run with no
//! implementation-chosen mark is the same under every admissible choice (k-rust
//! `docs/compatibility.md`, "Marks in executions"), tested on the runs kink judges.
//!
//! Under k-rust-backend's test-only feature `choice-sampling`, `choice_sampling::with_seed` makes
//! every site computing a value the definition leaves open compute another value some model gives
//! (k-rust `tests/choice_sampling.rs` shows each class reached). For every manifest of the flow
//! corpus (`testdata/flow`, nested ones and the fuzz flows included) and for `examples/imp`, each
//! seed in 1 to 3 and once without a seed, the manifest is admitted (compiled, never through a
//! cache) and every admitted program run inside the seed's scope, as kink runs it (kink-native
//! `execute_result`, a state set, the manifest's budget, no work bound; stuck leaves classified
//! by `all_normal`). The test fails on:
//!
//! - (a) a default run whose `implementationChosenValues` list is empty and that the clock did not
//!   cut, whose seeded run differs in its leaves (modality.rs's `leaf_sets`), in a list of its
//!   run facts, in its effects or in whether it timed out;
//! - (b) on any default run the clock did not cut, a complete leaf without a mark (its halt and
//!   configuration; its depth is the witness's) that a seeded run lacks;
//! - (c) a seeded admission that refuses what the default admits, or a seeded run the adapter
//!   refuses or the clock cuts where the default's did not (rerun to tell load from a difference).
//!
//! A difference is a missing mark. It also reports, without failing, the work and coverage
//! differences of unmarked runs (an unnoted read that changed no leaf) and, per class, how many
//! marked runs some seed changed (the corpus's power for the class).
//!
//! The file builds only with the feature (`required-features`), so no kink tier builds it; run
//! `cargo test -p kink-flow --no-default-features --features choice-sampling --test
//! choice_sampling -- --ignored`.

use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU64;
use std::path::{Path, PathBuf};

use k_rust::backend::BackendDiagnosticOutput;
use k_rust::k_rust_backend::choice_sampling;
use k_rust::kore::{ast::Pattern, codec};
use kink_corpus::{admission::input_backend, runner::all_normal};
use kink_flow::{admit::admit, manifest::FlowManifest, results::execution_budget};
use kink_native::execution::{
    AdaptedExecution, AdaptedLeaf, ExecutionAdapter, HaltClass, ResultModality, ResultRun,
    RunFacts, SolverProfile,
};

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

fn state_text(leaf: &AdaptedLeaf) -> String {
    codec::from_value(&leaf.branch.state)
        .map(|state: Pattern| state.to_string())
        .unwrap_or_else(|_| leaf.branch.state.to_string())
}

/// modality.rs's complete-leaf key: terminal class, depth for undefined steps and vacuous
/// leaves, configuration, the rule an undefined step names and the `total` claim a leaf
/// contradicts.
type CompleteKey = (String, Option<u64>, String, Option<String>, Option<String>);
type LeafSets = (BTreeSet<CompleteKey>, BTreeSet<(String, String)>);

/// modality.rs's `leaf_sets` under `all_normal`: the complete leaves, and the other leaves as
/// (halt, configuration).
fn leaf_sets(execution: &AdaptedExecution) -> LeafSets {
    let (mut complete, mut bounded) = (BTreeSet::new(), BTreeSet::new());
    for leaf in execution.leaves() {
        let state = state_text(leaf);
        match leaf.halt {
            HaltClass::Stuck => {
                let class = codec::from_value(&leaf.branch.state)
                    .map(|term: Pattern| format!("{:?}", all_normal(&term)))
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

fn complete(leaf: &AdaptedLeaf) -> bool {
    matches!(
        leaf.halt,
        HaltClass::Stuck | HaltClass::Trivial | HaltClass::Vacuous
    )
}

fn marked(leaf: &AdaptedLeaf) -> bool {
    leaf.diagnostics.iter().any(|diagnostic| {
        matches!(
            diagnostic,
            BackendDiagnosticOutput::ImplementationChosenValue { .. }
        )
    })
}

/// What a run gives that the checks compare.
#[derive(Debug)]
struct Observed {
    leaves: LeafSets,
    /// The complete leaves as (halt, configuration), and those of them without a mark.
    ends: BTreeSet<(String, String)>,
    unmarked_ends: BTreeSet<(String, String)>,
    facts: RunFacts,
    effects: String,
    timed_out: bool,
    work: u64,
    coverage: String,
}

impl Observed {
    fn of(execution: &AdaptedExecution) -> Self {
        let end = |leaf: &AdaptedLeaf| (format!("{:?}", leaf.halt), state_text(leaf));
        let ends = execution.leaves().iter().filter(|leaf| complete(leaf));
        Self {
            leaves: leaf_sets(execution),
            ends: ends.clone().map(end).collect(),
            unmarked_ends: ends.filter(|leaf| !marked(leaf)).map(end).collect(),
            facts: execution.facts().clone(),
            effects: format!("{:?}", execution.effects()),
            timed_out: execution.timed_out(),
            work: execution.work(),
            coverage: format!("{:?}", execution.coverage()),
        }
    }

    /// The run facts' lists (the solver's undecided answers are a count, not a list).
    fn lists(&self) -> impl PartialEq + std::fmt::Debug + '_ {
        (
            &self.facts.implementation_chosen_values,
            &self.facts.contradicted_claims,
            &self.facts.allowance_refusals,
            &self.facts.unsupported_hooks,
        )
    }

    fn classes(&self) -> BTreeSet<&str> {
        self.facts
            .implementation_chosen_values
            .iter()
            .map(|value| value.class.as_str())
            .collect()
    }

    /// Whether `other` gives another result: other leaves, lists or effects.
    fn differs(&self, other: &Self) -> bool {
        self.leaves != other.leaves
            || self.lists() != other.lists()
            || self.effects != other.effects
    }
}

/// A manifest admitted and run: `None` when the specification is refused, else each program's
/// run, or the refusal of its admission or run.
type Side = Option<BTreeMap<String, Result<Observed, String>>>;

/// Admit `manifest` and run every admitted program, inside `seed`'s scope when there is one.
fn side(manifest: &Path, seed: Option<u64>) -> Side {
    let go = || {
        let manifest = FlowManifest::read(manifest).unwrap();
        let admission = admit(&manifest);
        let spec = admission.spec.as_ref()?;
        let budget = execution_budget(manifest.budget);
        let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
        let mut backend = input_backend(&spec.compiled, &manifest.spec.main_module).unwrap();
        let mut runs = BTreeMap::new();
        for program in &admission.programs {
            let run = match &program.outcome {
                Err(refusal) => Err(format!("admission: {refusal:?}")),
                Ok(test) => adapter
                    .execute_result(
                        &mut backend,
                        &test.initial_state,
                        budget,
                        ResultRun {
                            modality: ResultModality::StateSet,
                            max_work: None,
                        },
                    )
                    .map(|execution| Observed::of(&execution))
                    .map_err(|failure| format!("run: {failure:?}")),
            };
            runs.insert(program.id.clone(), run);
        }
        Some(runs)
    };
    match seed {
        Some(seed) => choice_sampling::with_seed(NonZeroU64::new(seed).unwrap(), go),
        None => go(),
    }
}

const SEEDS: [u64; 3] = [1, 2, 3];

/// What the checks found over a corpus.
#[derive(Debug, Default)]
struct Tally {
    /// Default runs compared, those of them without a mark, and those the clock cut (not
    /// compared).
    runs: usize,
    unmarked: usize,
    default_timeouts: Vec<String>,
    /// Failures (a), (b) and (c).
    failures: Vec<String>,
    /// Unmarked runs whose seeded run did other work or covered other rules, with no other
    /// difference.
    work_or_coverage: Vec<String>,
    /// Per class: the marked runs whose list names it, and those some seed changed.
    marked: BTreeMap<String, usize>,
    changed: BTreeMap<String, usize>,
}

/// The checks over `manifest`; see the module documentation.
fn check(manifest: &Path, tally: &mut Tally) {
    let label = manifest
        .strip_prefix(repository())
        .unwrap_or(manifest)
        .display()
        .to_string();
    let Some(default) = side(manifest, None) else {
        return;
    };
    let seeded = SEEDS.map(|seed| (seed, side(manifest, Some(seed))));
    for (program, default_run) in &default {
        let id = format!("{label} {program}");
        let Ok(default_run) = default_run else {
            for (seed, side) in &seeded {
                if let Some(Ok(_)) = side.as_ref().and_then(|runs| runs.get(program)) {
                    tally.failures.push(format!(
                        "{id}: seed {seed} admits and runs what the default refuses"
                    ));
                }
            }
            continue;
        };
        if default_run.timed_out {
            tally.default_timeouts.push(id);
            continue;
        }
        tally.runs += 1;
        let unmarked = default_run.facts.implementation_chosen_values.is_empty();
        if unmarked {
            tally.unmarked += 1;
        }
        let mut changed = false;
        for (seed, side) in &seeded {
            let context = format!("{id}, seed {seed}");
            let run = match side.as_ref().map(|runs| runs.get(program)) {
                None => {
                    tally
                        .failures
                        .push(format!("(c) {context}: the specification is refused"));
                    continue;
                }
                Some(None) => unreachable!("one manifest lists the same programs"),
                Some(Some(Err(refusal))) => {
                    tally.failures.push(format!("(c) {context}: {refusal}"));
                    continue;
                }
                Some(Some(Ok(run))) => run,
            };
            if run.timed_out {
                tally
                    .failures
                    .push(format!("(c) {context}: the clock cut the seeded run only"));
                continue;
            }
            changed |= default_run.differs(run);
            if unmarked {
                if default_run.leaves != run.leaves {
                    tally.failures.push(format!(
                        "(a) {context}: unmarked run's leaves {:#?} became {:#?}",
                        default_run.leaves, run.leaves
                    ));
                } else if default_run.lists() != run.lists() {
                    tally.failures.push(format!(
                        "(a) {context}: unmarked run's facts {:?} became {:?}",
                        default_run.facts, run.facts
                    ));
                } else if default_run.effects != run.effects {
                    tally.failures.push(format!(
                        "(a) {context}: unmarked run's effects {} became {}",
                        default_run.effects, run.effects
                    ));
                } else if default_run.work != run.work || default_run.coverage != run.coverage {
                    tally.work_or_coverage.push(format!(
                        "{context}: work {} / {}, coverage equal: {}",
                        default_run.work,
                        run.work,
                        default_run.coverage == run.coverage
                    ));
                }
            }
            for end in default_run.unmarked_ends.difference(&run.ends) {
                tally.failures.push(format!(
                    "(b) {context}: unmarked complete leaf {end:?} missing from the seeded run"
                ));
            }
        }
        for class in default_run.classes() {
            *tally.marked.entry(class.to_owned()).or_default() += 1;
            if changed {
                *tally.changed.entry(class.to_owned()).or_default() += 1;
            }
        }
    }
}

/// Run `check` over `manifests` on a big stack (a looping program builds deep terms, as
/// kink-flow runs it), the seed's scope opened on that thread, and assert no failure.
fn check_all(name: &str, manifests: Vec<PathBuf>) {
    let tally = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let mut tally = Tally::default();
            for manifest in &manifests {
                check(manifest, &mut tally);
            }
            tally
        })
        .unwrap()
        .join()
        .unwrap();
    eprintln!("CHOICE-SAMPLING {name} {tally:#?}");
    assert!(tally.runs > 0, "{name}: no run compared");
    assert!(tally.failures.is_empty(), "{name}: {:#?}", tally.failures);
}

mod heavy {
    use super::*;

    /// Every manifest of the flow corpus.
    #[test]
    #[ignore = "heavy"]
    fn choice_sampling_over_the_flow_corpus() {
        let manifests = flow_manifests();
        for nested in ["fuzz/imp", "fuzz/impu"] {
            assert!(
                manifests.iter().any(|manifest| manifest
                    .starts_with(repository().join("testdata/flow").join(nested))),
                "the corpus includes {nested}"
            );
        }
        check_all("flow", manifests);
    }

    /// `examples/imp`, whose budget is 10 s a run.
    #[test]
    #[ignore = "heavy"]
    fn choice_sampling_over_examples_imp() {
        check_all("imp", vec![repository().join("examples/imp/FLOW.toml")]);
    }
}

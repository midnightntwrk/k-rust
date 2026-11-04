//! Every case through the real pipeline: Cargo, rustc, the collector, and `emit-k`'s lowering.
//!
//! The rule-level cases of one base are written as batch packages, one `k::rules!` block (or
//! sentence) and one command constructor per case, and collected once per batch with
//! [`krs_cli::collect_descriptors`]. A rustc or collector error is attributed to the case whose
//! item or command declaration holds its range, those cases are recorded as refused with their
//! own errors, and the batch is collected again without them. A failure that holds an error no
//! case owns (unlocated, or in the base) is bisected: each half is judged as a batch of its own,
//! down to a case alone, whose every error is its own. Once a batch collects, each of its cases
//! is lowered and emitted in-process from the descriptors of the base and that case alone
//! ([`sub_bundle`]), exactly as `krs emit-k` lowers a whole definition. A case that needs a
//! package of its own (an initializer, a computation-subject case) is a batch of one.
//!
//! K3 follows each collected batch ([`Worker::check_closure`]): its accepted cases that are no
//! initializer are rendered together, `krs expand` prints that package, and the printed source is
//! collected as a batch of its own. Each case is located in it by its tag (every top-level item
//! naming it, and its command variant), errors are attributed and bisected as for the batches,
//! and each case's sentences are emitted from the printed base and the case's printed items, then
//! compared with the sentences the case added to its own base ([`crate::closure`]).
//!
//! K6 follows each collected batch too ([`Worker::check_native`]): it judges each accepted case's
//! definition as `krs check` judges a definition ([`krs_cli::CollectedDefinition::check`]):
//! `emit-k`'s emission, every native route's capability table and native compile, and the
//! `native-rust` route's definition load. The native compile of a base costs far more than a
//! case's sentences add to it, so the accepted cases of a batch are judged together, as one
//! definition, when that definition is exactly theirs: its sentences are the base's and each
//! case's own sentences, as each emits alone. A case's definition is then part of the batch's,
//! and a refusal is bisected, as a collection failure is, down to the case whose definition alone
//! is refused; a batch whose cases lower otherwise together is judged case by case.
//!
//! K7 runs on K6's compile ([`crate::runs`]): where a check loads the definition the run
//! commands load, each accepted case's program is configured and run on it, and the verdicts are
//! kept when the check passes. A case's command is its own, so only its sentence can take its
//! program; a case whose sentence holds no command of its own (a subject's root,
//! `Case::unkeyed`) could take another case's program, so where one shares a check with other
//! cases, each such case, and the others together, are run on definitions apart.
//!
//! K7's dependency check follows each accepted check ([`Worker::check_dependency`]): each case
//! whose run conforms is run again on a definition without what it states (its sentences, its
//! initializer, or its attribute), where some run must end otherwise in its steps or cells,
//! unless the generator states why none does; a run that does not complete shows nothing, and
//! the case deviates.
//!
//! Workers run batches concurrently, each with one Cargo target directory reused across its
//! batches; every batch package is written fresh, under a name derived from its content, so no
//! build of an earlier batch can stand in for it.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::ops::Range;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use krs_cli::{
    CollectedDefinition, Command, CommandError, CommandRequest, DiagnosticEnvelope,
    DiagnosticSeverity, EmittedDefinition, FacetSelector, MessageFormat, PackageSelector,
    RegistrationMode, collect_descriptors,
};
use krs_exec::Semantics;
use krs_ir::DescriptorBundle;
use krs_test_support::class_matrix::invariants::{
    Observed, ObservedDiagnostic, Severity, signature,
};
use krs_test_support::class_matrix::k7::{K7, Removed, Run};
use krs_test_support::class_matrix::{Base, Case, Packaging, Placed, Removal, render};

use crate::closure::{Closure, additions, compare, sentences};
use crate::runs::{Ran, Without, run_case, run_without, twin_end};

/// The source file every case is written in.
pub const SOURCE_FILE: &str = "src/lib.rs";

/// The K namespace of every batch package.
const NAMESPACE: &str = "ORG-KRS-CLASS";

/// Whether `file` is a batch package's source, rather than a file of another package (the
/// facade's own `src/lib.rs`, where the framework's sorts are declared).
fn is_case_source(file: &krs_ir::SourceFileId) -> bool {
    file.package_relative_path() == SOURCE_FILE && file.package().k_namespace() == NAMESPACE
}

/// What one case did, and where its ranges lay in the source that judged it.
#[derive(Clone, Debug)]
pub struct Judged {
    /// The case's ID.
    pub id: String,
    /// What the pipeline reported.
    pub observed: Observed,
    /// The case's item in the judging source.
    pub item: Range<usize>,
    /// The case's construct in the judging source.
    pub spelling: Range<usize>,
    /// The case's entry in the judging source.
    pub entry: Range<usize>,
    /// The case's command declaration in the judging source.
    pub command: Option<Range<usize>>,
    /// What K1 found wrong with the case's provenance keys, once it was collected: an anchor
    /// outside its node, or a semantic key that lowering found twice; `None` when the case never
    /// reached the collector's output.
    pub keys: Option<Vec<String>>,
    /// How many cases shared the source that judged the case, the case included.
    pub batch: usize,
    /// The IDs of the other cases of the source that judged the case.
    pub neighbours: Vec<String>,
    /// The K sentences the case adds to its base, once accepted.
    pub additions: Option<Vec<String>>,
    /// K3's verdict, for an accepted case that is no initializer, when the run checks closure.
    pub closure: Option<Closure>,
    /// K6's verdict, for an accepted case the table does not refuse, when the run judges it.
    pub native: Option<Native>,
    /// K7's verdict, for a case K6 accepted and K7 has a plan for, when the run runs it.
    pub ran: Option<Ran>,
    /// How the twin check's runs of the case ended, by witness
    /// ([`krs_test_support::class_matrix::twin_runs`]), for a case K6 accepted, when K7 runs.
    pub twin_ends: Vec<(&'static str, String)>,
    /// Batch interference: K7's ([`Worker::check_interference`]), where the case's run deviated
    /// beside the other cases of its check and shows another verdict alone, or K2's
    /// ([`judge_all`]), where its refusal or acceptance was an unexpected failure beside the other
    /// cases of its batch and is another alone; and what the neighbours that change it write, or
    /// that the batched verdict did not reproduce. The case is then judged by its verdict alone,
    /// and the shard fails.
    pub interference: Option<String>,
    /// K7's dependency check ([`Worker::check_dependency`]), for a case whose run conforms, when
    /// the run makes it: how the case's runs ended on the definition without what it states
    /// (`depends: ..`, `unchanged, as stated: ..`, `refused, as stated: ..`, `independent: ..`,
    /// `not made: ..`), the TSV's `k7-dependency` line.
    pub dependency: Option<String>,
}

/// How a run judges its accepted cases by K6.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NativeMode {
    /// Not at all (`KRS_CLASS_NATIVE=0`).
    Off,
    /// The accepted cases of a batch together, bisected on a refusal (the default).
    Batched,
    /// Each accepted case alone (`KRS_CLASS_NATIVE=alone`), which the batched verdicts must
    /// equal.
    Alone,
}

/// K6's verdict on the definition an accepted case emits: what `krs check` says of it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Native {
    /// `emit-k`, `build` on every backend and the run commands' definition load accept it.
    Accepted,
    /// A command refuses it, or the judgement panics.
    Refused {
        /// [`native_signature`], or the panic's message.
        signature: String,
        /// The messages of the refusal's errors, for the reader of the TSV.
        messages: Vec<String>,
    },
}

impl Native {
    /// The verdict as the pending list records it.
    #[must_use]
    pub fn signature(&self) -> String {
        match self {
            Self::Accepted => "every native route accepts the definition".to_owned(),
            Self::Refused { signature, .. } => signature.clone(),
        }
    }
}

impl Judged {
    /// The case's ranges, for [`krs_test_support::class_matrix::invariants::signature`].
    #[must_use]
    pub fn placed<'a>(&self, case: &'a Case) -> Placed<'a> {
        Placed {
            case,
            item: self.item.clone(),
            spelling: self.spelling.clone(),
            entry: self.entry.clone(),
            command: self.command.clone(),
        }
    }
}

/// How a run is carried out: the worker count, the batch size and the scratch directory.
#[derive(Clone, Debug)]
pub struct Settings {
    /// Concurrent workers, each with its own Cargo target.
    pub workers: usize,
    /// The most cases in one batch package.
    pub batch: usize,
    /// Where the workers keep their targets and packages.
    pub scratch: PathBuf,
    /// Whether accepted cases are also judged by K3: printed by `krs expand` and emitted again.
    pub closure: bool,
    /// How accepted cases are judged by K6: their definition judged as `krs check` judges it.
    pub native: NativeMode,
    /// The cases the table refuses, which K6 leaves aside even when KRS accepts them: their K is
    /// K2's deviation, not a definition the table accepts.
    pub refused_by_table: BTreeSet<String>,
    /// K7's time limit per program, when the run runs the accepted cases (K6 compiles what they
    /// run on, so K7 runs only with K6).
    pub run: Option<Duration>,
    /// Whether K7 also runs each conforming case on a definition without what it states
    /// ([`Worker::check_dependency`]).
    pub depends: bool,
    /// Where to write the K text of each batch's accepted cases, for a reference frontend to read
    /// ([`write_k_text`]); `None` writes none.
    pub k_text: Option<PathBuf>,
}

/// What K2 makes of a case's judgement, for judging a batched verdict again alone
/// ([`judge_all`]).
pub struct K2Verdict {
    /// Whether the red list does not expect it: a deviation not recorded, or a recorded one that
    /// changed.
    pub unexpected: bool,
    /// The verdict as the red list compares it: `conforms`, or the deviation's signature.
    pub observed: String,
}

/// Judge every case of `cases` through the pipeline, in ID order. `k2` is K2's verdict on a
/// judged case: a case judged beside others whose verdict is an unexpected failure is judged
/// again alone, and by that judgement ([`rejudge`]).
///
/// # Panics
///
/// Panics if a worker panics outside the lowering of a case, which the harness does not expect.
#[must_use]
pub fn judge_all(
    cases: &[&Case],
    settings: &Settings,
    k2: &(dyn Fn(&Judged) -> K2Verdict + Sync),
) -> Vec<Judged> {
    let jobs = Mutex::new(batches(cases, settings.batch));
    let judged = Mutex::new(Vec::with_capacity(cases.len()));
    let builds = AtomicUsize::new(0);
    let cost = NativeCost::default();
    std::thread::scope(|scope| {
        for index in 0..settings.workers.max(1) {
            let worker = Worker::new(settings, index, &builds, &cost);
            let jobs = &jobs;
            let judged = &judged;
            scope.spawn(move || {
                fs::create_dir_all(&worker.root).expect("the worker directory is created");
                loop {
                    let Some(job) = jobs.lock().expect("the job queue is not poisoned").pop()
                    else {
                        break;
                    };
                    let mut out = Vec::new();
                    worker.judge(job, &mut out);
                    judged
                        .lock()
                        .expect("the results are not poisoned")
                        .extend(out);
                }
            });
        }
    });
    let mut judged = judged.into_inner().expect("the results are not poisoned");
    judged.sort_by(|left, right| left.id.cmp(&right.id));
    let again = rejudge(cases, settings, &builds, &cost, k2, &mut judged);
    eprintln!(
        "[krs-class] {} cases judged in {} package builds; {again} unexpected K2 verdicts judged \
         again alone",
        judged.len(),
        builds.load(Ordering::Relaxed)
    );
    if settings.native != NativeMode::Off {
        let cases = judged
            .iter()
            .filter(|judged| judged.native.is_some())
            .count();
        let checks = cost.checks.load(Ordering::Relaxed);
        let time = Duration::from_nanos(cost.nanos.load(Ordering::Relaxed));
        let each = time / u32::try_from(checks.max(1)).unwrap_or(u32::MAX);
        eprintln!(
            "[krs-class] K6 judged {cases} cases ({:?}) in {checks} checks, {} of them in batches that lower otherwise together; {} refusals of cases together that no case alone makes; {:.1} s of worker time, {:.2} s a check",
            settings.native,
            cost.apart.load(Ordering::Relaxed),
            cost.joint.load(Ordering::Relaxed),
            time.as_secs_f64(),
            each.as_secs_f64(),
        );
    }
    if settings.native != NativeMode::Off
        && let Some(limit) = settings.run
    {
        let runs = cost.runs.load(Ordering::Relaxed);
        let time = Duration::from_nanos(cost.run_nanos.load(Ordering::Relaxed));
        let apart = Duration::from_nanos(cost.apart_nanos.load(Ordering::Relaxed));
        eprintln!(
            "[krs-class] K7 ran {runs} programs ({} s each at most) in {:.1} s of worker time, and made {} checks apart, for cases beside a subject root's sentence and for deviations run again alone, {:.1} s",
            limit.as_secs(),
            time.as_secs_f64(),
            cost.apart_checks.load(Ordering::Relaxed),
            apart.as_secs_f64(),
        );
        if settings.depends {
            eprintln!(
                "[krs-class] K7's dependency check ran {} programs in {} checks without what the cases state, {:.1} s of worker time (collections included)",
                cost.depend_runs.load(Ordering::Relaxed),
                cost.depend_checks.load(Ordering::Relaxed),
                Duration::from_nanos(cost.depend_nanos.load(Ordering::Relaxed)).as_secs_f64(),
            );
        }
    }
    judged
}

/// What K6 cost a run: the checks it made, the workers' time they took, the cases judged alone
/// because their batch lowers otherwise together, and the refusals of cases together that no
/// case alone makes; and what K7 cost: the programs it ran and their time, and the checks it
/// made to run cases apart and theirs.
#[derive(Default)]
struct NativeCost {
    checks: AtomicUsize,
    nanos: AtomicU64,
    apart: AtomicUsize,
    joint: AtomicUsize,
    runs: AtomicUsize,
    run_nanos: AtomicU64,
    apart_checks: AtomicUsize,
    apart_nanos: AtomicU64,
    depend_checks: AtomicUsize,
    depend_runs: AtomicUsize,
    depend_nanos: AtomicU64,
}

/// A worker's part in K6.
#[derive(Clone, Copy)]
struct NativeRun<'a> {
    /// The cases the table refuses, which K6 leaves aside.
    refused_by_table: &'a BTreeSet<String>,
    cost: &'a NativeCost,
    /// Whether each case is judged alone, never in a batch.
    alone: bool,
    /// K7's time limit per program, when the run runs accepted cases.
    run: Option<Duration>,
    /// Whether K7 makes its dependency check.
    depends: bool,
}

/// K7's verdicts made on one loaded definition, and the cases a panic left unrun there.
#[derive(Default)]
struct Runs {
    ran: Mutex<BTreeMap<String, Ran>>,
    twin_ends: Mutex<BTreeMap<String, Vec<(&'static str, String)>>>,
    left: Mutex<Vec<String>>,
}

/// K6's and K7's verdicts on the cases of a batch, by ID.
#[derive(Default)]
struct Verdicts {
    native: BTreeMap<String, Native>,
    ran: BTreeMap<String, Ran>,
    twin_ends: BTreeMap<String, Vec<(&'static str, String)>>,
    interference: BTreeMap<String, String>,
    dependency: BTreeMap<String, String>,
}

/// Collect `source` alone, as a package in the directory `name` of the scratch, with a target of
/// its own.
///
/// # Errors
///
/// Fails as [`collect_descriptors`] fails.
pub fn collect_source(
    settings: &Settings,
    name: &str,
    source: &str,
) -> Result<CollectedDefinition, CommandError> {
    let builds = AtomicUsize::new(0);
    let worker = Worker {
        root: settings.scratch.join(name),
        builds: &builds,
        closure: false,
        native: None,
        k_text: None,
    };
    fs::create_dir_all(&worker.root).expect("the directory is created");
    worker.collect(source)
}

/// K2's batch interference. A case's verdict is meant to be its own: its errors are attributed to
/// it by their ranges, and it is lowered from its own descriptors. But a neighbour can change what
/// its batch's crate expands at all (rustc expands nothing in a crate one of whose items it cannot
/// parse, so a case's own rustc error then stands without KRS's answer beside it), and then the
/// case's verdict depends on its batch. So each case judged beside others whose K2 verdict is an
/// unexpected failure (a deviation not recorded, or a recorded one that changed) is judged again
/// alone, and by that judgement: batching is only how the builds are shared. Where the verdict
/// alone differs, the neighbours are bisected down to those beside which it still differs
/// ([`bisect`]), which the failure names ([`interference`]); where it is the same, the batched
/// verdict stands. Returns the number of cases judged again.
fn rejudge(
    cases: &[&Case],
    settings: &Settings,
    builds: &AtomicUsize,
    cost: &NativeCost,
    k2: &(dyn Fn(&Judged) -> K2Verdict + Sync),
    judged: &mut [Judged],
) -> usize {
    let by_id = cases
        .iter()
        .map(|case| (case.id.as_str(), *case))
        .collect::<BTreeMap<_, _>>();
    let requests = judged
        .iter()
        .enumerate()
        .filter(|(_, judged)| !judged.neighbours.is_empty())
        .filter_map(|(index, judged)| {
            let verdict = k2(judged);
            verdict.unexpected.then_some((index, verdict.observed))
        })
        .collect::<Vec<_>>();
    let count = requests.len();
    let jobs = Mutex::new(requests);
    let again = Mutex::new(Vec::new());
    let batched = &*judged;
    std::thread::scope(|scope| {
        for index in 0..settings.workers.max(1).min(count) {
            let worker = Worker::new(settings, index, builds, cost);
            let (jobs, again, by_id) = (&jobs, &again, &by_id);
            scope.spawn(move || {
                fs::create_dir_all(&worker.root).expect("the worker directory is created");
                loop {
                    let Some((index, verdict)) =
                        jobs.lock().expect("the job queue is not poisoned").pop()
                    else {
                        break;
                    };
                    let judged = &batched[index];
                    let neighbours = judged
                        .neighbours
                        .iter()
                        .filter_map(|id| by_id.get(id.as_str()).copied())
                        .collect::<Vec<_>>();
                    if let Some(alone) =
                        worker.judge_alone(by_id[judged.id.as_str()], &neighbours, &verdict, k2)
                    {
                        again
                            .lock()
                            .expect("the results are not poisoned")
                            .push((index, alone));
                    }
                }
            });
        }
    });
    for (index, alone) in again.into_inner().expect("the results are not poisoned") {
        judged[index] = alone;
    }
    count
}

/// The shared cases of each base in chunks of at most `size`, and every other case alone, the
/// largest jobs last so that workers take them first.
fn batches<'a>(cases: &[&'a Case], size: usize) -> Vec<Vec<&'a Case>> {
    let mut shared = BTreeMap::<_, Vec<&Case>>::new();
    let mut jobs = Vec::new();
    for case in cases {
        match case.packaging {
            Packaging::Shared(_) => shared.entry(case.base).or_default().push(case),
            Packaging::Own(_) | Packaging::Alone(_) => jobs.push(vec![*case]),
        }
    }
    for cases in shared.into_values() {
        jobs.extend(cases.chunks(size.max(1)).map(<[&Case]>::to_vec));
    }
    jobs.sort_by_key(Vec::len);
    jobs
}

struct Worker<'a> {
    root: PathBuf,
    builds: &'a AtomicUsize,
    closure: bool,
    /// K6's settings, when the run judges it.
    native: Option<NativeRun<'a>>,
    /// [`Settings::k_text`].
    k_text: Option<&'a Path>,
}

impl<'w> Worker<'w> {
    /// The worker `index` of a run: its directory and Cargo target are the same in every phase of
    /// the run.
    fn new(
        settings: &'w Settings,
        index: usize,
        builds: &'w AtomicUsize,
        cost: &'w NativeCost,
    ) -> Self {
        Worker {
            root: settings.scratch.join(format!("worker-{index}")),
            builds,
            closure: settings.closure,
            k_text: settings.k_text.as_deref(),
            native: (settings.native != NativeMode::Off).then_some(NativeRun {
                refused_by_table: &settings.refused_by_table,
                cost,
                alone: settings.native == NativeMode::Alone,
                run: settings.run,
                depends: settings.depends,
            }),
        }
    }

    /// The worker's Cargo target, holding the configuration that compiles every collector built
    /// in it unoptimized: verdicts are diagnostics, classes, K text and runs, which no
    /// optimization level changes.
    fn target(&self) -> PathBuf {
        let target = self.root.join("target");
        krs_test_support::write_unoptimized_collector_config(&target);
        target
    }

    /// [`rejudge`] for `case`, whose K2 verdict beside `neighbours` was `batched`: its judgement
    /// alone, which carries the interference where its verdict alone differs, or `None` where the
    /// batched verdict stands. The bisection judges by K2 only: it collects and lowers, and makes
    /// no check or run.
    fn judge_alone(
        &self,
        case: &Case,
        neighbours: &[&Case],
        batched: &str,
        k2: &(dyn Fn(&Judged) -> K2Verdict + Sync),
    ) -> Option<Judged> {
        let beside = |worker: &Worker<'_>, others: &[&Case]| {
            let mut set = vec![case];
            set.extend_from_slice(others);
            let mut out = Vec::new();
            worker.judge(set, &mut out);
            out.into_iter().find(|judged| judged.id == case.id)
        };
        let mut alone = beside(self, &[])?;
        let verdict = k2(&alone).observed;
        if verdict == batched {
            return None;
        }
        let k2_only = Worker {
            root: self.root.clone(),
            builds: self.builds,
            closure: false,
            native: None,
            k_text: None,
        };
        let culprits = bisect(neighbours, |others| {
            beside(&k2_only, others).is_some_and(|judged| k2(&judged).observed != verdict)
        });
        let named = |set: &[&Case]| {
            set.iter()
                .map(|culprit| format!("`{}`", culprit.id))
                .collect::<Vec<_>>()
                .join(", ")
        };
        alone.interference = Some(interference(
            "K2",
            &culprits,
            neighbours.len(),
            batched,
            &verdict,
            named,
        ));
        Some(alone)
    }

    /// Judge `cases` as one package, attributing failures and bisecting as the module says.
    fn judge(&self, cases: Vec<&Case>, out: &mut Vec<Judged>) {
        let mut remaining = cases;
        while !remaining.is_empty() {
            let rendered = render(&remaining);
            let count = rendered.cases.len();
            match self.collect(&rendered.source) {
                Ok(collected) => {
                    // An initializer case is a batch of one, and its base does not emit without
                    // the initializer it replaces: its additions are against the base's own
                    // sentences but its configuration, which is the case's own sentence even
                    // where it equals the base's.
                    let base = if remaining[0].replaces_initializer() {
                        self.preamble_sentences(remaining[0].base).map(|sentences| {
                            sentences
                                .into_iter()
                                .filter(|sentence| !sentence.starts_with("configuration"))
                                .collect()
                        })
                    } else {
                        base_sentences(&collected, &rendered.cases)
                    };
                    let mut judged = rendered
                        .cases
                        .iter()
                        .map(|placed| {
                            back_half(&collected, &rendered.cases, placed, base.as_deref())
                        })
                        .collect::<Vec<_>>();
                    if let Some(directory) = self.k_text {
                        write_k_text(directory, &collected, &rendered.cases, &judged);
                    }
                    self.check_native(&collected, &rendered.cases, base.as_deref(), &mut judged);
                    if self.closure {
                        self.check_closure(&rendered.cases, &mut judged);
                    }
                    out.extend(judged);
                    return;
                }
                Err(error) => {
                    let diagnostics = observe_error(&error);
                    if count == 1 {
                        out.push(judged(
                            &rendered.cases[0],
                            refused(diagnostics),
                            &rendered.cases,
                        ));
                        return;
                    }
                    let mut by_case = BTreeMap::<usize, Vec<ObservedDiagnostic>>::new();
                    let mut stray = false;
                    for diagnostic in diagnostics {
                        let holder = diagnostic.range.as_ref().and_then(|range| {
                            rendered.cases.iter().position(|placed| placed.owns(range))
                        });
                        match holder {
                            Some(index) => by_case.entry(index).or_default().push(diagnostic),
                            None => stray |= diagnostic.severity == Severity::Error,
                        }
                    }
                    if stray || by_case.is_empty() {
                        let (left, right) = remaining.split_at(remaining.len() / 2);
                        let (left, right) = (left.to_vec(), right.to_vec());
                        self.judge(left, out);
                        self.judge(right, out);
                        return;
                    }
                    let refused_ids = by_case
                        .iter()
                        .map(|(index, diagnostics)| {
                            let placed = &rendered.cases[*index];
                            out.push(judged(
                                placed,
                                refused(diagnostics.clone()),
                                &rendered.cases,
                            ));
                            placed.case.id.clone()
                        })
                        .collect::<BTreeSet<_>>();
                    remaining.retain(|case| !refused_ids.contains(&case.id));
                }
            }
        }
    }

    /// K6 over a collected batch: the definition of each case that KRS accepted and the table does
    /// not refuse, the base's descriptors and the case's, judged as `krs check` judges it: the
    /// cases together, bisected ([`Self::native_bisect`]), or each alone in the alone mode.
    fn check_native(
        &self,
        collected: &CollectedDefinition,
        all: &[Placed<'_>],
        base: Option<&[String]>,
        judged: &mut [Judged],
    ) {
        let Some(run) = self.native else {
            return;
        };
        let judged_cases = judged
            .iter()
            .filter(|judged| {
                !judged.observed.refused() && !run.refused_by_table.contains(&judged.id)
            })
            .map(|judged| judged.id.as_str())
            .collect::<BTreeSet<_>>();
        let cases = all
            .iter()
            .filter(|placed| judged_cases.contains(placed.case.id.as_str()))
            .collect::<Vec<_>>();
        let mut verdicts = Verdicts::default();
        if run.alone {
            for placed in cases {
                self.native_bisect(collected, all, &[placed], base, judged, &mut verdicts);
            }
        } else {
            self.native_bisect(collected, all, &cases, base, judged, &mut verdicts);
        }
        for judged in judged {
            judged.native = verdicts.native.remove(&judged.id);
            judged.ran = verdicts.ran.remove(&judged.id);
            judged.twin_ends = verdicts.twin_ends.remove(&judged.id).unwrap_or_default();
            judged.interference = verdicts.interference.remove(&judged.id);
            judged.dependency = verdicts.dependency.remove(&judged.id);
        }
    }

    /// Judge the definition of the base and `cases` together; on a refusal, each half, down to a
    /// case alone, whose verdict is its own definition's.
    ///
    /// Two conditions make a verdict on several cases together one on each case's own definition.
    /// The definition together is exactly theirs, which [`lowers_as_alone`] checks for every set
    /// of two or more cases, the halves of a bisection included (an emission, under 0.01 s beside
    /// a check's 1 to 2 s); a set that lowers otherwise is judged case by case. And an accepted
    /// definition that holds a case's definition accepts it: this harness assumes that a refusal
    /// of `krs check` is of a sentence the definition has, or of a feature one of its sentences
    /// needs, never of a sentence it lacks, so the other cases' sentences cannot hide one. A
    /// refusal only the cases together make is no case's: its halves' verdicts stand, and the run
    /// prints it and counts it, since a flaky refusal looks the same.
    /// `KRS_CLASS_NATIVE=alone` judges each case alone, without the assumption; the two modes
    /// must give the same verdicts (the shard's TSV, `k6/` lines).
    fn native_bisect(
        &self,
        collected: &CollectedDefinition,
        all: &[Placed<'_>],
        cases: &[&Placed<'_>],
        base: Option<&[String]>,
        judged: &[Judged],
        out: &mut Verdicts,
    ) {
        // No case, no verdict: the base alone is no case's definition.
        let Some(run) = self.native.filter(|_| !cases.is_empty()) else {
            return;
        };
        if cases.len() > 1 && !lowers_as_alone(collected, all, cases, base, judged) {
            run.cost.apart.fetch_add(cases.len(), Ordering::Relaxed);
            for placed in cases {
                self.native_bisect(collected, all, &[placed], base, judged, out);
            }
            return;
        }
        let ids = cases
            .iter()
            .map(|placed| placed.case.id.as_str())
            .collect::<BTreeSet<_>>();
        let bundle = sub_bundle_of(&collected.bundle, all, |placed| {
            ids.contains(placed.case.id.as_str())
        });
        // K7 runs the cases here unless a sentence of one could take another's program.
        let together = cases.len() == 1 || cases.iter().all(|placed| !placed.case.unkeyed);
        let runnable = if together {
            runnable(cases, run)
        } else {
            Vec::new()
        };
        let runs = Runs::default();
        let visit = |semantics: &mut Semantics| self.run_all(semantics, &runnable, &runs);
        let started = Instant::now();
        let checked = catch_unwind(AssertUnwindSafe(|| {
            collected.check_visiting(bundle, (!runnable.is_empty()).then_some(&visit))
        }));
        let elapsed = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
        run.cost.checks.fetch_add(1, Ordering::Relaxed);
        run.cost.nanos.fetch_add(elapsed, Ordering::Relaxed);
        let verdict = match checked {
            Ok(Ok(_)) => Native::Accepted,
            Ok(Err(error)) => Native::Refused {
                signature: native_signature(&error),
                messages: observe_error(&error)
                    .into_iter()
                    .filter(|diagnostic| diagnostic.severity == Severity::Error)
                    .map(|diagnostic| diagnostic.message)
                    .collect(),
            },
            Err(panic) => {
                let message = panic_message(&*panic);
                Native::Refused {
                    signature: format!("panic: {message}"),
                    messages: vec![message],
                }
            }
        };
        match (verdict, cases) {
            (Native::Accepted, _) => {
                for placed in cases {
                    out.native.insert(placed.case.id.clone(), Native::Accepted);
                }
                self.keep_runs(collected, all, cases, runs, out);
                if !together {
                    self.run_apart(collected, all, cases, out);
                }
                self.check_interference(collected, all, cases, judged, out);
                self.check_dependency(collected, all, cases, out);
            }
            (refused, [placed]) => {
                out.native.insert(placed.case.id.clone(), refused);
            }
            (refused, _) => {
                let (left, right) = cases.split_at(cases.len() / 2);
                self.native_bisect(collected, all, left, base, judged, out);
                self.native_bisect(collected, all, right, base, judged, out);
                let alone = cases.iter().any(|placed| {
                    matches!(
                        out.native.get(&placed.case.id),
                        Some(Native::Refused { .. })
                    )
                });
                if !alone {
                    run.cost.joint.fetch_add(1, Ordering::Relaxed);
                    eprintln!(
                        "[krs-class] K6: {} cases together are refused, none alone ({}): {}",
                        cases.len(),
                        cases[0].case.id,
                        refused.signature()
                    );
                }
            }
        }
    }

    /// K7 over `cases`, on the definition `semantics` loaded: each case's plan, run within the time
    /// limit, and where it conforms its counter-witnesses' plans, in order, none of which may apply
    /// (the first that does is the verdict). A panic of a
    /// run is its case's verdict, and the semantics it left is not used again: the cases after it
    /// are left to be run apart ([`Self::keep_runs`]).
    fn run_all(&self, semantics: &mut Semantics, cases: &[&Placed<'_>], runs: &Runs) {
        let Some(run) = self.native else {
            return;
        };
        let Some(limit) = run.run else {
            return;
        };
        for (index, placed) in cases.iter().enumerate() {
            let own = placed.case.command().map(|command| command.name.as_str());
            let started = Instant::now();
            let mut panicked = false;
            let twin_runs = krs_test_support::class_matrix::twin_runs(placed.case);
            if !twin_runs.is_empty() {
                let root = placed
                    .case
                    .term
                    .as_ref()
                    .is_some_and(|term| term.path.is_empty());
                let ends = twin_runs
                    .iter()
                    .map(|(witness, twin)| {
                        let end = catch_unwind(AssertUnwindSafe(|| {
                            twin_end(semantics, twin, root, limit)
                        }))
                        .unwrap_or_else(|panic| {
                            panicked = true;
                            format!("panic: {}", panic_message(&*panic))
                        });
                        (*witness, end)
                    })
                    .collect();
                runs.twin_ends
                    .lock()
                    .expect("the runs are not poisoned")
                    .insert(placed.case.id.clone(), ends);
            }
            let K7::Run(plan) = &placed.case.k7 else {
                if panicked {
                    runs.left.lock().expect("the runs are not poisoned").extend(
                        cases[index + 1..]
                            .iter()
                            .map(|placed| placed.case.id.clone()),
                    );
                    return;
                }
                continue;
            };
            let mut once = |plan| {
                catch_unwind(AssertUnwindSafe(|| run_case(semantics, plan, limit, own)))
                    .unwrap_or_else(|panic| {
                        panicked = true;
                        Ran::Deviates(format!("panic: {}", panic_message(&*panic)))
                    })
            };
            let mut verdict = once(plan);
            for counter in &placed.case.k7_counters {
                if !matches!(verdict, Ran::Conforms(_)) {
                    break;
                }
                if let Ran::Deviates(deviation) = once(counter) {
                    verdict = Ran::Deviates(format!(
                        "counter-witness `{}`: {deviation}",
                        counter.program
                    ));
                }
            }
            for input in &placed.case.k7_inputs {
                if !matches!(verdict, Ran::Conforms(_)) {
                    break;
                }
                if let Ran::Deviates(deviation) = once(input) {
                    verdict =
                        Ran::Deviates(format!("in its run of `{}`: {deviation}", input.program));
                }
            }
            let elapsed = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
            run.cost.runs.fetch_add(1, Ordering::Relaxed);
            run.cost.run_nanos.fetch_add(elapsed, Ordering::Relaxed);
            runs.ran
                .lock()
                .expect("the runs are not poisoned")
                .insert(placed.case.id.clone(), verdict);
            if panicked {
                runs.left.lock().expect("the runs are not poisoned").extend(
                    cases[index + 1..]
                        .iter()
                        .map(|placed| placed.case.id.clone()),
                );
                return;
            }
        }
    }

    /// K7's batch interference. A case's sentence is meant to change only what its own command
    /// runs, so its K7 verdict must not depend on the cases it shares a definition with; but a
    /// neighbour's sentence can change a symbol of the base (a function context on the base's
    /// `Probe` makes every application of it carry the configuration), and then the verdict
    /// does. So each case of `cases` whose run deviated beside other cases (the keyed cases run
    /// together; an unkeyed one runs alone already) is run again on a definition of its own, and
    /// judged by that run: the case's meaning is its run on its own definition, and batching is
    /// only how the runs are shared ([`adopted`]). Where the two verdicts differ in any way (it
    /// conforms alone, or deviates otherwise), the neighbours are bisected down to those beside
    /// which its verdict still differs from its own ([`bisect`]), whose sentences the failure
    /// names; where no half reproduces the difference and the whole neighbour set, run again,
    /// does not either, the batched verdict did not reproduce, a distinct failure that names no
    /// neighbour ([`interference`]). A deviation the case shows alone too is its own, and stands.
    fn check_interference<'a>(
        &self,
        collected: &CollectedDefinition,
        all: &[Placed<'a>],
        cases: &[&Placed<'a>],
        judged: &[Judged],
        out: &mut Verdicts,
    ) {
        let keyed = cases
            .iter()
            .filter(|placed| !placed.case.unkeyed)
            .copied()
            .collect::<Vec<_>>();
        if keyed.len() < 2 {
            return;
        }
        for placed in &keyed {
            let Some(batched @ Ran::Deviates(_)) = out.ran.get(&placed.case.id).cloned() else {
                continue;
            };
            let Some(alone) = adopted(&batched, self.ran_beside(collected, all, placed, &[]))
            else {
                continue;
            };
            let neighbours = keyed
                .iter()
                .filter(|other| other.case.id != placed.case.id)
                .copied()
                .collect::<Vec<_>>();
            let culprits = bisect(&neighbours, |beside| {
                self.ran_beside(collected, all, placed, beside)
                    .is_some_and(|ran| ran != alone)
            });
            let named = |culprits: &[&Placed<'_>]| {
                culprits
                    .iter()
                    .map(|culprit| {
                        let sentences = judged
                            .iter()
                            .find(|judged| judged.id == culprit.case.id)
                            .and_then(|judged| judged.additions.as_ref())
                            .map_or_else(
                                || "no sentence known".to_owned(),
                                |sentences| sentences.join(" | ").replace('\n', " "),
                            );
                        format!("`{}` (its sentences: {sentences})", culprit.case.id)
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            out.interference.insert(
                placed.case.id.clone(),
                interference(
                    "K7",
                    &culprits,
                    neighbours.len(),
                    &batched.signature(),
                    &alone.signature(),
                    named,
                ),
            );
            out.ran.insert(placed.case.id.clone(), alone);
        }
    }

    /// K7's dependency check. A witness is evidence of what a case states only if its runs
    /// depend on it: so each case of `cases` whose run conforms is run again, by the same plans,
    /// on a definition without what the case states ([`Removal`]), and judged by how those runs
    /// end ([`Without`], steps and cells only): some run must end otherwise, unless the
    /// generator states that none does ([`Removed::Unchanged`], which the check then requires)
    /// or that no such definition exists ([`Removed::Refused`], which it requires too).
    /// - The case's sentences ([`Removal::Sentences`]): one definition of the base and every
    ///   case's command, a static clause's production unmarked and its writing rule kept
    ///   ([`without_sentences`]). Each case's command is its own production, which no other case's
    ///   sentence rewrites, so one definition serves every case of the check. Each case's own
    ///   plan is run.
    /// - The case's initializer ([`Removal::Initializer`]): the base with its own initializer,
    ///   collected once per run ([`Self::preamble`]).
    /// - The case's attribute ([`Removal::Attribute`]): the cases rendered without their
    ///   attributes ([`krs_test_support::class_matrix::without_attribute`]) and collected as one
    ///   package; its plan and its counter run are run, since an attribute that orders a
    ///   sentence among its sibling's shows in the run where both match.
    ///
    /// The check shows that what the case states takes part in its runs (a step taken, an
    /// expansion made, a cell's value), not that a stated value depends on how the construct at
    /// the case's hole is lowered: that is the stated value's own evidence, at the one input the
    /// generator states (`x` = 1).
    ///
    /// A run that does not complete shows nothing: the check is not made, and the case deviates
    /// with why, as it does where the definition without it is refused (bisected down to one
    /// case, so that the reason is the case's own, [`Self::runs_without`]). Every outcome is
    /// recorded (`dependency`, the TSV's `k7-dependency` lines).
    fn check_dependency(
        &self,
        collected: &CollectedDefinition,
        all: &[Placed<'_>],
        cases: &[&Placed<'_>],
        out: &mut Verdicts,
    ) {
        let Some(run) = self.native.filter(|run| run.depends) else {
            return;
        };
        let Some(limit) = run.run else {
            return;
        };
        let conforming = cases
            .iter()
            .filter(|placed| {
                matches!(placed.case.k7, K7::Run(_))
                    && matches!(out.ran.get(&placed.case.id), Some(Ran::Conforms(_)))
            })
            .copied()
            .collect::<Vec<_>>();
        if conforming.is_empty() {
            return;
        }
        let of = |removal| {
            conforming
                .iter()
                .filter(|placed| placed.case.removal() == removal)
                .copied()
                .collect::<Vec<_>>()
        };
        let mut ended = BTreeMap::new();
        let sentences = of(Removal::Sentences);
        ended.extend(self.runs_without(&sentences, limit, &|set| {
            Ok(Definition::Of(
                collected,
                without_sentences(&collected.bundle, all, set),
            ))
        }));
        for placed in of(Removal::Initializer) {
            ended.extend(self.runs_without(&[placed], limit, &|_| {
                self.preamble(placed.case.base)
                    .map(|base| Definition::Of(base, base.bundle.clone()))
                    .ok_or_else(|| {
                        NotMade::refused("the base alone does not collect", String::new())
                    })
            }));
        }
        // A case whose definition without its attribute is refused is judged alone, so that the
        // others' are made together.
        let (refused, attributed): (Vec<_>, Vec<_>) = of(Removal::Attribute)
            .into_iter()
            .partition(|placed| matches!(placed.case.removed(), Removed::Refused(_)));
        let without_attribute = |set: &[&Placed<'_>]| {
            let without = set
                .iter()
                .map(|placed| {
                    krs_test_support::class_matrix::without_attribute(placed.case)
                        .expect("an attribute case has a case without its attribute")
                })
                .collect::<Vec<_>>();
            let rendered = render(&without.iter().collect::<Vec<_>>());
            self.collect(&rendered.source)
                .map(|collected| {
                    let bundle = collected.bundle.clone();
                    Definition::Collected(Box::new(collected), bundle)
                })
                .map_err(|error| refusal("the case without its attribute", &error))
        };
        ended.extend(self.runs_without(&attributed, limit, &without_attribute));
        for placed in refused {
            ended.extend(self.runs_without(&[placed], limit, &without_attribute));
        }
        for placed in conforming {
            let id = &placed.case.id;
            let outcome = ended.remove(id).map_or_else(
                || Outcome::NotMade(NotMade::refused("its runs were not made", String::new())),
                Outcome::of,
            );
            let (deviation, line) = judge_dependency(&placed.case.removed(), outcome);
            if let Some(deviation) = deviation {
                out.ran.insert(id.clone(), Ran::Deviates(deviation));
            }
            out.dependency.insert(id.clone(), line);
        }
    }

    /// The runs of each case of `cases` ([`dependency_runs`]) on the definition `make` gives
    /// for a set of them, by case ID. Where that definition is refused (or `make` refuses it),
    /// a refusal of several cases' definition is no one case's, so the set is bisected down to a
    /// case alone, whose refusal is its own. A run that panics is its case's end, and the
    /// semantics it left is not used again: the cases after it are run on a fresh load.
    fn runs_without<'d>(
        &self,
        cases: &[&Placed<'_>],
        limit: Duration,
        make: &dyn Fn(&[&Placed<'_>]) -> Result<Definition<'d>, NotMade>,
    ) -> BTreeMap<String, Result<Vec<Without>, NotMade>> {
        let mut ended = BTreeMap::new();
        if cases.is_empty() {
            return ended;
        }
        // The definition's making (a collection, for an attribute case) is the check's cost too.
        let started = Instant::now();
        let built = make(cases);
        if let Some(run) = self.native {
            let elapsed = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
            run.cost.depend_nanos.fetch_add(elapsed, Ordering::Relaxed);
        }
        let refused = match built {
            Ok(definition) => match self.run_on_definition(&definition, cases, limit) {
                Ok(runs) => return runs,
                Err(refused) => refused,
            },
            Err(refused) => refused,
        };
        if let [placed] = cases {
            ended.insert(placed.case.id.clone(), Err(refused));
        } else {
            let (left, right) = cases.split_at(cases.len() / 2);
            ended.extend(self.runs_without(left, limit, make));
            ended.extend(self.runs_without(right, limit, make));
        }
        ended
    }

    /// [`Self::runs_without`] on one definition: its check, visiting the cases in turn until one
    /// panics, then again for the cases after it. `Err` where the definition is refused before
    /// any case runs.
    fn run_on_definition(
        &self,
        definition: &Definition<'_>,
        cases: &[&Placed<'_>],
        limit: Duration,
    ) -> Result<BTreeMap<String, Result<Vec<Without>, NotMade>>, NotMade> {
        let cost = self.native.map(|run| run.cost);
        let mut ended = BTreeMap::new();
        let mut remaining = cases;
        while !remaining.is_empty() {
            let visited = Mutex::new(Vec::new());
            let visit = |semantics: &mut Semantics| {
                let mut visited = visited.lock().expect("the runs are not poisoned");
                visited.clear();
                for placed in remaining {
                    let mut ends = Vec::new();
                    for plan in dependency_runs(placed.case) {
                        if let Some(cost) = cost {
                            cost.depend_runs.fetch_add(1, Ordering::Relaxed);
                        }
                        match catch_unwind(AssertUnwindSafe(|| {
                            run_without(
                                semantics,
                                plan,
                                limit,
                                placed.case.removal() == Removal::Initializer,
                            )
                        })) {
                            Ok(end) => ends.push(end),
                            Err(panic) => {
                                visited.push(Err(NotMade::run(format!(
                                    "panic: {}",
                                    panic_message(&*panic)
                                ))));
                                return;
                            }
                        }
                    }
                    visited.push(Ok(ends));
                }
            };
            let started = Instant::now();
            let checked = catch_unwind(AssertUnwindSafe(|| {
                definition
                    .collected()
                    .check_visiting(definition.bundle().clone(), Some(&visit))
            }));
            if let Some(cost) = cost {
                let elapsed = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
                cost.depend_checks.fetch_add(1, Ordering::Relaxed);
                cost.depend_nanos.fetch_add(elapsed, Ordering::Relaxed);
            }
            let visited = visited.into_inner().expect("the runs are not poisoned");
            let panicked = matches!(visited.last(), Some(Err(_)));
            if visited.is_empty() {
                let refused = match &checked {
                    Ok(Ok(_)) => NotMade::refused("its runs were not made", String::new()),
                    Ok(Err(error)) => refusal("the definition without what the case states", error),
                    Err(panic) => NotMade::refused(
                        &format!("the check panicked: {}", panic_message(&**panic)),
                        String::new(),
                    ),
                };
                if ended.is_empty() {
                    return Err(refused);
                }
                for placed in remaining {
                    ended.insert(placed.case.id.clone(), Err(refused.clone()));
                }
                break;
            }
            let count = visited.len();
            for (placed, end) in remaining.iter().zip(visited) {
                ended.insert(placed.case.id.clone(), end);
            }
            remaining = &remaining[count..];
            if !panicked {
                // A check that loaded the definition visits every case, so none is left.
                for placed in remaining {
                    ended.insert(
                        placed.case.id.clone(),
                        Err(NotMade::run("its runs were not made".to_owned())),
                    );
                }
                break;
            }
        }
        Ok(ended)
    }

    /// K7's verdict on `placed`, run on the definition of the base, `placed` and `beside`.
    fn ran_beside<'a>(
        &self,
        collected: &CollectedDefinition,
        all: &[Placed<'a>],
        placed: &Placed<'a>,
        beside: &[&Placed<'a>],
    ) -> Option<Ran> {
        let mut set = vec![placed];
        set.extend_from_slice(beside);
        let mut out = Verdicts::default();
        self.run_on(collected, all, &set, &mut out);
        out.ran.remove(&placed.case.id)
    }

    /// Keep the runs of an accepted check of `cases`, and run each case a panic left unrun on a
    /// definition of its own.
    fn keep_runs(
        &self,
        collected: &CollectedDefinition,
        all: &[Placed<'_>],
        cases: &[&Placed<'_>],
        runs: Runs,
        out: &mut Verdicts,
    ) {
        out.ran
            .extend(runs.ran.into_inner().expect("the runs are not poisoned"));
        out.twin_ends.extend(
            runs.twin_ends
                .into_inner()
                .expect("the runs are not poisoned"),
        );
        let left = runs.left.into_inner().expect("the runs are not poisoned");
        for placed in cases.iter().filter(|placed| left.contains(&placed.case.id)) {
            self.run_on(collected, all, &[*placed], out);
        }
    }

    /// K7 over accepted `cases` of which some sentence holds no command of its own: the cases
    /// that each hold one, together, and each other case alone, each on its own definition.
    fn run_apart(
        &self,
        collected: &CollectedDefinition,
        all: &[Placed<'_>],
        cases: &[&Placed<'_>],
        out: &mut Verdicts,
    ) {
        if self.native.is_none() {
            return;
        }
        let keyed = cases
            .iter()
            .filter(|placed| !placed.case.unkeyed)
            .copied()
            .collect::<Vec<_>>();
        let mut sets = vec![keyed];
        sets.extend(
            cases
                .iter()
                .filter(|placed| placed.case.unkeyed)
                .map(|placed| vec![*placed]),
        );
        for set in sets {
            self.run_on(collected, all, &set, out);
        }
    }

    /// K7 over `set` on the definition of the base and `set` alone, made by a check of its own.
    fn run_on(
        &self,
        collected: &CollectedDefinition,
        all: &[Placed<'_>],
        set: &[&Placed<'_>],
        out: &mut Verdicts,
    ) {
        let Some(run) = self.native else {
            return;
        };
        let runnable = runnable(set, run);
        if runnable.is_empty() {
            return;
        }
        let ids = set
            .iter()
            .map(|placed| placed.case.id.as_str())
            .collect::<BTreeSet<_>>();
        let bundle = sub_bundle_of(&collected.bundle, all, |placed| {
            ids.contains(placed.case.id.as_str())
        });
        let runs = Runs::default();
        let visit = |semantics: &mut Semantics| self.run_all(semantics, &runnable, &runs);
        let started = Instant::now();
        let checked = catch_unwind(AssertUnwindSafe(|| {
            collected.check_visiting(bundle, Some(&visit))
        }));
        let elapsed = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
        run.cost.apart_checks.fetch_add(1, Ordering::Relaxed);
        run.cost.apart_nanos.fetch_add(elapsed, Ordering::Relaxed);
        match checked {
            Ok(Ok(_)) => self.keep_runs(collected, all, &runnable, runs, out),
            // Accepted together, refused apart: no definition of the case's own to run on.
            refused => {
                let why = match refused {
                    Ok(Err(error)) => native_signature(&error),
                    Err(panic) => format!("panic: {}", panic_message(&*panic)),
                    Ok(Ok(_)) => unreachable!("an accepted check is matched above"),
                };
                for placed in runnable
                    .iter()
                    .filter(|placed| matches!(placed.case.k7, K7::Run(_)))
                {
                    out.ran.insert(
                        placed.case.id.clone(),
                        Ran::Deviates(format!(
                            "K6 accepts the case beside the others of its batch, but refuses it apart: {why}"
                        )),
                    );
                }
            }
        }
    }

    /// The sentences `base` emits alone, with its own initializer; collected once per run, by the
    /// first worker that needs them.
    fn preamble_sentences(&self, base: Base) -> Option<Vec<String>> {
        static PREAMBLES: [OnceLock<Option<Vec<String>>>; Base::ALL.len()] =
            [const { OnceLock::new() }; Base::ALL.len()];
        PREAMBLES[base_index(base)]
            .get_or_init(|| {
                let collected = self.preamble(base)?;
                let emitted = collected.emit_k(collected.bundle.clone()).ok()?;
                Some(emitted_sentences(&emitted))
            })
            .clone()
    }

    /// `base` alone, with its own initializer, collected once per run by the first worker that
    /// needs it; `None` where it does not collect.
    fn preamble(&self, base: Base) -> Option<&'static CollectedDefinition> {
        static COLLECTED: [OnceLock<Option<CollectedDefinition>>; Base::ALL.len()] =
            [const { OnceLock::new() }; Base::ALL.len()];
        COLLECTED[base_index(base)]
            .get_or_init(|| self.collect(&base.preamble()).ok())
            .as_ref()
    }

    /// Write `source` as a fresh package and collect it.
    fn collect(&self, source: &str) -> Result<CollectedDefinition, CommandError> {
        let (collected, directory) = self.collect_kept(source);
        // The package's build lives in the worker's target; its sources are not needed again.
        let _ = fs::remove_dir_all(&directory);
        collected
    }

    /// [`Self::collect`], keeping the package's directory, which the caller removes.
    fn collect_kept(&self, source: &str) -> (Result<CollectedDefinition, CommandError>, PathBuf) {
        let build = self.builds.fetch_add(1, Ordering::Relaxed);
        let name = format!("krs_class_{:016x}", fnv1a64(source));
        let directory = self.root.join(format!("{build:05}-{name}"));
        let manifest = write_package(&directory, &name, source);
        let request = CommandRequest {
            command: Command::EmitK {
                output: directory.join("emitted"),
                ir: false,
            },
            manifest_path: manifest,
            root: FacetSelector {
                package: PackageSelector::Name(name),
                definition: "main".to_owned(),
            },
            dependencies: Vec::new(),
            cfg: Vec::new(),
            registration: RegistrationMode::Inventory,
            no_reuse: true,
            message_format: MessageFormat::Json,
            profile: None,
        };
        (
            collect_descriptors(&request, Some(&self.target())),
            directory,
        )
    }
}

/// The message of a caught panic: its payload's text, without the location rustc's hook prints.
/// The verdict of a case whose run deviated beside other cases, `batched`, given its run on a
/// definition of its own, `alone`: the run alone's, where the two differ in any way, or `None`
/// where the batched verdict stands (the same deviation alone, or no run alone).
fn adopted(batched: &Ran, alone: Option<Ran>) -> Option<Ran> {
    alone.filter(|alone| alone != batched)
}

/// The neighbours a case's verdict depends on, bisected ([`bisect`]).
#[derive(Clone, Debug, Eq, PartialEq)]
enum Culprits<T> {
    /// Beside these, a proper part of the neighbours, the verdict still differs from its own:
    /// one case, or a set no half of which makes it differ.
    Narrowed(Vec<T>),
    /// No half makes it differ, and the whole neighbour set, run again, still does.
    Whole(Vec<T>),
    /// No half makes it differ, and neither does the whole neighbour set run again: the batched
    /// verdict did not reproduce.
    NotReproduced,
}

/// Bisect `neighbours` by `differs` (whether the case's verdict beside a set of them differs
/// from its own): halved while one half makes it differ, down to one case, or to a set no half
/// of which does. A set the halving reached was run beside the case and differs; the whole set
/// was run only as the batch, so where the halving stops at it, it is run beside the case once
/// more before it is named.
fn bisect<T: Copy>(neighbours: &[T], mut differs: impl FnMut(&[T]) -> bool) -> Culprits<T> {
    let mut set = neighbours.to_vec();
    while set.len() > 1 {
        let (left, right) = set.split_at(set.len() / 2);
        if differs(left) {
            set = left.to_vec();
        } else if differs(right) {
            set = right.to_vec();
        } else {
            break;
        }
    }
    if set.len() < neighbours.len() {
        Culprits::Narrowed(set)
    } else if differs(&set) {
        Culprits::Whole(set)
    } else {
        Culprits::NotReproduced
    }
}

/// The failure of a case whose batched verdict of `test` (`K2`, `K7`), with the signature
/// `batched`, differs from its verdict alone, `alone`, beside `count` neighbours that `culprits`
/// bisected; `named` names a set of them.
fn interference<T>(
    test: &str,
    culprits: &Culprits<T>,
    count: usize,
    batched: &str,
    alone: &str,
    named: impl Fn(&[T]) -> String,
) -> String {
    match culprits {
        Culprits::Narrowed(set) | Culprits::Whole(set) => format!(
            "batch interference: {test} deviates beside {count} other cases ({batched}), and \
             alone it is {alone}; it still differs beside {}",
            named(set)
        ),
        Culprits::NotReproduced => format!(
            "{test}'s batched verdict did not reproduce (flaky?): it deviated beside {count} other \
             cases ({batched}), and alone it is {alone}, from which its verdict beside the same \
             cases again does not differ; it is judged by its verdict alone"
        ),
    }
}

fn panic_message(panic: &(dyn std::any::Any + Send)) -> String {
    panic
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| panic.downcast_ref::<&str>().map(|text| (*text).to_owned()))
        .unwrap_or_else(|| "a panic without a message".to_owned())
}

/// K6's signature of a refusal of `krs check`: who refuses, from the notes the check adds (the
/// refusing route by name, `every native route`, `load` for the run commands' definition load,
/// `emit-k`), then the code of each error, or an uncoded error's message. A refusal's codes name
/// the mistake without the definition's names, so the signature stays put while the case does.
fn native_signature(error: &CommandError) -> String {
    let mut refusers = Vec::new();
    let mut source = error;
    loop {
        match source {
            CommandError::Warned { source: inner, .. } => source = inner,
            CommandError::Attributed {
                note,
                source: inner,
            } => {
                refusers.push(refuser(note));
                source = inner;
            }
            _ => break,
        }
    }
    let errors = observe_error(error)
        .into_iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .map(|diagnostic| {
            diagnostic.code.unwrap_or_else(|| {
                let message = diagnostic.message.lines().next().unwrap_or_default();
                format!("uncoded: {message}")
            })
        })
        .collect::<Vec<_>>();
    format!("{} {}", refusers.join(" "), errors.join(", "))
        .trim()
        .to_owned()
}

/// The command or route a note of `krs check` names as refusing: the route a note opens with in
/// backquotes (`` `native-rust` is the route of .. ``), or the command it names.
fn refuser(note: &str) -> String {
    if note.starts_with("every native route") {
        "every native route".to_owned()
    } else if note.starts_with("`krs emit-k`") {
        "emit-k".to_owned()
    } else if note.starts_with("`krs run`") {
        "load".to_owned()
    } else if let Some(route) = note
        .strip_prefix('`')
        .and_then(|rest| rest.split_once('`'))
        .map(|(route, _)| route)
    {
        route.to_owned()
    } else {
        note.to_owned()
    }
}

/// Lower and emit one case of a collected batch from the base's descriptors and its own.
fn back_half(
    collected: &CollectedDefinition,
    all: &[Placed<'_>],
    placed: &Placed<'_>,
    base: Option<&[String]>,
) -> Judged {
    let bundle = sub_bundle(&collected.bundle, all, Some(placed));
    let mut keys = anchors_outside(&bundle, all, placed);
    let emitted = catch_unwind(AssertUnwindSafe(|| collected.emit_k(bundle)));
    let mut judged = match emitted {
        Ok(Ok(emitted)) => {
            let observed = Observed {
                accepted: true,
                diagnostics: observe_reports(&emitted.warnings.envelopes),
                panic: None,
            };
            let mut judged = judged(placed, observed, all);
            judged.additions = base.map(|base| additions(&emitted_sentences(&emitted), base));
            judged
        }
        Ok(Err(error)) => judged(placed, refused(observe_error(&error)), all),
        Err(panic) => {
            let message = panic_message(&*panic);
            let observed = Observed {
                accepted: false,
                diagnostics: Vec::new(),
                panic: Some(message),
            };
            judged(placed, observed, all)
        }
    };
    keys.extend(
        judged
            .observed
            .diagnostics
            .iter()
            .filter_map(|diagnostic| duplicate_key(&diagnostic.message)),
    );
    keys.sort();
    keys.dedup();
    judged.keys = Some(keys);
    judged
}

/// The anchors of `bundle` that lie where they cannot belong (K1: each anchor lies inside its
/// node, as far as the generator knows the nodes): an anchor of a descriptor declared in the
/// case's item outside the case's text, or any anchor inside another case's text. A descriptor
/// declared in the base, the case's command constructor included (its family's header is the
/// base's), may anchor in the base and in the case.
fn anchors_outside(
    bundle: &DescriptorBundle,
    all: &[Placed<'_>],
    placed: &Placed<'_>,
) -> Vec<String> {
    let mut outside = Vec::new();
    for descriptor in bundle.descriptors() {
        let declared_in_item = case_range(descriptor.origin())
            .is_some_and(|range| placed.item.start <= range.start && range.end <= placed.item.end);
        for origin in descriptor.provenance().origins() {
            let Some(range) = case_range(&origin.origin) else {
                continue;
            };
            let in_other = all
                .iter()
                .any(|other| other.case.id != placed.case.id && other.owns(&range));
            if in_other || (declared_in_item && !placed.owns(&range)) {
                outside.push(format!(
                    "the {:?} anchor of a {:?} descriptor lies outside its node",
                    origin.key.role(),
                    descriptor.id().item_kind(),
                ));
            }
        }
    }
    outside
}

/// The exact authored range of `origin` in the batch package's source.
fn case_range(origin: &krs_ir::OriginStack) -> Option<Range<usize>> {
    let range = origin
        .exact_authored_range()
        .filter(|range| is_case_source(&range.file))?;
    Some(range.start_byte as usize..range.end_byte as usize)
}

/// The K1 deviation a lowering message reports, if it reports a semantic key found twice. The
/// key's digest, which names the package, is left out.
fn duplicate_key(message: &str) -> Option<String> {
    let key = message.split("duplicate source-map key ").nth(1)?;
    let key = key.split_whitespace().next().unwrap_or_default();
    let role = key.rsplit_once('.').map_or(key, |(role, _digest)| role);
    Some(format!("the semantic key {role} is not injective"))
}

/// The descriptors of the base and of `placed`'s case ([`owner`]), or of the base alone.
fn sub_bundle(
    bundle: &DescriptorBundle,
    all: &[Placed<'_>],
    placed: Option<&Placed<'_>>,
) -> DescriptorBundle {
    sub_bundle_of(bundle, all, |owner| {
        placed.is_some_and(|placed| owner.case.id == placed.case.id)
    })
}

/// Whether the definition of the base and `cases` together lowers to exactly their sentences:
/// the base's, and each case's own as it emits them alone (its additions, in `judged`). Only then
/// is each case's definition part of theirs together.
fn lowers_as_alone(
    collected: &CollectedDefinition,
    all: &[Placed<'_>],
    cases: &[&Placed<'_>],
    base: Option<&[String]>,
    judged: &[Judged],
) -> bool {
    let Some(base) = base else {
        return false;
    };
    let ids = cases
        .iter()
        .map(|placed| placed.case.id.as_str())
        .collect::<BTreeSet<_>>();
    let mut expected = base.to_vec();
    for judged in judged
        .iter()
        .filter(|judged| ids.contains(judged.id.as_str()))
    {
        let Some(additions) = &judged.additions else {
            return false;
        };
        expected.extend(additions.iter().cloned());
    }
    let bundle = sub_bundle_of(&collected.bundle, all, |placed| {
        ids.contains(placed.case.id.as_str())
    });
    let Ok(Ok(emitted)) = catch_unwind(AssertUnwindSafe(|| collected.emit_k(bundle))) else {
        return false;
    };
    let mut together = emitted_sentences(&emitted);
    together.sort();
    expected.sort();
    together == expected
}

/// `base`'s place in [`Base::ALL`].
fn base_index(base: Base) -> usize {
    Base::ALL
        .iter()
        .position(|other| *other == base)
        .expect("every base is listed")
}

/// The definition K7's dependency check runs a set of cases on: a bundle of a collected
/// definition (the batch's, or a base's), or of a definition collected for the check.
enum Definition<'c> {
    Of(&'c CollectedDefinition, DescriptorBundle),
    Collected(Box<CollectedDefinition>, DescriptorBundle),
}

impl Definition<'_> {
    fn collected(&self) -> &CollectedDefinition {
        match self {
            Self::Of(collected, _) => collected,
            Self::Collected(collected, _) => collected,
        }
    }

    const fn bundle(&self) -> &DescriptorBundle {
        match self {
            Self::Of(_, bundle) | Self::Collected(_, bundle) => bundle,
        }
    }
}

/// Why K7's dependency check made no run of a case: the reason, which its deviation carries,
/// and the messages behind it, which only the TSV line does (a refusal's messages name the
/// sentences of the cases it was made beside).
#[derive(Clone, Debug, Eq, PartialEq)]
struct NotMade {
    reason: String,
    detail: String,
    /// Whether the definition without what the case states is refused (rather than a run of
    /// it not completing).
    refused: bool,
}

impl NotMade {
    fn refused(reason: &str, detail: String) -> Self {
        Self {
            reason: reason.to_owned(),
            detail,
            refused: true,
        }
    }

    const fn run(reason: String) -> Self {
        Self {
            reason,
            detail: String::new(),
            refused: false,
        }
    }
}

/// The refusal of `what` by `error`: its signature (codes and refusing stages), and its error
/// messages for the TSV.
fn refusal(what: &str, error: &CommandError) -> NotMade {
    NotMade::refused(
        &format!("{what} is refused: {}", native_signature(error)),
        observe_error(error)
            .into_iter()
            .filter(|diagnostic| diagnostic.severity == Severity::Error)
            .map(|diagnostic| diagnostic.message.replace(['\n', '\t'], " "))
            .collect::<Vec<_>>()
            .join(" | "),
    )
}

/// The runs K7's dependency check makes of `case`: its plan, and for an attribute case its
/// counter run too.
fn dependency_runs(case: &Case) -> Vec<&Run> {
    let K7::Run(plan) = &case.k7 else {
        return Vec::new();
    };
    let mut runs = vec![plan];
    if case.removal() == Removal::Attribute {
        runs.extend(&case.k7_counters);
    }
    runs
}

/// How a case's runs ended without what it states.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Outcome {
    /// A run ended otherwise: how.
    Depends(String),
    /// Every run ended as the plan states.
    Same,
    /// No run that ended otherwise, and one that was not made.
    NotMade(NotMade),
}

impl Outcome {
    /// The outcome of runs that ended `ended`: dependence where a run that completed ended
    /// otherwise, whatever the others did; otherwise not made where one was not made.
    fn of(ended: Result<Vec<Without>, NotMade>) -> Self {
        let ends = match ended {
            Ok(ends) => ends,
            Err(not_made) => return Self::NotMade(not_made),
        };
        let mut not_made = None;
        for (index, end) in ends.into_iter().enumerate() {
            let run = if index == 0 {
                String::new()
            } else {
                "the counter run: ".to_owned()
            };
            match end {
                Without::Differs(how) => return Self::Depends(format!("{run}{how}")),
                Without::NotMade(why) => {
                    not_made.get_or_insert_with(|| NotMade::run(format!("{run}{why}")));
                }
                Without::Same => {}
            }
        }
        not_made.map_or(Self::Same, Self::NotMade)
    }
}

/// K7's deviation of a case whose runs end as stated without its sentences too.
const INDEPENDENT: &str = "K7's dependency check: the runs end as stated without what the case states too, so they show nothing of it";

/// K7's dependency check's verdict on a case whose runs ended `outcome` without what it states,
/// where the generator states `removed`: the case's K7 deviation, if it deviates, and its TSV
/// line (`depends: ..`, `unchanged: ..`, `refused: ..`, `independent: ..`, `not made: ..`).
fn judge_dependency(removed: &Removed, outcome: Outcome) -> (Option<String>, String) {
    match (removed, outcome) {
        (_, Outcome::NotMade(not_made))
            if !(matches!(removed, Removed::Refused(_)) && not_made.refused) =>
        {
            let line = if not_made.detail.is_empty() {
                format!("not made: {}", not_made.reason)
            } else {
                format!("not made: {}: {}", not_made.reason, not_made.detail)
            };
            (
                Some(format!(
                    "K7's dependency check: not made: {}",
                    not_made.reason
                )),
                line,
            )
        }
        (Removed::Refused(why), Outcome::NotMade(not_made)) => (
            None,
            format!("refused, as stated ({why}): {}", not_made.reason),
        ),
        (Removed::Changes, Outcome::Depends(how)) => (None, format!("depends: {how}")),
        (Removed::Changes, Outcome::Same) => (
            Some(INDEPENDENT.to_owned()),
            format!("independent: {INDEPENDENT}"),
        ),
        (Removed::Unchanged(why), Outcome::Same) => (None, format!("unchanged, as stated: {why}")),
        (Removed::Unchanged(why), Outcome::Depends(how)) => {
            let deviation = format!(
                "K7's dependency check: a run ends otherwise without what the case states, where the case states none does ({why}): {how}"
            );
            (Some(deviation.clone()), format!("depends: {deviation}"))
        }
        (Removed::Refused(why), outcome) => {
            let deviation = format!(
                "K7's dependency check: the definition without what the case states is not refused, where the case states it is ({why})"
            );
            let how = match outcome {
                Outcome::Depends(how) => format!("depends: {how}"),
                _ => "unchanged".to_owned(),
            };
            (Some(deviation.clone()), format!("{how}; {deviation}"))
        }
        (_, Outcome::NotMade(_)) => unreachable!("judged above"),
    }
}

/// Whether `placed`'s command is a static clause's production (`#[k::desugar]`, `#[k::alias]`).
fn static_production(placed: &Placed<'_>) -> bool {
    placed
        .case
        .command()
        .is_some_and(|command| command.marker.is_some())
}

/// The definition `cases`' runs make without the cases' sentences ([`Removal::Sentences`]): the
/// descriptors of the base and of every case's command (its constructor, and what its
/// declaration in the base's command family declares), without any case's sentence. A static
/// clause's production is unmarked ([`unmarked`]), since with no clause nothing expands it, and
/// the case's rules are kept: they write the production in a rule, which the clause expands
/// (`DRIVE_RULE`), and are no clause.
fn without_sentences(
    bundle: &DescriptorBundle,
    all: &[Placed<'_>],
    cases: &[&Placed<'_>],
) -> DescriptorBundle {
    let ids = cases
        .iter()
        .map(|placed| placed.case.id.as_str())
        .collect::<BTreeSet<_>>();
    let descriptors = bundle
        .descriptors()
        .iter()
        .filter_map(|descriptor| {
            let Some(placed) = owner(descriptor, all) else {
                return Some(descriptor.clone());
            };
            if !ids.contains(placed.case.id.as_str()) {
                return None;
            }
            let commanded = placed
                .case
                .command()
                .is_some_and(|command| command.name == descriptor.id().item_name());
            let declared = case_range(descriptor.origin())
                .is_some_and(|range| placed.region(&range) == "command");
            if commanded || declared {
                Some(if static_production(placed) {
                    unmarked(descriptor)
                } else {
                    descriptor.clone()
                })
            } else if static_production(placed)
                && descriptor.id().item_kind() == krs_ir::ItemKind::Rule
            {
                Some(descriptor.clone())
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    let kept = descriptors
        .iter()
        .map(|descriptor| descriptor.id().clone())
        .collect::<BTreeSet<_>>();
    let declarations = bundle
        .declarations()
        .iter()
        .filter(|declaration| kept.contains(declaration.id()))
        .cloned()
        .collect();
    DescriptorBundle::with_declarations(descriptors, declarations)
        .and_then(|sub| sub.with_package_settings(bundle.package_settings().to_vec()))
        .expect("a subset of a valid bundle is valid")
}

/// `descriptor` without the marks of a static production (`#[k::alias]`, `#[k::desugar]`) on
/// any production it declares, and without their nodes' provenance.
fn unmarked(descriptor: &krs_ir::Descriptor) -> krs_ir::Descriptor {
    use krs_ir::bundle::DescriptorPayload;
    use krs_ir::transport::grammar::{ProductionAttribute, StageGrammarDescriptor};
    let DescriptorPayload::Grammar(grammar) = descriptor.payload() else {
        return descriptor.clone();
    };
    let mut grammar = grammar.clone();
    let mut keys = BTreeSet::new();
    let mut unmark = |production: &mut krs_ir::transport::grammar::DescriptorProduction| {
        production.attributes.retain(|attribute| match attribute {
            ProductionAttribute::Alias { key, recursive }
            | ProductionAttribute::Desugar { key, recursive } => {
                keys.insert(key.clone());
                keys.extend(recursive.clone());
                false
            }
            _ => true,
        });
    };
    match &mut *grammar {
        StageGrammarDescriptor::Production(production) => unmark(production),
        StageGrammarDescriptor::Tokens { productions } => productions.iter_mut().for_each(unmark),
        _ => {}
    }
    if keys.is_empty() {
        return descriptor.clone();
    }
    let provenance = descriptor
        .provenance()
        .without(&keys)
        .expect("a production keeps its own node");
    krs_ir::Descriptor::new(
        descriptor.id().clone(),
        descriptor.cfg().clone(),
        provenance,
        DescriptorPayload::Grammar(grammar),
    )
    .expect("a production without its static mark is a production")
}

/// The descriptors of the base and of the cases `keep` selects ([`owner`]).
fn sub_bundle_of(
    bundle: &DescriptorBundle,
    all: &[Placed<'_>],
    keep: impl Fn(&Placed<'_>) -> bool,
) -> DescriptorBundle {
    let descriptors = bundle
        .descriptors()
        .iter()
        .filter(|descriptor| owner(descriptor, all).is_none_or(&keep))
        .cloned()
        .collect::<Vec<_>>();
    let kept = descriptors
        .iter()
        .map(|descriptor| descriptor.id().clone())
        .collect::<BTreeSet<_>>();
    let declarations = bundle
        .declarations()
        .iter()
        .filter(|declaration| kept.contains(declaration.id()))
        .cloned()
        .collect();
    DescriptorBundle::with_declarations(descriptors, declarations)
        .and_then(|sub| sub.with_package_settings(bundle.package_settings().to_vec()))
        .expect("a subset of a valid bundle is valid")
}

/// The case of `all` a descriptor belongs to: the case whose text holds its authored range (its
/// item, or its command's declaration), or for a command's constructor descriptor, whose range is
/// its family's name in the base, the case of that command; `None` for the base's.
fn owner<'p, 'a>(descriptor: &krs_ir::Descriptor, all: &'p [Placed<'a>]) -> Option<&'p Placed<'a>> {
    let commanded = all.iter().find(|other| {
        other
            .case
            .command()
            .is_some_and(|command| command.name == descriptor.id().item_name())
    });
    commanded.or_else(|| {
        let range = case_range(descriptor.origin())?;
        all.iter().find(|other| other.owns(&range))
    })
}

fn judged(placed: &Placed<'_>, observed: Observed, all: &[Placed<'_>]) -> Judged {
    Judged {
        id: placed.case.id.clone(),
        observed,
        item: placed.item.clone(),
        spelling: placed.spelling.clone(),
        entry: placed.entry.clone(),
        command: placed.command.clone(),
        keys: None,
        batch: all.len(),
        neighbours: all
            .iter()
            .filter(|other| other.case.id != placed.case.id)
            .map(|other| other.case.id.clone())
            .collect(),
        additions: None,
        closure: None,
        native: None,
        ran: None,
        twin_ends: Vec::new(),
        interference: None,
        dependency: None,
    }
}

/// The cases of `cases` that K7 runs: those it has a plan for, when the run runs K7.
fn runnable<'p, 'a>(cases: &[&'p Placed<'a>], run: NativeRun<'_>) -> Vec<&'p Placed<'a>> {
    if run.run.is_none() {
        return Vec::new();
    }
    cases
        .iter()
        .filter(|placed| {
            matches!(placed.case.k7, K7::Run(_))
                || !krs_test_support::class_matrix::twin_runs(placed.case).is_empty()
        })
        .copied()
        .collect()
}

fn refused(diagnostics: Vec<ObservedDiagnostic>) -> Observed {
    Observed {
        accepted: false,
        diagnostics,
        panic: None,
    }
}

/// Every diagnostic a failure reports, as `krs --message-format json` prints them: its envelopes,
/// located ones first, and the warnings of the stages that completed. A failure that reports none
/// (a crashed collector) is one uncoded, unlocated error with its message.
pub fn observe_error(error: &CommandError) -> Vec<ObservedDiagnostic> {
    let envelopes = error.diagnostics().unwrap_or_default();
    let mut observed = observe_reports(&envelopes);
    if let Some(warnings) = error.warnings() {
        observed.extend(observe_reports(&warnings.envelopes));
    }
    if !observed
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        observed.push(ObservedDiagnostic {
            severity: Severity::Error,
            code: None,
            kind: None,
            range: None,
            labels: Vec::new(),
            message: error.to_string(),
            help: Vec::new(),
        });
    }
    observed
}

fn observe_reports(envelopes: &[DiagnosticEnvelope]) -> Vec<ObservedDiagnostic> {
    let severity = |severity: DiagnosticSeverity| match severity {
        DiagnosticSeverity::Error => Severity::Error,
        DiagnosticSeverity::Warning => Severity::Warning,
    };
    let in_case = |range: &krs_ir::SourceRange| {
        if is_case_source(&range.file) {
            range.start_byte as usize..range.end_byte as usize
        } else {
            // Located, but in another file: outside every case.
            usize::MAX..usize::MAX
        }
    };
    let (located, unlocated): (Vec<_>, Vec<_>) = envelopes
        .iter()
        .partition(|envelope| envelope.authored_range.is_some());
    located
        .into_iter()
        .chain(unlocated)
        .map(|envelope| ObservedDiagnostic {
            severity: severity(envelope.severity),
            code: Some(envelope.code.clone()),
            kind: Some(envelope.kind),
            range: envelope.authored_range.as_ref().map(in_case),
            labels: envelope
                .labels
                .iter()
                .map(|label| in_case(&label.range))
                .collect(),
            message: envelope.message.clone(),
            help: envelope.help.clone(),
        })
        .collect()
}

pub fn write_package(directory: &Path, name: &str, source: &str) -> PathBuf {
    let facade = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .expect("the facade crate exists");
    fs::create_dir_all(directory.join("src")).expect("the package directory is created");
    fs::write(directory.join(SOURCE_FILE), source).expect("the source is written");
    let manifest = directory.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n\
             [dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n\
             [package.metadata.krs]\nk-namespace = \"{NAMESPACE}\"\n\n\
             [package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            serde_json::to_string(facade.to_str().expect("the facade path is UTF-8"))
                .expect("a path serializes"),
        ),
    )
    .expect("the manifest is written");
    manifest
}

/// Writes the K text of the cases of a collected batch that KRS accepted under `directory`, for
/// a reference frontend to read (`scripts/krs-class-reference-frontend.sh`): their definition
/// together, `<hash>/definition.k`, and each case's own, `<hash>/cases/<hash>/definition.k`
/// beside its `id`. Nothing the class matrix judges reads it.
///
/// An emission that fails or panics leaves cases without K text, which no frontend then judges:
/// each is recorded under `dropped/` (`<hash>.txt`: the reason on its first line, then the case
/// IDs, one per line), the batch's when its joint emission fails, a case's when its own does, so
/// that the frontend's run counts them and fails rather than reading their absence as a verdict.
fn write_k_text(
    directory: &Path,
    collected: &CollectedDefinition,
    all: &[Placed<'_>],
    judged: &[Judged],
) {
    let accepted = judged
        .iter()
        .filter(|judged| !judged.observed.refused())
        .map(|judged| judged.id.as_str())
        .collect::<BTreeSet<_>>();
    if accepted.is_empty() {
        return;
    }
    let emit = |bundle| match catch_unwind(AssertUnwindSafe(|| collected.emit_k(bundle))) {
        Ok(Ok(emitted)) => Ok(emitted.definition),
        Ok(Err(error)) => Err(format!("the emission failed: {error}")),
        Err(panic) => Err(format!("the emission panicked: {}", panic_message(&*panic))),
    };
    let dropped = |reason: &str, ids: &[&str]| {
        let mut record = reason.replace('\n', " ");
        for id in ids {
            record.push('\n');
            record.push_str(id);
        }
        record.push('\n');
        let dropped = directory.join("dropped");
        let path = dropped.join(format!("{:016x}.txt", fnv1a64(&record)));
        let written = fs::create_dir_all(&dropped).and_then(|()| fs::write(&path, &record));
        if let Err(error) = written {
            panic!(
                "the dropped record is written at {}: {error}",
                path.display()
            );
        }
    };
    let together = sub_bundle_of(&collected.bundle, all, |placed| {
        accepted.contains(placed.case.id.as_str())
    });
    let definition = match emit(together) {
        Ok(definition) => definition,
        Err(reason) => {
            dropped(
                &format!("batch: {reason}"),
                &accepted.iter().copied().collect::<Vec<_>>(),
            );
            return;
        }
    };
    let batch = directory.join(format!("{:016x}", fnv1a64(&definition)));
    let written = fs::create_dir_all(batch.join("cases"))
        .and_then(|()| fs::write(batch.join("definition.k"), &definition));
    if let Err(error) = written {
        panic!("the K text is written under {}: {error}", batch.display());
    }
    for placed in all
        .iter()
        .filter(|placed| accepted.contains(placed.case.id.as_str()))
    {
        let definition = match emit(sub_bundle(&collected.bundle, all, Some(placed))) {
            Ok(definition) => definition,
            Err(reason) => {
                dropped(&format!("case: {reason}"), &[placed.case.id.as_str()]);
                continue;
            }
        };
        let case = batch
            .join("cases")
            .join(format!("{:016x}", fnv1a64(&placed.case.id)));
        let written = fs::create_dir_all(&case)
            .and_then(|()| fs::write(case.join("definition.k"), &definition))
            .and_then(|()| fs::write(case.join("id"), &placed.case.id));
        if let Err(error) = written {
            panic!("the K text is written under {}: {error}", case.display());
        }
    }
}

/// The 64-bit FNV-1a hash, which names a batch package after its source.
fn fnv1a64(text: &str) -> u64 {
    text.bytes().fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
        (hash ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3)
    })
}

/// The sentences of an emission: `definition.k`'s, and `spec.k`'s when there is one.
fn emitted_sentences(emitted: &EmittedDefinition) -> Vec<String> {
    let mut all = sentences(&emitted.definition);
    if let Some(spec) = &emitted.spec {
        all.extend(sentences(spec));
    }
    all
}

/// The sentences the base of a collected batch emits alone; `None` when it does not emit.
fn base_sentences(collected: &CollectedDefinition, all: &[Placed<'_>]) -> Option<Vec<String>> {
    let bundle = sub_bundle(&collected.bundle, all, None);
    collected
        .emit_k(bundle)
        .ok()
        .map(|emitted| emitted_sentences(&emitted))
}

/// The cases `printed`, the source `krs expand` printed for them, holds, placed where their
/// items are: each top-level item that names the case's tag (a printed form can be several items,
/// a function and its equation), the first with the case's command variant; a case that it holds
/// no item for, at its command variant alone. The IDs of the cases it holds neither for are the
/// error.
fn locate<'a>(printed: &str, cases: &[&'a Case]) -> Result<Vec<Placed<'a>>, Vec<String>> {
    use syn::spanned::Spanned as _;
    let Ok(file) = syn::parse_file(printed) else {
        return Err(cases.iter().map(|case| case.id.clone()).collect());
    };
    let mut items = Vec::new();
    let mut variants = BTreeMap::new();
    for item in &file.items {
        if let syn::Item::Enum(family) = item {
            for pair in family.variants.pairs() {
                // The variant with its comma, so that cutting it leaves a list.
                let mut range = pair.value().span().byte_range();
                if let Some(comma) = pair.punct() {
                    range.end = comma.span.byte_range().end;
                }
                variants.insert(pair.value().ident.to_string(), range);
            }
        } else {
            items.push(item.span().byte_range());
        }
    }
    let mut placed = Vec::new();
    let mut missing = Vec::new();
    for case in cases {
        let tag = case.tag();
        let upper = tag.to_uppercase();
        let mut command = case
            .command()
            .and_then(|command| variants.get(&command.name).cloned());
        let before = placed.len();
        for item in items.iter().filter(|range| {
            let text = &printed[(*range).clone()];
            text.contains(&tag) || text.contains(&upper)
        }) {
            // The printed item is all that is known of the case; an error in it is `@ item`.
            placed.push(Placed {
                case,
                item: item.clone(),
                spelling: item.start..item.start,
                entry: item.start..item.start,
                command: command.take(),
            });
        }
        if placed.len() == before {
            // A case whose sentence is configured out (`#[cfg(any())]`) denotes none, and its
            // printed form is its absence: what it adds is its command alone, so it is placed
            // there and judged by the sentences it emits, which its command's syntax is.
            match command.take() {
                Some(command) => placed.push(Placed {
                    case,
                    item: command.start..command.start,
                    spelling: command.start..command.start,
                    entry: command.start..command.start,
                    command: Some(command),
                }),
                None => missing.push(case.id.clone()),
            }
        }
    }
    if missing.is_empty() {
        Ok(placed)
    } else {
        Err(missing)
    }
}

/// `text` without `ranges`, which do not overlap.
fn without(text: &str, mut ranges: Vec<Range<usize>>) -> String {
    ranges.sort_by_key(|range| std::cmp::Reverse(range.start));
    let mut text = text.to_owned();
    for range in ranges {
        text.replace_range(range, "");
    }
    text
}

impl Worker<'_> {
    /// K3 over a collected batch: its accepted cases that are no initializer, printed together.
    fn check_closure(&self, all: &[Placed<'_>], judged: &mut [Judged]) {
        let original = judged
            .iter()
            .filter_map(|judged| {
                let additions = judged.additions.clone()?;
                (!judged.observed.refused()).then(|| (judged.id.clone(), additions))
            })
            .collect::<BTreeMap<_, _>>();
        let cases = all
            .iter()
            .map(|placed| placed.case)
            .filter(|case| original.contains_key(&case.id) && !case.replaces_initializer())
            .collect::<Vec<_>>();
        let mut verdicts = BTreeMap::new();
        self.closure(cases, &original, &mut verdicts);
        for judged in judged {
            judged.closure = verdicts.remove(&judged.id);
        }
    }

    /// Print `cases` together with `krs expand`, and judge the printed source; a refusal of the
    /// expansion is bisected down to a case alone.
    fn closure(
        &self,
        cases: Vec<&Case>,
        original: &BTreeMap<String, Vec<String>>,
        out: &mut BTreeMap<String, Closure>,
    ) {
        if cases.is_empty() {
            return;
        }
        let rendered = render(&cases);
        let (collected, directory) = self.collect_kept(&rendered.source);
        // A panic of `krs expand` is the printer's, which K3 judges: it is bisected down to the
        // case that makes it, as a refusal is.
        let printed = collected.map(|collected| {
            catch_unwind(AssertUnwindSafe(|| {
                collected.expand(collected.bundle.clone())
            }))
        });
        let _ = fs::remove_dir_all(&directory);
        let error = match printed {
            Ok(Ok(Ok(text))) => return self.printed(&text, cases, original, out),
            Ok(Ok(Err(error))) => ("krs expand".to_owned(), Some(error)),
            Ok(Err(panic)) => (
                format!("krs expand panicked: {}", panic_message(&*panic)),
                None,
            ),
            Err(error) => (
                "the accepted cases do not collect again".to_owned(),
                Some(error),
            ),
        };
        if let [placed] = rendered.cases.as_slice() {
            let verdict = error.1.map_or_else(
                || error.0.clone(),
                |refusal| {
                    let observed = refused(observe_error(&refusal));
                    format!("{}: {}", error.0, signature(&observed, placed))
                },
            );
            out.insert(placed.case.id.clone(), Closure::Refused(verdict));
        } else {
            let (left, right) = cases.split_at(cases.len() / 2);
            self.closure(left.to_vec(), original, out);
            self.closure(right.to_vec(), original, out);
            // A failure of the whole that neither half makes is no case's alone: each case of the
            // batch is red with it, rather than the failure going unrecorded.
            let attributed = cases
                .iter()
                .any(|case| matches!(out.get(&case.id), Some(Closure::Refused(_))));
            if !attributed {
                let codes = error.1.as_ref().map_or_else(String::new, |refusal| {
                    let codes = refused(observe_error(refusal))
                        .errors()
                        .map(|error| error.code.clone().unwrap_or_else(|| "uncoded".to_owned()))
                        .collect::<Vec<_>>();
                    format!(" ({})", codes.join(", "))
                });
                for case in &cases {
                    out.insert(
                        case.id.clone(),
                        Closure::Refused(format!(
                            "{}{codes} only with the other cases of its batch",
                            error.0
                        )),
                    );
                }
            }
        }
    }

    /// Collect `printed`, the source printed for `cases`, attributing its errors to the cases it
    /// prints as the batches do, and compare each case's sentences with its original ones.
    fn printed(
        &self,
        printed: &str,
        cases: Vec<&Case>,
        original: &BTreeMap<String, Vec<String>>,
        out: &mut BTreeMap<String, Closure>,
    ) {
        let mut text = printed.to_owned();
        let mut remaining = cases;
        while !remaining.is_empty() {
            let located = match locate(&text, &remaining) {
                Ok(located) => located,
                Err(missing) => {
                    for id in &missing {
                        let verdict = "no item of the printed source names the case".to_owned();
                        out.insert(id.clone(), Closure::Refused(verdict));
                    }
                    remaining.retain(|case| !missing.contains(&case.id));
                    continue;
                }
            };
            let error = match self.collect(&text) {
                Ok(collected) => {
                    let base = base_sentences(&collected, &located);
                    let mut seen = BTreeSet::new();
                    for placed in located.iter().filter(|placed| seen.insert(&placed.case.id)) {
                        let bundle = sub_bundle(&collected.bundle, &located, Some(placed));
                        let emitted = catch_unwind(AssertUnwindSafe(|| collected.emit_k(bundle)));
                        let verdict = match (emitted, &base) {
                            (Ok(Ok(emitted)), Some(base)) => compare(
                                &original[&placed.case.id],
                                &additions(&emitted_sentences(&emitted), base),
                            ),
                            (Ok(Ok(_)), None) => {
                                Closure::Refused("the printed base does not emit".to_owned())
                            }
                            (Ok(Err(error)), _) => {
                                Closure::Refused(signature(&refused(observe_error(&error)), placed))
                            }
                            (Err(panic), _) => {
                                Closure::Refused(format!("panic: {}", panic_message(&*panic)))
                            }
                        };
                        out.insert(placed.case.id.clone(), verdict);
                    }
                    return;
                }
                Err(error) => error,
            };
            let diagnostics = observe_error(&error);
            let mut by_case = BTreeMap::<usize, Vec<ObservedDiagnostic>>::new();
            let mut stray = false;
            for diagnostic in diagnostics {
                let holder = diagnostic
                    .range
                    .as_ref()
                    .and_then(|range| located.iter().position(|placed| placed.owns(range)));
                match holder {
                    Some(index) => by_case.entry(index).or_default().push(diagnostic),
                    None => stray |= diagnostic.severity == Severity::Error,
                }
            }
            if stray || by_case.is_empty() {
                if let [case] = remaining.as_slice()
                    && let Some(placed) = located.iter().find(|placed| placed.case.id == case.id)
                {
                    let observed = refused(observe_error(&error));
                    out.insert(
                        placed.case.id.clone(),
                        Closure::Refused(signature(&observed, placed)),
                    );
                } else {
                    let (left, right) = remaining.split_at(remaining.len() / 2);
                    self.closure(left.to_vec(), original, out);
                    self.closure(right.to_vec(), original, out);
                }
                return;
            }
            let mut cut = Vec::new();
            let mut by_id = BTreeMap::<&str, (usize, Vec<ObservedDiagnostic>)>::new();
            for (index, diagnostics) in by_case {
                let entry = by_id
                    .entry(located[index].case.id.as_str())
                    .or_insert((index, Vec::new()));
                entry.1.extend(diagnostics);
            }
            for (id, (index, diagnostics)) in by_id {
                let observed = refused(diagnostics);
                out.insert(
                    id.to_owned(),
                    Closure::Refused(signature(&observed, &located[index])),
                );
                for placed in located.iter().filter(|placed| placed.case.id == id) {
                    cut.push(placed.item.clone());
                    cut.extend(placed.command.clone());
                }
                remaining.retain(|case| case.id != id);
            }
            text = without(&text, cut);
        }
    }
}

#[cfg(test)]
mod tests {
    use krs_test_support::class_matrix::k7::Status;

    use krs_test_support::class_matrix::k7::Removed;

    use super::{
        Culprits, INDEPENDENT, NotMade, Outcome, Ran, Without, adopted, bisect, interference,
        judge_dependency,
    };

    /// A case's runs depend on what it states only where a run that completed ended otherwise:
    /// one such run decides, whatever the others did; a run that did not complete shows nothing,
    /// so where none ended otherwise the check is not made; runs that all end as stated are the
    /// same.
    #[test]
    fn dependence_is_shown_only_by_a_completed_run_that_ends_otherwise() {
        let differs = Without::Differs("not applied: 0 of 1 steps".to_owned());
        let not_made = Without::NotMade("time limit: no end within 60 s".to_owned());
        assert_eq!(
            Outcome::of(Ok(vec![Without::Same, differs.clone()])),
            Outcome::Depends("the counter run: not applied: 0 of 1 steps".to_owned())
        );
        assert_eq!(
            Outcome::of(Ok(vec![not_made.clone(), differs])),
            Outcome::Depends("the counter run: not applied: 0 of 1 steps".to_owned())
        );
        assert_eq!(
            Outcome::of(Ok(vec![Without::Same, not_made])),
            Outcome::NotMade(NotMade::run(
                "the counter run: time limit: no end within 60 s".to_owned()
            ))
        );
        assert_eq!(Outcome::of(Ok(vec![Without::Same])), Outcome::Same);
        let refused = NotMade::refused("the definition is refused: krs::x", "a | b".to_owned());
        assert_eq!(Outcome::of(Err(refused.clone())), Outcome::NotMade(refused));
    }

    /// Every outcome against every statement: dependence where a change is stated, a run that
    /// ends as stated where none is (each checked), a refusal where one is; anything else
    /// deviates, a check not made included, and the deviation carries no refusal's messages,
    /// which only the TSV line does.
    #[test]
    fn the_dependency_check_judges_each_outcome_against_what_the_case_states() {
        let depends = || Outcome::Depends("another value: k = k[]".to_owned());
        let refused = || {
            Outcome::NotMade(NotMade::refused(
                "the definition without what the case states is refused: krs::x",
                "message naming another case".to_owned(),
            ))
        };
        let timed_out = || Outcome::NotMade(NotMade::run("time limit".to_owned()));
        let unchanged = Removed::Unchanged("by design");
        let stated_refused = Removed::Refused("no definition");
        assert_eq!(
            judge_dependency(&Removed::Changes, depends()),
            (None, "depends: another value: k = k[]".to_owned())
        );
        assert_eq!(
            judge_dependency(&Removed::Changes, Outcome::Same)
                .0
                .as_deref(),
            Some(INDEPENDENT)
        );
        assert_eq!(
            judge_dependency(&unchanged, Outcome::Same),
            (None, "unchanged, as stated: by design".to_owned())
        );
        assert!(judge_dependency(&unchanged, depends()).0.is_some());
        assert!(judge_dependency(&stated_refused, refused()).0.is_none());
        assert!(judge_dependency(&stated_refused, Outcome::Same).0.is_some());
        assert!(judge_dependency(&stated_refused, depends()).0.is_some());
        assert!(judge_dependency(&stated_refused, timed_out()).0.is_some());
        for removed in [Removed::Changes, unchanged] {
            for outcome in [refused(), timed_out()] {
                let (deviation, line) = judge_dependency(&removed, outcome);
                let deviation = deviation.expect("a check not made deviates");
                assert!(
                    deviation.starts_with("K7's dependency check: not made: "),
                    "{deviation}"
                );
                assert!(!deviation.contains("message naming"), "{deviation}");
                assert!(line.starts_with("not made: "), "{line}");
            }
        }
        assert!(
            judge_dependency(&Removed::Changes, refused())
                .1
                .ends_with(": message naming another case")
        );
    }

    /// A batched K7 verdict stands only where the case's run alone is the same; where the run
    /// alone differs in any way, conforming or deviating otherwise, the case is judged by it.
    #[test]
    fn a_batched_verdict_stands_only_where_the_run_alone_is_the_same() {
        let batched = Ran::Deviates("no defined result: probe(..)".to_owned());
        let conforms = Ran::Conforms(Status::Value);
        let own = Ran::Deviates("not applied: 1 of 3 steps".to_owned());
        assert_eq!(adopted(&batched, Some(conforms.clone())), Some(conforms));
        assert_eq!(adopted(&batched, Some(own.clone())), Some(own));
        assert_eq!(adopted(&batched, Some(batched.clone())), None);
        assert_eq!(adopted(&batched, None), None);
    }

    /// The bisection names the one neighbour that changes the verdict; a pair across the halves,
    /// the whole set where it still differs run again; and no neighbour where it does not, which
    /// is a failure of its own.
    #[test]
    fn the_bisection_names_only_neighbours_it_reproduced_the_difference_beside() {
        let neighbours = [1, 2, 3, 4, 5, 6, 7, 8];
        let mut runs = Vec::new();
        let one = bisect(&neighbours, |set| {
            runs.push(set.to_vec());
            set.contains(&6)
        });
        assert_eq!(one, Culprits::Narrowed(vec![6]));
        // Each step ran a half beside the case, never the whole set again.
        assert!(runs.iter().all(|set| set.len() < neighbours.len()));

        // 2 and 7 only together: no half of the whole set holds both, so it is run once more.
        let mut whole_runs = 0;
        let pair = bisect(&neighbours, |set| {
            whole_runs += usize::from(set.len() == neighbours.len());
            set.contains(&2) && set.contains(&7)
        });
        assert_eq!(pair, Culprits::Whole(neighbours.to_vec()));
        assert_eq!(whole_runs, 1);
        // 5 and 7 together: the right half holds both, and no half of it does.
        assert_eq!(
            bisect(&neighbours, |set| set.contains(&5) && set.contains(&7)),
            Culprits::Narrowed(vec![5, 6, 7, 8])
        );
        // A batched deviation that no set reproduces, the whole one run again included (a
        // timeout under load), names no neighbour.
        assert_eq!(bisect(&neighbours, |_| false), Culprits::NotReproduced);
        // One neighbour: the set is the whole one, run again before it is named.
        assert_eq!(bisect(&[3], |_| true), Culprits::Whole(vec![3]));
        assert_eq!(bisect(&[3], |_| false), Culprits::NotReproduced);

        let batched = Ran::Deviates("no defined result".to_owned());
        let alone = Ran::Deviates("not applied: 1 of 3 steps".to_owned());
        let named = |set: &[i32]| format!("{set:?}");
        let (batched, alone) = (batched.signature(), alone.signature());
        let interfered = interference(
            "K7",
            &Culprits::Narrowed(vec![6]),
            8,
            &batched,
            &alone,
            named,
        );
        assert_eq!(
            interfered,
            "batch interference: K7 deviates beside 8 other cases (no defined result), and alone \
             it is not applied: 1 of 3 steps; it still differs beside [6]"
        );
        let k2 = interference(
            "K2",
            &Culprits::Whole(vec![4]),
            1,
            "krs::rust-expansion::uncoded-error @ spelling",
            "conforms",
            named,
        );
        assert_eq!(
            k2,
            "batch interference: K2 deviates beside 1 other cases (krs::rust-expansion::uncoded-error \
             @ spelling), and alone it is conforms; it still differs beside [4]"
        );
        let flaky = interference("K7", &Culprits::NotReproduced, 8, &batched, &alone, named);
        assert!(
            flaky.starts_with("K7's batched verdict did not reproduce (flaky?)")
                && !flaky.contains("batch interference"),
            "{flaky}"
        );
    }
}

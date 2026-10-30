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
use krs_ir::DescriptorBundle;
use krs_test_support::class_matrix::invariants::{
    Observed, ObservedDiagnostic, Severity, signature,
};
use krs_test_support::class_matrix::{Base, Case, Packaging, Placed, render};

use crate::closure::{Closure, additions, compare, sentences};

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
    /// The K sentences the case adds to its base, once accepted.
    pub additions: Option<Vec<String>>,
    /// K3's verdict, for an accepted case that is no initializer, when the run checks closure.
    pub closure: Option<Closure>,
    /// K6's verdict, for an accepted case the table does not refuse, when the run judges it.
    pub native: Option<Native>,
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
}

/// Judge every case of `cases` through the pipeline, in ID order.
///
/// # Panics
///
/// Panics if a worker panics outside the lowering of a case, which the harness does not expect.
#[must_use]
pub fn judge_all(cases: &[&Case], settings: &Settings) -> Vec<Judged> {
    let jobs = Mutex::new(batches(cases, settings.batch));
    let judged = Mutex::new(Vec::with_capacity(cases.len()));
    let builds = AtomicUsize::new(0);
    let cost = NativeCost::default();
    std::thread::scope(|scope| {
        for index in 0..settings.workers.max(1) {
            let worker = Worker {
                root: settings.scratch.join(format!("worker-{index}")),
                builds: &builds,
                closure: settings.closure,
                native: (settings.native != NativeMode::Off).then_some(NativeRun {
                    refused_by_table: &settings.refused_by_table,
                    cost: &cost,
                    alone: settings.native == NativeMode::Alone,
                }),
            };
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
    eprintln!(
        "[krs-class] {} cases judged in {} package builds",
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
            "[krs-class] K6 judged {cases} cases ({:?}) in {checks} checks, {} of them in batches that lower otherwise together; {:.1} s of worker time, {:.2} s a check",
            settings.native,
            cost.apart.load(Ordering::Relaxed),
            time.as_secs_f64(),
            each.as_secs_f64(),
        );
    }
    judged
}

/// What K6 cost a run: the checks it made, the workers' time they took, and the cases judged
/// alone because their batch lowers otherwise together.
#[derive(Default)]
struct NativeCost {
    checks: AtomicUsize,
    nanos: AtomicU64,
    apart: AtomicUsize,
}

/// A worker's part in K6.
#[derive(Clone, Copy)]
struct NativeRun<'a> {
    /// The cases the table refuses, which K6 leaves aside.
    refused_by_table: &'a BTreeSet<String>,
    cost: &'a NativeCost,
    /// Whether each case is judged alone, never in a batch.
    alone: bool,
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
    };
    fs::create_dir_all(&worker.root).expect("the directory is created");
    worker.collect(source)
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
}

impl Worker<'_> {
    fn target(&self) -> PathBuf {
        self.root.join("target")
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
                        out.push(judged(&rendered.cases[0], refused(diagnostics), 1));
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
                            out.push(judged(placed, refused(diagnostics.clone()), count));
                            placed.case.id.clone()
                        })
                        .collect::<BTreeSet<_>>();
                    remaining.retain(|case| !refused_ids.contains(&case.id));
                }
            }
        }
    }

    /// K6 over a collected batch: the definition of each case that KRS accepted and the table does
    /// not refuse, the base's descriptors and the case's, judged as `krs check` judges it. The
    /// cases are judged together when their definition together is exactly theirs
    /// ([`lowers_as_alone`]), and each alone otherwise.
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
        let mut verdicts = BTreeMap::new();
        if run.alone || cases.len() < 2 || !lowers_as_alone(collected, all, &cases, base, judged) {
            if cases.len() > 1 && !run.alone {
                run.cost.apart.fetch_add(cases.len(), Ordering::Relaxed);
            }
            for placed in cases {
                self.native_bisect(collected, all, &[placed], &mut verdicts);
            }
        } else {
            self.native_bisect(collected, all, &cases, &mut verdicts);
        }
        for judged in judged {
            judged.native = verdicts.remove(&judged.id);
        }
    }

    /// Judge the definition of the base and `cases` together; on a refusal, each half, down to a
    /// case alone, whose verdict is its own definition's. An accepted definition that holds a
    /// case's definition stands for it: a refusal of `krs check` is of a sentence the definition
    /// has, or of a feature one of its sentences needs, never of a sentence it lacks, so adding
    /// the other cases' sentences cannot hide one. `KRS_CLASS_NATIVE=alone` judges each case
    /// alone, which must give the same verdicts.
    fn native_bisect(
        &self,
        collected: &CollectedDefinition,
        all: &[Placed<'_>],
        cases: &[&Placed<'_>],
        out: &mut BTreeMap<String, Native>,
    ) {
        let Some(run) = self.native else {
            return;
        };
        let ids = cases
            .iter()
            .map(|placed| placed.case.id.as_str())
            .collect::<BTreeSet<_>>();
        let bundle = sub_bundle_of(&collected.bundle, all, |placed| {
            ids.contains(placed.case.id.as_str())
        });
        let started = Instant::now();
        let checked = catch_unwind(AssertUnwindSafe(|| collected.check(bundle)));
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
                    out.insert(placed.case.id.clone(), Native::Accepted);
                }
            }
            (refused, [placed]) => {
                out.insert(placed.case.id.clone(), refused);
            }
            (_, _) => {
                let (left, right) = cases.split_at(cases.len() / 2);
                self.native_bisect(collected, all, left, out);
                self.native_bisect(collected, all, right, out);
            }
        }
    }

    /// The sentences `base` emits alone, with its own initializer; collected once per run, by the
    /// first worker that needs them.
    fn preamble_sentences(&self, base: Base) -> Option<Vec<String>> {
        static PREAMBLES: [OnceLock<Option<Vec<String>>>; Base::ALL.len()] =
            [const { OnceLock::new() }; Base::ALL.len()];
        let index = Base::ALL
            .iter()
            .position(|other| *other == base)
            .expect("every base is listed");
        PREAMBLES[index]
            .get_or_init(|| {
                let collected = self.collect(&base.preamble()).ok()?;
                let emitted = collected.emit_k(collected.bundle.clone()).ok()?;
                Some(emitted_sentences(&emitted))
            })
            .clone()
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
    let batch = all.len();
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
            let mut judged = judged(placed, observed, batch);
            judged.additions = base.map(|base| additions(&emitted_sentences(&emitted), base));
            judged
        }
        Ok(Err(error)) => judged(placed, refused(observe_error(&error)), batch),
        Err(panic) => {
            let message = panic_message(&*panic);
            let observed = Observed {
                accepted: false,
                diagnostics: Vec::new(),
                panic: Some(message),
            };
            judged(placed, observed, batch)
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

fn judged(placed: &Placed<'_>, observed: Observed, batch: usize) -> Judged {
    Judged {
        id: placed.case.id.clone(),
        observed,
        item: placed.item.clone(),
        spelling: placed.spelling.clone(),
        entry: placed.entry.clone(),
        command: placed.command.clone(),
        keys: None,
        batch,
        additions: None,
        closure: None,
        native: None,
    }
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
/// a function and its equation), the first with the case's command variant. The IDs of the cases
/// it holds no item for are the error.
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
            missing.push(case.id.clone());
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
                            (Err(_), _) => Closure::Refused("panic".to_owned()),
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

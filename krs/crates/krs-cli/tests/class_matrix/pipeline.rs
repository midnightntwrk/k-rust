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
//! Workers run batches concurrently, each with one Cargo target directory reused across its
//! batches; every batch package is written fresh, under a name derived from its content, so no
//! build of an earlier batch can stand in for it.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::ops::Range;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use krs_cli::{
    CollectedDefinition, Command, CommandError, CommandRequest, DiagnosticEnvelope,
    DiagnosticSeverity, EmittedDefinition, FacetSelector, MessageFormat, PackageSelector,
    RegistrationMode, collect_descriptors,
};
use krs_ir::DescriptorBundle;
use krs_test_support::class_matrix::invariants::{
    Observed, ObservedDiagnostic, Severity, signature,
};
use krs_test_support::class_matrix::{Case, Packaging, Placed, render};

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
    std::thread::scope(|scope| {
        for index in 0..settings.workers.max(1) {
            let worker = Worker {
                root: settings.scratch.join(format!("worker-{index}")),
                builds: &builds,
                closure: settings.closure,
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
    judged
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
            Packaging::Own(_) => jobs.push(vec![*case]),
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
                    let base = base_sentences(&collected, &rendered.cases);
                    let mut judged = rendered
                        .cases
                        .iter()
                        .map(|placed| {
                            back_half(&collected, &rendered.cases, placed, base.as_deref())
                        })
                        .collect::<Vec<_>>();
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
                diagnostics: observe_reports(
                    &emitted.warnings.envelopes,
                    &emitted.warnings.unlocated,
                ),
                panic: None,
            };
            let mut judged = judged(placed, observed, batch);
            judged.additions = base.map(|base| additions(&emitted_sentences(&emitted), base));
            judged
        }
        Ok(Err(error)) => judged(placed, refused(observe_error(&error)), batch),
        Err(panic) => {
            let message = panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| panic.downcast_ref::<&str>().map(|text| (*text).to_owned()))
                .unwrap_or_else(|| "a panic without a message".to_owned());
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
    let descriptors = bundle
        .descriptors()
        .iter()
        .filter(|descriptor| {
            owner(descriptor, all)
                .is_none_or(|owner| placed.is_some_and(|placed| owner.case.id == placed.case.id))
        })
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
    }
}

fn refused(diagnostics: Vec<ObservedDiagnostic>) -> Observed {
    Observed {
        accepted: false,
        diagnostics,
        panic: None,
    }
}

/// Every diagnostic a failure reports, as `krs --message-format json` prints them: its located
/// envelopes, its unlocated diagnostics, and the warnings of the stages that completed. A failure
/// that reports none (a process failure) is one uncoded, unlocated error with its message.
pub fn observe_error(error: &CommandError) -> Vec<ObservedDiagnostic> {
    let envelopes = error.diagnostics().unwrap_or_default();
    let mut observed = observe_reports(&envelopes, &error.unlocated_diagnostics());
    if let Some(warnings) = error.warnings() {
        observed.extend(observe_reports(&warnings.envelopes, &warnings.unlocated));
    }
    if !observed
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        observed.push(ObservedDiagnostic {
            severity: Severity::Error,
            code: None,
            range: None,
            message: error.to_string(),
        });
    }
    observed
}

fn observe_reports(
    envelopes: &[DiagnosticEnvelope],
    unlocated: &[krs_cli::UnlocatedDiagnostic],
) -> Vec<ObservedDiagnostic> {
    let severity = |severity: DiagnosticSeverity| match severity {
        DiagnosticSeverity::Error => Severity::Error,
        DiagnosticSeverity::Warning => Severity::Warning,
    };
    let located = envelopes.iter().map(|envelope| {
        let range = &envelope.authored_range;
        ObservedDiagnostic {
            severity: severity(envelope.severity),
            code: Some(envelope.code.clone()),
            range: Some(if is_case_source(&range.file) {
                range.start_byte as usize..range.end_byte as usize
            } else {
                // Located, but in another file: outside every case.
                usize::MAX..usize::MAX
            }),
            message: envelope.message.clone(),
        }
    });
    let prose = unlocated.iter().map(|diagnostic| ObservedDiagnostic {
        severity: severity(diagnostic.severity),
        code: Some(diagnostic.code.clone()),
        range: None,
        message: diagnostic.message.clone(),
    });
    located.chain(prose).collect()
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
        let printed = collected.map(|collected| collected.expand(collected.bundle.clone()));
        let _ = fs::remove_dir_all(&directory);
        let error = match printed {
            Ok(Ok(text)) => return self.printed(&text, cases, original, out),
            Ok(Err(error)) => ("krs expand", error),
            Err(error) => ("the accepted cases do not collect again", error),
        };
        if let [placed] = rendered.cases.as_slice() {
            let observed = refused(observe_error(&error.1));
            let verdict = format!("{}: {}", error.0, signature(&observed, placed));
            out.insert(placed.case.id.clone(), Closure::Refused(verdict));
        } else {
            let (left, right) = cases.split_at(cases.len() / 2);
            self.closure(left.to_vec(), original, out);
            self.closure(right.to_vec(), original, out);
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

//! The class tests' full tier (gate `krs-class`, `scripts/krs-class.sh`): every case that
//! `krs_test_support::class_matrix` generates, through Cargo, rustc, the collector, and
//! `emit-k`'s lowering ([`pipeline`]), judged by the five table-free invariants and by
//! `krs/tests/class-matrix/expected.toml` where it covers the case, with the cases known not to
//! conform listed in `pending.toml`.
//!
//! The shards are ignored tests, one per family group: `readable` (readable records and claims),
//! `cells`, `init`, `terms`, and `import`, each of which also judges its accepted cases by K3
//! ([`closure`]) unless `KRS_CLASS_CLOSURE=0`; `k5`, which checks one broken header per entry
//! point ([`mutations`]); and `k4`, which compares KRS's sort judges with
//! k-rust's lattice on each base's emitted definition ([`lattice`]). Each prints its counts and its red cases per finding
//! and per step, and fails on a case that deviates and is not pending, a pending case that
//! conforms or deviates differently, and a table error.
//!
//! A K2 entry of `pending.toml` is keyed by the case's ID, and the fast tier reads the same entry
//! for a case the front refuses; where the two tiers observe such a case differently, this tier
//! reads `full/<case ID>` instead. A K1 entry of this tier, which judges keys after lowering, is
//! keyed `k1/<case ID>` (`class_matrix::pending`).
//!
//! The run is set by the environment (the script sets every variable from measured headroom):
//! - `KRS_CLASS_WORKERS`: concurrent workers, each with one Cargo target (default 1);
//! - `KRS_CLASS_BATCH`: the most cases in one batch package (default 40);
//! - `KRS_CLASS_SCRATCH`: the workers' directory, kept by the caller; by default each shard uses
//!   a temporary directory removed when it ends, failure included;
//! - `KRS_CLASS_FILTER`: a glob over case IDs (`expected.toml`'s syntax) that narrows a shard;
//! - `KRS_CLASS_OUT`: a directory for one TSV line per case and the pending entries of every
//!   deviation not yet recorded, `<shard>.tsv` and `<shard>.pending.toml`;
//! - `KRS_CLASS_RECORD=1`: the record mode. Each accepted case that no refusal rule covers gets
//!   its K written into `expected.toml` (`[accept."ID"].k`, [`closure::case_k`]), its entry
//!   created when the table has none; the K is reviewed as a diff, never written by hand.
//!
//! An accepted case that the table accepts must emit the K the table records, and the K of every
//! case its `same_k_as` names (K3's documented equal spellings, keyed `k3/<case ID>` with the
//! closure verdict).

#[path = "class_matrix/closure.rs"]
mod closure;
#[path = "class_matrix/lattice.rs"]
mod lattice;
#[path = "class_matrix/mutations.rs"]
mod mutations;
#[path = "class_matrix/pipeline.rs"]
mod pipeline;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use krs_compiler::testing::SortJudges;
use krs_test_support::class_matrix::invariants::{registry_kind, signature, violations};
use krs_test_support::class_matrix::pending::{
    CLOSURE, FULL, Judgement, KEYS, LATTICE, Observation, Pending, case_of,
};
use krs_test_support::class_matrix::table::{Expected, Glob, Resolution, Table, TableError};
use krs_test_support::class_matrix::{self, Base, Case, Family, Placed};

use closure::{Closure, case_k};
use pipeline::{Judged, Settings};

/// Whether a case no table entry decides fails the suite: the table covers every generated case,
/// so a new case needs its entry.
const UNCOVERED_IS_A_TABLE_ERROR: bool = true;

/// The K each accepted case was recorded with in this process, by ID: in the record mode, a
/// `same_k_as` names a case whose K an earlier shard of the run may have just written.
static RECORDED: Mutex<BTreeMap<String, String>> = Mutex::new(BTreeMap::new());

/// The generated cases and the two files that judge them.
struct Spec {
    cases: Vec<Case>,
    table: Table,
    pending: Pending,
}

fn spec() -> &'static Spec {
    static SPEC: OnceLock<Spec> = OnceLock::new();
    SPEC.get_or_init(|| {
        let table = Table::parse(&read_class_matrix("expected.toml"))
            .unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"));
        let pending = Pending::parse(&read_class_matrix("pending.toml"))
            .unwrap_or_else(|errors| panic!("pending.toml: {errors:#?}"));
        Spec {
            cases: class_matrix::cases(),
            table,
            pending,
        }
    })
}

fn class_matrix_path(file: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/class-matrix")
        .join(file)
}

fn read_class_matrix(file: &str) -> String {
    let path = class_matrix_path(file);
    std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

fn variable(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|value| !value.is_empty())
}

fn number(name: &str, default: usize) -> usize {
    variable(name).map_or(default, |value| {
        value
            .parse()
            .unwrap_or_else(|_| panic!("{name}={value:?} is not a count"))
    })
}

/// The prefix of every scratch directory of the tier, the script's and the test's own.
const SCRATCH_PREFIX: &str = "krs-class-";

/// The file in a scratch directory that names the process that owns it.
const OWNER: &str = "owner.pid";

/// Remove the scratch directories in the temporary directory whose owner is no running process:
/// a run that was killed (or a host that stopped) cannot remove its own, and its worker targets
/// are gigabytes. A directory whose owner file is missing or unreadable is reported, not removed.
fn remove_abandoned_scratch() {
    let Ok(entries) = std::fs::read_dir(std::env::temp_dir()) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let named = path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with(SCRATCH_PREFIX));
        if !named || !path.is_dir() {
            continue;
        }
        let owner = std::fs::read_to_string(path.join(OWNER))
            .ok()
            .and_then(|text| text.trim().parse::<u32>().ok());
        match owner {
            Some(pid) if Path::new(&format!("/proc/{pid}")).exists() => {}
            Some(_) => {
                eprintln!(
                    "[krs-class] removing the abandoned scratch {}",
                    path.display()
                );
                let _ = std::fs::remove_dir_all(&path);
            }
            None => eprintln!(
                "[krs-class] {} names no owner; remove it if no run uses it",
                path.display()
            ),
        }
    }
}

/// The run's settings, and the temporary scratch directory when the caller gave none.
fn settings() -> (Settings, Option<tempfile::TempDir>) {
    remove_abandoned_scratch();
    let (scratch, guard) = if let Some(directory) = variable("KRS_CLASS_SCRATCH") {
        (PathBuf::from(directory), None)
    } else {
        let guard = tempfile::Builder::new()
            .prefix(SCRATCH_PREFIX)
            .tempdir()
            .expect("the scratch directory is created");
        std::fs::write(guard.path().join(OWNER), std::process::id().to_string())
            .expect("the scratch's owner is written");
        (guard.path().to_path_buf(), Some(guard))
    };
    let settings = Settings {
        workers: number("KRS_CLASS_WORKERS", 1),
        batch: number("KRS_CLASS_BATCH", 40),
        scratch,
        closure: variable("KRS_CLASS_CLOSURE").is_none_or(|value| value != "0"),
    };
    (settings, guard)
}

/// The cases of `families`, narrowed by `KRS_CLASS_FILTER`.
fn selected(families: &[Family]) -> Vec<&'static Case> {
    let filter = variable("KRS_CLASS_FILTER").map(|pattern| {
        Glob::parse(&pattern).unwrap_or_else(|reason| panic!("KRS_CLASS_FILTER: {reason}"))
    });
    spec()
        .cases
        .iter()
        .filter(|case| families.contains(&case.family))
        .filter(|case| filter.as_ref().is_none_or(|glob| glob.matches(&case.id)))
        .collect()
}

/// What the table expects of a case that it covers and the case does not do, if anything. `k` is
/// the case's K once accepted; the record mode, which rewrites the table's K, leaves it out.
fn table_miss(
    expected: &Expected<'_>,
    judged: &Judged,
    placed: &Placed<'_>,
    k: Option<&str>,
) -> Option<String> {
    let observed = &judged.observed;
    match expected {
        Expected::Accept(_) if observed.refused() => Some("the table accepts the case".to_owned()),
        Expected::Accept(accepted) => match (accepted.k.as_deref(), k) {
            (Some(recorded), Some(k)) if recorded != k => {
                Some("the case emits other K than the table records".to_owned())
            }
            _ => None,
        },
        Expected::Refuse { rule, class } => {
            let Some(error) = observed.errors().next().filter(|_| observed.refused()) else {
                return Some(format!("the table refuses the case as {}", rule.class));
            };
            if error.code.as_deref() != Some(class.code.as_str()) {
                return Some(format!("the table expects {}", class.code));
            }
            let site = rule.at.range(placed);
            (!error.located_inside(site))
                .then(|| format!("the table expects the error inside the {:?}", rule.at))
        }
    }
}

/// One test's verdict on one case: its pending key ([`Shard::add`]), the signature of what the
/// case did, and what it should have done and did not (empty when it conforms).
struct Verdict {
    key: String,
    signature: String,
    misses: Vec<String>,
}

/// The verdicts of one shard, and what it prints and records.
#[derive(Default)]
struct Shard {
    verdicts: BTreeMap<&'static str, Vec<Verdict>>,
    failures: Vec<String>,
    lines: String,
    record: String,
}

impl Shard {
    /// Add `test`'s verdict on the case `id`, keyed `k1/<ID>` for K1, and for K2 by the case's
    /// ID, or `full/<ID>` when `pending.toml` has that entry.
    fn add(&mut self, test: &'static str, id: &str, signature: String, misses: Vec<String>) {
        let full = format!("{FULL}{id}");
        self.verdicts.entry(test).or_default().push(Verdict {
            key: match test {
                "k1" => format!("{KEYS}{id}"),
                "k3" => format!("{CLOSURE}{id}"),
                "k5" => id.to_owned(),
                _ if spec().pending.entries.contains_key(&full) => full,
                _ => id.to_owned(),
            },
            signature,
            misses,
        });
    }

    /// Apply the red list to every verdict, and fail each pending entry of `tests` for these
    /// `families` that names no verdict; returns the red keys.
    fn judge(&mut self, pending: &Pending, families: &[Family], stale_check: bool) -> Vec<String> {
        let mut red = Vec::new();
        for (test, verdicts) in &self.verdicts {
            for verdict in verdicts {
                let observation = if verdict.misses.is_empty() {
                    Observation::Conforms
                } else {
                    Observation::Deviates(&verdict.signature)
                };
                writeln!(
                    self.lines,
                    "{}\t{}\t{}",
                    verdict.key,
                    verdict.signature,
                    verdict.misses.join("; ")
                )
                .expect("writing to a String cannot fail");
                match pending.judge(&verdict.key, observation) {
                    Judgement::Red => red.push(verdict.key.clone()),
                    Judgement::Conforms => {}
                    failure => {
                        self.failures.push(format!("{}: {failure}", verdict.key));
                        if let Judgement::Unexpected { observed }
                        | Judgement::DeviationChanged { observed, .. } = failure
                        {
                            writeln!(
                                self.record,
                                "[{:?}]\nfinding = \"unassigned\"\ndeviation = {observed:?}\n# {}\n",
                                verdict.key,
                                verdict.misses.join("; ")
                            )
                            .expect("writing to a String cannot fail");
                        }
                    }
                }
            }
            if stale_check {
                let cases = verdicts
                    .iter()
                    .filter_map(|verdict| case_of(&verdict.key))
                    .collect::<BTreeSet<_>>();
                for key in pending.entries.keys() {
                    let ours = test_of(key) == *test;
                    let Some(case) = case_of(key).filter(|_| ours) else {
                        continue;
                    };
                    let in_shard = families
                        .iter()
                        .any(|family| case.starts_with(&format!("{}/", family.name())));
                    if in_shard && !cases.contains(case) {
                        self.failures.push(format!(
                            "{key}: pending, but this test judged no case with this ID"
                        ));
                    }
                }
            }
        }
        red
    }

    /// Apply the red list to `observed`, the signatures of the entries this test owns, which are
    /// those keyed under `prefix`: an entry with no observation conforms. Returns the red keys.
    fn judge_recorded(
        &mut self,
        pending: &Pending,
        prefix: &str,
        observed: &BTreeMap<String, String>,
    ) -> Vec<String> {
        let recorded = pending
            .entries
            .keys()
            .filter(|id| id.starts_with(prefix))
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut red = Vec::new();
        for key in recorded
            .iter()
            .chain(observed.keys())
            .collect::<BTreeSet<_>>()
        {
            let observation = observed
                .get(key)
                .map_or(Observation::Conforms, |signature| {
                    Observation::Deviates(signature)
                });
            match pending.judge(key, observation) {
                Judgement::Conforms => {}
                Judgement::Red => red.push(key.clone()),
                failure => {
                    self.failures.push(format!("{key}: {failure}"));
                    if let Judgement::Unexpected { observed }
                    | Judgement::DeviationChanged { observed, .. } = failure
                    {
                        writeln!(
                            self.record,
                            "[{key:?}]\nfinding = \"unassigned\"\ndeviation = {observed:?}\n"
                        )
                        .expect("writing to a String cannot fail");
                    }
                }
            }
        }
        red
    }
}

/// K2: the table-free invariants, and the table where it covers the case. `k` is the case's K
/// for the table's comparison, `None` in the record mode.
fn k2(
    shard: &mut Shard,
    resolution: &Resolution<'_>,
    case: &Case,
    judged: &Judged,
    k: Option<&str>,
) -> bool {
    let placed = judged.placed(case);
    let covered = resolution.expected.get(&judged.id);
    let site = covered.map_or(&placed.entry, |expected| expected.site(&placed));
    let mut misses = violations(&judged.observed, site, registry_kind)
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    if let Some(expected) = covered {
        misses.extend(table_miss(expected, judged, &placed, k));
    }
    let messages = judged
        .observed
        .errors()
        .map(|error| error.message.replace(['\n', '\t'], " "))
        .collect::<Vec<_>>();
    writeln!(
        shard.lines,
        "case\t{}\t{}\t{}",
        judged.id,
        judged.batch,
        messages.join(" | ")
    )
    .expect("writing to a String cannot fail");
    shard.add(
        "k2",
        &judged.id,
        signature(&judged.observed, &placed),
        misses,
    );
    covered.is_some()
}

/// The test a pending key belongs to.
fn test_of(key: &str) -> &'static str {
    if key.starts_with(KEYS) {
        "k1"
    } else if key.starts_with(CLOSURE) {
        "k3"
    } else if key.starts_with("entry/") {
        "k5"
    } else {
        "k2"
    }
}

/// The cases of `expected`'s `same_k_as` whose K is not `k`: the K this run recorded for them,
/// or else the table's.
fn other_k(expected: Option<&Expected<'_>>, k: &str) -> Vec<String> {
    let Some(Expected::Accept(accepted)) = expected else {
        return Vec::new();
    };
    let recorded = RECORDED.lock().expect("the recorded K is not poisoned");
    accepted
        .same_k_as
        .iter()
        .filter(|other| {
            let theirs = recorded
                .get(*other)
                .map(String::as_str)
                .or_else(|| spec().table.accept[*other].k.as_deref());
            theirs != Some(k)
        })
        .map(|other| format!("other K than {other}"))
        .collect()
}

/// K3: the source `krs expand` prints for the accepted cases emits each case's own sentences,
/// up to the normalization of [`closure`]; counted per form, which S6 reads. `pairs` are the
/// documented equal spellings whose K the case does not emit ([`other_k`]).
fn k3(
    shard: &mut Shard,
    judged: &Judged,
    pairs: Vec<String>,
    forms: &mut BTreeMap<String, BTreeMap<&'static str, usize>>,
) {
    let Some(verdict) = &judged.closure else {
        if !pairs.is_empty() {
            shard.add("k3", &judged.id, pairs.join("; "), pairs);
        }
        return;
    };
    let mut segments = judged.id.split('/');
    let family = segments.next().unwrap_or_default();
    let form = match family {
        "terms" | "import" => format!("{family}/{}", segments.next().unwrap_or_default()),
        _ => family.to_owned(),
    };
    *forms
        .entry(form)
        .or_default()
        .entry(verdict.column())
        .or_default() += 1;
    if let Closure::Different { original, printed } = verdict {
        writeln!(
            shard.lines,
            "k3-different\t{}\t{}\t{}",
            judged.id,
            original.join(" | ").replace('\n', " "),
            printed.join(" | ").replace('\n', " ")
        )
        .expect("writing to a String cannot fail");
    }
    let mut misses = if verdict.conforms() {
        Vec::new()
    } else {
        vec![verdict.column().to_owned()]
    };
    let signature = if pairs.is_empty() {
        verdict.signature()
    } else if verdict.conforms() {
        pairs.join("; ")
    } else {
        format!("{}; {}", verdict.signature(), pairs.join("; "))
    };
    misses.extend(pairs);
    shard.add("k3", &judged.id, signature, misses);
}

/// Write `recorded`, accepted cases' K by ID, into `expected.toml`: each case's `k`, its entry
/// created when the table has none, every other entry and key kept.
fn record(recorded: &BTreeMap<String, String>) {
    let path = class_matrix_path("expected.toml");
    let text = std::fs::read_to_string(&path).expect("expected.toml is read");
    let mut document = text
        .parse::<toml_edit::DocumentMut>()
        .expect("expected.toml parses");
    let accept = document
        .entry("accept")
        .or_insert_with(toml_edit::table)
        .as_table_mut()
        .expect("[accept] is a table");
    for (id, k) in recorded {
        let entry = accept
            .entry(id)
            .or_insert_with(toml_edit::table)
            .as_table_mut()
            .expect("an accept entry is a table");
        entry.insert("k", toml_edit::value(k.as_str()));
    }
    accept.sort_values();
    std::fs::write(&path, document.to_string()).expect("expected.toml is written");
}

/// K1 over the collected bundle and after lowering: every anchor of the case's descriptors lies
/// inside its node, and no semantic key is found twice. A case that never reached the
/// collector's output has no K1 verdict.
fn k1(shard: &mut Shard, judged: &Judged) {
    if let Some(keys) = &judged.keys {
        let signature = if keys.is_empty() {
            "keys injective, anchors inside their nodes".to_owned()
        } else {
            keys.join("; ")
        };
        shard.add("k1", &judged.id, signature, keys.clone());
    }
}

/// Each judged case's K once accepted ([`case_k`]), and in the record mode the K to record: every
/// accepted case's that no refusal rule covers, also made known to [`RECORDED`] before any
/// `same_k_as` is compared.
fn accepted_ks(
    judged: &[Judged],
    by_id: &BTreeMap<&str, &Case>,
    resolution: &Resolution<'_>,
    recording: bool,
) -> (Vec<Option<String>>, BTreeMap<String, String>) {
    let ks = judged
        .iter()
        .map(|judged| {
            (!judged.observed.refused())
                .then_some(judged.additions.as_deref())
                .flatten()
                .map(|additions| case_k(additions, &by_id[judged.id.as_str()].tag()))
        })
        .collect::<Vec<_>>();
    let mut recorded = BTreeMap::new();
    for (judged, k) in judged.iter().zip(&ks) {
        let refusal = matches!(
            resolution.expected.get(&judged.id),
            Some(Expected::Refuse { .. })
        );
        if recording
            && !refusal
            && let Some(k) = k
        {
            recorded.insert(judged.id.clone(), k.clone());
        }
    }
    RECORDED
        .lock()
        .expect("the recorded K is not poisoned")
        .extend(recorded.clone());
    (ks, recorded)
}

/// Run one shard: judge its cases and apply the table and the red list.
fn shard(name: &str, families: &[Family]) {
    let cases = selected(families);
    assert!(!cases.is_empty(), "the shard {name} selects no case");
    let spec = spec();
    let ids = spec
        .cases
        .iter()
        .map(|case| case.id.as_str())
        .collect::<Vec<_>>();
    let resolution = spec.table.resolve(&ids, registry_kind);
    let (settings, _scratch) = settings();
    let started = std::time::Instant::now();
    let judged = pipeline::judge_all(&cases, &settings);
    let by_id = cases
        .iter()
        .map(|case| (case.id.as_str(), *case))
        .collect::<BTreeMap<_, _>>();

    let mut shard = Shard::default();
    for error in &resolution.errors {
        if UNCOVERED_IS_A_TABLE_ERROR || !matches!(error, TableError::Uncovered { .. }) {
            shard.failures.push(format!("table: {error}"));
        }
    }
    let recording = variable("KRS_CLASS_RECORD").is_some_and(|value| value != "0");
    let mut accepted = 0;
    let mut uncovered = 0;
    let mut forms = BTreeMap::new();
    let (ks, recorded) = accepted_ks(&judged, &by_id, &resolution, recording);
    for (judged, k) in judged.iter().zip(ks) {
        let case = by_id[judged.id.as_str()];
        let expected = resolution.expected.get(&judged.id);
        if !judged.observed.refused() {
            accepted += 1;
            if k.is_none() {
                shard
                    .failures
                    .push(format!("{}: accepted, but its K is unknown", judged.id));
            }
        }
        if let (Some(Expected::Accept(entry)), Some(_), false) = (expected, &k, recording)
            && entry.k.is_none()
        {
            shard.failures.push(format!(
                "{}: accepted, but expected.toml records no K for it; run scripts/krs-class.sh --record",
                judged.id
            ));
        }
        let compared = k.as_deref().filter(|_| !recording);
        if !k2(&mut shard, &resolution, case, judged, compared) {
            uncovered += 1;
        }
        k1(&mut shard, judged);
        let pairs = k.as_deref().map_or_else(Vec::new, |k| other_k(expected, k));
        k3(&mut shard, judged, pairs, &mut forms);
    }
    if recording {
        record(&recorded);
        eprintln!(
            "[krs-class] {name}: recorded the K of {} accepted cases in expected.toml",
            recorded.len()
        );
    }
    let red = shard.judge(
        &spec.pending,
        families,
        variable("KRS_CLASS_FILTER").is_none(),
    );
    if let Some(out) = variable("KRS_CLASS_OUT") {
        let out = PathBuf::from(out);
        std::fs::create_dir_all(&out).expect("the output directory is created");
        std::fs::write(out.join(format!("{name}.tsv")), &shard.lines).expect("the TSV is written");
        std::fs::write(out.join(format!("{name}.pending.toml")), &shard.record)
            .expect("the pending entries are written");
    }

    for (form, counts) in &forms {
        eprintln!("[krs-class] {name}: K3 {form}: {counts:?}");
    }
    let tally = spec.pending.tally(red.iter().map(String::as_str));
    let mut by_test = BTreeMap::<&str, usize>::new();
    for key in &red {
        *by_test.entry(test_of(key)).or_default() += 1;
    }
    eprintln!(
        "[krs-class] {name}: {} cases in {:.1} s; {accepted} accepted, {} refused; red {} (by test {by_test:?}; by finding {:?}; by step {:?}); {uncovered} not covered by the table",
        judged.len(),
        started.elapsed().as_secs_f64(),
        judged.len() - accepted,
        red.len(),
        tally.by_finding,
        tally.by_step,
    );
    assert!(
        shard.failures.is_empty(),
        "{} class-test failures in shard {name}:\n{}",
        shard.failures.len(),
        shard.failures.join("\n")
    );
}

#[test]
#[ignore = "the full tier builds packages; run it through scripts/krs-class.sh"]
fn readable() {
    shard("readable", &[Family::Readable, Family::Claim]);
}

#[test]
#[ignore = "the full tier builds packages; run it through scripts/krs-class.sh"]
fn cells() {
    shard("cells", &[Family::Cells]);
}

#[test]
#[ignore = "the full tier builds packages; run it through scripts/krs-class.sh"]
fn init() {
    shard("init", &[Family::Init]);
}

#[test]
#[ignore = "the full tier builds packages; run it through scripts/krs-class.sh"]
fn terms() {
    shard("terms", &[Family::Terms]);
}

#[test]
#[ignore = "the full tier builds packages; run it through scripts/krs-class.sh"]
fn import() {
    shard("import", &[Family::Import]);
}

#[test]
#[ignore = "the full tier builds packages; run it through scripts/krs-class.sh"]
fn k4() {
    let spec = spec();
    let (settings, _scratch) = settings();
    let started = std::time::Instant::now();
    let comparisons = std::thread::scope(|scope| {
        let handles = Base::ALL.map(|base| {
            let settings = &settings;
            scope.spawn(move || {
                let name = format!("class-{}", format!("{base:?}").to_lowercase());
                let collected = pipeline::collect_source(settings, &name, &base.preamble())
                    .unwrap_or_else(|error| panic!("the {base:?} base collects: {error}"));
                let judges = SortJudges::of_bundle(&collected.bundle)
                    .unwrap_or_else(|error| panic!("the {base:?} base lowers: {error}"));
                let emitted = collected
                    .emit_k(collected.bundle.clone())
                    .unwrap_or_else(|error| panic!("the {base:?} base emits: {error}"));
                (name, lattice::compare(&judges, &emitted.ir))
            })
        });
        handles.map(|handle| handle.join().expect("a base's comparison does not panic"))
    });

    let mut observed = BTreeMap::<String, String>::new();
    let mut open = BTreeMap::<lattice::Class, usize>::new();
    let mut report = String::new();
    for (name, comparison) in &comparisons {
        writeln!(report, "{name}: {} sorts", comparison.sorts)
            .expect("writing to a String cannot fail");
        for ((judge, k_rust, class), count) in &comparison.counts {
            let signature = lattice::signature(count, *judge, *k_rust);
            writeln!(
                report,
                "  {} ~ {} {}: {signature}",
                judge.name(),
                k_rust.name(),
                class.name()
            )
            .expect("writing to a String cannot fail");
            if class.open() {
                *open.entry(*class).or_default() += count.krs_only + count.k_rust_only;
            } else {
                observed.insert(
                    format!(
                        "{LATTICE}{name}/{}~{}/{}",
                        judge.name(),
                        k_rust.name(),
                        class.name()
                    ),
                    signature,
                );
            }
        }
    }
    writeln!(report, "open classes (counted, not failed): {open:?}")
        .expect("writing to a String cannot fail");

    let mut shard = Shard::default();
    let red = shard.judge_recorded(&spec.pending, &format!("{LATTICE}class-"), &observed);
    if let Some(out) = variable("KRS_CLASS_OUT") {
        let out = PathBuf::from(out);
        std::fs::create_dir_all(&out).expect("the output directory is created");
        std::fs::write(out.join("k4.txt"), &report).expect("the report is written");
        std::fs::write(out.join("k4.pending.toml"), &shard.record)
            .expect("the pending entries are written");
    }
    let tally = spec.pending.tally(red.iter().map(String::as_str));
    eprint!("{report}");
    eprintln!(
        "[krs-class] k4: {} bases in {:.1} s; red {} (by finding {:?}; by step {:?})",
        comparisons.len(),
        started.elapsed().as_secs_f64(),
        red.len(),
        tally.by_finding,
        tally.by_step,
    );
    assert!(
        shard.failures.is_empty(),
        "{} class-test failures in shard k4:\n{}",
        shard.failures.len(),
        shard.failures.join("\n")
    );
}

#[test]
#[ignore = "the full tier builds packages; run it through scripts/krs-class.sh"]
fn k5() {
    let spec = spec();
    let (settings, _scratch) = settings();
    let started = std::time::Instant::now();
    let checked = mutations::check_all(&settings);
    let (base, checked): (Vec<_>, Vec<_>) = checked
        .into_iter()
        .partition(|checked| checked.id == "entry/base");
    let base = &base[0];
    assert!(
        base.krs == mutations::Counts::default() && base.cargo == mutations::Counts::default(),
        "the K5 base must pass both checks without a diagnostic: {}",
        base.signature()
    );
    let mut shard = Shard::default();
    let mut one = [0, 0];
    for checked in &checked {
        one[0] += usize::from(checked.krs.errors.len() == 1 && checked.krs.warnings.is_empty());
        one[1] += usize::from(checked.cargo.errors.len() == 1 && checked.cargo.warnings.is_empty());
        let misses = if checked.conforms() {
            Vec::new()
        } else {
            vec!["more or fewer than one diagnostic".to_owned()]
        };
        shard.add("k5", &checked.id, checked.signature(), misses);
    }
    let red = shard.judge(&spec.pending, &[], false);
    let judged = checked
        .iter()
        .map(|checked| checked.id.as_str())
        .collect::<BTreeSet<_>>();
    for key in spec.pending.entries.keys() {
        if key.starts_with("entry/") && !judged.contains(key.as_str()) {
            shard
                .failures
                .push(format!("{key}: pending, but no mutation has this ID"));
        }
    }
    if let Some(out) = variable("KRS_CLASS_OUT") {
        let out = PathBuf::from(out);
        std::fs::create_dir_all(&out).expect("the output directory is created");
        std::fs::write(out.join("k5.tsv"), &shard.lines).expect("the TSV is written");
        std::fs::write(out.join("k5.pending.toml"), &shard.record)
            .expect("the pending entries are written");
    }
    let tally = spec.pending.tally(red.iter().map(String::as_str));
    eprintln!(
        "[krs-class] k5: {} entry points in {:.1} s; one diagnostic under krs check {}, under cargo check {}; red {} (by finding {:?}; by step {:?})",
        checked.len(),
        started.elapsed().as_secs_f64(),
        one[0],
        one[1],
        red.len(),
        tally.by_finding,
        tally.by_step,
    );
    assert!(
        shard.failures.is_empty(),
        "{} class-test failures in shard k5:\n{}",
        shard.failures.len(),
        shard.failures.join("\n")
    );
}

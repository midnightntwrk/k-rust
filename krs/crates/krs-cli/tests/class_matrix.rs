//! The class tests' full tier (gate `krs-class`, `scripts/krs-class.sh`): every case that
//! `krs_test_support::class_matrix` generates, through Cargo, rustc, the collector, and
//! `emit-k`'s lowering ([`pipeline`]), judged by the five table-free invariants and by
//! `krs/tests/class-matrix/expected.toml` where it covers the case (a term case by the oracle
//! first, `class_matrix::table`'s precedence), with the cases known not to conform listed in
//! `pending.toml`.
//!
//! The shards are ignored tests, one per family group: `readable` (readable records and claims),
//! `cells`, `runs` (the readable records and `cells!` rules on the run base, which K7 runs), `init`,
//! `terms`, `import`, `notation` (the collection notation at the term
//! positions), and `attrs` (every sentence attribute on every sentence form), each of which also
//! judges its accepted cases by K3
//! ([`closure`]) unless `KRS_CLASS_CLOSURE=0`, by K6 (the definition an accepted case emits
//! passes the judgement `krs check` makes on the native routes, [`pipeline`]) unless
//! `KRS_CLASS_NATIVE=0`, and by K7 (the case's program, run on that definition, shows its
//! sentence applied, with the value the generator states, [`runs`]) unless `KRS_CLASS_RUN=0`,
//! and judges the advice of the classes whose refusal advises a rewrite (K8, [`k8`]);
//! `k5`, which checks one broken header per entry
//! point ([`mutations`]); and `k4`, which compares KRS's sort judges with
//! k-rust's lattice on each base's emitted definition ([`lattice`]). Each prints its counts and its red cases per finding
//! and per step, and fails on a case that deviates and is not pending, a pending case that
//! conforms or deviates differently, and a table error.
//!
//! A K2 entry of `pending.toml` is keyed by the case's ID, and the fast tier reads the same entry
//! for a case the front refuses; where the two tiers observe such a case differently, this tier
//! reads `full/<case ID>` instead. A K1 entry of this tier, which judges keys after lowering, is
//! keyed `k1/<case ID>`, a K6 entry `k6/<case ID>`, a K7 entry `k7/<case ID>`, and a K8 entry
//! `k8/<case ID>` (`class_matrix::pending`).
//!
//! The run is set by the environment (the script sets every variable from measured headroom):
//! - `KRS_CLASS_WORKERS`: concurrent workers, each with one Cargo target (default 1);
//! - `KRS_CLASS_BATCH`: the most cases in one batch package (default 40);
//! - `KRS_CLASS_SCRATCH`: the workers' directory, kept by the caller; by default each shard uses
//!   a temporary directory removed when it ends, failure included;
//! - `KRS_CLASS_FILTER`: a glob over case IDs (`expected.toml`'s syntax) that narrows a shard;
//! - `KRS_CLASS_NATIVE`: `0` skips K6, `alone` judges each accepted case alone rather than the
//!   accepted cases of a batch together (the default, `1`), which must give the same verdicts;
//! - `KRS_CLASS_RUN`: `0` skips K7, which runs on K6's compile and so does not run without it;
//!   `KRS_CLASS_RUN_SECONDS` is its time limit per program (default 60);
//! - `KRS_CLASS_OUT`: a directory for one TSV line per case and the pending entries of every
//!   deviation not yet recorded, `<shard>.tsv` and `<shard>.pending.toml`;
//! - `KRS_CLASS_RECORD=1`: the record mode. Each accepted case that the table does not refuse
//!   gets its K written into `expected.toml`, or a term family's into `accepted-terms.toml`
//!   (`[accept."ID"].k`, [`closure::case_k`]), its entry created when the table has none; the K is
//!   reviewed as a diff, never written by hand.
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
#[path = "class_matrix/runs.rs"]
mod runs;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use krs_compiler::testing::SortJudges;
use krs_test_support::class_matrix::advice::{Corpus, Followed, Reading, judge, read};
use krs_test_support::class_matrix::invariants::{
    Observed, registry_kind, signature, violations, without_rustc_parse_error,
};
use krs_test_support::class_matrix::k7::K7;
use krs_test_support::class_matrix::pending::{
    ADVICE, CLOSURE, FULL, Judgement, KEYS, LATTICE, NATIVE, Observation, Pending, RUN, case_of,
};
use krs_test_support::class_matrix::table::{
    Expected, Glob, Resolution, TERM_ACCEPTS_FILE, Table, TableError, in_term_accepts,
};
use krs_test_support::class_matrix::{self, Base, Case, Family, Placed};

use closure::{Closure, case_k};
use pipeline::{Judged, Native, NativeMode, Settings};
use runs::Ran;

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
        let table = Table::parse_with_term_accepts(
            &read_class_matrix("expected.toml"),
            &read_class_matrix(TERM_ACCEPTS_FILE),
        )
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
        native: match variable("KRS_CLASS_NATIVE").as_deref() {
            None | Some("1") => NativeMode::Batched,
            Some("0") => NativeMode::Off,
            Some("alone") => NativeMode::Alone,
            Some(other) => panic!("KRS_CLASS_NATIVE={other:?} is not 0, 1 or alone"),
        },
        refused_by_table: BTreeSet::new(),
        run: match variable("KRS_CLASS_RUN").as_deref() {
            None | Some("1") => Some(std::time::Duration::from_secs(number(
                "KRS_CLASS_RUN_SECONDS",
                60,
            ) as u64)),
            Some("0") => None,
            Some(other) => panic!("KRS_CLASS_RUN={other:?} is not 0 or 1"),
        },
    };
    let mut settings = settings;
    if settings.native == NativeMode::Off && settings.run.is_some() {
        eprintln!(
            "[krs-class] K7 runs on the definition K6 compiles: with KRS_CLASS_NATIVE=0 it does not run"
        );
        settings.run = None;
    }
    // K6 must make the judgement `krs check` makes, whose native compile infers sorts with Z3: a
    // build without the solver infers them by another engine and could judge otherwise.
    assert!(
        settings.native == NativeMode::Off || cfg!(feature = "z3-inference"),
        "K6 judges as `krs check` does, with Z3's sort inference, but this test was built without \
         `--features z3-inference`: build it with that feature and Z3 on the link path (as \
         scripts/krs-class.sh does), or skip K6 with KRS_CLASS_NATIVE=0"
    );
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
    observed: &Observed,
    placed: &Placed<'_>,
    k: Option<&str>,
) -> Option<String> {
    match expected {
        Expected::Accept(_) if observed.refused() => Some("the table accepts the case".to_owned()),
        Expected::Accept(accepted) => match (accepted.k.as_deref(), k) {
            (Some(recorded), Some(k)) if recorded != k => {
                Some("the case emits other K than the table records".to_owned())
            }
            _ => None,
        },
        Expected::Refuse { name, class, at } => {
            let Some(error) = observed.errors().next().filter(|_| observed.refused()) else {
                return Some(format!("the table refuses the case as {name}"));
            };
            if error.code.as_deref() != Some(class.code.as_str()) {
                return Some(format!("the table expects {}", class.code));
            }
            let site = at.range(placed);
            (!error.located_inside(site))
                .then(|| format!("the table expects the error inside the {at:?}"))
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
    /// K8's unchecked refusals by class: those whose proposed form no generated case writes.
    unchecked: BTreeMap<String, usize>,
}

impl Shard {
    /// Add `test`'s verdict on the case `id`, keyed `k1/<ID>` for K1, `k3/<ID>` for K3, `k6/<ID>`
    /// for K6, `k7/<ID>` for K7, and for K2 by the case's ID, or `full/<ID>` when `pending.toml`
    /// has that entry.
    fn add(&mut self, test: &'static str, id: &str, signature: String, misses: Vec<String>) {
        let full = format!("{FULL}{id}");
        self.verdicts.entry(test).or_default().push(Verdict {
            key: match test {
                "k1" => format!("{KEYS}{id}"),
                "k3" => format!("{CLOSURE}{id}"),
                "k6" => format!("{NATIVE}{id}"),
                "k7" => format!("{RUN}{id}"),
                "k8" => format!("{ADVICE}{id}"),
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
/// for the table's comparison, `None` in the record mode. At a position rustc parses, rustc's
/// parse error beside KRS's one error at the same spelling is left out of the judgement
/// ([`without_rustc_parse_error`]), not out of the signature. Whether the table covers the case.
/// The case's line of the TSV shows its errors' messages, the class the table expects, and their
/// help lines.
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
    let observed = without_rustc_parse_error(&judged.observed, &placed);
    let mut misses = violations(&observed, site, registry_kind)
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    if let Some(expected) = covered {
        misses.extend(table_miss(expected, &observed, &placed, k));
    }
    let messages = judged
        .observed
        .errors()
        .map(|error| error.message.replace(['\n', '\t'], " "))
        .collect::<Vec<_>>();
    let help = judged
        .observed
        .errors()
        .flat_map(|error| error.help.iter())
        .map(|help| help.replace(['\n', '\t'], " "))
        .collect::<Vec<_>>();
    let class = match covered {
        Some(Expected::Refuse { name, .. }) => name,
        Some(Expected::Accept(_)) => "accept",
        None => "-",
    };
    writeln!(
        shard.lines,
        "case\t{}\t{}\t{}\t{class}\t{}",
        judged.id,
        judged.batch,
        messages.join(" | "),
        help.join(" | ")
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

/// K8, the advice check (`class_matrix::advice`), keyed `k8/<case ID>`:
/// - a case a class advises writing in place of a case it refuses (`expected.toml`'s `advice`,
///   resolved on the refused case's form) is accepted, passes K6 and runs as K7 states where K6
///   and K7 ran;
/// - each refused case's KRS errors are read for the form they advise: a class marked
///   `advice = "none"` whose refusal advises one deviates; a class that advises a case deviates
///   where that case is not generated or not accepted on the refused case's form, or does not
///   write the form the refusal proposes (or writes the form it says to take away); a case the
///   table accepts, refused, deviates where its refusal advises a form, since the case already
///   writes what is valid.
///
/// Every refused case is read, whether or not its refusal conforms (a pending one included).
fn k8(
    shard: &mut Shard,
    resolution: &Resolution<'_>,
    advised_by: &BTreeMap<String, BTreeSet<&str>>,
    corpus: &Corpus,
    judged: &Judged,
) {
    if let Some(advising) = advised_by.get(&judged.id) {
        k8_advised(shard, advising, judged);
    }
    if judged.observed.refused() {
        k8_refusal(shard, resolution, corpus, judged);
    }
}

/// K8 on a case classes advise writing: it is accepted, passes K6 and runs as K7 states.
fn k8_advised(shard: &mut Shard, advising: &BTreeSet<&str>, judged: &Judged) {
    {
        let of = format!(
            "advice of {}",
            advising.iter().copied().collect::<Vec<_>>().join(", ")
        );
        let deviation = if judged.observed.refused() {
            Some(format!(
                "{of}: refused: {}",
                judged
                    .observed
                    .errors()
                    .map(|error| error.code.as_deref().unwrap_or("uncoded"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ))
        } else if let Some(native @ Native::Refused { .. }) = &judged.native {
            Some(format!("{of}: K6: {}", native.signature()))
        } else if let Some(ran @ Ran::Deviates(_)) = &judged.ran {
            Some(format!("{of}: K7: {}", ran.signature()))
        } else {
            None
        };
        let (signature, misses) = match deviation {
            Some(deviation) => (
                deviation,
                vec!["the form a class's refusal advises is not accepted as written".to_owned()],
            ),
            None => (format!("{of}: accepted"), Vec::new()),
        };
        shard.add("k8", &judged.id, signature, misses);
    }
}

/// K8 on a refused case: what its KRS errors advise, against its class's advice.
fn k8_refusal(shard: &mut Shard, resolution: &Resolution<'_>, corpus: &Corpus, judged: &Judged) {
    let mut reading = Reading::default();
    for error in judged.observed.errors().filter(|error| {
        error
            .code
            .as_deref()
            .is_some_and(|code| code.starts_with("krs::"))
    }) {
        reading.groups.extend(read(error).groups);
    }
    let forms = reading
        .forms()
        .map(|advice| {
            let verb = if advice.removes { "drop " } else { "" };
            format!("{verb}`{}`", advice.form)
        })
        .collect::<Vec<_>>();
    let advice = (!forms.is_empty()).then(|| forms.join(", "));
    let mut verdict = |signature: String, miss: Option<&str>| {
        shard.add(
            "k8",
            &judged.id,
            signature,
            miss.map(str::to_owned).into_iter().collect(),
        );
    };
    match resolution.expected.get(&judged.id) {
        Some(Expected::Refuse { name, class, .. }) => {
            let advised = class.advised_cases(&judged.id);
            if advised.is_empty() {
                if let Some(advice) = advice {
                    verdict(
                        format!("{name} advises none, and its refusal advises {advice}"),
                        Some("a refusal advises a rewrite its class does not"),
                    );
                }
                return;
            }
            // A refusal that advises nothing here has no advice to judge: the class's advised
            // cases are judged as cases of their own.
            if reading.groups.is_empty() {
                return;
            }
            let (signature, miss) = k8_against(
                name,
                &advised,
                &reading,
                advice.as_deref(),
                resolution,
                corpus,
            );
            let unchecked = signature.contains(UNCHECKED_MARK);
            verdict(signature, miss);
            if unchecked {
                *shard.unchecked.entry((*name).to_owned()).or_default() += 1;
            }
        }
        Some(Expected::Accept(_)) => {
            if let Some(advice) = advice {
                verdict(
                    format!("refused where the table accepts, advising {advice}"),
                    Some("a refusal of a case the table accepts advises a rewrite"),
                );
            }
        }
        None => {}
    }
}

/// K8's verdict on a refusal of the class `name` that reads `reading` (its forms `advice`),
/// against the class's advised cases `advised`: the signature, and the miss where it deviates.
fn k8_against(
    name: &str,
    advised: &[String],
    reading: &Reading,
    advice: Option<&str>,
    resolution: &Resolution<'_>,
    corpus: &Corpus,
) -> (String, Option<&'static str>) {
    // The advised cases this form has, generated and accepted, with their own text.
    let mut missing = Vec::new();
    let mut sources = Vec::new();
    for case in advised {
        match (
            spec().cases.iter().find(|generated| generated.id == *case),
            resolution.expected.get(case),
        ) {
            (None, _) => missing.push(format!("{case}, which is not generated")),
            (Some(generated), Some(Expected::Accept(_))) => {
                sources.push((case, generated.own_source()));
            }
            (Some(_), Some(Expected::Refuse { name: refused, .. })) => {
                missing.push(format!("{case}, which the table refuses ({refused})"));
            }
            (Some(_), None) => {
                missing.push(format!("{case}, which the table does not decide"));
            }
        }
    }
    if sources.is_empty() {
        (
            format!("{name} advises {}", missing.join("; ")),
            Some("the form a refusal advises does not exist on its form"),
        )
    } else {
        let cases = sources
            .iter()
            .map(|(case, _)| case.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        let texts = sources
            .into_iter()
            .map(|(_, source)| source)
            .collect::<Vec<_>>();
        let follows = advice.unwrap_or("prose");
        match judge(reading, &texts, corpus) {
            Followed::Followed => (
                format!("{name} advises {cases}, which follows {follows}"),
                None,
            ),
            Followed::Unwritten { form, writer } => (
                format!(
                    "{name}'s refusal advises `{form}`, which {cases} does not write ({writer} does)"
                ),
                Some("the refusal advises a form its class's advised case does not write"),
            ),
            Followed::Unchecked => (
                format!("{name} advises {cases}{UNCHECKED_MARK}no generated case writes {follows}"),
                None,
            ),
        }
    }
}

/// Write the shard's TSV and its unrecorded pending entries to `KRS_CLASS_OUT`, where it is set.
fn write_out(name: &str, shard: &Shard) {
    if let Some(out) = variable("KRS_CLASS_OUT") {
        let out = PathBuf::from(out);
        std::fs::create_dir_all(&out).expect("the output directory is created");
        std::fs::write(out.join(format!("{name}.tsv")), &shard.lines).expect("the TSV is written");
        std::fs::write(out.join(format!("{name}.pending.toml")), &shard.record)
            .expect("the pending entries are written");
    }
}

/// What a K8 signature says of a refusal whose proposed forms no generated case writes.
const UNCHECKED_MARK: &str = "; unchecked: ";

/// K8's unchecked refusals, by shard and class: refusals whose proposed form no generated case
/// writes, which only the class's reviewed `advice` states (`class_matrix::advice::Followed`).
/// A shard whose counts differ fails, so a new class or a message that adds unchecked advice is
/// reviewed before it is pinned here; a case shard listed in [`NO_UNCHECKED`] has none.
const UNCHECKED: &[(&str, &str, usize)] = &[
    ("init", "content-sort", 8),
    ("init", "initializer-remainder", 1),
    ("notation", "function-in-pattern", 4),
    ("notation", "ml-in-condition", 27),
    ("terms", "alias-at-subject-root", 2),
    ("terms", "alias-in-let-pattern", 34),
    ("terms", "configuration-variable-sort", 2),
    ("terms", "function-in-pattern", 8),
    ("terms", "island-at-subject-root", 18),
    ("terms", "ml-in-condition", 40),
    ("terms", "notation-in-pattern", 264),
    ("terms", "record-remainder-in-initializer", 4),
    ("terms", "sort-test-in-pattern", 70),
    ("terms", "wildcard-at-subject-root", 2),
];

/// The case shards whose refusals propose no form outside the generated cases: K8 checks all of
/// their advice. A case shard is pinned in [`UNCHECKED`] or here.
const NO_UNCHECKED: &[&str] = &["attrs", "cells", "import", "readable", "runs"];

/// Fail the shard `name` where its unchecked K8 refusals differ from [`UNCHECKED`]'s, or where it
/// is pinned neither there nor in [`NO_UNCHECKED`].
fn check_unchecked(name: &str, shard: &mut Shard) {
    if !NO_UNCHECKED.contains(&name) && !UNCHECKED.iter().any(|(pinned, ..)| *pinned == name) {
        shard.failures.push(format!(
            "the shard {name} pins its unchecked K8 refusals neither in UNCHECKED nor in NO_UNCHECKED"
        ));
    }
    let pinned = UNCHECKED
        .iter()
        .filter(|(pinned, ..)| *pinned == name)
        .map(|(_, class, count)| ((*class).to_owned(), *count))
        .collect::<BTreeMap<_, _>>();
    if shard.unchecked != pinned {
        shard.failures.push(format!(
            "K8's unchecked refusals by class are {:?}, where UNCHECKED pins {pinned:?}: review the advice no generated case writes, then pin it",
            shard.unchecked
        ));
    }
}

/// The own text of every generated case the table accepts, for the forms K8 reads.
fn accepted_corpus(resolution: &Resolution<'_>) -> Corpus {
    Corpus::new(
        spec()
            .cases
            .iter()
            .filter(|case| matches!(resolution.expected.get(&case.id), Some(Expected::Accept(_))))
            .map(|case| (case.id.clone(), case.own_source())),
    )
}

/// The classes that advise each case: every refused case's resolution of its class's advice
/// that the table accepts. A resolution the table refuses is the refused case's deviation, which
/// [`k8`] reports there, where the refusal advises it.
fn advised_by<'r>(resolution: &'r Resolution<'_>) -> BTreeMap<String, BTreeSet<&'r str>> {
    let mut advised = BTreeMap::<String, BTreeSet<&str>>::new();
    for (id, expected) in &resolution.expected {
        if let Expected::Refuse { name, class, .. } = expected {
            for case in class.advised_cases(id) {
                if matches!(resolution.expected.get(&case), Some(Expected::Accept(_))) {
                    advised.entry(case).or_default().insert(name);
                }
            }
        }
    }
    advised
}

/// The test a pending key belongs to.
fn test_of(key: &str) -> &'static str {
    if key.starts_with(KEYS) {
        "k1"
    } else if key.starts_with(CLOSURE) {
        "k3"
    } else if key.starts_with(NATIVE) {
        "k6"
    } else if key.starts_with(RUN) {
        "k7"
    } else if key.starts_with(ADVICE) {
        "k8"
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
        "terms" | "import" | "notation" => {
            format!("{family}/{}", segments.next().unwrap_or_default())
        }
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

/// Write `recorded`, accepted cases' K by ID, into the table: a term family's case into
/// [`TERM_ACCEPTS_FILE`], any other into `expected.toml`; each case's `k`, its entry created when
/// the file has none, every other entry and key kept.
fn record(recorded: &BTreeMap<String, String>) {
    let (terms, others): (BTreeMap<_, _>, BTreeMap<_, _>) =
        recorded.iter().partition(|(id, _)| in_term_accepts(id));
    for (file, recorded) in [(TERM_ACCEPTS_FILE, terms), ("expected.toml", others)] {
        if recorded.is_empty() {
            continue;
        }
        let path = class_matrix_path(file);
        let text = std::fs::read_to_string(&path).unwrap_or_else(|_| panic!("{file} is read"));
        let mut document = text
            .parse::<toml_edit::DocumentMut>()
            .unwrap_or_else(|_| panic!("{file} parses"));
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
        std::fs::write(&path, document.to_string()).unwrap_or_else(|_| panic!("{file} is written"));
    }
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

/// K6: the definition an accepted case emits passes the judgement `krs check` makes, on every
/// native route. A case K6 did not judge (refused, refused by the table, or a run with
/// `KRS_CLASS_NATIVE=0`) has no K6 verdict.
fn k6(shard: &mut Shard, judged: &Judged) {
    if let Some(native) = &judged.native {
        let misses = match native {
            Native::Accepted => Vec::new(),
            Native::Refused { messages, .. } => {
                writeln!(
                    shard.lines,
                    "k6-refusal\t{}\t{}",
                    judged.id,
                    messages.join(" | ").replace(['\n', '\t'], " ")
                )
                .expect("writing to a String cannot fail");
                vec!["`krs check` refuses the definition KRS wrote".to_owned()]
            }
        };
        shard.add("k6", &judged.id, native.signature(), misses);
    }
}

/// K7: the program of a case K6 accepted, run on the definition K6 judged, shows that the case's
/// sentence applied, with the value the generator states. A case K7 did not run (no plan, K6
/// refused it, or a run with `KRS_CLASS_RUN=0`) has no K7 verdict.
fn k7(shard: &mut Shard, judged: &Judged) {
    if let Some(ran) = &judged.ran {
        let misses = match ran {
            Ran::Conforms(_) => Vec::new(),
            Ran::Deviates(_) => {
                vec!["the run does not show what the case's sentence denotes".to_owned()]
            }
        };
        shard.add("k7", &judged.id, ran.signature(), misses);
    }
}

/// Print what K7 checked of the cases K6 accepts, when the run ran K7: a stated value, liveness
/// only, nothing (and why: no driver, no witness, no value), or a deviation.
fn k7_statuses(name: &str, judged: &[Judged], by_id: &BTreeMap<&str, &Case>, ran: bool) {
    if !ran {
        return;
    }
    let mut statuses = BTreeMap::<&'static str, usize>::new();
    for judged in judged
        .iter()
        .filter(|judged| judged.native == Some(Native::Accepted))
    {
        let status = match (&by_id[judged.id.as_str()].k7, &judged.ran) {
            (_, Some(Ran::Deviates(_))) => "deviates",
            (K7::Run(_), None) => "not run",
            (plan, _) => plan.status(),
        };
        *statuses.entry(status).or_default() += 1;
    }
    eprintln!(
        "[krs-class] {name}: K7 over the {} cases K6 accepts, by what it checks: {statuses:?}",
        statuses.values().sum::<usize>()
    );
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
    let resolution = spec.table.resolve_cases(&spec.cases, registry_kind);
    let (mut settings, _scratch) = settings();
    settings.refused_by_table = resolution
        .expected
        .iter()
        .filter(|(_, expected)| matches!(expected, Expected::Refuse { .. }))
        .map(|(id, _)| id.clone())
        .collect();
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
    let advised = advised_by(&resolution);
    let corpus = accepted_corpus(&resolution);
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
        let covered = k2(&mut shard, &resolution, case, judged, compared);
        uncovered += usize::from(!covered);
        k1(&mut shard, judged);
        let pairs = k.as_deref().map_or_else(Vec::new, |k| other_k(expected, k));
        k3(&mut shard, judged, pairs, &mut forms);
        k6(&mut shard, judged);
        k7(&mut shard, judged);
        k8(&mut shard, &resolution, &advised, &corpus, judged);
    }
    if recording {
        record(&recorded);
        eprintln!(
            "[krs-class] {name}: recorded the K of {} accepted cases in expected.toml",
            recorded.len()
        );
    }
    let whole = variable("KRS_CLASS_FILTER").is_none();
    if whole {
        check_unchecked(name, &mut shard);
    }
    let red = shard.judge(&spec.pending, families, whole);
    write_out(name, &shard);

    for (form, counts) in &forms {
        eprintln!("[krs-class] {name}: K3 {form}: {counts:?}");
    }
    k7_statuses(name, &judged, &by_id, settings.run.is_some());
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
fn runs() {
    shard("runs", &[Family::ReadableRun, Family::CellsRun]);
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
fn notation() {
    shard("notation", &[Family::Notation]);
}

#[test]
#[ignore = "the full tier builds packages; run it through scripts/krs-class.sh"]
fn attrs() {
    shard("attrs", &[Family::Attributes]);
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
        one[1] += usize::from(checked.cargo.errors.len() == 1);
        let misses = if checked.conforms() {
            Vec::new()
        } else {
            vec![
                "more or fewer than one diagnostic under krs check, or one error under cargo check"
                    .to_owned(),
            ]
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
        "[krs-class] k5: {} entry points in {:.1} s; one diagnostic under krs check {}, one error under cargo check {}; red {} (by finding {:?}; by step {:?})",
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

/// A machine of one computation cell for K7's bound, with `extra` declarations after it.
fn bound_source(commands: &str, initial: &str, extra: &str) -> String {
    format!(
        "use k::builtin::{{Int, KSequence}};\nuse k::{{KItem, KResult, Term}};\n\nk::sorts! {{\n    Stmt;\n}}\n\n#[k::constructors(sort = Stmt, result = KResult)]\n#[rustfmt::skip]\npub enum Cmd {{\n    #[k::syntax(\"go\")] Go(),\n    #[k::syntax(\"hold({{a}})\")] Hold {{ a: KItem }},\n{commands}}}\n\n#[k::configuration]\npub struct Machine {{\n    #[k::cell]\n    pub k: KSequence,\n}}\n\nimpl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {{\n        Self {{ k: k::k![{initial}] }}\n    }}\n}}\n{extra}"
    )
}

/// K7's bound: a program whose expansion does not end, a desugar that rewrites its own
/// application into a larger one, and an initial configuration whose evaluation does not end, a
/// function that calls itself on a larger argument, each give a deviation within the run's time
/// limit, not a hung worker: the program's parse and expansion and its run are one request,
/// cancelled at the limit.
#[test]
#[ignore = "builds two packages and compiles them natively; run it with the class tier's environment"]
fn k7_bounds_a_program_whose_expansion_or_run_does_not_end() {
    use krs_test_support::class_matrix::k7::{Run, Status};
    let limit = std::time::Duration::from_secs(5);
    let scratch = tempfile::tempdir().expect("the scratch directory is created");
    let settings = Settings {
        workers: 1,
        batch: 1,
        scratch: scratch.path().to_path_buf(),
        closure: false,
        native: NativeMode::Batched,
        refused_by_table: BTreeSet::new(),
        run: Some(limit),
    };
    let spin = bound_source(
        "    #[k::syntax(\"spin({a})\")] #[k::desugar] Spin { a: KItem },\n",
        "pgm",
        "\n#[k::desugar]\nfn spin(k::term![Cmd::Spin(x)]: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Spin(Cmd::Hold(x))\n}\n",
    );
    let count = bound_source(
        "",
        "pgm, Count(0)",
        "\n#[k::function(partial, syntax = \"count({a})\")]\npub fn Count(a: Term<Int>) -> Term<Int> {\n    Count(a + 1)\n}\n",
    );
    for (name, source, program) in [("spin", spin, "spin(go)"), ("count", count, "go")] {
        let collected = pipeline::collect_source(&settings, name, &source)
            .unwrap_or_else(|error| panic!("{name} collects: {error}"));
        let plan = Run {
            program: program.to_owned(),
            variables: Vec::new(),
            depth: 0,
            steps: 0,
            cells: Vec::new(),
            status: Status::Liveness,
        };
        let ran = Mutex::new(None);
        let visit = |semantics: &mut krs_exec::Semantics| {
            let started = std::time::Instant::now();
            let verdict = runs::run_case(semantics, &plan, limit);
            *ran.lock().expect("not poisoned") = Some((verdict, started.elapsed()));
        };
        let checked = collected.check_visiting(collected.bundle.clone(), Some(&visit));
        let (verdict, elapsed) = ran
            .into_inner()
            .expect("not poisoned")
            .unwrap_or_else(|| panic!("{name}: no run ({checked:?})"));
        eprintln!(
            "[krs-class] K7 bound, {name}: {} in {elapsed:?}",
            verdict.signature()
        );
        assert!(
            matches!(verdict, Ran::Deviates(_)),
            "{name}: {}",
            verdict.signature()
        );
        assert!(
            elapsed < limit * 2,
            "{name}: the run took {elapsed:?}, past its limit of {limit:?}"
        );
    }
}

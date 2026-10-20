//! Re-pin L1-3: `kink-flow run --compile-workers N` changes nothing but wall time. Each list runs
//! cold, then warm, in private copies of its fixture, with 1 (the sequential path) and with more
//! compile workers; every run document must be equal once the wall times are removed, and the
//! outcome cache (`outcomes/`), the killer hints and the stored report must be byte-equal. With 2
//! workers a chunk holds 8 mutations, so `collstore`'s 9 span two chunks.

use kink_flow::{
    FlowManifest, MutationList,
    results::CACHE_DIRECTORY,
    search::{ProgramOrder, RunOptions, run},
};
use serde_json::Value;
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if name == CACHE_DIRECTORY {
            continue;
        }
        if entry.file_type().unwrap().is_dir() {
            copy_dir(&entry.path(), &to.join(&name));
        } else {
            fs::copy(entry.path(), to.join(&name)).unwrap();
        }
    }
}

/// A private copy of the testdata/flow fixture `name` for `workers`.
fn fixture(name: &str, list: &str, workers: usize) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-compile-workers-{}", std::process::id()))
        .join(format!("{}-{list}-{workers}", name.replace('/', "_")));
    let _ = fs::remove_dir_all(&dir);
    copy_dir(
        &Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../testdata/flow")
            .join(name),
        &dir,
    );
    dir
}

/// The document without its wall times (`call_wall_ms`, `wall_ms`, `baseline_ms`: the session's
/// timings, flow F-13), which are the only fields that differ between equal runs.
fn timeless(value: &Value) -> Value {
    match value {
        Value::Object(map) => Value::Object(
            map.iter()
                .filter(|(key, _)| {
                    !matches!(key.as_str(), "call_wall_ms" | "wall_ms" | "baseline_ms")
                })
                .map(|(key, value)| (key.clone(), timeless(value)))
                .collect(),
        ),
        Value::Array(items) => Value::Array(items.iter().map(timeless).collect()),
        other => other.clone(),
    }
}

/// Every file of the cache directory's outcome store and hints, by relative path, with its
/// bytes.
fn stores(cache: &Path) -> BTreeMap<PathBuf, Vec<u8>> {
    fn walk(root: &Path, dir: &Path, files: &mut BTreeMap<PathBuf, Vec<u8>>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                walk(root, &path, files);
            } else {
                files.insert(
                    path.strip_prefix(root).unwrap().to_owned(),
                    fs::read(&path).unwrap(),
                );
            }
        }
    }
    let mut files = BTreeMap::new();
    walk(cache, &cache.join("outcomes"), &mut files);
    if let Ok(bytes) = fs::read(cache.join("hints.json")) {
        files.insert(PathBuf::from("hints.json"), bytes);
    }
    files
}

fn search(dir: &Path, list: &str, workers: usize) -> (Value, bool) {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let mutations = MutationList::read(&dir.join(list)).unwrap();
    run(
        &manifest,
        &mutations,
        &RunOptions {
            only: Vec::new(),
            cache: None,
            order: ProgramOrder::Corpus,
            compile_workers: Some(workers),
            memo: kink_flow::memo::MemoUse::On,
        },
    )
}

/// The statuses of a run document, for the failure message and the minimum below.
fn statuses(document: &Value) -> Vec<String> {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| format!("{}={}", row["id"], row["status"]))
        .collect()
}

fn compare(name: &str, list: &str, workers: &[usize]) -> Vec<String> {
    let dirs = workers
        .iter()
        .map(|&w| fixture(name, list, w))
        .collect::<Vec<_>>();
    let mut cold_statuses = Vec::new();
    for round in ["cold", "warm"] {
        let runs = dirs
            .iter()
            .zip(workers)
            .map(|(dir, &w)| search(dir, list, w))
            .collect::<Vec<_>>();
        let (reference, ok) = &runs[0];
        if round == "cold" {
            cold_statuses = statuses(reference);
        }
        let cache = dirs[0].join(CACHE_DIRECTORY);
        let report = fs::read(cache.join("report.json")).unwrap();
        for ((document, again_ok), (dir, w)) in runs.iter().zip(dirs.iter().zip(workers)).skip(1) {
            assert_eq!(again_ok, ok, "{name} {list} {round}: {w} workers");
            assert_eq!(
                timeless(document),
                timeless(reference),
                "STOP: {name} {list} {round}: {w} compile workers changed the run document"
            );
            let again = dir.join(CACHE_DIRECTORY);
            assert_eq!(
                stores(&again),
                stores(&cache),
                "STOP: {name} {list} {round}: {w} compile workers changed the stores"
            );
            assert_eq!(
                timeless(
                    &serde_json::from_slice::<Value>(&fs::read(again.join("report.json")).unwrap())
                        .unwrap()
                ),
                timeless(&serde_json::from_slice::<Value>(&report).unwrap()),
                "STOP: {name} {list} {round}: the stored report"
            );
        }
        eprintln!(
            "L13_FLOW_WORKERS {name} {list} {round} statuses={:?}",
            statuses(reference)
        );
    }
    cold_statuses
}

fn warn_if_one_worker() {
    if std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get) < 2 {
        // Review L1-3-1 D3: the workers are capped at the host's parallelism.
        eprintln!(
            "this host allows one compile worker: every worker count runs the sequential path, \
             so the comparison is vacuous here"
        );
    }
}

/// One test per fixture list (test-gate TG-F, formerly `compile_workers_change_no_row_record_or_hint`):
/// calc's status list, which holds every status class the former test required of the two lists
/// together, in the kink tier, and collstore, whose 9 mutations span two chunks of 2 workers, in
/// the heavy tier.
mod kink_tier {
    use super::*;

    #[test]
    #[ignore = "kink"]
    fn compile_workers_change_no_row_record_or_hint_on_calc() {
        warn_if_one_worker();
        let calc = compare("calc", "MUTATIONS-statuses.toml", &[1, 4]);
        assert_eq!(calc.len(), 6);
        // Several statuses, a refusal before any test among them.
        assert!(calc.iter().any(|s| s.ends_with("=\"killed\"")));
        assert!(calc.iter().any(|s| s.ends_with("=\"survived\"")));
        assert!(
            calc.iter()
                .any(|s| s.ends_with("=\"invalid\"") || s.ends_with("=\"equivalent\"")),
            "{calc:?}"
        );
    }
}

mod heavy {
    use super::*;

    #[test]
    #[ignore = "heavy"]
    fn compile_workers_change_no_row_record_or_hint_on_collstore() {
        warn_if_one_worker();
        let collstore = compare("collections/collstore", "MUTATIONS.toml", &[1, 2, 4]);
        assert_eq!(collstore.len(), 9);
    }
}

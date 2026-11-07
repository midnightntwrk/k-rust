//! `kink-flow run --full` (CF-23): every comparable program on every selected mutation, in corpus
//! order, under kink-campaign's `ScheduleMode::Full`; each row's `killed_by` and the document's
//! kill `matrix`; one outcome store for both schedules.
//!
//! Every first-kill run here is in corpus order (`ProgramOrder::Corpus`), so that its killers do
//! not depend on host timing. Statuses are always compared with a first-kill or a cold run of the
//! same files: the full schedule may change which cells run, never a status.

mod flow_support;

use flow_support::{copy_all, copy_dir, flow};
use kink_campaign::ScheduleMode;
use kink_corpus::load_source;
use kink_flow::{
    FlowManifest, MutationList,
    admit::corpus_source,
    cli::{CommandFiles, EXIT_UNASKED, EXIT_YES, FlowCommand, OutputFormat},
    digest::hint_key,
    hints::{HINTS_SCHEMA, hints_path},
    memo::MemoUse,
    outcomes::{OUTCOMES_DIRECTORY, record_sha256},
    resolve,
    results::CACHE_DIRECTORY,
    search::{ProgramOrder, RunMode, RunOptions, run_with},
    verdicts::verdicts,
};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

/// A fresh directory for one test, under the target's temporary directory.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-full-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// A private copy of a testdata/flow fixture.
fn fixture(name: &str, test: &str) -> PathBuf {
    let dir = scratch(test).join(name);
    copy_dir(&flow(name), &dir);
    dir
}

/// `kink-flow run` through the library under `schedule` (first-kill in corpus order).
fn run_as(
    manifest: &Path,
    mutations: &Path,
    only: &[&str],
    schedule: ScheduleMode,
    mode: RunMode,
    memo: MemoUse,
) -> (Value, bool) {
    let manifest = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    run_with(
        &manifest,
        &list,
        &RunOptions {
            only: only.iter().map(|id| (*id).to_owned()).collect(),
            order: ProgramOrder::Corpus,
            compile_workers: Some(1),
            memo,
            schedule,
            ..RunOptions::default()
        },
        mode,
    )
}

fn full(manifest: &Path, mutations: &Path) -> Value {
    let (document, ok) = run_as(
        manifest,
        mutations,
        &[],
        ScheduleMode::Full,
        RunMode::Search,
        MemoUse::On,
    );
    assert!(ok, "{document:#}");
    document
}

fn first_kill(manifest: &Path, mutations: &Path) -> Value {
    let (document, ok) = run_as(
        manifest,
        mutations,
        &[],
        ScheduleMode::FirstKill,
        RunMode::Search,
        MemoUse::On,
    );
    assert!(ok, "{document:#}");
    document
}

fn rows(document: &Value) -> &Vec<Value> {
    document["mutations"].as_array().unwrap()
}

fn mutation<'d>(document: &'d Value, id: &str) -> &'d Value {
    rows(document)
        .iter()
        .find(|m| m["id"] == id)
        .unwrap_or_else(|| panic!("no mutation {id}"))
}

/// `(id, status)` of every row.
fn statuses(document: &Value) -> Vec<(String, String)> {
    rows(document)
        .iter()
        .map(|m| {
            (
                m["id"].as_str().unwrap().to_owned(),
                m["status"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

/// `(id, killed_by)` of every row.
fn killed_by(document: &Value) -> Vec<(String, Value)> {
    rows(document)
        .iter()
        .map(|m| (m["id"].as_str().unwrap().to_owned(), m["killed_by"].clone()))
        .collect()
}

/// The programs of each campaign call of a mutation.
fn calls(document: &Value, id: &str) -> Vec<Vec<String>> {
    mutation(document, id)["calls"]
        .as_array()
        .unwrap()
        .iter()
        .map(|call| {
            call["programs"]
                .as_array()
                .unwrap()
                .iter()
                .map(|p| p.as_str().unwrap().to_owned())
                .collect()
        })
        .collect()
}

/// `(program, outcome)` of every executed entry of a mutation, in the row's order.
fn executed(document: &Value, id: &str) -> Vec<(String, String)> {
    mutation(document, id)["executed"]
        .as_array()
        .unwrap()
        .iter()
        .map(|e| {
            (
                e["program"].as_str().unwrap().to_owned(),
                e["outcome"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

fn strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|s| (*s).to_owned()).collect()
}

fn cache_of(manifest: &Path) -> PathBuf {
    manifest.parent().unwrap().join(CACHE_DIRECTORY)
}

/// The document without its wall times (`call_wall_ms`, `wall_ms`, `baseline_ms`), the only
/// fields that differ between equal runs.
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

/// Every file of the outcome store, by relative path, as JSON without the records'
/// `allowance_bytes` (the writing process's memory allowance, for diagnosis only: in neither the
/// key nor the record digest).
fn outcome_store(manifest: &Path) -> BTreeMap<PathBuf, Value> {
    fn walk(root: &Path, dir: &Path, files: &mut BTreeMap<PathBuf, Value>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                walk(root, &path, files);
            } else {
                let mut file: Value =
                    serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
                if let Some(records) = file["records"].as_object_mut() {
                    for record in records.values_mut() {
                        record.as_object_mut().unwrap().remove("allowance_bytes");
                    }
                }
                files.insert(path.strip_prefix(root).unwrap().to_owned(), file);
            }
        }
    }
    let root = cache_of(manifest).join(OUTCOMES_DIRECTORY);
    let mut files = BTreeMap::new();
    walk(&root, &root, &mut files);
    files
}

/// Every file of the outcome store and the hints, by relative path, with its bytes.
fn store_bytes(manifest: &Path) -> BTreeMap<PathBuf, Vec<u8>> {
    let cache = cache_of(manifest);
    let mut files = BTreeMap::new();
    let mut stack = vec![cache.join(OUTCOMES_DIRECTORY)];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else {
                files.insert(
                    path.strip_prefix(&cache).unwrap().to_owned(),
                    fs::read(&path).unwrap(),
                );
            }
        }
    }
    if let Ok(bytes) = fs::read(cache.join("hints.json")) {
        files.insert(PathBuf::from("hints.json"), bytes);
    }
    files
}

fn program_digest(document: &Value, id: &str) -> String {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["id"] == id)
        .unwrap()["digest"]
        .as_str()
        .unwrap()
        .to_owned()
}

/// The outcome file of mutation `id` in the context of `document`.
fn outcome_file(manifest: &Path, document: &Value, id: &str) -> PathBuf {
    cache_of(manifest)
        .join(OUTCOMES_DIRECTORY)
        .join(
            document["outcome_cache"]["context_sha256"]
                .as_str()
                .unwrap(),
        )
        .join(format!(
            "{}.json",
            mutation(document, id)["identity"].as_str().unwrap()
        ))
}

fn read_json(path: &Path) -> Value {
    serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap()
}

fn write_json(path: &Path, value: &Value) {
    fs::write(path, serde_json::to_string_pretty(value).unwrap()).unwrap();
}

/// The program ids of the records of mutation `id`'s outcome file.
fn recorded(manifest: &Path, document: &Value, id: &str) -> Vec<String> {
    let path = outcome_file(manifest, document, id);
    if !path.exists() {
        return Vec::new();
    }
    read_json(&path)["records"]
        .as_object()
        .unwrap()
        .values()
        .map(|record| record["program_id"].as_str().unwrap().to_owned())
        .collect()
}

/// Rewrite program `program`'s record of mutation `id` with `change` and reseal it, as a cache
/// whose writer can forge a record would hold it.
fn forge_record(
    manifest: &Path,
    document: &Value,
    id: &str,
    program: &str,
    change: impl FnOnce(&mut Value),
) {
    let path = outcome_file(manifest, document, id);
    let mut file = read_json(&path);
    let digest = program_digest(document, program);
    let context = file["context_sha256"].as_str().unwrap().to_owned();
    let identity = file["mutation_identity"].as_str().unwrap().to_owned();
    let record = &mut file["records"][&digest];
    assert!(record.is_object(), "{id} has no record for {program}");
    change(record);
    let slots = record["slots"]
        .as_array()
        .unwrap()
        .iter()
        .map(|s| s.as_str().unwrap())
        .collect::<Vec<_>>();
    let sealed = record_sha256(
        &context,
        &identity,
        &digest,
        record["baseline_run_sha256"].as_str().unwrap(),
        record["outcome"].as_str().unwrap(),
        &slots,
        record["mutant_run_sha256"].as_str().unwrap(),
        &record["difference"],
        &kink_flow::outcomes::OutcomeRecord::report_value(record),
    );
    record["record_sha256"] = json!(sealed.to_string());
    write_json(&path, &file);
}

/// Remove program `program`'s record of mutation `id`.
fn delete_record(manifest: &Path, document: &Value, id: &str, program: &str) {
    let path = outcome_file(manifest, document, id);
    let mut file = read_json(&path);
    let digest = program_digest(document, program);
    assert!(
        file["records"]
            .as_object_mut()
            .unwrap()
            .remove(&digest)
            .is_some(),
        "{id} has no record for {program}"
    );
    write_json(&path, &file);
}

/// Write program `program`'s killed record of mutation `from` into mutation `to`'s outcome file
/// as `to`'s, resealed: what a cache would hold if an earlier command had seen `program` kill
/// `to`'s mutant (the rest of `to`'s file, if it has one, is replaced).
fn forge_kill(manifest: &Path, document: &Value, from: &str, to: &str, program: &str) {
    let mut file = read_json(&outcome_file(manifest, document, from));
    let context = file["context_sha256"].as_str().unwrap().to_owned();
    let identity = mutation(document, to)["identity"]
        .as_str()
        .unwrap()
        .to_owned();
    let digest = program_digest(document, program);
    let mut record = file["records"][&digest].clone();
    assert_eq!(
        record["outcome"], "killed",
        "{from} on {program}: {record:#}"
    );
    let slots = record["slots"]
        .as_array()
        .unwrap()
        .iter()
        .map(|s| s.as_str().unwrap().to_owned())
        .collect::<Vec<_>>();
    let slots = slots.iter().map(String::as_str).collect::<Vec<_>>();
    let sealed = record_sha256(
        &context,
        &identity,
        &digest,
        record["baseline_run_sha256"].as_str().unwrap(),
        "killed",
        &slots,
        record["mutant_run_sha256"].as_str().unwrap(),
        &record["difference"],
        &kink_flow::outcomes::OutcomeRecord::report_value(&record),
    );
    record["record_sha256"] = json!(sealed.to_string());
    file["mutation_identity"] = json!(identity);
    file["mutation_id"] = json!(to);
    let mut records = serde_json::Map::new();
    records.insert(digest, record);
    file["records"] = Value::Object(records);
    let path = outcome_file(manifest, document, to);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    write_json(&path, &file);
}

/// The hint key of mutation `id` of `mutations` under `manifest`.
fn hint_key_of(manifest: &Path, mutations: &Path, id: &str) -> String {
    let flow = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    let loaded = load_source(&corpus_source(&flow)).unwrap();
    let mutation = list.mutations.iter().find(|m| m.id == id).unwrap();
    let resolved = resolve(&flow, &loaded, mutation).unwrap();
    hint_key(mutation, &resolved).to_string()
}

/// The hints file as mutation id -> hinted program id.
fn hints(manifest: &Path) -> BTreeMap<String, String> {
    let value = read_json(&hints_path(&cache_of(manifest)));
    assert_eq!(value["schema"], HINTS_SCHEMA);
    value["hints"]
        .as_object()
        .unwrap()
        .values()
        .map(|entry| {
            (
                entry["mutation_id"].as_str().unwrap().to_owned(),
                entry["program_id"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

/// Set the hint of mutation `id` to program `program` of `document`.
fn set_hint(manifest: &Path, mutations: &Path, document: &Value, id: &str, program: &str) {
    let key = hint_key_of(manifest, mutations, id);
    let path = hints_path(&cache_of(manifest));
    let mut value = read_json(&path);
    value["hints"][key] = json!({
        "mutation_id": id,
        "program_id": program,
        "program_digest": program_digest(document, program),
    });
    write_json(&path, &value);
}

/// The hint a full run leaves for each killed row: the first of its `killed_by`.
fn first_killers(document: &Value) -> BTreeMap<String, String> {
    rows(document)
        .iter()
        .filter(|row| row["status"] == "killed")
        .map(|row| {
            (
                row["id"].as_str().unwrap().to_owned(),
                row["killed_by"][0].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

/// A manifest of `programs` (ids of the fixture's `FLOW.toml`, in that order), written beside it
/// as `name`, so that it shares the fixture's cache.
fn subset_manifest(dir: &Path, name: &str, programs: &[&str]) -> PathBuf {
    let text = fs::read_to_string(dir.join("FLOW.toml")).unwrap();
    let mut blocks = text.split("[[program]]");
    let mut out = blocks.next().unwrap().to_owned();
    let blocks = blocks
        .map(|block| {
            let id = block
                .lines()
                .find_map(|line| line.trim().strip_prefix("id = "))
                .unwrap()
                .trim_matches('"')
                .to_owned();
            (id, block.to_owned())
        })
        .collect::<BTreeMap<_, _>>();
    for program in programs {
        out.push_str("[[program]]");
        out.push_str(&blocks[*program]);
    }
    let path = dir.join(name);
    fs::write(&path, out).unwrap();
    path
}

/// The full matrix of calc's `MUTATIONS.toml` (killers in corpus order: add, nested, sub, inline).
fn calc_killed_by() -> Vec<(String, Value)> {
    [
        // 1 + 2, (1 + 2) * 3 and 2 * 3 + 1 each add.
        ("add-becomes-sub", json!(["add", "nested", "inline"])),
        // Only sub subtracts.
        ("sub-off-by-one", json!(["sub"])),
        // (1 + 2) * 3 and 2 * 3 multiply.
        ("mul-becomes-add", json!(["nested", "inline"])),
        ("no-mul", json!(["nested", "inline"])),
        // I2 +Int I1 equals I1 +Int I2 on every input.
        ("add-swaps-operands", json!([])),
    ]
    .into_iter()
    .map(|(id, killers)| (id.to_owned(), killers))
    .collect()
}

fn calc_statuses() -> Vec<(String, String)> {
    [
        ("add-becomes-sub", "killed"),
        ("sub-off-by-one", "killed"),
        ("mul-becomes-add", "killed"),
        ("no-mul", "killed"),
        ("add-swaps-operands", "survived"),
    ]
    .into_iter()
    .map(|(id, status)| (id.to_owned(), status.to_owned()))
    .collect()
}

/// The parser: `--full` once, never with `--order`.
#[test]
fn the_full_flag_parses() {
    let files = || CommandFiles {
        mutations: Some(flow("calc").join("MUTATIONS.toml")),
        ..CommandFiles::default()
    };
    let parse = |args: &[&str]| {
        FlowCommand::parse(
            "run",
            files(),
            &args.iter().map(|a| (*a).to_owned()).collect::<Vec<_>>(),
        )
    };
    let FlowCommand::Run { options, .. } = parse(&["--full"]).unwrap() else {
        panic!("run");
    };
    assert_eq!(options.schedule, ScheduleMode::Full);
    let FlowCommand::Run { options, .. } = parse(&[]).unwrap() else {
        panic!("run");
    };
    assert_eq!(options.schedule, ScheduleMode::FirstKill);
    let FlowCommand::Run { options, mode, .. } =
        parse(&["--full", "--verify", "--output", "verdicts"]).unwrap()
    else {
        panic!("run");
    };
    assert_eq!(
        (options.schedule, mode),
        (ScheduleMode::Full, RunMode::Verify)
    );
    assert!(matches!(
        parse(&["--full", "--output", "verdicts"]).unwrap().output(),
        OutputFormat::Verdicts
    ));
    assert_eq!(
        parse(&["--full", "--full"]).unwrap_err(),
        "unexpected argument \"--full\""
    );
    for args in [
        ["--full", "--order", "corpus"],
        ["--order", "cost", "--full"],
    ] {
        assert_eq!(
            parse(&args).unwrap_err(),
            "--order orders the first-kill search; --full runs every program in corpus order"
        );
    }
}

/// A run document that refuses its input names the run's schedule and a null matrix, whichever
/// input was refused: a manifest that does not decode, or a mutation list that does not decode.
#[test]
fn a_refused_run_document_names_its_schedule() {
    let binary = env!("CARGO_BIN_EXE_kink-flow");
    let dir = fixture("calc", "refused");
    let bad_flow = dir.join("BAD-FLOW.toml");
    fs::write(&bad_flow, "[spec]\nentry = 3\n").unwrap();
    let bad_list = dir.join("BAD-MUTATIONS.toml");
    fs::write(&bad_list, "this is not TOML [").unwrap();
    let profile = kink_native::execution::SolverProfile::BUILD.name();
    for (manifest, mutations, section) in [
        (&bad_flow, dir.join("MUTATIONS.toml"), "spec"),
        (&dir.join("FLOW.toml"), bad_list.clone(), "mutation_list"),
    ] {
        for (args, schedule) in [(&[][..], "first-kill"), (&["--full"][..], "full")] {
            let run = |output: &[&str]| {
                Command::new(binary)
                    .arg("run")
                    .arg(manifest)
                    .arg(&mutations)
                    .args(args)
                    .args(output)
                    .output()
                    .unwrap()
            };
            let output = run(&[]);
            assert_eq!(output.status.code(), Some(i32::from(EXIT_UNASKED)));
            let document: Value = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(document["schema"], "kink-flow-run");
            assert_eq!(document[section]["outcome"], "refused", "{document:#}");
            assert_eq!(document["schedule"], schedule, "{section}: {document:#}");
            assert_eq!(
                document.get("matrix"),
                Some(&Value::Null),
                "{section}: {document:#}"
            );
            let output = run(&["--output", "verdicts"]);
            assert_eq!(output.status.code(), Some(i32::from(EXIT_UNASKED)));
            let printed = String::from_utf8(output.stdout).unwrap();
            assert!(
                printed.starts_with(&format!(
                    "schema = \"kink-flow-verdicts\"\nversion = 5\ndocument = \"run\"\n\
                     schedule = \"{schedule}\"\nprofile = \"{profile}\"\n\n[{section}]\n\
                     outcome = \"refused\"\n"
                )),
                "{printed}"
            );
        }
    }
}

/// `--progress` (once) reports a run on stderr: a line before the baseline results naming how many
/// mutations and programs the run has, a line as each program's baseline row is decided, with its
/// place, its id and its class, one before the list is resolved, then a line as each mutation's
/// row is decided, with its place, its id and its status, in list order. stdout stays the document, whose rows are those
/// of the same run without the flag; without it (and with stderr no terminal) stderr is empty.
#[test]
fn a_run_reports_its_progress_on_stderr() {
    let binary = env!("CARGO_BIN_EXE_kink-flow");
    let run = |test: &str, progress: bool| {
        let dir = fixture("calc", test);
        let mut command = Command::new(binary);
        command
            .arg("run")
            .arg(dir.join("FLOW.toml"))
            .arg(dir.join("MUTATIONS.toml"))
            .arg("--full");
        if progress {
            command.arg("--progress");
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(i32::from(EXIT_YES)),
            "{output:?}"
        );
        let document: Value = serde_json::from_slice(&output.stdout).unwrap();
        (document, String::from_utf8(output.stderr).unwrap())
    };
    let (document, stderr) = run("progress", true);
    let rows = document["mutations"].as_array().unwrap();
    let programs = document["programs"].as_array().unwrap();
    let plural =
        |count: usize, noun: &str| format!("{count} {noun}{}", if count == 1 { "" } else { "s" });
    let mut expected = vec![format!(
        "kink-flow: run: {} on {}, after the baseline results",
        plural(rows.len(), "mutation"),
        plural(programs.len(), "program")
    )];
    // The cold run stores no record before it runs a program: no line says `stored`.
    for (index, program) in programs.iter().enumerate() {
        assert_eq!(program["cached"], false, "{program:#}");
        expected.push(format!(
            "kink-flow: run: baseline of program {} of {}, `{}`: {}",
            index + 1,
            programs.len(),
            program["id"].as_str().unwrap(),
            program["class"].as_str().unwrap()
        ));
    }
    expected.push(format!(
        "kink-flow: run: resolving the list's {}",
        plural(rows.len(), "mutation")
    ));
    for (index, row) in rows.iter().enumerate() {
        expected.push(format!(
            "kink-flow: run: mutation {} of {}, `{}`: {}",
            index + 1,
            rows.len(),
            row["id"].as_str().unwrap(),
            row["status"].as_str().unwrap()
        ));
    }
    assert_eq!(stderr.lines().collect::<Vec<_>>(), expected, "{stderr}");
    let (quiet, stderr) = run("progress-quiet", false);
    assert_eq!(stderr, "");
    // The same cold run of another copy of the fixture gives the same rows.
    let verdicts = |document: &Value| {
        document["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| {
                (
                    row["id"].clone(),
                    row["status"].clone(),
                    row["killed_by"].clone(),
                )
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(verdicts(&quiet), verdicts(&document));

    let files = || CommandFiles {
        mutations: Some(flow("calc").join("MUTATIONS.toml")),
        ..CommandFiles::default()
    };
    let parse = |args: &[&str]| {
        FlowCommand::parse(
            "run",
            files(),
            &args.iter().map(|a| (*a).to_owned()).collect::<Vec<_>>(),
        )
    };
    assert!(matches!(
        parse(&["--progress"]).unwrap(),
        FlowCommand::Run { progress: true, .. }
    ));
    assert!(matches!(
        parse(&[]).unwrap(),
        FlowCommand::Run {
            progress: false,
            ..
        }
    ));
    assert_eq!(
        parse(&["--progress", "--progress"]).unwrap_err(),
        "unexpected argument \"--progress\""
    );
}

/// The matrix of two rows, from rows alone (`report::matrix`).
#[test]
fn the_matrix_is_read_from_the_rows() {
    let programs = [
        json!({"id": "a", "class": "comparable"}),
        json!({"id": "x", "class": "refused"}),
        json!({"id": "b", "class": "comparable"}),
    ];
    let mutations = [
        json!({"id": "m1", "killed_by": ["a", "b"], "executed": [
            {"program": "a", "outcome": "distinguish"}, {"program": "b", "outcome": "distinguish"}]}),
        json!({"id": "m2", "killed_by": ["b"], "executed": [
            {"program": "a", "outcome": "unknown"}, {"program": "b", "outcome": "distinguish"}]}),
        json!({"id": "m3", "killed_by": [], "executed": [
            {"program": "a", "outcome": "agree"}, {"program": "b", "outcome": "timeout"}]}),
        json!({"id": "m4", "killed_by": null, "executed": []}),
    ];
    assert_eq!(
        kink_flow::report::matrix(&programs, &mutations),
        json!({"programs": [
            {"id": "a", "kills": ["m1"], "sole_killer_of": [], "undecided": ["m2"]},
            {"id": "b", "kills": ["m1", "m2"], "sole_killer_of": ["m2"], "undecided": ["m3"]},
        ]})
    );
}

mod kink_tier {
    use super::*;

    /// "A flag runs every program on every mutant and reports the matrix."
    #[test]
    #[ignore = "kink"]
    fn full_runs_every_program_on_every_mutant() {
        let dir = fixture("calc", "every-program");
        let manifest = dir.join("FLOW.toml");
        let document = full(&manifest, &dir.join("MUTATIONS.toml"));
        assert_eq!(document["schedule"], "full");
        assert_eq!(document["order"], "corpus");
        assert_eq!(statuses(&document), calc_statuses());
        assert_eq!(killed_by(&document), calc_killed_by());
        for row in rows(&document) {
            let id = row["id"].as_str().unwrap();
            assert_eq!(
                executed(&document, id)
                    .into_iter()
                    .map(|(program, _)| program)
                    .collect::<Vec<_>>(),
                strings(&["add", "nested", "sub", "inline"]),
                "{id}"
            );
            assert_eq!(
                calls(&document, id),
                vec![strings(&["add", "nested", "sub", "inline"])],
                "{id}"
            );
            // The killer is the first of `killed_by`, found by the call.
            assert_eq!(
                row["killer"],
                row["killed_by"].get(0).cloned().unwrap_or(Value::Null)
            );
            if row["status"] == "killed" {
                assert_eq!(row["killer_source"], "search", "{id}");
                // Every distinguishing cell carries its kill evidence; only the killer's shows
                // the mutant's KORE.
                for entry in row["executed"].as_array().unwrap() {
                    let killer = entry["program"] == row["killer"];
                    let distinguishes = entry["outcome"] == "distinguish";
                    assert_eq!(!entry["difference"].is_null(), distinguishes, "{entry:#}");
                    let kore = &entry["slots"]["whole-term"]["sides"]["mutant"]["kore"];
                    assert_eq!(!kore.is_null(), killer, "{id}: {entry:#}");
                }
            }
        }
        assert_eq!(
            document["matrix"],
            json!({"programs": [
                {"id": "add", "kills": ["add-becomes-sub"], "sole_killer_of": [], "undecided": []},
                {"id": "nested", "kills": ["add-becomes-sub", "mul-becomes-add", "no-mul"],
                 "sole_killer_of": [], "undecided": []},
                {"id": "sub", "kills": ["sub-off-by-one"], "sole_killer_of": ["sub-off-by-one"],
                 "undecided": []},
                {"id": "inline", "kills": ["add-becomes-sub", "mul-becomes-add", "no-mul"],
                 "sole_killer_of": [], "undecided": []},
            ]})
        );
        // A first-kill run names no `killed_by` and no matrix.
        let other = fixture("calc", "every-program-first-kill");
        let first = first_kill(&other.join("FLOW.toml"), &other.join("MUTATIONS.toml"));
        assert_eq!(first["schedule"], "first-kill");
        assert!(first["matrix"].is_null());
        assert!(rows(&first).iter().all(|row| row["killed_by"].is_null()));
        assert_eq!(statuses(&first), statuses(&document));
    }

    /// The status of a full row is the first-kill row's (search.rs module documentation): on
    /// calc's two lists (every status class among them), register's, divide's and loop's, whose
    /// countdown is `unknown` on its mutant under a small depth bound (an undecided cell).
    #[test]
    #[ignore = "kink"]
    fn full_status_equals_first_kill_status() {
        for (name, manifest, mutations) in [
            ("calc", "FLOW.toml", "MUTATIONS.toml"),
            ("calc", "FLOW.toml", "MUTATIONS-statuses.toml"),
            ("register", "FLOW.toml", "MUTATIONS.toml"),
            ("divide", "FLOW.toml", "MUTATIONS.toml"),
            ("loop", "FLOW-depth.toml", "MUTATIONS.toml"),
        ] {
            let a = fixture(name, &format!("status-{name}-{mutations}-first"));
            let b = fixture(name, &format!("status-{name}-{mutations}-full"));
            let (first, _) = run_as(
                &a.join(manifest),
                &a.join(mutations),
                &[],
                ScheduleMode::FirstKill,
                RunMode::Search,
                MemoUse::On,
            );
            let (all, _) = run_as(
                &b.join(manifest),
                &b.join(mutations),
                &[],
                ScheduleMode::Full,
                RunMode::Search,
                MemoUse::On,
            );
            assert_eq!(
                statuses(&all),
                statuses(&first),
                "STOP: {name} {mutations}: --full moved a status"
            );
            for (row, first_row) in rows(&all).iter().zip(rows(&first)) {
                if row["status"] == "killed" {
                    // The first-kill killer is one of the killers.
                    let killers = row["killed_by"].as_array().unwrap();
                    assert!(killers.contains(&first_row["killer"]), "{name}: {row:#}");
                }
            }
            if name == "loop" {
                assert_eq!(
                    all["matrix"]["programs"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|p| (p["id"].clone(), p["undecided"].clone()))
                        .collect::<Vec<_>>(),
                    vec![
                        (json!("countdown"), json!(["countdown-escapes"])),
                        (json!("twice"), json!([])),
                    ],
                    "{:#}",
                    all["matrix"]
                );
            }
        }
    }

    /// "Outcomes it proves are cached as usual": a warm full run is decided by tier 1, a later
    /// first-kill run too, and the memos change nothing.
    #[test]
    #[ignore = "kink"]
    fn full_outcomes_are_cached_as_usual() {
        let dir = fixture("calc", "cached");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let cold = full(&manifest, &mutations);
        // Every cell of calc is a kill or an agreement: 5 mutations, 4 programs.
        assert_eq!(cold["outcome_cache"]["records_written"], 20);
        let warm = full(&manifest, &mutations);
        assert_eq!(warm["outcome_cache"]["mutations_from_cache"], 5);
        assert_eq!(warm["outcome_cache"]["programs_from_cache"], 20);
        assert_eq!(warm["outcome_cache"]["records_written"], 0);
        assert_eq!(statuses(&warm), statuses(&cold));
        assert_eq!(killed_by(&warm), killed_by(&cold));
        assert_eq!(warm["matrix"], cold["matrix"]);
        for row in rows(&warm) {
            let id = row["id"].as_str().unwrap();
            assert!(calls(&warm, id).is_empty(), "{id}");
            assert_eq!(executed(&warm, id), executed(&cold, id), "{id}");
            assert!(
                row["executed"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|e| e["cached"] == true),
                "{id}"
            );
            assert_eq!(row["killer"], mutation(&cold, id)["killer"]);
            if row["status"] == "killed" {
                assert_eq!(row["killer_source"], "outcome-cache", "{id}");
                assert_eq!(row["killer_from_cache"], true, "{id}");
            }
        }
        // The hints are the first-kill rule's: each killed row's killer, the first of its
        // `killed_by` (`full_hints_follow_killed_by` pins the rule).
        assert_eq!(hints(&manifest), first_killers(&warm));
        // A first-kill run after it is decided by tier 1 for every mutation, with no call.
        let first = first_kill(&manifest, &mutations);
        assert_eq!(first["outcome_cache"]["mutations_from_cache"], 5);
        assert_eq!(statuses(&first), calc_statuses());
        for row in rows(&first) {
            let id = row["id"].as_str().unwrap();
            assert!(calls(&first, id).is_empty(), "{id}");
        }
        // The memos change nothing.
        let (without, ok) = run_as(
            &manifest,
            &mutations,
            &[],
            ScheduleMode::Full,
            RunMode::Search,
            MemoUse::Off,
        );
        assert!(ok);
        let with = full(&manifest, &mutations);
        assert_eq!(timeless(&without), timeless(&with));
    }

    /// One store serves both schedules: a full run after a first-kill run calls, per mutation,
    /// exactly the programs with no record, and leaves the store a cold full run leaves.
    #[test]
    #[ignore = "kink"]
    fn first_kill_records_serve_a_full_run() {
        let dir = fixture("calc", "first-then-full");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let first = first_kill(&manifest, &mutations);
        let before = rows(&first)
            .iter()
            .map(|row| {
                let id = row["id"].as_str().unwrap();
                (id.to_owned(), recorded(&manifest, &first, id))
            })
            .collect::<BTreeMap<_, _>>();
        let after = full(&manifest, &mutations);
        for row in rows(&after) {
            let id = row["id"].as_str().unwrap();
            let missing = ["add", "nested", "sub", "inline"]
                .into_iter()
                .filter(|program| !before[id].iter().any(|p| p == program))
                .map(str::to_owned)
                .collect::<Vec<_>>();
            let expected = if missing.is_empty() {
                Vec::new()
            } else {
                vec![missing]
            };
            assert_eq!(calls(&after, id), expected, "{id}");
        }
        let cold_dir = fixture("calc", "first-then-full-cold");
        let cold_manifest = cold_dir.join("FLOW.toml");
        let cold = full(&cold_manifest, &cold_dir.join("MUTATIONS.toml"));
        assert_eq!(statuses(&after), statuses(&cold));
        assert_eq!(killed_by(&after), killed_by(&cold));
        assert_eq!(after["matrix"], cold["matrix"]);
        assert_eq!(outcome_store(&manifest), outcome_store(&cold_manifest));
    }

    /// Cached and live cells mix soundly: with any one record of a cold full run deleted, and
    /// with the records of a run over the corpus without its first program, a full run has the
    /// cold full run's statuses and `killed_by`.
    #[test]
    #[ignore = "kink"]
    fn partially_cached_full_equals_cold_full() {
        let base = fixture("calc", "partial-base");
        let manifest = base.join("FLOW.toml");
        let mutations = base.join("MUTATIONS.toml");
        let cold = full(&manifest, &mutations);
        let mut mixed = 0;
        for row in rows(&cold) {
            let id = row["id"].as_str().unwrap();
            for program in ["add", "nested", "sub", "inline"] {
                let dir = scratch(&format!("partial-{id}-{program}")).join("calc");
                copy_all(&base, &dir);
                let manifest = dir.join("FLOW.toml");
                delete_record(&manifest, &cold, id, program);
                let (partial, ok) = run_as(
                    &manifest,
                    &dir.join("MUTATIONS.toml"),
                    &[id],
                    ScheduleMode::Full,
                    RunMode::Search,
                    MemoUse::On,
                );
                assert!(ok, "{partial:#}");
                let again = mutation(&partial, id);
                assert_eq!(
                    again["status"], row["status"],
                    "STOP: {id} without {program}"
                );
                assert_eq!(
                    again["killed_by"], row["killed_by"],
                    "{id} without {program}"
                );
                assert_eq!(calls(&partial, id), vec![strings(&[program])]);
                assert_eq!(executed(&partial, id), executed(&cold, id));
                mixed += 1;
            }
        }
        assert_eq!(mixed, 20);
        // The records of a run over the corpus without `add` (an agreement set and kills it did
        // not see `add` beside).
        let dir = fixture("calc", "partial-subset");
        let subset = subset_manifest(&dir, "FLOW-subset.toml", &["nested", "sub", "inline"]);
        let filled = full(&subset, &dir.join("MUTATIONS.toml"));
        assert_eq!(filled["outcome_cache"]["records_written"], 15);
        let partial = full(&dir.join("FLOW.toml"), &dir.join("MUTATIONS.toml"));
        assert_eq!(statuses(&partial), statuses(&cold));
        assert_eq!(killed_by(&partial), killed_by(&cold));
        assert_eq!(partial["matrix"], cold["matrix"]);
        for row in rows(&partial) {
            let id = row["id"].as_str().unwrap();
            assert_eq!(calls(&partial, id), vec![strings(&["add"])], "{id}");
        }
    }

    /// Why `killed_by` is full-only: the first-kill killer is history (a valid killed record
    /// decides before a cheaper killer is tried), `killed_by` is not.
    #[test]
    #[ignore = "kink"]
    fn the_first_kill_killer_is_history_but_killed_by_is_not() {
        let dir = fixture("calc", "history");
        let mutations = dir.join("MUTATIONS.toml");
        let only = ["add-becomes-sub"];
        let two = subset_manifest(&dir, "FLOW-two.toml", &["nested", "inline"]);
        let three = subset_manifest(&dir, "FLOW-three.toml", &["add", "nested", "inline"]);
        let killer = |manifest: &Path, schedule| {
            let (document, ok) = run_as(
                manifest,
                &mutations,
                &only,
                schedule,
                RunMode::Search,
                MemoUse::On,
            );
            assert!(ok, "{document:#}");
            let row = mutation(&document, "add-becomes-sub");
            assert_eq!(row["status"], "killed");
            (row["killer"].clone(), row["killed_by"].clone())
        };
        assert_eq!(killer(&two, ScheduleMode::FirstKill).0, "nested");
        // Warm: the valid `nested` record decides, where a cold run reports `add`.
        assert_eq!(killer(&three, ScheduleMode::FirstKill).0, "nested");
        assert_eq!(
            killer(&three, ScheduleMode::Full),
            (json!("add"), json!(["add", "nested", "inline"]))
        );
        let cold = fixture("calc", "history-cold");
        let cold_three = subset_manifest(&cold, "FLOW-three.toml", &["add", "nested", "inline"]);
        assert_eq!(killer(&cold_three, ScheduleMode::FirstKill).0, "add");
        let cold = fixture("calc", "history-cold-full");
        let cold_three = subset_manifest(&cold, "FLOW-three.toml", &["add", "nested", "inline"]);
        assert_eq!(
            killer(&cold_three, ScheduleMode::Full),
            (json!("add"), json!(["add", "nested", "inline"]))
        );
    }

    /// A full run's hint is the first of `killed_by` (corpus order), on a live and on a cached
    /// row alike, and a row with no kill removes it; a hint naming no comparable program is
    /// reported (`stale_killer`) and replaced.
    #[test]
    #[ignore = "kink"]
    fn full_hints_follow_killed_by() {
        let dir = fixture("calc", "hints");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let cold = full(&manifest, &mutations);
        assert_eq!(
            hints(&manifest),
            [
                ("add-becomes-sub", "add"),
                ("mul-becomes-add", "nested"),
                ("no-mul", "nested"),
                ("sub-off-by-one", "sub"),
            ]
            .into_iter()
            .map(|(id, program)| (id.to_owned(), program.to_owned()))
            .collect()
        );
        // A hint on no-mul's last killer and one on the survivor: a warm full run, decided by
        // tier 1 with no call, puts back the first killer and removes the survivor's hint.
        set_hint(&manifest, &mutations, &cold, "no-mul", "inline");
        set_hint(&manifest, &mutations, &cold, "add-swaps-operands", "add");
        let warm = full(&manifest, &mutations);
        assert_eq!(warm["outcome_cache"]["mutations_from_cache"], 5);
        assert_eq!(hints(&manifest), first_killers(&cold));
        // A hint naming a program that left the corpus.
        let without = subset_manifest(&dir, "FLOW-without-nested.toml", &["add", "sub", "inline"]);
        let (stale, ok) = run_as(
            &without,
            &mutations,
            &["no-mul"],
            ScheduleMode::Full,
            RunMode::Search,
            MemoUse::On,
        );
        assert!(ok, "{stale:#}");
        let row = mutation(&stale, "no-mul");
        assert!(row["stale_killer"].is_string(), "{row:#}");
        assert_eq!(row["status"], "killed");
        assert_eq!(row["killed_by"], json!(["inline"]));
        assert!(calls(&stale, "no-mul").is_empty());
        assert_eq!(hints(&without)["no-mul"], "inline");
    }

    /// A cached kill next to a mutant that no longer compiles: under first-kill the kill decides
    /// with no call, but a full row needs every cell, so the live call over the rest finds the
    /// mutant rejected, and the cached outcome and the call do not form one plan. That is the
    /// corpus error `outcome-conflict`: no verdict, nothing written, the run stops, and the row
    /// keeps the cached kill's entry (the rejected mutant ran no test, so the call adds none).
    /// `run --full --verify`, its next step, reports the forged kill.
    #[test]
    #[ignore = "kink"]
    fn a_cached_kill_next_to_a_rejected_mutant_is_an_outcome_conflict() {
        let dir = fixture("macro", "conflict");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let (cold, _) = run_as(
            &manifest,
            &mutations,
            &[],
            ScheduleMode::FirstKill,
            RunMode::Search,
            MemoUse::On,
        );
        assert_eq!(mutation(&cold, "plus-unbound")["reason"], "rejected");
        forge_kill(
            &manifest,
            &cold,
            "plus-becomes-minus",
            "plus-unbound",
            "sum",
        );
        let before = fs::read_to_string(outcome_file(&manifest, &cold, "plus-unbound")).unwrap();
        let only = ["plus-unbound"];
        let (first, ok) = run_as(
            &manifest,
            &mutations,
            &only,
            ScheduleMode::FirstKill,
            RunMode::Search,
            MemoUse::On,
        );
        assert!(ok, "{first:#}");
        let row = mutation(&first, "plus-unbound");
        assert_eq!(
            (&row["status"], &row["killer_source"]),
            (&json!("killed"), &json!("outcome-cache"))
        );
        assert!(calls(&first, "plus-unbound").is_empty());
        let (document, ok) = run_as(
            &manifest,
            &mutations,
            &only,
            ScheduleMode::Full,
            RunMode::Search,
            MemoUse::On,
        );
        assert!(!ok, "{document:#}");
        let row = mutation(&document, "plus-unbound");
        assert_eq!(row["status"], "error");
        assert_eq!(row["reason"], "outcome-conflict", "{row:#}");
        assert!(row["killed_by"].is_null(), "{row:#}");
        let detail = row["detail"].as_str().unwrap();
        assert!(
            detail.ends_with("run `kink-flow run FLOW.toml MUTATIONS.toml --full --verify`"),
            "{detail}"
        );
        assert_eq!(calls(&document, "plus-unbound"), vec![strings(&["seven"])]);
        assert_eq!(
            executed(&document, "plus-unbound"),
            EXECUTED_CONFLICT
                .iter()
                .map(|(program, outcome)| ((*program).to_owned(), (*outcome).to_owned()))
                .collect::<Vec<_>>(),
            "{row:#}"
        );
        assert_eq!(
            document["stopped"],
            json!({"mutation": "plus-unbound", "reason": "outcome-conflict"})
        );
        assert_eq!(document["outcome_cache"]["records_written"], 0);
        assert_eq!(
            fs::read_to_string(outcome_file(&manifest, &cold, "plus-unbound")).unwrap(),
            before
        );
        let (verified, ok) = run_as(
            &manifest,
            &mutations,
            &only,
            ScheduleMode::Full,
            RunMode::Verify,
            MemoUse::On,
        );
        assert!(!ok);
        let row = mutation(&verified, "plus-unbound");
        assert_eq!(row["status"], "error");
        assert_eq!(row["reason"], "outcome-mismatch:sum", "{row:#}");
    }

    /// The executed entries of the outcome-conflict row: the cached kill alone, since a rejected
    /// mutant runs no test in the live call.
    const EXECUTED_CONFLICT: &[(&str, &str)] = &[("sum", "distinguish")];

    /// A mutant-scope infrastructure failure next to a cached kill gives the status a cold full
    /// run gives (error, reason infrastructure), not a corpus error: the cached kill leaves the
    /// row and the counts, as a cached agreement does, and nothing is written.
    #[test]
    #[ignore = "kink"]
    fn an_infrastructure_failure_next_to_a_cached_kill_is_the_cold_status() {
        let dir = fixture("macro", "infrastructure");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let (cold, _) = run_as(
            &manifest,
            &mutations,
            &[],
            ScheduleMode::FirstKill,
            RunMode::Search,
            MemoUse::On,
        );
        forge_kill(
            &manifest,
            &cold,
            "plus-becomes-minus",
            "plus-in-a-group",
            "sum",
        );
        let before = fs::read_to_string(outcome_file(&manifest, &cold, "plus-in-a-group")).unwrap();
        let only = ["plus-in-a-group"];
        let (document, ok) = run_as(
            &manifest,
            &mutations,
            &only,
            ScheduleMode::Full,
            RunMode::Search,
            MemoUse::On,
        );
        assert!(ok, "no corpus error: {document:#}");
        let fresh = fixture("macro", "infrastructure-cold");
        let (cold_full, _) = run_as(
            &fresh.join("FLOW.toml"),
            &fresh.join("MUTATIONS.toml"),
            &only,
            ScheduleMode::Full,
            RunMode::Search,
            MemoUse::On,
        );
        let row = mutation(&document, "plus-in-a-group");
        let cold_row = mutation(&cold_full, "plus-in-a-group");
        assert_eq!(row["reason"], "infrastructure", "{row:#}");
        for key in ["status", "reason", "killed_by", "killer"] {
            assert_eq!(row[key], cold_row[key], "{key}");
        }
        assert_eq!(
            calls(&document, "plus-in-a-group"),
            vec![strings(&["seven"])]
        );
        assert_eq!(timeless(&row["executed"]), timeless(&cold_row["executed"]));
        assert_eq!(document["outcome_cache"]["programs_from_cache"], 0);
        assert_eq!(document["outcome_cache"]["mutations_from_cache"], 0);
        assert_eq!(document["outcome_cache"]["records_written"], 0);
        assert_eq!(
            fs::read_to_string(outcome_file(&manifest, &cold, "plus-in-a-group")).unwrap(),
            before
        );
    }

    /// `run --verify --full`: every program runs live, every record is compared, nothing is
    /// written; a forged record is reported.
    #[test]
    #[ignore = "kink"]
    fn verify_full() {
        let dir = fixture("calc", "verify");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let cold = full(&manifest, &mutations);
        let stores = store_bytes(&manifest);
        let verify = || {
            run_as(
                &manifest,
                &mutations,
                &[],
                ScheduleMode::Full,
                RunMode::Verify,
                MemoUse::On,
            )
        };
        let (verified, ok) = verify();
        assert!(ok, "{verified:#}");
        assert_eq!(verified["mismatches"], json!([]));
        assert_eq!(statuses(&verified), statuses(&cold));
        assert_eq!(killed_by(&verified), killed_by(&cold));
        for row in rows(&verified) {
            let id = row["id"].as_str().unwrap();
            assert_eq!(
                calls(&verified, id),
                vec![strings(&["add", "nested", "sub", "inline"])],
                "{id}"
            );
        }
        assert_eq!(store_bytes(&manifest), stores);
        // A forged kill of a program that agrees (a kill's slots hold a distinction).
        forge_record(&manifest, &cold, "add-swaps-operands", "add", |record| {
            record["outcome"] = json!("killed");
            record["slots"] = json!(["distinguish", "agree"]);
        });
        let (forged, ok) = verify();
        assert!(!ok);
        let row = mutation(&forged, "add-swaps-operands");
        assert_eq!(row["status"], "error");
        assert_eq!(row["reason"], "outcome-mismatch:add");
        assert!(row["killed_by"].is_null());
        assert!(
            forged["mismatches"]
                .as_array()
                .unwrap()
                .iter()
                .any(|m| m["program"] == "add" && m["cached"]["outcome"] == "killed")
        );
        // The status the forged record gives on the cached path is reported too.
        assert!(
            forged["mismatches"]
                .as_array()
                .unwrap()
                .iter()
                .any(|m| m["program"].is_null() && m["cached"]["status"] == "killed")
        );
    }

    /// The binary: `--full` is accepted once and never with `--order`; `report` prints the
    /// stored full document byte for byte.
    #[test]
    #[ignore = "kink"]
    fn cli_full() {
        let binary = env!("CARGO_BIN_EXE_kink-flow");
        let dir = fixture("calc", "cli");
        let cache = scratch("cli-cache");
        let run = |args: &[&str]| {
            Command::new(binary)
                .arg("run")
                .arg(dir.join("FLOW.toml"))
                .arg(dir.join("MUTATIONS.toml"))
                .args(args)
                .arg("--cache")
                .arg(&cache)
                .output()
                .unwrap()
        };
        for (args, message) in [
            (&["--full", "--full"][..], "unexpected argument \"--full\""),
            (
                &["--full", "--order", "corpus"][..],
                "--order orders the first-kill search; --full runs every program in corpus order",
            ),
        ] {
            let output = run(args);
            assert_eq!(
                output.status.code(),
                Some(i32::from(EXIT_UNASKED)),
                "{args:?}"
            );
            let stderr = String::from_utf8(output.stderr).unwrap();
            assert!(stderr.contains(message), "{stderr}");
        }
        let output = run(&["--full", "--only", "no-mul"]);
        assert_eq!(output.status.code(), Some(i32::from(EXIT_YES)));
        let document: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(document["schedule"], "full");
        assert_eq!(
            mutation(&document, "no-mul")["killed_by"],
            json!(["nested", "inline"])
        );
        let report = Command::new(binary)
            .arg("report")
            .arg(dir.join("FLOW.toml"))
            .arg("--cache")
            .arg(&cache)
            .output()
            .unwrap();
        assert_eq!(report.status.code(), Some(i32::from(EXIT_YES)));
        assert_eq!(report.stdout, output.stdout);
    }

    /// The verdicts rendering (`--output verdicts`): a full rendering holds the schedule, the
    /// profile and each killed mutation's `killed_by`, and is the same cold and warm; a first-kill
    /// rendering holds no killer, and is the same before and after a full run filled the cache.
    #[test]
    #[ignore = "kink"]
    fn verdicts_full() {
        let dir = fixture("calc", "verdicts");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let full_cold = verdicts(&full(&manifest, &mutations)).unwrap();
        let full_warm = verdicts(&full(&manifest, &mutations)).unwrap();
        // First-kill after the full run filled the cache, and on a cold cache.
        let first_warm = verdicts(&first_kill(&manifest, &mutations)).unwrap();
        let cold = fixture("calc", "verdicts-cold");
        let first_cold = verdicts(&first_kill(
            &cold.join("FLOW.toml"),
            &cold.join("MUTATIONS.toml"),
        ))
        .unwrap();
        assert_eq!(full_cold, full_warm);
        assert_eq!(first_cold, first_warm);
        let profile = kink_native::execution::SolverProfile::BUILD.name();
        assert!(
            full_cold.starts_with(&format!(
                "schema = \"kink-flow-verdicts\"\nversion = 5\ndocument = \"run\"\nschedule = \
                 \"full\"\nprofile = \"{profile}\"\n"
            )),
            "{full_cold}"
        );
        assert!(
            full_cold.contains(
                "\n[[mutation]]\nid = \"add-becomes-sub\"\nstatus = \"killed\"\nkilled_by = \
                 [\"add\", \"nested\", \"inline\"]\n"
            ),
            "{full_cold}"
        );
        // A survivor has no `killed_by` line.
        assert!(
            full_cold
                .ends_with("\n[[mutation]]\nid = \"add-swaps-operands\"\nstatus = \"survived\"\n"),
            "{full_cold}"
        );
        assert!(
            first_cold.starts_with(&format!(
                "schema = \"kink-flow-verdicts\"\nversion = 5\ndocument = \"run\"\nschedule = \
                 \"first-kill\"\nprofile = \"{profile}\"\n"
            )),
            "{first_cold}"
        );
        assert!(!first_cold.contains("killed_by"), "{first_cold}");
    }
}

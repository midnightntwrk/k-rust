//! Digests, the result cache and `kink-flow results` (flow F-03 deliverables 1-6).

use kink_campaign::{
    Campaign, CampaignOptions, CampaignReport, ScheduleMode, TestCase, run_campaign_multi,
};
use kink_corpus::ProgramSource;
use kink_corpus::{load_source, runner::all_normal};
use kink_flow::{
    FlowManifest, Program, admit,
    admit::{admit_spec, corpus_source},
    cli::{EXIT_CORPUS, EXIT_OK, EXIT_USAGE, results},
    digest::{program_digest, spec_digest},
    results::{
        BaselineRunner, CACHE_DIRECTORY, RESULT_SCHEMA_VERSION, ResultClass, ResultsOptions,
        execution_budget, fixed_oracles, run_digest,
    },
};
use kink_patch::{Discovery, Patch, SelectionPolicy, select};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

fn flow(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/flow")
        .join(name)
}

/// A fresh directory for one test, under the target's temporary directory.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-results-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

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

/// A private copy of a testdata/flow fixture.
fn fixture(name: &str, test: &str) -> PathBuf {
    let dir = scratch(test).join(name);
    copy_dir(&flow(name), &dir);
    dir
}

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn append(path: &Path, text: &str) {
    let mut contents = fs::read_to_string(path).unwrap();
    contents.push_str(text);
    fs::write(path, contents).unwrap();
}

#[track_caller]
fn run(manifest: &Path, verify: bool) -> (Value, u8) {
    results(
        manifest,
        &ResultsOptions {
            verify,
            cache: None,
        },
    )
}

/// `(id, class, cached)` of every program row.
fn rows(document: &Value) -> Vec<(String, String, bool)> {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            (
                p["id"].as_str().unwrap().to_owned(),
                p["class"].as_str().unwrap().to_owned(),
                p["cached"].as_bool().unwrap(),
            )
        })
        .collect()
}

fn expect(rows: &[(&str, &str, bool)]) -> Vec<(String, String, bool)> {
    rows.iter()
        .map(|(id, class, cached)| ((*id).to_owned(), (*class).to_owned(), *cached))
        .collect()
}

fn program_digests(document: &Value) -> Vec<(String, String)> {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            (
                p["id"].as_str().unwrap().to_owned(),
                p["digest"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

fn spec_hex(document: &Value) -> String {
    document["spec"]["digest"].as_str().unwrap().to_owned()
}

/// The record of program `id` in the document's cache.
fn record_path(manifest: &Path, document: &Value, id: &str) -> PathBuf {
    let digest = program_digests(document)
        .into_iter()
        .find(|(program, _)| program == id)
        .unwrap()
        .1;
    manifest
        .parent()
        .unwrap()
        .join(CACHE_DIRECTORY)
        .join("results")
        .join(spec_hex(document))
        .join(format!("{digest}.json"))
}

fn read_json(path: &Path) -> Value {
    serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap()
}

fn manifest_spec_digest(manifest: &FlowManifest) -> String {
    let loaded = load_source(&corpus_source(manifest)).unwrap();
    spec_digest(manifest, &loaded.files).to_string()
}

const CALC_FLOW: &str = include_str!("../../../testdata/flow/calc/FLOW.toml");

/// The calc manifest with every value unchanged: other key order, comments, inline tables,
/// and the defaults written out.
const CALC_FLOW_REFORMATTED: &str = r#"
# the same corpus, written differently
[[program]]
file = "programs/add.calc"
id = "add"

[[program]]
id   =   "nested"
file =   "programs/nested.calc"
variables = {}

[spec]
syntax_module = "CALC-SYNTAX"
main_module = "CALC"
md_selector = "k"
include_dirs = [ "." ]
entry = "calc.k"

[budget]
max_depth = 100000
time_ms = 10000

[[program]]
id = "sub"
file = "programs/sub.calc"

[[program]]
text = "2 * 3 + 1"
id = "inline"
"#;

#[test]
fn digests_ignore_formatting_and_program_ids() {
    let dir = fixture("calc", "digests-format");
    let original = FlowManifest::decode(CALC_FLOW, &dir).unwrap();
    let reformatted = FlowManifest::decode(CALC_FLOW_REFORMATTED, &dir).unwrap();
    assert_eq!(
        manifest_spec_digest(&original),
        manifest_spec_digest(&reformatted)
    );
    let digest = |manifest: &FlowManifest, id: &str| {
        let program = manifest.programs.iter().find(|p| p.id == id).unwrap();
        let text = match &program.source {
            ProgramSource::Text(text) => text.clone(),
            ProgramSource::File(name) => fs::read_to_string(dir.join(name)).unwrap(),
        };
        program_digest(program, &text)
    };
    for id in ["add", "nested", "sub", "inline"] {
        assert_eq!(digest(&original, id), digest(&reformatted, id), "{id}");
    }
    // Renaming a program changes no digest.
    let renamed = FlowManifest::decode(&CALC_FLOW.replace("\"add\"", "\"plus\""), &dir).unwrap();
    assert_eq!(digest(&original, "add"), digest(&renamed, "plus"));
    assert_eq!(
        manifest_spec_digest(&original),
        manifest_spec_digest(&renamed)
    );
}

#[test]
fn the_spec_digest_covers_every_required_file_and_nothing_else() {
    let dir = scratch("digests-spec");
    write(
        &dir.join("main.k"),
        "requires \"lib.k\"\nmodule MAIN\n  imports LIB\n  configuration <k> $PGM:Exp </k>\nendmodule\n",
    );
    write(
        &dir.join("include/lib.k"),
        "module LIB\n  imports INT\n  syntax Exp ::= Int\nendmodule\n",
    );
    write(&dir.join("unrelated.k"), "// not required\n");
    let manifest = FlowManifest::decode(
        "[spec]\nentry = \"main.k\"\nmain_module = \"MAIN\"\ninclude_dirs = [\"include\"]\n\n[[program]]\nid = \"one\"\ntext = \"1\"\n",
        &dir,
    )
    .unwrap();
    // The load reports the required file of the include directory (stop rule of F-03).
    let loaded = load_source(&corpus_source(&manifest)).unwrap();
    assert_eq!(
        loaded
            .files
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>(),
        ["include/lib.k", "main.k"]
    );
    let base = manifest_spec_digest(&manifest);
    write(&dir.join("unrelated.k"), "// still not required\n");
    assert_eq!(manifest_spec_digest(&manifest), base);
    append(&dir.join("include/lib.k"), "// edited\n");
    let after_lib = manifest_spec_digest(&manifest);
    assert_ne!(after_lib, base);
    append(&dir.join("main.k"), "// edited\n");
    let after_main = manifest_spec_digest(&manifest);
    assert_ne!(after_main, after_lib);
    assert_ne!(after_main, base);
    // How the spec is loaded is part of the digest too.
    let mut other_selector = manifest.clone();
    other_selector.spec.md_selector = "k | other".into();
    assert_ne!(manifest_spec_digest(&other_selector), after_main);
}

#[test]
fn a_program_digest_changes_with_its_text_start_sort_and_variables_only() {
    let program = |id: &str| Program {
        id: id.into(),
        source: ProgramSource::Text(String::new()),
        start_sort: None,
        variables: vec![("A".into(), "1".into()), ("B".into(), "2".into())],
    };
    let base = program_digest(&program("p"), "1 + 2");
    let other = program_digest(&program("q"), "3");
    assert_eq!(program_digest(&program("renamed"), "1 + 2"), base);
    assert_ne!(program_digest(&program("p"), "1 + 3"), base);
    assert_eq!(program_digest(&program("q"), "3"), other);
    let mut sorted = program("p");
    sorted.start_sort = Some("Exp".into());
    assert_ne!(program_digest(&sorted, "1 + 2"), base);
    let mut variable = program("p");
    variable.variables[1].1 = "3".into();
    assert_ne!(program_digest(&variable, "1 + 2"), base);
    let mut fewer = program("p");
    fewer.variables.pop();
    assert_ne!(program_digest(&fewer, "1 + 2"), base);
    let mut reversed = program("p");
    reversed.variables.reverse();
    assert_eq!(program_digest(&reversed, "1 + 2"), base);
}

#[test]
fn a_fresh_cache_fills_every_program_and_a_second_run_computes_nothing() {
    for (name, ids) in [
        ("calc", &["add", "nested", "sub", "inline"][..]),
        ("register", &["store", "increment", "double"][..]),
    ] {
        let manifest = fixture(name, &format!("fill-{name}")).join("FLOW.toml");
        let (first, status) = run(&manifest, false);
        assert_eq!(status, EXIT_OK, "{first:#}");
        assert_eq!(first["schema"], "kink-flow-results");
        assert_eq!(first["result_schema_version"], RESULT_SCHEMA_VERSION);
        assert_eq!(
            rows(&first),
            ids.iter()
                .map(|id| ((*id).to_owned(), "comparable".to_owned(), false))
                .collect::<Vec<_>>()
        );
        for id in ids {
            let record = read_json(&record_path(&manifest, &first, id));
            assert_eq!(record["class"], "comparable");
            assert_eq!(record["program_id"], *id);
            assert_eq!(record["key"]["schema_version"], RESULT_SCHEMA_VERSION);
            assert_eq!(record["key"]["spec"], first["spec"]["digest"]);
            assert_eq!(
                record["run_sha256"],
                run_digest(&record["baseline"]).unwrap().to_string()
            );
            assert_eq!(record["baseline"]["test_id"], *id);
            assert_eq!(record["final_configuration"].as_array().unwrap().len(), 1);
            assert_eq!(record["coverage"]["complete"], true);
        }
        let (second, status) = run(&manifest, false);
        assert_eq!(status, EXIT_OK);
        assert_eq!(
            rows(&second),
            ids.iter()
                .map(|id| ((*id).to_owned(), "comparable".to_owned(), true))
                .collect::<Vec<_>>()
        );
        assert_eq!(second["summary"]["computed"], 0);
        let mut uncached = second.clone();
        for program in uncached["programs"].as_array_mut().unwrap() {
            program["cached"] = json!(false);
        }
        uncached["summary"]["computed"] = first["summary"]["computed"].clone();
        assert_eq!(uncached, first);
    }
}

#[test]
fn editing_one_program_recomputes_exactly_that_one() {
    let manifest = fixture("calc", "edit-program").join("FLOW.toml");
    let (first, _) = run(&manifest, false);
    let old = record_path(&manifest, &first, "sub");
    write(
        &manifest.parent().unwrap().join("programs/sub.calc"),
        "10 - 4\n",
    );
    let (second, status) = run(&manifest, false);
    assert_eq!(status, EXIT_OK);
    assert_eq!(
        rows(&second),
        expect(&[
            ("add", "comparable", true),
            ("nested", "comparable", true),
            ("sub", "comparable", false),
            ("inline", "comparable", true),
        ])
    );
    let (before, after) = (program_digests(&first), program_digests(&second));
    assert_eq!(before[0], after[0]);
    assert_ne!(before[2], after[2]);
    assert_eq!(spec_hex(&first), spec_hex(&second));
    // The new text has a new record; the old record stays and is not used.
    let new = record_path(&manifest, &second, "sub");
    assert_ne!(new, old);
    assert!(old.is_file() && new.is_file());
    assert_ne!(read_json(&new)["run_sha256"], read_json(&old)["run_sha256"]);
}

#[test]
fn editing_the_spec_recomputes_every_program_under_a_new_spec_directory() {
    let manifest = fixture("calc", "edit-spec").join("FLOW.toml");
    let (first, _) = run(&manifest, false);
    append(&manifest.parent().unwrap().join("calc.k"), "// edited\n");
    let (second, status) = run(&manifest, false);
    assert_eq!(status, EXIT_OK);
    assert_ne!(spec_hex(&first), spec_hex(&second));
    assert_eq!(program_digests(&first), program_digests(&second));
    assert!(
        rows(&second)
            .iter()
            .all(|(_, class, cached)| class == "comparable" && !cached)
    );
    let results = manifest
        .parent()
        .unwrap()
        .join(CACHE_DIRECTORY)
        .join("results");
    let mut directories = fs::read_dir(&results)
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .collect::<Vec<_>>();
    directories.sort();
    let mut expected = vec![spec_hex(&first), spec_hex(&second)];
    expected.sort();
    assert_eq!(directories, expected);
}

#[test]
fn verify_passes_on_an_untouched_cache_and_fails_after_a_hand_edited_record() {
    let manifest = fixture("calc", "verify").join("FLOW.toml");
    let (first, _) = run(&manifest, false);
    let (verified, status) = run(&manifest, true);
    assert_eq!(status, EXIT_OK, "{verified:#}");
    assert!(
        verified["programs"]
            .as_array()
            .unwrap()
            .iter()
            .all(|p| p["verify"] == "match" && p["cached"] == true)
    );
    assert_eq!(verified["mismatches"], json!([]));

    // A record whose run digest was edited by hand.
    let path = record_path(&manifest, &first, "nested");
    let original = fs::read_to_string(&path).unwrap();
    let mut record: Value = serde_json::from_str(&original).unwrap();
    record["run_sha256"] = json!("0".repeat(64));
    let edited = serde_json::to_string_pretty(&record).unwrap();
    fs::write(&path, &edited).unwrap();
    // Without --verify the record is current (its key is unchanged) and is used as it is.
    let (plain, status) = run(&manifest, false);
    assert_eq!(status, EXIT_OK);
    assert!(rows(&plain).iter().all(|(_, _, cached)| *cached));
    let (verified, status) = run(&manifest, true);
    assert_eq!(status, EXIT_CORPUS);
    let verdicts = verified["programs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| (p["id"].as_str().unwrap(), p["verify"].as_str().unwrap()))
        .collect::<Vec<_>>();
    assert_eq!(
        verdicts,
        [
            ("add", "match"),
            ("nested", "mismatch"),
            ("sub", "match"),
            ("inline", "match")
        ]
    );
    let mismatches = verified["mismatches"].as_array().unwrap();
    assert_eq!(mismatches.len(), 2, "{mismatches:#?}");
    assert!(mismatches.iter().all(|m| m["program"] == "nested"
        && m["record"]
            == format!(
                "results/{}/{}",
                spec_hex(&first),
                path.file_name().unwrap().to_str().unwrap()
            )));
    assert!(
        mismatches[0]["detail"]
            .as_str()
            .unwrap()
            .contains("is not the digest of its baseline row")
    );
    assert!(
        mismatches[1]["detail"]
            .as_str()
            .unwrap()
            .starts_with("run_sha256: cached 0000")
    );
    // --verify reports; it never rewrites the record.
    assert_eq!(fs::read_to_string(&path).unwrap(), edited);

    // A record whose baseline row was edited by hand, its digest left alone.
    let mut record: Value = serde_json::from_str(&original).unwrap();
    let row = record["baseline"].to_string().replace("\"9\"", "\"10\"");
    assert_ne!(row, record["baseline"].to_string());
    record["baseline"] = serde_json::from_str(&row).unwrap();
    fs::write(&path, record.to_string()).unwrap();
    let (verified, status) = run(&manifest, true);
    assert_eq!(status, EXIT_CORPUS);
    let mismatches = verified["mismatches"].as_array().unwrap();
    assert_eq!(mismatches.len(), 1, "{mismatches:#?}");
    assert!(
        mismatches[0]["detail"]
            .as_str()
            .unwrap()
            .contains("is not the digest of its baseline row")
    );

    // Restored, it verifies again.
    fs::write(&path, &original).unwrap();
    assert_eq!(run(&manifest, true).1, EXIT_OK);
}

#[test]
fn a_non_terminating_program_is_class_timeout() {
    let manifest = fixture("loop", "timeout").join("FLOW-timeout.toml");
    let (first, status) = run(&manifest, false);
    assert_eq!(status, EXIT_OK, "{first:#}");
    assert_eq!(
        rows(&first),
        expect(&[
            ("spin", "timeout", false),
            ("countdown", "comparable", false)
        ])
    );
    assert_eq!(
        first["programs"][0]["cause"],
        "the run did not finish within time_ms = 500"
    );
    let record = read_json(&record_path(&manifest, &first, "spin"));
    assert_eq!(record["class"], "timeout");
    assert!(record["baseline"].is_null() && record["run_sha256"].is_null());
    assert!(record["final_configuration"].is_null());
    assert_eq!(record["key"]["budget"]["time_ms"], 500);
    assert_eq!(record["key"]["budget"]["max_depth"], 1_000_000_000_u64);
    // A timeout is a result too: the next run reuses it.
    let (second, _) = run(&manifest, false);
    assert_eq!(
        rows(&second),
        expect(&[("spin", "timeout", true), ("countdown", "comparable", true)])
    );
}

#[test]
fn a_final_configuration_with_a_map_is_class_unknown_with_the_runners_cause() {
    let manifest = fixture("map-store", "map").join("FLOW.toml");
    let (document, status) = run(&manifest, false);
    assert_eq!(status, EXIT_OK, "{document:#}");
    assert_eq!(rows(&document), expect(&[("store", "unknown", false)]));
    assert_eq!(
        document["programs"][0]["cause"],
        "the campaign runner refused the baseline run (BaselineOracleFailed: a baseline \
         declaration-scoped oracle gate rejected); every path ended, but a final configuration \
         is not a value kink can compare (for example it holds a Map, Set or List, an \
         unevaluated function or a symbolic term); leaves: stuck at depth 1"
    );
    let record = read_json(&record_path(&manifest, &document, "store"));
    assert_eq!(record["class"], "unknown");
    assert!(record["baseline"].is_null() && record["run_sha256"].is_null());
    let finals = record["final_configuration"].as_array().unwrap();
    assert_eq!(finals.len(), 1);
    // The stored map `1 |-> 2` is in the final configuration the reader sees.
    let text = finals[0].as_str().unwrap();
    assert!(
        text.contains("Lbl'UndsPipe'-'-GT-Unds'") && text.contains("\\dv{SortInt{}}(\"2\")"),
        "{text}"
    );
    // An unknown program reaches its rule, but only a comparable program covers it.
    assert_eq!(
        record["coverage"]["sentences"][0]["label"],
        "MAP-STORE.store"
    );
    assert_eq!(document["rules"][0]["status"], "uncovered");
    assert_eq!(document["rules"][0]["reached_by"], json!([]));
}

#[test]
fn rules_no_comparable_program_reaches_are_listed_first() {
    let manifest = fixture("loop", "rules").join("FLOW.toml");
    let (document, status) = run(&manifest, false);
    assert_eq!(status, EXIT_OK, "{document:#}");
    let listed = document["rules"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| {
            (
                r["label"].as_str().unwrap_or("-").to_owned(),
                r["file"].as_str().unwrap().to_owned(),
                r["start_line"].as_u64().unwrap(),
                r["status"].as_str().unwrap().to_owned(),
                r["reached_by"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|p| p.as_str().unwrap().to_owned())
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    let rule = |label: &str, line: u64, status: &str, reached: &[&str]| {
        (
            label.to_owned(),
            "loop.k".to_owned(),
            line,
            status.to_owned(),
            reached.iter().map(|p| (*p).to_owned()).collect::<Vec<_>>(),
        )
    };
    assert_eq!(
        listed,
        [
            rule("LOOP.spin", 20, "uncovered", &[]),
            rule("LOOP.unused", 24, "uncovered", &[]),
            rule("LOOP.countdown", 21, "covered", &["countdown"]),
            rule("LOOP.done", 22, "covered", &["countdown"]),
            rule("LOOP.twice", 23, "covered", &["twice"]),
            rule("-", 19, "not-observable", &[]),
        ]
    );
    assert_eq!(
        document["rules"][5]["reason"],
        "equation: coverage sees rewrite steps only"
    );
    assert_eq!(
        document["summary"],
        json!({"programs": 2, "comparable": 2, "computed": 2, "rules": 6, "uncovered": 2,
               "covered": 3, "not_observable": 1, "mismatches": 0})
    );
    // calc: every rule is covered, the unlabelled one by `sub` alone.
    let (calc, _) = run(&fixture("calc", "rules-calc").join("FLOW.toml"), false);
    assert_eq!(
        calc["rules"]
            .as_array()
            .unwrap()
            .iter()
            .map(|r| (
                r["label"].clone(),
                r["status"].clone(),
                r["reached_by"].clone()
            ))
            .collect::<Vec<_>>(),
        [
            (
                json!("CALC.add"),
                json!("covered"),
                json!(["add", "nested", "inline"])
            ),
            (
                json!("CALC.mul"),
                json!("covered"),
                json!(["nested", "inline"])
            ),
            (json!(null), json!("covered"), json!(["sub"])),
        ]
    );
}

#[test]
fn a_record_is_used_only_under_its_own_key() {
    let manifest = fixture("calc", "keys").join("FLOW.toml");
    let (first, _) = run(&manifest, false);
    // Another schema version in a record: recomputed and rewritten, never used.
    let add = record_path(&manifest, &first, "add");
    let mut record = read_json(&add);
    record["key"]["schema_version"] = json!("kink-flow/result/v0");
    fs::write(&add, record.to_string()).unwrap();
    // Another program's record at this program's path.
    let nested = record_path(&manifest, &first, "nested");
    fs::copy(record_path(&manifest, &first, "sub"), &nested).unwrap();
    // A file that is not a record.
    fs::write(record_path(&manifest, &first, "inline"), "not json").unwrap();
    let (second, status) = run(&manifest, false);
    assert_eq!(status, EXIT_OK);
    assert_eq!(
        rows(&second),
        expect(&[
            ("add", "comparable", false),
            ("nested", "comparable", false),
            ("sub", "comparable", true),
            ("inline", "comparable", false),
        ])
    );
    assert_eq!(
        read_json(&add)["key"]["schema_version"],
        RESULT_SCHEMA_VERSION
    );
    assert_eq!(read_json(&nested)["program_id"], "nested");
    // Another budget: every program is recomputed under the new key.
    let text = fs::read_to_string(&manifest).unwrap();
    fs::write(&manifest, format!("{text}\n[budget]\ntime_ms = 20000\n")).unwrap();
    let (third, status) = run(&manifest, false);
    assert_eq!(status, EXIT_OK);
    assert!(rows(&third).iter().all(|(_, _, cached)| !cached));
    assert_eq!(spec_hex(&third), spec_hex(&first));
    assert_eq!(program_digests(&third), program_digests(&first));
    assert_eq!(read_json(&add)["key"]["budget"]["time_ms"], 20000);
    let (fourth, _) = run(&manifest, false);
    assert!(rows(&fourth).iter().all(|(_, _, cached)| *cached));
}

/// The empty generation a zero-mutant campaign runs (as kink-corpus `baseline_only`).
fn run_together(
    spec: &kink_flow::AdmittedSpec,
    manifest: &FlowManifest,
    tests: &[TestCase],
) -> Vec<Value> {
    let discovery = Discovery::empty(spec.validator.baseline(), false, false);
    let generation = select(&discovery, SelectionPolicy::Each, 1)
        .unwrap()
        .fold("test", |_| -> Patch { unreachable!() })
        .unwrap();
    let module = k_rust::kast::identifier::encode(&manifest.spec.main_module);
    let campaign = Campaign {
        validator: &spec.validator,
        module: &module,
        observation: &[],
        classify: &all_normal,
        tests,
        budget: execution_budget(manifest.budget),
    };
    let run = run_campaign_multi(
        &campaign,
        &[generation],
        &CampaignOptions {
            schedule: ScheduleMode::FirstKill,
            selection: kink_campaign::SelectionPolicy::None,
            share_evidence: true,
        },
    )
    .unwrap();
    run.baseline
        .iter()
        .map(|evidence| CampaignReport::baseline_row(evidence).unwrap())
        .collect()
}

#[test]
fn the_run_digest_depends_on_neither_the_program_id_nor_the_other_tests() {
    for name in ["calc", "register"] {
        let manifest = FlowManifest::read(&flow(name).join("FLOW.toml")).unwrap();
        let admission = admit(&manifest);
        let spec = admission.spec.as_ref().unwrap();
        let mut tests = admission
            .programs
            .iter()
            .map(|p| p.outcome.clone().unwrap())
            .collect::<Vec<_>>();
        let runner = BaselineRunner::new(spec, &manifest).unwrap();
        let alone = tests
            .iter()
            .map(|test| {
                let result = runner.run(test.clone());
                assert_eq!(result.class, ResultClass::Comparable);
                result.run_sha256().unwrap()
            })
            .collect::<Vec<_>>();
        // Under another id, the same program has the same run digest (and another row).
        let mut renamed = tests[0].clone();
        renamed.id = "renamed".into();
        let result = runner.run(renamed);
        assert_eq!(result.baseline.as_ref().unwrap()["test_id"], "renamed");
        assert_eq!(result.run_sha256().unwrap(), alone[0]);
        // Every program in one campaign, in both orders: the same run digests.
        for test in &mut tests {
            test.oracles = fixed_oracles();
        }
        let together = run_together(spec, &manifest, &tests);
        assert_eq!(
            together
                .iter()
                .map(|row| run_digest(row).unwrap())
                .collect::<Vec<_>>(),
            alone
        );
        tests.reverse();
        let reversed = run_together(spec, &manifest, &tests);
        let mut expected = alone.clone();
        expected.reverse();
        assert_eq!(
            reversed
                .iter()
                .map(|row| run_digest(row).unwrap())
                .collect::<Vec<_>>(),
            expected
        );
    }
}

#[test]
fn the_binarys_results_command() {
    let binary = env!("CARGO_BIN_EXE_kink-flow");
    let dir = fixture("calc", "binary");
    let manifest = dir.join("FLOW.toml");
    let cache = scratch("binary-cache");
    let output = Command::new(binary)
        .args(["results", manifest.to_str().unwrap(), "--cache"])
        .arg(&cache)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(i32::from(EXIT_OK)));
    let document: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(document["summary"]["comparable"], 4);
    assert!(cache.join("results").join(spec_hex(&document)).is_dir());
    assert!(!dir.join(CACHE_DIRECTORY).exists());
    let output = Command::new(binary)
        .args(["results", manifest.to_str().unwrap(), "--verify", "--cache"])
        .arg(&cache)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(i32::from(EXIT_OK)));
    let document: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert!(rows(&document).iter().all(|(_, _, cached)| *cached));

    // A refused program is a corpus error; the others still get results.
    let output = Command::new(binary)
        .args([
            "results",
            dir.join("FLOW-bad-program.toml").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(i32::from(EXIT_CORPUS)));
    let document: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(
        rows(&document),
        expect(&[
            ("add", "comparable", false),
            ("bad", "refused", false),
            ("sub", "comparable", false),
        ])
    );
    assert!(
        document["programs"][1]["cause"]
            .as_str()
            .unwrap()
            .starts_with("inputs/parse: ")
    );

    // A manifest that does not decode, and a spec that does not compile.
    let broken = dir.join("broken.toml");
    write(&broken, "[spec]\nentry = \"calc.k\"\n");
    let output = Command::new(binary)
        .args(["results", broken.to_str().unwrap()])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(i32::from(EXIT_CORPUS)));
    let document: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(document["schema"], "kink-flow-results");
    assert_eq!(document["spec"]["stage"], "manifest");
    let (document, status) = run(&flow("compile-error").join("FLOW.toml"), false);
    assert_eq!(status, EXIT_CORPUS);
    assert_eq!(document["spec"]["stage"], "compile");
    assert_eq!(document["programs"], json!([]));

    // Usage errors.
    for args in [
        vec!["results"],
        vec![
            "results",
            manifest.to_str().unwrap(),
            "--verify",
            "--verify",
        ],
        vec!["results", manifest.to_str().unwrap(), "--cache"],
        vec!["results", manifest.to_str().unwrap(), "--other"],
        vec!["results", dir.join("missing.toml").to_str().unwrap()],
    ] {
        let output = Command::new(binary).args(&args).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(i32::from(EXIT_USAGE)),
            "{args:?}"
        );
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn admit_spec_admits_programs_one_at_a_time_like_admit() {
    let manifest = FlowManifest::read(&flow("calc").join("FLOW-bad-program.toml")).unwrap();
    let whole = admit(&manifest);
    let (record, admitted) = admit_spec(&manifest);
    assert_eq!(record.text(), whole.record.text());
    let (spec, mut inputs) = admitted.unwrap();
    // In reverse order, each program alone gives what `admit` gave.
    for (program, expected) in manifest.programs.iter().zip(&whole.programs).rev() {
        let outcome = inputs
            .text(program)
            .and_then(|text| inputs.test_case(&spec, program, text));
        assert_eq!(outcome, expected.outcome, "{}", program.id);
    }
}

//! Store-only aggregation keeps unknown evidence and admission boundaries.
use kink_corpus::{
    manifest::CorpusManifest, runner::run_definition, store::Store, summary::summarize,
};
use kink_native::execution::SolverProfile;
use kink_patch::{CAMPAIGN_MANIFEST_DOMAIN, canonical_json, payload_digest, sha256};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};
fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}
fn profile() -> &'static str {
    SolverProfile::BUILD.name()
}
fn clean() -> Value {
    let mut v: Value = serde_json::from_str(include_str!(
        "../../../testdata/corpus/admission-v1/clean.json"
    ))
    .unwrap();
    let d = &mut v["definitions"][0];
    d["root"]["path"] = json!("testdata/corpus/store-v1");
    d["main_module"] = json!("CS13-CLEAN");
    d["files"][0]["sha256"] =
        json!(sha256(include_bytes!("../../../testdata/corpus/store-v1/clean.k")).to_string());
    d["tests"][0]["input"]["program"]["text"] = json!("a");
    d["tests"][1]["input"]["program"]["text"] = json!("b");
    v
}
fn decode(v: &Value) -> CorpusManifest {
    CorpusManifest::from_canonical_json(&canonical_json(v)).unwrap()
}
fn store(name: &str) -> Store {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("cs13-summary-{name}-{}", std::process::id()));
    if path.exists() {
        fs::remove_dir_all(&path).unwrap();
    }
    Store::new(path)
}
fn with_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}
fn run(m: &CorpusManifest, s: &Store) -> Value {
    let outcome = run_definition(&workspace(), m, "clean", s).unwrap();
    let entry = outcome.campaign.unwrap();
    assert_eq!(entry["time_bound_fired"], false);
    let path = s
        .profile_path(m.digest(), profile())
        .join("campaigns")
        .join(format!(
            "{}.json",
            entry["manifest_sha256"].as_str().unwrap()
        ));
    s.read_json(&path).unwrap()
}
fn rewrite(s: &Store, m: &CorpusManifest, report: &Value) {
    let root = s.profile_path(m.digest(), profile());
    let mut index = s.read_json(&root.join("index.json")).unwrap();
    let old = root.join("campaigns").join(format!(
        "{}.json",
        index["clean"]["manifest_sha256"].as_str().unwrap()
    ));
    let mut report = report.clone();
    let digest = payload_digest(
        CAMPAIGN_MANIFEST_DOMAIN,
        canonical_json(&report["manifest"]).as_bytes(),
    )
    .to_string();
    report["manifest_sha256"] = json!(digest);
    let text = canonical_json(&report);
    index["clean"]["manifest_sha256"] = json!(digest);
    index["clean"]["report_sha256"] = json!(sha256(text.as_bytes()).to_string());
    let next = root.join("campaigns").join(format!("{digest}.json"));
    s.write_text(&next, &text).unwrap();
    s.write_json(&root.join("index.json"), &index).unwrap();
    if old != next {
        fs::remove_file(old).unwrap();
    }
}
fn document(s: &Store, m: &CorpusManifest) -> Value {
    summarize(s, &m.digest().to_string(), profile())
        .unwrap()
        .value()
        .clone()
}
fn pattern_manifest(state_first: bool) -> CorpusManifest {
    let mut v = clean();
    let pre = k_rust::kore::codec::to_value(
        &k_rust::kore::parser::parse_pattern("X:SortGeneratedTopCell{}").unwrap(),
    )
    .unwrap();
    let d = &mut v["definitions"][0];
    d["observation"] = json!([{"constructor":"tick","pre":pre,"post":null,"payload":[]}]);
    let pattern = json!({"crash_policy":"reject","projection":{"pattern":{"plan":{"variables":[],"arms":[{"atoms":[{"constructor":"tick","payload":[]}],"relations":[]}],"side_condition":null},"with_bindings":false}}});
    for test in d["tests"].as_array_mut().unwrap() {
        test["oracles"] = if state_first {
            json!([test["oracles"][0].clone(), pattern.clone()])
        } else {
            json!([pattern.clone()])
        };
    }
    decode(&v)
}
fn assert_safe_json(path: &Path, forbidden: &[&str]) {
    for entry in fs::read_dir(path).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            assert_safe_json(&path, forbidden);
        } else if path.extension().is_some_and(|e| e == "json") {
            let text = fs::read_to_string(&path).unwrap();
            let value: Value = serde_json::from_str(&text).unwrap();
            if value["format"] == "KRUST-PROVENANCE" {
                // The artifact must retain the provenance codec's exact bytes.
                kink_patch::SemanticInput::read(&text).unwrap();
            } else {
                assert_eq!(text, canonical_json(&value));
            }
            for absolute in forbidden {
                assert!(
                    !text.contains(absolute),
                    "absolute path in {}",
                    path.display()
                );
            }
            for key in [
                "elapsed",
                "wall_clock",
                "duration_ms",
                "timestamp",
                "timings",
            ] {
                assert!(!text.contains(&format!("\"{key}\"")));
            }
        }
    }
}

#[test]
fn summary_is_reproducible_and_only_reads_the_digest_checked_store_copy() {
    with_stack(|| {
        let m = decode(&clean());
        let a = store("deterministic-a");
        let b = store("deterministic-b");
        let report = run(&m, &a);
        assert_eq!(run(&m, &b), report);
        let generated = summarize(&a, &m.digest().to_string(), profile()).unwrap();
        fn keys(value: &Value, expected: &[&str]) {
            let mut actual = value
                .as_object()
                .unwrap()
                .keys()
                .map(String::as_str)
                .collect::<Vec<_>>();
            let mut expected = expected.to_vec();
            actual.sort();
            expected.sort();
            assert_eq!(actual, expected);
        }
        keys(
            generated.value(),
            &[
                "schema",
                "version",
                "corpus_manifest_sha256",
                "profile",
                "definitions",
                "totals",
                "exposed",
            ],
        );
        let definition = &generated.value()["definitions"][0];
        keys(
            definition,
            &["id", "admission", "census", "campaign", "patterns"],
        );
        keys(&definition["admission"], &["outcome", "stage", "reason"]);
        keys(&definition["census"], &["verdict", "findings", "inert"]);
        keys(
            &definition["campaign"],
            &[
                "manifest_sha256",
                "report_sha256",
                "time_bound_fired",
                "tally",
                "unknown_causes",
                "per_operator",
                "score",
            ],
        );
        keys(
            &generated.value()["totals"],
            &[
                "definitions",
                "tally",
                "unknown_causes",
                "score",
                "patterns",
            ],
        );
        keys(
            &generated.value()["totals"]["definitions"],
            &["listed", "admitted", "exposed", "refused", "error"],
        );
        keys(
            &generated.value()["totals"]["patterns"],
            &[
                "tests_with_match",
                "tests_no_match",
                "tests_unknown",
                "any_match",
            ],
        );
        let first = generated.text();
        assert_eq!(
            first,
            summarize(&b, &m.digest().to_string(), profile())
                .unwrap()
                .text()
        );
        let summary_path = a.profile_path(m.digest(), profile()).join("summary.json");
        a.write_text(&summary_path, &first).unwrap();
        assert_eq!(
            first,
            summarize(&a, &m.digest().to_string(), profile())
                .unwrap()
                .text()
        );
        assert_eq!(first, fs::read_to_string(&summary_path).unwrap());
        assert_safe_json(
            a.root(),
            &[
                workspace().to_str().unwrap(),
                a.root().to_str().unwrap(),
                "/home/",
                "/tmp/",
            ],
        );
        let copy = a.corpus_path(m.digest()).join("corpus-manifest.json");
        assert_eq!(fs::read_to_string(&copy).unwrap(), m.text());
        let mut changed = m.text().into_bytes();
        changed[0] = b'[';
        fs::write(&copy, changed).unwrap();
        assert!(summarize(&a, &m.digest().to_string(), profile()).is_err());
        assert_eq!(fs::read_to_string(&summary_path).unwrap(), first);
        assert!(run_definition(&workspace(), &m, "clean", &a).is_err());
        a.write_text(&copy, &m.text()).unwrap();
        assert!(summarize(&a, &"0".repeat(64), profile()).is_err());
        let wrong = a.root().join("0".repeat(64));
        fs::create_dir_all(&wrong).unwrap();
        fs::write(wrong.join("corpus-manifest.json"), m.text()).unwrap();
        assert!(summarize(&a, &"0".repeat(64), profile()).is_err());
        fs::write(&copy, serde_json::to_string_pretty(&m.value()).unwrap()).unwrap();
        assert!(summarize(&a, &m.digest().to_string(), profile()).is_err());
        fs::remove_file(&copy).unwrap();
        assert!(summarize(&a, &m.digest().to_string(), profile()).is_err());
        fs::remove_dir_all(a.root()).unwrap();
        fs::remove_dir_all(b.root()).unwrap();
    });
}

#[test]
fn mutant_census_flag_moves_campaign_out_of_every_total() {
    with_stack(|| {
        let m = decode(&clean());
        let s = store("flagged");
        let mut report = run(&m, &s);
        let before = document(&s, &m);
        assert_eq!(before["totals"]["tally"], report["summary"]["tally"]);
        report["manifest"]["admission"]["verdict"] = json!("flagged");
        rewrite(&s, &m, &report);
        let after = document(&s, &m);
        assert_eq!(
            after["definitions"][0]["admission"],
            json!({"outcome":"refused","stage":"declaration-census","reason":"vi-t13-mutant"})
        );
        assert_eq!(after["totals"]["definitions"]["admitted"], 0);
        assert_eq!(
            after["totals"]["definitions"]["refused"]["declaration-census"],
            1
        );
        for (_, count) in after["totals"]["tally"].as_object().unwrap() {
            assert_eq!(count, 0, "STOP: flagged tally enters totals");
        }
        assert_eq!(after["exposed"], json!([]));
        fs::remove_dir_all(s.root()).unwrap();
    });
}

#[test]
fn pattern_rows_follow_declared_slots_and_unknown_is_never_no_match() {
    with_stack(|| {
        let m = pattern_manifest(true);
        let s = store("pattern");
        let mut report = run(&m, &s);
        let summary = document(&s, &m);
        let rows = summary["definitions"][0]["patterns"].as_array().unwrap();
        assert_eq!(rows.len(), 2);
        for row in rows {
            assert_eq!(row["oracle"], 1);
            let baseline = report["baseline"]
                .as_array()
                .unwrap()
                .iter()
                .find(|r| r["test_id"] == row["test_id"])
                .unwrap();
            let side = &baseline["run"]["sides"][1];
            let expected = if side["normal"]["pattern"].is_object() {
                "match"
            } else if side["normal"]["pattern"] == "no-match" {
                "no-match"
            } else {
                "unknown"
            };
            assert_eq!(row["baseline"], expected);
        }
        for row in report["baseline"].as_array_mut().unwrap() {
            row["run"]["sides"][1] = json!("unknown");
        }
        rewrite(&s, &m, &report);
        let summary = document(&s, &m);
        assert_eq!(
            summary["totals"]["patterns"],
            json!({"tests_with_match":0,"tests_no_match":0,"tests_unknown":2,"any_match":"unknown"})
        );
        for row in summary["definitions"][0]["patterns"].as_array().unwrap() {
            assert_eq!(row["baseline"], "unknown");
        }
        report["baseline"][0]["run"]["sides"]
            .as_array_mut()
            .unwrap()
            .pop();
        rewrite(&s, &m, &report);
        assert!(summarize(&s, &m.digest().to_string(), profile()).is_err());
        fs::remove_dir_all(s.root()).unwrap();
    });
}

#[test]
fn unknown_state_sides_never_create_pattern_rows_or_pattern_totals() {
    with_stack(|| {
        let m = decode(&clean());
        let s = store("state-only");
        let mut report = run(&m, &s);
        for row in report["baseline"].as_array_mut().unwrap() {
            row["run"]["sides"][0] = json!("unknown");
        }
        rewrite(&s, &m, &report);
        let summary = document(&s, &m);
        assert!(summary["definitions"][0]["patterns"].is_null());
        assert_eq!(summary["totals"]["patterns"]["tests_with_match"], 0);
        assert_eq!(summary["totals"]["patterns"]["tests_no_match"], 0);
        assert_eq!(summary["totals"]["patterns"]["tests_unknown"], 0);
        fs::remove_dir_all(s.root()).unwrap();
    });
}

#[test]
fn summary_never_constructs_a_mutant_status() {
    let source = include_str!("../src/summary.rs");
    assert!(!source.contains("MutantStatus::"));
}

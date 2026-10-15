//! Binary/library byte identity, child isolation, resume, pinning and stored replay.
use kink_corpus::{manifest::CorpusManifest, run_definition, store::Store, summary::summarize};
use kink_native::execution::SolverProfile;
use kink_patch::{canonical_json, sha256};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs,
    os::{fd::OwnedFd, unix::net::UnixStream},
    path::{Path, PathBuf},
    process::{Command, Output},
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
struct Scratch(PathBuf);
impl Scratch {
    fn new(name: &str) -> Self {
        let path = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("cs13b-{name}-{}", std::process::id()));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }
    fn manifest(&self, value: &Value) -> (PathBuf, CorpusManifest) {
        let text = canonical_json(value);
        let path = self.0.join("corpus.json");
        fs::write(&path, &text).unwrap();
        (path, CorpusManifest::from_canonical_json(&text).unwrap())
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}
fn clean() -> Value {
    let mut value: Value = serde_json::from_str(include_str!(
        "../../../testdata/corpus/admission-v1/clean.json"
    ))
    .unwrap();
    let d = &mut value["definitions"][0];
    d["root"]["path"] = json!("testdata/corpus/store-v1");
    d["main_module"] = json!("CS13-CLEAN");
    d["files"][0]["sha256"] =
        json!(sha256(include_bytes!("../../../testdata/corpus/store-v1/clean.k")).to_string());
    d["files"].as_array_mut().unwrap().push(json!({"name":"program.txt","sha256":sha256(include_bytes!("../../../testdata/corpus/store-v1/program.txt")).to_string()}));
    d["tests"][0]["input"]["program"] = json!({"file":"program.txt"});
    d["tests"][1]["input"]["program"]["text"] = json!("b");
    value
}
fn mini() -> Value {
    let mut value = clean();
    let base = value["definitions"][0].clone();
    for (id, file, module) in [
        ("float", "float.k", "TB02FLOAT"),
        ("flagged", "t13owk.k", "T13OWK"),
        ("map", "map.k", "CS12-MAP"),
    ] {
        let mut d = base.clone();
        d["id"] = json!(id);
        d["root"]["path"] = json!("testdata/corpus/admission-v1");
        d["entry"] = json!(file);
        d["main_module"] = json!(module);
        d["files"] = json!([{"name":file,"sha256":sha256(&fs::read(workspace().join("testdata/corpus/admission-v1").join(file)).unwrap()).to_string()}]);
        d["tests"][0]["input"]["program"] = json!({"text":"true"});
        d["tests"][1]["input"]["program"] = json!({"text":"false"});
        value["definitions"].as_array_mut().unwrap().push(d);
    }
    let mut excluded = base.clone();
    excluded["id"] = json!("let-test");
    value["definitions"].as_array_mut().unwrap().push(excluded);
    let mut renamed = base;
    renamed["id"] = json!("renamed");
    renamed["root"]["path"] =
        json!("testdata/corpus/admission-v1/k-distribution/tests/regression-new/let-test");
    value["definitions"].as_array_mut().unwrap().push(renamed);
    value
}
fn command(name: &str, manifest: &Path, store: &Store) -> Command {
    command_at(name, manifest, store, &workspace())
}
fn command_at(name: &str, manifest: &Path, store: &Store, workspace: &Path) -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_kink-corpus"));
    cmd.arg(name)
        .arg("--workspace")
        .arg(workspace)
        .arg("--store")
        .arg(store.root())
        .arg("--")
        .arg(manifest);
    // Tests remain isolated from any ambient abort hook.
    cmd.env_remove("KINK_CORPUS_TEST_ABORT");
    cmd
}
fn success(output: Output) -> String {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}
fn stored_bytes(root: &Path) -> BTreeMap<PathBuf, Vec<u8>> {
    all_stored_bytes(root)
        .into_iter()
        .filter(|(path, _)| path.file_name().unwrap() != "timings.log")
        .collect()
}
fn all_stored_bytes(root: &Path) -> BTreeMap<PathBuf, Vec<u8>> {
    fn walk(root: &Path, path: &Path, result: &mut BTreeMap<PathBuf, Vec<u8>>) {
        for entry in fs::read_dir(path).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                walk(root, &path, result);
            } else {
                result.insert(
                    path.strip_prefix(root).unwrap().into(),
                    fs::read(path).unwrap(),
                );
            }
        }
    }
    let mut result = BTreeMap::new();
    walk(root, root, &mut result);
    result
}
fn library_store(manifest: &CorpusManifest, store: &Store) -> String {
    for definition in manifest.definitions() {
        run_definition(&workspace(), manifest, &definition.id, store).unwrap();
    }
    let summary = summarize(store, &manifest.digest().to_string(), profile()).unwrap();
    store
        .write_text(
            &store
                .profile_path(manifest.digest(), profile())
                .join("summary.json"),
            &summary.text(),
        )
        .unwrap();
    summary.text()
}
fn with_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn binary_matches_library_and_resume_and_summary_preserve_store_bytes() {
    with_stack(|| {
        let scratch = Scratch::new("identity");
        for schedule in ["full", "first-kill"] {
            let mut value = mini();
            value["campaign"]["schedule"] = json!(schedule);
            let (path, manifest) = scratch.manifest(&value);
            let binary = Store::new(scratch.0.join(format!("binary-{schedule}")));
            let library = Store::new(scratch.0.join(format!("library-{schedule}")));
            success(command("run", &path, &binary).output().unwrap());
            for definition in manifest.definitions() {
                run_definition(&workspace(), &manifest, &definition.id, &library).unwrap();
            }
            let summary = summarize(&library, &manifest.digest().to_string(), profile()).unwrap();
            library
                .write_text(
                    &library
                        .profile_path(manifest.digest(), profile())
                        .join("summary.json"),
                    &summary.text(),
                )
                .unwrap();
            let before = stored_bytes(binary.root());
            assert_eq!(
                before,
                stored_bytes(library.root()),
                "STOP: binary/library store bytes differ"
            );
            for bytes in before.values() {
                let text = String::from_utf8_lossy(bytes);
                for forbidden in [
                    workspace().to_str().unwrap(),
                    scratch.0.to_str().unwrap(),
                    "/home/",
                    "/tmp/",
                    "elapsed",
                    "timings",
                    "wall_clock",
                ] {
                    assert!(!text.contains(forbidden), "stored host value: {forbidden}");
                }
            }
            let resumed = success(
                command("run", &path, &binary)
                    .env("KINK_CORPUS_TEST_ABORT", "clean")
                    .output()
                    .unwrap(),
            );
            assert!(resumed.contains("clean: resumed"));
            assert_eq!(before, stored_bytes(binary.root()));
            let regenerated = success(
                Command::new(env!("CARGO_BIN_EXE_kink-corpus"))
                    .arg("summary")
                    .arg("--store")
                    .arg(binary.root())
                    .arg(manifest.digest().to_string())
                    .arg(profile())
                    .env("KINK_CORPUS_TEST_ABORT", "clean")
                    .output()
                    .unwrap(),
            );
            assert_eq!(regenerated.trim_end(), summary.text());
            assert_eq!(before, stored_bytes(binary.root()));
            assert!(
                binary
                    .profile_path(manifest.digest(), profile())
                    .join("timings.log")
                    .exists()
            );
            let digest = manifest.digest();
            let index = binary.read_index(digest, profile()).unwrap();
            let artifact = binary
                .read_json(&binary.profile_path(digest, profile()).join(format!(
                    "campaigns/{}.json",
                    index["clean"]["manifest_sha256"].as_str().unwrap()
                )))
                .unwrap();
            let artifact_path = binary.profile_path(digest, profile()).join(
                artifact["manifest"]["baseline"]["artifact"]
                    .as_str()
                    .unwrap(),
            );
            let modified = fs::metadata(&artifact_path).unwrap().modified().unwrap();
            success(command("run", &path, &binary).output().unwrap());
            assert_eq!(
                fs::metadata(artifact_path).unwrap().modified().unwrap(),
                modified
            );
        }
    });
}

#[test]
fn abort_is_error_process_and_next_definition_runs() {
    let scratch = Scratch::new("abort");
    let mut value = clean();
    let mut next = value["definitions"][0].clone();
    next["id"] = json!("next");
    value["definitions"].as_array_mut().unwrap().push(next);
    let (path, manifest) = scratch.manifest(&value);
    let store = Store::new(scratch.0.join("store"));
    success(
        command("run", &path, &store)
            .env("KINK_CORPUS_TEST_ABORT", "clean")
            .output()
            .unwrap(),
    );
    let admission = store
        .read_json(
            &store
                .admission_path(manifest.digest(), profile(), "clean")
                .unwrap(),
        )
        .unwrap();
    assert_eq!(admission["outcome"], "error");
    assert_eq!(admission["reason"], "process");
    let summary = store
        .read_json(
            &store
                .profile_path(manifest.digest(), profile())
                .join("summary.json"),
        )
        .unwrap();
    assert_eq!(summary["totals"]["definitions"]["error"], 1);
    assert_eq!(
        summary["definitions"][1]["admission"]["outcome"],
        "admitted"
    );
    assert!(
        store
            .read_index(manifest.digest(), profile())
            .unwrap()
            .get("clean")
            .is_none()
    );
    assert!(
        store
            .read_index(manifest.digest(), profile())
            .unwrap()
            .get("next")
            .is_some()
    );
}

#[test]
fn replay_uses_stored_inputs_and_sampling_budget_and_checks_time_bound_evidence() {
    let scratch = Scratch::new("replay");
    let mut value = clean();
    value["campaign"]["budget_mutants"] = json!({"per_spec_max":1,"total_max":1,"seed":"00ff"});
    let (path, manifest) = scratch.manifest(&value);
    let store = Store::new(scratch.0.join("store"));
    success(command("run", &path, &store).output().unwrap());
    let output = success(
        Command::new(env!("CARGO_BIN_EXE_kink-corpus"))
            .arg("replay-check")
            .arg("--workspace")
            .arg("missing-workspace")
            .arg("--store")
            .arg(store.root())
            .arg(&path)
            .arg("clean")
            .env_remove("KINK_CORPUS_TEST_ABORT")
            .output()
            .unwrap(),
    );
    assert_eq!(output.trim(), "Reproduced");
    let base = store.profile_path(manifest.digest(), profile());
    let mut index = store.read_index(manifest.digest(), profile()).unwrap();
    let report_path = base.join(format!(
        "campaigns/{}.json",
        index["clean"]["manifest_sha256"].as_str().unwrap()
    ));
    let mut report = store.read_json(&report_path).unwrap();
    index["clean"]["time_bound_fired"] = json!(true);
    store.write_json(&base.join("index.json"), &index).unwrap();
    let refused = command("replay-check", &path, &store)
        .arg("clean")
        .output()
        .unwrap();
    assert!(
        !refused.status.success(),
        "edited flag bypassed evidence check"
    );
    // Synthetic stored timeout evidence avoids a host-dependent watchdog race.
    report["baseline"][0]["run"]["sides"][0] = json!("timeout");
    let text = canonical_json(&report);
    fs::write(report_path, &text).unwrap();
    index["clean"]["report_sha256"] = json!(sha256(text.as_bytes()).to_string());
    store.write_json(&base.join("index.json"), &index).unwrap();
    assert_eq!(
        success(
            command("replay-check", &path, &store)
                .arg("clean")
                .output()
                .unwrap()
        )
        .trim(),
        "not-applicable: time-bound"
    );
}

#[test]
fn pin_is_canonical_stable_and_includes_file_backed_inputs() {
    let scratch = Scratch::new("pin");
    let mut value = clean();
    value["definitions"][0]["files"] = json!([]);
    let (path, _) = scratch.manifest(&value);
    let pin = || {
        success(
            Command::new(env!("CARGO_BIN_EXE_kink-corpus"))
                .arg("pin")
                .arg("--workspace")
                .arg(workspace())
                .arg(&path)
                .env("KINK_CORPUS_TEST_ABORT", "clean")
                .output()
                .unwrap(),
        )
    };
    pin();
    let first = fs::read_to_string(&path).unwrap();
    let manifest = CorpusManifest::from_canonical_json(&first).unwrap();
    assert_eq!(
        manifest.definitions()[0]
            .files
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>(),
        vec!["clean.k", "program.txt"]
    );
    pin();
    assert_eq!(fs::read_to_string(&path).unwrap(), first);
    let store = Store::new(scratch.0.join("store"));
    success(command("run", &path, &store).output().unwrap());
    assert_eq!(
        success(
            command("replay-check", &path, &store)
                .arg("clean")
                .output()
                .unwrap()
        )
        .trim(),
        "Reproduced"
    );
    // Moving otherwise valid evidence into another corpus directory must not
    // let resume reuse a campaign with a different declared execution budget.
    let old_digest = manifest.digest();
    let mut changed = manifest.value();
    changed["campaign"]["budget"]["time_ms"] = json!(120000);
    let (_, changed_manifest) = scratch.manifest(&changed);
    for (relative, bytes) in stored_bytes(&store.corpus_path(old_digest)) {
        store
            .write_bytes(
                &store.corpus_path(changed_manifest.digest()).join(relative),
                &bytes,
            )
            .unwrap();
    }
    store
        .write_text(
            &store
                .corpus_path(changed_manifest.digest())
                .join("corpus-manifest.json"),
            &changed_manifest.text(),
        )
        .unwrap();
    let transplanted = command("run", &path, &store).output().unwrap();
    assert!(!transplanted.status.success());
    assert!(
        String::from_utf8_lossy(&transplanted.stderr)
            .contains("stored campaign declaration differs")
    );
}

#[test]
fn resume_refuses_transplanted_generation_and_admission_without_writing_store() {
    let scratch = Scratch::new("transplant");
    let ws = scratch.0.join("workspace");
    let root = ws.join("definition");
    fs::create_dir_all(&root).unwrap();
    let source = include_bytes!("../../../testdata/corpus/store-v1/clean.k");
    fs::write(root.join("clean.k"), source).unwrap();
    fs::write(root.join("other.k"), source).unwrap();
    fs::write(
        root.join("program.txt"),
        include_bytes!("../../../testdata/corpus/store-v1/program.txt"),
    )
    .unwrap();
    let mut value = clean();
    value["definitions"][0]["root"]["path"] = json!("definition");
    value["definitions"][0]["files"]
        .as_array_mut()
        .unwrap()
        .push(json!({"name":"other.k","sha256":sha256(source).to_string()}));
    value["definitions"][0]["files"]
        .as_array_mut()
        .unwrap()
        .sort_by(|a, b| a["name"].as_str().cmp(&b["name"].as_str()));
    let (path, manifest) = scratch.manifest(&value);
    let store = Store::new(scratch.0.join("store"));
    success(command_at("run", &path, &store, &ws).output().unwrap());
    let original = all_stored_bytes(&store.corpus_path(manifest.digest()));

    let mut capped = value.clone();
    // The clean fixture's delete-rule population has three members.
    capped["campaign"]["max_candidates_per_spec"] = json!(1);
    let mut excluded = value.clone();
    excluded["exclusions"].as_array_mut().unwrap().push(json!({
        "case":"clean", "reason":"other", "citation":"CS-13B D1 regression"
    }));
    let mut changed_entry = value.clone();
    changed_entry["definitions"][0]["entry"] = json!("other.k");
    let mut variants = vec![
        ("candidate cap", capped),
        ("exclusion", excluded),
        ("entry", changed_entry),
    ];
    if SolverProfile::BUILD == SolverProfile::NoZ3 {
        let mut requires_z3 = value;
        requires_z3["definitions"][0]["requires_profile"] = json!("z3");
        variants.push(("required profile", requires_z3));
    }

    for (case, changed) in variants {
        let (path, changed_manifest) = scratch.manifest(&changed);
        let transplanted = store.corpus_path(changed_manifest.digest());
        for (relative, bytes) in &original {
            store
                .write_bytes(&transplanted.join(relative), bytes)
                .unwrap();
        }
        store
            .write_text(
                &transplanted.join("corpus-manifest.json"),
                &changed_manifest.text(),
            )
            .unwrap();
        let before = all_stored_bytes(store.root());
        let output = command_at("run", &path, &store, &ws).output().unwrap();
        assert!(
            !output.status.success(),
            "transplanted {case} was resumed: {}",
            String::from_utf8_lossy(&output.stdout)
        );
        assert_eq!(
            all_stored_bytes(store.root()),
            before,
            "refusing transplanted {case} changed store bytes"
        );
    }
}

#[test]
fn closed_stdout_run_and_resume_preserve_library_evidence() {
    with_stack(|| {
        let scratch = Scratch::new("closed-stdout");
        let (path, manifest) = scratch.manifest(&clean());
        let store = Store::new(scratch.0.join("binary"));
        let library = Store::new(scratch.0.join("library"));
        let summary = library_store(&manifest, &library);
        // A Unix socket whose reader is gone deterministically gives BrokenPipe
        // to both the child progress print and the parent's summary print.
        let (reader, writer) = UnixStream::pair().unwrap();
        drop(reader);
        success(
            command("run", &path, &store)
                .stdout(OwnedFd::from(writer))
                .output()
                .unwrap(),
        );
        let before = stored_bytes(store.root());
        assert_eq!(before, stored_bytes(library.root()));
        let (reader, writer) = UnixStream::pair().unwrap();
        drop(reader);
        success(
            command("run", &path, &store)
                .stdout(OwnedFd::from(writer))
                .output()
                .unwrap(),
        );
        assert_eq!(stored_bytes(store.root()), before);
        assert_eq!(
            success(command("run", &path, &store).output().unwrap()).trim_end(),
            format!("clean: resumed\n{summary}")
        );
        assert_eq!(stored_bytes(store.root()), before);
    });
}

#[test]
fn process_metadata_after_missing_admission_can_be_retried() {
    with_stack(|| {
        let scratch = Scratch::new("retry-process");
        let (path, manifest) = scratch.manifest(&clean());
        let store = Store::new(scratch.0.join("binary"));
        let library = Store::new(scratch.0.join("library"));
        let summary = library_store(&manifest, &library);
        success(command("run", &path, &store).output().unwrap());
        let before = stored_bytes(store.root());
        assert_eq!(before, stored_bytes(library.root()));
        let admission = store
            .admission_path(manifest.digest(), profile(), "clean")
            .unwrap();
        fs::remove_file(&admission).unwrap();
        success(
            command("run", &path, &store)
                .env("KINK_CORPUS_TEST_ABORT", "clean")
                .output()
                .unwrap(),
        );
        let failed = store.read_json(&admission).unwrap();
        assert_eq!(failed["outcome"], "error");
        assert_eq!(failed["stage"], "process");
        assert_eq!(failed["reason"], "process");
        let output = success(command("run", &path, &store).output().unwrap());
        assert!(output.trim_end().ends_with(&summary));
        assert_eq!(stored_bytes(store.root()), before);
    });
}

#[test]
fn leading_dash_definition_is_admitted_and_replayed_after_option_terminator() {
    let scratch = Scratch::new("leading-dash");
    let mut value = clean();
    value["definitions"][0]["id"] = json!("-id");
    let (path, manifest) = scratch.manifest(&value);
    let store = Store::new(scratch.0.join("store"));
    success(command("run", &path, &store).output().unwrap());
    let admission = store
        .read_json(
            &store
                .admission_path(manifest.digest(), profile(), "-id")
                .unwrap(),
        )
        .unwrap();
    assert_eq!(admission["outcome"], "admitted");
    assert_eq!(
        success(
            command("replay-check", &path, &store)
                .arg("-id")
                .output()
                .unwrap()
        )
        .trim(),
        "Reproduced"
    );
}

/// F-16 review 1 minor 2 (flow F-17): the resume binding checks the same file set as
/// admission, test inputs included. After a completed run, the program file is replaced by
/// a link to the same bytes inside a below-floor case directory; resume refuses at the
/// exclusion check (before F-17 it checked definition sources only and refused later, on the
/// file list) and writes nothing.
#[cfg(unix)]
#[test]
fn resume_refuses_a_test_input_that_now_lies_in_a_below_floor_case_directory() {
    let scratch = Scratch::new("input-exclusion");
    let ws = scratch.0.join("workspace");
    let root = ws.join("definition");
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("clean.k"),
        include_bytes!("../../../testdata/corpus/store-v1/clean.k"),
    )
    .unwrap();
    let program = include_bytes!("../../../testdata/corpus/store-v1/program.txt");
    fs::write(root.join("program.txt"), program).unwrap();
    let mut value = clean();
    value["definitions"][0]["root"]["path"] = json!("definition");
    let (path, _) = scratch.manifest(&value);
    let store = Store::new(scratch.0.join("store"));
    success(command_at("run", &path, &store, &ws).output().unwrap());
    let resumed = success(command_at("run", &path, &store, &ws).output().unwrap());
    assert!(resumed.contains("clean: resumed"), "{resumed}");

    let case = root.join("k-distribution/tests/regression-new/let-test");
    fs::create_dir_all(&case).unwrap();
    fs::write(case.join("program.txt"), program).unwrap();
    fs::remove_file(root.join("program.txt")).unwrap();
    std::os::unix::fs::symlink(case.join("program.txt"), root.join("program.txt")).unwrap();
    let before = all_stored_bytes(store.root());
    let output = command_at("run", &path, &store, &ws).output().unwrap();
    assert!(
        !output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("stored definition is excluded"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(all_stored_bytes(store.root()), before);
}

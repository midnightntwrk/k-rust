//! In-process corpus storage, artifact replay and declared sampling.
use k_rust::{kompile::CompileOptions, kore::ast::Pattern};
use kink_campaign::{
    Campaign, ManifestOperator, MultiManifestInput, ReplayDeclaration, ReplayOperator,
    ReplayOutcome, campaign_manifest_multi_with_budget, replay_with_budget,
};
use kink_corpus::{
    manifest::CorpusManifest, runner::run_definition, store::Store, summary::summarize,
};
use kink_native::{NativeValidator, execution::SolverProfile};
use kink_patch::{OperatorSpec, SemanticInput, canonical_json, resolve_universe, sha256};
use kink_pattern::ExecutionTerminalKind;
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
    match SolverProfile::BUILD {
        SolverProfile::NoZ3 => "no-z3",
        SolverProfile::Z3 => "z3",
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
    d["tests"][0]["input"]["program"]["text"] = json!("a");
    d["tests"][1]["input"]["program"]["text"] = json!("b");
    value
}
fn decode(value: &Value) -> CorpusManifest {
    CorpusManifest::from_canonical_json(&canonical_json(value)).unwrap()
}
fn store(name: &str) -> Store {
    let path =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("cs13-{name}-{}", std::process::id()));
    if path.exists() {
        fs::remove_dir_all(&path).unwrap();
    }
    Store::new(path)
}
/// A fresh store `name` holding a copy of `from`'s files. A store holds no absolute path and no
/// host value (summary.rs `summary_is_reproducible_and_only_reads_the_digest_checked_store_copy`),
/// so the copy is the store the same run would have written there.
fn copy_store(from: &Store, name: &str) -> Store {
    fn copy(from: &Path, to: &Path) {
        fs::create_dir_all(to).unwrap();
        for entry in fs::read_dir(from).unwrap() {
            let entry = entry.unwrap();
            let target = to.join(entry.file_name());
            if entry.file_type().unwrap().is_dir() {
                copy(&entry.path(), &target);
            } else {
                fs::copy(entry.path(), target).unwrap();
            }
        }
    }
    let to = store(name);
    copy(from.root(), to.root());
    to
}
fn with_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}
fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}
fn replay_stored(manifest: &CorpusManifest, store: &Store) -> Value {
    let outcome = run_definition(&workspace(), manifest, "clean", store).unwrap();
    let entry = outcome.campaign.clone().unwrap();
    let resumed = run_definition(
        Path::new("missing-workspace-cs13"),
        manifest,
        "clean",
        store,
    )
    .unwrap();
    assert!(resumed.resumed);
    assert_eq!(resumed.admission, outcome.admission);
    assert_eq!(resumed.campaign, outcome.campaign);
    assert!(
        !entry["time_bound_fired"].as_bool().unwrap(),
        "STOP: clean time bound fired"
    );
    let path = store.profile_path(manifest.digest(), profile());
    let report_text = fs::read_to_string(path.join("campaigns").join(format!(
        "{}.json",
        entry["manifest_sha256"].as_str().unwrap()
    )))
    .unwrap();
    assert_eq!(
        sha256(report_text.as_bytes()).to_string(),
        entry["report_sha256"].as_str().unwrap()
    );
    let report: Value = serde_json::from_str(&report_text).unwrap();
    let artifact =
        fs::read_to_string(path.join(report["manifest"]["baseline"]["artifact"].as_str().unwrap()))
            .unwrap();
    assert_eq!(
        sha256(artifact.as_bytes()).to_string(),
        report["manifest"]["baseline"]["semantic_input_sha256"]
    );
    let (_, baseline) = SemanticInput::read(&artifact).unwrap();
    let validator = NativeValidator::bind(baseline, CompileOptions::default());
    let manifest = store.read_manifest(manifest.digest()).unwrap();
    let d = &manifest.definitions()[0];
    let tests = store
        .rebuild_tests(manifest.digest(), "clean", validator.baseline())
        .unwrap();
    let c = manifest.campaign();
    let mut budget = c.budget;
    if let Some(depth) = d.max_depth {
        budget.max_depth = Some(depth);
    }
    let module = k_rust::kast::identifier::encode(&d.main_module);
    let replay_ops = manifest
        .operators()
        .iter()
        .map(|spec| ReplayOperator::Spec {
            spec,
            cap: usize::try_from(c.max_candidates_per_spec).unwrap(),
        })
        .collect::<Vec<_>>();
    let declaration = ReplayDeclaration {
        module: &module,
        observation: &d.observation,
        classify: &normal,
        classifier: "kink-corpus/all-normal/v1",
        tests: &tests,
        budget,
        schedule: c.schedule,
        selection: c.selection,
        operators: &replay_ops,
    };
    assert_eq!(
        replay_with_budget(
            &report_text,
            &artifact,
            &declaration,
            c.budget_mutants.as_ref()
        ),
        ReplayOutcome::Reproduced,
        "STOP: stored clean replay differs"
    );
    // Independently rebuild generation and campaign declaration from the corpus input.
    let universe = resolve_universe(validator.baseline(), manifest.universe());
    let specs = manifest
        .operators()
        .iter()
        .map(|s| (s, usize::try_from(c.max_candidates_per_spec).unwrap()))
        .collect::<Vec<_>>();
    let generations = OperatorSpec::generate_all(
        validator.baseline(),
        &universe,
        &specs,
        c.budget_mutants
            .as_ref()
            .map(|b| (b.per_spec_max, b.total_max, b.seed.as_slice())),
    )
    .unwrap();
    let campaign = Campaign {
        validator: &validator,
        module: &module,
        observation: &d.observation,
        classify: &normal,
        tests: &tests,
        budget,
    };
    let operators = manifest
        .operators()
        .iter()
        .map(ManifestOperator::Spec)
        .collect::<Vec<_>>();
    let rebuilt = campaign_manifest_multi_with_budget(
        &MultiManifestInput {
            campaign: &campaign,
            generations: &generations,
            schedule: c.schedule,
            selection: c.selection,
            operators: &operators,
            classifier: "kink-corpus/all-normal/v1",
            universe: Some(&universe),
        },
        c.budget_mutants.as_ref(),
    )
    .unwrap();
    assert_eq!(rebuilt.value(), &report["manifest"]);
    if c.budget_mutants.is_some() {
        assert!(generations.iter().any(|g| !g.scored()));
    }
    report
}

#[test]
fn sampling_budget_is_stored_unscored_and_replayed_from_declared_budget() {
    with_stack(|| {
        let mut value = clean();
        value["campaign"]["budget_mutants"] = json!({"per_spec_max":1,"total_max":1,"seed":"00ff"});
        let manifest = decode(&value);
        let store = store("sampled");
        let report = replay_stored(&manifest, &store);
        assert_eq!(
            report["manifest"]["budget_mutants"],
            value["campaign"]["budget_mutants"]
        );
        assert!(
            report["manifest"]["operators"][0]["population"]
                .as_u64()
                .unwrap()
                > 1
        );
        assert!(report["summary"]["score"].is_null());
        let summary = summarize(&store, &manifest.digest().to_string(), profile()).unwrap();
        assert!(summary.value()["totals"]["score"].is_null());
        fs::remove_dir_all(store.root()).unwrap();
    });
}

#[test]
fn stored_copy_precedes_admission_and_conflicting_bytes_are_refused() {
    with_stack(|| {
        let manifest = decode(&clean());
        let store = store("conflict");
        let root = store.corpus_path(manifest.digest());
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("corpus-manifest.json"), "x").unwrap();
        assert!(run_definition(&workspace(), &manifest, "clean", &store).is_err());
        assert_eq!(fs::read_dir(&root).unwrap().count(), 1);
        assert_eq!(
            fs::read_to_string(root.join("corpus-manifest.json")).unwrap(),
            "x"
        );
        fs::remove_dir_all(store.root()).unwrap();
    });
}

#[test]
fn time_bound_detection_reads_only_run_evidence() {
    use kink_corpus::store::time_bound_fired;
    assert!(!time_bound_fired(
        &json!({"manifest":{"budget":{"time_ms":1},"status":"timeout","failed":"time-limit"},"baseline":[],"mutants":[]})
    ));
    assert!(time_bound_fired(
        &json!({"baseline":[{"run":{"sides":["timeout"]}}],"mutants":[]})
    ));
    assert!(time_bound_fired(
        &json!({"baseline":[{"run":{"failed":"time-limit"}}],"mutants":[]})
    ));
    assert!(time_bound_fired(
        &json!({"baseline":[],"mutants":[{"status":"timeout"}]})
    ));
    assert!(time_bound_fired(
        &json!({"baseline":[],"mutants":[{"status":"killed","tests":[{"run":{"failed":"time-limit"}}]}]})
    ));
}

/// A stale store: its name, the keys removed from the manifest's `kink` member and a
/// `(key, value)` written into it.
type Stale = (String, Vec<&'static str>, Option<(&'static str, String)>);

mod kink_tier {
    use super::*;

    #[test]
    #[ignore = "kink"]
    fn mini_corpus_records_admission_stores_artifacts_and_replays() {
        with_stack(|| {
            let mut value = clean();
            let base = value["definitions"][0].clone();
            let mut definitions = vec![base.clone()];
            for (id, file, module) in [
                ("float", "float.k", "TB02FLOAT"),
                ("flagged", "t13owk.k", "T13OWK"),
                ("map", "map.k", "CS12-MAP"),
            ] {
                let mut d = base.clone();
                d["id"] = json!(id);
                d["entry"] = json!(file);
                d["main_module"] = json!(module);
                d["root"]["path"] = json!("testdata/corpus/admission-v1");
                d["files"] = json!([{"name":file,"sha256":sha256(&fs::read(workspace().join("testdata/corpus/admission-v1").join(file)).unwrap()).to_string()}]);
                d["tests"][0]["input"]["program"]["text"] = json!("true");
                d["tests"][1]["input"]["program"]["text"] = json!("false");
                definitions.push(d);
            }
            let mut excluded = base.clone();
            excluded["id"] = json!("let-test");
            definitions.push(excluded);
            let mut renamed = base;
            renamed["id"] = json!("renamed");
            renamed["root"]["path"] =
                json!("testdata/corpus/admission-v1/k-distribution/tests/regression-new/let-test");
            definitions.push(renamed);
            value["definitions"] = json!(definitions);
            let manifest = decode(&value);
            let store = store("mini");
            for (id, stage, reason) in [
                ("float", "representation", "G-F"),
                ("flagged", "declaration-census", "vi-t13"),
                ("map", "baseline", "baseline-oracle-failed"),
                ("let-test", "exclusion", "below-floor"),
                ("renamed", "exclusion", "below-floor"),
            ] {
                let outcome = run_definition(&workspace(), &manifest, id, &store).unwrap();
                assert!(outcome.campaign.is_none());
                assert_eq!(outcome.admission["stage"], stage);
                assert_eq!(outcome.admission["reason"], reason);
            }
            let report = replay_stored(&manifest, &store);
            let summary_doc = summarize(&store, &manifest.digest().to_string(), profile()).unwrap();
            let summary = summary_doc.value();
            assert_eq!(summary["totals"]["definitions"]["listed"], 6);
            assert_eq!(summary["totals"]["definitions"]["admitted"], 1);
            assert_eq!(
                summary["totals"]["tally"], report["summary"]["tally"],
                "STOP: refused definition reached totals"
            );
            assert_eq!(summary["exposed"], json!([]));
            fs::remove_dir_all(store.root()).unwrap();
        });
    }

    /// A 1 ms time bound: whether the watchdog fires is a race, never an asserted fixture result,
    /// but either way the run's record is consistent. With a campaign, its stored report is the
    /// indexed one, the index's time-bound flag is the report's evidence (`time_bound_fired`), and a
    /// rerun resumes the same entry; without one, the admission record is the stored one (packet
    /// test-gate TG-P: before, the test asserted only that the run returned).
    #[test]
    #[ignore = "kink"]
    fn tiny_time_bound_is_probed_without_assuming_a_watchdog_race() {
        with_stack(|| {
            let mut value = clean();
            value["campaign"]["budget"]["time_ms"] = json!(1);
            let manifest = decode(&value);
            let store = store("tiny-time");
            let outcome = run_definition(&workspace(), &manifest, "clean", &store).unwrap();
            if let Some(entry) = &outcome.campaign {
                let fired = entry["time_bound_fired"].as_bool().unwrap();
                println!("CS13_TINY_TIME_BOUND_FIRED {fired}");
                let text = fs::read_to_string(
                    store
                        .profile_path(manifest.digest(), profile())
                        .join("campaigns")
                        .join(format!(
                            "{}.json",
                            entry["manifest_sha256"].as_str().unwrap()
                        )),
                )
                .unwrap();
                assert_eq!(
                    sha256(text.as_bytes()).to_string(),
                    entry["report_sha256"].as_str().unwrap()
                );
                let report: Value = serde_json::from_str(&text).unwrap();
                assert_eq!(fired, kink_corpus::store::time_bound_fired(&report));
                let resumed = run_definition(&workspace(), &manifest, "clean", &store).unwrap();
                assert!(resumed.resumed);
                assert_eq!(resumed.campaign, outcome.campaign);
            } else {
                println!(
                    "CS13_TINY_TIME_BOUND_NO_CAMPAIGN {}",
                    canonical_json(&outcome.admission)
                );
                let path = store
                    .admission_path(manifest.digest(), profile(), "clean")
                    .unwrap();
                assert_eq!(store.read_json(&path).unwrap(), outcome.admission);
            }
            fs::remove_dir_all(store.root()).unwrap();
        });
    }

    #[test]
    #[ignore = "kink"]
    fn file_backed_program_replays_without_workspace_and_refuses_changed_or_missing_input() {
        with_stack(|| {
            let store = store("file-program");
            let workspace = store.root().join("workspace");
            let fixture = workspace.join("fixture");
            fs::create_dir_all(&fixture).unwrap();
            fs::write(
                fixture.join("clean.k"),
                include_bytes!("../../../testdata/corpus/store-v1/clean.k"),
            )
            .unwrap();
            let bytes = include_bytes!("../../../testdata/corpus/store-v1/program.txt");
            fs::write(fixture.join("program.txt"), bytes).unwrap();
            let pin = sha256(bytes);
            let mut value = clean();
            let d = &mut value["definitions"][0];
            d["root"]["path"] = json!("fixture");
            d["files"]
                .as_array_mut()
                .unwrap()
                .push(json!({"name":"program.txt","sha256":pin.to_string()}));
            d["tests"][0]["input"]["program"] = json!({"file":"program.txt"});
            let manifest = decode(&value);
            let outcome = run_definition(&workspace, &manifest, "clean", &store).unwrap();
            assert!(outcome.campaign.is_some());
            let input_path = store.input_path(manifest.digest(), pin);
            assert_eq!(fs::read(&input_path).unwrap(), bytes);
            fs::remove_dir_all(&workspace).unwrap();
            replay_stored(&manifest, &store);
            let expected = summarize(&store, &manifest.digest().to_string(), profile())
                .unwrap()
                .text();
            let report = store.read_index(manifest.digest(), profile()).unwrap();
            let root = store.profile_path(manifest.digest(), profile());
            let report_text = fs::read_to_string(root.join(format!(
                "campaigns/{}.json",
                report["clean"]["manifest_sha256"].as_str().unwrap()
            )))
            .unwrap();
            let report: Value = serde_json::from_str(&report_text).unwrap();
            let artifact = fs::read_to_string(
                root.join(report["manifest"]["baseline"]["artifact"].as_str().unwrap()),
            )
            .unwrap();
            let (_, baseline) = SemanticInput::read(&artifact).unwrap();
            let mut changed = bytes.to_vec();
            changed[0] = b'b';
            fs::write(&input_path, changed).unwrap();
            assert!(
                store
                    .rebuild_tests(manifest.digest(), "clean", &baseline)
                    .is_err()
            );
            assert!(summarize(&store, &manifest.digest().to_string(), profile()).is_err());
            assert!(
                run_definition(
                    Path::new("missing-workspace-cs13"),
                    &manifest,
                    "clean",
                    &store
                )
                .is_err()
            );
            fs::remove_file(&input_path).unwrap();
            assert!(
                store
                    .rebuild_tests(manifest.digest(), "clean", &baseline)
                    .is_err()
            );
            assert!(summarize(&store, &manifest.digest().to_string(), profile()).is_err());
            fs::write(&input_path, bytes).unwrap();
            assert_eq!(
                summarize(&store, &manifest.digest().to_string(), profile())
                    .unwrap()
                    .text(),
                expected
            );
            fs::remove_dir_all(store.root()).unwrap();
        });
    }

    #[test]
    #[ignore = "kink"]
    fn file_backed_kore_state_is_stored_and_rebuilt_without_workspace() {
        with_stack(|| {
            let store = store("file-kore");
            let mut value = clean();
            let inline = decode(&value);
            let admitted = kink_corpus::admission::admit_definition(&inline, "clean", &workspace())
                .admitted
                .unwrap();
            let text = canonical_json(
                &k_rust::kore::codec::to_value(&admitted.tests[0].initial_state).unwrap(),
            );
            let pin = sha256(text.as_bytes());
            let workspace = store.root().join("workspace");
            let fixture = workspace.join("fixture");
            fs::create_dir_all(&fixture).unwrap();
            fs::write(
                fixture.join("clean.k"),
                include_bytes!("../../../testdata/corpus/store-v1/clean.k"),
            )
            .unwrap();
            fs::write(fixture.join("state.json"), &text).unwrap();
            value["definitions"][0]["root"]["path"] = json!("fixture");
            value["definitions"][0]["tests"][0]["input"] =
                json!({"kore_state":{"file":"state.json","sha256":pin.to_string()}});
            let manifest = decode(&value);
            run_definition(&workspace, &manifest, "clean", &store).unwrap();
            assert_eq!(
                fs::read_to_string(store.input_path(manifest.digest(), pin)).unwrap(),
                text
            );
            fs::remove_dir_all(&workspace).unwrap();
            replay_stored(&manifest, &store);
            let path = store.input_path(manifest.digest(), pin);
            fs::write(&path, "x").unwrap();
            assert!(summarize(&store, &manifest.digest().to_string(), profile()).is_err());
            fs::remove_dir_all(store.root()).unwrap();
        });
    }

    #[test]
    #[ignore = "kink"]
    fn conflicting_stored_input_is_refused_before_campaign_publication() {
        with_stack(|| {
            let store = store("input-conflict");
            let mut value = clean();
            let bytes = include_bytes!("../../../testdata/corpus/store-v1/program.txt");
            let pin = sha256(bytes);
            value["definitions"][0]["files"]
                .as_array_mut()
                .unwrap()
                .push(json!({"name":"program.txt","sha256":pin.to_string()}));
            value["definitions"][0]["tests"][0]["input"]["program"] = json!({"file":"program.txt"});
            let manifest = decode(&value);
            let path = store.input_path(manifest.digest(), pin);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, "x").unwrap();
            assert!(run_definition(&workspace(), &manifest, "clean", &store).is_err());
            assert_eq!(fs::read_to_string(path).unwrap(), "x");
            assert!(!store.profile_path(manifest.digest(), profile()).exists());
            fs::remove_dir_all(store.root()).unwrap();
        });
    }

    /// Re-pin R0c-fix-4 (R0c-fix-3 review minor 5): a store whose report a build with other mutant
    /// admission algorithms wrote at the same k-rust pin (here one before R0c-fix-4, whose campaign
    /// manifest names no admission algorithm, its digests and index entry rewritten to agree) is
    /// refused on resume, and its summary is refused too. Re-pin R0-tail (R0c-fix-4 review minor 4):
    /// so is one a build with another definition-exclusion algorithm wrote: a build before R0-tail
    /// (1ee9955), whose manifest names the three admission algorithms but no exclusion version, and a
    /// build with another exclusion version. Packet CACHE-ID: the manifest's `kink` member is kink's
    /// whole semantics identity, so so is one from a build before CACHE-ID (64b56fa: no patch
    /// admission, execution request, result schema, coverage or k-rust revision there) and one with
    /// any single component changed. Re-pin L1-2-land: the one-sided kill rule is a component
    /// (`one_sided`), so a store from a build before it (830c18e: every other component equal, none
    /// for the rule) is refused too, as is one with another version of the rule (the loop below).
    #[test]
    #[ignore = "kink"]
    fn a_report_from_another_admission_build_is_refused() {
        with_stack(|| {
            let mut stale: Vec<Stale> = vec![
                (
                    "stale-admission".into(),
                    vec![
                        "claim_removal",
                        "mutant_consistency",
                        "mutant_effect",
                        "definition_exclusion",
                        "k_rust_revision",
                        "patch_admission",
                        "execution_request",
                        "result_schema",
                        "coverage",
                        "one_sided",
                    ],
                    None,
                ),
                (
                    "stale-exclusion".into(),
                    vec![
                        "definition_exclusion",
                        "k_rust_revision",
                        "patch_admission",
                        "execution_request",
                        "result_schema",
                        "coverage",
                        "one_sided",
                    ],
                    None,
                ),
                (
                    "before-cache-id".into(),
                    vec![
                        "k_rust_revision",
                        "patch_admission",
                        "execution_request",
                        "result_schema",
                        "coverage",
                        "one_sided",
                    ],
                    None,
                ),
                ("before-one-sided".into(), vec!["one_sided"], None),
            ];
            for component in kink_campaign::KINK_IDENTITY {
                stale.push((
                    format!("other-{}", component.key),
                    Vec::new(),
                    Some((component.key, format!("{}-other", component.value))),
                ));
            }
            stale.push((
                "other-exclusion".into(),
                Vec::new(),
                Some((
                    "definition_exclusion",
                    "kink-native/definition-exclusion/v0".into(),
                )),
            ));
            stale.push((
                "later-component".into(),
                Vec::new(),
                Some(("later_algorithm", "kink/later/v1".into())),
            ));
            // One run writes the store each stale variant starts from (packet test-gate TG-P: before,
            // each variant ran the same campaign into a store of its own).
            let manifest = decode(&clean());
            let written_store = store("stale-template");
            let outcome = run_definition(&workspace(), &manifest, "clean", &written_store).unwrap();
            let entry = outcome.campaign.unwrap();
            for (name, removed, written) in stale {
                let store = copy_store(&written_store, &name);
                let root = store.profile_path(manifest.digest(), profile());
                let current = root.join("campaigns").join(format!(
                    "{}.json",
                    entry["manifest_sha256"].as_str().unwrap()
                ));
                let mut report: Value =
                    serde_json::from_str(&fs::read_to_string(&current).unwrap()).unwrap();
                let kink = report["manifest"]["kink"].as_object_mut().unwrap();
                for key in removed {
                    assert!(kink.remove(key).is_some(), "{name}: {key}");
                }
                if let Some((key, value)) = written {
                    kink.insert(key.into(), json!(value));
                }
                let digest = kink_patch::payload_digest(
                    kink_patch::CAMPAIGN_MANIFEST_DOMAIN,
                    canonical_json(&report["manifest"]).as_bytes(),
                )
                .to_string();
                report["manifest_sha256"] = json!(digest);
                let text = canonical_json(&report);
                store
                    .write_text(&root.join(format!("campaigns/{digest}.json")), &text)
                    .unwrap();
                let mut index = store.read_index(manifest.digest(), profile()).unwrap();
                index["clean"]["manifest_sha256"] = json!(digest);
                index["clean"]["report_sha256"] = json!(sha256(text.as_bytes()).to_string());
                store.write_json(&root.join("index.json"), &index).unwrap();
                let Err(refused) = run_definition(&workspace(), &manifest, "clean", &store) else {
                    panic!("{name}: the stale report is not resumed")
                };
                assert!(
                    refused.to_string().contains("admission algorithms"),
                    "{name}: {refused}"
                );
                let Err(summary) = summarize(&store, &manifest.digest().to_string(), profile())
                else {
                    panic!("{name}: the stale report is not summarized")
                };
                assert!(
                    summary.to_string().contains("admission algorithms"),
                    "{name}: {summary}"
                );
            }
        });
    }

    /// Packet CACHE-ID-fix-1 (CACHE-ID review 1 major, minors 4 and 5): a store is honoured only by
    /// the build that wrote it and only for the run options kink-corpus runs with. Each index entry
    /// names its writer's build (`kink_build`) and run options (`run_options`), and each admission
    /// record its writer's build, outside the campaign report's bytes, so the report is unchanged.
    /// An entry of another build (simulated by writing another build's identity into it, as build A
    /// would), one with no build (every store written before CACHE-ID-fix-1) and one with other or
    /// no run options are refused by resume and by summary, with every semantics-identity component
    /// equal; resume also refuses an admission record of another build, and summary reads one as
    /// missing. tests/runner.rs runs the same with two real builds. Re-pin L1-2-land: the entry
    /// records every run option (kink-campaign `RunOptions::value`), the one-sided rule's `one_sided`
    /// included, so an entry made with the rule on, and one written before the rule was recorded
    /// (`{result_modality, work}` only), are refused too.
    #[test]
    #[ignore = "kink"]
    fn a_store_of_another_build_or_other_run_options_is_refused() {
        with_stack(|| {
            let other = sha256(b"another kink build").to_string();
            let this = kink_campaign::kink_build().unwrap().to_string();
            let entries: [(&str, &str, Value); 6] = [
                ("other-build", "kink_build", json!(other)),
                ("no-build", "kink_build", Value::Null),
                (
                    "other-run-options",
                    "run_options",
                    json!({"result_modality":"path-set","work":null,"one_sided":"off"}),
                ),
                (
                    "one-sided-on",
                    "run_options",
                    json!({
                        "result_modality": "state-set",
                        "work": null,
                        "one_sided": "no-crash-classifier",
                    }),
                ),
                (
                    "run-options-before-one-sided",
                    "run_options",
                    json!({"result_modality":"state-set","work":null}),
                ),
                ("no-run-options", "run_options", Value::Null),
            ];
            // One run writes the store each variant starts from (packet test-gate TG-P: before, each
            // variant ran the same campaign into a store of its own).
            let manifest = decode(&clean());
            let written_store = store("other-build-template");
            let outcome = run_definition(&workspace(), &manifest, "clean", &written_store).unwrap();
            let entry = outcome.campaign.unwrap();
            assert_eq!(entry["kink_build"], this);
            assert_eq!(
                entry["run_options"],
                json!({"result_modality":"state-set","work":null,"one_sided":"off"})
            );
            assert_eq!(outcome.admission["kink_build"], this);
            for (name, key, value) in entries {
                let store = copy_store(&written_store, name);
                let root = store.profile_path(manifest.digest(), profile());
                let report_path = root.join("campaigns").join(format!(
                    "{}.json",
                    entry["manifest_sha256"].as_str().unwrap()
                ));
                let report = fs::read(&report_path).unwrap();
                assert!(!String::from_utf8_lossy(&report).contains(&this));
                let mut index = store.read_index(manifest.digest(), profile()).unwrap();
                if value.is_null() {
                    index["clean"].as_object_mut().unwrap().remove(key);
                } else {
                    index["clean"][key] = value;
                }
                store.write_json(&root.join("index.json"), &index).unwrap();
                let Err(refused) = run_definition(&workspace(), &manifest, "clean", &store) else {
                    panic!("{name}: resumed")
                };
                let expected = if key == "kink_build" {
                    "not by this build"
                } else {
                    "run options"
                };
                assert!(refused.to_string().contains(expected), "{name}: {refused}");
                let Err(summary) = summarize(&store, &manifest.digest().to_string(), profile())
                else {
                    panic!("{name}: summarized")
                };
                assert!(summary.to_string().contains(expected), "{name}: {summary}");
                assert_eq!(fs::read(&report_path).unwrap(), report, "{name}");
            }
            // An admission record of another build: resume refuses it, and summary reads it as
            // missing (an error/process row that scores nothing), for an admitted definition and
            // for a refused one; the same refusal record of this build is reported as written.
            let store = copy_store(&written_store, "other-admission-build");
            let root = store.profile_path(manifest.digest(), profile());
            let path = store
                .admission_path(manifest.digest(), profile(), "clean")
                .unwrap();
            let mut admission = store.read_json(&path).unwrap();
            admission["kink_build"] = json!(other);
            store.write_json(&path, &admission).unwrap();
            let Err(refused) = run_definition(&workspace(), &manifest, "clean", &store) else {
                panic!("an admission record of another build was resumed")
            };
            assert!(
                refused.to_string().contains("admission record"),
                "{refused}"
            );
            let missing = json!({"outcome":"error","stage":"process","reason":"process"});
            let summary = summarize(&store, &manifest.digest().to_string(), profile()).unwrap();
            assert_eq!(summary.value()["definitions"][0]["admission"], missing);
            assert_eq!(summary.value()["totals"]["definitions"]["admitted"], 0);
            let mut index = store.read_index(manifest.digest(), profile()).unwrap();
            index.as_object_mut().unwrap().remove("clean");
            store.write_json(&root.join("index.json"), &index).unwrap();
            admission["outcome"] = json!("refused");
            admission["stage"] = json!("compile");
            admission["reason"] = json!("forged");
            for (build, expected) in [
                (json!(other), missing),
                (
                    json!(this),
                    json!({"outcome":"refused","stage":"compile","reason":"forged"}),
                ),
            ] {
                admission["kink_build"] = build;
                store.write_json(&path, &admission).unwrap();
                let summary = summarize(&store, &manifest.digest().to_string(), profile()).unwrap();
                assert_eq!(summary.value()["definitions"][0]["admission"], expected);
            }
        });
    }
}

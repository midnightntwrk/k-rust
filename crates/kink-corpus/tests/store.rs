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
fn tiny_time_bound_is_probed_without_assuming_a_watchdog_race() {
    with_stack(|| {
        let mut value = clean();
        value["campaign"]["budget"]["time_ms"] = json!(1);
        let manifest = decode(&value);
        let store = store("tiny-time");
        let outcome = run_definition(&workspace(), &manifest, "clean", &store).unwrap();
        if let Some(entry) = outcome.campaign {
            println!(
                "CS13_TINY_TIME_BOUND_FIRED {}",
                entry["time_bound_fired"].as_bool().unwrap()
            );
            // The wall-clock race is observational, never an asserted fixture result.
        } else {
            println!(
                "CS13_TINY_TIME_BOUND_NO_CAMPAIGN {}",
                canonical_json(&outcome.admission)
            );
        }
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

#[test]
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

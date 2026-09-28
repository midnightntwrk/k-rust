//! Production collector rendering contract.

use krs_cli::{
    CargoMetadata, CollectorPlan, CollectorRuntime, DefinitionRequest, FacetSelector,
    GeneratedCollector, KrsCfg, PackageSelector, PlanningErrorKind, RegistrationMode,
};
use krs_test_support::temp_dir;
use serde_json::json;
use std::fs;
use std::path::PathBuf;
use std::time::{Duration, SystemTime};

#[test]
fn production_collector_owns_the_complete_collection_entrypoint() {
    let metadata = CargoMetadata::from_json(
        &serde_json::to_vec(&json!({
            "packages": [{
                "id": "language 0.1.0 (path+file:///language)",
                "name": "language",
                "version": "0.1.0",
                "source": null,
                "manifest_path": "/language/Cargo.toml",
                "metadata": {
                    "krs": {
                        "k-namespace": "ORG-EXAMPLE-LANGUAGE",
                        "definitions": { "main": {} }
                    }
                },
                "targets": [{
                    "name": "language",
                    "kind": ["lib"],
                    "crate_types": ["lib"]
                }]
            }],
            "resolve": { "nodes": [{
                "id": "language 0.1.0 (path+file:///language)",
                "features": [],
                "dependencies": []
            }] },
            "workspace_members": ["language 0.1.0 (path+file:///language)"]
        }))
        .unwrap(),
    )
    .unwrap();
    let plan = CollectorPlan::resolve_definition(
        &metadata,
        &DefinitionRequest {
            root: FacetSelector {
                package: PackageSelector::Name("language".to_owned()),
                definition: "main".to_owned(),
            },
            dependencies: Vec::new(),
            host_target: "x86_64-unknown-linux-gnu".to_owned(),
            cfg: Vec::new(),
        },
        CollectorRuntime {
            host_manifest: PathBuf::from("/tool/krs/Cargo.toml"),
            compiler_manifest: PathBuf::from("/tool/krs-compiler/Cargo.toml"),
        },
    )
    .unwrap();
    assert!(plan.is_production());

    let generated = GeneratedCollector::from_plan(&plan).unwrap();
    assert_cargo_config(&plan, &generated);
    let manifest = String::from_utf8(generated.manifest).unwrap();
    let source = String::from_utf8(generated.main_source).unwrap();
    let selection = String::from_utf8(generated.canonical_selection).unwrap();

    assert!(manifest.contains("__krs_host_runtime = { package = \"krs\""));
    assert!(manifest.contains("__krs_compiler_runtime = { package = \"krs-compiler\""));
    assert!(manifest.ends_with("\n[workspace]\n\n[profile.dev]\ndebug = 0\n"));
    let package_name = manifest
        .lines()
        .find(|line| line.starts_with("name = "))
        .unwrap();
    assert!(package_name.starts_with("name = \"krs-generated-collector-"));
    assert_ne!(package_name, "name = \"krs-generated-collector\"");
    assert!(source.contains("__krs_host_runtime::host_descriptors()"));
    assert!(source.contains("__krs_host_runtime::builtin_registry,"));
    assert!(source.contains("__krs_compiler_runtime::run_collector("));
    assert!(!source.contains("SELECTED_FACETS"));
    assert!(!selection.contains("/language"));
    assert!(!selection.contains("/tool"));

    let mut alternate_metadata = metadata;
    alternate_metadata.packages[0].metadata["krs"]["k-namespace"] = json!("ORG-EXAMPLE-ALTERNATE");
    let alternate_plan = CollectorPlan::resolve_definition(
        &alternate_metadata,
        &DefinitionRequest {
            root: FacetSelector {
                package: PackageSelector::Name("language".to_owned()),
                definition: "main".to_owned(),
            },
            dependencies: Vec::new(),
            host_target: "x86_64-unknown-linux-gnu".to_owned(),
            cfg: Vec::new(),
        },
        CollectorRuntime {
            host_manifest: PathBuf::from("/tool/krs/Cargo.toml"),
            compiler_manifest: PathBuf::from("/tool/krs-compiler/Cargo.toml"),
        },
    )
    .unwrap();
    let alternate_manifest = String::from_utf8(
        GeneratedCollector::from_plan(&alternate_plan)
            .unwrap()
            .manifest,
    )
    .unwrap();
    let alternate_package_name = alternate_manifest
        .lines()
        .find(|line| line.starts_with("name = "))
        .unwrap();
    assert_ne!(package_name, alternate_package_name);
}

fn assert_cargo_config(plan: &CollectorPlan, generated: &GeneratedCollector) {
    let cargo_config = String::from_utf8(generated.cargo_config.clone()).unwrap();
    assert!(cargo_config.contains("target = \"x86_64-unknown-linux-gnu\""));
    assert!(cargo_config.contains("rustflags = []"));
    let mut cfg_plan = plan.clone();
    cfg_plan.cfg.push(KrsCfg {
        key: "backend".to_owned(),
        value: Some("llvm".to_owned()),
    });
    let cfg_config = String::from_utf8(
        GeneratedCollector::from_plan(&cfg_plan)
            .unwrap()
            .cargo_config,
    )
    .unwrap();
    assert!(cfg_config.contains("--check-cfg=cfg(backend,values(\\\"llvm\\\"))"));
    assert!(cfg_config.contains("--cfg=backend=\\\"llvm\\\""));
}

fn explicit_metadata(krs_features: &[&str], helper: bool) -> CargoMetadata {
    let language = "language 0.1.0 (path+file:///language)";
    let facade = "krs 0.1.0 (path+file:///tool/krs)";
    let helper_id = "helper 0.1.0 (path+file:///helper)";
    let mut packages = vec![
        json!({
            "id": language,
            "name": "language",
            "version": "0.1.0",
            "source": null,
            "manifest_path": "/language/Cargo.toml",
            "metadata": {
                "krs": {
                    "k-namespace": "ORG-EXAMPLE-LANGUAGE",
                    "definitions": { "main": {} }
                }
            },
            "targets": [{ "name": "language", "kind": ["lib"], "crate_types": ["lib"] }]
        }),
        json!({
            "id": facade,
            "name": "krs",
            "version": "0.1.0",
            "source": null,
            "manifest_path": "/tool/krs/Cargo.toml",
            "targets": [{ "name": "krs", "kind": ["lib"], "crate_types": ["lib"] }]
        }),
    ];
    let mut language_dependencies = vec![facade];
    let mut nodes = vec![json!({ "id": facade, "features": krs_features, "dependencies": [] })];
    if helper {
        packages.push(json!({
            "id": helper_id,
            "name": "helper",
            "version": "0.1.0",
            "source": null,
            "manifest_path": "/helper/Cargo.toml",
            "targets": [{ "name": "helper", "kind": ["lib"], "crate_types": ["lib"] }]
        }));
        nodes.push(json!({ "id": helper_id, "features": [], "dependencies": [facade] }));
        language_dependencies.push(helper_id);
    }
    nodes.push(json!({ "id": language, "features": [], "dependencies": language_dependencies }));
    CargoMetadata::from_json(
        &serde_json::to_vec(&json!({
            "packages": packages,
            "resolve": { "nodes": nodes },
            "workspace_members": [language]
        }))
        .unwrap(),
    )
    .unwrap()
}

fn explicit_plan(metadata: &CargoMetadata) -> CollectorPlan {
    CollectorPlan::resolve_definition(
        metadata,
        &DefinitionRequest {
            root: FacetSelector {
                package: PackageSelector::Name("language".to_owned()),
                definition: "main".to_owned(),
            },
            dependencies: Vec::new(),
            host_target: "x86_64-unknown-linux-gnu".to_owned(),
            cfg: Vec::new(),
        },
        CollectorRuntime {
            host_manifest: PathBuf::from("/tool/krs/Cargo.toml"),
            compiler_manifest: PathBuf::from("/tool/krs-compiler/Cargo.toml"),
        },
    )
    .unwrap()
}

#[test]
fn explicit_registration_collector_reads_semantics_tables_without_inventory() {
    let plan = explicit_plan(&explicit_metadata(&[], false));
    assert_eq!(plan.registration(), RegistrationMode::Inventory);
    let inventory = GeneratedCollector::from_plan(&plan).unwrap();

    let plan = plan.with_explicit_registration().unwrap();
    assert_eq!(plan.registration(), RegistrationMode::Explicit);
    let generated = GeneratedCollector::from_plan(&plan).unwrap();
    let manifest = String::from_utf8(generated.manifest.clone()).unwrap();
    let source = String::from_utf8(generated.main_source.clone()).unwrap();

    assert!(manifest.contains(
        "__krs_host_runtime = { package = \"krs\", path = \"/tool/krs\", default-features = false }"
    ));
    assert!(manifest.contains(
        "__krs_compiler_runtime = { package = \"krs-compiler\", path = \"/tool/krs-compiler\" }"
    ));
    assert!(source.contains(
        "let tables: &[&__krs_host_runtime::__private::RegistrationTable] = &[\n        &language::__KRS_REGISTRATIONS,\n    ];\n"
    ));
    assert!(source.contains("__krs_host_runtime::host_descriptors_from(tables)"));
    assert!(!source.contains("host_descriptors()"));
    assert_eq!(generated.canonical_selection, inventory.canonical_selection);
    assert_ne!(generated.main_source, inventory.main_source);
}

#[test]
fn explicit_registration_rejects_an_active_inventory_feature() {
    let plan = explicit_plan(&explicit_metadata(&["default", "inventory"], false));
    let error = plan.with_explicit_registration().unwrap_err();
    assert_eq!(error.kind(), PlanningErrorKind::InventoryFeatureActive);
}

#[test]
fn explicit_registration_rejects_an_unselected_krs_dependent() {
    let plan = explicit_plan(&explicit_metadata(&[], true));
    let error = plan.with_explicit_registration().unwrap_err();
    assert_eq!(error.kind(), PlanningErrorKind::UnregisteredKrsDependent);
    assert!(error.to_string().contains("helper 0.1.0"));
}

#[test]
fn writing_an_unchanged_collector_preserves_generated_file_mtimes() {
    let temporary = temp_dir();
    let output = temporary.path().join("collector");
    let generated =
        GeneratedCollector::from_plan(&explicit_plan(&explicit_metadata(&[], false))).unwrap();
    generated.write_to(&output).unwrap();

    let files = [
        ".krs-collector",
        "Cargo.toml",
        "src/main.rs",
        ".cargo/config.toml",
        "krs-selection.json",
    ];
    let old = SystemTime::UNIX_EPOCH + Duration::from_secs(1_700_000_000);
    for file in files {
        fs::OpenOptions::new()
            .write(true)
            .open(output.join(file))
            .unwrap()
            .set_modified(old)
            .unwrap();
    }

    generated.write_to(&output).unwrap();
    for file in files {
        assert_eq!(
            fs::metadata(output.join(file)).unwrap().modified().unwrap(),
            old,
            "{file}"
        );
    }
}

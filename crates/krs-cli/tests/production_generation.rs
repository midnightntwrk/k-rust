//! Production collector rendering contract.

use krs_cli::{
    CargoMetadata, CollectorPlan, CollectorRuntime, DefinitionRequest, FacetSelector,
    GeneratedCollector, PackageSelector,
};
use serde_json::json;
use std::path::PathBuf;

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
    let manifest = String::from_utf8(generated.manifest).unwrap();
    let source = String::from_utf8(generated.main_source).unwrap();
    let selection = String::from_utf8(generated.canonical_selection).unwrap();

    assert!(manifest.contains("__krs_host_runtime = { package = \"krs\""));
    assert!(manifest.contains("__krs_compiler_runtime = { package = \"krs-compiler\""));
    let package_name = manifest
        .lines()
        .find(|line| line.starts_with("name = "))
        .unwrap();
    assert!(package_name.starts_with("name = \"krs-generated-collector-"));
    assert_ne!(package_name, "name = \"krs-generated-collector\"");
    assert!(source.contains("__krs_host_runtime::host_descriptors()"));
    assert!(source.contains("__krs_host_runtime::builtin_registry()"));
    assert!(source.contains("__krs_compiler_runtime::collect_host_descriptors_with_builtins("));
    assert!(source.contains("bundle.to_canonical_json()"));
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

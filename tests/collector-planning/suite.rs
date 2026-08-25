use krs_cli::{
    CargoMetadata, CollectorEntrypoint, CollectorPlan, CollectorRequest, FacetSelector,
    GeneratedCollector, KrsCfg, PackageSelector, PlanningErrorKind,
};
use serde_json::json;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

const ROOT_ID: &str = "fixture-root 0.1.0 (path+fixture/root)";
const SAME_A_ID: &str = "same-name 0.1.0 (path+fixture/same-dash)";
const SAME_B_ID: &str = "same-name 0.1.0 (path+fixture/same-underscore)";
const RUNTIME_ID: &str = "mock-collector 0.1.0 (path+fixture/mock-collector)";

#[test]
fn reordered_metadata_and_requests_generate_identical_bytes() {
    let normal = plan(false);
    let reordered = plan(true);

    assert_eq!(normal.facets, reordered.facets);
    assert_eq!(normal.package_closure, reordered.package_closure);
    assert_eq!(
        normal.canonical_selection_json().unwrap(),
        reordered.canonical_selection_json().unwrap()
    );
    assert_eq!(
        GeneratedCollector::from_plan(&normal).unwrap(),
        GeneratedCollector::from_plan(&reordered).unwrap()
    );
}

#[test]
fn aliases_collisions_and_dependency_only_facets_are_explicit() {
    let plan = plan(false);
    let generated = GeneratedCollector::from_plan(&plan).unwrap();
    let manifest = String::from_utf8(generated.manifest).unwrap();
    let source = String::from_utf8(generated.main_source).unwrap();

    assert!(manifest.contains("same_name__1 = { package = \"same-name\""));
    assert!(manifest.contains("same_name__2 = { package = \"same-name\""));
    assert!(manifest.contains("features = [\"default\", \"verification\"]"));
    assert!(source.contains("extern crate same_name__1 as _;"));
    assert!(source.contains("extern crate same_name__2 as _;"));
    assert!(source.contains("\"ORG-EXAMPLE-SAME-A\", \"core\""));
    assert!(source.contains("\"ORG-EXAMPLE-SAME-B\", \"core\""));
    assert_eq!(source.matches("mock_collector::collect(").count(), 1);
}

#[test]
fn canonical_selection_is_path_free_while_build_manifest_uses_paths() {
    let fixture = fixture_root();
    let generated = GeneratedCollector::from_plan(&plan(false)).unwrap();
    let canonical = String::from_utf8(generated.canonical_selection).unwrap();
    let manifest = String::from_utf8(generated.manifest).unwrap();

    assert!(!canonical.contains(fixture.to_string_lossy().as_ref()));
    assert!(manifest.contains(fixture.to_string_lossy().as_ref()));
    assert!(canonical.contains("\"verification\""));
    assert!(canonical.contains("\"k_backend\""));
}

#[test]
fn host_target_and_cfg_are_explicit_build_inputs() {
    let generated = GeneratedCollector::from_plan(&plan(false)).unwrap();
    let config = String::from_utf8(generated.cargo_config).unwrap();
    let manifest = String::from_utf8(generated.manifest).unwrap();

    assert!(config.contains("target = \"x86_64-unknown-linux-gnu\""));
    assert!(config.contains("--cfg=k_backend=\\\"llvm\\\""));
    assert!(config.contains("--cfg=krs_test"));
    assert!(manifest.contains("host-only = true"));
}

#[test]
fn missing_and_ambiguous_selections_are_rejected() {
    let metadata = metadata(false);
    let mut ambiguous = request(false);
    ambiguous.root.package = PackageSelector::Name("same-name".into());
    assert_eq!(
        CollectorPlan::resolve(&metadata, &ambiguous)
            .unwrap_err()
            .kind(),
        PlanningErrorKind::AmbiguousPackage
    );

    let mut missing_definition = request(false);
    missing_definition.root.definition = "absent".into();
    assert_eq!(
        CollectorPlan::resolve(&metadata, &missing_definition)
            .unwrap_err()
            .kind(),
        PlanningErrorKind::MissingDefinition
    );

    let mut missing_package = request(false);
    missing_package.dependencies.push(FacetSelector {
        package: PackageSelector::Name("missing-package".into()),
        definition: "core".into(),
    });
    assert_eq!(
        CollectorPlan::resolve(&metadata, &missing_package)
            .unwrap_err()
            .kind(),
        PlanningErrorKind::MissingPackage
    );
}

#[test]
fn generated_fixture_collector_compiles_and_reserves_stdout_for_protocol() {
    let output_directory = temporary_directory();
    let generated = GeneratedCollector::from_plan(&plan_for_current_host()).unwrap();
    generated.write_to(&output_directory).unwrap();

    let output = Command::new("cargo")
        .args(["run", "--quiet", "--offline"])
        .current_dir(&output_directory)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "generated collector failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"{\"protocol\":2,\"selected_facets\":3}\n");
    assert!(output.stderr.is_empty());

    fs::remove_dir_all(output_directory).unwrap();
}

fn plan(reordered: bool) -> CollectorPlan {
    CollectorPlan::resolve(&metadata(reordered), &request(reordered)).unwrap()
}

fn plan_for_current_host() -> CollectorPlan {
    let mut request = request(false);
    request.host_target = host_target();
    CollectorPlan::resolve(&metadata(false), &request).unwrap()
}

fn request(reordered: bool) -> CollectorRequest {
    let mut dependencies = vec![
        FacetSelector {
            package: PackageSelector::Id(SAME_A_ID.into()),
            definition: "core".into(),
        },
        FacetSelector {
            package: PackageSelector::Id(SAME_B_ID.into()),
            definition: "core".into(),
        },
    ];
    let mut cfg = vec![
        KrsCfg {
            key: "k_backend".into(),
            value: Some("llvm".into()),
        },
        KrsCfg {
            key: "krs_test".into(),
            value: None,
        },
    ];
    if reordered {
        dependencies.reverse();
        cfg.reverse();
    }
    CollectorRequest {
        root: FacetSelector {
            package: PackageSelector::Id(ROOT_ID.into()),
            definition: "main".into(),
        },
        dependencies,
        entrypoint: CollectorEntrypoint {
            package: PackageSelector::Id(RUNTIME_ID.into()),
            function: vec!["collect".into()],
        },
        host_target: "x86_64-unknown-linux-gnu".into(),
        cfg,
    }
}

fn metadata(reordered: bool) -> CargoMetadata {
    let fixture = fixture_root();
    let package = |id: &str,
                   name: &str,
                   directory: &str,
                   namespace: Option<&str>,
                   definition: Option<serde_json::Value>| {
        let target_name = if id == ROOT_ID {
            "custom_semantics_root".to_owned()
        } else {
            name.replace('-', "_")
        };
        let metadata = match (namespace, definition) {
            (Some(namespace), Some(definition)) => json!({
                "krs": {
                    "k-namespace": namespace,
                    "definitions": definition
                }
            }),
            _ => json!({}),
        };
        json!({
            "id": id,
            "name": name,
            "version": "0.1.0",
            "source": null,
            "manifest_path": fixture.join(directory).join("Cargo.toml"),
            "metadata": metadata,
            "targets": [{
                "name": target_name,
                "kind": ["lib"],
                "crate_types": ["lib"]
            }]
        })
    };
    let mut packages = vec![
        package(
            ROOT_ID,
            "fixture-root",
            "root",
            Some("ORG-EXAMPLE-ROOT"),
            Some(json!({ "main": { "root": "crate", "syntax-root": "crate::syntax" } })),
        ),
        package(
            SAME_A_ID,
            "same-name",
            "same-dash",
            Some("ORG-EXAMPLE-SAME-A"),
            Some(json!({ "core": { "root": "crate" } })),
        ),
        package(
            SAME_B_ID,
            "same-name",
            "same-underscore",
            Some("ORG-EXAMPLE-SAME-B"),
            Some(json!({ "core": {} })),
        ),
        package(RUNTIME_ID, "mock-collector", "mock-collector", None, None),
    ];
    let mut root_dependencies = vec![SAME_A_ID, SAME_B_ID, RUNTIME_ID];
    let mut same_a_features = vec!["verification", "default"];
    let mut nodes = vec![
        json!({ "id": ROOT_ID, "features": ["root-feature"], "dependencies": root_dependencies.clone() }),
        json!({ "id": SAME_A_ID, "features": same_a_features.clone(), "dependencies": [] }),
        json!({ "id": SAME_B_ID, "features": [], "dependencies": [] }),
        json!({ "id": RUNTIME_ID, "features": [], "dependencies": [] }),
    ];
    if reordered {
        packages.reverse();
        root_dependencies.reverse();
        same_a_features.reverse();
        nodes.reverse();
        // Rebuild the affected node so its internal arrays are reordered too.
        nodes.retain(|node| node["id"] != ROOT_ID && node["id"] != SAME_A_ID);
        nodes.push(json!({ "id": ROOT_ID, "features": ["root-feature"], "dependencies": root_dependencies }));
        nodes.push(json!({ "id": SAME_A_ID, "features": same_a_features, "dependencies": [] }));
    }
    CargoMetadata::from_json(
        &serde_json::to_vec(&json!({
            "packages": packages,
            "resolve": { "nodes": nodes },
            "workspace_members": [ROOT_ID]
        }))
        .unwrap(),
    )
    .unwrap()
}

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/collector-planning/fixtures")
        .canonicalize()
        .unwrap()
}

fn host_target() -> String {
    let output = Command::new("rustc").arg("-vV").output().unwrap();
    assert!(output.status.success());
    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .unwrap()
        .to_owned()
}

fn temporary_directory() -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let unique = NEXT.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "krs-collector-planning-{}-{unique}",
        std::process::id()
    ))
}

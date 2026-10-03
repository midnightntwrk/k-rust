use krs_cli::{
    CargoMetadata, CollectorEntrypoint, CollectorPlan, CollectorRequest, FacetSelector,
    GeneratedCollector, KrsCfg, PackageSelector, PlanningErrorKind, RegistrationMode,
};
use krs_test_support::{fixture_build_env, shared_fixture_target};
use serde_json::json;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use toml_edit::DocumentMut;

const ROOT_ID: &str = "fixture-root 0.1.0 (path+fixture/root)";
const SAME_A_ID: &str = "same-name 0.1.0 (path+fixture/same-dash)";
const SAME_B_ID: &str = "same-name 0.1.0 (path+fixture/same-underscore)";
const RUNTIME_ID: &str = "mock-collector 0.1.0 (path+fixture/mock-collector)";

#[test]
fn reordered_metadata_and_requests_generate_identical_bytes() {
    let normal = plan(false);
    let reordered = plan(true);

    assert!(!normal.is_production());
    assert_eq!(normal.registration(), RegistrationMode::Inventory);
    assert_eq!(
        normal
            .clone()
            .with_explicit_registration()
            .unwrap_err()
            .kind(),
        PlanningErrorKind::InvalidRegistrationMode
    );
    assert_eq!(normal.facets(), reordered.facets());
    assert_eq!(normal.package_closure(), reordered.package_closure());
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

    let config: DocumentMut = config.parse().unwrap();
    assert_eq!(
        config["build"]["target"].as_str(),
        Some("x86_64-unknown-linux-gnu")
    );
    let flags = config["build"]["rustflags"].as_array().unwrap();
    assert_eq!(
        flags
            .iter()
            .map(|flag| flag.as_str().unwrap())
            .collect::<Vec<_>>(),
        [
            "--check-cfg=cfg(k_backend,values(\"llvm\"))",
            "--check-cfg=cfg(krs_test)",
            "--cfg=k_backend=\"llvm\"",
            "--cfg=krs_test",
        ]
    );
    assert!(manifest.contains("host-only = true"));
}

#[test]
fn reserved_package_names_receive_rust_aliases() {
    let mut metadata = metadata(false);
    for name in ["gen", "try"] {
        let id = format!("{name} 0.1.0 (path+fixture/{name})");
        metadata.packages.push(
            serde_json::from_value(json!({
                "id": id,
                "name": name,
                "version": "0.1.0",
                "source": null,
                "manifest_path": format!("/fixture/{name}/Cargo.toml"),
                "metadata": {"krs": {
                    "k-namespace": format!("ORG-EXAMPLE-{}", name.to_ascii_uppercase()),
                    "definitions": {"core": {}}
                }},
                "targets": [{"name": name, "kind": ["lib"], "crate_types": ["lib"]}]
            }))
            .unwrap(),
        );
        metadata.resolve.as_mut().unwrap().nodes.push(
            serde_json::from_value(json!({
                "id": id, "features": [], "dependencies": []
            }))
            .unwrap(),
        );
        metadata
            .resolve
            .as_mut()
            .unwrap()
            .nodes
            .iter_mut()
            .find(|node| node.id == ROOT_ID)
            .unwrap()
            .dependencies
            .push(id.clone());
    }
    let mut request = request(false);
    for name in ["gen", "try"] {
        request.dependencies.push(FacetSelector {
            package: PackageSelector::Name(name.to_owned()),
            definition: "core".to_owned(),
        });
    }
    let generated =
        GeneratedCollector::from_plan(&CollectorPlan::resolve(&metadata, &request).unwrap())
            .unwrap();
    let manifest = String::from_utf8(generated.manifest).unwrap();
    let source = String::from_utf8(generated.main_source).unwrap();
    for name in ["gen", "try"] {
        assert!(manifest.contains(&format!("pkg_{name} = {{ package = \"{name}\"")));
        assert!(source.contains(&format!("extern crate pkg_{name} as _;")));
    }
    syn::parse_file(&source).unwrap();
}

#[test]
fn control_character_round_trips_through_generated_rust_and_toml() {
    let control = '\u{0008}';
    let definition = format!("main{control}");
    let mut metadata = metadata(false);
    let root = metadata
        .packages
        .iter_mut()
        .find(|package| package.id == ROOT_ID)
        .unwrap();
    root.manifest_path = format!("/fixture/root{control}/Cargo.toml");
    root.metadata["krs"]["definitions"]
        .as_object_mut()
        .unwrap()
        .insert(definition.clone(), json!({"root": "crate"}));
    let mut request = request(false);
    request.root.definition = definition.clone();
    let generated =
        GeneratedCollector::from_plan(&CollectorPlan::resolve(&metadata, &request).unwrap())
            .unwrap();
    let source = String::from_utf8(generated.main_source).unwrap();
    let parsed = syn::parse_file(&source).unwrap();
    let selected = parsed
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == "SELECTED_FACETS" => Some(item),
            _ => None,
        })
        .unwrap();
    let syn::Expr::Reference(reference) = selected.expr.as_ref() else {
        panic!("expected selected facets reference")
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("expected selected facets array")
    };
    let syn::Expr::Tuple(tuple) = array.elems.first().unwrap() else {
        panic!("expected selected facet tuple")
    };
    let syn::Expr::Lit(literal) = &tuple.elems[1] else {
        panic!("expected definition literal")
    };
    let syn::Lit::Str(literal) = &literal.lit else {
        panic!("expected string literal")
    };
    assert_eq!(literal.value(), definition);

    let manifest = String::from_utf8(generated.manifest).unwrap();
    let manifest: DocumentMut = manifest.parse().unwrap();
    assert_eq!(
        manifest["dependencies"]["fixture_root"]["path"].as_str(),
        Some(format!("/fixture/root{control}").as_str())
    );
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
    let target = shared_fixture_target();
    let output_directory = temporary_directory();
    let generated = GeneratedCollector::from_plan(&plan_for_current_host()).unwrap();
    generated.write_to(&output_directory).unwrap();

    let mut command = Command::new("cargo");
    fixture_build_env(&mut command, target.path());
    let output = command
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

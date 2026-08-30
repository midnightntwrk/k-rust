use std::{fs, path::Path};

use toml::Value;

#[test]
fn z3_acquisition_is_feature_selectable() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let workspace = manifest(&root.join("Cargo.toml"));
    let frontend = manifest(&root.join("crates/k-rust/Cargo.toml"));
    let backend = manifest(&root.join("crates/k-rust-backend/Cargo.toml"));

    let z3 = &workspace["workspace"]["dependencies"]["z3"];
    assert_eq!(z3["default-features"].as_bool(), Some(false));
    assert!(
        z3.get("features").is_none(),
        "the workspace dependency must not impose an acquisition mode: {z3:#?}"
    );

    let frontend_features = frontend["features"].as_table().unwrap();
    assert_feature(
        frontend_features,
        "default",
        &["cli", "z3-inference-gh-release"],
    );
    assert_feature(
        frontend_features,
        "cli",
        &["dep:clap", "mpfr-folding", "z3-inference"],
    );
    assert_feature(
        frontend_features,
        "z3-inference",
        &["dep:z3", "k-rust-backend/z3"],
    );
    assert_feature(
        frontend_features,
        "z3-inference-gh-release",
        &[
            "z3-inference",
            "z3/gh-release",
            "k-rust-backend/z3-gh-release",
        ],
    );

    let backend_features = backend["features"].as_table().unwrap();
    assert_feature(backend_features, "z3", &["dep:z3"]);
    assert_feature(backend_features, "z3-gh-release", &["z3", "z3/gh-release"]);

    for (name, features) in [
        ("frontend z3-inference", &frontend_features["z3-inference"]),
        ("frontend cli", &frontend_features["cli"]),
        ("backend z3", &backend_features["z3"]),
    ] {
        let features = strings(features);
        assert!(
            features.iter().all(|feature| !is_acquisition(feature)),
            "system feature {name} selects an acquisition mode: {features:?}"
        );
    }
}

fn manifest(path: &Path) -> Value {
    fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("could not read {}: {error}", path.display()))
        .parse()
        .unwrap_or_else(|error| panic!("could not parse {}: {error}", path.display()))
}

fn assert_feature(table: &toml::Table, name: &str, expected: &[&str]) {
    assert_eq!(strings(&table[name]), expected, "feature {name}");
}

fn strings(value: &Value) -> Vec<&str> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|value| value.as_str().unwrap())
        .collect()
}

fn is_acquisition(feature: &str) -> bool {
    ["gh-release", "bundled", "vendored", "vcpkg"]
        .iter()
        .any(|mode| feature.contains(mode))
}

use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

use toml::Value;

const MANIFEST: &str = include_str!("../../../scripts/reference-differential.toml");
const SECTIONS: [&str; 5] = ["compile", "kast", "execution", "proof", "rpc"];

#[test]
fn differential_manifest_is_complete_and_unambiguous() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    assert_eq!(manifest["version"].as_integer(), Some(1));

    let reference = manifest["reference"].as_table().expect("reference pins");
    for pin in [
        "k",
        "imp",
        "wasm",
        "evm-equivalence",
        "kevm",
        "kevm-plugin",
        "mir",
    ] {
        let revision = reference[pin]["revision"]
            .as_str()
            .expect("revision string");
        assert_eq!(revision.len(), 40, "{pin} must use a full Git revision");
        assert!(
            revision.bytes().all(|byte| byte.is_ascii_hexdigit()),
            "{pin} must use a hexadecimal Git revision"
        );
    }
    assert!(
        reference["k"]["version"]
            .as_str()
            .is_some_and(|version| !version.is_empty()),
        "K must have a pinned release version"
    );

    let allowed_requirements = BTreeSet::from(["reference-toolchain"]);
    for section in SECTIONS {
        let entries = manifest[section].as_array().expect("coverage array");
        assert!(!entries.is_empty(), "{section} coverage must not be empty");
        let mut names = BTreeSet::new();
        for entry in entries {
            let name = entry["name"].as_str().expect("coverage name");
            assert!(names.insert(name), "duplicate {section} case {name}");
            let requirements = entry["requires"].as_array().expect("case requirements");
            assert!(
                !requirements.is_empty(),
                "{section} case {name} has no requirement"
            );
            for requirement in requirements {
                let requirement = requirement.as_str().expect("string requirement");
                assert!(
                    allowed_requirements.contains(requirement),
                    "unknown requirement {requirement} on {section} case {name}"
                );
            }
            assert!(
                entry["constructs"].as_array().is_some(),
                "{section} case {name} has no construct classification"
            );
        }
    }

    for entry in manifest["compile"].as_array().unwrap() {
        assert!(
            entry["comparisons"]
                .as_array()
                .is_some_and(|comparisons| !comparisons.is_empty()),
            "every compile case must declare compared artifacts"
        );
    }

    let mut paths = BTreeSet::new();
    collect_workspace_paths(&manifest, &mut paths);
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    for relative in paths {
        let path = workspace.join(&relative);
        assert!(
            path.exists(),
            "workspace fixture does not exist: {}",
            path.display()
        );
    }

    let mut constructs = BTreeSet::new();
    for section in SECTIONS {
        for entry in manifest[section].as_array().unwrap() {
            let blocked = entry["requires"]
                .as_array()
                .unwrap()
                .iter()
                .any(|requirement| requirement.as_str() == Some("semantics-support"));
            if !blocked {
                constructs.extend(
                    entry["constructs"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|construct| construct.as_str().expect("string construct")),
                );
            }
        }
    }
    let required_constructs = BTreeSet::from([
        "bounded-search",
        "collections",
        "crypto-hook",
        "deep-term",
        "macro-runtime",
        "owise",
        "star-cell-variable",
    ]);
    let missing = required_constructs
        .difference(&constructs)
        .copied()
        .collect::<Vec<_>>();
    assert!(
        missing.is_empty(),
        "missing runnable corpus constructs: {missing:?}"
    );
}

fn collect_workspace_paths(value: &Value, output: &mut BTreeSet<PathBuf>) {
    match value {
        Value::String(value) => {
            if let Some(relative) = value.strip_prefix("${workspace}/") {
                output.insert(PathBuf::from(relative));
            }
        }
        Value::Array(values) => {
            for value in values {
                collect_workspace_paths(value, output);
            }
        }
        Value::Table(values) => {
            for value in values.values() {
                collect_workspace_paths(value, output);
            }
        }
        Value::Integer(_) | Value::Float(_) | Value::Boolean(_) | Value::Datetime(_) => {}
    }
}

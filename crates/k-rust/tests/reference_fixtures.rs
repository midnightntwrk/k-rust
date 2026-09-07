use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use sha2::{Digest, Sha256};
use toml::Value;

const SUBSYSTEM_REGISTRY: &str = include_str!("../../../scripts/conformance/subsystems.toml");

#[test]
fn reference_fixture_manifests_are_consistent() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference");
    let mut found = BTreeSet::new();
    let registry = SUBSYSTEM_REGISTRY.parse::<Value>().unwrap();
    let mut owners = BTreeSet::new();
    let mut homes = BTreeSet::new();
    for row in registry["subsystem"].as_array().unwrap() {
        assert!(
            owners.insert(row["name"].as_str().unwrap()),
            "duplicate subsystem owner"
        );
        assert!(!row["source_pattern"].as_str().unwrap().is_empty());
        for home in row["fixture_homes"].as_array().unwrap() {
            assert!(
                homes.insert(home.as_str().unwrap()),
                "fixture home has multiple default owners"
            );
        }
    }

    assert!(root.join("README.md").is_file());

    for &subsystem in &homes {
        let directory = root.join(subsystem);
        assert!(
            directory.join("README.md").is_file(),
            "reference/{subsystem} must have a README.md"
        );
        let manifests = find_named(&directory, "reference.toml");
        assert!(
            !manifests.is_empty(),
            "no reference.toml under reference/{subsystem}"
        );
        for manifest in manifests {
            check_manifest(&root, subsystem, &manifest);
            found.insert(subsystem);
        }
    }

    assert_eq!(found, homes);
    for definition in find_named(&root, "definition.kore") {
        let mut directory = definition.parent().unwrap();
        let manifest_path = loop {
            let candidate = directory.join("reference.toml");
            if candidate.is_file() {
                break candidate;
            }
            directory = directory.parent().unwrap_or_else(|| {
                panic!(
                    "committed definition.kore has no reference.toml: {}",
                    definition.display()
                )
            });
            assert!(directory.starts_with(&root));
        };
        let manifest = fs::read_to_string(&manifest_path)
            .unwrap()
            .parse::<Value>()
            .unwrap();
        assert_eq!(manifest["backend_isolation"].as_bool(), Some(true));
        assert!(
            manifest["backend_isolation_reason"]
                .as_str()
                .is_some_and(|reason| !reason.trim().is_empty()),
            "{} must justify its committed definition.kore",
            manifest_path.display()
        );
    }
}

#[test]
fn census_distinguishes_explicit_markers_from_reference_mentions() {
    let workspace = temporary_directory("reference-census");
    let test_directory = workspace.join("crates/k-rust/tests");
    fs::create_dir_all(&test_directory).unwrap();
    fs::write(
        test_directory.join("cli.rs"),
        concat!(
            "\n#",
            r#"[test]
fn reference_named_case() {
    assert!(true);
}

"#,
            "#",
            r#"[test]
fn comment_marked_case() {
    // reference: kore-exec fixture.kore
    assert!(true);
}

"#,
            "#",
            r#"[test]
fn mention_without_a_marker() {
    assert_eq!("reference backend", "reference backend");
}

"#,
            "#",
            r#"[test]
fn marker_after_the_first_body_line_does_not_count() {
    let answer = 1;
    // reference: kore-exec is mentioned too late to be a marker
    assert_eq!(answer, 1);
}
"#,
            "#",
            r#"[test]
fn reference_search_fixture_is_attributed_to_the_backend() {
    assert!("fixtures/reference/search/sd/depth-two.kore".ends_with(".kore"));
}
"#,
        ),
    )
    .unwrap();
    fs::write(
        test_directory.join("module_to_kore.rs"),
        concat!(
            "#",
            r#"[test]
fn reference_emission_uses_a_shared_kompile_fixture() {
    assert!("fixtures/reference/kompile/assoc-strict/attributes.toml".ends_with(".toml"));
}
"#
        ),
    )
    .unwrap();
    let output_path = workspace.join("census.toml");
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let output = Command::new("python3")
        .arg(repository.join("scripts/conformance/test-corpus.py"))
        .args(["--workspace", workspace.to_str().unwrap()])
        .args(["--output", output_path.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let census = fs::read_to_string(&output_path)
        .unwrap()
        .parse::<Value>()
        .unwrap();
    assert_eq!(census["totals"]["tests"].as_integer(), Some(6));
    assert_eq!(census["totals"]["reference_marked"].as_integer(), Some(4));
    assert_eq!(census["totals"]["mentions_reference"].as_integer(), Some(5));
    let cli = census["subsystem"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["name"].as_str() == Some("cli-rpc"))
        .unwrap();
    assert_eq!(cli["reference_marked"].as_integer(), Some(2));
    assert_eq!(cli["mentions_reference"].as_integer(), Some(3));
    assert_eq!(cli["has_reference_derived_test"].as_bool(), Some(true));
    assert_eq!(cli["reference_marked_tests"].as_array().unwrap().len(), 2);
    let search = census["subsystem"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["name"].as_str() == Some("backend-rewrite-search"))
        .unwrap();
    assert_eq!(search["tests"].as_integer(), Some(1));
    assert_eq!(search["reference_marked"].as_integer(), Some(1));
    let emission = census["subsystem"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["name"].as_str() == Some("module_to_kore"))
        .unwrap();
    assert_eq!(emission["reference_marked"].as_integer(), Some(1));

    fs::remove_dir_all(workspace).unwrap();
}

#[test]
fn fixture_refresh_requires_explicit_opt_in() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let output = Command::new("bash")
        .arg(repository.join("scripts/reference-fixtures-refresh.sh"))
        .arg("inner/scan-d")
        .env_remove("K_REFERENCE_REFRESH")
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("K_REFERENCE_REFRESH=1"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn temporary_directory(label: &str) -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let nonce = NEXT.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!("k-rust-{label}-{}-{nonce}", std::process::id()))
}

fn find_named(directory: &Path, name: &str) -> Vec<std::path::PathBuf> {
    let mut found = Vec::new();
    let entries = fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("read {}: {error}", directory.display()));
    for entry in entries {
        let path = entry.unwrap().path();
        if path.is_dir() {
            found.extend(find_named(&path, name));
        } else if path.file_name().and_then(|name| name.to_str()) == Some(name) {
            found.push(path);
        }
    }
    found
}

fn check_manifest(root: &Path, subsystem: &str, path: &Path) {
    let source = fs::read_to_string(path).unwrap();
    let manifest = source
        .parse::<Value>()
        .unwrap_or_else(|error| panic!("parse {}: {error}", path.display()));
    assert_eq!(manifest["subsystem"].as_str(), Some(subsystem));
    assert_eq!(
        manifest["case"].as_str(),
        path.parent()
            .unwrap()
            .file_name()
            .and_then(|name| name.to_str()),
        "{} case must match its directory",
        path.display()
    );
    for field in ["case", "harvested_from", "k_revision", "haskell_backend"] {
        assert!(
            manifest[field]
                .as_str()
                .is_some_and(|value| !value.trim().is_empty()),
            "{} must provide {field}",
            path.display()
        );
    }
    let artifacts = manifest["artifact"]
        .as_array()
        .unwrap_or_else(|| panic!("{} has no [[artifact]] rows", path.display()));
    assert!(!artifacts.is_empty(), "{} has no artifacts", path.display());
    for artifact in artifacts {
        let relative = check_recorded_file(root, path, artifact, "artifact");
        for field in ["command", "tool"] {
            assert!(
                artifact[field]
                    .as_str()
                    .is_some_and(|value| !value.trim().is_empty()),
                "{} artifact {relative:?} must provide {field}",
                path.display()
            );
        }
        assert!(artifact["exit_code"].as_integer().is_some());
        if relative.file_name().and_then(|name| name.to_str()) == Some("definition.kore") {
            assert_eq!(manifest["backend_isolation"].as_bool(), Some(true));
        }
    }
    for kind in ["input", "expectation"] {
        for recorded in manifest
            .get(kind)
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            check_recorded_file(root, path, recorded, kind);
            assert!(
                recorded["source"]
                    .as_str()
                    .is_some_and(|source| !source.trim().is_empty()),
                "{} {kind} must name its source",
                path.display()
            );
        }
    }
}

fn check_recorded_file<'a>(
    root: &Path,
    manifest: &Path,
    record: &'a Value,
    kind: &str,
) -> &'a Path {
    let relative = record["file"]
        .as_str()
        .unwrap_or_else(|| panic!("{} {kind} has no file", manifest.display()));
    let relative = Path::new(relative);
    assert!(
        !relative.is_absolute()
            && relative
                .components()
                .all(|component| matches!(component, std::path::Component::Normal(_))),
        "{} uses unsafe {kind} path {}",
        manifest.display(),
        relative.display()
    );
    let recorded_path = manifest.parent().unwrap().join(relative);
    assert!(
        recorded_path.starts_with(root) && recorded_path.is_file(),
        "{} references missing {kind} {}",
        manifest.display(),
        recorded_path.display()
    );
    let bytes = fs::read(&recorded_path).unwrap();
    assert!(
        bytes.len() <= 512 * 1024,
        "reference {kind} exceeds 512 KiB: {}",
        recorded_path.display()
    );
    let digest = Sha256::digest(&bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    assert_eq!(
        record["sha256"].as_str(),
        Some(digest.as_str()),
        "reference {kind} digest changed: {}",
        recorded_path.display()
    );
    relative
}

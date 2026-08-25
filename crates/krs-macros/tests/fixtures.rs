//! Self-contained compile/run coverage for the procedural macro facade.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join(name)
        .join("Cargo.toml")
}

fn cargo(manifest: &Path, arguments: &[&str]) -> Output {
    let fixture_name = manifest
        .parent()
        .and_then(Path::file_name)
        .expect("fixture manifest has a parent name");
    let target = std::env::temp_dir()
        .join("krs-macros-fixtures")
        .join(fixture_name);
    Command::new(env!("CARGO"))
        .args(arguments)
        .arg("--manifest-path")
        .arg(manifest)
        .arg("--offline")
        .env("CARGO_TERM_COLOR", "never")
        .env("CARGO_TARGET_DIR", target)
        .output()
        .expect("fixture Cargo process starts")
}

#[test]
fn renamed_facade_positive_surface_registers_expected_descriptors() {
    let manifest = fixture("positive");
    let check = cargo(&manifest, &["check", "--all-targets"]);
    assert!(
        check.status.success(),
        "positive fixture failed:\n{}",
        String::from_utf8_lossy(&check.stderr)
    );
    let run = cargo(&manifest, &["run", "--quiet"]);
    assert!(
        run.status.success(),
        "positive descriptor assertions failed:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    let repeated = cargo(&manifest, &["run", "--quiet"]);
    assert!(repeated.status.success(), "repeated fixture run failed");
    assert!(!run.stdout.is_empty(), "fixture must print its sorted summary");
    assert_eq!(run.stdout, repeated.stdout, "descriptor summary changed");
}

#[test]
fn rejected_surface_reports_local_failures() {
    let manifest = fixture("negative");
    let cases = [
        ("wrong_sort_item", "expected `trait`"),
        ("wrong_rule_item", "expected `fn`"),
        (
            "malformed_constructor_attr",
            "missing required argument `sort = ...`",
        ),
        ("tuple_constructor", "tuple structs are outside M1"),
        ("unsupported_rule", "the root must be a named path"),
        ("duplicate_binder", "same binding cannot be introduced"),
        ("unsupported_term", "root must be a named path"),
        ("missing_path", "cannot find module or crate `missing`"),
        ("wrong_configuration_item", "expected `struct`"),
        (
            "missing_initializer",
            "no associated function or constant named `__krs_initializer_payload`",
        ),
        ("duplicate_initializer", "duplicate definitions with name `init`"),
        (
            "initializer_control_flow",
            "statements, semicolons, control flow, mutation, and early return are forbidden",
        ),
        ("unsupported_k", "root must be a named path"),
        ("free_initializer", "`Self` is only available in impls"),
        (
            "trait_initializer",
            "method `__krs_initializer_payload` is not a member of trait `Initializes`",
        ),
        (
            "orphan_strictness",
            "is a constructor helper; place `#[k::constructor(...)]` before it",
        ),
        (
            "orphan_bracket",
            "is a sort helper; place `#[k::sort]` before it",
        ),
        (
            "tuple_enum_constructor",
            "tuple enum constructor variants are unsupported",
        ),
        ("standalone_variant_alias", "expected type, found variant"),
        (
            "malformed_precedence",
            "a precedence chain must contain at least one `>`",
        ),
        ("false_avoid", "`avoid` must be the Rust Boolean literal `true`"),
    ];
    for (binary, expected) in cases {
        let output = cargo(&manifest, &["check", "--bin", binary]);
        assert!(!output.status.success(), "`{binary}` unexpectedly compiled");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(expected),
            "`{binary}` did not report `{expected}`:\n{stderr}"
        );
    }
}

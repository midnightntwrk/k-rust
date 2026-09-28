//! Self-contained compile/run coverage for the procedural macro facade.

use std::path::{Path, PathBuf};

use krs_test_support::{cargo_fixture, check_compile_fixtures};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join(name)
        .join("Cargo.toml")
}

#[test]
fn renamed_facade_positive_surface_registers_expected_descriptors() {
    let manifest = fixture("positive");
    let check = cargo_fixture(&manifest).args(&["--all-targets"]).check();
    assert!(
        check.status.success(),
        "positive fixture failed:\n{}",
        String::from_utf8_lossy(&check.stderr)
    );
    let clippy = cargo_fixture(&manifest).args(&["--all-targets"]).clippy();
    assert!(
        clippy.status.success(),
        "positive fixture lint hygiene failed:\n{}",
        String::from_utf8_lossy(&clippy.stderr)
    );
    let tests = cargo_fixture(&manifest).args(&["--quiet"]).test();
    assert!(
        tests.status.success(),
        "positive fixture tests failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&tests.stdout),
        String::from_utf8_lossy(&tests.stderr)
    );
    let run = cargo_fixture(&manifest).args(&["--quiet"]).run();
    assert!(
        run.status.success(),
        "positive descriptor assertions failed:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    let repeated = cargo_fixture(&manifest).args(&["--quiet"]).run();
    assert!(repeated.status.success(), "repeated fixture run failed");
    assert!(
        !run.stdout.is_empty(),
        "fixture must print its sorted summary"
    );
    assert_eq!(run.stdout, repeated.stdout, "descriptor summary changed");
    expect_test::expect_file!["golden/positive_summary.txt"]
        .assert_eq(std::str::from_utf8(&run.stdout).unwrap());
}

#[test]
fn compile_fixtures_match_source_directives() {
    let checked = check_compile_fixtures(&fixture("negative"));
    for (name, expectation) in checked {
        println!("{name}: {expectation}");
    }
}

#[test]
fn initializer_lint_suppression_is_scoped_to_generated_output() {
    let manifest = fixture("negative");
    let output = cargo_fixture(&manifest)
        .args(&["--bin", "initializer_lint_scope"])
        .clippy();
    assert!(
        !output.status.success(),
        "ordinary sibling method unexpectedly inherited initializer lint suppression"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("ordinary") && stderr.contains("could have a `#[must_use]` attribute"),
        "initializer lint fixture did not report the unsuppressed sibling method:\n{stderr}"
    );
    assert!(
        !stderr.contains("pub fn init"),
        "initializer itself still triggered an author-facing lint:\n{stderr}"
    );
}

#[test]
fn non_bool_guard_is_rejected_after_real_collection_and_sort_inference() {
    let manifest = fixture("negative");
    let output = cargo_fixture(&manifest)
        .args(&["--quiet", "--bin", "requires_non_bool"])
        .run();
    assert!(
        output.status.success(),
        "non-Bool collection fixture failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        "application result sort Int is not admissible at sort Bool"
    );
}

#[test]
fn map_update_lookalike_is_rejected_after_type_identity_resolution() {
    let manifest = fixture("negative");
    let output = cargo_fixture(&manifest)
        .args(&["--quiet", "--bin", "readable_rule_update_lookalike"])
        .run();
    assert!(
        output.status.success(),
        "map-update lookalike fixture failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("impostor")
            && stdout.contains("update")
            && stdout.contains("registered term operation"),
        "lookalike rejection did not retain the authored path and registry boundary: {stdout}"
    );
}

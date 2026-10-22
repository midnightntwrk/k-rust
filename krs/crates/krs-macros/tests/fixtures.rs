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
fn expression_notation_emits_the_k_of_the_calls_it_denotes() {
    let manifest = fixture("negative");
    let output = cargo_fixture(&manifest)
        .args(&["--quiet", "--bin", "expression_notation_emits_call_form"])
        .run();
    assert!(
        output.status.success(),
        "expression-notation fixture failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    expect_test::expect_file!["golden/expression_notation_rule.txt"]
        .assert_eq(std::str::from_utf8(&output.stdout).unwrap());
}

#[test]
fn operators_emit_the_k_of_the_calls_they_denote() {
    let manifest = fixture("negative");
    let output = cargo_fixture(&manifest)
        .args(&["--quiet", "--bin", "operator_notation_emits_call_form"])
        .run();
    assert!(
        output.status.success(),
        "operator fixture failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    expect_test::expect_file!["golden/operator_notation_rule.txt"]
        .assert_eq(std::str::from_utf8(&output.stdout).unwrap());
}

#[test]
fn an_operator_whose_operands_choose_no_domain_names_the_explicit_forms() {
    expect_test::expect![[r"
        `==` has operands of sorts `Obj` and `Obj`, which choose no builtin domain; write the operation you mean: `a.eq::<Int>(b)`, `a.eq::<Bool>(b)`, `a.eq::<String>(b)`, `a.eq::<Float>(b)`, or `a.eq::<K>(b)` to compare terms
    "]]
    .assert_eq(&run_fixture("operator_ambiguous"));
}

#[test]
fn bitwise_and_on_bool_points_to_the_connectives() {
    expect_test::expect![[r"
        `&` is not a `Bool` connective: Rust's precedence would make `a == b & c == d` a parse error; write `a && b`, or `bool::and(a, b)` to evaluate both operands
    "]]
    .assert_eq(&run_fixture("operator_bool_bitand"));
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

/// Runs an in-process collection fixture and returns its standard output.
fn run_fixture(bin: &str) -> String {
    let output = cargo_fixture(fixture("negative"))
        .args(&["--quiet", "--bin", bin])
        .run();
    assert!(
        output.status.success(),
        "{bin} failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

const CHAIN_HELP: &str = "so one `{family}` production can sit directly at the edge of another, where a chain decides how they parse; rank every variant, for example `#[k::precedence((A) > left (B, C))]`, or list them all in one bare tier to accept every nesting";

fn missing_chain(family: &str, reasons: &str) -> String {
    format!(
        "`{family}` needs a `#[k::precedence(..)]` chain: {reasons}, {}\n",
        CHAIN_HELP.replace("{family}", family)
    )
}

#[test]
fn a_chainless_family_whose_variant_nests_at_its_own_edge_is_rejected() {
    assert_eq!(
        run_fixture("precedence_chain_missing_own_sort"),
        missing_chain(
            "Op",
            "`Add` begins with `lhs: Exp` (the family's own sort) and ends with `rhs: Exp` (the family's own sort)"
        )
    );
}

#[test]
fn a_chainless_family_nesting_through_a_subsort_is_rejected() {
    assert_eq!(
        run_fixture("precedence_chain_missing_through_subsort"),
        missing_chain(
            "AtomSyntax",
            "`Wrap` ends with `inner: Exp` (through the subsorts `Atom` < `Exp`)"
        )
    );
}

#[test]
fn a_chainless_family_ending_with_a_k_item_field_is_rejected() {
    assert_eq!(
        run_fixture("precedence_chain_missing_through_k_item"),
        missing_chain(
            "Steps",
            "`Then` ends with `next: KItem` (`KItem` admits every sort)"
        )
    );
}

#[test]
fn a_family_that_cannot_nest_at_an_edge_omits_its_chain_and_emits_no_group() {
    expect_test::expect![[r##"
        syntax Instr ::= AluOp "a" "," Operand8 [symbol(instructionAlu8), format(%1 %2%3 %4)]
        syntax Instr ::= "ld" Operand8 "," Operand8 [symbol(instructionLd8), format(%1 %2%3 %4)]
        syntax Instr ::= "nop" [symbol(instructionNop), format(%1)]
        syntax Instr ::= "#" "unimplemented" "(" Instr ")" [symbol(instructionUnimplemented), format(%1%2%3%4%5)]
    "##]]
    .assert_eq(&run_fixture("precedence_chain_omitted"));
}

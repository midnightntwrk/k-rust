//! Self-contained compile/run coverage for the procedural macro facade.

use std::path::{Path, PathBuf};

use krs_test_support::cargo_fixture;

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
fn nonlinear_binding_fixture_compiles() {
    let manifest = fixture("negative");
    let run = cargo_fixture(&manifest)
        .args(&["--quiet", "--bin", "duplicate_binder"])
        .check();
    assert!(
        run.status.success(),
        "non-linear binding fixture failed:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
}

#[test]
#[allow(clippy::too_many_lines)] // One table-driven inventory of rejected macro fixtures.
fn rejected_surface_reports_local_failures() {
    let manifest = fixture("negative");
    let cases = [
        ("wrong_sort_item", "expected `trait`"),
        ("wrong_rule_item", "expected `fn`"),
        (
            "malformed_constructor_attr",
            "missing required argument `sort = ...`",
        ),
        ("tuple_constructor", "tuple structs are not supported"),
        ("unsupported_rule", "the root must be a named path"),
        ("unsupported_term", "root must be a named path"),
        ("missing_path", "cannot find module or crate `missing`"),
        ("missing_cell_wrapper", "cannot find type `KCell`"),
        ("malformed_sorts", "expected a member type after `,`"),
        (
            "readable_membership_duplicate",
            "duplicate readable membership relation `relative:Int -> relative:Expr`",
        ),
        (
            "readable_rule_unbound_where",
            "rule narrowing names unbound subject binding `absent`",
        ),
        (
            "readable_rule_control_header",
            "control-flow rule surface and is not implemented yet",
        ),
        (
            "readable_rule_non_glob_import",
            "only `use Enum::*;` imports",
        ),
        (
            "readable_rule_ambiguous_module_globs",
            "`Shared` is ambiguous",
        ),
        (
            "readable_rule_duplicate_extra",
            "duplicate extra-cell mention `env`",
        ),
        (
            "readable_rule_bad_update",
            "update base must be the cell `env`",
        ),
        (
            "readable_rule_explicit_tail",
            "implicit preserved tail; do not spell another tail",
        ),
        ("wrong_configuration_item", "expected `struct`"),
        (
            "readable_missing_cell",
            "wrapper-free configurations require `#[k::cell]` on every plain field",
        ),
        (
            "readable_ambiguous_main",
            "at most one configuration variable may be marked `main`",
        ),
        (
            "missing_initializer",
            "no associated function or constant named `__krs_initializer_payload`",
        ),
        (
            "duplicate_initializer",
            "duplicate definitions with name `init`",
        ),
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
        (
            "malformed_readable_family",
            "enum variant `Other` is missing from the exhaustive chain",
        ),
        (
            "readable_precedence_unknown",
            "unknown enum variant `Unti`; did you mean `Unit`?",
        ),
        (
            "readable_precedence_duplicate",
            "enum variant `Unit` appears more than once",
        ),
        (
            "readable_precedence_reserved_group",
            "reserved associativity keywords",
        ),
        (
            "readable_precedence_malformed",
            "`>` must be followed by a precedence group",
        ),
        ("standalone_variant_alias", "expected type, found variant"),
        (
            "malformed_precedence",
            "a precedence chain must contain at least one `>`",
        ),
        (
            "false_avoid",
            "`avoid` must be the Rust Boolean literal `true`",
        ),
        (
            "malformed_state_rule",
            "a result remainder must reuse a subject frame of the same kind",
        ),
        (
            "wrong_state_wrapper",
            "cell wrapper and rule state family disagree",
        ),
        (
            "invalid_rule_label",
            "`label` must be a nonempty K rule label",
        ),
        (
            "requires_host_literal",
            "a rule condition must be an object-Bool term constructor, not a host literal",
        ),
        ("requires_unbound", "cannot find type `unbound`"),
        ("requires_post_only", "cannot find type `post`"),
        (
            "orphan_priority",
            "is an equation helper; place it immediately before `#[k::equation]`",
        ),
        (
            "priority_on_rule",
            "is an equation helper; place it immediately before `#[k::equation]`",
        ),
        (
            "orphan_alias",
            "on a production is a constructor helper; place `#[k::constructor(...)]` before it",
        ),
        (
            "claim_duplicate_modality",
            "a claim requires exactly one modality",
        ),
        ("claim_invalid_label", "invalid portable K claim label"),
        (
            "claim_one_path_circularity",
            "circularity is valid only on an all-path claim",
        ),
        (
            "claim_duplicate_exists",
            "a claim may declare only one `exists` helper",
        ),
        (
            "claim_duplicate_ensures",
            "a claim may declare only one `ensures` helper",
        ),
        (
            "claim_empty_ensures",
            "claim helper payload must not be empty",
        ),
        (
            "claim_anonymous_rhs",
            "anonymous! is allowed only in claim subjects",
        ),
        ("claim_anonymous_reference", "cannot find type `_B`"),
        (
            "claim_invalid_signature",
            "a configuration-rule subject must be `cells! { ... }`",
        ),
        ("claim_wrong_item", "expected `fn`"),
        ("malformed_symbol", "invalid explicit stable symbol"),
        ("duplicate_symbol", "duplicate #[k::symbol] attribute"),
        (
            "reversed_symbol",
            "#[k::symbol] must appear before the symbol-bearing KRS declaration attribute",
        ),
        (
            "unknown_function_hook",
            "unknown KRS hook; expected `krypto::keccak256_raw`, `krypto::sha256_raw`, `krypto::ripemd160_raw`, `krypto::ecdsa_recover`, `krypto::bn128_valid`, `krypto::bn128_add`, `krypto::bn128_mul`, `krypto::bn128_g2_valid`, or `krypto::bn128_ate`",
        ),
        (
            "claim_orphan_exists",
            "`#[k::exists]` is a claim helper; place `#[k::claim(...)]` before it",
        ),
        (
            "claim_orphan_ensures",
            "`#[k::ensures]` is a claim helper; place `#[k::claim(...)]` before it",
        ),
        ("unrelated_unused_import", "unused import: `term`"),
    ];
    for (binary, expected) in cases {
        let output = cargo_fixture(&manifest).args(&["--bin", binary]).check();
        assert!(!output.status.success(), "`{binary}` unexpectedly compiled");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(expected),
            "`{binary}` did not report `{expected}`:\n{stderr}"
        );
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
        "application result sort Builtin(Int) is not admissible at sort Builtin(Bool)"
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

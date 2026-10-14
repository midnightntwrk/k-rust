//! Frozen negative surface coverage for reachability claims.

use krs_syntax::KrsSyntax;

fn assert_error_contains<T: std::fmt::Debug>(
    result: Result<T, krs_syntax::SyntaxError>,
    expected: &str,
) {
    let error = result.expect_err("surface unexpectedly parsed");
    assert!(
        error.to_string().contains(expected),
        "expected {expected:?}, got {error}"
    );
}

#[test]
fn claim_metadata_rejects_missing_duplicate_and_incompatible_modalities() {
    for (source, expected) in [
        (
            r#"label = "missing-modality""#,
            "claim requires `all_paths` or `one_path`",
        ),
        (
            r#"all_paths, one_path, label = "two-modalities""#,
            "a claim requires exactly one modality",
        ),
        (
            r#"one_path, label = "circular", circularity"#,
            "circularity is valid only on an all-path claim",
        ),
        (
            r#"all_paths, label = "duplicate", label = "again""#,
            "duplicate claim label",
        ),
        (
            r#"all_paths, label = "valid", circularity, circularity"#,
            "duplicate circularity modifier",
        ),
        (
            r#"all_paths, label = "valid", priority = 40"#,
            "unknown claim argument",
        ),
        (
            r#"all_paths, label = "valid", trusted, trusted"#,
            "duplicate trusted modifier",
        ),
        (
            r#"all_paths, label = "valid", circularity, trusted"#,
            "a trusted claim is assumed, not proved; circularity has no effect",
        ),
        (
            r#"all_paths, label = "valid", trusted, circularity"#,
            "a trusted claim is assumed, not proved; circularity has no effect",
        ),
        (
            r#"all_paths, label = "valid", trusted = true"#,
            "`trusted` is a bare flag",
        ),
    ] {
        assert_error_contains(krs_syntax::ClaimAttribute::parse_source(source), expected);
    }
}

#[test]
fn claim_metadata_rejects_missing_and_nonportable_labels() {
    for (source, expected) in [
        ("all_paths", "claim requires an explicit `label = \"...\"`"),
        (r#"all_paths, label = """#, "invalid portable K claim label"),
        (
            r#"all_paths, label = "contains space""#,
            "invalid portable K claim label",
        ),
        (
            r#"all_paths, label = "contains:colon""#,
            "invalid portable K claim label",
        ),
        (
            r#"all_paths, label = "contains[bracket]""#,
            "invalid portable K claim label",
        ),
    ] {
        assert_error_contains(krs_syntax::ClaimAttribute::parse_source(source), expected);
    }
}

#[test]
fn exists_rejects_empty_malformed_and_duplicate_binders() {
    for (source, expected) in [
        ("", "exists requires at least one `name: Sort` binder"),
        ("n", "expected `:`"),
        ("n:", "unexpected end of input"),
        ("n: Int, n: Int", "duplicate existential binder"),
    ] {
        assert_error_contains(krs_syntax::ExistsAttribute::parse_source(source), expected);
    }
}

#[test]
fn claim_item_rejects_duplicate_and_malformed_helpers() {
    let body = r"
        fn bad(
            cells! {
                k: k::configuration::KCell(0, tail @ ..),
                state @ ..
            }: Machine,
        ) -> Machine {
            cells! {
                k: k::configuration::KCell(1, ..tail),
                ..state
            }
        }
    ";
    for (helpers, expected) in [
        (
            "#[k::exists(n: Int)] #[k::exists(m: Int)]",
            "a claim may declare only one `exists` helper",
        ),
        (
            "#[k::ensures(is_ok(n))] #[k::ensures(is_done(n))]",
            "a claim may declare only one `ensures` helper",
        ),
        (
            "#[k::exists]",
            "claim helpers require parenthesized payloads",
        ),
        ("#[k::ensures()]", "claim helper payload must not be empty"),
    ] {
        assert_error_contains(
            krs_syntax::StateClaimItem::parse_source(&format!("{helpers} {body}")),
            expected,
        );
    }
}

#[test]
fn claim_item_rejects_shadowing_and_non_configuration_shapes() {
    assert_error_contains(
        krs_syntax::StateClaimItem::parse_source(
            r"
            #[k::exists(n: Int)]
            fn shadow(
                n: Term<Int>,
                cells! {
                    k: k::configuration::KCell(n, tail @ ..),
                    state @ ..
                }: Machine,
            ) -> Machine {
                cells! {
                    k: k::configuration::KCell(n, ..tail),
                    ..state
                }
            }
            ",
        ),
        "an existential cannot shadow a universal or structural binding",
    );

    for (source, expected) in [
        (
            "fn term_claim(value: Term<Int>) -> Term<Int> { value }",
            "a configuration-rule subject must be `cells! { ... }`",
        ),
        (
            "fn missing_result(cells! { k: KCell(0, tail @ ..) }: Machine) {}",
            "a configuration rule must declare its configuration result type",
        ),
        (
            "fn two_results(cells! { k: KCell(0, tail @ ..) }: Machine) -> Machine { let x = 1; cells! { k: KCell(x, ..tail) } }",
            "a configuration-rule body must contain exactly one `cells!` expression",
        ),
    ] {
        assert_error_contains(krs_syntax::StateClaimItem::parse_source(source), expected);
    }
}

#[test]
fn claim_item_accepts_readable_sort_aliases_for_binders() {
    let claim = krs_syntax::StateClaimItem::parse_source(
        r#"
        #[k::exists(new_value: Value)]
        fn readable(
            body: Stmt,
            cells! { k: KCell(body, tail @ ..), state @ .. }: Machine,
        ) -> Machine {
            cells! { k: KCell(k::anonymous!(Value, "_V"), ..tail), ..state }
        }
        "#,
    )
    .unwrap();

    let body = claim
        .rule()
        .bindings()
        .iter()
        .find(|binding| binding.name() == "body")
        .unwrap();
    assert_eq!(body.term_sort().unwrap().sort().segments[0].ident, "Stmt");
    assert_eq!(claim.existentials()[0].sort().segments[0].ident, "Value");
    assert!(
        claim
            .sort_candidates()
            .unwrap()
            .iter()
            .all(|candidate| candidate.path().segments[0].ident == "Value")
    );
}

#[test]
fn trusted_claims_parse_with_either_modality() {
    for source in [
        r#"all_paths, label = "helper-axiom", trusted"#,
        r#"one_path, label = "helper-axiom", trusted"#,
    ] {
        let claim = krs_syntax::ClaimAttribute::parse_source(source).expect("trusted claim");
        assert!(claim.trusted());
        assert!(!claim.circularity());
        assert!(
            claim
                .provenance()
                .expect("provenance")
                .iter()
                .any(|anchor| anchor.role() == krs_ir::ProvenanceRole::ClaimTrusted)
        );
    }
    let plain = krs_syntax::ClaimAttribute::parse_source(r#"all_paths, label = "plain""#)
        .expect("plain claim");
    assert!(!plain.trusted());
}

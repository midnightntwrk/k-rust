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
    let candidates = claim.sort_candidates().unwrap();
    assert!(
        candidates
            .iter()
            .all(|candidate| candidate.path().segments[0].ident == "Value")
    );
    // Each candidate's key is the one its sort holds in the claim's
    // anchors: the existential sort follows the universal binder's.
    let anchors = claim.provenance().unwrap();
    for candidate in &candidates {
        let anchor = anchors
            .iter()
            .find(|anchor| anchor.key() == *candidate.key())
            .unwrap();
        let path = krs_syntax::TokenRange::for_tokens(candidate.path()).unwrap();
        assert_eq!(
            (anchor.range().start(), anchor.range().end()),
            (path.start(), path.end())
        );
    }
    assert_eq!(
        candidates[0].key(),
        &krs_ir::ProvenanceRole::ClaimBinderSort.key(1)
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

#[test]
fn a_readable_claim_clause_is_a_claim_labelled_by_its_name() {
    let block = krs_syntax::ClaimBlock::parse_source(
        r"
        for Machine;
        use Instruction::*;

        /// `3 + 4` leaves 7 on the stack.
        #[k::claim(all_paths, circularity)]
        #[k::requires(int::ge(g, 0))]
        simple_addition: {
            instrs: [Const(I32, 3), Const(I32, 4), Binary(I32, Add)],
            valstack: Empty(),
            gas: g,
        } => {
            instrs: [],
            valstack: Cons(Integer(I32, 7), Empty()),
        };
        ",
    )
    .unwrap();
    let [clause] = block.clauses() else {
        panic!("one clause");
    };
    let claim = clause.claim().expect("a claims! clause is a claim");
    assert_eq!(claim.label().value(), "simple-addition");
    assert_eq!(claim.modality(), krs_syntax::ClaimModality::AllPaths);
    assert!(claim.circularity() && !claim.trusted());
    assert!(clause.rule().requires().is_some());
    let roles = clause
        .provenance()
        .unwrap()
        .into_iter()
        .chain(clause.attribute_provenance().unwrap())
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    for role in [
        krs_syntax::ProvenanceRole::ClaimDeclaration,
        krs_syntax::ProvenanceRole::ClaimLabel,
        krs_syntax::ProvenanceRole::ClaimModality,
        krs_syntax::ProvenanceRole::ClaimCircularity,
    ] {
        assert!(roles.contains(&role), "{role:?} in {roles:?}");
    }
    for role in [
        krs_syntax::ProvenanceRole::RuleDeclaration,
        krs_syntax::ProvenanceRole::RuleLabel,
    ] {
        assert!(!roles.contains(&role), "{role:?} in {roles:?}");
    }
}

#[test]
fn a_readable_claim_clause_rejects_rule_only_forms() {
    for (clause, expected) in [
        (
            "x: { k: [Go()] } => { k: [] };",
            "a claim clause states its modality",
        ),
        (
            "#[k::claim(all_paths)] #[k::rule(owise)] x: { k: [Go()] } => { k: [] };",
            "`#[k::rule(..)]` is a rule's metadata",
        ),
        (
            "#[k::claim(all_paths)] #[k::fresh(n: Int)] x: { k: [Go()] } => { k: [] };",
            "a claim has no fresh binders",
        ),
        (
            "#[k::claim(all_paths, label = \"y\")] x: { k: [Go()] } => { k: [] };",
            "labelled by its name",
        ),
        (
            "#[k::claim(all_paths)] x: Go() => 1;",
            "a pair of cell records",
        ),
        (
            "#[k::claim(all_paths)] #[k::claim(one_path)] x: { k: [Go()] } => { k: [] };",
            "one `#[k::claim(..)]`",
        ),
    ] {
        let error =
            krs_syntax::ClaimBlock::parse_source(&format!("for Machine; {clause}")).unwrap_err();
        assert!(error.to_string().contains(expected), "{clause}: {error}");
    }
}

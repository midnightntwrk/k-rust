//! Attribute payload parser acceptance, rejection, and span tests.

use krs_syntax::{
    ProvenanceRole, SyntaxErrorKind, parse_alias_attribute_source,
    parse_constructor_attribute_source, parse_constructors_attribute_source,
    parse_context_alias_attribute_source, parse_equation_attribute_source,
    parse_function_attribute_source, parse_priority_attribute_source, parse_rule_attribute_source,
    parse_simplification_attribute_source, parse_sort_attribute_source,
    parse_subsort_attribute_source,
};
use quote::ToTokens;

#[test]
fn empty_marker_attributes_are_accepted() {
    let sort = parse_sort_attribute_source("").unwrap();
    assert!(!sort.is_reference());
    assert!(sort.alias().is_none());
    assert!(sort.parents().is_empty());
    parse_equation_attribute_source("").unwrap();
    parse_alias_attribute_source("").unwrap();
    let rule = parse_rule_attribute_source("").unwrap();
    assert!(rule.label().is_none());
    assert!(!rule.is_owise());
}

#[test]
fn sort_accepts_explicit_alias_and_parent_carriers() {
    let alias = parse_sort_attribute_source("alias = Expr").unwrap();
    assert!(alias.is_reference());
    assert_eq!(alias.alias().unwrap(), "Expr");
    assert!(alias.parents().is_empty());

    let inherited =
        parse_sort_attribute_source("parents = [Expr, k::KResult], alias = Value,").unwrap();
    assert!(inherited.is_reference());
    assert_eq!(inherited.alias().unwrap(), "Value");
    assert_eq!(
        inherited
            .parents()
            .iter()
            .map(ToTokens::to_token_stream)
            .map(|tokens| tokens.to_string())
            .collect::<Vec<_>>(),
        ["Expr", "k :: KResult"]
    );
}

#[test]
fn sort_rejects_incomplete_duplicate_unknown_and_malformed_reference_payloads() {
    let cases = [
        "parents = [Expr]",
        "alias = Expr, alias = Value",
        "alias = Expr, parents = [], parents = [Value]",
        "alias = crate::Expr",
        "alias = \"Expr\"",
        "alias = Expr, parents = Expr",
        "alias = Expr, parents = [Vec<Expr>]",
        "alias = Expr, result = KResult",
    ];
    for source in cases {
        assert!(
            parse_sort_attribute_source(source).is_err(),
            "unexpectedly accepted {source:?}"
        );
    }
    let missing = parse_sort_attribute_source("parents = [Expr]").unwrap_err();
    assert!(matches!(
        missing.kind(),
        SyntaxErrorKind::MissingArgument { name: "alias" }
    ));
}

#[test]
fn subsort_reference_attribute_requires_one_semantic_sort_path() {
    let parsed = parse_subsort_attribute_source("sort = crate::Value,").unwrap();
    assert_eq!(
        parsed.sort().to_token_stream().to_string(),
        "crate :: Value"
    );

    for source in [
        "",
        "sort = Value, sort = Expr",
        "supersort = Value",
        "sort = \"Value\"",
        "sort = Vec<Value>",
    ] {
        assert!(
            parse_subsort_attribute_source(source).is_err(),
            "unexpectedly accepted {source:?}"
        );
    }
}

#[test]
fn constructors_distinguishes_closed_readable_and_reference_families() {
    let closed = parse_constructors_attribute_source("sort = Expr").unwrap();
    assert!(!closed.is_open_family());
    assert!(!closed.is_reference());
    assert!(closed.result().is_none());

    let readable = parse_constructors_attribute_source("result = KResult, sort = Expr,").unwrap();
    assert!(readable.is_open_family());
    assert!(!readable.is_reference());
    assert_eq!(
        readable.result().unwrap().to_token_stream().to_string(),
        "KResult"
    );

    let reference = parse_constructors_attribute_source("reference, sort = Expr").unwrap();
    assert!(reference.is_open_family());
    assert!(reference.is_reference());
    assert!(reference.result().is_none());
    assert_eq!(reference.sort().to_token_stream().to_string(), "Expr");
}

#[test]
fn constructors_reference_is_bare_unique_and_mutually_exclusive_with_result() {
    for source in [
        "reference",
        "sort = Expr, reference, reference",
        "sort = Expr, reference = true",
        "sort = Expr, reference, result = KResult",
        "sort = Expr, result = KResult, reference",
    ] {
        assert!(
            parse_constructors_attribute_source(source).is_err(),
            "unexpectedly accepted {source:?}"
        );
    }

    for source in [
        "sort = Expr, reference, result = KResult",
        "sort = Expr, result = KResult, reference",
    ] {
        let error = parse_constructors_attribute_source(source).unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::InvalidArgumentValue { .. }
        ));
    }
}

#[test]
fn alias_rejects_recursive_and_other_payloads() {
    for source in ["recursive", "true", "mode = recursive"] {
        assert!(
            parse_alias_attribute_source(source).is_err(),
            "unexpectedly accepted {source:?}"
        );
    }
}

#[test]
fn context_alias_requires_typed_name_and_here_identifiers() {
    let parsed = parse_context_alias_attribute_source("here = site, name = eval_context,").unwrap();
    assert_eq!(parsed.name(), "eval_context");
    assert_eq!(parsed.here(), "site");

    let anchors = parsed.provenance().unwrap();
    assert_eq!(anchors.len(), 2);
    assert_eq!(anchors[0].role(), ProvenanceRole::ContextAliasName);
    assert_eq!(anchors[0].key().unwrap().role(), "context_alias_name");
    assert_eq!(anchors[1].role(), ProvenanceRole::ContextAliasHere);
    assert_eq!(anchors[1].key().unwrap().role(), "context_alias_here");
}

#[test]
fn context_alias_rejects_missing_duplicate_unknown_and_qualified_values() {
    let cases = [
        "",
        "name = execute",
        "here = site",
        "name = execute, name = other, here = site",
        "name = execute, here = site, result = Value",
        "name = aliases::execute, here = site",
        "name = execute, here = bindings::site",
        "name = \"execute\", here = site",
    ];
    for source in cases {
        assert!(
            parse_context_alias_attribute_source(source).is_err(),
            "unexpectedly accepted {source:?}"
        );
    }
}

#[test]
fn equation_does_not_invent_an_explicit_label_surface() {
    let error = parse_equation_attribute_source(r#"label = "not-settled""#).unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::UnexpectedAttributePayload {
            attribute: "equation"
        }
    ));
}

#[test]
fn priority_accepts_one_u32_and_anchors_its_literal() {
    let priority = parse_priority_attribute_source("40").unwrap();
    assert_eq!(priority.value(), 40);
    let anchors = priority.provenance().unwrap();
    assert_eq!(anchors.len(), 1);
    assert_eq!(anchors[0].role(), ProvenanceRole::EquationPriority);
}

#[test]
fn priority_rejects_missing_noninteger_multiple_and_overflow_values() {
    for source in ["", "high", "40, 80", "4294967296"] {
        assert!(
            parse_priority_attribute_source(source).is_err(),
            "unexpectedly accepted {source:?}"
        );
    }
}

#[test]
fn simplification_accepts_empty_or_one_typed_priority() {
    let plain = parse_simplification_attribute_source("").unwrap();
    assert_eq!(plain.priority(), None);
    assert!(plain.provenance().unwrap().is_empty());

    let hinted = parse_simplification_attribute_source("priority = 50").unwrap();
    assert_eq!(hinted.priority(), Some(50));
    let anchors = hinted.provenance().unwrap();
    assert_eq!(anchors.len(), 1);
    assert_eq!(anchors[0].role(), ProvenanceRole::SimplificationPriority);
}

#[test]
fn simplification_rejects_unknown_duplicate_and_invalid_hints() {
    for source in [
        "priority",
        "priority = high",
        "priority = 1, priority = 2",
        "priority = 4294967296",
        "label = 1",
    ] {
        assert!(
            parse_simplification_attribute_source(source).is_err(),
            "unexpectedly accepted {source:?}"
        );
    }
}

#[test]
fn total_function_requires_and_anchors_total_sort_syntax_and_hook() {
    let parsed = parse_function_attribute_source(
        r##"syntax = "#next({value})", total, hook = krypto::keccak256_raw, sort = crate::Int"##,
    )
    .unwrap();
    assert_eq!(
        parsed.production().sort.segments.last().unwrap().ident,
        "Int"
    );
    assert_eq!(
        parsed.production().syntax.as_ref().unwrap().value(),
        "#next({value})"
    );
    let anchors = parsed.provenance().unwrap();
    assert!(
        anchors
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::FunctionTotal)
    );
    let hook = parsed.hook().expect("hook path is retained");
    assert_eq!(
        hook.to_token_stream().to_string(),
        "krypto :: keccak256_raw"
    );
    let hook_anchor = anchors
        .iter()
        .find(|anchor| anchor.role() == ProvenanceRole::FunctionHook)
        .expect("hook provenance is retained");
    assert_eq!(hook_anchor.key().unwrap().role(), "function_hook");
    assert_eq!(hook_anchor.key().unwrap().ordinal(), 0);
}

#[test]
fn function_accepts_partial_and_rejects_missing_or_duplicate_totality() {
    let partial =
        parse_function_attribute_source(r#"partial, sort = Int, syntax = "f({value})""#).unwrap();
    assert!(!partial.is_total());
    for source in [
        r#"sort = Int, syntax = "f({value})""#,
        r#"total, partial, sort = Int, syntax = "f({value})""#,
        r#"total, sort = Int, syntax = "f({value})", hook = krypto::keccak256_raw, hook = krypto::keccak256_raw"#,
        r"total, sort = Int",
    ] {
        assert!(
            parse_function_attribute_source(source).is_err(),
            "unexpectedly accepted {source:?}"
        );
    }
}

#[test]
fn rule_accepts_an_exact_k_label_and_anchors_its_literal() {
    let attribute = parse_rule_attribute_source(r#"owise, label = "if-true""#).unwrap();
    assert_eq!(attribute.label().unwrap().value(), "if-true");
    assert!(attribute.is_owise());
    let anchors = attribute.provenance().unwrap();
    assert_eq!(anchors.len(), 2);
    assert_eq!(anchors[0].role(), ProvenanceRole::RuleLabel);
    assert_eq!(anchors[0].key().unwrap().role(), "rule_label");
    assert_eq!(anchors[1].role(), ProvenanceRole::RuleOwise);
    assert_eq!(anchors[1].key().unwrap().role(), "rule_owise");
}

#[test]
fn rule_rejects_unknown_duplicate_non_string_and_invalid_labels() {
    let cases = [
        "unknown = \"x\"",
        "label = \"first\", label = \"second\"",
        "owise, owise",
        "label = identifier",
        "label = \"\"",
        "label = \"1starts-with-digit\"",
        "label = \"contains space\"",
        "label = \"contains/slash\"",
    ];
    for source in cases {
        assert!(
            parse_rule_attribute_source(source).is_err(),
            "unexpectedly accepted {source:?}"
        );
    }
}

#[test]
fn marker_attributes_and_sort_reject_unknown_payload_at_first_token() {
    let error = parse_sort_attribute_source("unexpected").unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::UnknownArgument { name } if name == "unexpected"
    ));
    assert_eq!(error.span().start().column, 0);
}

#[test]
fn constructor_accepts_required_sort_and_optional_template_in_any_order() {
    let parsed = parse_constructor_attribute_source(
        r#"syntax = r"{lhs} + {rhs}", sort = crate::syntax::Expr,"#,
    )
    .unwrap();
    assert_eq!(parsed.syntax.as_ref().unwrap().value(), "{lhs} + {rhs}");
    assert_eq!(parsed.sort.segments.last().unwrap().ident, "Expr");

    let anchors = parsed.provenance().unwrap();
    assert_eq!(anchors.len(), 2);
    assert_eq!(anchors[0].role(), ProvenanceRole::ConstructorSort);
    assert_eq!(anchors[0].key().unwrap().role(), "constructor_sort");
    assert_eq!(anchors[1].role(), ProvenanceRole::ConstructorSyntax);
}

#[test]
fn constructor_syntax_is_optional() {
    let parsed = parse_constructor_attribute_source("sort = Value").unwrap();
    assert!(parsed.syntax.is_none());
    assert_eq!(parsed.provenance().unwrap().len(), 1);
}

#[test]
fn constructor_rejects_unknown_duplicate_missing_and_wrong_values() {
    let cases = [
        ("sort = Value, unsupported = \"x\"", "unknown"),
        ("sort = Value, sort = Expr", "duplicate"),
        ("sort = Value, syntax = \"x\", syntax = \"y\"", "duplicate"),
        ("syntax = \"x\"", "missing"),
        ("sort = \"Value\"", "sort_value"),
        ("sort = Value, syntax = template", "syntax_value"),
        ("sort = Vec<Value>", "sort_value"),
    ];
    for (source, expected) in cases {
        let error = parse_constructor_attribute_source(source).unwrap_err();
        match expected {
            "unknown" => assert!(matches!(
                error.kind(),
                SyntaxErrorKind::UnknownArgument { name } if name == "unsupported"
            )),
            "duplicate" => assert!(matches!(
                error.kind(),
                SyntaxErrorKind::DuplicateArgument { .. }
            )),
            "missing" => assert!(matches!(
                error.kind(),
                SyntaxErrorKind::MissingArgument { name: "sort" }
            )),
            "sort_value" => assert!(matches!(
                error.kind(),
                SyntaxErrorKind::InvalidArgumentValue { name: "sort", .. }
                    | SyntaxErrorKind::RustSyntax(_)
            )),
            "syntax_value" => assert!(matches!(
                error.kind(),
                SyntaxErrorKind::InvalidArgumentValue { name: "syntax", .. }
            )),
            _ => unreachable!(),
        }
    }
}

#[test]
fn duplicate_error_points_at_the_second_key() {
    let error = parse_constructor_attribute_source("sort = Value,\nsort = Expr").unwrap_err();
    let start = error.span().start();
    assert_eq!((start.line, start.column), (2, 0));
}

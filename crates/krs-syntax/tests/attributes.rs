//! Attribute payload parser acceptance, rejection, and span tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{ProvenanceRole, SyntaxErrorKind};
use proc_macro2::TokenStream;
use quote::ToTokens;

#[test]
fn empty_marker_attributes_are_accepted() {
    let sort = krs_syntax::SortAttribute::parse_source("").unwrap();
    assert!(!sort.is_reference());
    assert!(sort.alias().is_none());
    assert!(sort.parents().is_empty());
    krs_syntax::EquationAttribute::parse_source("").unwrap();
    krs_syntax::AliasAttribute::parse_source("").unwrap();
    let rule = krs_syntax::RuleAttribute::parse_source("").unwrap();
    assert!(rule.label().is_none());
    assert!(!rule.is_owise());
}

#[test]
fn sort_accepts_explicit_alias_and_parent_carriers() {
    let alias = krs_syntax::SortAttribute::parse_source("alias = Expr").unwrap();
    assert!(alias.is_reference());
    assert_eq!(alias.alias().unwrap(), "Expr");
    assert!(alias.parents().is_empty());

    let inherited =
        krs_syntax::SortAttribute::parse_source("parents = [Expr, k::KResult], alias = Value,")
            .unwrap();
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
        (
            "parents = [Expr]",
            SyntaxErrorKind::MissingArgument { name: "alias" },
        ),
        (
            "alias = Expr, alias = Value",
            SyntaxErrorKind::DuplicateArgument { name: "alias" },
        ),
        (
            "alias = Expr, parents = [], parents = [Value]",
            SyntaxErrorKind::DuplicateArgument { name: "parents" },
        ),
        (
            "alias = crate::Expr",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "alias",
                expected: "an unqualified Rust identifier",
            },
        ),
        (
            "alias = \"Expr\"",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "alias",
                expected: "an unqualified Rust identifier",
            },
        ),
        (
            "alias = Expr, parents = Expr",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "parents",
                expected: "an array of plain Rust sort paths",
            },
        ),
        (
            "alias = Expr, parents = [Vec::<Expr>]",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "parents",
                expected: "an array of plain Rust sort paths without generic arguments",
            },
        ),
        (
            "alias = Expr, result = KResult",
            SyntaxErrorKind::UnknownArgument {
                name: "result".into(),
            },
        ),
    ];
    for (source, expected_kind) in cases {
        let error = krs_syntax::SortAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
    let missing = krs_syntax::SortAttribute::parse_source("parents = [Expr]").unwrap_err();
    assert!(matches!(
        missing.kind(),
        SyntaxErrorKind::MissingArgument { name: "alias" }
    ));
}

#[test]
fn subsort_reference_attribute_requires_one_semantic_sort_path() {
    let parsed = krs_syntax::SubsortAttribute::parse_source("sort = crate::Value,").unwrap();
    assert_eq!(
        parsed.sort().to_token_stream().to_string(),
        "crate :: Value"
    );

    for (source, expected_kind) in [
        ("", SyntaxErrorKind::MissingArgument { name: "sort" }),
        (
            "sort = Value, sort = Expr",
            SyntaxErrorKind::DuplicateArgument { name: "sort" },
        ),
        (
            "supersort = Value",
            SyntaxErrorKind::UnknownArgument {
                name: "supersort".into(),
            },
        ),
        (
            "sort = \"Value\"",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "sort",
                expected: "a Rust trait path",
            },
        ),
        (
            "sort = Vec::<Value>",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "sort",
                expected: "a plain Rust trait path without generic arguments",
            },
        ),
    ] {
        let error = krs_syntax::SubsortAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn constructors_distinguishes_closed_readable_and_reference_families() {
    let closed = krs_syntax::ConstructorsAttribute::parse_source("sort = Expr").unwrap();
    assert!(!closed.is_open_family());
    assert!(!closed.is_reference());
    assert!(closed.result().is_none());

    let readable =
        krs_syntax::ConstructorsAttribute::parse_source("result = KResult, sort = Expr,").unwrap();
    assert!(readable.is_open_family());
    assert!(!readable.is_reference());
    assert_eq!(
        readable.result().unwrap().to_token_stream().to_string(),
        "KResult"
    );

    let reference =
        krs_syntax::ConstructorsAttribute::parse_source("reference, sort = Expr").unwrap();
    assert!(reference.is_open_family());
    assert!(reference.is_reference());
    assert!(reference.result().is_none());
    assert_eq!(reference.sort().to_token_stream().to_string(), "Expr");
}

#[test]
fn constructors_reference_is_bare_unique_and_mutually_exclusive_with_result() {
    for (source, expected_kind) in [
        (
            "reference",
            SyntaxErrorKind::MissingArgument { name: "sort" },
        ),
        (
            "sort = Expr, reference, reference",
            SyntaxErrorKind::DuplicateArgument { name: "reference" },
        ),
        (
            "sort = Expr, reference = true",
            SyntaxErrorKind::RustSyntax("expected `,`".into()),
        ),
        (
            "sort = Expr, reference, result = KResult",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "result",
                expected: "omitted when bare `reference` is present",
            },
        ),
        (
            "sort = Expr, result = KResult, reference",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "reference",
                expected: "omitted when `result = ...` is present",
            },
        ),
    ] {
        let error = krs_syntax::ConstructorsAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }

    for source in [
        "sort = Expr, reference, result = KResult",
        "sort = Expr, result = KResult, reference",
    ] {
        let error = krs_syntax::ConstructorsAttribute::parse_source(source).unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::InvalidArgumentValue { .. }
        ));
    }
}

#[test]
fn alias_clause_rejects_recursive_and_other_payloads() {
    for (source, expected_kind) in [
        (
            "recursive",
            SyntaxErrorKind::InvalidRuleKey {
                reason: krs_syntax::RECURSIVE_ON_CLAUSE,
            },
        ),
        (
            "true",
            SyntaxErrorKind::UnexpectedAttributePayload { attribute: "alias" },
        ),
        (
            "mode = recursive",
            SyntaxErrorKind::UnexpectedAttributePayload { attribute: "alias" },
        ),
    ] {
        let error = krs_syntax::AliasAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn context_alias_requires_typed_name_and_here_identifiers() {
    let parsed =
        krs_syntax::ContextAliasAttribute::parse_source("here = site, name = eval_context,")
            .unwrap();
    assert_eq!(parsed.name(), "eval_context");
    assert_eq!(parsed.here(), "site");

    let anchors = parsed.provenance().unwrap();
    assert_eq!(anchors.len(), 2);
    assert_eq!(anchors[0].role(), ProvenanceRole::ContextAliasName);
    assert_eq!(anchors[0].key().role(), ProvenanceRole::ContextAliasName);
    assert_eq!(anchors[1].role(), ProvenanceRole::ContextAliasHere);
    assert_eq!(anchors[1].key().role(), ProvenanceRole::ContextAliasHere);
}

#[test]
fn context_alias_rejects_missing_duplicate_unknown_and_qualified_values() {
    let cases = [
        ("", SyntaxErrorKind::MissingArgument { name: "name" }),
        (
            "name = execute",
            SyntaxErrorKind::MissingArgument { name: "here" },
        ),
        (
            "here = site",
            SyntaxErrorKind::MissingArgument { name: "name" },
        ),
        (
            "name = execute, name = other, here = site",
            SyntaxErrorKind::DuplicateArgument { name: "name" },
        ),
        (
            "name = execute, here = site, result = Value",
            SyntaxErrorKind::UnknownArgument {
                name: "result".into(),
            },
        ),
        (
            "name = aliases::execute, here = site",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "name",
                expected: "an unqualified Rust identifier",
            },
        ),
        (
            "name = execute, here = bindings::site",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "here",
                expected: "an unqualified Rust identifier",
            },
        ),
        (
            "name = \"execute\", here = site",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "name",
                expected: "an unqualified Rust identifier",
            },
        ),
    ];
    for (source, expected_kind) in cases {
        let error = krs_syntax::ContextAliasAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn equation_does_not_invent_an_explicit_label_surface() {
    let error =
        krs_syntax::EquationAttribute::parse_source(r#"label = "not-settled""#).unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::UnknownArgument { name } if name == "label"
    ));
}

#[test]
fn equation_accepts_owise_or_one_priority_and_anchors_them() {
    let plain = krs_syntax::EquationAttribute::parse_source("").unwrap();
    assert_eq!(plain.equation_priority(), None);
    assert!(plain.provenance().unwrap().is_empty());

    let owise = krs_syntax::EquationAttribute::parse_source("owise").unwrap();
    assert!(owise.is_owise());
    assert_eq!(
        owise.equation_priority(),
        Some((ProvenanceRole::EquationOwise, 200))
    );
    let anchors = owise.provenance().unwrap();
    assert_eq!(anchors.len(), 1);
    assert_eq!(anchors[0].role(), ProvenanceRole::EquationOwise);

    let priority = krs_syntax::EquationAttribute::parse_source("priority = 40").unwrap();
    assert_eq!(priority.priority(), Some(40));
    assert_eq!(
        priority.equation_priority(),
        Some((ProvenanceRole::EquationPriority, 40))
    );
    let anchors = priority.provenance().unwrap();
    assert_eq!(anchors.len(), 1);
    assert_eq!(anchors[0].role(), ProvenanceRole::EquationPriority);
}

#[test]
fn equation_rejects_owise_with_priority_out_of_range_and_duplicates() {
    for (source, expected_kind) in [
        (
            "owise, priority = 40",
            SyntaxErrorKind::InvalidRuleKey {
                reason: "owise is priority 200; write one of them",
            },
        ),
        (
            "priority = 40, owise",
            SyntaxErrorKind::InvalidRuleKey {
                reason: "owise is priority 200; write one of them",
            },
        ),
        (
            "priority = 255",
            SyntaxErrorKind::InvalidRuleKey {
                reason: "k-rust ranks rule priorities 0..=254",
            },
        ),
        (
            "priority = 40, priority = 41",
            SyntaxErrorKind::DuplicateArgument { name: "priority" },
        ),
        (
            "owise, owise",
            SyntaxErrorKind::DuplicateArgument { name: "owise" },
        ),
        (
            "priority = high",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "priority",
                expected: "an unsuffixed integer literal",
            },
        ),
    ] {
        let error = krs_syntax::EquationAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn standalone_priority_is_retired_with_its_replacement() {
    let error = krs_syntax::PriorityAttribute::parse_source("40").unwrap_err();
    assert_eq!(
        error.kind(),
        &SyntaxErrorKind::RetiredAttribute {
            attribute: "#[k::priority(..)]",
            replacement: "#[k::equation(priority = 40)]".into(),
        }
    );
    assert_eq!(
        error.to_string(),
        "`#[k::priority(..)]` is retired; write `#[k::equation(priority = 40)]`"
    );
}

#[test]
fn owise_on_a_simplification_and_priority_on_an_alias_are_rejected() {
    let error = krs_syntax::SimplificationAttribute::parse_source("owise").unwrap_err();
    assert_eq!(
        error.kind(),
        &SyntaxErrorKind::InvalidRuleKey {
            reason: "a simplification has its own `priority = N`, a simplifier hint; owise has no meaning there",
        }
    );
    for source in ["priority = 40", "owise"] {
        let error = krs_syntax::AliasAttribute::parse_source(source).unwrap_err();
        assert_eq!(
            error.kind(),
            &SyntaxErrorKind::InvalidRuleKey {
                reason: "static rules have no priority",
            },
            "{source}"
        );
    }
}

#[test]
fn simplification_accepts_empty_or_one_typed_priority() {
    let plain = krs_syntax::SimplificationAttribute::parse_source("").unwrap();
    assert_eq!(plain.priority(), None);
    assert!(plain.provenance().unwrap().is_empty());

    let hinted = krs_syntax::SimplificationAttribute::parse_source("priority = 50").unwrap();
    assert_eq!(hinted.priority(), Some(50));
    let anchors = hinted.provenance().unwrap();
    assert_eq!(anchors.len(), 1);
    assert_eq!(anchors[0].role(), ProvenanceRole::SimplificationPriority);
}

#[test]
fn simplification_rejects_unknown_duplicate_and_invalid_hints() {
    for (source, expected_kind) in [
        (
            "priority",
            SyntaxErrorKind::RustSyntax("expected `=`".into()),
        ),
        (
            "priority = high",
            SyntaxErrorKind::RustSyntax("expected integer literal".into()),
        ),
        (
            "priority = 1, priority = 2",
            SyntaxErrorKind::DuplicateArgument { name: "priority" },
        ),
        (
            "priority = 4294967296",
            SyntaxErrorKind::RustSyntax("number too large to fit in target type".into()),
        ),
        (
            "label = 1",
            SyntaxErrorKind::UnknownArgument {
                name: "label".into(),
            },
        ),
    ] {
        let error = krs_syntax::SimplificationAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn total_function_requires_and_anchors_total_sort_syntax_and_hook() {
    let parsed = krs_syntax::FunctionAttribute::parse_source(
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
    assert_eq!(hook_anchor.key().role(), ProvenanceRole::FunctionHook);
    assert_eq!(hook_anchor.key().ordinal(), 0);
}

#[test]
fn function_accepts_partial_and_rejects_missing_or_duplicate_totality() {
    let partial = krs_syntax::FunctionAttribute::parse_source(
        r#"partial, sort = Int, syntax = "f({value})""#,
    )
    .unwrap();
    assert!(!partial.is_total());
    for (source, expected_kind) in [
        (
            r#"sort = Int, syntax = "f({value})""#,
            SyntaxErrorKind::MissingArgument { name: "total" },
        ),
        (
            r#"total, partial, sort = Int, syntax = "f({value})""#,
            SyntaxErrorKind::DuplicateArgument { name: "totality" },
        ),
        (
            r#"total, sort = Int, syntax = "f({value})", hook = krypto::keccak256_raw, hook = krypto::keccak256_raw"#,
            SyntaxErrorKind::DuplicateArgument { name: "hook" },
        ),
        (
            r"total, sort = Int",
            SyntaxErrorKind::MissingArgument { name: "syntax" },
        ),
    ] {
        let error = krs_syntax::FunctionAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn rule_accepts_an_exact_k_label_and_anchors_its_literal() {
    let attribute = krs_syntax::RuleAttribute::parse_source(r#"owise, label = "if-true""#).unwrap();
    assert_eq!(attribute.label().unwrap().value(), "if-true");
    assert!(attribute.is_owise());
    let anchors = attribute.provenance().unwrap();
    assert_eq!(anchors.len(), 2);
    assert_eq!(anchors[0].role(), ProvenanceRole::RuleLabel);
    assert_eq!(anchors[0].key().role(), ProvenanceRole::RuleLabel);
    assert_eq!(anchors[1].role(), ProvenanceRole::RuleOwise);
    assert_eq!(anchors[1].key().role(), ProvenanceRole::RuleOwise);
}

#[test]
fn rule_accepts_a_transition_priority_and_anchors_its_literal() {
    let attribute =
        krs_syntax::RuleAttribute::parse_source(r#"priority = 40, label = "prefer-heads""#)
            .unwrap();
    assert_eq!(attribute.priority(), Some(40));
    assert!(!attribute.is_owise());
    assert_eq!(
        attribute.transition_priority(),
        Some((ProvenanceRole::RulePriority, 40))
    );
    let anchors = attribute.provenance().unwrap();
    assert_eq!(anchors.len(), 2);
    assert_eq!(anchors[1].role(), ProvenanceRole::RulePriority);
    let owise = krs_syntax::RuleAttribute::parse_source("owise").unwrap();
    assert_eq!(
        owise.transition_priority(),
        Some((ProvenanceRole::RuleOwise, 200))
    );
    let edge = krs_syntax::RuleAttribute::parse_source("priority = 254").unwrap();
    assert_eq!(edge.priority(), Some(254));
}

#[test]
fn rule_accepts_anywhere_and_rejects_it_beside_ordering_keys() {
    let attribute =
        krs_syntax::RuleAttribute::parse_source(r#"anywhere, label = "reassociate""#).unwrap();
    assert!(attribute.anywhere().is_some());
    let anchors = attribute.provenance().unwrap();
    assert_eq!(anchors[1].role(), ProvenanceRole::RuleAnywhere);
    for source in [
        "anywhere, owise",
        "priority = 40, anywhere",
        "anywhere, nondet = g",
    ] {
        let error = krs_syntax::RuleAttribute::parse_source(source).unwrap_err();
        assert_eq!(
            error.kind(),
            &SyntaxErrorKind::InvalidRuleKey {
                reason: "an anywhere rule applies to any subterm, outside rule priority and the overlap check; it takes no `owise`, `priority`, or `nondet`",
            },
            "{source}"
        );
    }
    let error = krs_syntax::RuleAttribute::parse_source("anywhere, anywhere").unwrap_err();
    assert_eq!(
        error.kind(),
        &SyntaxErrorKind::DuplicateArgument { name: "anywhere" }
    );
}

#[test]
fn rule_accepts_a_nondet_group_and_functions_reject_it() {
    let attribute = krs_syntax::RuleAttribute::parse_source("nondet = toss").unwrap();
    assert_eq!(attribute.nondet().unwrap(), "toss");
    assert_eq!(
        attribute.provenance().unwrap()[0].role(),
        ProvenanceRole::RuleNondetGroup
    );
    let reason =
        "functions are deterministic in K; overlapping equations make the function ill-defined";
    let equation = krs_syntax::EquationAttribute::parse_source("nondet = g").unwrap_err();
    let simplification =
        krs_syntax::SimplificationAttribute::parse_source("nondet = g").unwrap_err();
    let alias = krs_syntax::AliasAttribute::parse_source("nondet = g").unwrap_err();
    for error in [equation, simplification, alias] {
        assert_eq!(error.kind(), &SyntaxErrorKind::InvalidRuleKey { reason });
    }
}

#[test]
fn rule_rejects_unknown_duplicate_non_string_and_invalid_labels() {
    let cases = [
        (
            "unknown = \"x\"",
            SyntaxErrorKind::UnknownArgument {
                name: "unknown".into(),
            },
        ),
        (
            "label = \"first\", label = \"second\"",
            SyntaxErrorKind::DuplicateArgument { name: "label" },
        ),
        (
            "owise, owise",
            SyntaxErrorKind::DuplicateArgument { name: "owise" },
        ),
        (
            "owise, priority = 40",
            SyntaxErrorKind::InvalidRuleKey {
                reason: "owise is priority 200; write one of them",
            },
        ),
        (
            "priority = 255",
            SyntaxErrorKind::InvalidRuleKey {
                reason: "k-rust ranks rule priorities 0..=254",
            },
        ),
        (
            "priority = 40u8",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "priority",
                expected: "an unsuffixed integer literal",
            },
        ),
        (
            "priority = 1, priority = 2",
            SyntaxErrorKind::DuplicateArgument { name: "priority" },
        ),
        (
            "label = identifier",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "label",
                expected: "a Rust string literal",
            },
        ),
        (
            "label = \"\"",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "label",
                expected: "a nonempty K rule label using ASCII letters, digits, `_`, or `-` and beginning with a letter",
            },
        ),
        (
            "label = \"1starts-with-digit\"",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "label",
                expected: "a nonempty K rule label using ASCII letters, digits, `_`, or `-` and beginning with a letter",
            },
        ),
        (
            "label = \"contains space\"",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "label",
                expected: "a nonempty K rule label using ASCII letters, digits, `_`, or `-` and beginning with a letter",
            },
        ),
        (
            "label = \"contains/slash\"",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "label",
                expected: "a nonempty K rule label using ASCII letters, digits, `_`, or `-` and beginning with a letter",
            },
        ),
    ];
    for (source, expected_kind) in cases {
        let error = krs_syntax::RuleAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn marker_attributes_and_sort_reject_unknown_payload_at_first_token() {
    let error = krs_syntax::SortAttribute::parse_source("unexpected").unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::UnknownArgument { name } if name == "unexpected"
    ));
    assert_eq!(error.span().start().column, 0);
}

#[test]
fn constructor_accepts_required_sort_and_optional_template_in_any_order() {
    let parsed = krs_syntax::ConstructorAttribute::parse_source(
        r#"syntax = r"{lhs} + {rhs}", sort = crate::syntax::Expr,"#,
    )
    .unwrap();
    assert_eq!(parsed.syntax.as_ref().unwrap().value(), "{lhs} + {rhs}");
    assert_eq!(parsed.sort.segments.last().unwrap().ident, "Expr");

    let anchors = parsed.provenance().unwrap();
    assert_eq!(anchors.len(), 2);
    assert_eq!(anchors[0].role(), ProvenanceRole::ConstructorSort);
    assert_eq!(anchors[0].key().role(), ProvenanceRole::ConstructorSort);
    assert_eq!(anchors[1].role(), ProvenanceRole::ConstructorSyntax);
}

#[test]
fn constructor_syntax_is_optional() {
    let parsed = krs_syntax::ConstructorAttribute::parse_source("sort = Value").unwrap();
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
        let error = krs_syntax::ConstructorAttribute::parse_source(source).unwrap_err();
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
    let error =
        krs_syntax::ConstructorAttribute::parse_source("sort = Value,\nsort = Expr").unwrap_err();
    let start = error.span().start();
    assert_eq!((start.line, start.column), (2, 0));
}

#[test]
fn desugar_clause_rejects_recursive_and_other_payloads() {
    krs_syntax::DesugarAttribute::parse_source("").unwrap();
    for (source, expected_kind) in [
        (
            "recursive",
            SyntaxErrorKind::InvalidRuleKey {
                reason: krs_syntax::RECURSIVE_ON_CLAUSE,
            },
        ),
        (
            "priority = 40",
            SyntaxErrorKind::InvalidRuleKey {
                reason: "static rules have no priority",
            },
        ),
        (
            "owise",
            SyntaxErrorKind::InvalidRuleKey {
                reason: "static rules have no priority",
            },
        ),
        (
            "true",
            SyntaxErrorKind::UnexpectedAttributePayload {
                attribute: "desugar",
            },
        ),
    ] {
        let error = krs_syntax::DesugarAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn static_production_markers_accept_only_recursive() {
    use krs_syntax::{StaticMode, StaticProductionAttribute};
    for mode in [StaticMode::Alias, StaticMode::Desugar] {
        let plain = StaticProductionAttribute::parse_marker(mode, TokenStream::new()).unwrap();
        assert_eq!(plain.mode(), mode);
        assert!(!plain.is_recursive());
        assert!(plain.provenance().is_empty());
        let recursive =
            StaticProductionAttribute::parse_marker(mode, "recursive".parse().unwrap()).unwrap();
        assert!(recursive.is_recursive());
        assert_eq!(recursive.provenance().len(), 1);
        for (source, expected_kind) in [
            (
                "unbound_variables = [x]",
                SyntaxErrorKind::UnknownArgument {
                    name: "unbound_variables".to_owned(),
                },
            ),
            (
                "recursive, recursive",
                SyntaxErrorKind::UnexpectedAttributePayload {
                    attribute: "recursive",
                },
            ),
            (
                "priority = 40",
                SyntaxErrorKind::InvalidRuleKey {
                    reason: "static rules have no priority",
                },
            ),
            (
                "\"recursive\"",
                SyntaxErrorKind::UnexpectedAttributePayload {
                    attribute: mode.name(),
                },
            ),
        ] {
            let error =
                StaticProductionAttribute::parse_marker(mode, source.parse().unwrap()).unwrap_err();
            assert_eq!(error.kind(), &expected_kind, "{source}");
        }
    }
}

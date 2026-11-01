//! Attribute payload parser acceptance, rejection, and span tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{ProvenanceRole, SyntaxErrorKind};
use proc_macro2::TokenStream;
use quote::ToTokens;

/// The refusal of an order on a static clause, whose clauses never overlap.
const STATIC_CLAUSE_ORDER: &str = "a static production's clauses rewrite each of its applications into one term as it is read, so they never overlap and none is chosen against another: an order (`owise`, `priority`, `nondet`) means nothing on a clause";

#[test]
fn empty_marker_attributes_are_accepted() {
    let sort = krs_syntax::SortAttribute::parse_source("").unwrap();
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
    assert_eq!(alias.alias().unwrap(), "Expr");
    assert!(alias.parents().is_empty());

    let inherited =
        krs_syntax::SortAttribute::parse_source("parents = [Expr, k::KResult], alias = Value,")
            .unwrap();
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
fn sort_alias_names_the_marker_trait() {
    let marker = |source: &str| syn::parse_str::<syn::Ident>(source).unwrap();
    let alias = krs_syntax::SortAttribute::parse_source("alias = Expr").unwrap();
    assert_eq!(alias.checked_alias(&marker("ExprSort")).unwrap(), "Expr");
    let anchors = alias.provenance(&marker("ExprSort")).unwrap();
    assert_eq!(anchors.len(), 1);
    assert_eq!(anchors[0].role(), ProvenanceRole::SortDeclaration);

    let error = alias.checked_alias(&marker("Expression")).unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::UnaliasedSort { .. }
    ));
    assert!(
        error
            .to_string()
            .contains("the marker trait of the sort alias `Expr` is named `ExprSort`")
    );

    let unaliased = krs_syntax::SortAttribute::parse_source("").unwrap();
    let error = unaliased.checked_alias(&marker("Expr")).unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::UnaliasedSort { .. }
    ));
    assert!(error.to_string().contains(
        "write `#[k::sort(alias = Expr)] pub trait ExprSort {}` with `pub type Expr = k::Term<dyn ExprSort>;`"
    ));
    let error = unaliased.checked_alias(&marker("ExprSort")).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("#[k::sort(alias = Expr)] pub trait ExprSort {}")
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
fn constructors_distinguishes_readable_and_reference_families() {
    for source in ["sort = Expr", "sort = Expr, internal"] {
        let error = krs_syntax::ConstructorsAttribute::parse_source(source).unwrap_err();
        let SyntaxErrorKind::UnsupportedEnumConstructorDeclaration { reason } = error.kind() else {
            panic!("{source}: {:?}", error.kind());
        };
        assert!(reason.contains("`result = KResult`"), "{reason}");
        assert!(reason.contains("`k::sorts!`"), "{reason}");
    }

    let readable =
        krs_syntax::ConstructorsAttribute::parse_source("result = KResult, sort = Expr,").unwrap();
    assert!(!readable.is_reference());
    assert_eq!(
        readable.result().unwrap().to_token_stream().to_string(),
        "KResult"
    );

    let reference =
        krs_syntax::ConstructorsAttribute::parse_source("reference, sort = Expr").unwrap();
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
            SyntaxErrorKind::UnknownArgument {
                name: "true".into(),
            },
        ),
        (
            "mode = recursive",
            SyntaxErrorKind::UnknownArgument {
                name: "mode".into(),
            },
        ),
        (
            "\"recursive\"",
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
            "name = execute, here = site, label = \"l\"",
            SyntaxErrorKind::UnknownArgument {
                name: "label".into(),
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

/// A label names the one sentence an equation or a simplification marker states, in place of
/// its fn's or row's name, as a rule's does.
#[test]
fn equation_and_simplification_take_a_label_and_anchor_it() {
    let equation = krs_syntax::EquationAttribute::parse_source(r#"label = "named""#).unwrap();
    assert_eq!(equation.label().unwrap().value(), "named");
    assert_eq!(
        equation.provenance().unwrap()[0].role(),
        ProvenanceRole::RuleLabel
    );
    let simplification =
        krs_syntax::SimplificationAttribute::parse_source(r#"label = "named", priority = 20"#)
            .unwrap();
    assert_eq!(simplification.label().unwrap().value(), "named");
    let error =
        krs_syntax::EquationAttribute::parse_source(r#"label = "a", label = "b""#).unwrap_err();
    assert_eq!(
        error.kind(),
        &SyntaxErrorKind::DuplicateArgument { name: "label" }
    );
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
                reason: "owise applies where no other rule or equation applies, which no priority orders; write one of them",
            },
        ),
        (
            "priority = 40, owise",
            SyntaxErrorKind::InvalidRuleKey {
                reason: "owise applies where no other rule or equation applies, which no priority orders; write one of them",
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
            replacement: Some("#[k::equation(priority = 40)]".into()),
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
                reason: STATIC_CLAUSE_ORDER,
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
            SyntaxErrorKind::InvalidArgumentValue {
                name: "label",
                expected: "a Rust string literal",
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
    ] {
        let error = krs_syntax::FunctionAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
    // An omitted `syntax` is completed from the declaration, which knows
    // whether the production is program syntax.
    let attribute = krs_syntax::FunctionAttribute::parse_source("total, sort = Int").unwrap();
    assert!(!attribute.has_authored_syntax());
    assert!(attribute.production().syntax_template().is_none());
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
    for error in [equation, simplification] {
        assert_eq!(error.kind(), &SyntaxErrorKind::InvalidRuleKey { reason });
    }
    // A static clause is no function: its clauses never overlap, so no order means anything there.
    let alias = krs_syntax::AliasAttribute::parse_source("nondet = g").unwrap_err();
    assert_eq!(
        alias.kind(),
        &SyntaxErrorKind::InvalidRuleKey {
            reason: STATIC_CLAUSE_ORDER
        }
    );
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
                reason: "owise applies where no other rule or equation applies, which no priority orders; write one of them",
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

    // The sort and the syntax come first, then the template's items.
    let anchors = parsed.full_provenance().unwrap();
    assert_eq!(anchors.len(), 7);
    assert_eq!(anchors[0].role(), ProvenanceRole::ConstructorSort);
    assert_eq!(anchors[0].key().role(), ProvenanceRole::ConstructorSort);
    assert_eq!(anchors[1].role(), ProvenanceRole::ConstructorSyntax);
    // The constructor descriptor denotes the sort alone; the syntax is the
    // grammar descriptor's.
    let sort = parsed.constructor_sort_provenance().unwrap();
    assert_eq!(sort.len(), 1);
    assert_eq!(sort[0].key(), anchors[0].key());
}

#[test]
fn constructor_syntax_is_optional() {
    let parsed = krs_syntax::ConstructorAttribute::parse_source("sort = Value").unwrap();
    assert!(parsed.syntax.is_none());
    assert_eq!(parsed.full_provenance().unwrap().len(), 1);
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
fn desugar_clause_accepts_unbound_variables() {
    let attribute =
        krs_syntax::DesugarAttribute::parse_source("unbound_variables = [x, _, r#y]").unwrap();
    let unbound = attribute.unbound_variables().unwrap();
    assert_eq!(unbound.key(), "unbound_variables");
    assert_eq!(
        unbound.names().map(ToString::to_string).collect::<Vec<_>>(),
        ["x", "r#y"]
    );
    assert!(unbound.wildcard().is_some());
    let anchors = attribute.provenance().unwrap();
    assert_eq!(
        anchors
            .iter()
            .map(|anchor| (anchor.role(), anchor.ordinal()))
            .collect::<Vec<_>>(),
        [
            (ProvenanceRole::UnboundVariables, 0),
            (ProvenanceRole::UnboundVariable, 0),
            (ProvenanceRole::UnboundVariable, 1),
            (ProvenanceRole::UnboundVariable, 2),
        ]
    );
    assert!(
        krs_syntax::DesugarAttribute::parse_source("")
            .unwrap()
            .unbound_variables()
            .is_none()
    );
}

#[test]
fn desugar_clause_rejects_malformed_unbound_variables() {
    for (source, reason) in [
        (
            "unbound_variables = []",
            "`unbound_variables = []` lists nothing; list the result's names the pattern does not bind, or omit the key",
        ),
        (
            "unbound_variables = [x, x]",
            "`x` is listed twice in `unbound_variables`",
        ),
        (
            "unbound_variables = [_, _]",
            "`_` is listed twice in `unbound_variables`",
        ),
        (
            "unbound_variables = [x], recursive",
            "a desugar clause takes only `unbound_variables = [..]`",
        ),
    ] {
        let error = krs_syntax::DesugarAttribute::parse_source(source).unwrap_err();
        assert_eq!(
            error.kind(),
            &SyntaxErrorKind::InvalidUnboundVariables {
                reason: reason.to_owned()
            },
            "{source}"
        );
        assert_eq!(
            error.kind().code().as_str(),
            "krs::syntax::invalid-unbound-variables"
        );
    }
}

#[test]
fn unbound_variables_is_rejected_outside_desugar_clauses() {
    let expected = SyntaxErrorKind::InvalidUnboundVariables {
        reason: krs_syntax::UNBOUND_VARIABLES_OUTSIDE_DESUGAR_CLAUSE.to_owned(),
    };
    let source = "unbound_variables = [x]";
    for error in [
        krs_syntax::AliasAttribute::parse_source(source).unwrap_err(),
        krs_syntax::RuleAttribute::parse_source(source).unwrap_err(),
        krs_syntax::EquationAttribute::parse_source(source).unwrap_err(),
        krs_syntax::SimplificationAttribute::parse_source(source).unwrap_err(),
        krs_syntax::ClaimAttribute::parse_source(source).unwrap_err(),
        krs_syntax::ClaimAttribute::parse_source(
            r#"all_paths, label = "c", unbound_variables = [x]"#,
        )
        .unwrap_err(),
        krs_syntax::ContextAttribute::parse_source("hole = h, unbound_variables = [x]")
            .unwrap_err(),
        krs_syntax::ContextAliasAttribute::parse_source("name = n, unbound_variables = [x]")
            .unwrap_err(),
    ] {
        assert_eq!(error.kind(), &expected);
    }
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
                reason: STATIC_CLAUSE_ORDER,
            },
        ),
        (
            "owise",
            SyntaxErrorKind::InvalidRuleKey {
                reason: STATIC_CLAUSE_ORDER,
            },
        ),
        (
            "true",
            SyntaxErrorKind::UnknownArgument {
                name: "true".into(),
            },
        ),
        (
            "1",
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
                SyntaxErrorKind::InvalidUnboundVariables {
                    reason: krs_syntax::UNBOUND_VARIABLES_OUTSIDE_DESUGAR_CLAUSE.to_owned(),
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

/// A parser of one marker's payload.
type MarkerParser = fn(&str) -> Result<(), krs_syntax::SyntaxError>;

/// A marker's parser, with the keys it needs written before the case's key.
fn marker_parser(marker: krs_syntax::Marker) -> (&'static str, MarkerParser) {
    use krs_syntax::Marker;
    fn parse<T: KrsSyntax>(source: &str) -> Result<(), krs_syntax::SyntaxError> {
        T::parse_source(source).map(|_| ())
    }
    match marker {
        Marker::Rule => ("", parse::<krs_syntax::RuleAttribute>),
        Marker::Equation => ("", parse::<krs_syntax::EquationAttribute>),
        Marker::Simplification => ("", parse::<krs_syntax::SimplificationAttribute>),
        Marker::Claim => (
            "all_paths, label = \"c\", ",
            parse::<krs_syntax::ClaimAttribute>,
        ),
        Marker::Context => ("hole = h, ", parse::<krs_syntax::ContextAttribute>),
        Marker::ContextAlias => (
            "name = n, here = h, ",
            parse::<krs_syntax::ContextAliasAttribute>,
        ),
        Marker::StaticClause => ("", parse::<krs_syntax::AliasAttribute>),
        Marker::Initializer => ("", parse::<krs_syntax::InitAttribute>),
        Marker::Constant => ("", parse::<krs_syntax::ConstantAttribute>),
    }
}

/// A well-formed value of every sentence key.
fn key_source(key: &str) -> String {
    match key {
        "label" => "label = \"named\"".to_owned(),
        "priority" => "priority = 20".to_owned(),
        "nondet" => "nondet = g".to_owned(),
        "hole" | "name" | "here" => format!("{key} = x"),
        "result" => "result = KResult".to_owned(),
        "unbound_variables" => "unbound_variables = [y]".to_owned(),
        key => key.to_owned(),
    }
}

/// One mistake, one class, at the key (NT-33): every sentence key a marker does not take is
/// refused by `misplaced_key`, never by the parser's generic code or as a payload, so a key or a
/// marker added without its place in the table cannot fall through to a parse error.
#[test]
fn every_sentence_key_a_marker_does_not_take_is_refused_for_what_it_is_there() {
    for marker in krs_syntax::Marker::ALL {
        let (base, parse) = marker_parser(marker);
        for key in krs_syntax::SENTENCE_KEYS {
            let source = format!("{base}{}", key_source(key));
            let result = parse(&source);
            if marker.takes(key) {
                if let Err(error) = result {
                    // A key the marker takes may still need another (`heat` needs `hole`): its
                    // refusal is then the marker's own, never a parse error.
                    let code = error.kind().code();
                    assert_ne!(
                        code.as_str(),
                        "krs::syntax::rust-syntax",
                        "{marker:?} {source}"
                    );
                    assert_ne!(
                        code.as_str(),
                        "krs::syntax::unexpected-attribute-payload",
                        "{marker:?} {source}"
                    );
                }
                continue;
            }
            let error = result.expect_err(&format!("{marker:?} takes no {key}"));
            let expected = krs_syntax::misplaced_key_named(marker, key, error.span());
            assert_eq!(error.kind(), expected.kind(), "{marker:?} {source}");
            assert_eq!(
                error.span().start(),
                expected.span().start(),
                "{marker:?} {source}"
            );
        }
    }
}

/// The table answers each key for what it means: an order where nothing is ordered, a
/// restriction outside a function and `anywhere` outside a transition are the rule key's
/// mistake; any key on a declaration's marker is one it does not take.
#[test]
fn the_misplaced_key_table_names_the_mistake_by_its_code() {
    use krs_syntax::Marker;
    let code = |marker, key| {
        krs_syntax::misplaced_key_named(marker, key, proc_macro2::Span::call_site())
            .kind()
            .code()
            .as_str()
            .to_owned()
    };
    for (marker, key, expected) in [
        (Marker::Claim, "owise", "krs::syntax::invalid-rule-key"),
        (Marker::Context, "priority", "krs::syntax::invalid-rule-key"),
        (
            Marker::StaticClause,
            "nondet",
            "krs::syntax::invalid-rule-key",
        ),
        (Marker::Equation, "nondet", "krs::syntax::invalid-rule-key"),
        (
            Marker::Equation,
            "anywhere",
            "krs::syntax::invalid-rule-key",
        ),
        (Marker::Equation, "result", "krs::syntax::invalid-rule-key"),
        (Marker::Rule, "concrete", "krs::syntax::invalid-rule-key"),
        (Marker::Rule, "recursive", "krs::syntax::invalid-rule-key"),
        (Marker::Claim, "heat", "krs::syntax::unknown-argument"),
        (
            Marker::StaticClause,
            "label",
            "krs::syntax::unknown-argument",
        ),
        (
            Marker::Initializer,
            "owise",
            "krs::syntax::unknown-argument",
        ),
        (
            Marker::Constant,
            "unbound_variables",
            "krs::syntax::unknown-argument",
        ),
        (
            Marker::Rule,
            "unbound_variables",
            "krs::syntax::invalid-unbound-variables",
        ),
    ] {
        assert_eq!(code(marker, key), expected, "{marker:?} {key}");
    }
}

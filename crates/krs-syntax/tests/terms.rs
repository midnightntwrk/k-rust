//! Named term grammar and endpoint-preservation tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{ProvenanceRole, SyntaxErrorKind, TermRootKind, TermSymbolKind};

#[test]
fn named_call_terms_preserve_preorder_paths_and_exact_endpoints() {
    let source = "m::Outer(inner::Leaf(value))";
    let term = krs_syntax::TermExpression::parse_source(source).unwrap();
    assert_eq!(term.root_kind(), TermRootKind::Call);
    let symbols = term.symbols();
    assert_eq!(symbols.len(), 3);
    assert_eq!(symbols[0].kind(), TermSymbolKind::ApplicationHead);
    assert_eq!(symbols[0].path().segments.last().unwrap().ident, "Outer");
    assert_eq!(symbols[1].path().segments.last().unwrap().ident, "Leaf");
    assert_eq!(symbols[2].kind(), TermSymbolKind::Reference);

    let anchors = term.provenance().unwrap();
    assert_eq!(anchors[0].role(), ProvenanceRole::TermPayload);
    assert_eq!(
        (
            anchors[0].range().start().line,
            anchors[0].range().start().column
        ),
        (1, 0)
    );
    assert_eq!(
        (
            anchors[0].range().end().line,
            anchors[0].range().end().column
        ),
        (1, source.len())
    );
    assert_eq!(
        (
            anchors[1].range().start().column,
            anchors[1].range().end().column
        ),
        (0, 8)
    );
    assert_eq!(
        (
            anchors[2].range().start().column,
            anchors[2].range().end().column
        ),
        (9, 20)
    );
    assert_eq!(
        (
            anchors[3].range().start().column,
            anchors[3].range().end().column
        ),
        (21, 26)
    );
    assert_eq!(anchors[3].key().role(), ProvenanceRole::TermPath);
    assert_eq!(anchors[3].key().ordinal(), 2);
}

#[test]
fn record_and_unit_terms_are_accepted() {
    let record = krs_syntax::TermExpression::parse_source(
        "crate::Add { lhs, rhs: IntValue(1), flag: true }",
    )
    .unwrap();
    assert_eq!(record.root_kind(), TermRootKind::Record);
    assert_eq!(record.symbols().len(), 3);

    let unit = krs_syntax::TermExpression::parse_source("syntax::Done").unwrap();
    assert_eq!(unit.root_kind(), TermRootKind::Named);
}

#[test]
fn int_and_bool_literals_are_root_and_nested_nodes() {
    let integer = krs_syntax::TermExpression::parse_source("42").unwrap();
    assert_eq!(integer.root_kind(), TermRootKind::Literal);
    assert_eq!(integer.nodes().len(), 1);

    let boolean = krs_syntax::TermExpression::parse_source("bool_ops::not(false)").unwrap();
    assert_eq!(boolean.nodes().len(), 2);
    let anchors = boolean.full_provenance().unwrap();
    assert_eq!(anchors[1].role(), ProvenanceRole::TermApplicationHead);
    assert_eq!(anchors[2].role(), ProvenanceRole::TermLiteral);
}

#[test]
fn out_of_scope_rust_expressions_are_rejected() {
    for source in [
        "lhs + rhs",
        "value.method()",
        "if test { A } else { B }",
        "Ctor { field, ..base }",
        "42u32",
        "1.0",
        "'x'",
        "Ctor::<Value>(value)",
        "outer!(value)",
    ] {
        let error = krs_syntax::TermExpression::parse_source(source).unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::UnsupportedTermExpression { .. } | SyntaxErrorKind::UnsupportedPath
        ));
    }
}

//! Authored binders cannot forge generated semantic identities.

use krs_diagnostic::{Location, ToDiagnostic, codes};
use krs_syntax::{KrsSyntax, SyntaxError, SyntaxErrorKind};

fn assert_reserved(error: &SyntaxError, source: &str, binder: &str) {
    assert_eq!(error.kind(), &SyntaxErrorKind::ReservedBinder);
    let diagnostic = error.to_diagnostic();
    assert_eq!(diagnostic.code, codes::syntax::RESERVED_BINDER);
    assert!(error.to_string().contains(krs_ir::ir::RESERVED_MARKER));
    assert!(
        error
            .to_string()
            .contains("reserved for generated identifiers")
    );
    let start = source.find(binder).unwrap();
    assert_eq!(error.span().start().line, 1);
    assert_eq!(error.span().start().column, start);
    assert_eq!(error.span().end().column, start + binder.len());
    assert!(matches!(diagnostic.primary.location, Location::Span(_)));
}

#[test]
fn native_and_term_subject_binders_reject_reserved_encodings() {
    for binder in ["__krs_wildcard_1", "_x__krs_3", "a__krs_b"] {
        for pattern in [format!("Foo({binder})"), format!("term![Foo({binder})]")] {
            let source = format!("fn step({pattern}: Term<Expr>) -> Term<Expr> {{ Done }}");
            assert_reserved(
                &krs_syntax::RuleItem::parse_source(&source).unwrap_err(),
                &source,
                binder,
            );
        }
    }
}

#[test]
fn state_term_and_frame_binders_reject_reserved_encodings() {
    for binder in ["__krs_wildcard_1", "_x__krs_3"] {
        for subject in [
            format!("k: KCell({binder}, tail @ ..), state @ .."),
            format!("k: KCell(0, {binder} @ ..), state @ .."),
            format!("k: KCell(0, tail @ ..), {binder} @ .."),
            format!("k: KCell(0, tail @ ..), env: Cell(map![0 -> {binder}]), state @ .."),
            format!("k: KCell(0, tail @ ..), env: Cell(map![{binder} @ ..]), state @ .."),
        ] {
            let source = format!(
                "fn step(cells! {{ {subject} }}: Machine) -> Machine {{ cells! {{ k: KCell(0, ..tail), ..state }} }}"
            );
            assert_reserved(
                &krs_syntax::StateRuleItem::parse_source(&source).unwrap_err(),
                &source,
                binder,
            );
        }
        let source = format!(
            "fn step({binder}: Term<Int>, cells! {{ k: KCell(0, tail @ ..), state @ .. }}: Machine) -> Machine {{ cells! {{ k: KCell(0, ..tail), ..state }} }}"
        );
        assert_reserved(
            &krs_syntax::StateRuleItem::parse_source(&source).unwrap_err(),
            &source,
            binder,
        );
    }
}

#[test]
fn existential_and_initializer_binders_reject_reserved_encodings() {
    for binder in ["__krs_wildcard_1", "_x__krs_3"] {
        let source = format!("{binder}: Int");
        assert_reserved(
            &krs_syntax::ExistsAttribute::parse_source(&source).unwrap_err(),
            &source,
            binder,
        );
        let source = format!(
            "fn init({binder}: Term<Expr>) -> Self {{ Self {{ k: KCell::new(k![{binder}]) }} }}"
        );
        assert_reserved(
            &krs_syntax::InitializerFunction::parse_source(&source).unwrap_err(),
            &source,
            binder,
        );
    }
}

#[test]
fn anonymous_spelling_rejects_reserved_encodings() {
    for binder in ["__krs_wildcard_1", "_x__krs_3"] {
        let literal = format!("\"{binder}\"");
        let source = format!("k::anonymous!(Int, {literal})");
        assert_reserved(
            &krs_syntax::TermExpression::parse_source(&source).unwrap_err(),
            &source,
            &literal,
        );
    }
}

#[test]
fn ordinary_binders_wildcards_anonymous_spelling_and_item_names_remain_accepted() {
    for binder in ["x", "_x", "__x"] {
        krs_syntax::RuleItem::parse_source(&format!(
            "fn a__krs_b(__krs_wildcard_1({binder}, _): Term<Expr>) -> Term<Expr> {{ _x__krs_3({binder}) }}"
        ))
        .unwrap();
    }
    krs_syntax::RuleItem::parse_source(
        "fn a__krs_b(_x__krs_3: Term<Expr>) -> Term<Expr> { __krs_wildcard_1 }",
    )
    .unwrap();
    krs_syntax::TermExpression::parse_source("k::anonymous!(Int, \"_x\")").unwrap();
    krs_syntax::ConstructorDeclaration::parse_source("struct a__krs_b;").unwrap();
}

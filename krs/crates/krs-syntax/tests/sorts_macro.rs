//! Folded sort-block parser and provenance tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{ProvenanceRole, SortsEntry, SyntaxErrorKind};

#[test]
fn declarations_bounds_brackets_and_memberships_preserve_order() {
    let declaration = krs_syntax::SortsDeclaration::parse_source(
        r#"
            #[k::bracket("(", ")")]
            Expr;
            impl Expr for builtin::Id;
            Value: Expr + k::KResult;
            impl Value for builtin::Int, builtin::Bool;
            Stmt;
        "#,
    )
    .unwrap();
    assert_eq!(declaration.entries().len(), 5);

    let SortsEntry::Sort(expr) = &declaration.entries()[0] else {
        panic!("first entry must be Expr")
    };
    assert_eq!(expr.name(), "Expr");
    assert_eq!(expr.brackets().len(), 1);
    assert_eq!(
        expr.bracket_provenance(&expr.brackets()[0])
            .unwrap()
            .iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::BracketValueReference)
            .count(),
        1
    );

    let SortsEntry::Sort(value) = &declaration.entries()[2] else {
        panic!("third entry must be Value")
    };
    assert_eq!(value.parents().len(), 2);
    assert_eq!(
        value
            .provenance()
            .unwrap()
            .iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::SortParent)
            .count(),
        2
    );

    let SortsEntry::Membership(membership) = &declaration.entries()[3] else {
        panic!("fourth entry must be Value membership")
    };
    assert_eq!(membership.members().len(), 2);
    for member in membership.members() {
        let anchors = membership.member_provenance(member).unwrap();
        assert_eq!(anchors[0].role(), ProvenanceRole::SubsortDeclaration);
        assert_eq!(anchors[1].role(), ProvenanceRole::SubsortSuperSort);
        assert_eq!(anchors[2].role(), ProvenanceRole::SubsortSubSort);
    }
}

#[test]
fn membership_only_blocks_are_supported() {
    let declaration =
        krs_syntax::SortsDeclaration::parse_source("impl crate::Expr for crate::Feature;").unwrap();
    assert!(matches!(declaration.entries(), [SortsEntry::Membership(_)]));
}

#[test]
fn malformed_or_ambiguous_lines_are_rejected_locally() {
    for (source, expected_kind) in [
        (
            "",
            SyntaxErrorKind::RustSyntax(
                "unexpected end of input, `sorts!` requires at least one sort or membership line"
                    .into(),
            ),
        ),
        ("Expr", SyntaxErrorKind::RustSyntax("expected `;`".into())),
        (
            "Value:;",
            SyntaxErrorKind::RustSyntax("expected identifier".into()),
        ),
        (
            "impl Value Int;",
            SyntaxErrorKind::RustSyntax("expected `for`".into()),
        ),
        (
            "impl Value for;",
            SyntaxErrorKind::RustSyntax("expected identifier".into()),
        ),
        (
            "impl Value for Int,;",
            SyntaxErrorKind::RustSyntax("expected a member type after `,`".into()),
        ),
        (
            "#[k::unknown] Expr;",
            SyntaxErrorKind::RustSyntax(
                "only `#[k::bracket(...)]` is supported on a `sorts!` declaration".into(),
            ),
        ),
        (
            "#[k::bracket(\"(\", \")\")] impl Expr for Id;",
            SyntaxErrorKind::RustSyntax(
                "membership lines in `sorts!` do not accept attributes".into(),
            ),
        ),
        (
            "impl Value<T> for Int;",
            SyntaxErrorKind::RustSyntax("expected `for`".into()),
        ),
    ] {
        let error = krs_syntax::SortsDeclaration::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

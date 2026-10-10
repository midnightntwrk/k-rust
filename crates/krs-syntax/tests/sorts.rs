//! Sort marker-trait parser tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{ProvenanceRole, SyntaxErrorKind};

#[test]
fn marker_sort_preserves_parent_paths_and_order() {
    let sort = krs_syntax::SortDeclaration::parse_source(
        "pub trait ValueSort: crate::ExprSort + super::KResultSort {}",
    )
    .unwrap();
    assert_eq!(sort.item().ident, "ValueSort");
    assert_eq!(sort.parents().len(), 2);
    assert_eq!(sort.parents()[0].segments.last().unwrap().ident, "ExprSort");

    let attribute =
        krs_syntax::SortAttribute::parse_source("alias = Value, parents = [Expr, KResult]")
            .unwrap();
    let marker = syn::parse_str::<syn::Ident>("ValueSort").unwrap();
    let anchors = attribute.provenance(&marker).unwrap();
    assert_eq!(anchors[0].role(), ProvenanceRole::SortDeclaration);
    assert_eq!(anchors[1].key().role(), ProvenanceRole::SortParent);
    assert_eq!(anchors[1].ordinal(), 0);
    assert_eq!(anchors[2].ordinal(), 1);
}

#[test]
fn non_marker_sort_shapes_are_rejected() {
    for source in [
        "trait Generic<T> {}",
        "trait WithItem { type Value; }",
        "trait Lifetime: 'static {}",
        "trait Optional: ?Sized {}",
        "unsafe trait Unsafe {}",
    ] {
        let error = krs_syntax::SortDeclaration::parse_source(source).unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::UnsupportedSortDeclaration { .. } | SyntaxErrorKind::RustSyntax(_)
        ));
    }
}

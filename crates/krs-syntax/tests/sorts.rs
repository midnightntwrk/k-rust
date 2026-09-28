//! Sort marker-trait parser tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{ProvenanceRole, SyntaxErrorKind};

#[test]
fn marker_sort_preserves_parent_paths_and_order() {
    let sort = krs_syntax::SortDeclaration::parse_source(
        "pub trait Value: crate::Expr + super::KResult {}",
    )
    .unwrap();
    assert_eq!(sort.item().ident, "Value");
    assert_eq!(sort.parents().len(), 2);
    assert_eq!(sort.parents()[0].segments.last().unwrap().ident, "Expr");

    let anchors = sort.provenance().unwrap();
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

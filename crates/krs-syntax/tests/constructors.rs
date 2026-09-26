//! Unit and record constructor declaration parser tests.

use krs_syntax::{ProvenanceRole, SyntaxErrorKind, parse_constructor_declaration_source};

#[test]
fn unit_and_named_record_constructors_preserve_original_items() {
    let unit = parse_constructor_declaration_source("pub struct Halt;").unwrap();
    assert_eq!(unit.name(), "Halt");
    assert!(unit.fields().is_empty());
    assert!(matches!(unit.item().fields, syn::Fields::Unit));

    let record = parse_constructor_declaration_source(
        "#[derive(Clone)] pub struct Add { \
         pub lhs: krs::Term<dyn model::Expr>, \
         rhs: Term<crate::value::Value> \
         }",
    )
    .unwrap();
    assert_eq!(record.item().attrs.len(), 1);
    assert_eq!(record.name(), "Add");
    assert_eq!(record.fields().len(), 2);
    assert_eq!(record.fields()[0].name(), "lhs");
    assert_eq!(record.fields()[1].name(), "rhs");
    assert_eq!(
        record.fields()[0].term_sort().sort_spelling(),
        "model :: Expr"
    );
    assert!(record.fields()[0].term_sort().is_dynamic());
    assert_eq!(
        record.fields()[1].term_sort().sort_spelling(),
        "crate :: value :: Value"
    );
    assert!(!record.fields()[1].term_sort().is_dynamic());
}

#[test]
fn constructor_provenance_keys_declaration_and_inner_field_sorts() {
    let constructor = parse_constructor_declaration_source(
        "struct Pair { left: Term<dyn syntax::Expr>, right: Term<value::Value> }",
    )
    .unwrap();
    let anchors = constructor.provenance().unwrap();

    assert_eq!(anchors.len(), 3);
    assert_eq!(anchors[0].role(), ProvenanceRole::ConstructorDeclaration);
    assert_eq!(anchors[0].key().unwrap().role(), "constructor_declaration");
    assert_eq!(anchors[1].role(), ProvenanceRole::ConstructorFieldSort);
    assert_eq!(anchors[1].ordinal(), 0);
    assert_eq!(anchors[2].ordinal(), 1);
    assert_eq!(anchors[1].key().unwrap().role(), "constructor_field_sort");
    assert_eq!(anchors[1].range().start().column, 29);
    assert_eq!(anchors[1].range().end().column, 41);
}

#[test]
fn production_rustdoc_is_normalized_and_has_exact_full_provenance() {
    let constructor = parse_constructor_declaration_source(
        "/// First line.\n#[doc = \"Second line.\"]\nstruct Documented;",
    )
    .unwrap();
    assert_eq!(
        constructor
            .documentation()
            .iter()
            .map(krs_syntax::ProductionDocumentation::text)
            .collect::<Vec<_>>(),
        ["First line.", "Second line."],
    );
    let documentation = constructor
        .full_provenance()
        .unwrap()
        .into_iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::ConstructorDocumentation)
        .collect::<Vec<_>>();
    assert_eq!(
        documentation
            .iter()
            .map(krs_syntax::ProvenanceAnchor::ordinal)
            .collect::<Vec<_>>(),
        [0, 1],
    );

    let error = parse_constructor_declaration_source(
        "#[doc = concat!(\"not literal\")] struct DynamicDoc;",
    )
    .unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::UnsupportedConstructorDeclaration { .. }
    ));
}

#[test]
fn tuple_generic_where_and_attributed_field_shapes_are_rejected() {
    let cases = [
        "struct Tuple(Term<Expr>);",
        "struct Generic<T> { value: Term<T> }",
        "struct Where where Expr: Sort { value: Term<Expr> }",
        "struct Attributed { #[cfg(any())] value: Term<Expr> }",
    ];

    for source in cases {
        let error = parse_constructor_declaration_source(source).unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::UnsupportedConstructorDeclaration { .. }
        ));
        assert_ne!(error.span().start().column, 0, "{source}");
    }
}

#[test]
fn fields_without_unambiguous_object_sort_types_are_rejected() {
    for source in [
        "struct RawBuiltin { value: Int }",
        "struct GenericSort { value: Term<Vec<Expr>> }",
        "struct MultipleBounds { value: Term<dyn Expr + Value> }",
        "struct Reference { value: &'static Term<Expr> }",
    ] {
        let error = parse_constructor_declaration_source(source).unwrap_err();
        assert!(matches!(error.kind(), SyntaxErrorKind::InvalidTermType));
    }
}

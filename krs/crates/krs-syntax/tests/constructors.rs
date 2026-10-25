//! Unit and record constructor declaration parser tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{ProvenanceRole, SyntaxErrorKind};

#[test]
fn unit_and_named_record_constructors_preserve_original_items() {
    let unit = krs_syntax::ConstructorDeclaration::parse_source("pub struct Halt;").unwrap();
    assert_eq!(unit.name(), "Halt");
    assert!(unit.fields().is_empty());
    assert!(matches!(unit.item().fields, syn::Fields::Unit));

    let record = krs_syntax::ConstructorDeclaration::parse_source(
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
        record.fields()[0].term_sort().sort_token_text(),
        "model :: Expr"
    );
    assert!(record.fields()[0].term_sort().is_dynamic());
    assert_eq!(
        record.fields()[1].term_sort().sort_token_text(),
        "crate :: value :: Value"
    );
    assert!(!record.fields()[1].term_sort().is_dynamic());
}

#[test]
fn constructor_provenance_keys_declaration_and_inner_field_sorts() {
    let constructor = krs_syntax::ConstructorDeclaration::parse_source(
        "struct Pair { left: Term<dyn syntax::Expr>, right: Term<value::Value> }",
    )
    .unwrap();
    let anchors = constructor.full_provenance().unwrap();

    assert_eq!(anchors.len(), 5);
    assert_eq!(anchors[0].role(), ProvenanceRole::ConstructorDeclaration);
    assert_eq!(
        anchors[0].key().role(),
        ProvenanceRole::ConstructorDeclaration
    );
    assert_eq!(anchors[1].role(), ProvenanceRole::ConstructorFieldSort);
    assert_eq!(anchors[1].ordinal(), 0);
    assert_eq!(anchors[2].ordinal(), 1);
    assert_eq!(
        anchors[1].key().role(),
        ProvenanceRole::ConstructorFieldSort
    );
    assert_eq!(anchors[1].range().start().column, 29);
    assert_eq!(anchors[1].range().end().column, 41);
    // The constructor descriptor denotes the field sorts, not the
    // declaration or the field names, which are the grammar descriptor's.
    let keys = |anchors: &[krs_syntax::ProvenanceAnchor]| {
        anchors
            .iter()
            .map(krs_syntax::ProvenanceAnchor::key)
            .collect::<Vec<_>>()
    };
    assert_eq!(
        keys(&constructor.sort_provenance().unwrap()),
        keys(&anchors[1..3])
    );
}

#[test]
fn production_rustdoc_is_normalized_and_has_exact_full_provenance() {
    let constructor = krs_syntax::ConstructorDeclaration::parse_source(
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

    let error = krs_syntax::ConstructorDeclaration::parse_source(
        "#[doc = concat!(\"not literal\")] struct DynamicDoc;",
    )
    .unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::UnsupportedConstructorDeclaration { .. }
    ));
}

#[test]
fn tuple_and_attributed_field_shapes_are_rejected() {
    let cases = [
        "struct Tuple(Term<Expr>);",
        "struct Attributed { #[cfg(any())] value: Term<Expr> }",
    ];

    for source in cases {
        let error = krs_syntax::ConstructorDeclaration::parse_source(source).unwrap_err();
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
        let error = krs_syntax::ConstructorDeclaration::parse_source(source).unwrap_err();
        assert!(matches!(error.kind(), SyntaxErrorKind::InvalidTermType));
    }
}

#[test]
fn typed_collection_fields_keep_their_element_types_and_anchor_each_one() {
    let constructor = krs_syntax::ConstructorDeclaration::parse_source(
        "struct Snapshot { storage: Term<Map<Int, Set<Int>>>, size: Term<Int>, log: Term<List<k::Term<dyn Entry>>> }",
    )
    .unwrap();
    let storage = constructor.fields()[0].term_sort();
    assert_eq!(storage.sort_token_text(), "Map");
    let spellings = |arguments: &[krs_syntax::SortArgument]| {
        krs_syntax::SortArgument::preorder(arguments)
            .into_iter()
            .map(|argument| {
                let last = argument.path.segments.last().unwrap();
                (last.ident.to_string(), argument.dynamic)
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        spellings(storage.arguments()),
        [
            ("Int".to_owned(), false),
            ("Set".to_owned(), false),
            ("Int".to_owned(), false),
        ]
    );
    assert!(constructor.fields()[1].term_sort().arguments().is_empty());
    assert_eq!(
        spellings(constructor.fields()[2].term_sort().arguments()),
        [("Entry".to_owned(), true)]
    );

    // The element types are numbered in preorder across the fields; the
    // compact and full anchor catalogs, which the grammar uses, omit them.
    let anchors = constructor.argument_provenance().unwrap();
    assert_eq!(
        anchors
            .iter()
            .map(|anchor| (anchor.role(), anchor.ordinal()))
            .collect::<Vec<_>>(),
        (0..4)
            .map(|ordinal| (ProvenanceRole::ConstructorFieldSortArgument, ordinal))
            .collect::<Vec<_>>()
    );
    assert!(
        constructor
            .full_provenance()
            .unwrap()
            .iter()
            .all(|anchor| anchor.role() != ProvenanceRole::ConstructorFieldSortArgument)
    );
}

#[test]
fn a_collection_element_type_is_a_sort_or_a_collection_type() {
    for source in [
        "struct Bad { value: Term<Map<Int, &Int>> }",
        "struct Bad { value: Term<List<[Int; 2]>> }",
        "struct Bad { value: Term<Set<<T as Tr>::Sort>> }",
    ] {
        let error = krs_syntax::ConstructorDeclaration::parse_source(source).unwrap_err();
        assert!(
            matches!(error.kind(), SyntaxErrorKind::InvalidCollectionArgument),
            "{source}: {error}"
        );
    }
}

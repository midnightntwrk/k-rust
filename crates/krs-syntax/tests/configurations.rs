//! Explicit single-`<k>` configuration parser tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{ConfigurationCellContent, ProvenanceRole, SyntaxErrorKind};

#[test]
fn named_root_attribute_preserves_literal_and_anchor() {
    let attribute =
        krs_syntax::ConfigurationAttribute::parse_source(r#"root = "machine""#).unwrap();
    assert_eq!(attribute.root().value(), "machine");
    let anchors = attribute.provenance().unwrap();
    assert_eq!(anchors.len(), 1);
    assert_eq!(anchors[0].role(), ProvenanceRole::ConfigurationRoot);
    assert_eq!(anchors[0].key().role(), ProvenanceRole::ConfigurationRoot);
    assert_eq!(anchors[0].range().start().column, 7);
    assert_eq!(anchors[0].range().end().column, 16);
}

#[test]
fn named_root_rejects_duplicate_unknown_and_non_string_arguments() {
    let cases = [
        (r#"root = "a", root = "b""#, "duplicate"),
        (r#"name = "a""#, "unknown"),
        ("root = machine", "invalid"),
        (r#"root = """#, "invalid"),
    ];
    for (source, expected) in cases {
        let error = krs_syntax::ConfigurationAttribute::parse_source(source).unwrap_err();
        match expected {
            "duplicate" => assert!(matches!(
                error.kind(),
                SyntaxErrorKind::DuplicateArgument { name: "root" }
            )),
            "unknown" => assert!(matches!(
                error.kind(),
                SyntaxErrorKind::UnknownArgument { name } if name == "name"
            )),
            "invalid" => assert!(matches!(
                error.kind(),
                SyntaxErrorKind::InvalidArgumentValue { name: "root", .. }
            )),
            _ => unreachable!(),
        }
    }
}

#[test]
fn one_fixed_computation_cell_preserves_type_paths_and_order() {
    let declaration = krs_syntax::ConfigurationDeclaration::parse_source(
        "#[derive(Clone)] pub struct Machine { \
         pub k: k::configuration::KCell<k::builtin::KSequence>, \
         }",
    )
    .unwrap();
    assert_eq!(declaration.item().attrs.len(), 1);
    assert_eq!(declaration.name(), "Machine");
    assert_eq!(declaration.cell().name(), "k");

    let candidates = declaration.reference_candidates();
    assert_eq!(candidates.len(), 2);
    assert_eq!(candidates[0].path_spelling(), "k::configuration::KCell");
    assert_eq!(
        candidates[0].key().role(),
        ProvenanceRole::ConfigurationCellWrapper
    );
    assert_eq!(candidates[1].path_spelling(), "k::builtin::KSequence");

    let roles = declaration
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert_eq!(
        roles,
        [
            ProvenanceRole::ConfigurationDeclaration,
            ProvenanceRole::ConfigurationField,
            ProvenanceRole::ConfigurationCellWrapper,
            ProvenanceRole::ConfigurationCellContent,
        ]
    );
}

#[test]
fn readable_plain_fields_infer_leaf_wrappers_and_keep_exact_provenance() {
    let declaration = krs_syntax::ConfigurationDeclaration::parse_source(
        r#"
        pub struct Machine {
            /// The computation cell.
            #[renamed::cell(color = "green")]
            pub k: renamed::builtin::KSequence,
            #[renamed::cell(color = "yellow")]
            pub env: renamed::builtin::Map<renamed::builtin::Id, Value>,
        }
        "#,
    )
    .unwrap();

    assert!(declaration.cells()[0].is_computation_cell());
    assert!(declaration.cells()[0].has_inferred_wrapper());
    assert!(matches!(
        declaration.cells()[1].cell_content(),
        ConfigurationCellContent::Leaf {
            computation: false,
            ..
        }
    ));
    assert!(declaration.cells()[1].has_inferred_wrapper());

    let candidates = declaration
        .reference_candidates()
        .into_iter()
        .map(|candidate| candidate.path_spelling())
        .collect::<Vec<_>>();
    assert_eq!(
        candidates,
        [
            "renamed::builtin::KSequence",
            "renamed::builtin::Map",
            "renamed::builtin::Id",
            "Value",
        ]
    );
    let roles = declaration
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert_eq!(
        roles,
        [
            ProvenanceRole::ConfigurationDeclaration,
            ProvenanceRole::ConfigurationField,
            ProvenanceRole::ConfigurationCellColor,
            ProvenanceRole::ConfigurationCellWrapper,
            ProvenanceRole::ConfigurationCellContent,
            ProvenanceRole::ConfigurationField,
            ProvenanceRole::ConfigurationCellColor,
            ProvenanceRole::ConfigurationCellWrapper,
            ProvenanceRole::ConfigurationCellContent,
            ProvenanceRole::ConfigurationCellContentArgument,
            ProvenanceRole::ConfigurationCellContentArgument,
        ]
    );
}

#[test]
fn readable_plain_fields_require_cell_helpers_on_every_field() {
    let source = "struct Machine { #[k::cell] k: KSequence, env: Map<Id, Value> }";
    let error = krs_syntax::ConfigurationDeclaration::parse_source(source).unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::UnsupportedConfigurationField { reason }
            if reason.contains("require `#[k::cell]`")
    ));
    assert_eq!(error.span().start().column, source.find("Map").unwrap());
}

#[test]
fn unsupported_struct_and_multiplicity_shapes_are_local_errors() {
    let cases = [
        "struct Unit;",
        "struct Tuple(KCell<KSequence>);",
        "struct Empty {}",
        "struct Generic<T> { k: KCell<KSequence> }",
        "struct Optional { k: OptionalCell<KSequence> }",
        "struct WrongContent { k: KCell<Map> }",
    ];
    for source in cases {
        let error = krs_syntax::ConfigurationDeclaration::parse_source(source).unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::UnsupportedConfigurationDeclaration { .. }
                | SyntaxErrorKind::UnsupportedConfigurationField { .. }
        ));
        if source.contains("OptionalCell") {
            assert!(error.span().start().column > source.find('{').unwrap());
        }
    }
}

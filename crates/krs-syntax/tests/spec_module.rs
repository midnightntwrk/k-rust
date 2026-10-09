//! `#[k::spec_module(name = "..", imports = [..])]` on an inline `mod` (KF-041).

use krs_syntax::{KrsSyntax, ProvenanceRole, SpecModuleAttribute, SpecModuleItem, SyntaxErrorKind};

fn reason(error: &krs_syntax::SyntaxError) -> String {
    match error.kind() {
        SyntaxErrorKind::InvalidSpecModule { reason } => reason.clone(),
        other => panic!("unexpected error kind {other:?}"),
    }
}

#[test]
fn the_attribute_takes_an_optional_name_and_import_paths() {
    let attribute =
        SpecModuleAttribute::parse_source(r#"name = "IMP-SUM-SPEC", imports = [lemmas, crate]"#)
            .unwrap();
    assert_eq!(attribute.name().unwrap().value(), "IMP-SUM-SPEC");
    let imports = attribute
        .imports()
        .iter()
        .map(krs_syntax::surface::path_text)
        .collect::<Vec<_>>();
    assert_eq!(imports, ["lemmas", "crate"]);
    let roles = attribute
        .provenance()
        .unwrap()
        .iter()
        .map(|anchor| (anchor.key().role(), anchor.key().ordinal()))
        .collect::<Vec<_>>();
    assert_eq!(
        roles,
        [
            (ProvenanceRole::SpecModuleName, 0),
            (ProvenanceRole::SpecModuleImport, 0),
            (ProvenanceRole::SpecModuleImport, 1),
        ]
    );

    let bare = SpecModuleAttribute::parse_source("").unwrap();
    assert!(bare.name().is_none());
    assert!(bare.imports().is_empty());
    SpecModuleAttribute::parse_source("imports = [::dependency, super::lemmas,]").unwrap();
}

#[test]
fn malformed_attributes_are_rejected() {
    for (source, expected) in [
        (r#"name = "imp-spec""#, "is not a K module name"),
        (r#"name = "IMP--SPEC""#, "is not a K module name"),
        (r#"name = "IMP-SPEC-""#, "is not a K module name"),
        (
            r#"name = "IMP-SYNTAX""#,
            "reserves for program-syntax modules",
        ),
        ("imports = [Vec<u8>]", "plain Rust module path"),
    ] {
        let error = SpecModuleAttribute::parse_source(source).unwrap_err();
        assert!(reason(&error).contains(expected), "{source}: {error}");
    }
    assert!(matches!(
        SpecModuleAttribute::parse_source(r#"name = "A", name = "B""#)
            .unwrap_err()
            .kind(),
        SyntaxErrorKind::DuplicateArgument { name: "name" }
    ));
    assert!(matches!(
        SpecModuleAttribute::parse_source("imports = [a], imports = [b]")
            .unwrap_err()
            .kind(),
        SyntaxErrorKind::DuplicateArgument { name: "imports" }
    ));
    assert!(matches!(
        SpecModuleAttribute::parse_source("labels = [a]")
            .unwrap_err()
            .kind(),
        SyntaxErrorKind::UnknownArgument { .. }
    ));
}

#[test]
fn the_attribute_applies_to_an_inline_module_only() {
    let module =
        SpecModuleItem::parse_source("mod sum_spec { use super::*; fn helper() {} }").unwrap();
    assert_eq!(module.ident(), "sum_spec");
    assert_eq!(module.items().len(), 2);
    assert_eq!(
        module.provenance()[0].key().role(),
        ProvenanceRole::SpecModuleDeclaration
    );
    let file_module = SpecModuleItem::parse_source("mod sum_spec;").unwrap_err();
    assert!(reason(&file_module).contains("needs the module body inline"));
    let function = SpecModuleItem::parse_source("fn sum_spec() {}").unwrap_err();
    assert!(reason(&function).contains("applies to an inline `mod name { .. }`"));
}

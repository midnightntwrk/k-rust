//! The `overload = Path` production key (KF-038).

use krs_syntax::{KrsSyntax, ProvenanceRole, SyntaxErrorKind};
use quote::ToTokens;

fn roles(anchors: &[krs_syntax::ProvenanceAnchor]) -> Vec<ProvenanceRole> {
    anchors
        .iter()
        .map(krs_syntax::ProvenanceAnchor::role)
        .collect()
}

#[test]
fn variant_and_constructor_take_a_target_path() {
    let variant = krs_syntax::VariantSyntaxAttribute::parse_source(
        r#""{base}.{field}", group = "lval", overload = ExpSyntax::Dot, format = "{base}.{field}""#,
    )
    .unwrap();
    assert_eq!(
        variant.overload().unwrap().to_token_stream().to_string(),
        "ExpSyntax :: Dot"
    );
    assert!(roles(&variant.provenance().unwrap()).contains(&ProvenanceRole::ConstructorOverload));

    let constructor = krs_syntax::ConstructorAttribute::parse_source(
        r#"sort = LVal, syntax = "{base}.{field}", overload = crate::exp::Dot"#,
    )
    .unwrap();
    assert_eq!(
        constructor
            .overload()
            .unwrap()
            .to_token_stream()
            .to_string(),
        "crate :: exp :: Dot"
    );
    assert!(
        roles(&constructor.full_provenance().unwrap())
            .contains(&ProvenanceRole::ConstructorOverload)
    );
    let plain = krs_syntax::VariantSyntaxAttribute::parse_source(r#""{base}.{field}""#).unwrap();
    assert!(plain.overload().is_none());
}

#[test]
fn overload_rejects_non_paths_duplicates_and_functions() {
    let cases = [
        (
            r#""x", overload = "ExpSyntax::Dot""#,
            SyntaxErrorKind::InvalidArgumentValue {
                name: "overload",
                expected: "a Rust path to the overloaded production",
            },
        ),
        (
            r#""x", overload = Choose::<Int>"#,
            SyntaxErrorKind::InvalidArgumentValue {
                name: "overload",
                expected: "a plain Rust path to the overloaded production, without generic arguments",
            },
        ),
        (
            r#""x", overload = A::B, overload = A::C"#,
            SyntaxErrorKind::DuplicateArgument { name: "overload" },
        ),
    ];
    for (source, expected) in cases {
        let error = krs_syntax::VariantSyntaxAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected, "{source}");
    }
    let function = krs_syntax::FunctionAttribute::parse_source(
        r#"total, overload = Exp::Dot, sort = Int, syntax = "f({value})""#,
    )
    .unwrap_err();
    assert_eq!(
        function.kind(),
        &SyntaxErrorKind::UnknownArgument {
            name: "overload".to_owned()
        }
    );
}

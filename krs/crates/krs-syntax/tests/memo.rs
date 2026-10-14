//! The bare `memo` flag of `#[k::function]` (KF-046).

use krs_syntax::{KrsSyntax, ProvenanceRole, SyntaxErrorKind};

#[test]
fn function_takes_a_bare_memo_flag() {
    let function = krs_syntax::FunctionAttribute::parse_source(
        r##"total, memo, sort = Int, syntax = "#dasmOpCode({op})""##,
    )
    .unwrap();
    assert_eq!(function.memo().unwrap(), "memo");
    assert!(
        function
            .provenance()
            .unwrap()
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::FunctionMemo)
    );
    let plain =
        krs_syntax::FunctionAttribute::parse_source(r#"partial, sort = Int, syntax = "f({x})""#)
            .unwrap();
    assert!(plain.memo().is_none());
}

#[test]
fn memo_rejects_duplicates_values_and_constructors() {
    let function_cases = [
        (
            r#"total, memo, memo, sort = Int, syntax = "f({x})""#,
            SyntaxErrorKind::DuplicateArgument { name: "memo" },
        ),
        (
            r#"total, memo = true, sort = Int, syntax = "f({x})""#,
            SyntaxErrorKind::InvalidArgumentValue {
                name: "memo",
                expected: "a bare flag in `#[k::function]`",
            },
        ),
    ];
    for (source, expected) in function_cases {
        let error = krs_syntax::FunctionAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected, "{source}");
    }
    let unknown = SyntaxErrorKind::UnknownArgument {
        name: "memo".to_owned(),
    };
    let constructor =
        krs_syntax::ConstructorAttribute::parse_source(r#"sort = Exp, syntax = "x", memo"#)
            .unwrap_err();
    assert_eq!(constructor.kind(), &unknown);
    let variant = krs_syntax::VariantSyntaxAttribute::parse_source(r#""x", memo"#).unwrap_err();
    assert_eq!(variant.kind(), &unknown);
}

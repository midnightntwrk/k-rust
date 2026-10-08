//! The `prefer` parser preference on production attributes (KF-002).

use krs_syntax::{KrsSyntax, ProvenanceRole, SyntaxErrorKind};

fn roles(anchors: &[krs_syntax::ProvenanceAnchor]) -> Vec<ProvenanceRole> {
    anchors
        .iter()
        .map(krs_syntax::ProvenanceAnchor::role)
        .collect()
}

#[test]
fn variant_accepts_bare_and_reference_spellings() {
    for source in [
        r#""if {condition} then {body}", prefer"#,
        r#""if {condition} then {body}", group = "stmt", prefer = true, format = "if {condition} then {body}""#,
    ] {
        let attribute = krs_syntax::VariantSyntaxAttribute::parse_source(source).unwrap();
        assert!(attribute.prefer(), "{source}");
        assert!(!attribute.avoid(), "{source}");
        assert!(
            roles(&attribute.provenance().unwrap()).contains(&ProvenanceRole::ConstructorPrefer),
            "{source}"
        );
    }
    let plain = krs_syntax::VariantSyntaxAttribute::parse_source(r#""if {condition} then {body}""#)
        .unwrap();
    assert!(!plain.prefer());
}

#[test]
fn constructor_takes_the_reference_spelling() {
    let attribute = krs_syntax::ConstructorAttribute::parse_source(
        r#"sort = Stmt, syntax = "if {condition} then {body}", prefer = true"#,
    )
    .unwrap();
    assert!(attribute.prefer());
    assert!(
        roles(&attribute.full_provenance().unwrap()).contains(&ProvenanceRole::ConstructorPrefer)
    );
    assert!(!roles(&attribute.provenance().unwrap()).contains(&ProvenanceRole::ConstructorPrefer));
}

#[test]
fn prefer_rejects_false_duplicates_and_avoid() {
    let both = SyntaxErrorKind::InvalidArgumentValue {
        name: "prefer",
        expected: "omitted: a production is either preferred or avoided, not both",
    };
    let variant_cases = [
        (
            r#""x", prefer = false"#,
            SyntaxErrorKind::InvalidArgumentValue {
                name: "prefer",
                expected: "the Rust Boolean literal `true`",
            },
        ),
        (
            r#""x", prefer = "yes""#,
            SyntaxErrorKind::InvalidArgumentValue {
                name: "prefer",
                expected: "a Rust Boolean literal",
            },
        ),
        (
            r#""x", prefer, prefer"#,
            SyntaxErrorKind::DuplicateArgument { name: "prefer" },
        ),
        (r#""x", avoid, prefer"#, both.clone()),
        (
            r#""x", prefer, avoid"#,
            SyntaxErrorKind::InvalidArgumentValue {
                name: "avoid",
                expected: "omitted: a production is either preferred or avoided, not both",
            },
        ),
    ];
    for (source, expected) in variant_cases {
        let error = krs_syntax::VariantSyntaxAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected, "{source}");
    }
    let constructor_cases = [
        (
            r"sort = Stmt, prefer = true, prefer = true",
            SyntaxErrorKind::DuplicateArgument { name: "prefer" },
        ),
        (r"sort = Stmt, avoid = true, prefer = true", both),
    ];
    for (source, expected) in constructor_cases {
        let error = krs_syntax::ConstructorAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected, "{source}");
    }
    let function = krs_syntax::FunctionAttribute::parse_source(
        r#"total, prefer, sort = Int, syntax = "f({value})""#,
    )
    .unwrap_err();
    assert_eq!(
        function.kind(),
        &SyntaxErrorKind::UnknownArgument {
            name: "prefer".to_owned()
        }
    );
}

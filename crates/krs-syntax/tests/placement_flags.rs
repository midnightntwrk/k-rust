//! `internal` and `program` placement flags on production attributes.

use krs_syntax::{KrsSyntax, PlacementFlag, ProvenanceRole, SyntaxErrorKind};

fn roles(anchors: &[krs_syntax::ProvenanceAnchor]) -> Vec<ProvenanceRole> {
    anchors
        .iter()
        .map(krs_syntax::ProvenanceAnchor::role)
        .collect()
}

#[test]
fn constructor_accepts_bare_and_reference_spellings() {
    for source in [
        r##"sort = Expr, syntax = "#lookup({name})", internal"##,
        r##"sort = Expr, syntax = "#lookup({name})", internal = true"##,
    ] {
        let attribute = krs_syntax::ConstructorAttribute::parse_source(source).unwrap();
        assert_eq!(attribute.placement(), Some(PlacementFlag::Internal));
        assert_eq!(attribute.placement_key().unwrap(), "internal");
        assert!(
            roles(&attribute.full_provenance().unwrap())
                .contains(&ProvenanceRole::ConstructorInternal)
        );
        assert!(
            !roles(&attribute.provenance().unwrap()).contains(&ProvenanceRole::ConstructorInternal)
        );
    }
    let program = krs_syntax::ConstructorAttribute::parse_source(
        r#"sort = Expr, syntax = "x", program = true"#,
    )
    .unwrap();
    assert_eq!(program.placement(), Some(PlacementFlag::Program));
}

#[test]
fn variant_syntax_and_function_flags_parse() {
    let variant =
        krs_syntax::VariantSyntaxAttribute::parse_source(r##""#inc({value})", internal"##).unwrap();
    assert_eq!(variant.placement(), Some(PlacementFlag::Internal));
    assert!(roles(&variant.provenance().unwrap()).contains(&ProvenanceRole::ConstructorInternal));
    let program = krs_syntax::VariantSyntaxAttribute::parse_source(
        r#""{lhs} + {rhs}", group = "add", program"#,
    )
    .unwrap();
    assert_eq!(program.placement(), Some(PlacementFlag::Program));

    let function = krs_syntax::FunctionAttribute::parse_source(
        r##"total, internal, sort = Int, syntax = "#addOne({value})""##,
    )
    .unwrap();
    assert_eq!(
        function.production().placement(),
        Some(PlacementFlag::Internal)
    );
    assert!(roles(&function.provenance().unwrap()).contains(&ProvenanceRole::ConstructorInternal));
}

#[test]
fn flags_reject_false_duplicates_and_the_other_flag() {
    let cases = [
        (
            r"sort = Expr, internal = false",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "internal",
                expected: "omitted or the Rust Boolean literal `true`",
            },
        ),
        (
            r"sort = Expr, internal, internal",
            SyntaxErrorKind::DuplicateArgument { name: "internal" },
        ),
        (
            r"sort = Expr, internal, program",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "program",
                expected: "omitted: a production is either `internal` or `program`, not both",
            },
        ),
    ];
    for (source, expected) in cases {
        let error = krs_syntax::ConstructorAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected, "{source}");
    }
    let error = krs_syntax::FunctionAttribute::parse_source(
        r#"total, program = true, sort = Int, syntax = "f({value})""#,
    )
    .unwrap_err();
    assert_eq!(
        error.kind(),
        &SyntaxErrorKind::InvalidArgumentValue {
            name: "program",
            expected: "a bare flag in `#[k::function]`",
        }
    );
}

#[test]
fn family_flag_makes_every_variant_internal() {
    let declaration = krs_syntax::EnumConstructorDeclaration::parse_source(
        r##"#[k::constructors(sort = Expr, result = KResult, internal)]
#[k::precedence((Inc, Dec))]
pub enum Aux {
    #[k::syntax("#inc({value})")]
    Inc { value: Expr },
    #[k::syntax("#dec({value})")]
    Dec { value: Expr },
}"##,
    )
    .unwrap();
    for variant in declaration.variants() {
        let syntax = variant.syntax().unwrap();
        assert_eq!(syntax.placement(), Some(PlacementFlag::Internal));
        assert!(
            roles(&declaration.variant_provenance(variant).unwrap())
                .contains(&ProvenanceRole::ConstructorInternal)
        );
    }

    for (variant_flag, expected) in [
        (
            "internal",
            SyntaxErrorKind::DuplicateArgument { name: "internal" },
        ),
        (
            "program",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "program",
                expected: "omitted in an `internal` family: a production is either `internal` or `program`, not both",
            },
        ),
    ] {
        let error = krs_syntax::EnumConstructorDeclaration::parse_source(&format!(
            r##"#[k::constructors(sort = Expr, result = KResult, internal)]
#[k::precedence((Inc))]
pub enum Aux {{
    #[k::syntax("#inc({{value}})", {variant_flag})]
    Inc {{ value: Expr }},
}}"##
        ))
        .unwrap_err();
        assert_eq!(error.kind(), &expected);
    }
}

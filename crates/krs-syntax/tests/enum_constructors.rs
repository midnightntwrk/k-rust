//! Closed-enum constructor-family parser and provenance contract tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{
    EnumConstructorDeclaration, ProvenanceRole, StrictnessKind, StructuredFormatFragment,
    SyntaxErrorKind, SyntaxTemplateItem,
};

#[test]
fn multiple_unit_and_record_variants_preserve_rust_and_metadata() {
    let declaration = krs_syntax::EnumConstructorDeclaration::parse_source(
        r#"#[doc = "kept enum"]
#[k::constructors(sort = model::Value)]
pub enum BooleanExpr {
    #[allow(dead_code)]
    #[k::syntax("true")]
    True,
    #[k::syntax("{rhs} && {lhs}", group = "boolean_and", avoid = true, format = "%1 %2 %3")]
    And { pub lhs: Term<dyn ExprAlias>, rhs: crate::Term<AliasValue> },
}"#,
    )
    .unwrap();

    assert_eq!(declaration.sort_name(), "BooleanExpr");
    let membership_sort = declaration.membership_sort();
    assert_eq!(
        quote::quote!(#membership_sort).to_string(),
        "model :: Value"
    );
    assert_eq!(declaration.item().attrs.len(), 1);
    assert_eq!(declaration.variants().len(), 2);
    assert_eq!(declaration.variants()[0].name(), "True");
    assert!(declaration.variants()[0].fields().is_empty());
    assert_eq!(declaration.variants()[0].variant().attrs.len(), 1);

    let record = &declaration.variants()[1];
    assert_eq!(record.name(), "And");
    assert_eq!(record.result_sort(), "BooleanExpr");
    assert_eq!(record.fields().len(), 2);
    assert_eq!(record.fields()[0].name(), "lhs");
    assert_eq!(
        record.fields()[0].term_sort().sort_token_text(),
        "ExprAlias"
    );
    assert!(record.fields()[0].term_sort().is_dynamic());
    assert_eq!(record.fields()[1].name(), "rhs");
    assert_eq!(
        record.fields()[1].term_sort().sort_token_text(),
        "AliasValue"
    );

    let syntax = record.syntax().unwrap();
    assert_eq!(
        syntax.syntax_template().items(),
        [
            SyntaxTemplateItem::Field("rhs".into()),
            SyntaxTemplateItem::Terminal("&&".into()),
            SyntaxTemplateItem::Field("lhs".into()),
        ]
    );
    assert_eq!(syntax.group().unwrap().value(), "boolean_and");
    assert!(syntax.avoid());
    assert_eq!(
        syntax.structured_format().unwrap().fragments(),
        [
            StructuredFormatFragment::Item(1),
            StructuredFormatFragment::Literal(" ".into()),
            StructuredFormatFragment::Item(2),
            StructuredFormatFragment::Literal(" ".into()),
            StructuredFormatFragment::Item(3),
        ]
    );

    // The retained expansion item and the parsed semantic view agree after
    // consuming only the two `k::syntax` helpers.
    assert_eq!(declaration.item().variants[0].attrs.len(), 1);
    assert!(declaration.item().variants[1].attrs.is_empty());
}

#[test]
fn aliases_remain_authored_paths_and_are_not_a_parser_resolution_concern() {
    let declaration = krs_syntax::EnumConstructorDeclaration::parse_source(
        r#"#[k::constructors(sort = OuterAlias)]
enum Family {
    #[k::syntax("wrap {value}")]
    Wrap { value: Term<InnerAlias> },
}"#,
    )
    .unwrap();
    let membership_sort = declaration.membership_sort();
    assert_eq!(quote::quote!(#membership_sort).to_string(), "OuterAlias");
    assert_eq!(
        declaration.variants()[0].fields()[0]
            .term_sort()
            .sort_token_text(),
        "InnerAlias"
    );

    let split_attribute =
        krs_syntax::ConstructorsAttribute::parse_source("sort = renamed::Outer").unwrap();
    let split_item: syn::ItemEnum =
        syn::parse_str(r#"#[doc = "ordinary"] enum ViaMacro { #[k::syntax("unit")] Unit }"#)
            .unwrap();
    let split = EnumConstructorDeclaration::from_parts(&split_attribute, split_item).unwrap();
    assert_eq!(split.item().attrs.len(), 1);
    assert_eq!(split.variants()[0].name(), "Unit");
}

#[test]
fn semantic_descriptors_have_separate_exact_provenance_catalogs() {
    let declaration = krs_syntax::EnumConstructorDeclaration::parse_source(
        "#[k::constructors(sort = outer::Value)]\n\
         pub enum Boolean {\n\
             /// Equality production.\n\
             #[k::syntax(\"{rhs} == {lhs}\")]\n\
             Equal { lhs: Term<left::Expr>, rhs: Term<right::Expr> },\n\
         }",
    )
    .unwrap();

    let sort = declaration.sort_provenance().unwrap();
    assert_eq!(sort.len(), 1);
    assert_eq!(sort[0].role(), ProvenanceRole::SortDeclaration);
    assert_eq!(
        (sort[0].range().start().line, sort[0].range().start().column),
        (2, 9)
    );

    let membership = declaration.membership_provenance().unwrap();
    assert_eq!(
        membership
            .iter()
            .map(krs_syntax::ProvenanceAnchor::role)
            .collect::<Vec<_>>(),
        [
            ProvenanceRole::SubsortDeclaration,
            ProvenanceRole::SubsortSubSort,
            ProvenanceRole::SubsortSuperSort,
        ]
    );
    assert_eq!(membership[0].range().start(), membership[1].range().start());
    assert_eq!(
        (
            membership[2].range().start().line,
            membership[2].range().start().column
        ),
        (1, 25)
    );

    let production = declaration.variants()[0].provenance().unwrap();
    let roles = production
        .iter()
        .map(|anchor| (anchor.role(), anchor.ordinal()))
        .collect::<Vec<_>>();
    assert!(roles.contains(&(ProvenanceRole::ConstructorSort, 0)));
    assert!(roles.contains(&(ProvenanceRole::ConstructorDeclaration, 0)));
    assert!(roles.contains(&(ProvenanceRole::ConstructorFieldSort, 0)));
    assert!(roles.contains(&(ProvenanceRole::ConstructorFieldSort, 1)));
    assert!(roles.contains(&(ProvenanceRole::ConstructorFieldDeclaration, 0)));
    assert!(roles.contains(&(ProvenanceRole::ConstructorFieldDeclaration, 1)));
    assert!(roles.contains(&(ProvenanceRole::ConstructorDocumentation, 0)));
    assert_eq!(
        declaration.variants()[0].documentation()[0].text(),
        "Equality production."
    );
    assert_eq!(
        production
            .iter()
            .find(|anchor| anchor.role() == ProvenanceRole::ConstructorDeclaration)
            .unwrap()
            .range()
            .start()
            .line,
        5
    );

    let template_fields = production
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::ConstructorSyntaxFieldReference)
        .collect::<Vec<_>>();
    assert_eq!(template_fields.len(), 2);
    // Template order is rhs/lhs while field declaration provenance remains
    // lhs/rhs, proving the two semantic orders are not conflated.
    assert_eq!(template_fields[0].ordinal(), 0);
    assert_eq!(template_fields[1].ordinal(), 1);
}

#[test]
fn unsupported_enum_shapes_and_helpers_are_rejected_locally() {
    let cases = [
        "enum Missing { Unit }",
        "#[k::constructors(sort = Value)] #[k::other] enum ExtraOuter { Unit }",
        "#[k::constructors(sort = Value)] #[k::constructors(sort = Other)] enum Duplicate { Unit }",
        "#[k::constructors(sort = Value)] enum Generic<T> { Unit }",
        "#[k::constructors(sort = Value)] enum Where where Value: Sort { Unit }",
        "#[k::constructors(sort = Value)] enum Tuple { Value(Term<Expr>) }",
        "#[k::constructors(sort = Value)] enum Discriminant { Value = 1 }",
        "#[k::constructors(sort = Value)] enum VariantHelper { #[k::strict(sequence = [value], result = Value)] Value { value: Term<Value> } }",
        "#[k::constructors(sort = Value)] enum DuplicateSyntax { #[k::syntax(\"x\")] #[k::syntax(\"y\")] Value }",
        "#[k::constructors(sort = Value)] enum FieldAttribute { Value { #[cfg(any())] value: Term<Value> } }",
    ];
    for source in cases {
        let error = krs_syntax::EnumConstructorDeclaration::parse_source(source).unwrap_err();
        assert!(
            matches!(
                error.kind(),
                SyntaxErrorKind::UnsupportedEnumConstructorDeclaration { .. }
            ),
            "unexpected error for {source}: {error}"
        );
    }
}

#[test]
fn invalid_term_shapes_and_templates_reuse_constructor_contract() {
    let invalid_term = krs_syntax::EnumConstructorDeclaration::parse_source(
        "#[k::constructors(sort = Value)] enum Raw { Value { value: Int } }",
    )
    .unwrap_err();
    assert!(matches!(
        invalid_term.kind(),
        SyntaxErrorKind::InvalidTermType
    ));

    for source in [
        "#[k::constructors(sort = Value)] enum Missing { #[k::syntax(\"prefix\")] Value { value: Term<Value> } }",
        "#[k::constructors(sort = Value)] enum Repeated { #[k::syntax(\"{value} {value}\")] Value { value: Term<Value> } }",
        "#[k::constructors(sort = Value)] enum Unknown { #[k::syntax(\"{other}\")] Value { value: Term<Value> } }",
    ] {
        let error = krs_syntax::EnumConstructorDeclaration::parse_source(source).unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::InvalidTemplateFieldOccurrence { .. }
                | SyntaxErrorKind::UnknownTemplateField { .. }
        ));
    }
}

#[test]
#[allow(clippy::too_many_lines)] // One end-to-end readable production metadata specimen.
fn readable_open_family_parses_exhaustive_chain_fields_and_formats() {
    let declaration = krs_syntax::EnumConstructorDeclaration::parse_source(
        r#"#[dialect::constructors(sort = ExprAlias, result = framework::KResult)]
#[dialect::precedence(
    (Neg) > left remainder (Mul, Block, ValueNode, EmptyBlock)
)]
enum Op {
    #[dialect::syntax("-{value}")]
    #[dialect::strict]
    Neg { value: ExprAlias },
    #[dialect::syntax("{lhs} * {rhs}")]
    #[dialect::seqstrict(using = eval_context, lhs, rhs)]
    Mul { lhs: ExprAlias, rhs: builtin::Int },
    #[dialect::syntax("{{{body}}}")]
    #[dialect::format("{{%i%n{body}%d%n}}")]
    Block { body: StmtAlias },
    #[dialect::syntax("value {value}")]
    ValueNode { value: ValueAlias },
    #[dialect::syntax("{{}}")]
    #[dialect::alias]
    EmptyBlock(),
}"#,
    )
    .unwrap();

    assert!(declaration.is_open_family());
    assert_eq!(declaration.precedence_groups().count(), 2);
    assert_eq!(declaration.precedence_chain_groups().unwrap().len(), 2);
    assert_eq!(
        declaration
            .precedence_descriptor()
            .unwrap()
            .unwrap()
            .groups
            .len(),
        2
    );
    assert_eq!(
        declaration
            .precedence_groups()
            .nth(1)
            .unwrap()
            .associativity(),
        Some(krs_syntax::GroupAssociativity::Left)
    );
    assert_eq!(
        declaration
            .precedence_groups()
            .next()
            .unwrap()
            .associativity(),
        None
    );
    assert_eq!(
        declaration
            .precedence_groups()
            .nth(1)
            .unwrap()
            .name()
            .unwrap(),
        "remainder"
    );
    assert_eq!(
        declaration
            .precedence_groups()
            .next()
            .unwrap()
            .emitted_name(declaration.sort_name(), 0),
        "op_tier0"
    );
    assert_eq!(
        declaration
            .precedence_groups()
            .nth(1)
            .unwrap()
            .emitted_name(declaration.sort_name(), 1),
        "remainder"
    );
    let constructor_sort = declaration.variants()[0].constructor_sort();
    assert_eq!(quote::quote!(#constructor_sort).to_string(), "ExprAlias");
    assert_eq!(
        declaration.variants()[1].fields()[1]
            .term_sort()
            .sort_token_text(),
        "builtin :: Int"
    );
    assert_eq!(
        declaration.variants()[0].strictness().unwrap().fields(),
        ["value"]
    );
    assert!(
        declaration.variants()[0]
            .strictness()
            .unwrap()
            .has_readable_result()
    );
    assert_eq!(
        declaration.variants()[1]
            .strictness()
            .unwrap()
            .using()
            .unwrap(),
        "eval_context"
    );
    assert_eq!(
        declaration.variants()[3].fields()[0]
            .term_sort()
            .sort_token_text(),
        "ValueAlias"
    );
    assert_eq!(declaration.variants()[4].variant().fields.len(), 0);
    assert!(declaration.variants()[4].is_alias());
    assert!(
        declaration.variants()[4]
            .provenance()
            .unwrap()
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::AliasProduction)
    );

    assert_eq!(
        declaration.variants()[1]
            .syntax()
            .unwrap()
            .structured_format()
            .unwrap()
            .fragments(),
        [
            StructuredFormatFragment::Item(1),
            StructuredFormatFragment::Literal(" * ".into()),
            StructuredFormatFragment::Item(3),
        ]
    );
    assert_eq!(
        declaration.variants()[2]
            .syntax()
            .unwrap()
            .structured_format()
            .unwrap()
            .fragments(),
        [
            StructuredFormatFragment::Literal("{".into()),
            StructuredFormatFragment::Indent,
            StructuredFormatFragment::Newline,
            StructuredFormatFragment::Item(2),
            StructuredFormatFragment::Dedent,
            StructuredFormatFragment::Newline,
            StructuredFormatFragment::Literal("}".into()),
        ]
    );
    let block_roles = declaration
        .variant_provenance(&declaration.variants()[2])
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert!(block_roles.contains(&ProvenanceRole::ConstructorGroup));
    assert!(block_roles.contains(&ProvenanceRole::ConstructorFormat));
    assert!(declaration.precedence_provenance().unwrap().is_some());
    assert!(declaration.associativity_provenance().unwrap().is_some());
}

#[test]
fn enum_precedence_distinguishes_bare_and_explicit_non_associative_groups() {
    let declaration = krs_syntax::EnumConstructorDeclaration::parse_source(
        r#"#[k::constructors(sort = Expr, result = KResult)]
#[k::precedence((Not) > non_assoc equality (Eq) > (Atom))]
enum Family {
    #[k::syntax("!{value}")] Not { value: Expr },
    #[k::syntax("{lhs} == {rhs}")] Eq { lhs: Expr, rhs: Expr },
    #[k::syntax("atom")] Atom,
}"#,
    )
    .unwrap();

    assert_eq!(
        declaration
            .precedence_groups()
            .next()
            .unwrap()
            .associativity(),
        None
    );
    assert_eq!(
        declaration
            .precedence_groups()
            .nth(1)
            .unwrap()
            .associativity(),
        Some(krs_syntax::GroupAssociativity::NonAssociative)
    );
    assert_eq!(
        declaration
            .precedence_groups()
            .nth(1)
            .unwrap()
            .name()
            .unwrap(),
        "equality"
    );
    assert_eq!(
        declaration
            .precedence_groups()
            .nth(2)
            .unwrap()
            .associativity(),
        None
    );
}

#[test]
fn readable_family_rejects_malformed_fields_and_variant_precedence_helpers() {
    for (source, expected_kind) in [
        (
            "#[k::constructors(sort = Expr, result = KResult)] enum Missing { #[k::syntax(\"x\")] X }",
            SyntaxErrorKind::InvalidEnumPrecedence {
                reason: "a readable constructor family requires one exhaustive enum-level `#[k::precedence((Variant, ...) > ...)]` chain".into(),
            },
        ),
        (
            "#[k::constructors(sort = Expr, result = KResult)] enum Bad { #[k::precedence(middle)] #[k::syntax(\"x\")] X }",
            SyntaxErrorKind::UnsupportedEnumConstructorDeclaration {
                reason: "readable enum variants support only `syntax`, `format`, `strict`, `seqstrict`, and `alias` KRS helpers; precedence belongs on the enum",
            },
        ),
        (
            "#[k::constructors(sort = Expr, result = KResult)] #[k::precedence((X))] enum Bad { #[k::syntax(\"{x}\")] X { x: Vec<Expr> } }",
            SyntaxErrorKind::InvalidTermType,
        ),
        (
            "#[k::constructors(sort = Expr, result = KResult)] #[k::precedence((X))] enum Bad { #[k::syntax(\"{x}\")] #[k::strict(y)] X { x: Expr } }",
            SyntaxErrorKind::InvalidStrictness {
                reason: "strictness names a field absent from the production",
            },
        ),
        (
            "#[k::constructors(sort = Expr, result = KResult)] #[k::precedence((X))] enum Bad { #[k::syntax(\"x\")] X(u8) }",
            SyntaxErrorKind::UnsupportedEnumConstructorDeclaration {
                reason: "tuple enum constructor variants are unsupported; readable families permit only zero-field tuple variants",
            },
        ),
    ] {
        let error = krs_syntax::EnumConstructorDeclaration::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn reference_family_requires_and_preserves_fully_materialized_metadata() {
    let declaration = krs_syntax::EnumConstructorDeclaration::parse_source(
        r#"#[k::constructors(sort = Expr, reference)]
enum Op {
    #[k::syntax(
        "{lhs} + {rhs}",
        group = "op_tier2",
        avoid = true,
        format = "{lhs} + {rhs}",
    )]
    #[k::seqstrict(sequence = [rhs, lhs], result = KResult)]
    Add {
        lhs: k::Term<dyn ExprSort>,
        rhs: k::Term<k::Int>,
    },
}"#,
    )
    .unwrap();

    assert!(declaration.is_open_family());
    assert!(declaration.is_reference_family());
    assert!(declaration.precedence_groups().next().is_none());
    assert!(declaration.precedence_provenance().unwrap().is_none());
    assert!(declaration.associativity_provenance().unwrap().is_none());

    let variant = &declaration.variants()[0];
    let constructor_sort = variant.constructor_sort();
    assert_eq!(quote::quote!(#constructor_sort).to_string(), "Expr");
    assert_eq!(variant.fields().len(), 2);
    assert_eq!(
        variant.fields()[0].term_sort().sort_token_text(),
        "ExprSort"
    );
    assert!(variant.fields()[0].term_sort().is_dynamic());
    assert_eq!(
        variant.fields()[1].term_sort().sort_token_text(),
        "k :: Int"
    );
    assert!(!variant.fields()[1].term_sort().is_dynamic());

    let syntax = variant.syntax().unwrap();
    assert_eq!(syntax.group().unwrap().value(), "op_tier2");
    assert!(syntax.avoid());
    assert_eq!(syntax.format().unwrap().value(), "{lhs} + {rhs}");
    assert_eq!(
        syntax.structured_format().unwrap().fragments(),
        [
            StructuredFormatFragment::Item(1),
            StructuredFormatFragment::Literal(" + ".into()),
            StructuredFormatFragment::Item(3),
        ]
    );

    let strictness = variant.strictness().unwrap();
    assert_eq!(strictness.kind(), StrictnessKind::SeqStrict);
    assert_eq!(strictness.fields(), ["rhs", "lhs"]);
    let result_sort = strictness.result_sort();
    assert_eq!(quote::quote!(#result_sort).to_string(), "KResult");
    assert!(strictness.has_readable_result());
}

#[test]
fn reference_family_rejects_partially_materialized_layer_one_forms() {
    let cases = [
        (
            r#"#[k::constructors(sort = Expr, reference)]
enum MissingGroup {
    #[k::syntax("x", format = "x")]
    X,
}"#,
            "requires an explicit `group`",
        ),
        (
            r#"#[k::constructors(sort = Expr, reference)]
enum MissingFormat {
    #[k::syntax("x", group = "atom")]
    X,
}"#,
            "requires an explicit `format`",
        ),
        (
            r#"#[k::constructors(sort = Expr, reference)]
enum AliasField {
    #[k::syntax("{value}", group = "atom", format = "{value}")]
    X { value: Expr },
}"#,
            "expected `Term<SortPath>` or `Term<dyn SortPath>`",
        ),
        (
            r#"#[k::constructors(sort = Expr, reference)]
#[k::precedence((X))]
enum EnumPrecedence {
    #[k::syntax("x", group = "atom", format = "x")]
    X,
}"#,
            "carries precedence in freestanding family-owned grammar blocks",
        ),
        (
            r#"#[k::constructors(sort = Expr, reference)]
enum ShorthandStrictness {
    #[k::syntax("{value}", group = "atom", format = "{value}")]
    #[k::strict]
    X { value: Term<dyn ExprSort> },
}"#,
            "missing required argument `sequence",
        ),
        (
            r#"#[k::constructors(sort = Expr, reference)]
enum SiblingFormat {
    #[k::syntax("x", group = "atom")]
    #[k::format("x")]
    X,
}"#,
            "materializes format inside `syntax`",
        ),
    ];

    for (source, expected) in cases {
        let error = krs_syntax::EnumConstructorDeclaration::parse_source(source).unwrap_err();
        assert!(
            error.to_string().contains(expected),
            "`{source}` reported `{error}` instead of containing `{expected}`"
        );
    }
}

#[test]
fn enum_precedence_chain_is_exhaustive_named_and_fail_fast() {
    let cases = [
        (
            "#[k::constructors(sort = Expr, result = KResult)] #[k::precedence((A))] enum Family { #[k::syntax(\"a\")] A, #[k::syntax(\"b\")] B }",
            "variant `B` is missing",
        ),
        (
            "#[k::constructors(sort = Expr, result = KResult)] #[k::precedence((A, C))] enum Family { #[k::syntax(\"a\")] A, #[k::syntax(\"b\")] B }",
            "unknown enum variant `C`",
        ),
        (
            "#[k::constructors(sort = Expr, result = KResult)] #[k::precedence((A, A))] enum Family { #[k::syntax(\"a\")] A }",
            "variant `A` appears more than once",
        ),
        (
            "#[k::constructors(sort = Expr, result = KResult)] #[k::precedence(left right (A))] enum Family { #[k::syntax(\"a\")] A }",
            "reserved associativity keywords",
        ),
        (
            "#[k::constructors(sort = Expr, result = KResult)] #[k::precedence(non_assoc left (A))] enum Family { #[k::syntax(\"a\")] A }",
            "reserved associativity keywords",
        ),
        (
            "#[k::constructors(sort = Expr, result = KResult)] #[k::precedence((A) >)] enum Family { #[k::syntax(\"a\")] A }",
            "followed by a precedence group",
        ),
        (
            "#[k::constructors(sort = Expr, result = KResult)] #[k::precedence(named (A) > named (B))] enum Family { #[k::syntax(\"a\")] A, #[k::syntax(\"b\")] B }",
            "identity `named` is repeated",
        ),
        (
            "#[k::constructors(sort = Expr, result = KResult)] #[k::precedence(family_tier1 (A) > (B))] enum Family { #[k::syntax(\"a\")] A, #[k::syntax(\"b\")] B }",
            "identity `family_tier1` is repeated",
        ),
    ];
    for (source, expected) in cases {
        let error = krs_syntax::EnumConstructorDeclaration::parse_source(source).unwrap_err();
        assert!(
            error.to_string().contains(expected),
            "`{source}` reported `{error}` instead of containing `{expected}`"
        );
    }

    let suggestion = krs_syntax::EnumConstructorDeclaration::parse_source(
        "#[k::constructors(sort = Expr, result = KResult)] #[k::precedence((Mull))] enum Family { #[k::syntax(\"mul\")] Mul }",
    )
    .unwrap_err();
    assert!(suggestion.to_string().contains("did you mean `Mul`"));
}

#[test]
fn materialized_variant_group_may_match_the_exhaustive_chain() {
    let declaration = krs_syntax::EnumConstructorDeclaration::parse_source(
        r#"#[k::constructors(sort = Expr, result = KResult)]
#[k::precedence((Atom) > left infix (Add))]
enum Family {
    #[k::syntax("atom", group = "family_tier0")]
    Atom,
    #[k::syntax("{lhs} + {rhs}", group = "infix")]
    Add { lhs: Expr, rhs: Expr },
}"#,
    )
    .unwrap();

    for variant in declaration.variants() {
        let groups = declaration
            .variant_provenance(variant)
            .unwrap()
            .into_iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::ConstructorGroup)
            .collect::<Vec<_>>();
        assert_eq!(
            groups.len(),
            1,
            "{} has duplicate group provenance",
            variant.name()
        );
    }
}

#[test]
fn materialized_variant_group_must_match_the_exhaustive_chain() {
    let error = krs_syntax::EnumConstructorDeclaration::parse_source(
        r#"#[k::constructors(sort = Expr, result = KResult)]
#[k::precedence((Atom))]
enum Family {
    #[k::syntax("atom", group = "wrong")]
    Atom,
}"#,
    )
    .unwrap_err();

    assert!(
        error.to_string().contains(
            "variant `Atom` materializes group `wrong` but the exhaustive chain assigns `family_tier0`"
        ),
        "unexpected error: {error}"
    );
}

#[test]
fn a_single_precedence_group_has_no_chain_descriptor() {
    let declaration = krs_syntax::EnumConstructorDeclaration::parse_source(
        r#"#[k::constructors(sort = Expr, result = KResult)]
#[k::precedence((X))]
enum Single {
    #[k::syntax("x")]
    X,
}"#,
    )
    .unwrap();
    assert_eq!(declaration.precedence_groups().count(), 1);
    assert!(declaration.precedence_chain_groups().is_none());
    assert!(declaration.precedence_descriptor().unwrap().is_none());
    assert!(declaration.precedence_provenance().unwrap().is_none());
}

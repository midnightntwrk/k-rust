//! M3A object-grammar, metadata, and provenance contract tests.

use krs_syntax::{
    GroupAssociativity, ProvenanceRole, StrictnessKind, StructuredFormatFragment, SyntaxErrorKind,
    SyntaxTemplateItem, TermSymbolKind, parse_associativity_declaration_source,
    parse_bracket_attribute_source, parse_constructor_attribute_source,
    parse_constructor_declaration_source, parse_precedence_declaration_source,
    parse_rule_item_source, parse_seqstrict_attribute_source, parse_strict_attribute_source,
    parse_subsort_declaration_source, parse_term_expression_source, parse_token_attribute_source,
    parse_token_declaration_source,
};

#[test]
fn nominal_expr_production_is_checked_and_keyed() {
    let attribute = parse_constructor_attribute_source(
        r#"sort = Expr, syntax = "{lhs} + {rhs}", group = "additive", avoid = true, format = "%1%2%3""#,
    )
    .unwrap();
    let declaration = parse_constructor_declaration_source(
        "pub struct Add { pub lhs: Term<dyn Expr>, pub rhs: Term<dyn Expr> }",
    )
    .unwrap();
    attribute.validate_declaration(&declaration).unwrap();

    let template = attribute.syntax_template().unwrap();
    assert_eq!(
        template.items(),
        [
            SyntaxTemplateItem::Field("lhs".into()),
            SyntaxTemplateItem::Terminal("+".into()),
            SyntaxTemplateItem::Field("rhs".into()),
        ]
    );
    assert_eq!(attribute.group.as_ref().unwrap().value(), "additive");
    assert!(attribute.avoid);
    assert_eq!(
        attribute.structured_format().unwrap().fragments(),
        [
            StructuredFormatFragment::Item(1),
            StructuredFormatFragment::Item(2),
            StructuredFormatFragment::Item(3),
        ]
    );

    let roles = attribute
        .m3a_provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert!(roles.contains(&ProvenanceRole::ConstructorSyntaxItem));
    assert_eq!(
        roles
            .iter()
            .filter(|role| **role == ProvenanceRole::ConstructorSyntaxFieldReference)
            .count(),
        2
    );
    assert!(roles.contains(&ProvenanceRole::ConstructorGroup));
    assert!(roles.contains(&ProvenanceRole::ConstructorAvoid));
    assert!(roles.contains(&ProvenanceRole::ConstructorFormatFragment));

    let declaration_roles = declaration
        .m3a_provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert_eq!(
        declaration_roles
            .iter()
            .filter(|role| **role == ProvenanceRole::ConstructorFieldDeclaration)
            .count(),
        2
    );
}

#[test]
fn templates_escape_braces_and_reject_field_mismatches() {
    let declaration =
        parse_constructor_declaration_source("struct Pair { left: Term<Expr>, right: Term<Expr> }")
            .unwrap();
    let escaped =
        parse_constructor_attribute_source(r#"sort = Expr, syntax = "{{{left}}}:{right}""#)
            .unwrap();
    escaped.validate_declaration(&declaration).unwrap();
    assert_eq!(
        escaped.syntax_template().unwrap().items(),
        [
            SyntaxTemplateItem::Terminal("{".into()),
            SyntaxTemplateItem::Field("left".into()),
            SyntaxTemplateItem::Terminal("}".into()),
            SyntaxTemplateItem::Terminal(":".into()),
            SyntaxTemplateItem::Field("right".into()),
        ]
    );

    for source in [
        r#"sort = Expr, syntax = "{left}""#,
        r#"sort = Expr, syntax = "{left}{left}{right}""#,
        r#"sort = Expr, syntax = "{left}{missing}""#,
    ] {
        let attribute = parse_constructor_attribute_source(source).unwrap();
        let error = attribute.validate_declaration(&declaration).unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::InvalidTemplateFieldOccurrence { .. }
                | SyntaxErrorKind::UnknownTemplateField { .. }
        ));
    }

    for source in [
        r#"sort = Expr, syntax = """#,
        r#"sort = Expr, syntax = "{""#,
        r#"sort = Expr, syntax = "}""#,
        r#"sort = Expr, syntax = "{}""#,
        r#"sort = Expr, syntax = "{left{right}}""#,
    ] {
        assert!(matches!(
            parse_constructor_attribute_source(source)
                .unwrap_err()
                .kind(),
            SyntaxErrorKind::InvalidSyntaxTemplate { .. }
        ));
    }

    let unmatched_open =
        parse_constructor_attribute_source(r#"sort = Expr, syntax = "{""#).unwrap_err();
    assert!(unmatched_open.to_string().contains("did you mean `{{`"));
}

#[test]
fn syntax_layout_is_nonsemantic_and_terminals_match_k_token_boundaries() {
    let attribute = parse_constructor_attribute_source(
        r#"sort = Expr, syntax = "if ({condition}) {body} else {otherwise}""#,
    )
    .unwrap();
    assert_eq!(
        attribute.syntax_template().unwrap().items(),
        [
            SyntaxTemplateItem::Terminal("if".into()),
            SyntaxTemplateItem::Terminal("(".into()),
            SyntaxTemplateItem::Field("condition".into()),
            SyntaxTemplateItem::Terminal(")".into()),
            SyntaxTemplateItem::Field("body".into()),
            SyntaxTemplateItem::Terminal("else".into()),
            SyntaxTemplateItem::Field("otherwise".into()),
        ]
    );
    let compact = parse_constructor_attribute_source(
        r#"sort = Expr, syntax = "if({condition}){body}else{otherwise}""#,
    )
    .unwrap();
    assert_eq!(
        attribute.syntax_template().unwrap().items(),
        compact.syntax_template().unwrap().items()
    );

    let operators = parse_constructor_attribute_source(
        r#"sort = Expr, syntax = "{lhs} >= {rhs};{lhs2} != {rhs2}""#,
    )
    .unwrap();
    assert_eq!(
        operators.syntax_template().unwrap().items(),
        [
            SyntaxTemplateItem::Field("lhs".into()),
            SyntaxTemplateItem::Terminal(">=".into()),
            SyntaxTemplateItem::Field("rhs".into()),
            SyntaxTemplateItem::Terminal(";".into()),
            SyntaxTemplateItem::Field("lhs2".into()),
            SyntaxTemplateItem::Terminal("!=".into()),
            SyntaxTemplateItem::Field("rhs2".into()),
        ]
    );
    assert_eq!(
        operators
            .m3a_provenance()
            .unwrap()
            .iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::ConstructorSyntaxItem)
            .count(),
        7
    );
}

#[test]
fn group_avoid_and_structured_format_values_are_closed() {
    for source in [
        r#"sort = Expr, group = """#,
        r#"sort = Expr, group = "a::b""#,
        "sort = Expr, avoid = choice",
        "sort = Expr, avoid = false",
        r#"sort = Expr, format = "%""#,
        r#"sort = Expr, format = "%0""#,
        r#"sort = Expr, format = "%70000""#,
    ] {
        assert!(
            parse_constructor_attribute_source(source).is_err(),
            "{source}"
        );
    }

    let declaration = parse_constructor_declaration_source("struct Unit;").unwrap();
    let out_of_range =
        parse_constructor_attribute_source(r#"sort = Expr, syntax = "unit", format = "%2""#)
            .unwrap();
    assert!(matches!(
        out_of_range
            .validate_declaration(&declaration)
            .unwrap_err()
            .kind(),
        SyntaxErrorKind::InvalidFormat { .. }
    ));
}

#[test]
fn authored_id_token_is_distinct_from_builtin_int_and_bool() {
    let attribute =
        parse_token_attribute_source(r#"regex = r"[a-zA-Z][a-zA-Z0-9_]*", prec = 2"#).unwrap();
    assert_eq!(attribute.regex().value(), "[a-zA-Z][a-zA-Z0-9_]*");
    assert_eq!(attribute.lexical_precedence(), Some(2));
    let declaration = parse_token_declaration_source("pub struct Id(String);").unwrap();
    assert_eq!(declaration.name(), "Id");
    assert_eq!(
        declaration.provenance().unwrap()[0].role(),
        ProvenanceRole::TokenDeclaration
    );

    for source in [
        r#"regex = """#,
        r#"regex = "[a-z""#,
        r#"regex = "(abc""#,
        r#"regex = "abc\\""#,
        r#"regex = "abc", prec = -1"#,
        r#"regex = "abc", prec = 2u8"#,
        r#"regex = "abc", regex = "def""#,
    ] {
        assert!(parse_token_attribute_source(source).is_err(), "{source}");
    }
    for source in [
        "struct Id;",
        "struct Id(String, String);",
        "struct Id { text: String }",
        "struct Id(u64);",
        "struct Id<T>(T);",
        "struct Id(#[cfg(any())] String);",
    ] {
        assert!(matches!(
            parse_token_declaration_source(source).unwrap_err().kind(),
            SyntaxErrorKind::UnsupportedTokenDeclaration { .. }
        ));
    }
}

#[test]
fn bracket_is_syntax_only_and_has_one_same_sort_value() {
    let bracket = parse_bracket_attribute_source(r#""({value})""#).unwrap();
    assert_eq!(
        bracket.template().items(),
        [
            SyntaxTemplateItem::Terminal("(".into()),
            SyntaxTemplateItem::Field("value".into()),
            SyntaxTemplateItem::Terminal(")".into()),
        ]
    );
    let anchors = bracket.provenance().unwrap();
    assert_eq!(anchors[0].role(), ProvenanceRole::BracketDeclaration);
    assert_eq!(
        anchors
            .iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::BracketValueReference)
            .count(),
        1
    );
    for source in [
        r#""({other})""#,
        r#""({value}{value})""#,
        r#""{value}""#,
        r#""(""#,
        r#""({value})", extra"#,
    ] {
        assert!(parse_bracket_attribute_source(source).is_err(), "{source}");
    }

    let delimiters = parse_bracket_attribute_source(r#""(", ")""#).unwrap();
    assert_eq!(delimiters.template().items(), bracket.template().items());
    assert_eq!(
        delimiters
            .provenance()
            .unwrap()
            .iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::BracketValueReference)
            .count(),
        1
    );
    for source in [r#""", ")""#, r#""(", """#, r#""(", ")", "extra""#] {
        assert!(parse_bracket_attribute_source(source).is_err(), "{source}");
    }
}

#[test]
fn strictness_is_ordered_typed_and_field_checked() {
    let declaration =
        parse_constructor_declaration_source("struct Add { lhs: Term<Expr>, rhs: Term<Expr> }")
            .unwrap();
    let strict = parse_strict_attribute_source("sequence = [lhs], result = Value").unwrap();
    assert_eq!(strict.kind(), StrictnessKind::Strict);
    assert!(strict.using().is_none());
    strict
        .validate_fields(
            declaration
                .fields()
                .iter()
                .map(krs_syntax::ConstructorField::name),
        )
        .unwrap();

    let sequential = parse_seqstrict_attribute_source(
        "result = value::Value, using = m3d_eval, sequence = [rhs, lhs],",
    )
    .unwrap();
    assert_eq!(sequential.kind(), StrictnessKind::SeqStrict);
    assert_eq!(sequential.using().unwrap(), "m3d_eval");
    assert_eq!(sequential.fields()[0], "rhs");
    assert_eq!(sequential.fields()[1], "lhs");
    let anchors = sequential.provenance().unwrap();
    assert_eq!(
        anchors[1].role(),
        ProvenanceRole::StrictnessContextAliasReference
    );
    assert_eq!(anchors[2].role(), ProvenanceRole::StrictnessFieldReference);
    assert_eq!(
        anchors[1].key().unwrap().role(),
        "strictness_context_alias_reference"
    );

    for source in [
        "sequence = [], result = Value",
        "sequence = [lhs, lhs], result = Value",
        "sequence = [module::lhs], result = Value",
        "sequence = [lhs]",
        "result = Value",
        "sequence = [lhs], result = Vec<Value>",
        "using = aliases::execute, sequence = [lhs], result = Value",
        "using = execute, using = other, sequence = [lhs], result = Value",
    ] {
        assert!(
            parse_seqstrict_attribute_source(source).is_err(),
            "{source}"
        );
    }
    let unknown = parse_seqstrict_attribute_source("sequence = [missing], result = Value").unwrap();
    assert!(matches!(
        unknown
            .validate_fields(
                declaration
                    .fields()
                    .iter()
                    .map(krs_syntax::ConstructorField::name),
            )
            .unwrap_err()
            .kind(),
        SyntaxErrorKind::InvalidStrictness { .. }
    ));
}

#[test]
fn precedence_supports_unrelated_chains_and_stable_flattened_order() {
    let declaration = parse_precedence_declaration_source(
        "multiplicative > additive > comparison; prefix > equality;",
    )
    .unwrap();
    assert!(declaration.owner().is_none());
    assert_eq!(declaration.chains().len(), 2);
    let edges = declaration.chains()[0].edges().collect::<Vec<_>>();
    assert_eq!(edges.len(), 2);
    assert_eq!(edges[0].higher(), "multiplicative");
    assert_eq!(edges[0].lower(), "additive");
    let references = declaration
        .provenance()
        .unwrap()
        .into_iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::PrecedenceGroupReference)
        .collect::<Vec<_>>();
    assert_eq!(references.len(), 5);
    assert_eq!(references[4].ordinal(), 4);

    for source in ["", "additive", "> additive", "a >", "a > b c > d"] {
        assert!(
            parse_precedence_declaration_source(source).is_err(),
            "{source}"
        );
    }
}

#[test]
fn precedence_accepts_an_optional_family_owner_and_rejects_malformed_owners() {
    let declaration = parse_precedence_declaration_source(
        "for Op; multiplicative > additive; prefix > equality;",
    )
    .unwrap();
    assert_eq!(declaration.owner().unwrap(), "Op");
    assert_eq!(declaration.chains().len(), 2);
    assert_eq!(
        declaration
            .provenance()
            .unwrap()
            .iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::PrecedenceGroupReference)
            .count(),
        4
    );

    for source in [
        "for; a > b",
        "for syntax::Op; a > b",
        "for Op a > b",
        "for Op;",
        "for Op;; a > b",
    ] {
        assert!(
            parse_precedence_declaration_source(source).is_err(),
            "{source}"
        );
    }
}

#[test]
fn associativity_is_typed_and_rejects_bad_punctuation() {
    let declaration = parse_associativity_declaration_source(
        "left: multiplicative, additive; right: exponent; non_associative: equality;",
    )
    .unwrap();
    assert!(declaration.owner().is_none());
    assert_eq!(declaration.sentences().len(), 3);
    assert_eq!(
        declaration.sentences()[0].associativity(),
        GroupAssociativity::Left
    );
    assert_eq!(
        declaration.sentences()[2].associativity(),
        GroupAssociativity::NonAssociative
    );
    assert_eq!(
        declaration
            .provenance()
            .unwrap()
            .iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::AssociativityGroupReference)
            .count(),
        4
    );

    for source in [
        "",
        "left additive;",
        "left:;",
        "middle: additive;",
        "left: additive additive;",
        "left: additive, additive;",
    ] {
        assert!(
            parse_associativity_declaration_source(source).is_err(),
            "{source}"
        );
    }
}

#[test]
fn associativity_accepts_an_optional_family_owner_and_rejects_malformed_owners() {
    let declaration = parse_associativity_declaration_source(
        "for StmtSyntax; left: application, addition; right: sequence;",
    )
    .unwrap();
    assert_eq!(declaration.owner().unwrap(), "StmtSyntax");
    assert_eq!(declaration.sentences().len(), 2);
    assert_eq!(
        declaration
            .provenance()
            .unwrap()
            .iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::AssociativityGroupReference)
            .count(),
        3
    );

    for source in [
        "for; left: addition;",
        "for syntax::Op; left: addition;",
        "for Op left: addition;",
        "for Op;",
        "for Op;; left: addition;",
    ] {
        assert!(
            parse_associativity_declaration_source(source).is_err(),
            "{source}"
        );
    }
}

#[test]
fn explicit_builtin_to_authored_subsort_retains_both_paths() {
    let declaration = parse_subsort_declaration_source("impl value::Value for k::Int {}").unwrap();
    assert_eq!(
        declaration.super_sort().to_token_stream().to_string(),
        "value :: Value"
    );
    assert_eq!(
        declaration.sub_sort().to_token_stream().to_string(),
        "k :: Int"
    );
    assert_eq!(declaration.spelling(), "value :: Value for k :: Int");
    let anchors = declaration.provenance().unwrap();
    assert_eq!(anchors[0].role(), ProvenanceRole::SubsortDeclaration);
    assert_eq!(anchors[1].role(), ProvenanceRole::SubsortSuperSort);
    assert_eq!(anchors[2].role(), ProvenanceRole::SubsortSubSort);

    for source in [
        "impl Int {}",
        "impl !Value for Int {}",
        "unsafe impl Value for Int {}",
        "impl<T> Value for T {}",
        "impl Value for (Int, Bool) {}",
        "impl Value for Int { fn marker() {} }",
    ] {
        assert!(matches!(
            parse_subsort_declaration_source(source).unwrap_err().kind(),
            SyntaxErrorKind::UnsupportedSubsortDeclaration { .. } | SyntaxErrorKind::RustSyntax(_)
        ));
    }
}

#[test]
fn rules_preserve_builtin_heads_binders_and_literals_for_v6() {
    let rule = parse_rule_item_source(
        "fn add(Add { lhs, rhs }: Term<Expr>) -> Term<Value> { int::add(lhs, int::sub(rhs, 0)) }",
    )
    .unwrap();
    let candidates = rule.m3a_term_reference_candidates().unwrap();
    let actual = candidates
        .iter()
        .map(|candidate| {
            (
                candidate.key().role().to_owned(),
                candidate.kind(),
                candidate.path_spelling(),
            )
        })
        .collect::<Vec<_>>();
    assert!(actual.contains(&(
        "rule_left_application_head".into(),
        TermSymbolKind::ApplicationHead,
        "Add".into()
    )));
    assert!(actual.contains(&(
        "rule_right_application_head".into(),
        TermSymbolKind::ApplicationHead,
        "int :: add".into()
    )));
    assert!(actual.contains(&(
        "rule_right_application_head".into(),
        TermSymbolKind::ApplicationHead,
        "int :: sub".into()
    )));
    assert!(
        !actual
            .iter()
            .any(|(_, _, path)| path == "lhs" || path == "rhs")
    );
    assert!(
        rule.m3a_provenance()
            .unwrap()
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::RuleRightLiteral)
    );

    let literal_root =
        parse_rule_item_source("fn identity(true: Term<k::Bool>) -> Term<k::Bool> { true }")
            .unwrap();
    let roles = literal_root
        .m3a_provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert!(roles.contains(&ProvenanceRole::RuleLeftLiteral));
    assert!(roles.contains(&ProvenanceRole::RuleRightLiteral));
}

#[test]
fn rule_records_preserve_field_identity_on_both_sides() {
    let rule = parse_rule_item_source(
        "fn swap(Add { rhs: y, lhs: x }: Term<Expr>) -> Term<Expr> { \
         Add { lhs: x, rhs: y } }",
    )
    .unwrap();
    let left = rule.subject_tree().application().unwrap();
    let left_names = left
        .arguments()
        .named()
        .unwrap()
        .iter()
        .map(|argument| argument.name().to_string())
        .collect::<Vec<_>>();
    assert_eq!(left_names, ["rhs", "lhs"]);

    let right_names = rule
        .result()
        .tree()
        .application()
        .unwrap()
        .arguments()
        .named()
        .unwrap()
        .iter()
        .map(|argument| argument.name().to_string())
        .collect::<Vec<_>>();
    assert_eq!(right_names, ["lhs", "rhs"]);

    let anchors = rule.m3a_provenance().unwrap();
    let left_fields = anchors
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::RuleLeftRecordFieldName)
        .collect::<Vec<_>>();
    let right_fields = anchors
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::RuleRightRecordFieldName)
        .collect::<Vec<_>>();
    assert_eq!(left_fields.len(), 2);
    assert_eq!(right_fields.len(), 2);
    assert_eq!(left_fields[0].ordinal(), 0);
    assert_eq!(left_fields[1].ordinal(), 1);
    assert_eq!(right_fields[0].ordinal(), 0);
    assert_eq!(right_fields[1].ordinal(), 1);
}

#[test]
fn rule_subject_wildcards_are_structured_and_exactly_keyed() {
    let rule = parse_rule_item_source(
        "fn short_circuit(And { lhs: false, rhs: _ }: Term<Expr>) -> Term<Expr> { false }",
    )
    .unwrap();
    let arguments = rule
        .subject_tree()
        .application()
        .unwrap()
        .arguments()
        .named()
        .unwrap();
    assert!(arguments[0].value().literal().is_some());
    assert!(arguments[1].value().wildcard_range().is_some());

    let wildcards = rule
        .m3a_provenance()
        .unwrap()
        .into_iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::RuleLeftWildcard)
        .collect::<Vec<_>>();
    assert_eq!(wildcards.len(), 1);
    assert_eq!(wildcards[0].ordinal(), 0);
    assert_eq!(wildcards[0].range().start().column, 40);
    assert_eq!(wildcards[0].range().end().column, 41);

    let multiple =
        parse_rule_item_source("fn many(Pair(_, Pair(_, _)): Term<Expr>) -> Term<Expr> { Done }")
            .unwrap();
    let multiple_wildcards = multiple
        .m3a_provenance()
        .unwrap()
        .into_iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::RuleLeftWildcard)
        .collect::<Vec<_>>();
    assert_eq!(
        multiple_wildcards
            .iter()
            .map(krs_syntax::ProvenanceAnchor::ordinal)
            .collect::<Vec<_>>(),
        [0, 1, 2]
    );
    assert!(
        multiple_wildcards
            .windows(2)
            .all(|pair| pair[0].range().start().column < pair[1].range().start().column)
    );

    assert!(parse_term_expression_source("_").is_err());
}

use quote::ToTokens;

#[test]
fn exact_public_surface_is_ordinary_rust_token_syntax() {
    let source = r#"
        #[k::sort]
        #[k::bracket("({value})")]
        pub trait Expr: KItem {}

        #[k::token(regex = r"[a-zA-Z][a-zA-Z0-9_]*", prec = 2)]
        pub struct Id(String);

        #[k::constructor(
            sort = Expr,
            syntax = "{lhs} + {rhs}",
            group = "additive",
            avoid = true,
            format = "%1%2%3",
        )]
        #[k::seqstrict(sequence = [lhs, rhs], result = Value)]
        pub struct Add {
            pub lhs: Term<dyn Expr>,
            pub rhs: Term<dyn Expr>,
        }

        #[k::subsort]
        impl Value for k::Int {}

        k::precedence! {
            multiplicative > additive > comparison;
            prefix > equality;
        }

        k::associativity! {
            left: multiplicative, additive, comparison;
            non_associative: equality;
        }
    "#;
    let file = syn::parse_file(source).unwrap();
    assert_eq!(file.items.len(), 6);
    syn::parse_file(&file.to_token_stream().to_string()).unwrap();
}

#[test]
fn every_imp_expression_operator_template_uses_the_frozen_item_shapes() {
    for operator in ["-", "!"] {
        let source = format!(r#"sort = Expr, syntax = "{operator}{{value}}", format = "%1%2""#);
        let attribute = parse_constructor_attribute_source(&source).unwrap();
        let declaration =
            parse_constructor_declaration_source("struct Unary { value: Term<Expr> }").unwrap();
        attribute.validate_declaration(&declaration).unwrap();
        assert_eq!(attribute.syntax_template().unwrap().items().len(), 2);
    }

    for operator in [
        "*", "/", "+", "-", ">=", ">", "<=", "<", "==", "!=", "&&", "||",
    ] {
        let source =
            format!(r#"sort = Expr, syntax = "{{lhs}} {operator} {{rhs}}", group = "operators""#);
        let attribute = parse_constructor_attribute_source(&source).unwrap();
        let declaration = parse_constructor_declaration_source(
            "struct Binary { lhs: Term<Expr>, rhs: Term<Expr> }",
        )
        .unwrap();
        attribute.validate_declaration(&declaration).unwrap();
        assert_eq!(
            attribute.syntax_template().unwrap().items()[1],
            SyntaxTemplateItem::Terminal(operator.into())
        );
    }
}

#[test]
fn m3a_reference_spans_and_ordinals_are_exact_and_deterministic() {
    let precedence =
        parse_precedence_declaration_source("multiplicative > additive; prefix > equality")
            .unwrap();
    let references = precedence
        .provenance()
        .unwrap()
        .into_iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::PrecedenceGroupReference)
        .collect::<Vec<_>>();
    assert_eq!(
        references
            .iter()
            .map(|anchor| (
                anchor.ordinal(),
                anchor.range().start().column,
                anchor.range().end().column,
            ))
            .collect::<Vec<_>>(),
        [(0, 0, 14), (1, 17, 25), (2, 27, 33), (3, 36, 44)]
    );

    let strict =
        parse_seqstrict_attribute_source("sequence = [right, left], result = value::Value")
            .unwrap();
    let anchors = strict.provenance().unwrap();
    assert_eq!(anchors[1].ordinal(), 0);
    assert_eq!(anchors[1].range().start().column, 12);
    assert_eq!(anchors[2].ordinal(), 1);
    assert_eq!(anchors[2].range().start().column, 19);
    assert_eq!(anchors[3].role(), ProvenanceRole::StrictnessResultSort);
    assert_eq!(anchors[3].range().start().column, 35);
}

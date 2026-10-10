//! Object-grammar, metadata, and provenance contract tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{
    GroupAssociativity, ProvenanceRole, StrictnessKind, StructuredFormatFragment, SyntaxErrorKind,
    SyntaxTemplateItem, TermSymbolKind,
};
use krs_test_support::assert_rejects;

#[test]
fn nominal_expr_production_is_checked_and_keyed() {
    let attribute = krs_syntax::ConstructorAttribute::parse_source(
        r#"sort = Expr, syntax = "{lhs} + {rhs}", group = "additive", avoid = true, format = "%1%2%3""#,
    )
    .unwrap();
    let declaration = krs_syntax::ConstructorDeclaration::parse_source(
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
        .full_provenance()
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
        .full_provenance()
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
    let declaration = krs_syntax::ConstructorDeclaration::parse_source(
        "struct Pair { left: Term<Expr>, right: Term<Expr> }",
    )
    .unwrap();
    let escaped = krs_syntax::ConstructorAttribute::parse_source(
        r#"sort = Expr, syntax = "{{{left}}}:{right}""#,
    )
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
        let attribute = krs_syntax::ConstructorAttribute::parse_source(source).unwrap();
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
            krs_syntax::ConstructorAttribute::parse_source(source)
                .unwrap_err()
                .kind(),
            SyntaxErrorKind::InvalidSyntaxTemplate { .. }
        ));
    }

    let unmatched_open =
        krs_syntax::ConstructorAttribute::parse_source(r#"sort = Expr, syntax = "{""#).unwrap_err();
    assert!(unmatched_open.to_string().contains("did you mean `{{`"));
}

#[test]
fn syntax_layout_is_nonsemantic_and_terminals_match_k_token_boundaries() {
    let attribute = krs_syntax::ConstructorAttribute::parse_source(
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
    let compact = krs_syntax::ConstructorAttribute::parse_source(
        r#"sort = Expr, syntax = "if({condition}){body}else{otherwise}""#,
    )
    .unwrap();
    assert_eq!(
        attribute.syntax_template().unwrap().items(),
        compact.syntax_template().unwrap().items()
    );

    let operators = krs_syntax::ConstructorAttribute::parse_source(
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
            .full_provenance()
            .unwrap()
            .iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::ConstructorSyntaxItem)
            .count(),
        7
    );
}

#[test]
fn group_avoid_and_structured_format_values_are_closed() {
    for (source, expected_kind) in [
        (
            r#"sort = Expr, group = """#,
            SyntaxErrorKind::InvalidArgumentValue {
                name: "group",
                expected: "a nonempty identifier-shaped Rust string literal",
            },
        ),
        (
            r#"sort = Expr, group = "a::b""#,
            SyntaxErrorKind::InvalidArgumentValue {
                name: "group",
                expected: "a nonempty identifier-shaped Rust string literal",
            },
        ),
        (
            "sort = Expr, avoid = choice",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "avoid",
                expected: "a Rust Boolean literal",
            },
        ),
        (
            "sort = Expr, avoid = false",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "avoid",
                expected: "the Rust Boolean literal `true`",
            },
        ),
        (
            r#"sort = Expr, format = "%""#,
            SyntaxErrorKind::InvalidFormat {
                reason: "`%` must be followed by `%n`, `%i`, `%d`, `%c`, `%r`, `%%`, or a one-based item position",
            },
        ),
        (
            r#"sort = Expr, format = "%0""#,
            SyntaxErrorKind::InvalidFormat {
                reason: "item positions are one-based and `%0` is invalid",
            },
        ),
        (
            r#"sort = Expr, format = "%70000""#,
            SyntaxErrorKind::InvalidFormat {
                reason: "an item position must fit in `u16`",
            },
        ),
    ] {
        let error = krs_syntax::ConstructorAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }

    let declaration = krs_syntax::ConstructorDeclaration::parse_source("struct Unit;").unwrap();
    let out_of_range = krs_syntax::ConstructorAttribute::parse_source(
        r#"sort = Expr, syntax = "unit", format = "%2""#,
    )
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
        krs_syntax::TokenAttribute::parse_source(r#"regex = r"[a-zA-Z][a-zA-Z0-9_]*", prec = 2"#)
            .unwrap();
    assert_eq!(attribute.regex().unwrap().value(), "[a-zA-Z][a-zA-Z0-9_]*");
    assert_eq!(attribute.lexical_precedence(), Some(2));
    let declaration = krs_syntax::TokenDeclaration::parse_source("pub struct Id(String);").unwrap();
    assert_eq!(declaration.name(), "Id");
    assert_eq!(
        declaration.provenance().unwrap()[0].role(),
        ProvenanceRole::TokenDeclaration
    );

    for (source, expected_kind) in [
        (
            r#"regex = """#,
            SyntaxErrorKind::InvalidTokenRegex {
                reason: "the regex must not be empty",
            },
        ),
        (
            r#"regex = "[a-z""#,
            SyntaxErrorKind::InvalidTokenRegex {
                reason: "unclosed character class",
            },
        ),
        (
            r#"regex = "(abc""#,
            SyntaxErrorKind::InvalidTokenRegex {
                reason: "unclosed parenthesis",
            },
        ),
        (
            r#"regex = "abc\\""#,
            SyntaxErrorKind::InvalidTokenRegex {
                reason: "dangling escape",
            },
        ),
        (
            r#"regex = "abc", prec = -1"#,
            SyntaxErrorKind::InvalidArgumentValue {
                name: "prec",
                expected: "an unsuffixed nonnegative `u32` integer literal",
            },
        ),
        (
            r#"regex = "abc", prec = 2u8"#,
            SyntaxErrorKind::InvalidArgumentValue {
                name: "prec",
                expected: "an unsuffixed nonnegative `u32` integer literal",
            },
        ),
        (
            r#"regex = "abc", regex = "def""#,
            SyntaxErrorKind::DuplicateArgument { name: "regex" },
        ),
    ] {
        let error = krs_syntax::TokenAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
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
            krs_syntax::TokenDeclaration::parse_source(source)
                .unwrap_err()
                .kind(),
            SyntaxErrorKind::UnsupportedTokenDeclaration { .. }
        ));
    }
}

#[test]
fn bracket_is_syntax_only_and_has_one_same_sort_value() {
    let bracket = krs_syntax::BracketAttribute::parse_source(r#""({value})""#).unwrap();
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
    for (source, expected_kind) in [
        (
            r#""({other})""#,
            SyntaxErrorKind::UnknownTemplateField {
                name: "other".into(),
            },
        ),
        (
            r#""({value}{value})""#,
            SyntaxErrorKind::InvalidTemplateFieldOccurrence {
                name: "value".into(),
                expected: 1,
                actual: 2,
            },
        ),
        (
            r#""{value}""#,
            SyntaxErrorKind::InvalidSyntaxTemplate {
                reason: "a bracket must contain terminal text around `{value}`",
            },
        ),
        (
            r#""(""#,
            SyntaxErrorKind::InvalidTemplateFieldOccurrence {
                name: "value".into(),
                expected: 1,
                actual: 0,
            },
        ),
        (
            r#""({value})", extra"#,
            SyntaxErrorKind::RustSyntax("expected string literal".into()),
        ),
    ] {
        let error = krs_syntax::BracketAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }

    let delimiters = krs_syntax::BracketAttribute::parse_source(r#""(", ")""#).unwrap();
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
    for (source, expected_kind) in [
        (
            r#""", ")""#,
            SyntaxErrorKind::InvalidSyntaxTemplate {
                reason: "bracket delimiters must not be empty",
            },
        ),
        (
            r#""(", """#,
            SyntaxErrorKind::InvalidSyntaxTemplate {
                reason: "bracket delimiters must not be empty",
            },
        ),
        (
            r#""(", ")", "extra""#,
            SyntaxErrorKind::RustSyntax("expected exactly two bracket delimiter literals".into()),
        ),
    ] {
        let error = krs_syntax::BracketAttribute::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One fixture checks the complete ordered strictness and field-validation contract."
)]
fn strictness_is_ordered_typed_and_field_checked() {
    let declaration = krs_syntax::ConstructorDeclaration::parse_source(
        "struct Add { lhs: Term<Expr>, rhs: Term<Expr> }",
    )
    .unwrap();
    let strict = krs_syntax::parse_strict_attribute(
        krs_syntax::parse::tokens_from_source("sequence = [lhs], result = Value").unwrap(),
    )
    .unwrap();
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

    let sequential = krs_syntax::parse_seqstrict_attribute(
        krs_syntax::parse::tokens_from_source(
            "result = value::Value, using = eval_context, sequence = [rhs, lhs],",
        )
        .unwrap(),
    )
    .unwrap();
    assert_eq!(sequential.kind(), StrictnessKind::SeqStrict);
    assert_eq!(sequential.using().unwrap(), "eval_context");
    assert_eq!(sequential.fields()[0], "rhs");
    assert_eq!(sequential.fields()[1], "lhs");
    let anchors = sequential.provenance().unwrap();
    assert_eq!(
        anchors[1].role(),
        ProvenanceRole::StrictnessContextAliasReference
    );
    assert_eq!(anchors[2].role(), ProvenanceRole::StrictnessFieldReference);
    assert_eq!(
        anchors[1].key().role(),
        ProvenanceRole::StrictnessContextAliasReference
    );

    for (source, expected_kind) in [
        (
            "sequence = [], result = Value",
            SyntaxErrorKind::InvalidStrictness {
                reason: "the field sequence must not be empty",
            },
        ),
        (
            "sequence = [lhs, lhs], result = Value",
            SyntaxErrorKind::InvalidStrictness {
                reason: "the field sequence must not contain duplicates",
            },
        ),
        (
            "sequence = [module::lhs], result = Value",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "sequence",
                expected: "an array of unqualified Rust field identifiers",
            },
        ),
        (
            "sequence = [lhs]",
            SyntaxErrorKind::MissingArgument { name: "result" },
        ),
        (
            "result = Value",
            SyntaxErrorKind::MissingArgument { name: "sequence" },
        ),
        (
            "sequence = [lhs], result = Vec<Value>",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "result",
                expected: "a plain Rust sort path",
            },
        ),
        (
            "using = aliases::execute, sequence = [lhs], result = Value",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "using",
                expected: "an unqualified Rust context-alias identifier",
            },
        ),
        (
            "using = execute, using = other, sequence = [lhs], result = Value",
            SyntaxErrorKind::DuplicateArgument { name: "using" },
        ),
    ] {
        let error = krs_syntax::parse_seqstrict_attribute(
            krs_syntax::parse::tokens_from_source(source).unwrap(),
        )
        .unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
    let unknown = krs_syntax::parse_seqstrict_attribute(
        krs_syntax::parse::tokens_from_source("sequence = [missing], result = Value").unwrap(),
    )
    .unwrap();
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
    let declaration = krs_syntax::PrecedenceDeclaration::parse_source(
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

    for (source, expected_kind) in [
        (
            "",
            SyntaxErrorKind::InvalidGrammarMacro {
                reason: "precedence must contain at least one chain",
            },
        ),
        (
            "additive",
            SyntaxErrorKind::InvalidGrammarMacro {
                reason: "a precedence chain must contain at least one `>`",
            },
        ),
        (
            "> additive",
            SyntaxErrorKind::RustSyntax("expected identifier".into()),
        ),
        (
            "a >",
            SyntaxErrorKind::RustSyntax("unexpected end of input, expected identifier".into()),
        ),
        (
            "a > b c > d",
            SyntaxErrorKind::RustSyntax("expected `;`".into()),
        ),
    ] {
        let error = krs_syntax::PrecedenceDeclaration::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn precedence_accepts_an_optional_family_owner_and_rejects_malformed_owners() {
    let declaration = krs_syntax::PrecedenceDeclaration::parse_source(
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

    for (source, expected_kind) in [
        (
            "for; a > b",
            SyntaxErrorKind::RustSyntax("expected identifier".into()),
        ),
        (
            "for syntax::Op; a > b",
            SyntaxErrorKind::RustSyntax("expected `;`".into()),
        ),
        (
            "for Op a > b",
            SyntaxErrorKind::RustSyntax("expected `;`".into()),
        ),
        (
            "for Op;",
            SyntaxErrorKind::InvalidGrammarMacro {
                reason: "precedence must contain at least one chain",
            },
        ),
        (
            "for Op;; a > b",
            SyntaxErrorKind::RustSyntax("expected identifier".into()),
        ),
    ] {
        let error = krs_syntax::PrecedenceDeclaration::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn associativity_is_typed_and_rejects_bad_punctuation() {
    let declaration = krs_syntax::AssociativityDeclaration::parse_source(
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

    for (source, expected_kind) in [
        (
            "",
            SyntaxErrorKind::InvalidGrammarMacro {
                reason: "associativity must contain at least one sentence",
            },
        ),
        (
            "left additive;",
            SyntaxErrorKind::RustSyntax("expected `:`".into()),
        ),
        (
            "left:;",
            SyntaxErrorKind::InvalidGrammarMacro {
                reason: "an associativity sentence must name at least one group",
            },
        ),
        (
            "middle: additive;",
            SyntaxErrorKind::InvalidGrammarMacro {
                reason: "expected `left`, `right`, or `non_associative`",
            },
        ),
        (
            "left: additive additive;",
            SyntaxErrorKind::RustSyntax("expected `;`".into()),
        ),
        (
            "left: additive, additive;",
            SyntaxErrorKind::InvalidGrammarMacro {
                reason: "an associativity sentence must not repeat a group",
            },
        ),
    ] {
        let error = krs_syntax::AssociativityDeclaration::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn associativity_accepts_an_optional_family_owner_and_rejects_malformed_owners() {
    let declaration = krs_syntax::AssociativityDeclaration::parse_source(
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

    for (source, expected_kind) in [
        (
            "for; left: addition;",
            SyntaxErrorKind::RustSyntax("expected identifier".into()),
        ),
        (
            "for syntax::Op; left: addition;",
            SyntaxErrorKind::RustSyntax("expected `;`".into()),
        ),
        (
            "for Op left: addition;",
            SyntaxErrorKind::RustSyntax("expected `;`".into()),
        ),
        (
            "for Op;",
            SyntaxErrorKind::InvalidGrammarMacro {
                reason: "associativity must contain at least one sentence",
            },
        ),
        (
            "for Op;; left: addition;",
            SyntaxErrorKind::RustSyntax("expected identifier".into()),
        ),
    ] {
        let error = krs_syntax::AssociativityDeclaration::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn explicit_builtin_to_authored_subsort_retains_both_paths() {
    let declaration =
        krs_syntax::SubsortDeclaration::parse_source("impl value::ValueSort for k::Int {}")
            .unwrap();
    assert_eq!(
        declaration.super_sort().to_token_stream().to_string(),
        "value :: ValueSort"
    );
    assert_eq!(
        declaration.sub_sort().to_token_stream().to_string(),
        "k :: Int"
    );
    assert_eq!(declaration.spelling(), "value::ValueSort for k::Int");
    assert!(declaration.unaliased_error().to_string().contains(
        "write `#[k::subsort(sort = value::Value)] impl value::ValueSort for k::Int {}`"
    ));
    let attribute = krs_syntax::SubsortAttribute::parse_source("sort = value::Value").unwrap();
    let anchors = declaration.provenance(&attribute).unwrap();
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
            krs_syntax::SubsortDeclaration::parse_source(source)
                .unwrap_err()
                .kind(),
            SyntaxErrorKind::UnsupportedSubsortDeclaration { .. } | SyntaxErrorKind::RustSyntax(_)
        ));
    }
}

#[test]
fn rules_preserve_builtin_heads_binders_and_literals() {
    let rule = krs_syntax::RuleItem::parse_source(
        "fn add(Add { lhs, rhs }: Term<Expr>) -> Term<Value> { int::add(lhs, int::sub(rhs, 0)) }",
    )
    .unwrap();
    let candidates = rule.term_reference_candidates().unwrap();
    let actual = candidates
        .iter()
        .map(|candidate| {
            (
                candidate.key().role(),
                candidate.kind(),
                candidate.path_spelling(),
            )
        })
        .collect::<Vec<_>>();
    assert!(actual.contains(&(
        ProvenanceRole::RuleLeftApplicationHead,
        TermSymbolKind::ApplicationHead,
        "Add".into()
    )));
    assert!(actual.contains(&(
        ProvenanceRole::RuleRightApplicationHead,
        TermSymbolKind::ApplicationHead,
        "int::add".into()
    )));
    assert!(actual.contains(&(
        ProvenanceRole::RuleRightApplicationHead,
        TermSymbolKind::ApplicationHead,
        "int::sub".into()
    )));
    assert!(
        !actual
            .iter()
            .any(|(_, _, path)| path == "lhs" || path == "rhs")
    );
    assert!(
        rule.full_provenance()
            .unwrap()
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::RuleRightLiteral)
    );

    let literal_root = krs_syntax::RuleItem::parse_source(
        "fn identity(true: Term<k::Bool>) -> Term<k::Bool> { true }",
    )
    .unwrap();
    let roles = literal_root
        .full_provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert!(roles.contains(&ProvenanceRole::RuleLeftLiteral));
    assert!(roles.contains(&ProvenanceRole::RuleRightLiteral));
}

#[test]
fn rule_records_preserve_field_identity_on_both_sides() {
    let rule = krs_syntax::RuleItem::parse_source(
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
        .unwrap()
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

    let anchors = rule.full_provenance().unwrap();
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
    let rule = krs_syntax::RuleItem::parse_source(
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
        .full_provenance()
        .unwrap()
        .into_iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::RuleLeftWildcard)
        .collect::<Vec<_>>();
    assert_eq!(wildcards.len(), 1);
    assert_eq!(wildcards[0].ordinal(), 0);
    assert_eq!(wildcards[0].range().start().column, 40);
    assert_eq!(wildcards[0].range().end().column, 41);

    let multiple = krs_syntax::RuleItem::parse_source(
        "fn many(Pair(_, Pair(_, _)): Term<Expr>) -> Term<Expr> { Done }",
    )
    .unwrap();
    let multiple_wildcards = multiple
        .full_provenance()
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

    assert_rejects!(
        krs_syntax::TermExpression::parse_source("_"),
        error if matches!(error.kind(), SyntaxErrorKind::UnsupportedTermExpression { .. })
    );
}

use quote::ToTokens;

#[test]
fn exact_public_surface_is_ordinary_rust_token_syntax() {
    let source = r#"
        #[k::sort(alias = Expr, parents = [k::KItem])]
        #[k::bracket("({value})")]
        pub trait ExprSort: k::KItemSort {}

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
            pub lhs: Term<dyn ExprSort>,
            pub rhs: Term<dyn ExprSort>,
        }

        #[k::subsort(sort = Value)]
        impl ValueSort for k::Int {}

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
        let attribute = krs_syntax::ConstructorAttribute::parse_source(&source).unwrap();
        let declaration =
            krs_syntax::ConstructorDeclaration::parse_source("struct Unary { value: Term<Expr> }")
                .unwrap();
        attribute.validate_declaration(&declaration).unwrap();
        assert_eq!(attribute.syntax_template().unwrap().items().len(), 2);
    }

    for operator in [
        "*", "/", "+", "-", ">=", ">", "<=", "<", "==", "!=", "&&", "||",
    ] {
        let source =
            format!(r#"sort = Expr, syntax = "{{lhs}} {operator} {{rhs}}", group = "operators""#);
        let attribute = krs_syntax::ConstructorAttribute::parse_source(&source).unwrap();
        let declaration = krs_syntax::ConstructorDeclaration::parse_source(
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
fn term_reference_spans_and_ordinals_are_exact_and_deterministic() {
    let precedence = krs_syntax::PrecedenceDeclaration::parse_source(
        "multiplicative > additive; prefix > equality",
    )
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

    let strict = krs_syntax::parse_seqstrict_attribute(
        krs_syntax::parse::tokens_from_source("sequence = [right, left], result = value::Value")
            .unwrap(),
    )
    .unwrap();
    let anchors = strict.provenance().unwrap();
    assert_eq!(anchors[1].ordinal(), 0);
    assert_eq!(anchors[1].range().start().column, 12);
    assert_eq!(anchors[2].ordinal(), 1);
    assert_eq!(anchors[2].range().start().column, 19);
    assert_eq!(anchors[3].role(), ProvenanceRole::StrictnessResultSort);
    assert_eq!(anchors[3].range().start().column, 35);
}

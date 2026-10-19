//! Named term grammar and endpoint-preservation tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{
    ProvenanceRole, SyntaxErrorKind, TermArguments, TermRootKind, TermSymbolKind, TermTree,
};

#[test]
fn named_call_terms_preserve_preorder_paths_and_exact_endpoints() {
    let source = "m::Outer(inner::Leaf(value))";
    let term = krs_syntax::TermExpression::parse_source(source).unwrap();
    assert_eq!(term.root_kind(), TermRootKind::Call);
    let symbols = term.symbols();
    assert_eq!(symbols.len(), 3);
    assert_eq!(symbols[0].kind(), TermSymbolKind::ApplicationHead);
    assert_eq!(symbols[0].path().segments.last().unwrap().ident, "Outer");
    assert_eq!(symbols[1].path().segments.last().unwrap().ident, "Leaf");
    assert_eq!(symbols[2].kind(), TermSymbolKind::Reference);

    let anchors = term.provenance().unwrap();
    assert_eq!(anchors[0].role(), ProvenanceRole::TermPayload);
    assert_eq!(
        (
            anchors[0].range().start().line,
            anchors[0].range().start().column
        ),
        (1, 0)
    );
    assert_eq!(
        (
            anchors[0].range().end().line,
            anchors[0].range().end().column
        ),
        (1, source.len())
    );
    assert_eq!(
        (
            anchors[1].range().start().column,
            anchors[1].range().end().column
        ),
        (0, 8)
    );
    assert_eq!(
        (
            anchors[2].range().start().column,
            anchors[2].range().end().column
        ),
        (9, 20)
    );
    assert_eq!(
        (
            anchors[3].range().start().column,
            anchors[3].range().end().column
        ),
        (21, 26)
    );
    assert_eq!(anchors[3].key().role(), ProvenanceRole::TermPath);
    assert_eq!(anchors[3].key().ordinal(), 2);
}

#[test]
fn record_and_unit_terms_are_accepted() {
    let record = krs_syntax::TermExpression::parse_source(
        "crate::Add { lhs, rhs: IntValue(1), flag: true }",
    )
    .unwrap();
    assert_eq!(record.root_kind(), TermRootKind::Record);
    assert_eq!(record.symbols().len(), 3);

    let unit = krs_syntax::TermExpression::parse_source("syntax::Done").unwrap();
    assert_eq!(unit.root_kind(), TermRootKind::Named);
}

#[test]
fn int_and_bool_literals_are_root_and_nested_nodes() {
    let integer = krs_syntax::TermExpression::parse_source("42").unwrap();
    assert_eq!(integer.root_kind(), TermRootKind::Literal);
    assert_eq!(integer.nodes().len(), 1);

    let boolean = krs_syntax::TermExpression::parse_source("bool_ops::not(false)").unwrap();
    assert_eq!(boolean.nodes().len(), 2);
    let anchors = boolean.full_provenance().unwrap();
    assert_eq!(anchors[1].role(), ProvenanceRole::TermApplicationHead);
    assert_eq!(anchors[2].role(), ProvenanceRole::TermLiteral);
}

#[test]
fn out_of_scope_rust_expressions_are_rejected() {
    for source in [
        "lhs + rhs",
        "lhs & rhs",
        "!flag",
        "lhs < rhs",
        "if test { A } else { B }",
        "Ctor { field, ..base }",
        "42u32",
        "1.0f16",
        "'x'",
        "outer!(value)",
    ] {
        let error = krs_syntax::TermExpression::parse_source(source).unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::UnsupportedTermExpression { .. } | SyntaxErrorKind::UnsupportedPath
        ));
    }
}

/// The call a notation tree denotes, spelled with the operation paths that
/// expansion qualifies by the facade's `builtin` module.
fn denoted(tree: &TermTree) -> String {
    match tree {
        TermTree::Application(application) => {
            assert!(
                application.instance().is_empty(),
                "the domain is no instance"
            );
            let head = krs_syntax::notation_operation(application.head())
                .unwrap_or_else(|| application.head().clone());
            let head = quote::ToTokens::to_token_stream(&head)
                .to_string()
                .replace(' ', "");
            let TermArguments::Positional(arguments) = application.arguments() else {
                panic!("notation denotes positional calls");
            };
            let arguments = arguments.iter().map(denoted).collect::<Vec<_>>();
            format!("{head}({})", arguments.join(", "))
        }
        TermTree::Reference(path) => quote::ToTokens::to_token_stream(path).to_string(),
        TermTree::Literal(literal) => literal.spelling(),
        other => panic!("unexpected notation operand {other:?}"),
    }
}

fn denoted_source(source: &str) -> String {
    let term = krs_syntax::TermExpression::parse_source(source).unwrap();
    assert_eq!(term.root_kind(), TermRootKind::Call, "{source}");
    denoted(term.tree())
}

#[test]
fn connectives_denote_short_circuit_calls_with_rust_grouping() {
    for (source, expected) in [
        ("a && b", "bool::and_then(a, b)"),
        ("a || b", "bool::or_else(a, b)"),
        ("a || b && c", "bool::or_else(a, bool::and_then(b, c))"),
        ("a && b || c", "bool::or_else(bool::and_then(a, b), c)"),
        ("a && b && c", "bool::and_then(bool::and_then(a, b), c)"),
        ("a || b || c", "bool::or_else(bool::or_else(a, b), c)"),
        ("(a || b) && c", "bool::and_then(bool::or_else(a, b), c)"),
        ("a && (b && c)", "bool::and_then(a, bool::and_then(b, c))"),
        ("Ok(a) || true", "bool::or_else(Ok(a), true)"),
    ] {
        assert_eq!(denoted_source(source), expected, "{source}");
    }
}

#[test]
fn domain_method_calls_denote_module_calls_and_chain() {
    for (source, expected) in [
        ("a.lt::<Int>(b)", "int::lt(a, b)"),
        ("a.not::<Bool>()", "bool::not(a)"),
        ("s.concat::<String>(t)", "string::concat(s, t)"),
        ("x.sqrt::<Float>()", "float::sqrt(x)"),
        ("b.length::<Bytes>()", "bytes::length(b)"),
        ("a.eq::<K>(b)", "kequal::eq(a, b)"),
        ("c.ite::<K>(1, 2)", "kequal::ite(c, 1, 2)"),
        ("a.r#pow_mod::<Int>(b, m)", "int::pow_mod(a, b, m)"),
        (
            "b.bit_and::<Int>(m).ne::<Int>(b)",
            "int::ne(int::bit_and(b, m), b)",
        ),
        (
            "d.ne::<Int>(0) && n.div::<Int>(d).gt::<Int>(1)",
            "bool::and_then(int::ne(d, 0), int::gt(int::div(n, d), 1))",
        ),
        (
            "Pair(x, y).eq::<K>(Pair(y, x))",
            "kequal::eq(Pair(x, y), Pair(y, x))",
        ),
    ] {
        assert_eq!(denoted_source(source), expected, "{source}");
    }
}

#[test]
fn notation_heads_take_the_operator_and_method_spans_inside_the_authored_payload() {
    let source = "a && x.lt::<Int>(y)";
    let term = krs_syntax::TermExpression::parse_source(source).unwrap();
    let columns = |range: krs_syntax::TokenRange| (range.start().column, range.end().column);
    let anchors = term.full_provenance().unwrap();
    assert_eq!(anchors[0].role(), ProvenanceRole::TermPayload);
    assert_eq!(columns(anchors[0].range()), (0, source.len()));
    let heads = anchors
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::TermApplicationHead)
        .map(|anchor| columns(anchor.range()))
        .collect::<Vec<_>>();
    assert_eq!(heads, [(2, 4), (7, 9)]);
    let kinds = term
        .symbols()
        .iter()
        .map(krs_syntax::TermSymbol::kind)
        .collect::<Vec<_>>();
    assert_eq!(
        kinds,
        [
            TermSymbolKind::ApplicationHead,
            TermSymbolKind::Reference,
            TermSymbolKind::ApplicationHead,
            TermSymbolKind::Reference,
            TermSymbolKind::Reference,
        ]
    );
    assert_eq!(term.spelling(), "a && x . lt :: < Int > (y)");
}

#[test]
fn denoted_tokens_qualify_generated_heads_and_keep_authored_spans() {
    let term =
        krs_syntax::TermExpression::parse_source("Wrap(a || b.lt::<Int>(c), k::is!(Int, d && e))")
            .unwrap();
    let builtin: syn::Path = syn::parse_str("::renamed::builtin").unwrap();
    assert_eq!(
        term.denoted_tokens(&builtin).to_string(),
        "Wrap (:: renamed :: builtin :: bool :: or_else (a , :: renamed :: builtin :: int :: lt (b , c)) , k :: is ! (Int , d && e))"
    );
}

#[test]
fn malformed_method_calls_name_the_domain_or_the_call_form() {
    for (source, expected) in [
        (
            "a.lt(b)",
            "a method call names its builtin domain in a turbofish: write `lt::<Int>`, `lt::<String>`, or `lt::<Float>`",
        ),
        (
            "a.and_then(b)",
            "a method call names its builtin domain in a turbofish: write `and_then::<Bool>`",
        ),
        (
            "a.frobnicate::<Int>(b)",
            "the builtin module `int` has no operation `frobnicate`",
        ),
        (
            "a.concat::<Int>(b)",
            "the builtin module `int` has no operation `concat`; `concat::<String>` or `concat::<Bytes>` exist",
        ),
        (
            "a.lt::<Nat>(b)",
            "`Nat` is not a builtin domain; a method call names `Int`, `Bool`, `String`, `Float`, `Bytes`, or `K`",
        ),
        (
            "a.lt::<k::builtin::Int>(b)",
            "the turbofish of a method call names one builtin domain by its bare name",
        ),
        (
            "c.ite::<K, Int>(a, b)",
            "the turbofish of a method call names one builtin domain by its bare name",
        ),
        (
            "x.empty::<Bytes>()",
            "`bytes::empty` takes no operands, so it has no receiver; write the call `bytes::empty()`",
        ),
        (
            "a.clone()",
            "`.clone(..)` is not a builtin operation of any domain",
        ),
        ("f(a.gt::<Int>(0) && b.lt(1))", "write `lt::<Int>`"),
    ] {
        let error = krs_syntax::TermExpression::parse_source(source).unwrap_err();
        let SyntaxErrorKind::InvalidExpressionNotation { reason } = error.kind() else {
            panic!("{source}: expected an expression-notation error, found {error}");
        };
        assert!(reason.contains(expected), "{source}: {reason}");
    }
}

#[test]
fn a_left_hand_side_rejects_notation_by_name() {
    for (source, expected) in [
        (
            "fn r(k::term![Check(a && b)]: Term<Bool>) -> Term<Bool> { a }",
            "`&&` is not a pattern: a left-hand side matches `bool::and_then` only as the call `bool::and_then(..)`",
        ),
        (
            "fn r(k::term![Check(a || b)]: Term<Bool>) -> Term<Bool> { a }",
            "`||` is not a pattern: a left-hand side matches `bool::or_else` only as the call `bool::or_else(..)`",
        ),
        (
            "fn r(k::term![Check(a.lt::<Int>(b))]: Term<Bool>) -> Term<Bool> { a }",
            "a method call is not a pattern: a left-hand side matches `int::lt` only as the call `int::lt(..)`",
        ),
        (
            "fn r(k::term![Check(a.lt(b))]: Term<Bool>) -> Term<Bool> { a }",
            "write `lt::<Int>`",
        ),
    ] {
        let error = krs_syntax::RuleItem::parse_source(source).unwrap_err();
        let SyntaxErrorKind::InvalidExpressionNotation { reason } = error.kind() else {
            panic!("{source}: expected an expression-notation error, found {error}");
        };
        assert!(reason.contains(expected), "{source}: {reason}");
    }
    let error = krs_syntax::parse_cells_pattern("k: KCell(Check(a && b), ..), ..".parse().unwrap())
        .unwrap_err();
    assert!(
        matches!(
            error.kind(),
            SyntaxErrorKind::InvalidExpressionNotation { .. }
        ),
        "{error}"
    );
}

#[test]
fn notation_is_accepted_wherever_the_denoted_call_is() {
    let rule = krs_syntax::RuleItem::parse_source(
        "#[k::requires(n.gt::<Int>(0) && (t.lt::<Int>(c) || b.bit_and::<Int>(m).ne::<Int>(b)))]
         fn r(k::term![Check(n, t, c, b, m)]: Term<Bool>) -> Term<Bool> { n.ge::<Int>(t) || false }",
    )
    .unwrap();
    assert_eq!(
        denoted(rule.requires().unwrap().term().tree()),
        "bool::and_then(int::gt(n, 0), bool::or_else(int::lt(t, c), int::ne(int::bit_and(b, m), b)))"
    );
    let sequence = krs_syntax::parse_k_sequence_expression(
        "Assert(a && b), Compare(x.max::<Int>(y))".parse().unwrap(),
    )
    .unwrap();
    assert_eq!(
        denoted(sequence.items()[0].tree()),
        "Assert(bool::and_then(a, b))"
    );
    assert_eq!(
        denoted(sequence.items()[1].tree()),
        "Compare(int::max(x, y))"
    );
    let block =
        krs_syntax::TermExpression::parse_source("{ let x = a.add::<Int>(1); x.gt::<Int>(0) }")
            .unwrap();
    assert!(matches!(block.tree(), TermTree::Let { .. }));
    let or_bool =
        krs_syntax::TermExpression::parse_source("k::or_bool!(a && b, c.lt::<Int>(d))").unwrap();
    assert!(matches!(or_bool.tree(), TermTree::OrBool { .. }));
}

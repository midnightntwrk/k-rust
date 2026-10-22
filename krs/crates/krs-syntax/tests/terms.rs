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
        "*pointer",
        "lhs = rhs",
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
            let head = quote::ToTokens::to_token_stream(application.head())
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

#[test]
fn only_notation_marks_an_application_as_notation() {
    let term = krs_syntax::TermExpression::parse_source(
        "Wrap(a && b, __krs_builtin::int::add(a, 1), int::add(a, 1))",
    )
    .unwrap();
    let TermTree::Application(wrap) = term.tree() else {
        panic!("a call");
    };
    let TermArguments::Positional(arguments) = wrap.arguments() else {
        panic!("positional arguments");
    };
    let notation = arguments
        .iter()
        .map(|argument| match argument {
            TermTree::Application(application) => (
                quote::ToTokens::to_token_stream(application.head())
                    .to_string()
                    .replace(' ', ""),
                application.is_notation(),
            ),
            other => panic!("unexpected argument {other:?}"),
        })
        .collect::<Vec<_>>();
    assert!(!wrap.is_notation());
    assert_eq!(
        notation,
        [
            ("bool::and_then".to_owned(), true),
            ("__krs_builtin::int::add".to_owned(), false),
            ("int::add".to_owned(), false),
        ]
    );
}

#[test]
fn readable_patterns_name_notation_where_a_pattern_parser_stops() {
    for (source, expected) in [
        (
            "for Exp; check: Check { a: n && m } => n;",
            "`&&` is not a pattern",
        ),
        (
            "for Exp; check: Check(n.lt::<Int>(m)) => n;",
            "a method call is not a pattern: a left-hand side matches `int::lt`",
        ),
        ("for Exp; check: n || m => n;", "`||` is not a pattern"),
        (
            "for Machine; burn: { fuel: f.add::<Int>(1), acc: a } => { acc: a };",
            "a method call is not a pattern: a left-hand side matches `int::add`",
        ),
    ] {
        let error = krs_syntax::RuleBlock::parse_source(source).unwrap_err();
        let SyntaxErrorKind::InvalidExpressionNotation { reason } = error.kind() else {
            panic!("{source}: expected an expression-notation error, found {error}");
        };
        assert!(reason.contains(expected), "{source}: {reason}");
    }
}

#[test]
fn operators_denote_their_markers_with_rust_precedence() {
    for (source, expected) in [
        ("a + b", "__operator::add(a, b)"),
        ("a - b * c", "__operator::sub(a, __operator::mul(b, c))"),
        ("a / b % c", "__operator::rem(__operator::div(a, b), c)"),
        ("a << 1 >> b", "__operator::shr(__operator::shl(a, 1), b)"),
        (
            "(a & 15) + (b & 15) > 15",
            "__operator::gt(__operator::add(__operator::bit_and(a, 15), __operator::bit_and(b, 15)), 15)",
        ),
        (
            "a & 15 == 0",
            "__operator::eq(__operator::bit_and(a, 15), 0)",
        ),
        (
            "a | b ^ c & d",
            "__operator::bit_or(a, __operator::bit_xor(b, __operator::bit_and(c, d)))",
        ),
        ("-x * y", "__operator::mul(__operator::neg(x), y)"),
        ("!(a == b)", "__operator::not(__operator::eq(a, b))"),
        (
            "!a && b != c",
            "bool::and_then(__operator::not(a), __operator::ne(b, c))",
        ),
        (
            "a <= b || a >= c",
            "bool::or_else(__operator::le(a, b), __operator::ge(a, c))",
        ),
        ("a < -1", "__operator::lt(a, -1)"),
        ("x - -1.5", "__operator::sub(x, -1.5)"),
        ("s + t", "__operator::add(s, t)"),
        ("Wrap(n + 1)", "Wrap(__operator::add(n, 1))"),
        ("n.add::<Int>(1) * 2", "__operator::mul(int::add(n, 1), 2)"),
    ] {
        assert_eq!(denoted_source(source), expected, "{source}");
    }
}

#[test]
fn operator_heads_span_the_operator() {
    let source = "a <= b + -c";
    let term = krs_syntax::TermExpression::parse_source(source).unwrap();
    let columns = |range: krs_syntax::TokenRange| (range.start().column, range.end().column);
    let heads = term
        .full_provenance()
        .unwrap()
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::TermApplicationHead)
        .map(|anchor| columns(anchor.range()))
        .collect::<Vec<_>>();
    assert_eq!(heads, [(2, 4), (7, 8), (9, 10)]);
}

#[test]
fn denoted_tokens_call_the_operator_markers() {
    let term = krs_syntax::TermExpression::parse_source("Wrap(!a, b * -c < 1)").unwrap();
    let builtin: syn::Path = syn::parse_str("::renamed::builtin").unwrap();
    assert_eq!(
        term.denoted_tokens(&builtin).to_string(),
        "Wrap (:: renamed :: builtin :: __operator :: not (a) , :: renamed :: builtin :: __operator :: lt (:: renamed :: builtin :: __operator :: mul (b , :: renamed :: builtin :: __operator :: neg (c)) , 1))"
    );
}

#[test]
fn rust_only_operators_name_the_term_form() {
    for (source, expected) in [
        (
            "Wrap(a += 1)",
            "`+=` assigns, and a term has nothing to assign to; write the value `a + b`",
        ),
        ("a <<= b", "`<<=` assigns"),
        ("x as Int", "`as` converts Rust values"),
        ("Wrap(a..b)", "a range is not a term"),
    ] {
        let error = krs_syntax::TermExpression::parse_source(source).unwrap_err();
        let SyntaxErrorKind::InvalidExpressionNotation { reason } = error.kind() else {
            panic!("{source}: expected an expression-notation error, found {error}");
        };
        assert!(reason.contains(expected), "{source}: {reason}");
    }
}

#[test]
fn a_left_hand_side_rejects_operators_naming_their_calls() {
    for (source, expected) in [
        (
            "fn r(k::term![Check(n + 1)]: Term<Bool>) -> Term<Bool> { n }",
            "`+` is not a pattern: a left-hand side matches a builtin operation only as its call, `int::add(..)`, `string::concat(..)`, or `float::add(..)`",
        ),
        (
            "fn r(k::term![Check(a == b)]: Term<Bool>) -> Term<Bool> { a }",
            "`==` is not a pattern",
        ),
        (
            "fn r(k::term![Check(-n)]: Term<Bool>) -> Term<Bool> { n }",
            "`-` is not a pattern: a left-hand side matches a builtin operation only as its call, `int::sub(0, ..)` or `float::neg(..)`",
        ),
        (
            "fn r(k::term![Check(!b)]: Term<Bool>) -> Term<Bool> { b }",
            "`int::bit_not(..)` or `bool::not(..)`",
        ),
    ] {
        let error = krs_syntax::RuleItem::parse_source(source).unwrap_err();
        let SyntaxErrorKind::InvalidExpressionNotation { reason } = error.kind() else {
            panic!("{source}: expected an expression-notation error, found {error}");
        };
        assert!(reason.contains(expected), "{source}: {reason}");
    }
    let error =
        krs_syntax::RuleBlock::parse_source("for Machine; tick: { pc: p + 1 } => { pc: p };")
            .unwrap_err();
    assert!(
        error.to_string().contains("`+` is not a pattern"),
        "{error}"
    );
}

#[test]
fn operators_are_accepted_wherever_the_denoted_call_is() {
    let rule = krs_syntax::RuleItem::parse_source(
        "#[k::requires(n > 0 && (t < c || b & m != b))]
         fn r(k::term![Check(n, t, c, b, m)]: Term<Int>) -> Term<Int> { n * 2 - t }",
    )
    .unwrap();
    assert_eq!(
        denoted(rule.requires().unwrap().term().tree()),
        "bool::and_then(__operator::gt(n, 0), bool::or_else(__operator::lt(t, c), __operator::ne(__operator::bit_and(b, m), b)))"
    );
    assert_eq!(
        denoted(rule.result().unwrap().tree()),
        "__operator::sub(__operator::mul(n, 2), t)"
    );
    let sequence =
        krs_syntax::parse_k_sequence_expression("Push(x + 1), Pop()".parse().unwrap()).unwrap();
    assert_eq!(
        denoted(sequence.items()[0].tree()),
        "Push(__operator::add(x, 1))"
    );
    let or_bool = krs_syntax::TermExpression::parse_source("k::or_bool!(a < b, !c)").unwrap();
    assert!(matches!(or_bool.tree(), TermTree::OrBool { .. }));
}

#[test]
fn a_pattern_alternative_is_not_reported_as_an_operator() {
    let error = krs_syntax::RuleItem::parse_source(
        "fn r(k::term![Check(Red() | b.lt::<Int>(c))]: Term<Bool>) -> Term<Bool> { b }",
    )
    .unwrap_err();
    let SyntaxErrorKind::InvalidExpressionNotation { reason } = error.kind() else {
        panic!("expected an expression-notation error, found {error}");
    };
    assert!(
        reason.starts_with("a method call is not a pattern"),
        "{reason}"
    );
}

//! `name @ pattern` (K's `#as`, KF-029): pattern payloads are Rust patterns
//! (PAT-1), so an alias can name any subpattern of a left-hand side.

use krs_syntax::{
    KrsSyntax, MapBody, ProvenanceRole, StateTerm, SyntaxErrorKind, TermExpression, TermNode,
    TermTree,
};

fn tokens(source: &str) -> proc_macro2::TokenStream {
    krs_syntax::parse::tokens_from_source(source).unwrap()
}

fn alias(tree: &TermTree) -> (&str, &TermTree) {
    let TermTree::As { binding, pattern } = tree else {
        panic!("expected `name @ pattern`, found {tree:?}");
    };
    (Box::leak(binding.to_string().into_boxed_str()), pattern)
}

fn reason(error: &krs_syntax::SyntaxError) -> String {
    match error.kind() {
        SyntaxErrorKind::InvalidPatternAs { reason } => reason.clone(),
        other => panic!("expected an invalid-pattern-as error, found {other:?}"),
    }
}

#[test]
fn a_term_subject_aliases_a_nested_subpattern_before_its_binders() {
    let rule = krs_syntax::RuleItem::parse_source(
        "fn dup(k::term![Dup(p @ Pair(a, b))]: Term<Exp>) -> Term<Exp> { Pair(p, Pair(b, a)) }",
    )
    .unwrap();
    let pattern = &rule.parameter().pattern;
    assert_eq!(pattern.bindings(), ["p", "a", "b"]);
    let TermTree::Application(dup) = rule.subject_tree() else {
        panic!("the subject root is the matched constructor");
    };
    let argument = &dup.arguments().positional().unwrap()[0];
    let (name, inner) = alias(argument);
    assert_eq!(name, "p");
    assert!(inner.application().is_some());
    let anchors = rule.full_provenance().unwrap();
    let roles = anchors
        .iter()
        .filter(|anchor| {
            matches!(
                anchor.role(),
                ProvenanceRole::PatternAs | ProvenanceRole::PatternAsBinding
            )
        })
        .map(|anchor| (anchor.role(), anchor.ordinal()))
        .collect::<Vec<_>>();
    assert_eq!(
        roles,
        [
            (ProvenanceRole::PatternAs, 0),
            (ProvenanceRole::PatternAsBinding, 0)
        ]
    );
}

#[test]
fn pattern_payloads_keep_every_expression_form() {
    // The pattern twin of each form accepted before PAT-1 builds the same
    // nodes and symbols as the expression spelling.
    for (pattern, expression) in [
        (
            "Foo(x, y, 1, -2, true, \"s\", 1.5, -2.5, f64::NEG_INFINITY)",
            "Foo(x, y, 1, -2, true, \"s\", 1.5, -2.5, f64::NEG_INFINITY)",
        ),
        ("Foo { a, b: Bar(), .. }", "Foo { a, b: Bar() }"),
        (
            "k::fragment![Frame { pc: p, code: c }]",
            "k::fragment![Frame { pc: p, code: c }]",
        ),
        ("k::lexeme!(Name, \"x\")", "k::lexeme!(Name, \"x\")"),
        ("Nil", "Nil"),
    ] {
        let pattern_term = TermExpression::parse_pattern_tokens(tokens(pattern)).unwrap();
        let expression_term = TermExpression::parse_source(expression).unwrap();
        let kinds = |term: &TermExpression| {
            term.nodes()
                .iter()
                .map(|node| {
                    format!("{node:?}")
                        .split([' ', '('])
                        .next()
                        .unwrap()
                        .to_owned()
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(kinds(&pattern_term), kinds(&expression_term), "{pattern}");
        assert_eq!(
            pattern_term.symbols().len(),
            expression_term.symbols().len(),
            "{pattern}"
        );
        assert_eq!(
            pattern_term.root_kind(),
            expression_term.root_kind(),
            "{pattern}"
        );
    }
}

#[test]
fn state_island_patterns_alias_cells_sequence_items_and_map_entries() {
    let cells = krs_syntax::parse_cells_pattern(tokens(
        "k: KCell(Wrap(p @ Pair(a, _)), tail @ ..), env: Cell(e @ Env(_)), state @ ..",
    ))
    .unwrap();
    let StateTerm::KSequence(sequence) = cells.entries()[0].value() else {
        panic!("the k cell holds a sequence");
    };
    assert!(
        sequence.items()[0]
            .nodes()
            .iter()
            .any(|node| matches!(node, TermNode::As { binding, .. } if binding == "p"))
    );
    let StateTerm::Term(env) = cells.entries()[1].value() else {
        panic!("a leaf cell holds a term");
    };
    assert_eq!(alias(env.tree()).0, "e");

    let sequence =
        krs_syntax::parse_k_sequence_pattern(tokens("h @ Head(_) ~> rest @ ..")).unwrap();
    assert_eq!(alias(sequence.items()[0].tree()).0, "h");

    let map = krs_syntax::parse_map_pattern(tokens("k @ Key(_) -> v @ Val(_), rest @ ..")).unwrap();
    let MapBody::Items { items, .. } = map.body() else {
        panic!("a map pattern lists items");
    };
    assert_eq!(alias(items[0].key().tree()).0, "k");
    assert_eq!(alias(items[0].value().tree()).0, "v");
}

#[test]
fn readable_clauses_alias_subpatterns() {
    let block = krs_syntax::RuleBlock::parse_source(
        "for Exp; use ExpSyntax::*; dup_pair: Dup(p @ Pair(a, b)) => Pair(p, Pair(b, a));",
    )
    .unwrap();
    assert_eq!(
        block.clauses()[0].rule().parameter().pattern.bindings(),
        ["p", "a", "b"]
    );
}

#[test]
fn malformed_aliases_are_rejected() {
    for (source, expected) in [
        (
            "fn r(k::term![Dup(ref p @ Pair(a, b))]: Term<Exp>) -> Term<Exp> { p }",
            "K's #as binds the matched term itself; remove `ref`",
        ),
        (
            "fn r(k::term![Dup(mut p @ Pair(a, b))]: Term<Exp>) -> Term<Exp> { p }",
            "K binders are immutable; remove `mut`",
        ),
        (
            "fn r(k::term![Dup(p @ Pair(p, _))]: Term<Exp>) -> Term<Exp> { p }",
            "an alias cannot occur inside its own subpattern (E0416)",
        ),
        (
            "fn r(k::term![Dup(p @ ..)]: Term<Exp>) -> Term<Exp> { p }",
            "a `..` remainder binds only inside a sequence, collection or cells! pattern",
        ),
        (
            "fn r(k::term![p @ Dup(_)]: Term<Exp>) -> Term<Exp> { p }",
            "cannot alias a whole rule subject",
        ),
        (
            "fn r(k::term![Dup(a)]: Term<Exp>) -> Term<Exp> { Pair(p @ a, a) }",
            "binds only on a left-hand side (K's #as is LHS-only)",
        ),
        (
            "#[k::requires(is(p @ a))] fn r(k::term![Dup(a)]: Term<Exp>) -> Term<Exp> { a }",
            "binds only on a left-hand side (K's #as is LHS-only)",
        ),
    ] {
        let error = krs_syntax::RuleItem::parse_source(source).unwrap_err();
        assert!(reason(&error).contains(expected), "{source}: {error}");
    }
    let readable = krs_syntax::RuleBlock::parse_source(
        "for Exp; use ExpSyntax::*; bad: Dup(a) => Pair(p @ a, a);",
    )
    .unwrap_err();
    assert!(reason(&readable).contains("LHS-only"), "{readable}");
    let result =
        krs_syntax::parse_cells_expression(tokens("k: KCell(Pair(p @ a, a), ..tail)")).unwrap_err();
    assert!(reason(&result).contains("LHS-only"), "{result}");
}

#[test]
fn a_negated_float_constant_keeps_its_specific_reason() {
    let error = TermExpression::parse_pattern_tokens(tokens("F(-f64::INFINITY)")).unwrap_err();
    assert!(error.to_string().contains("f64::NEG_INFINITY"), "{error}");
}

#[test]
fn or_patterns_wait_for_their_own_form() {
    let error = TermExpression::parse_pattern_tokens(tokens("Foo(Red() | Blue())")).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("`|` alternatives are not supported"),
        "{error}"
    );
}

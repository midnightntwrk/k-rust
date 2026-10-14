//! `A | B` (K's `#Or`, KF-030): an or-pattern in a left-hand side matches
//! what any of its alternatives matches; every alternative binds the same
//! names.

use krs_syntax::{KrsSyntax, ProvenanceRole, StateTerm, SyntaxErrorKind, TermExpression, TermTree};

fn tokens(source: &str) -> proc_macro2::TokenStream {
    krs_syntax::parse::tokens_from_source(source).unwrap()
}

fn alternatives(tree: &TermTree) -> Vec<&TermTree> {
    let TermTree::Or { alternatives, .. } = tree else {
        panic!("expected `A | B`, found {tree:?}");
    };
    alternatives.iter().collect()
}

fn reason(error: &krs_syntax::SyntaxError) -> String {
    match error.kind() {
        SyntaxErrorKind::InvalidPatternOr { reason } => reason.clone(),
        other => panic!("expected an invalid-pattern-or error, found {other:?}: {error}"),
    }
}

#[test]
fn a_term_subject_nests_alternatives_below_its_root() {
    let rule = krs_syntax::RuleItem::parse_source(
        "fn code_rgb(k::term![ColorCode(Red() | Green() | Blue())]: Term<Int>) -> Term<Int> { 1 }",
    )
    .unwrap();
    assert!(rule.parameter().pattern.bindings().is_empty());
    let TermTree::Application(code) = rule.subject_tree() else {
        panic!("the subject root is the matched function");
    };
    let argument = &code.arguments().positional().unwrap()[0];
    assert_eq!(alternatives(argument).len(), 3);
    let roles = rule
        .full_provenance()
        .unwrap()
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::PatternOr)
        .map(krs_syntax::ProvenanceAnchor::ordinal)
        .collect::<Vec<_>>();
    assert_eq!(roles, [0]);
}

#[test]
fn alternatives_that_bind_the_same_names_bind_them_once() {
    let rule = krs_syntax::RuleItem::parse_source(
        "fn first(k::term![First(Pair(x, Red()) | Pair(x, Green()))]: Term<Exp>) -> Term<Exp> { x }",
    )
    .unwrap();
    assert_eq!(rule.parameter().pattern.bindings(), ["x"]);
    let nested =
        TermExpression::parse_pattern_tokens(tokens("F(p @ (A() | B()), (C() | D()))")).unwrap();
    let TermTree::Application(application) = nested.tree() else {
        panic!("the root is an application");
    };
    assert_eq!(application.arguments().positional().unwrap().len(), 2);
}

#[test]
fn readable_clauses_take_nested_and_top_level_alternatives() {
    let block = krs_syntax::RuleBlock::parse_source(
        "for Exp; use ExpSyntax::*; \
         rgb: Color(Red() | Green() | Blue()) => 1; \
         primary: Red() | Green() | Blue() => 1;",
    )
    .unwrap();
    let rgb = block.clauses()[0].rule().subject_tree();
    let TermTree::Application(color) = rgb else {
        panic!("a nested or-pattern keeps its constructor root");
    };
    assert_eq!(
        alternatives(&color.arguments().positional().unwrap()[0]).len(),
        3
    );
    let primary = block.clauses()[1].rule().subject_tree();
    assert_eq!(alternatives(primary).len(), 3);
    assert!(
        block.clauses()[1]
            .rule()
            .parameter()
            .pattern
            .bindings()
            .is_empty()
    );
}

#[test]
fn state_island_items_take_alternatives() {
    let cells = krs_syntax::parse_cells_pattern(tokens(
        "k: KCell((Red() | Green()), tail @ ..), env: Cell(Some(x) | Other(x)), state @ ..",
    ))
    .unwrap();
    let StateTerm::KSequence(sequence) = cells.entries()[0].value() else {
        panic!("the k cell holds a sequence");
    };
    assert_eq!(alternatives(sequence.items()[0].tree()).len(), 2);
    let StateTerm::Term(env) = cells.entries()[1].value() else {
        panic!("a leaf cell holds a term");
    };
    assert_eq!(alternatives(env.tree()).len(), 2);
}

#[test]
fn malformed_or_patterns_are_rejected() {
    for (source, expected) in [
        (
            "fn r(k::term![First(Pair(x, _) | Pair(_, y))]: Term<Exp>) -> Term<Exp> { x }",
            "variable `x` is not bound in all alternatives",
        ),
        (
            "fn r(k::term![Red() | Green()]: Term<Int>) -> Term<Int> { 1 }",
            "`|` cannot join whole `k::term!` subjects",
        ),
        (
            "fn r(k::term![Dup(a)]: Term<Exp>) -> Term<Exp> { Red() | Green() }",
            "`|` is a pattern alternative; for Bool disjunction use bool::or or k::or_bool!",
        ),
        (
            "#[k::requires(a | b)] fn r(k::term![Dup(a, b)]: Term<Exp>) -> Term<Exp> { a }",
            "`|` is a pattern alternative; for Bool disjunction use bool::or or k::or_bool!",
        ),
    ] {
        let error = krs_syntax::RuleItem::parse_source(source).unwrap_err();
        assert!(reason(&error).contains(expected), "{source}: {error}");
    }
    let error =
        krs_syntax::parse_cells_pattern(tokens("k: KCell(A(), tail @ .. | B())")).unwrap_err();
    assert!(
        reason(&error).contains("or-patterns combine terms, not remainders"),
        "{error}"
    );
    let error = krs_syntax::parse_cells_pattern(tokens("k: KCell(A() | tail @ ..)")).unwrap_err();
    assert!(
        reason(&error).contains("or-patterns combine terms, not remainders"),
        "{error}"
    );
    let readable = krs_syntax::RuleBlock::parse_source(
        "for Exp; use ExpSyntax::*; bad: Pair(x, _) | Pair(_, y) => 1;",
    )
    .unwrap_err();
    assert!(
        reason(&readable).contains("variable `x` is not bound in all alternatives"),
        "{readable}"
    );
    let result = krs_syntax::RuleBlock::parse_source(
        "for Exp; use ExpSyntax::*; bad: Dup(a) => Red() | Green();",
    )
    .unwrap_err();
    assert!(reason(&result).contains("pattern alternative"), "{result}");
    let records = krs_syntax::RuleBlock::parse_source(
        "for Machine; bad: { fuel: f } | { acc: f } => { fuel: f };",
    )
    .unwrap_err();
    assert!(
        reason(&records).contains("`|` cannot join whole machine records"),
        "{records}"
    );
    let inside = krs_syntax::RuleBlock::parse_source(
        "for Machine; good: { fuel: Red() | Green(), acc: a } => { fuel: Red(), acc: a };",
    );
    assert!(inside.is_ok(), "{:?}", inside.err());
}

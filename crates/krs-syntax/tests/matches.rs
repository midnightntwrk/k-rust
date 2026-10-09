//! `k::matches!(subject, pattern)` (K's `:=K`, KF-031): an object-Bool shape
//! test whose subject is a term expression and whose pattern is a Rust
//! pattern (`_`, `@`, `|`; no `if` guard). The pattern's names are local
//! binders (BIND-1).

use krs_syntax::{KrsSyntax, ProvenanceRole, SyntaxErrorKind, TermExpression, TermNode, TermTree};

fn matches_parts(tree: &TermTree) -> (&TermTree, &TermTree, Vec<String>) {
    let TermTree::Matches {
        subject,
        pattern,
        binders,
        ..
    } = tree
    else {
        panic!("expected `k::matches!`, found {tree:?}");
    };
    (
        subject,
        pattern,
        binders.iter().map(ToString::to_string).collect(),
    )
}

fn reason(error: &krs_syntax::SyntaxError) -> String {
    match error.kind() {
        SyntaxErrorKind::InvalidMatches { reason } => reason.clone(),
        other => panic!("expected an invalid-matches error, found {other:?}: {error}"),
    }
}

#[test]
fn an_expression_subject_and_a_pattern_with_wildcards_aliases_and_alternatives() {
    let term = TermExpression::parse_source(
        "k::matches!(f(e), Pair(p @ Pair(_, x), x) | Pair(p @ Unit(), x))",
    )
    .unwrap();
    let (subject, pattern, binders) = matches_parts(term.tree());
    assert!(matches!(subject, TermTree::Application(_)));
    let TermTree::Or { alternatives, .. } = pattern else {
        panic!("the pattern keeps its alternatives, found {pattern:?}");
    };
    assert_eq!(alternatives.len(), 2);
    assert_eq!(binders, ["p", "x"]);
    // The shell precedes the subject's nodes, then the pattern's, then one
    // node per wildcard.
    assert!(matches!(term.nodes()[0], TermNode::Matches(_)));
    let wildcards = term
        .nodes()
        .iter()
        .filter(|node| matches!(node, TermNode::MatchesWildcard(_)))
        .count();
    assert_eq!(wildcards, 1);
    assert!(matches!(
        term.nodes().last(),
        Some(TermNode::MatchesWildcard(_))
    ));
}

#[test]
fn a_bare_root_path_is_a_constructor_and_qualified_paths_are_not_binders() {
    let term = TermExpression::parse_source("k::matches!(e, Nil)").unwrap();
    assert!(matches_parts(term.tree()).2.is_empty());
    let term = TermExpression::parse_source("k::matches!(e, ExpSyntax::Pair(ExpSyntax::Nil, -1))")
        .unwrap();
    assert!(matches_parts(term.tree()).2.is_empty());
}

#[test]
fn matches_composes_with_bool_operations_in_a_condition() {
    let term = TermExpression::parse_source("bool::not(k::matches!(e, Pair(_, _)))").unwrap();
    let TermTree::Application(not) = term.tree() else {
        panic!("the root is bool::not");
    };
    matches_parts(&not.arguments().positional().unwrap()[0]);
}

#[test]
fn rule_provenance_numbers_shells_and_pattern_wildcards() {
    let rule = krs_syntax::RuleItem::parse_source(
        "fn is_pair(k::term![IsPair(e)]: Term<Bool>) -> Term<Bool> { k::matches!(e, Unit() | Pair(_, _)) }",
    )
    .unwrap();
    let anchors = rule.full_provenance().unwrap();
    let ordinals = |role| {
        anchors
            .iter()
            .filter(|anchor| anchor.role() == role)
            .map(krs_syntax::ProvenanceAnchor::ordinal)
            .collect::<Vec<_>>()
    };
    assert_eq!(ordinals(ProvenanceRole::Matches), [0]);
    assert_eq!(ordinals(ProvenanceRole::MatchesWildcard), [0, 1]);
    assert_eq!(ordinals(ProvenanceRole::PatternOr), [0]);
}

#[test]
fn readable_clauses_take_matches_in_conditions() {
    let block = krs_syntax::RuleBlock::parse_source(
        "for Exp; use ExpSyntax::*; \
         #[k::requires(k::matches!(e, Pair(_, _)))] is_pair: IsPair(e) => true; \
         #[k::requires(bool::not(k::matches!(e, Pair(_, _))))] not_pair: IsPair(e) => false;",
    )
    .unwrap();
    assert_eq!(block.clauses().len(), 2);
    let anchors = block.clauses()[1].provenance().unwrap();
    assert_eq!(
        anchors
            .iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::MatchesWildcard)
            .count(),
        2
    );
}

#[test]
fn a_guard_is_rejected() {
    let error =
        TermExpression::parse_source("k::matches!(e, Pair(x, _) if bool::eq(x, 1))").unwrap_err();
    assert_eq!(
        reason(&error),
        "K's :=K has no guard; conjoin a separate condition with bool::and"
    );
}

#[test]
fn std_matches_is_rejected() {
    for source in [
        "matches!(e, Pair(_, _))",
        "std::matches!(e, Pair(_, _))",
        "core::matches!(e, Pair(_, _))",
    ] {
        let error = TermExpression::parse_source(source).unwrap_err();
        assert_eq!(
            reason(&error),
            "did you mean `k::matches!`? std's matches! tests a host value",
            "{source}"
        );
    }
}

#[test]
fn matches_is_rejected_in_a_pattern() {
    let error = krs_syntax::RuleItem::parse_source(
        "fn is_pair(k::term![IsPair(k::matches!(e, Pair(_, _)))]: Term<Exp>) -> Term<Exp> { 1 }",
    )
    .unwrap_err();
    assert!(reason(&error).starts_with("`k::matches!` is a Bool test (K's :=K)"));
    let error = krs_syntax::RuleBlock::parse_source(
        "for Exp; use ExpSyntax::*; is_pair: IsPair(k::matches!(e, Pair(_, _))) => true;",
    )
    .unwrap_err();
    assert!(reason(&error).starts_with("`k::matches!` is a Bool test (K's :=K)"));
}

#[test]
fn malformed_arguments_are_rejected() {
    for source in ["k::matches!(e)", "k::matches!(e,)", "k::matches!(e, ..)"] {
        assert!(
            TermExpression::parse_source(source).is_err(),
            "{source} must be rejected"
        );
    }
}

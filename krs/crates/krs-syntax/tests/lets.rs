//! Term blocks (K's `#let`, KF-032): a Rust block in a term position holds
//! zero or more `let pattern = term;` statements and one result term. The
//! statements nest to the right, and each pattern's names are local binders
//! (BIND-1) visible in the rest of the block.

use krs_syntax::{KrsSyntax, ProvenanceRole, SyntaxErrorKind, TermExpression, TermNode, TermTree};

/// One `let` statement's pattern, sort, value, body, and binders.
fn let_parts(tree: &TermTree) -> (&TermTree, Option<String>, &TermTree, &TermTree, Vec<String>) {
    let TermTree::Let {
        pattern,
        sort,
        value,
        body,
        binders,
        ..
    } = tree
    else {
        panic!("expected a `let` statement, found {tree:?}");
    };
    (
        pattern,
        sort.as_ref().map(|sort| quote::quote!(#sort).to_string()),
        value,
        body,
        binders.iter().map(ToString::to_string).collect(),
    )
}

fn reason(error: &krs_syntax::SyntaxError) -> String {
    match error.kind() {
        SyntaxErrorKind::InvalidLet { reason } => reason.clone(),
        other => panic!("expected an invalid-let error, found {other:?}: {error}"),
    }
}

const SHAPE: &str = "a term block is `let pattern = term;`* followed by one result term (K's #let)";

#[test]
fn a_rule_body_with_let_statements_is_a_term_block() {
    let rule = krs_syntax::RuleItem::parse_source(
        "fn swap_pair(k::term![SwapPair(p)]: Term<Exp>) -> Term<Exp> { \
         let ExpSyntax::Pair(x, y) = p; ExpSyntax::Pair(y, x) }",
    )
    .unwrap();
    let (pattern, sort, value, body, binders) = let_parts(rule.result().unwrap().tree());
    assert!(matches!(pattern, TermTree::Application(_)));
    assert_eq!(sort, None);
    assert!(matches!(value, TermTree::Reference(_)));
    assert!(matches!(body, TermTree::Application(_)));
    assert_eq!(binders, ["x", "y"]);
    // The shell precedes the pattern's nodes, then the value's, then the
    // result's.
    assert!(matches!(
        rule.result().unwrap().nodes()[0],
        TermNode::Let { .. }
    ));
}

#[test]
fn a_block_nested_in_a_term_is_a_term_block() {
    let term = TermExpression::parse_source(
        "int::mul({ let n: Int = int::div(d, 160); int::mul(n, n) }, 2)",
    )
    .unwrap();
    let TermTree::Application(multiplication) = term.tree() else {
        panic!("the root is int::mul");
    };
    let block = &multiplication.arguments().positional().unwrap()[0];
    let (pattern, sort, _, _, binders) = let_parts(block);
    assert!(matches!(pattern, TermTree::Reference(_)));
    assert_eq!(sort.as_deref(), Some("Int"));
    // A bare root name binds, unlike a `k::matches!` root.
    assert_eq!(binders, ["n"]);
}

#[test]
fn two_lets_nest_to_the_right_with_their_sorts() {
    let term = TermExpression::parse_source(
        "{ let m: Int = e; let n: Int = int::add(m, 1); int::mul(n, m) }",
    )
    .unwrap();
    let (_, sort, _, body, binders) = let_parts(term.tree());
    assert_eq!(sort.as_deref(), Some("Int"));
    assert_eq!(binders, ["m"]);
    let (_, sort, _, body, binders) = let_parts(body);
    assert_eq!(sort.as_deref(), Some("Int"));
    assert_eq!(binders, ["n"]);
    assert!(matches!(body, TermTree::Application(_)));
}

#[test]
fn rule_provenance_numbers_lets_sorts_and_pattern_wildcards() {
    let rule = krs_syntax::RuleItem::parse_source(
        "fn second(k::term![Second(p)]: Term<Exp>) -> Term<Exp> { \
         let Pair(_, y) = p; let z: Exp = y; z }",
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
    assert_eq!(ordinals(ProvenanceRole::Let), [0, 1]);
    assert_eq!(ordinals(ProvenanceRole::LetSort), [1]);
    assert_eq!(ordinals(ProvenanceRole::LetWildcard), [0]);
}

#[test]
fn readable_clauses_take_blocks_in_results_and_conditions() {
    let block = krs_syntax::RuleBlock::parse_source(
        "for Exp; use ExpSyntax::*; \
         swap: Swap { e } => { let Pair(x, y) = e; Pair(y, x) }; \
         #[k::requires({ let m: Int = e; int::gt(m, 0) })] positive: Positive { e } => 1;",
    )
    .unwrap();
    assert_eq!(block.clauses().len(), 2);
    for clause in block.clauses() {
        let anchors = clause.provenance().unwrap();
        assert_eq!(
            anchors
                .iter()
                .filter(|anchor| anchor.role() == ProvenanceRole::Let)
                .count(),
            1
        );
    }
}

#[test]
fn anything_but_let_statements_and_one_result_is_rejected() {
    for source in [
        "{ let x = e; x; }",
        "{ let x = e; }",
        "{ f(e); x }",
        "{ let Pair(x, _) = e else { 0 }; x }",
        "{ let mut x = e; x }",
        "{ let ref x = e; x }",
        "{ let x; x }",
        "{ fn helper() {} x }",
        "{}",
    ] {
        let error = TermExpression::parse_source(source).unwrap_err();
        assert_eq!(reason(&error), SHAPE, "{source}");
    }
}

/// `|` and `name @ pattern` in a `let` pattern build their nodes: where a
/// `let` pattern refuses them is the position table's to say.
#[test]
fn let_patterns_read_alternatives_and_aliases() {
    let term = TermExpression::parse_source("{ let Pair(x, (y | y)) = e; x }").unwrap();
    let (pattern, ..) = let_parts(term.tree());
    let TermTree::Application(pair) = pattern else {
        panic!("expected an application, found {pattern:?}");
    };
    let krs_syntax::TermArguments::Positional(arguments) = pair.arguments() else {
        panic!("expected positional arguments");
    };
    assert!(matches!(arguments[1], TermTree::Or { .. }));
    let term = TermExpression::parse_source("{ let Pair(p @ Unit(), _) = e; p }").unwrap();
    let (pattern, _, _, _, binders) = let_parts(term.tree());
    let TermTree::Application(pair) = pattern else {
        panic!("expected an application, found {pattern:?}");
    };
    let krs_syntax::TermArguments::Positional(arguments) = pair.arguments() else {
        panic!("expected positional arguments");
    };
    assert!(matches!(arguments[0], TermTree::As { .. }));
    assert_eq!(binders, ["p"]);
}

#[test]
fn an_ascription_names_one_binder() {
    let error = TermExpression::parse_source("{ let Pair(x, y): Exp = e; x }").unwrap_err();
    assert_eq!(
        reason(&error),
        "a `let` sort ascription names one binder and a plain sort: `let x: Sort = term;`"
    );
}

/// A block in a pattern is the `let` it denotes, which the position table
/// refuses where it stands (`krs_syntax::positions`), as it judges every
/// construct.
#[test]
fn a_block_in_a_pattern_is_read_as_a_let() {
    let rule = krs_syntax::RuleItem::parse_source(
        "fn second(k::term![Second(Pair(_, { let y = 1; y }))]: Term<Exp>) -> Term<Exp> { 1 }",
    )
    .unwrap();
    assert!(
        rule.parameter()
            .pattern
            .nodes()
            .iter()
            .any(|node| matches!(node, TermNode::Let { .. }))
    );
}

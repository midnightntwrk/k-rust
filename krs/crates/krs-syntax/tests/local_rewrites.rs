//! `k::rewrite!(from => to)` (K's local `=>`, KF-011): a pattern island that
//! marks what changes in the subject of a single-body `#[k::rule]` fn, one
//! that returns `()`. The left side is a pattern; the right side is a term
//! over the subject's bindings; `()` on the right is `.K`.

use krs_syntax::{
    KrsSyntax, ProvenanceRole, StateRuleItem, SyntaxErrorKind, TermExpression, TermNode, TermTree,
};

fn reason(error: &krs_syntax::SyntaxError) -> String {
    match error.kind() {
        SyntaxErrorKind::InvalidLocalRewrite { reason } => reason.clone(),
        other => panic!("expected an invalid-local-rewrite error, found {other:?}: {error}"),
    }
}

const ASSIGN: &str = r"
#[k::rule]
fn assign(
    name: Term<Id>,
    value: Value,
    k::cells! {
        k: k::configuration::KCell(k::rewrite!(StmtSyntax::Assign(name, value) => ()), ..),
        env: k::configuration::Cell(map![name -> k::rewrite!(_ => value), ..]),
        state @ ..
    }: Machine,
) {}
";

#[test]
fn a_pattern_payload_keeps_both_sides_and_numbers_their_nodes() {
    let term = TermExpression::parse_pattern_tokens(
        "Pair(k::rewrite!(Marked(v) => v), _)".parse().unwrap(),
    )
    .unwrap();
    let TermTree::Application(pair) = term.tree() else {
        panic!("the root is the pair");
    };
    let TermTree::Rewrite { from, to, .. } = &pair.arguments().positional().unwrap()[0] else {
        panic!("the first argument is the rewrite");
    };
    assert!(matches!(**from, TermTree::Application(_)));
    assert!(matches!(to.as_deref(), Some(TermTree::Reference(_))));
    // The shell counts its sides' nodes: `Marked`, `v`, then `v`.
    let shell = term
        .nodes()
        .iter()
        .find_map(|node| match node {
            TermNode::Rewrite {
                from_nodes,
                to_nodes,
                ..
            } => Some((*from_nodes, *to_nodes)),
            _ => None,
        })
        .unwrap();
    assert_eq!(shell, (2, 1));
}

#[test]
fn unit_on_the_right_is_dot_k() {
    let term = TermExpression::parse_pattern_tokens(
        "k::rewrite!(StmtSyntax::Assign(name, value) => ())"
            .parse()
            .unwrap(),
    )
    .unwrap();
    let TermTree::Rewrite { to, .. } = term.tree() else {
        panic!("the root is the rewrite");
    };
    assert!(to.is_none());
}

#[test]
fn a_single_body_configuration_rule_binds_its_left_image() {
    let rule = StateRuleItem::parse_source(ASSIGN).unwrap();
    assert!(rule.result().is_none() && rule.result_type().is_none());
    let names = rule
        .bindings()
        .iter()
        .map(|binding| binding.name().to_string())
        .collect::<Vec<_>>();
    assert_eq!(names, ["name", "value", "state"]);
    let anchors = rule.provenance().unwrap();
    for role in [
        ProvenanceRole::RuleLocalRewrite,
        ProvenanceRole::RuleLocalRewriteFrom,
        ProvenanceRole::RuleLocalRewriteTo,
    ] {
        let ordinals = anchors
            .iter()
            .filter(|anchor| anchor.role() == role)
            .map(krs_syntax::ProvenanceAnchor::ordinal)
            .collect::<Vec<_>>();
        assert_eq!(ordinals, [0, 1], "{role:?}");
    }
    assert!(
        anchors
            .iter()
            .all(|anchor| anchor.role() != ProvenanceRole::RuleResult)
    );
}

#[test]
fn a_single_body_term_rule_has_no_result() {
    let rule = krs_syntax::RuleItem::parse_source(
        "#[k::rule] fn unmark(k::term![Pair(k::rewrite!(Marked(v) => v), _)]: Term<Exp>) {}",
    )
    .unwrap();
    assert!(rule.result().is_none() && rule.result_sort().is_none());
    assert_eq!(rule.parameter().pattern.bindings().len(), 1);
}

#[test]
fn misplaced_and_malformed_rewrites_are_rejected() {
    for (source, expected) in [
        (
            ASSIGN.replace(
                "k::rewrite!(_ => value)",
                "k::rewrite!(k::rewrite!(_ => value) => value)",
            ),
            "cannot occur inside another rewrite",
        ),
        (
            ASSIGN.replace("k::rewrite!(_ => value)", "k::rewrite!(_ => other)"),
            "`other` on the right of `k::rewrite!` is not bound",
        ),
        (
            ASSIGN.replace(
                "map![name -> k::rewrite!(_ => value), ..]",
                "map![k::rewrite!(name => value) -> value, ..]",
            ),
            "a rewrite never adds or removes an entry",
        ),
        (
            ASSIGN
                .replace(
                    "k::rewrite!(StmtSyntax::Assign(name, value) => ())",
                    "StmtSyntax::Assign(name, value)",
                )
                .replace("k::rewrite!(_ => value)", "value"),
            "a single-body rule must change something",
        ),
        (
            ASSIGN.replace(
                ") {}",
                ") -> Machine { k::cells! { env: k::configuration::Cell(map![]), ..state } }",
            ),
            "a rule with a result already states the whole after-state",
        ),
        (
            ASSIGN.replace(") {}", ") { panic!() }"),
            "has an empty body",
        ),
        (
            ASSIGN.replace("#[k::rule]", "#[k::rule]\n#[k::fresh(l: Loc)]"),
            "a single-body rule takes no",
        ),
        (
            ASSIGN.replace("k::rewrite!(_ => value)", "k::rewrite!(_ value)"),
            "`k::rewrite!` expects `from => to`",
        ),
    ] {
        let error = StateRuleItem::parse_source(&source).unwrap_err();
        assert!(
            reason(&error).contains(expected),
            "expected {expected:?}, got {error}"
        );
    }
}

#[test]
fn a_rewrite_outside_a_pattern_is_rejected() {
    let error = TermExpression::parse_source("int::add(k::rewrite!(a => b), 1)").unwrap_err();
    assert!(reason(&error).contains("marks what changes inside the subject"));
    let error = krs_syntax::RuleItem::parse_source(
        "#[k::rule] fn f(k::term![Pair(k::rewrite!(a => b), c)]: Term<Exp>) -> Term<Exp> { c }",
    )
    .unwrap_err();
    assert!(reason(&error).contains("a rule with a result"));
    let error =
        krs_syntax::RuleBlock::parse_source("for Exp; bad: Pair(k::rewrite!(a => b), c) => c;")
            .unwrap_err();
    assert!(reason(&error).contains("reference-only"));
}

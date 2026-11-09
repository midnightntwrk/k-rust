//! Every node of a sentence's terms holds a key from the sentence's parse, whatever its kind:
//! expansion reads each node's key by its kind, and a node a sentence form leaves unkeyed is an
//! internal error at expansion (`krs::expand::missing-provenance-key`), not an author's mistake.
//! A context alias keyed only its cells' heads, references and literals, none of the islands a
//! rule's subject keys (finding NT-2-17); a constant keyed no turbofish instance (NT-2-19). Each
//! form here holds one node of every kind its terms admit before expansion judges them, and the
//! forms together hold one of every kind ([`kind`] tells them apart without a fallthrough, so a
//! new kind fails to compile here until its keys are counted and a form holds one).

use std::collections::BTreeSet;

use krs_syntax::{
    ConstantItem, KrsSyntax, RuleItem, StateClaimItem, StateRuleItem, TermExpression, TermNode,
};

/// How many kinds [`kind`] tells apart.
const KINDS: usize = 18;

/// A node's kind, numbered, and the keys a node of the kind holds at least: one for its own
/// place, one per turbofish instance of an application head, one per part of a lexeme (its sort
/// and text), a sort test (its shell and sort) and an alias (its shell and name), a typed `let`'s
/// sort, and three for an anonymous value (its occurrence, sort and spelling), an `ml::exists`
/// closure (its binder's sort, the binder and the connective) and a local rewrite (the rewrite
/// and its two sides).
fn kind(node: &TermNode) -> (usize, usize) {
    match node {
        TermNode::ApplicationHead(path) => (
            0,
            1 + path
                .segments
                .last()
                .map_or(0, |segment| match &segment.arguments {
                    syn::PathArguments::AngleBracketed(arguments) => arguments.args.len(),
                    _ => 0,
                }),
        ),
        TermNode::Reference(_) => (1, 1),
        TermNode::Literal(_) => (2, 1),
        TermNode::IdToken(_) => (3, 1),
        TermNode::BytesToken(_) => (4, 1),
        TermNode::Anonymous { .. } => (5, 3),
        TermNode::OrBool(_) => (6, 1),
        TermNode::Lexeme { .. } => (7, 2),
        TermNode::SortTest { .. } => (8, 2),
        TermNode::As { .. } => (9, 2),
        TermNode::Or(_) => (10, 1),
        TermNode::Matches(_) => (11, 1),
        TermNode::MatchesWildcard(_) => (12, 1),
        TermNode::Let { sort, .. } => (13, 1 + usize::from(sort.is_some())),
        TermNode::LetWildcard(_) => (14, 1),
        TermNode::Closure { .. } => (15, 3),
        TermNode::Rewrite { .. } => (16, 3),
        TermNode::MapEntries(_) => (17, 1),
    }
}

/// The nodes of `terms` that hold fewer keys than their kind has parts, by index and kind, for
/// an assertion message; and the kinds the terms hold, into `seen`.
fn unkeyed<'a>(
    terms: impl IntoIterator<Item = &'a TermExpression>,
    seen: &mut BTreeSet<usize>,
) -> Vec<String> {
    let mut missing = Vec::new();
    for term in terms {
        for (index, node) in term.nodes().iter().enumerate() {
            let (kind, parts) = kind(node);
            seen.insert(kind);
            if term.keys().node(index).len() < parts {
                missing.push(format!("{index}: {node:?}"));
            }
        }
    }
    missing
}

/// The pattern's terms: one of each island kind, an alias, alternatives and a turbofish, in a
/// computation item and in a looked-up key.
const CELLS: &str = r#"k::cells! {
        k: k::configuration::KCell(
            site,
            Cmd::Every(k::id!("$x"), k::bytes!(b"ab"), k::lexeme!(Word, "w"), Wrap::<dyn KItemSort>(x)),
            y @ Cmd::Hold(_),
            Cmd::Go() | Cmd::Hold(_),
            -1,
            tail @ ..
        ),
        env: k::configuration::Cell(k::map![k::project!(Int, x) -> v, ..]),
        state @ ..
    }"#;

/// A built term holding the islands a result holds: a sort test, a typed `let`, a `let` with a
/// `_` in its pattern, and a `k::matches!` with a `_` in its pattern.
const BUILT: &str = "{ let z: KItem = x; let Cmd::Pair { a: _, b } = z; Cmd::Pair { a: k::is!(Int, b), b: k::matches!(x, Cmd::Hold(_)) } }";

/// Each form's name, the nodes its terms leave unkeyed, and the kinds its terms hold.
type Form = (&'static str, Vec<String>, BTreeSet<usize>);

/// Every form's terms, which together hold every kind.
fn forms() -> Vec<Form> {
    let mut forms = Vec::new();
    let mut record = |form, terms: Vec<&TermExpression>| {
        let mut seen = BTreeSet::new();
        let missing = unkeyed(terms, &mut seen);
        forms.push((form, missing, seen));
    };

    let source = format!("fn every(x: KItem, y: KItem, v: KItem, {CELLS}: Machine) {{}}");
    let alias = krs_syntax::parse_state_context_alias_item(
        krs_syntax::parse::tokens_from_source(&source).unwrap(),
        &syn::parse_str("site").unwrap(),
    )
    .unwrap();
    record(
        "context alias",
        alias
            .pattern()
            .entries()
            .iter()
            .flat_map(|entry| entry.value().terms())
            .collect(),
    );

    let source = format!(
        "#[k::requires(k::matches!(x, Cmd::Hold(_)))]\nfn every(site: KItem, x: KItem, y: KItem, v: KItem, {CELLS}: Machine) -> Machine {{ k::cells! {{ k: k::configuration::KCell({BUILT}, ..tail), ..state }} }}"
    );
    let rule = StateRuleItem::parse_source(&source).unwrap();
    let mut terms = cells_terms(&rule);
    terms.extend(rule.requires().map(krs_syntax::RuleCondition::term));
    record("cells! rule", terms);

    let constant = ConstantItem::parse_source(
        r#"const EVERY: Exp = Cmd::Every(k::id!("$x"), k::bytes!(b"ab"), k::lexeme!(Word, "w"), Wrap::<dyn KItemSort>(-1));"#,
    )
    .unwrap();
    record("constant", vec![constant.value()]);

    let source = format!(
        "#[k::requires(k::matches!(x, Cmd::Hold(_)))]\nfn every(k::term![Cmd::Every(k::id!(\"$x\"), k::bytes!(b\"ab\"), k::lexeme!(Word, \"w\"), Wrap::<dyn KItemSort>(x), y @ Cmd::Hold(_), Cmd::Go() | Cmd::Hold(_), -1, map![x -> v, rest @ ..])]: Term<Stmt>) -> Term<Stmt> {{ {BUILT} }}"
    );
    let rule = RuleItem::parse_rule_tokens(krs_syntax::parse::tokens_from_source(&source).unwrap())
        .unwrap();
    let mut terms = rule
        .parameter()
        .pattern
        .term()
        .into_iter()
        .collect::<Vec<_>>();
    terms.extend(rule.result());
    terms.extend(rule.requires().map(krs_syntax::RuleCondition::term));
    record("rule", terms);

    let source =
        "fn every(k::term![Cmd::Pair(k::rewrite!(Cmd::Go() => Cmd::Hold(1)), x)]: Term<Stmt>) {}";
    let rule = RuleItem::parse_rule_tokens(krs_syntax::parse::tokens_from_source(source).unwrap())
        .unwrap();
    record(
        "single-body rule",
        rule.parameter().pattern.term().into_iter().collect(),
    );

    let claim = StateClaimItem::parse_source(
        r#"
        #[k::requires(k::or_bool!(k::ml::exists(|n: Int| k::ml::equals(n, x)), true))]
        fn every(
            x: KItem,
            k::cells! { k: k::configuration::KCell(x, tail @ ..), state @ .. }: Machine,
        ) -> Machine {
            k::cells! { k: k::configuration::KCell(k::anonymous!(Value, "_V"), ..tail), ..state }
        }
        "#,
    )
    .unwrap();
    let mut terms = cells_terms(claim.rule());
    terms.extend(claim.rule().requires().map(krs_syntax::RuleCondition::term));
    terms.extend(claim.ensures().map(krs_syntax::ClaimEnsures::term));
    record("cells! claim", terms);
    forms
}

/// A `cells!` sentence's subject and result terms.
fn cells_terms(rule: &StateRuleItem) -> Vec<&TermExpression> {
    rule.subject()
        .entries()
        .iter()
        .chain(
            rule.result()
                .into_iter()
                .flat_map(krs_syntax::CellsExpression::entries),
        )
        .flat_map(|entry| entry.value().terms())
        .collect()
}

#[test]
fn every_form_keys_every_node_of_its_terms() {
    let missing = forms()
        .iter()
        .filter(|(_, missing, _)| !missing.is_empty())
        .map(|(form, missing, _)| format!("{form}: {missing:?}"))
        .collect::<Vec<_>>();
    assert_eq!(missing, Vec::<String>::new());
}

#[test]
fn the_forms_hold_every_node_kind() {
    let seen = forms()
        .into_iter()
        .flat_map(|(_, _, seen)| seen)
        .collect::<BTreeSet<_>>();
    assert_eq!(seen, (0..KINDS).collect::<BTreeSet<_>>());
}

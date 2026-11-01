//! Every node of a sentence's terms holds a key from the sentence's parse, whatever its kind:
//! expansion reads each node's key by its kind, and a node a sentence form leaves unkeyed is an
//! internal error at expansion (`krs::expand::missing-provenance-key`), not an author's mistake.
//! A context alias keyed only its cells' heads, references and literals, none of the islands a
//! rule's subject keys (finding NT-2-17); a constant keyed no turbofish instance (NT-2-19). Each
//! form here holds one node of every kind its terms admit before expansion judges them.

use krs_syntax::{ConstantItem, KrsSyntax, StateRuleItem, TermExpression};

/// The nodes of `terms` that hold no key, by kind and index, for an assertion message.
fn unkeyed<'a>(terms: impl IntoIterator<Item = &'a TermExpression>) -> Vec<String> {
    terms
        .into_iter()
        .flat_map(|term| {
            term.nodes()
                .iter()
                .enumerate()
                .filter(|(index, _)| term.keys().node(*index).is_empty())
                .map(|(index, node)| format!("{index}: {node:?}"))
                .collect::<Vec<_>>()
        })
        .collect()
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

#[test]
fn a_context_alias_keys_every_node_of_its_pattern() {
    let source = format!("fn every(x: KItem, y: KItem, v: KItem, {CELLS}: Machine) {{}}");
    let alias = krs_syntax::parse_state_context_alias_item(
        krs_syntax::parse::tokens_from_source(&source).unwrap(),
        &syn::parse_str("site").unwrap(),
    )
    .unwrap();
    let terms = alias
        .pattern()
        .entries()
        .iter()
        .flat_map(|entry| entry.value().terms())
        .collect::<Vec<_>>();
    assert!(terms.len() >= 5, "{terms:?}");
    assert_eq!(unkeyed(terms), Vec::<String>::new());
}

#[test]
fn a_cells_rule_keys_every_node_of_its_subject() {
    let source = format!(
        "fn every(site: KItem, x: KItem, y: KItem, v: KItem, {CELLS}: Machine) -> Machine {{ k::cells! {{ k: k::configuration::KCell(..tail), ..state }} }}"
    );
    let rule = StateRuleItem::parse_source(&source).unwrap();
    let terms = rule
        .subject()
        .entries()
        .iter()
        .flat_map(|entry| entry.value().terms())
        .collect::<Vec<_>>();
    assert_eq!(unkeyed(terms), Vec::<String>::new());
}

#[test]
fn a_constant_keys_every_node_of_its_value() {
    let constant = ConstantItem::parse_source(
        r#"const EVERY: Exp = Cmd::Every(k::id!("$x"), k::bytes!(b"ab"), k::lexeme!(Word, "w"), Wrap::<dyn KItemSort>(-1));"#,
    )
    .unwrap();
    assert_eq!(unkeyed([constant.value()]), Vec::<String>::new());
}

//! Bracket list notation (F6): each bracket level is a call of the list
//! marker, so `[a, b, ..rest]` is `__list::cons(a, __list::cons(b, rest))`
//! and `[]` is `__list::empty()`; a readable record reads a bracketed value
//! as list elements when it is not the computation cell's or a List
//! collection's.

use krs_syntax::{
    KrsSyntax, RuleBlock, RuleExtra, RuleListRest, TermArguments, TermExpression, TermTree,
};
use quote::ToTokens;

/// The tree as `head(arguments)`, with a binder or wildcard as written.
fn spelled(tree: &TermTree) -> String {
    match tree {
        TermTree::Application(application) => {
            let head = application
                .head()
                .to_token_stream()
                .to_string()
                .replace(' ', "");
            let arguments = match application.arguments() {
                TermArguments::Positional(arguments) => {
                    arguments.iter().map(spelled).collect::<Vec<_>>()
                }
                TermArguments::Named(arguments) => arguments
                    .iter()
                    .map(|argument| format!("{}: {}", argument.name(), spelled(argument.value())))
                    .collect(),
            };
            let marker = if application.is_notation() { "!" } else { "" };
            format!("{head}{marker}({})", arguments.join(", "))
        }
        TermTree::Reference(path) => path.to_token_stream().to_string(),
        TermTree::Wildcard(_) => "_".to_owned(),
        TermTree::Literal(_) => "literal".to_owned(),
        other => format!("{other:?}"),
    }
}

fn pattern(source: &str) -> String {
    spelled(
        TermExpression::parse_pattern_tokens(source.parse().unwrap())
            .unwrap()
            .tree(),
    )
}

fn expression(source: &str) -> String {
    spelled(
        TermExpression::from_expression(syn::parse_str(source).unwrap())
            .unwrap()
            .tree(),
    )
}

#[test]
fn each_bracket_level_is_one_marker_call() {
    assert_eq!(pattern("Run([])"), "Run(__list::empty!())");
    assert_eq!(
        pattern("Run([a, b])"),
        "Run(__list::cons!(a, __list::cons!(b, __list::empty!())))"
    );
    assert_eq!(
        pattern("Run([a, b, rest @ ..])"),
        "Run(__list::cons!(a, __list::cons!(b, rest)))"
    );
    assert_eq!(pattern("Run([a, ..])"), "Run(__list::cons!(a, _))");
    assert_eq!(
        pattern("Run([Pair(a, [b, ..]), ..])"),
        "Run(__list::cons!(Pair(a, __list::cons!(b, _)), _))"
    );
    assert_eq!(
        expression("Run([a, b, ..rest])"),
        "Run(__list::cons!(a, __list::cons!(b, rest)))"
    );
    assert_eq!(
        expression("[a + 1]"),
        "__list::cons!(__operator::add!(a, literal), __list::empty!())"
    );
}

#[test]
fn malformed_lists_are_rejected_with_their_reason() {
    for (source, reason) in [
        ("Run([.., x])", "`..` may only end a list"),
        ("Run([x, .., y])", "`..` may only end a list"),
        ("Run([..])", "`[..]` and `[rest @ ..]` name no element"),
        (
            "Run([rest @ ..])",
            "`[..]` and `[rest @ ..]` name no element",
        ),
    ] {
        let error = TermExpression::parse_pattern_tokens(source.parse().unwrap())
            .unwrap_err()
            .to_string();
        assert!(error.contains(reason), "{source}: {error}");
    }
    for (source, reason) in [
        ("Run([..rest, x])", "`..` may only end a list"),
        ("Run([..rest])", "it is the list `rest` itself"),
        (
            "Run([x, ..])",
            "an anonymous `..` keeps the rest only in a readable record cell",
        ),
        ("Run([x, ..=rest])", "a list's rest is written `..rest`"),
    ] {
        let error = TermExpression::from_expression(syn::parse_str(source).unwrap())
            .unwrap_err()
            .to_string();
        assert!(error.contains(reason), "{source}: {error}");
    }
}

fn read(source: &str) -> krs_syntax::RuleClause {
    RuleBlock::parse_source(&format!("for Machine; use Op::*; {source}"))
        .unwrap()
        .clauses()[0]
        .clone()
}

/// The list extras of a clause: cell, element count, pattern rest, and
/// result rest.
fn lists(clause: &krs_syntax::RuleClause) -> Vec<(String, usize, &'static str, &'static str)> {
    fn rest<T>(rest: &RuleListRest<T>) -> &'static str {
        match rest {
            RuleListRest::Exact => "exact",
            RuleListRest::Shared(_) => "shared",
            RuleListRest::Named(_) => "named",
        }
    }
    clause
        .extras()
        .iter()
        .filter_map(|extra| match extra {
            RuleExtra::RewriteList {
                cell,
                before,
                after,
                ..
            } => Some((
                cell.to_string(),
                before.items().len(),
                rest(before.rest()),
                after.as_ref().map_or("read", |after| rest(after.rest())),
            )),
            _ => None,
        })
        .collect()
}

#[test]
fn a_record_reads_one_bracketed_value_as_the_head_and_the_others_as_lists() {
    // `k` is the head whatever the order; the stack is a list.
    for source in [
        "add: { k: [Add(), ..], stack: [a, b, ..] } => { k: [..], stack: [Chop(a + b), ..] };",
        "add: { stack: [a, b, ..], k: [Add(), ..] } => { k: [..], stack: [Chop(a + b), ..] };",
    ] {
        let clause = read(source);
        assert_eq!(clause.computation_cell().unwrap(), "k", "{source}");
        assert_eq!(
            lists(&clause),
            [("stack".to_owned(), 2, "shared", "shared")],
            "{source}"
        );
        assert_eq!(clause.bindings(), ["a", "b"]);
        clause.provenance().unwrap();
    }
    // Without `k`, the first value is read as the head; the collector moves
    // it to the cell the configuration declares.
    let clause = read("two: { k1: [A(), ..], k2: [B(), ..] } => { k1: [..], k2: [..] };");
    assert_eq!(clause.computation_cell().unwrap(), "k1");
    assert_eq!(lists(&clause), [("k2".to_owned(), 1, "shared", "shared")]);
}

#[test]
fn a_named_rest_or_a_term_result_reads_only_as_a_list() {
    let clause = read("swap: { stack: [a, b, rest @ ..] } => { stack: [b, a, ..rest] };");
    assert!(clause.computation_cell().is_none());
    assert_eq!(lists(&clause), [("stack".to_owned(), 2, "named", "named")]);
    assert_eq!(clause.bindings(), ["a", "b", "rest"]);
    clause.provenance().unwrap();

    let clause = read("pop: { stack: [_, rest @ ..] } => { stack: rest };");
    assert_eq!(lists(&clause), [("stack".to_owned(), 1, "named", "named")]);

    let clause = read("pair: { k: [Pair(), ..], stack: [a, b] } => { k: [..], stack: [] };");
    assert_eq!(lists(&clause), [("stack".to_owned(), 2, "exact", "exact")]);

    // A cell matched by one term is written with list notation as a term.
    let clause = read("push: { k: [Push(v), ..], stack: s } => { k: [..], stack: [v, ..s] };");
    assert!(lists(&clause).is_empty());
}

#[test]
fn a_list_cells_rest_is_one_rest_on_both_sides() {
    for (source, reason) in [
        (
            "a: { k: [A(), ..], stack: [x, ..] } => { k: [..], stack: [x] };",
            "the pattern's `..` keeps the rest of the list",
        ),
        (
            "a: { k: [A(), ..], stack: [x, rest @ ..] } => { k: [..], stack: [x, ..] };",
            "the pattern ends in no anonymous `..`",
        ),
        (
            "a: { k: [A(), ..], stack: [.., x] } => { k: [..] };",
            "`..` may only end a list",
        ),
    ] {
        let error = RuleBlock::parse_source(&format!("for Machine; use Op::*; {source}"))
            .err()
            .unwrap_or_else(|| panic!("{source} parsed"))
            .to_string();
        assert!(error.contains(reason), "{source}: {error}");
    }
}

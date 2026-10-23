//! Bracket list notation (F6): each bracket level is a call of the list
//! marker, so `[a, b, ..rest]` is `__list::cons(a, __list::cons(b, rest))`,
//! `[..rest, z]` is `__list::snoc(rest, z)`, and `[]` is `__list::empty()`;
//! a bracket holds at most one rest, anywhere. A readable record reads a
//! bracketed value as list elements when it is not the computation cell's or
//! a List collection's.

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

/// Once the rest leads, each level takes the last element: the front is
/// consed onto the back, which is snoc'ed onto the rest.
#[test]
fn a_rest_anywhere_takes_the_back_elements_from_the_end() {
    assert_eq!(pattern("Run([.., z])"), "Run(__list::snoc!(_, z))");
    assert_eq!(
        pattern("Run([rest @ .., z])"),
        "Run(__list::snoc!(rest, z))"
    );
    assert_eq!(
        pattern("Run([a, mid @ .., y, z])"),
        "Run(__list::cons!(a, __list::snoc!(__list::snoc!(mid, y), z)))"
    );
    assert_eq!(
        pattern("Run([a, .., z])"),
        "Run(__list::cons!(a, __list::snoc!(_, z)))"
    );
    assert_eq!(
        expression("Run([..rest, z])"),
        "Run(__list::snoc!(rest, z))"
    );
    assert_eq!(
        expression("Run([a, ..mid, y, z])"),
        "Run(__list::cons!(a, __list::snoc!(__list::snoc!(mid, y), z)))"
    );
    assert_eq!(
        expression("[..log, [x, ..xs]]"),
        "__list::snoc!(log, __list::cons!(x, xs))"
    );
}

/// Each level's marker spans from its own element to the end of the
/// brackets, so no two levels of one bracket share a span.
#[test]
fn each_level_is_anchored_at_its_own_element() {
    let term =
        TermExpression::from_expression(syn::parse_str("[a, ..mid, y, z]").unwrap()).unwrap();
    let mut starts = Vec::new();
    let mut pending = vec![term.tree()];
    while let Some(tree) = pending.pop() {
        if let TermTree::Application(application) = tree {
            if application.is_notation() {
                starts.push(application.head().segments[0].ident.span().start().column);
            }
            if let TermArguments::Positional(arguments) = application.arguments() {
                pending.extend(arguments);
            }
        }
    }
    starts.sort_unstable();
    // `a`, `y`, and `z` start the three levels.
    assert_eq!(starts, [1, 11, 14]);
}

#[test]
fn malformed_lists_are_rejected_with_their_reason() {
    for (source, reason) in [
        ("Run([.., x, ..])", "a list holds at most one rest `..`"),
        (
            "Run([a, rest @ .., b, ..])",
            "a list holds at most one rest `..`",
        ),
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
        (
            "Run([..xs, ..ys])",
            "join two lists with `list::concat(xs, ys)`",
        ),
        (
            "Run([a, ..xs, b, ..ys])",
            "a list holds at most one rest `..`",
        ),
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

/// The list extras of a clause: cell, front element count, pattern rest,
/// and result rest.
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

/// A rest may stand anywhere: the elements after it are the list's back.
#[test]
fn a_record_list_has_a_front_and_a_back() {
    let back = |clause: &krs_syntax::RuleClause| -> Vec<(usize, usize)> {
        clause
            .extras()
            .iter()
            .filter_map(|extra| match extra {
                RuleExtra::RewriteList { before, after, .. } => Some((
                    before.back().len(),
                    after.as_ref().map_or(0, |after| after.back().len()),
                )),
                _ => None,
            })
            .collect()
    };
    let clause = read(
        "last: { k: [Last(), ..], queue: [.., v], acc: _ } => { k: [..], queue: [..], acc: v };",
    );
    assert_eq!(
        lists(&clause),
        [("queue".to_owned(), 0, "shared", "shared")]
    );
    assert_eq!(back(&clause), [(1, 0)]);
    clause.provenance().unwrap();

    let clause =
        read("swap: { k: [Swap(), ..], queue: [a, .., z] } => { k: [..], queue: [z, .., a] };");
    assert_eq!(
        lists(&clause),
        [("queue".to_owned(), 1, "shared", "shared")]
    );
    assert_eq!(back(&clause), [(1, 1)]);
    assert_eq!(clause.bindings(), ["a", "z"]);

    let clause = read(
        "rot: { k: [Rot(), ..], queue: [a, mid @ .., y, z] } => { k: [..], queue: [y, z, ..mid, a] };",
    );
    assert_eq!(lists(&clause), [("queue".to_owned(), 1, "named", "named")]);
    assert_eq!(back(&clause), [(2, 1)]);
    assert_eq!(clause.bindings(), ["a", "mid", "y", "z"]);
    clause.provenance().unwrap();

    let clause =
        read("log: { k: [Log(e), ..], logs: [first, ..] } => { k: [..], logs: [first, .., e] };");
    assert_eq!(back(&clause), [(0, 1)]);
}

/// A value that reads as list elements and as a List collection's
/// instances, but is not the computation cell, is read as elements and
/// carries its List reading beside it for the collector.
#[test]
fn elements_that_read_as_instances_carry_the_instances_beside_them() {
    for source in [
        "pop: { k: [Pop(), ..], job: [.., Job { payload: p }] } => { k: [p, ..], job: [..] };",
        "drop: { k: [Drop(), ..], job: [first @ Job { payload: p }, ..] } => { k: [p, ..], job: [..] };",
    ] {
        let clause = read(source);
        assert_eq!(clause.computation_cell().unwrap(), "k", "{source}");
        assert_eq!(lists(&clause).len(), 1, "{source}");
        assert_eq!(
            clause.bracket_alternative().unwrap().cell().to_string(),
            "job",
            "{source}"
        );
        clause.provenance().unwrap();
    }
    // Instances whose children are not all `name: value` read only as
    // instances or only as elements.
    let clause = read(
        "pop: { k: [Pop(), ..], job: [.., Job { payload, .. }] } => { k: [payload, ..], job: [..] };",
    );
    assert_eq!(lists(&clause).len(), 1);
    assert!(clause.bracket_alternative().is_none());
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
            "the pattern holds no anonymous `..`",
        ),
        (
            "a: { k: [A(), ..], stack: [.., x, ..] } => { k: [..] };",
            "a list holds at most one rest `..`",
        ),
        (
            "a: { k: [A(), ..], stack: [x, rest @ ..] } => { k: [..], stack: [..rest, x, ..more] };",
            "a list holds at most one rest `..`",
        ),
    ] {
        let error = RuleBlock::parse_source(&format!("for Machine; use Op::*; {source}"))
            .err()
            .unwrap_or_else(|| panic!("{source} parsed"))
            .to_string();
        assert!(error.contains(reason), "{source}: {error}");
    }
}

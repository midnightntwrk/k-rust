//! Readable computation-cell patterns: a front prefix of several items, a
//! whole (exact) cell, and a cell the rule only reads.

use krs_syntax::{KrsSyntax, RuleBlock, RuleHeadResult};

fn block(clauses: &str) -> RuleBlock {
    RuleBlock::parse_source(&format!("for Machine; use Op::*; {clauses}")).unwrap()
}

fn error(clause: &str) -> String {
    RuleBlock::parse_source(&format!("for Machine; use Op::*; {clause}"))
        .err()
        .unwrap_or_else(|| panic!("{clause} parsed"))
        .to_string()
}

#[test]
fn a_binder_repeated_across_cells_is_one_binder() {
    let block = block("a: { k: [Run { n }, ..], left: n } => { k: [..], left: 0 };");
    assert_eq!(block.clauses()[0].bindings(), ["n"]);
}

#[test]
fn a_prefix_matches_several_items_and_keeps_the_rest() {
    let block = block(
        "store: { k: [v, Store { addr: a }, ..], acc: s } => { k: [..], acc: int::add(s, v) } where v: Int;",
    );
    let clause = &block.clauses()[0];
    let head = clause.head().unwrap();
    assert!(head.subject());
    assert!(!head.exact());
    assert_eq!(head.following().len(), 1);
    assert_eq!(head.following()[0].pattern().bindings(), ["a"]);
    assert_eq!(clause.bindings(), ["v", "a", "s"]);
    assert!(matches!(
        clause.head_result(),
        Some(RuleHeadResult::Erase(_))
    ));
    // Every left-side anchor of the second item is numbered after the first.
    clause.provenance().unwrap();
}

#[test]
fn an_exact_pattern_names_the_whole_cell() {
    let block = block(
        "start: { k: [Run { n }], left: _ } => { k: [Op::Boundary], left: n };
         done: { k: [Abort { code: c }, _ignored], acc: _ } => { k: [], acc: c };
         idle: { k: [] } => { k: [Op::Boundary] };",
    );
    let [start, done, idle] = block.clauses() else {
        panic!("three clauses");
    };
    assert!(start.head().unwrap().exact());
    assert!(matches!(
        start.head_result(),
        Some(RuleHeadResult::Replace(_))
    ));
    assert_eq!(done.head().unwrap().following().len(), 1);
    assert!(matches!(done.head_result(), Some(RuleHeadResult::Erase(_))));
    let empty = idle.head().unwrap();
    assert!(empty.exact() && !empty.subject() && empty.following().is_empty());
    assert!(idle.bindings().is_empty());
    for clause in block.clauses() {
        clause.provenance().unwrap();
    }
}

#[test]
fn a_computation_cell_the_result_leaves_out_is_read_only() {
    let block = block("tick: { k: [Op::Boundary, ..], left: n } => { left: int::sub(n, 1) };");
    let clause = &block.clauses()[0];
    assert_eq!(clause.computation_cell().unwrap(), "k");
    assert!(clause.head().is_some());
    assert!(clause.head_result().is_none());
}

#[test]
fn a_binder_repeated_across_items_is_one_nonlinear_binding() {
    let block = block("same: { k: [Run { n }, Load { addr: n }, ..] } => { k: [..] };");
    assert_eq!(block.clauses()[0].bindings(), ["n"]);
}

/// `k: [.., x]` and `k: [x, .., y]` read as list elements, which a `List`
/// cell may hold; the collector, which knows `k` is the computation cell,
/// rejects an element after its rest.
#[test]
fn a_k_value_with_a_back_reads_as_list_elements() {
    for source in [
        "a: { k: [.., x] } => { k: [..] };",
        "a: { k: [x, .., y] } => { k: [..] };",
    ] {
        let block = block(source);
        let clause = &block.clauses()[0];
        assert!(clause.computation_cell().is_none(), "{source}");
        assert!(
            matches!(clause.extras(), [krs_syntax::RuleExtra::RewriteList { before, .. }] if before.back().len() == 1),
            "{source}"
        );
    }
}

#[test]
fn unsupported_shapes_are_rejected_with_their_reason() {
    for (clause, reason) in [
        (
            "a: { k: [..], acc: 0 } => { k: [Op::Boundary, ..] };",
            "`[..]` matches any computation",
        ),
        (
            "a: { k: [Run { n }, ..] } => { k: [Op::Boundary] };",
            "so the result ends in `..` too",
        ),
        (
            "a: { k: [Run { n }] } => { k: [Op::Boundary, ..] };",
            "there is no rest for the result's `..` to keep",
        ),
        (
            "a: { k: [Run { n }, ..] } => { k: 3 };",
            "the computation cell's result is a bracketed sequence",
        ),
    ] {
        let message = error(clause);
        assert!(message.contains(reason), "{clause}: {message}");
    }
}

#[test]
fn an_item_may_be_an_alias_or_alternatives() {
    for (clause, bindings) in [
        (
            "a: { k: [op @ (Push() | Pop()), ..] } => { k: [Wrap(op), ..] };",
            &["op"][..],
        ),
        (
            "a: { k: [x, op @ (Push() | Pop()), ..] } => { k: [op, ..] };",
            &["x", "op"][..],
        ),
        ("a: { k: [Push() | Pop(), ..] } => { k: [..] };", &[][..]),
        (
            "a: { k: [Run { n }, ..], acc: v @ Pair(_, _) } => { k: [v, ..] };",
            &["n", "v"][..],
        ),
    ] {
        assert_eq!(block(clause).clauses()[0].bindings(), bindings, "{clause}");
    }
}

/// The fields of a bit template in the first item name values in every
/// result term: the computation cell's items and the other cells' values.
#[test]
fn a_head_item_template_s_fields_reach_every_result_term() {
    let block = block(
        r#"low: { k: [k::bits!("0000 01xx"), ..], acc } => { k: [x, ..], acc: int::add(acc, x) };"#,
    );
    let clause = &block.clauses()[0];
    let Some(RuleHeadResult::Replace(item)) = clause.head_result() else {
        panic!("one result item");
    };
    assert_eq!(
        item.spelling(),
        "__krs_bits_0 . bit_range :: < Int > (0 , 2)"
    );
    let [
        krs_syntax::RuleExtra::RewriteCell {
            after: Some(after), ..
        },
    ] = clause.extras()
    else {
        panic!("one rewritten cell");
    };
    assert_eq!(
        after.spelling(),
        "int :: add (acc , __krs_bits_0 . bit_range :: < Int > (0 , 2))"
    );
    assert_eq!(clause.bindings(), ["__krs_bits_0", "acc"]);
}

#[test]
fn a_head_item_template_s_field_is_not_rebound_or_read_in_state() {
    for (clause, reason) in [
        (
            r#"a: { k: [k::bits!("01xx"), ..], acc: x } => { k: [..] };"#,
            "`x` is a field of the sentence's bit template and cannot be bound again here",
        ),
        (
            r#"a: { k: [k::bits!("01xx"), ..], mark: None } => { k: [..], mark: Some(x) };"#,
            "it occurs in the result of the optional or collection cell `mark`",
        ),
    ] {
        let message = error(clause);
        assert!(message.contains(reason), "{clause}: {message}");
    }
}

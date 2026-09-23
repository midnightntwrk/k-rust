//! OT-01: the `ceil_free` shortcut of `definedness::ceil_term_recursive` against the walk that
//! never reads the attribute (`ceil_term_without_attribute`), over terms of every `TermKind`
//! built by the public constructors (`lean_bridge::generators::term_with_ground_keys`).
//!
//! The property is `ceilFree_sound` of `lean/KRust/TermAttributes.lean` applied to the Rust: a
//! term whose stored attribute is true has no definedness obligation, so `ceil_term` with the
//! shortcut returns the same list as the full walk for every term, not only for `ceil_free`
//! ones. The definition declares the generator's sorts with `Int` a subsort of `KItem`, so that
//! the matcher the full walk falls back on for keys with different headers has a subsort
//! relation to consult.

use std::collections::BTreeMap;

use k_rust_kore::kore::parser::parse_definition;
use proptest::{
    strategy::{Strategy, ValueTree},
    test_runner::{Config, RngAlgorithm, TestRng, TestRunner},
};

use super::lean_bridge::generators::term_with_ground_keys;
use crate::{
    definedness::{ceil_term, ceil_term_without_attribute},
    definition::BackendDefinition,
    term::{Term, TermKind},
};

const CASES: usize = 4096;

fn definition() -> BackendDefinition {
    let source = r#"[]
        module MAIN
            sort SortKItem{} []
            sort SortInt{} [hasDomainValues{}()]
            sort SortS{} []
            symbol inj{From, To}(From) : To [sortInjection{}()]
            axiom{R} \exists{R}(Val:SortKItem{}, \equals{SortKItem{}, R}(Val:SortKItem{},
                inj{SortInt{}, SortKItem{}}(From:SortInt{}))) [subsort{SortInt{}, SortKItem{}}()]
        endmodule []"#;
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn kind_name(term: &Term) -> &'static str {
    match term.kind() {
        TermKind::And(..) => "and",
        TermKind::Application { .. } => "application",
        TermKind::DomainValue { .. } => "domain value",
        TermKind::Variable(_) => "variable",
        TermKind::Injection { .. } => "injection",
        TermKind::Map { .. } => "map",
        TermKind::List { .. } => "list",
        TermKind::Set { .. } => "set",
    }
}

/// Keys or elements of a map or set without a rest, when there are at least two.
fn closed_keys(term: &Term) -> Option<usize> {
    match term.kind() {
        TermKind::Map {
            entries,
            rest: None,
            ..
        } if entries.len() > 1 => Some(entries.len()),
        TermKind::Set {
            elements,
            rest: None,
            ..
        } if elements.len() > 1 => Some(elements.len()),
        _ => None,
    }
}

#[test]
fn ceil_free_shortcut_returns_the_full_walk() {
    let definition = definition();
    let strategy = term_with_ground_keys();
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    // (kind, ceil_free) -> cases, and closed collections of several keys by ceil_free.
    let mut kinds = BTreeMap::<(&str, bool), usize>::new();
    let mut closed = [0usize; 2];
    for case in 0..CASES {
        let term = strategy.new_tree(&mut runner).expect("a case").current();
        let full = ceil_term_without_attribute(&definition, &term);
        let free = term.attributes().ceil_free();
        if free {
            assert!(
                full.is_empty(),
                "case {case}: a ceil_free term has definedness obligations {full:?}: {term:?}"
            );
        }
        assert_eq!(
            ceil_term(&definition, &term),
            full,
            "case {case}: the shortcut changed the obligations of {term:?}"
        );
        *kinds.entry((kind_name(&term), free)).or_default() += 1;
        if closed_keys(&term).is_some() {
            closed[usize::from(free)] += 1;
        }
    }
    eprintln!(
        "ceil_free by root kind: {kinds:?}; closed collections of several keys [not free, free]: {closed:?}"
    );
    for kind in [
        "and",
        "application",
        "domain value",
        "variable",
        "injection",
        "map",
        "list",
        "set",
    ] {
        assert!(
            kinds.contains_key(&(kind, true)),
            "no ceil_free root of kind {kind}"
        );
        if kind != "domain value" {
            assert!(
                kinds.contains_key(&(kind, false)),
                "no root of kind {kind} without ceil_free"
            );
        }
    }
    assert!(
        closed.iter().all(|&count| count > 0),
        "the generator should reach closed maps and sets of several keys with and without ceil_free"
    );
}

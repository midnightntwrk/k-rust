//! Compare the `ceil_free` shortcut of `definedness::ceil_term_recursive` against the walk that
//! never reads the attribute (`ceil_term_without_attribute`), over terms of every `TermKind`
//! built by the public constructors (`lean_bridge::generators::term_with_ground_keys`).
//!
//! The property is `ceilFree_sound` of `lean/KRust/TermAttributes.lean` applied to the Rust: a
//! term whose stored attribute is true has no definedness obligation, so `ceil_term` with the
//! shortcut returns the same list as the full walk for every term, not only for `ceil_free`
//! ones. The definition declares the generator's sorts with `Int` a subsort of `KItem`, so that
//! the matcher the full walk falls back on for keys with different headers has a subsort
//! relation to consult.
//!
//! Separately, an all-pair structural-equality oracle checks that syntactic collection
//! collisions at any depth exclude both positive shape flags before simplification.

use std::{collections::BTreeMap, sync::Arc};

use k_rust_kore::kore::parser::parse_definition;
use proptest::{
    strategy::{Strategy, ValueTree},
    test_runner::{Config, RngAlgorithm, TestRng, TestRunner},
};

use super::lean_bridge::generators::term_with_ground_keys;
use crate::{
    definedness::{ceil_term, ceil_term_without_attribute},
    definition::BackendDefinition,
    term::{CollectionSymbols, ListDefinition, MapDefinition, Sort, Symbol, Term, TermKind},
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

#[derive(Debug, Default)]
struct CollisionCoverage {
    root_sets: usize,
    root_maps: usize,
    inherited: usize,
    concrete_controls: usize,
}

impl CollisionCoverage {
    fn assert_covered(&self) {
        eprintln!("hereditary collection collision coverage: {self:?}");
        assert!(self.root_sets > 0, "no repeated-element set root");
        assert!(self.root_maps > 0, "no repeated-key map root");
        assert!(self.inherited > 0, "no inherited collection collision");
        assert!(
            self.concrete_controls > 0,
            "no collision-free concrete control"
        );
    }
}

/// An independent all-pair oracle: structural equality detects collisions regardless of order,
/// and every child is visited even when the root or an earlier child already has a collision.
fn check_hereditary_collisions(term: &Term, case: &str, coverage: &mut CollisionCoverage) -> bool {
    let mut root_collision = false;
    let mut child_collision = false;
    match term.kind() {
        TermKind::And(left, right) => {
            child_collision |= check_hereditary_collisions(left, case, coverage);
            child_collision |= check_hereditary_collisions(right, case, coverage);
        }
        TermKind::Application { arguments, .. } => {
            for child in arguments {
                child_collision |= check_hereditary_collisions(child, case, coverage);
            }
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        TermKind::Injection { term, .. } => {
            child_collision |= check_hereditary_collisions(term, case, coverage);
        }
        TermKind::Map { entries, rest, .. } => {
            for (index, (key, value)) in entries.iter().enumerate() {
                for (other_key, _) in &entries[index + 1..] {
                    root_collision |= key == other_key;
                }
                child_collision |= check_hereditary_collisions(key, case, coverage);
                child_collision |= check_hereditary_collisions(value, case, coverage);
            }
            if let Some(rest) = rest {
                child_collision |= check_hereditary_collisions(rest, case, coverage);
            }
            coverage.root_maps += usize::from(root_collision);
        }
        TermKind::List { heads, rest, .. } => {
            for head in heads {
                child_collision |= check_hereditary_collisions(head, case, coverage);
            }
            if let Some((middle, tails)) = rest {
                child_collision |= check_hereditary_collisions(middle, case, coverage);
                for tail in tails {
                    child_collision |= check_hereditary_collisions(tail, case, coverage);
                }
            }
        }
        TermKind::Set { elements, rest, .. } => {
            for (index, element) in elements.iter().enumerate() {
                for other in &elements[index + 1..] {
                    root_collision |= element == other;
                }
                child_collision |= check_hereditary_collisions(element, case, coverage);
            }
            if let Some(rest) = rest {
                child_collision |= check_hereditary_collisions(rest, case, coverage);
            }
            coverage.root_sets += usize::from(root_collision);
        }
    }
    let collision = root_collision || child_collision;
    if collision {
        coverage.inherited += usize::from(!root_collision);
        assert!(
            !term.attributes().constructor_like,
            "{case}: a syntactic collection collision must exclude constructor likeness: {term:?}"
        );
        assert!(
            !term.concrete_after_normalization(),
            "{case}: a syntactic collection collision must exclude concrete shape: {term:?}"
        );
    } else if matches!(term.kind(), TermKind::Map { .. } | TermKind::Set { .. }) {
        coverage.concrete_controls += usize::from(term.concrete_after_normalization());
    }
    collision
}

#[test]
fn forced_collection_collisions_have_negative_shape_flags() {
    let symbols = |prefix: &str| CollectionSymbols {
        unit: format!("{prefix}unit").into(),
        element: format!("{prefix}element").into(),
        concat: format!("{prefix}concat").into(),
    };
    let map_definition = Arc::new(MapDefinition {
        symbols: symbols("Map"),
        key_sort: "SortInt".into(),
        value_sort: "SortInt".into(),
        map_sort: "SortMap".into(),
    });
    let set_definition = Arc::new(ListDefinition {
        symbols: symbols("Set"),
        element_sort: "SortInt".into(),
        list_sort: "SortSet".into(),
    });
    let int = |value: &str| Term::domain_value(Sort::simple("SortInt"), value);
    let set = |elements| Term::set(set_definition.clone(), elements, None);
    let map = |entries| Term::map(map_definition.clone(), entries, None);
    let wrap = |term: Term| {
        Term::application(
            Arc::new(Symbol::constructor(
                "wrap",
                vec![term.sort()],
                Sort::simple("SortS"),
            )),
            vec![],
            vec![term],
        )
    };
    let repeated_set = set(vec![int("0"), int("0")]);
    let repeated_map = map(vec![(int("0"), int("0")), (int("0"), int("0"))]);
    let different_values = map(vec![(int("0"), int("0")), (int("0"), int("1"))]);
    let mut coverage = CollisionCoverage::default();
    for (case, term) in [
        ("repeated set element", repeated_set.clone()),
        ("repeated map key and value", repeated_map.clone()),
        ("repeated map key with different values", different_values),
        ("inherited repeated set element", wrap(repeated_set)),
        ("inherited repeated map key", wrap(repeated_map)),
    ] {
        assert!(check_hereditary_collisions(&term, case, &mut coverage));
    }
    for (case, term) in [
        ("empty set", set(vec![])),
        ("singleton set", set(vec![int("0")])),
        ("distinct set elements", set(vec![int("0"), int("1")])),
        ("empty map", map(vec![])),
        ("singleton map", map(vec![(int("0"), int("0"))])),
        (
            "distinct map keys",
            map(vec![(int("0"), int("0")), (int("1"), int("0"))]),
        ),
    ] {
        assert!(!check_hereditary_collisions(&term, case, &mut coverage));
        assert!(term.concrete_after_normalization(), "{case}: {term:?}");
    }
    assert_eq!(coverage.root_sets, 2);
    assert_eq!(coverage.root_maps, 3);
    assert_eq!(coverage.inherited, 2);
    assert_eq!(coverage.concrete_controls, 6);
    coverage.assert_covered();
}

#[test]
fn generated_collection_collisions_have_negative_shape_flags() {
    let strategy = term_with_ground_keys();
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let mut coverage = CollisionCoverage::default();
    for case in 0..CASES {
        let term = strategy.new_tree(&mut runner).expect("a case").current();
        check_hereditary_collisions(&term, &format!("generated case {case}"), &mut coverage);
    }
    coverage.assert_covered();
}

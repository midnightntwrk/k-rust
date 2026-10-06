//! Compare the `ceil_free` shortcut of the definedness walk (`definedness::ceil_term`) against the
//! walk that never reads the attribute (`ceil_term_without_attribute`), over terms of every `TermKind`
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
    term::{
        CollectionSymbols, HeadRole, ListDefinition, MapDefinition, Sort, Symbol, Term, TermKind,
    },
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

struct CollisionShape {
    collision: bool,
    ground_constructor_tree: bool,
}

/// An independent all-pair oracle: structural equality detects collisions regardless of order,
/// and every child is visited even when the root or an earlier child already has a collision.
/// Ground constructor trees are recognized from kinds and free heads, without reading shape
/// flags, so clearing either positive flag on a collision-free collection also fails this check.
fn check_hereditary_collisions(
    term: &Term,
    case: &str,
    coverage: &mut CollisionCoverage,
) -> CollisionShape {
    let mut root_collision = false;
    let mut child_collision = false;
    let mut ground_constructor_tree = true;
    let mut visit = |child: &Term| {
        let shape = check_hereditary_collisions(child, case, coverage);
        child_collision |= shape.collision;
        ground_constructor_tree &= shape.ground_constructor_tree;
    };
    match term.kind() {
        TermKind::And(left, right) => {
            visit(left);
            visit(right);
            ground_constructor_tree = false;
        }
        TermKind::Application {
            symbol, arguments, ..
        } => {
            for child in arguments {
                visit(child);
            }
            ground_constructor_tree &= symbol.attributes.head_role() == HeadRole::FreeConstructor;
        }
        TermKind::DomainValue { .. } => {}
        TermKind::Variable(_) => ground_constructor_tree = false,
        TermKind::Injection { term, .. } => visit(term),
        TermKind::Map { entries, rest, .. } => {
            for (index, (key, value)) in entries.iter().enumerate() {
                for (other_key, _) in &entries[index + 1..] {
                    root_collision |= key == other_key;
                }
                visit(key);
                visit(value);
            }
            if let Some(rest) = rest {
                visit(rest);
            }
            coverage.root_maps += usize::from(root_collision);
        }
        TermKind::List { heads, rest, .. } => {
            for head in heads {
                visit(head);
            }
            if let Some((middle, tails)) = rest {
                visit(middle);
                for tail in tails {
                    visit(tail);
                }
            }
        }
        TermKind::Set { elements, rest, .. } => {
            for (index, element) in elements.iter().enumerate() {
                for other in &elements[index + 1..] {
                    root_collision |= element == other;
                }
                visit(element);
            }
            if let Some(rest) = rest {
                visit(rest);
            }
            coverage.root_sets += usize::from(root_collision);
        }
    }
    let collision = root_collision || child_collision;
    ground_constructor_tree &= !collision;
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
    } else if ground_constructor_tree
        && matches!(term.kind(), TermKind::Map { .. } | TermKind::Set { .. })
    {
        assert!(
            term.concrete_after_normalization(),
            "{case}: a collision-free ground constructor collection must retain concrete shape: {term:?}"
        );
        assert!(
            term.attributes().constructor_like,
            "{case}: a collision-free ground constructor collection must retain constructor likeness: {term:?}"
        );
        coverage.concrete_controls += 1;
    }
    CollisionShape {
        collision,
        ground_constructor_tree,
    }
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
        assert!(check_hereditary_collisions(&term, case, &mut coverage).collision);
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
        assert!(!check_hereditary_collisions(&term, case, &mut coverage).collision);
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
    assert_eq!(coverage.root_sets, 30);
    assert_eq!(coverage.root_maps, 28);
    assert_eq!(coverage.inherited, 55);
    assert_eq!(coverage.concrete_controls, 805);
}

/// Keys for the grouping of `collection_disequalities`: rigid keys of a few skeletons over a
/// small alphabet (domain values of two sorts, injections with two sources and two targets,
/// free constructors of one and two arguments, an `anywhere` symbol with and without the
/// evaluated mark), so that keys of one skeleton, equal keys and keys of different skeletons
/// are all frequent, and keys that are not rigid (variables, function applications, maps).
fn grouping_key() -> impl Strategy<Value = Term> {
    use proptest::prelude::*;
    let sorts = || {
        prop_oneof![
            Just(Sort::simple("SortInt")),
            Just(Sort::simple("SortKItem")),
            Just(Sort::simple("SortS")),
        ]
    };
    let leaf = prop_oneof![
        4 => (sorts(), prop_oneof![Just("0"), Just("1"), Just("2")])
            .prop_map(|(sort, value)| Term::domain_value(sort, value)),
        1 => (prop_oneof![Just("X"), Just("Y")], sorts())
            .prop_map(|(name, sort)| Term::variable(crate::term::Variable::new(name, sort))),
    ];
    let symbol = |name: &str, arity: usize, anywhere: bool, function: bool| {
        let mut symbol = Symbol::constructor(
            name,
            vec![Sort::simple("SortS"); arity],
            Sort::simple("SortS"),
        );
        symbol.attributes = crate::term::SymbolAttributes::constructor().with_anywhere(anywhere);
        if function {
            symbol.attributes.symbol_type =
                crate::term::SymbolType::Function(crate::term::FunctionType::Total);
        }
        Arc::new(symbol)
    };
    let loc = symbol("loc", 1, false, false);
    let pair = symbol("pair", 2, false, false);
    let norm = symbol("norm", 1, true, false);
    let function = symbol("f", 1, false, true);
    let (int, kitem, s) = (
        Sort::simple("SortInt"),
        Sort::simple("SortKItem"),
        Sort::simple("SortS"),
    );
    let value = || prop_oneof![Just("0"), Just("1"), Just("2")];
    // Keys of six skeletons, their domain values drawn from three texts.
    let templates = {
        let (loc, pair, norm) = (loc.clone(), pair.clone(), norm.clone());
        (0..6usize, value(), value(), any::<bool>()).prop_map(
            move |(template, first, second, marked)| {
                let dv = |sort: &Sort, value: &str| Term::domain_value(sort.clone(), value);
                match template {
                    0 => dv(&int, first),
                    1 => Term::injection(int.clone(), kitem.clone(), dv(&int, first)),
                    2 => Term::application(
                        loc.clone(),
                        vec![],
                        vec![Term::injection(int.clone(), s.clone(), dv(&int, first))],
                    ),
                    3 => Term::application(
                        pair.clone(),
                        vec![],
                        vec![
                            dv(&s, first),
                            Term::application(loc.clone(), vec![], vec![dv(&s, second)]),
                        ],
                    ),
                    4 => {
                        let term = Term::application(norm.clone(), vec![], vec![dv(&s, first)]);
                        // An equation head is rigid only with the evaluated mark.
                        if marked {
                            term.with_evaluated_mark_for_test()
                        } else {
                            term
                        }
                    }
                    _ => Term::injection(s.clone(), kitem.clone(), dv(&s, first)),
                }
            },
        )
    };
    let random = leaf.prop_recursive(3, 24, 2, move |inner| {
        let (loc, pair, norm, function) =
            (loc.clone(), pair.clone(), norm.clone(), function.clone());
        prop_oneof![
            3 => (sorts(), sorts(), inner.clone())
                .prop_map(|(source, target, term)| Term::injection(source, target, term)),
            3 => inner.clone().prop_map(move |term| Term::application(loc.clone(), vec![], vec![term])),
            2 => (inner.clone(), inner.clone())
                .prop_map(move |(left, right)| Term::application(pair.clone(), vec![], vec![left, right])),
            2 => (inner.clone(), any::<bool>()).prop_map(move |(term, marked)| {
                let term = Term::application(norm.clone(), vec![], vec![term]);
                if marked && term.attributes().variables.is_empty() {
                    term.with_evaluated_mark_for_test()
                } else {
                    term
                }
            }),
            1 => inner.clone().prop_map(move |term| Term::application(function.clone(), vec![], vec![term])),
        ]
    });
    prop_oneof![3 => templates, 1 => random]
}

/// The grouping by apartness skeleton states the disequalities that `elements_are_apart` states
/// pair by pair, in the same order, for the sorted keys of a map and the sorted elements of a set
/// (`apart_of_sameSkeleton` of the Lean model, applied to the Rust): a pair it skips is a pair of
/// distinct rigid keys with one skeleton, which `elements_are_apart` separates.
#[test]
fn grouped_disequalities_are_the_pairwise_ones() {
    use proptest::prelude::*;
    let definition = definition();
    let strategy = prop::collection::vec(grouping_key(), 0..12);
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let set_definition = Arc::new(ListDefinition {
        symbols: CollectionSymbols {
            unit: "Setunit".into(),
            element: "Setelement".into(),
            concat: "Setconcat".into(),
        },
        element_sort: "SortKItem".into(),
        list_sort: "SortSet".into(),
    });
    // Pairs skipped by the grouping, pairs with a disequality, and collections with a repeat.
    let (mut skipped, mut stated, mut repeats) = (0, 0, 0);
    for case in 0..CASES {
        let keys = strategy.new_tree(&mut runner).expect("a case").current();
        let set = Term::set(set_definition.clone(), keys, None);
        let TermKind::Set { elements, .. } = set.kind() else {
            unreachable!("a set without a rest is a set");
        };
        let keys = elements.iter().collect::<Vec<_>>();
        let checks = |grouped| {
            crate::definedness::APARTNESS_CHECKS.set(0);
            let disequalities =
                crate::definedness::collection_disequalities(&definition, &keys, grouped);
            (disequalities, crate::definedness::APARTNESS_CHECKS.get())
        };
        let (pairwise, all) = checks(false);
        let (grouped, made) = checks(true);
        assert_eq!(
            grouped, pairwise,
            "case {case}: the grouping changed the disequalities of {keys:?}"
        );
        assert_eq!(all, keys.len() * keys.len().saturating_sub(1) / 2);
        skipped += all - made;
        stated += pairwise.len();
        repeats += usize::from(keys.windows(2).any(|pair| pair[0] == pair[1]));
    }
    eprintln!("pairs skipped {skipped}, disequalities stated {stated}, repeats {repeats}");
    assert!(skipped > 0 && stated > 0 && repeats > 0);
}

/// R-def: the ceil of a map whose keys are rigid with one skeleton makes no apartness check
/// beyond its repeated keys, however many keys it has: two distinct keys of one skeleton are
/// apart. A value that is not `ceil_free` keeps the walk from skipping the map, as the store of
/// an interpreter's configuration does when it holds a closure. Keys of a second skeleton are
/// checked against the first ones and among themselves only when they are not rigid.
#[test]
fn keys_of_one_skeleton_need_no_apartness_check() {
    let definition = definition();
    let map_definition = Arc::new(MapDefinition {
        symbols: CollectionSymbols {
            unit: "Mapunit".into(),
            element: "Mapelement".into(),
            concat: "Mapconcat".into(),
        },
        key_sort: "SortKItem".into(),
        value_sort: "SortKItem".into(),
        map_sort: "SortMap".into(),
    });
    let (int, kitem, s) = (
        Sort::simple("SortInt"),
        Sort::simple("SortKItem"),
        Sort::simple("SortS"),
    );
    let key = |value: usize| {
        Term::injection(
            int.clone(),
            kitem.clone(),
            Term::domain_value(int.clone(), value.to_string()),
        )
    };
    let mut partial = Symbol::constructor("partial", vec![s.clone()], kitem.clone());
    partial.attributes.symbol_type =
        crate::term::SymbolType::Function(crate::term::FunctionType::Partial);
    let undefined = Term::application(
        Arc::new(partial),
        vec![],
        vec![Term::domain_value(s.clone(), "a")],
    );
    let value = Term::domain_value(int.clone(), "0");
    let checks = |entries: Vec<(Term, Term)>| {
        let map = Term::map(map_definition.clone(), entries, None);
        crate::definedness::APARTNESS_CHECKS.set(0);
        let obligations = ceil_term(&definition, &map);
        (crate::definedness::APARTNESS_CHECKS.get(), obligations)
    };
    let mut entries = (0..200)
        .map(|index| (key(index), value.clone()))
        .collect::<Vec<_>>();
    entries.push((key(200), undefined.clone()));
    let (made, obligations) = checks(entries.clone());
    assert_eq!(made, 0);
    assert_eq!(
        obligations,
        vec![crate::rule::Predicate::Ceil(undefined.clone())]
    );
    // A repeated key: one check, and its disequality, which makes the map `\bottom`.
    entries.push((key(7), value.clone()));
    let (made, obligations) = checks(entries.clone());
    assert_eq!(made, 1);
    assert!(obligations.contains(&crate::rule::Predicate::Not(Box::new(
        crate::rule::Predicate::Equals(key(7), key(7))
    ))));
    // Keys of a second skeleton (`inj{S, KItem}(\dv{S}(…))`): each is checked against the 201
    // keys of the first, not against its own group.
    entries.pop();
    entries.extend((0..3).map(|index| {
        (
            Term::injection(
                s.clone(),
                kitem.clone(),
                Term::domain_value(s.clone(), index.to_string()),
            ),
            value.clone(),
        )
    }));
    let (made, _) = checks(entries);
    assert_eq!(made, 3 * 201);
}

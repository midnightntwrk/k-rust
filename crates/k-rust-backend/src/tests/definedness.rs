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
                for (other_key, _) in entries.range(index + 1..) {
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
                for other in elements.range(index + 1..) {
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
        key_sort: Sort::simple("SortInt"),
        value_sort: Sort::simple("SortInt"),
        map_sort: "SortMap".into(),
    });
    let set_definition = Arc::new(ListDefinition {
        symbols: symbols("Set"),
        element_sort: Sort::simple("SortInt"),
        list_sort: "SortSet".into(),
    });
    let int = |value: &str| Term::raw_domain_value(Sort::simple("SortInt"), value);
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
    assert_eq!(coverage.root_sets, 25);
    assert_eq!(coverage.root_maps, 19);
    assert_eq!(coverage.inherited, 38);
    assert_eq!(coverage.concrete_controls, 800);
}

/// Keys for the grouping of `collection_disequalities`: rigid keys of a few skeletons over a
/// small alphabet (domain values of two sorts, injections with two sources and two targets,
/// free constructors of one and two arguments, an `anywhere` symbol with and without the
/// evaluated mark), so that keys of one skeleton, equal keys and keys of different skeletons
/// are all frequent, and keys that are not rigid (variables, function applications, and maps,
/// sets and lists, bare or below a constructor). [`KeyCoverage`] counts these classes.
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
            .prop_map(|(sort, value)| Term::raw_domain_value(sort, value)),
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
                let dv = |sort: &Sort, value: &str| Term::raw_domain_value(sort.clone(), value);
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
    let collections = collection_definitions();
    let random = leaf.prop_recursive(3, 24, 2, move |inner| {
        let (loc, pair, norm, function) =
            (loc.clone(), pair.clone(), norm.clone(), function.clone());
        let (maps, sets, lists) = collections.clone();
        prop_oneof![
            1 => prop::collection::vec((inner.clone(), inner.clone()), 0..3)
                .prop_map(move |entries| Term::map(maps.clone(), entries, None)),
            1 => prop::collection::vec(inner.clone(), 0..3)
                .prop_map(move |elements| Term::set(sets.clone(), elements, None)),
            1 => prop::collection::vec(inner.clone(), 0..3)
                .prop_map(move |items| Term::list(lists.clone(), items, None)),
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

/// A map, a set and a list definition over the sort `SortKItem`, for keys that hold a
/// collection.
fn collection_definitions() -> (Arc<MapDefinition>, Arc<ListDefinition>, Arc<ListDefinition>) {
    let symbols = |prefix: &str| CollectionSymbols {
        unit: format!("{prefix}unit").into(),
        element: format!("{prefix}element").into(),
        concat: format!("{prefix}concat").into(),
    };
    (
        Arc::new(MapDefinition {
            symbols: symbols("Map"),
            key_sort: Sort::simple("SortKItem"),
            value_sort: Sort::simple("SortKItem"),
            map_sort: "SortMap".into(),
        }),
        Arc::new(ListDefinition {
            symbols: symbols("Set"),
            element_sort: Sort::simple("SortKItem"),
            list_sort: "SortSet".into(),
        }),
        Arc::new(ListDefinition {
            symbols: symbols("List"),
            element_sort: Sort::simple("SortKItem"),
            list_sort: "SortList".into(),
        }),
    )
}

/// The classes of keys [`grouping_key`]'s documentation names that a property's keys held.
#[derive(Debug, Default)]
struct KeyCoverage {
    variables: usize,
    function_applications: usize,
    collections: usize,
    collections_below_a_constructor: usize,
}

impl KeyCoverage {
    fn count(&mut self, key: &Term) {
        fn holds(term: &Term, found: &mut dyn FnMut(&Term, bool) -> bool, below: bool) -> bool {
            if found(term, below) {
                return true;
            }
            match term.kind() {
                TermKind::Application { arguments, .. } => arguments
                    .iter()
                    .any(|argument| holds(argument, found, true)),
                TermKind::Injection { term, .. } => holds(term, found, below),
                TermKind::Map { entries, .. } => entries
                    .iter()
                    .any(|(key, value)| holds(key, found, below) || holds(value, found, below)),
                TermKind::Set { elements, .. } => {
                    elements.iter().any(|element| holds(element, found, below))
                }
                TermKind::List { heads, .. } => heads.iter().any(|item| holds(item, found, below)),
                _ => false,
            }
        }
        let collection = |term: &Term| {
            matches!(
                term.kind(),
                TermKind::Map { .. } | TermKind::Set { .. } | TermKind::List { .. }
            )
        };
        self.variables += usize::from(!key.attributes().variables.is_empty());
        self.function_applications += usize::from(holds(
            key,
            &mut |term, _| {
                matches!(term.kind(), TermKind::Application { symbol, .. }
                    if matches!(symbol.attributes.symbol_type, crate::term::SymbolType::Function(_)))
            },
            false,
        ));
        self.collections += usize::from(holds(key, &mut |term, _| collection(term), false));
        self.collections_below_a_constructor += usize::from(holds(
            key,
            &mut |term, below| below && collection(term),
            false,
        ));
    }

    fn assert_covered(&self) {
        eprintln!("grouping key coverage: {self:?}");
        assert!(self.variables > 0, "no key holds a variable");
        assert!(
            self.function_applications > 0,
            "no key holds a function application"
        );
        assert!(self.collections > 0, "no key holds a collection");
        assert!(
            self.collections_below_a_constructor > 0,
            "no key holds a collection below a constructor"
        );
    }
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
        element_sort: Sort::simple("SortKItem"),
        list_sort: "SortSet".into(),
    });
    // Pairs skipped by the grouping, pairs with a disequality, and collections with a repeat.
    let (mut skipped, mut stated, mut repeats) = (0, 0, 0);
    let mut coverage = KeyCoverage::default();
    for case in 0..CASES {
        let keys = strategy.new_tree(&mut runner).expect("a case").current();
        for key in &keys {
            coverage.count(key);
        }
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
    coverage.assert_covered();
}

/// The grouping states the pairwise disequalities on each generated key beside its one-edit
/// neighbours (`generators::one_edit_neighbours`: a collection's rest or definition, one sort, a
/// variable's name, one symbol or one domain value changed at any depth), keys that agree on
/// every field but one and so share a skeleton or differ in it by that field alone.
#[test]
fn grouped_disequalities_are_the_pairwise_ones_on_one_edit_neighbours() {
    use proptest::prelude::*;

    use super::lean_bridge::generators::one_edit_neighbours;
    let definition = definition();
    let (_, set_definition, _) = collection_definitions();
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let mut neighbours = 0usize;
    for case in 0..CASES {
        let key = grouping_key()
            .new_tree(&mut runner)
            .expect("a case")
            .current();
        let mut keys = vec![key.clone()];
        keys.extend(
            one_edit_neighbours(&key)
                .into_iter()
                .map(|(_, neighbour)| neighbour),
        );
        neighbours += keys.len() - 1;
        let set = Term::set(set_definition.clone(), keys, None);
        let TermKind::Set { elements, .. } = set.kind() else {
            unreachable!("a set without a rest is a set");
        };
        let keys = elements.iter().collect::<Vec<_>>();
        let pairwise = crate::definedness::collection_disequalities(&definition, &keys, false);
        let grouped = crate::definedness::collection_disequalities(&definition, &keys, true);
        assert_eq!(
            grouped, pairwise,
            "case {case}: the grouping changed the disequalities of {keys:?}"
        );
    }
    assert!(neighbours > 0, "no key has a neighbour");
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
        key_sort: Sort::simple("SortKItem"),
        value_sort: Sort::simple("SortKItem"),
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
            Term::raw_domain_value(int.clone(), value.to_string()),
        )
    };
    let mut partial = Symbol::constructor("partial", vec![s.clone()], kitem.clone());
    partial.attributes.symbol_type =
        crate::term::SymbolType::Function(crate::term::FunctionType::Partial);
    let undefined = Term::application(
        Arc::new(partial),
        vec![],
        vec![Term::raw_domain_value(s.clone(), "a")],
    );
    let value = Term::raw_domain_value(int.clone(), "0");
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
                Term::raw_domain_value(s.clone(), index.to_string()),
            ),
            value.clone(),
        )
    }));
    let (made, _) = checks(entries);
    assert_eq!(made, 3 * 201);
}

/// A map without a rest whose keys share one header and repeat none, holding one undefined value
/// among 4,096 entries: the walk reaches that entry through the entries' summaries and states no
/// key disequality (two distinct keys of one header are apart), so it takes from its work list
/// the map, that entry's key and value and the value's argument, not the other 8,190 children;
/// the obligations are the full walk's. The same holds of a list of 4,096 items one of which is
/// undefined. (A set's undefined element is one of its keys, which has no header, so the walk
/// states its disequality from each other element.)
#[test]
fn one_undefined_item_of_a_large_collection_is_reached_without_the_others() {
    let definition = definition();
    let (map_definition, _, list_definition) = collection_definitions();
    let (int, kitem, s) = (
        Sort::simple("SortInt"),
        Sort::simple("SortKItem"),
        Sort::simple("SortS"),
    );
    let key = |value: usize| {
        Term::injection(
            int.clone(),
            kitem.clone(),
            Term::raw_domain_value(int.clone(), value.to_string()),
        )
    };
    let mut partial = Symbol::constructor("partial", vec![s.clone()], kitem.clone());
    partial.attributes.symbol_type =
        crate::term::SymbolType::Function(crate::term::FunctionType::Partial);
    let undefined = Term::application(
        Arc::new(partial),
        vec![],
        vec![Term::raw_domain_value(s.clone(), "a")],
    );
    let map = Term::map(
        map_definition,
        (0..4096)
            .map(|index| {
                let value = if index == 1234 {
                    undefined.clone()
                } else {
                    key(index)
                };
                (key(index), value)
            })
            .collect(),
        None,
    );
    let mut elements = (0..4095).map(key).collect::<Vec<_>>();
    elements.push(undefined.clone());
    let list = Term::list(list_definition, elements, None);
    for (term, walked) in [(map, 4), (list, 3)] {
        crate::definedness::WALKED_TERMS.set(0);
        let obligations = ceil_term(&definition, &term);
        assert_eq!(
            crate::definedness::WALKED_TERMS.get(),
            walked,
            "{}",
            kind_name(&term)
        );
        assert_eq!(
            obligations,
            vec![crate::rule::Predicate::Ceil(undefined.clone())]
        );
        assert_eq!(obligations, ceil_term_without_attribute(&definition, &term));
    }
}

/// A collection of 4,096 items with one undefined item, built over `item` at each position:
/// the map binds `key(index)` to it, the set and the list hold it.
#[cfg(debug_assertions)]
fn collections_of(item: impl Fn(usize) -> Term) -> [Term; 3] {
    let (map_definition, set_definition, list_definition) = collection_definitions();
    [
        Term::map(
            map_definition,
            (0..4096)
                .map(|index| (collection_key(index), item(index)))
                .collect(),
            None,
        ),
        Term::set(set_definition, (0..4096).map(&item).collect(), None),
        Term::list(list_definition, (0..4096).map(&item).collect(), None),
    ]
}

/// `inj{Int, KItem}(\dv{Int}(index))`.
#[cfg(debug_assertions)]
fn collection_key(index: usize) -> Term {
    let (int, kitem) = (Sort::simple("SortInt"), Sort::simple("SortKItem"));
    Term::injection(
        int.clone(),
        kitem,
        Term::raw_domain_value(int, index.to_string()),
    )
}

/// `partial(\dv{S}(name))`, an application of a partial function: its ceil is an obligation.
#[cfg(debug_assertions)]
fn undefined_item(name: &str) -> Term {
    let (kitem, s) = (Sort::simple("SortKItem"), Sort::simple("SortS"));
    let mut partial = Symbol::constructor("partial", vec![s.clone()], kitem);
    partial.attributes.symbol_type =
        crate::term::SymbolType::Function(crate::term::FunctionType::Partial);
    Term::application(
        Arc::new(partial),
        vec![],
        vec![Term::raw_domain_value(s, name)],
    )
}

/// Debug builds: a collection that is not `ceil_free`, since it holds an undefined item the walk
/// takes, and that also holds an item whose stored `ceil_free` attribute is wrong (an
/// application of a partial function, forged `ceil_free`). The walk passes over the forged item
/// through the collection's summaries, as over every other `ceil_free` item, and the debug check
/// of the items it passes over finds the forged item's obligation. The forged item is a map
/// value, a set element and a list item, among 4,096 items, so that it lies in a subtree the walk
/// skips whole.
#[cfg(debug_assertions)]
#[test]
fn the_debug_check_finds_a_wrong_ceil_free_item_the_walk_passes_over() {
    let definition = definition();
    let forged = undefined_item("forged").with_ceil_free_for_test();
    let taken = undefined_item("taken");
    for term in collections_of(|index| match index {
        100 => forged.clone(),
        3000 => taken.clone(),
        _ => collection_key(index),
    }) {
        assert!(!term.attributes().ceil_free(), "{}", kind_name(&term));
        let walked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            ceil_term(&definition, &term)
        }));
        let failure = walked.expect_err(kind_name(&term));
        let message = failure
            .downcast_ref::<String>()
            .map(String::as_str)
            .unwrap_or_default();
        assert!(
            message.starts_with("a ceil_free term has definedness obligations")
                && message.contains("forged"),
            "{}: {message}",
            kind_name(&term)
        );
    }
}

/// Debug builds: the check of the items the walk passes over reads each tree node once. Of a map,
/// a set and a list of 4,096 items one of which is undefined, a first walk hands over every
/// other item; a second walk hands over only the items of the leaf it enters to reach the
/// undefined one, the checked subtrees beside that leaf being marked; and a walk of the
/// collection with one item added hands over, beyond those, the items of the leaves the addition
/// built, at most two leaves' worth (`Chunked::check_passed_over`). Neither grows with the items.
#[cfg(debug_assertions)]
#[test]
fn the_debug_check_of_passed_over_items_reads_what_an_edit_built() {
    use crate::{definedness::PASSED_OVER_ITEMS, term::chunked::DEFAULT_BRANCHING};
    let definition = definition();
    let (map_definition, set_definition, list_definition) = collection_definitions();
    let taken = undefined_item("taken");
    let handed_over = |term: &Term| {
        PASSED_OVER_ITEMS.set(0);
        ceil_term(&definition, term);
        PASSED_OVER_ITEMS.get()
    };
    for term in collections_of(|index| {
        if index == 3000 {
            taken.clone()
        } else {
            collection_key(index)
        }
    }) {
        let added = collection_key(5000);
        let edited = match term.kind() {
            TermKind::Map { .. } => Term::map(
                map_definition.clone(),
                vec![(added.clone(), added)],
                Some(term.clone()),
            ),
            TermKind::Set { .. } => {
                Term::set(set_definition.clone(), vec![added], Some(term.clone()))
            }
            _ => Term::list(
                list_definition.clone(),
                vec![added],
                Some((term.clone(), Vec::new())),
            ),
        };
        let name = kind_name(&term);
        assert_eq!(handed_over(&term), 4095, "{name}");
        let again = handed_over(&term);
        assert!(
            again < DEFAULT_BRANCHING,
            "{name}: {again} items handed over again"
        );
        let after_edit = handed_over(&edited);
        assert!(
            after_edit <= again + 2 * DEFAULT_BRANCHING,
            "{name}: {after_edit} items handed over after one addition"
        );
    }
}

/// `grouping_key`'s keys that are not rigid include collections, as its doc states: a key holding
/// a collection is not rigid (`rigid_apart_skeleton_hash` gives `None` at a
/// `FixedRoot::Collection`), so the grouping must check it pairwise, and a grouping that read a
/// collection as rigid would skip a pair `elements_are_apart` does not separate, which
/// `grouped_disequalities_are_the_pairwise_ones` sees only on keys that hold one.
#[test]
fn grouping_keys_include_keys_that_hold_a_collection() {
    use proptest::prelude::*;
    fn holds_a_collection(term: &Term) -> bool {
        let mut pending = vec![term];
        // Invariant: `pending` holds the unvisited subterms of the visited ones.
        while let Some(term) = pending.pop() {
            match term.kind() {
                TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. } => {
                    return true;
                }
                TermKind::Application { arguments, .. } => pending.extend(arguments),
                TermKind::Injection { term, .. } => pending.push(term),
                _ => {}
            }
        }
        false
    }
    let strategy = prop::collection::vec(grouping_key(), 0..12);
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let mut with_collection = 0usize;
    for _ in 0..CASES {
        let keys = strategy.new_tree(&mut runner).expect("a case").current();
        with_collection += keys.iter().filter(|key| holds_a_collection(key)).count();
    }
    assert!(with_collection > 0, "no generated key holds a collection");
}

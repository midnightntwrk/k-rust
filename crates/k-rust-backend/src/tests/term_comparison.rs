//! `PartialEq` and `Ord` for `Term`, and the work-list comparisons they hand deep terms to,
//! against the derived equality and order of `TermKind`.
//!
//! The derived comparison of two kinds compares their children with `Term`'s own comparison.
//! So a comparison that agrees with the derived one at the root of every pair also agrees with
//! it below, by induction on the size of the terms; the test checks the root of generated pairs:
//! independent terms (small alphabets, so long common parts are frequent), and each term against
//! a copy that shares no node with it, which the pointer test cannot shortcut.

use std::cmp::Ordering;

use proptest::{
    strategy::{Strategy, ValueTree},
    test_runner::{Config, RngAlgorithm, TestRng, TestRunner},
};

use super::lean_bridge::generators::{term, term_with_ground_keys};
use crate::term::{Term, equal_terms_on_work_list, order_terms_on_work_list};

const CASES: usize = 4096;

fn agree(left: &Term, right: &Term) {
    let order = left.kind().cmp(right.kind());
    assert_eq!(left.cmp(right), order, "order of {left:?} and {right:?}");
    assert_eq!(
        order_terms_on_work_list(left, right),
        order,
        "order on a work list of {left:?} and {right:?}"
    );
    let equal = left.kind() == right.kind();
    assert_eq!(left == right, equal, "equality of {left:?} and {right:?}");
    assert_eq!(
        equal_terms_on_work_list(left, right),
        equal,
        "equality on a work list of {left:?} and {right:?}"
    );
}

#[test]
fn term_comparison_is_the_derived_comparison_of_the_kinds() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let mut orders = [0usize; 3];
    let mut equal_unshared = 0usize;
    for strategy in [term().boxed(), term_with_ground_keys().boxed()] {
        for _ in 0..CASES {
            let left = strategy.new_tree(&mut runner).expect("a case").current();
            let right = strategy.new_tree(&mut runner).expect("a case").current();
            let copy = left.unshared_copy();
            for (first, second) in [
                (&left, &right),
                (&right, &left),
                (&left, &copy),
                (&copy, &right),
            ] {
                agree(first, second);
                orders[(first.cmp(second) as i8 + 1) as usize] += 1;
            }
            assert_eq!(left.cmp(&copy), Ordering::Equal);
            assert!(left == copy);
            equal_unshared += 1;
        }
    }
    eprintln!("orders [less, equal, greater]: {orders:?}; unshared copies: {equal_unshared}");
    assert!(orders.iter().all(|&count| count > 100), "{orders:?}");
}

/// Whether `left` and `right` are collections of one kind and one definition whose entries are
/// equal and of which one has a rest and the other none: the pairs on which the comparison reads
/// the rest arm `None` against `Some`, and so the only pairs that tell a wrong arm there apart.
fn differ_only_in_having_a_rest(left: &Term, right: &Term) -> bool {
    use crate::term::TermKind;
    match (left.kind(), right.kind()) {
        (
            TermKind::Map {
                definition: left_definition,
                entries: left_entries,
                rest: left_rest,
            },
            TermKind::Map {
                definition: right_definition,
                entries: right_entries,
                rest: right_rest,
            },
        ) => {
            left_definition == right_definition
                && left_entries == right_entries
                && left_rest.is_some() != right_rest.is_some()
        }
        (
            TermKind::Set {
                definition: left_definition,
                elements: left_elements,
                rest: left_rest,
            },
            TermKind::Set {
                definition: right_definition,
                elements: right_elements,
                rest: right_rest,
            },
        ) => {
            left_definition == right_definition
                && left_elements == right_elements
                && left_rest.is_some() != right_rest.is_some()
        }
        (
            TermKind::List {
                definition: left_definition,
                heads: left_heads,
                rest: left_rest,
            },
            TermKind::List {
                definition: right_definition,
                heads: right_heads,
                rest: right_rest,
            },
        ) => {
            left_definition == right_definition
                && left_heads == right_heads
                && left_rest.is_some() != right_rest.is_some()
        }
        _ => false,
    }
}

/// The comparison is the derived comparison of the kinds on each generated collection against
/// its one-edit neighbour that differs from it only in having a rest (a variable of the
/// collection's sort added, or its rest removed). A comparison is decided by the first field in
/// which two terms differ, so these pairs are the only ones that reach the rest arm with every
/// field before it equal, and independent draws almost never produce them: a comparison with the
/// `None` and `Some` rests ordered the other way passes
/// `term_comparison_is_the_derived_comparison_of_the_kinds`, and fails here.
#[test]
fn the_comparison_is_the_derived_comparison_on_collections_that_differ_only_in_having_a_rest() {
    use crate::term::{Sort, TermKind, Variable};
    let rest = |sort: &str| Term::variable(Variable::new("Rest", Sort::simple(sort)));
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let mut compared = 0usize;
    for strategy in [term().boxed(), term_with_ground_keys().boxed()] {
        for _ in 0..CASES {
            let collection = strategy.new_tree(&mut runner).expect("a case").current();
            #[expect(
                clippy::wildcard_enum_match_arm,
                reason = "only collections have a rest"
            )]
            let neighbour = match collection.kind() {
                TermKind::Map {
                    definition,
                    entries,
                    rest: own,
                } if !entries.is_empty() => Term::map(
                    definition.clone(),
                    entries.to_vec(),
                    own.is_none().then(|| rest("SortMap")),
                ),
                TermKind::Set {
                    definition,
                    elements,
                    rest: own,
                } if !elements.is_empty() => Term::set(
                    definition.clone(),
                    elements.to_vec(),
                    own.is_none().then(|| rest("SortSet")),
                ),
                TermKind::List {
                    definition,
                    heads,
                    rest: own,
                } if !heads.is_empty() => Term::list(
                    definition.clone(),
                    heads.to_vec(),
                    own.is_none().then(|| (rest("SortList"), Vec::new())),
                ),
                _ => continue,
            };
            assert!(
                differ_only_in_having_a_rest(&collection, &neighbour)
                    || matches!(collection.kind(), TermKind::List { rest: Some((_, tails)), .. } if !tails.is_empty()),
                "{collection:?} and {neighbour:?}"
            );
            agree(&collection, &neighbour);
            agree(&neighbour, &collection);
            compared += 1;
        }
    }
    assert!(compared > 0, "no collection compared with its neighbour");
}

/// The comparison is the derived comparison on each generated term against each of its one-edit
/// neighbours (`generators::one_edit_neighbours`: a collection's rest or definition, one sort, a
/// variable's name, one symbol or one domain value changed at any depth), the pairs that reach
/// the arm comparing the edited field with every field before it equal; every kind of edit
/// occurs.
#[test]
fn the_comparison_is_the_derived_comparison_on_one_edit_neighbours() {
    use super::lean_bridge::generators::{Edit, one_edit_neighbours};
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let mut edits = std::collections::BTreeMap::<Edit, usize>::new();
    for strategy in [term().boxed(), term_with_ground_keys().boxed()] {
        for _ in 0..CASES / 4 {
            let term = strategy.new_tree(&mut runner).expect("a case").current();
            for (edit, neighbour) in one_edit_neighbours(&term) {
                agree(&term, &neighbour);
                agree(&neighbour, &term);
                *edits.entry(edit).or_default() += 1;
            }
        }
    }
    eprintln!("one-edit neighbours compared: {edits:?}");
    for edit in Edit::ALL {
        assert!(edits.contains_key(&edit), "no {edit:?} edit: {edits:?}");
    }
}

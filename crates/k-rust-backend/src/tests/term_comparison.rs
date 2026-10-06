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
use crate::term::{InjectionComparison, Term, equal_terms_on_work_list, order_terms_on_work_list};

const CASES: usize = 4096;

/// An injection callback of `Term::apart_with`.
type Injections = dyn Fn(&Term, &Term) -> InjectionComparison;

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

/// `Term::apart_with`, which recurses for a few levels before it continues on the work list,
/// decides every generated pair as the work-list search alone does, with an injection callback
/// that decides nothing and one that compares the operands.
#[test]
fn apartness_is_the_work_list_search() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let undecided = |_: &Term, _: &Term| InjectionComparison::Undecided;
    let operands = |left: &Term, right: &Term| match (left.kind(), right.kind()) {
        (
            crate::term::TermKind::Injection { term: left, .. },
            crate::term::TermKind::Injection { term: right, .. },
        ) => InjectionComparison::Compare(left.clone(), right.clone()),
        _ => InjectionComparison::Undecided,
    };
    let mut apart = 0usize;
    for strategy in [term().boxed(), term_with_ground_keys().boxed()] {
        for _ in 0..CASES {
            let left = strategy.new_tree(&mut runner).expect("a case").current();
            let right = strategy.new_tree(&mut runner).expect("a case").current();
            for injections in [&undecided as &Injections, &operands] {
                for (first, second) in [(&left, &right), (&right, &left)] {
                    let decided = first.apart_with(second, injections).is_some();
                    assert_eq!(
                        decided,
                        first.apart_on_work_list(second, injections).is_some(),
                        "apartness of {first:?} and {second:?}"
                    );
                    apart += usize::from(decided);
                }
            }
        }
    }
    eprintln!("apart pairs: {apart}");
    assert!(apart > 100, "{apart}");
}

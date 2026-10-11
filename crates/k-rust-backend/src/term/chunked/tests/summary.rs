//! Tests of the generic summaries and of the group summary kept by difference: each summary at
//! the root against its definition over the item `Vec`, the multiset against a `BTreeMap` of
//! counts, and the work a path copy does on the multisets of a tree of distinct variables.

use std::{
    collections::{BTreeMap, HashSet},
    sync::Arc,
};

use proptest::prelude::*;

use super::edit::height;
use super::{DEFAULT, Entry, check_invariants, choices, entries, fx_hash, shaped};
use crate::term::chunked::{
    Chunked, Group, Item, Node, NodeSummary, Summary,
    multiset::{Multiset, Occurrences},
    summary::{Count, Uniform},
};

/// Every generic summary at the root is what its definition says of the item sequence.
fn summaries_match_definitions<const B: usize>(items: &[Entry], shape: Vec<u8>) {
    let tree = shaped::<Entry, B>(items.to_vec(), shape);
    let summary = tree
        .summary()
        .cloned()
        .unwrap_or_else(NodeSummary::identity);
    let (tally, failing, symbolic, cells, marked, header) = &summary.extra;
    let odd = || items.iter().filter(|item| item.value % 2 == 1);
    assert_eq!(
        tally.sum,
        items.iter().map(|item| u64::from(item.value)).sum::<u64>()
    );
    assert_eq!(tally.odd, odd().count());
    assert_eq!(tally.first_odd, odd().next().map(|item| item.value));
    for flag in 0..2 {
        let expected = items.iter().filter(|item| !item.flags()[flag]).count();
        assert_eq!(failing.failing(flag), expected);
        assert_eq!(failing.holds(flag), expected == 0);
    }
    assert_eq!(
        symbolic.0,
        items.iter().filter(|item| item.symbolic_key()).count()
    );
    assert_eq!(
        cells.get(),
        items.iter().map(Entry::cells).sum::<usize>().min(2)
    );
    assert_eq!(marked.0, items.iter().any(Entry::marked));
    let expected_header = match items {
        [] => Uniform::Empty,
        [first, ..] if items.iter().all(|item| item.header() == first.header()) => {
            Uniform::One(first.header())
        }
        _ => Uniform::Mixed,
    };
    assert_eq!(*header, expected_header);
    assert_eq!(
        summary.collision,
        items.windows(2).any(|pair| pair[0].key == pair[1].key)
    );
    let mut variables = BTreeMap::new();
    for item in items {
        for variable in item.variables() {
            *variables.entry(variable).or_insert(0) += 1;
        }
    }
    check_multiset(&summary.group, &variables);
}

/// The multiset's tree satisfies the invariant, holds one entry per element in order, and
/// agrees with the model on every count; equal multisets built differently are equal.
fn check_multiset<const B: usize>(multiset: &Multiset<u8, B>, model: &BTreeMap<u8, usize>) {
    check_invariants(multiset.entries());
    let entries: Vec<(u8, usize)> = multiset
        .entries()
        .iter()
        .map(|entry| (entry.element, entry.count))
        .collect();
    let expected: Vec<(u8, usize)> = model.iter().map(|(&e, &c)| (e, c)).collect();
    assert_eq!(entries, expected);
    assert_eq!(multiset.len(), model.len());
    assert_eq!(multiset.is_empty(), model.is_empty());
    assert!(multiset.elements().eq(model.keys()));
    for element in 0..64 {
        assert_eq!(
            multiset.count(&element),
            model.get(&element).copied().unwrap_or(0)
        );
    }
    assert_eq!(format!("{multiset:?}"), format!("{model:?}"));
    let rebuilt = Multiset::<u8, B>::of(
        model
            .iter()
            .flat_map(|(&element, &count)| std::iter::repeat_n(element, count)),
    );
    assert_eq!(multiset, &rebuilt);
}

/// One step of a multiset history: add, remove, combine with another multiset, or subtract a
/// part of the multiset.
#[derive(Clone, Debug)]
enum Step {
    Add(u8, usize),
    Remove(usize, usize),
    Combine(Vec<u8>),
    Subtract(Vec<u8>),
}

fn step() -> impl Strategy<Value = Step> {
    prop_oneof![
        (0u8..64, 1usize..4).prop_map(|(element, count)| Step::Add(element, count)),
        (any::<usize>(), any::<usize>()).prop_map(|(which, count)| Step::Remove(which, count)),
        prop::collection::vec(0u8..64, 0..40).prop_map(Step::Combine),
        prop::collection::vec(any::<u8>(), 0..64).prop_map(Step::Subtract),
    ]
}

fn multiset_history<const B: usize>(steps: &[Step]) {
    let mut versions = vec![(Multiset::<u8, B>::new(), BTreeMap::new())];
    for step in steps {
        let (multiset, model) = versions.last().expect("a first version").clone();
        let (multiset, model) = match step {
            Step::Add(element, count) => {
                let mut model = model;
                *model.entry(*element).or_insert(0) += count;
                (multiset.add(element, *count), model)
            }
            Step::Remove(which, count) => {
                if model.is_empty() {
                    continue;
                }
                let (&element, &held) = model.iter().nth(which % model.len()).expect("in range");
                let count = 1 + count % held;
                let mut model = model;
                if held == count {
                    model.remove(&element);
                } else {
                    model.insert(element, held - count);
                }
                (multiset.remove(&element, count), model)
            }
            Step::Combine(elements) => {
                let other = Multiset::of(elements.iter().copied());
                let mut model = model;
                for element in elements {
                    *model.entry(*element).or_insert(0) += 1;
                }
                // Both orders: the combination adds the lighter side to the heavier one.
                let combined = multiset.clone().combine(&other);
                assert_eq!(combined, other.combine(&multiset));
                (combined, model)
            }
            Step::Subtract(choices) => {
                let mut part = Vec::new();
                let mut rest = BTreeMap::new();
                for (index, (&element, &held)) in model.iter().enumerate() {
                    let taken = choices
                        .get(index)
                        .map_or(0, |choice| usize::from(*choice) % (held + 1));
                    part.extend(std::iter::repeat_n(element, taken));
                    if held > taken {
                        rest.insert(element, held - taken);
                    }
                }
                (multiset.subtract(&Multiset::of(part)), rest)
            }
        };
        check_multiset(&multiset, &model);
        versions.push((multiset, model));
    }
    for (multiset, model) in &versions {
        check_multiset(multiset, model);
    }
}

proptest! {
    #[test]
    fn generic_summaries_match_their_definitions(items in entries(300), shape in choices()) {
        summaries_match_definitions::<5>(&items, shape.clone());
        summaries_match_definitions::<6>(&items, shape.clone());
        summaries_match_definitions::<DEFAULT>(&items, shape);
    }

    #[test]
    fn a_multiset_follows_its_model(steps in prop::collection::vec(step(), 0..40)) {
        multiset_history::<5>(&steps);
        multiset_history::<6>(&steps);
        multiset_history::<DEFAULT>(&steps);
    }

    #[test]
    fn counts_form_a_group(a in 0usize..1000, b in 0usize..1000) {
        let sum = Count(a).combine(&Count(b));
        prop_assert_eq!(sum, Count(b).combine(&Count(a)));
        prop_assert_eq!(sum.subtract(&Count(b)), Count(a));
        prop_assert_eq!(Count(a).combine(&Count::identity()), Count(a));
    }
}

#[test]
fn an_occurrence_hashes_its_element_and_count() {
    let entry = Occurrences {
        element: 3u8,
        count: 2,
    };
    assert_eq!(entry.hash64(), fx_hash(&entry));
}

/// A variable as an item: its own key, mentioning itself.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Var(pub(super) u32);

impl Item for Var {
    type Key = u32;
    type Summary = ();
    type Group = Multiset<u32, 5>;

    fn key(&self) -> &u32 {
        &self.0
    }

    fn hash64(&self) -> u64 {
        u64::from(self.0)
    }

    fn summary(&self) {}

    fn group(&self) -> Multiset<u32, 5> {
        Multiset::of([self.0])
    }
}

type Multinode = Node<Occurrences<u32>>;

/// Every node of the multisets of every node of `tree`.
fn multiset_nodes(tree: &Chunked<Var, 5>) -> HashSet<*const Multinode> {
    let mut nodes = HashSet::new();
    let mut pending: Vec<&Arc<Node<Var>>> = tree.root.iter().collect();
    while let Some(node) = pending.pop() {
        let mut inner: Vec<&Arc<Multinode>> = node.summary().group.entries().root.iter().collect();
        while let Some(multinode) = inner.pop() {
            if nodes.insert(Arc::as_ptr(multinode))
                && let Node::Internal { children, .. } = &**multinode
            {
                inner.extend(children);
            }
        }
        if let Node::Internal { children, .. } = &**node {
            pending.extend(children);
        }
    }
    nodes
}

/// The multiset nodes of `after` that `before` does not hold.
pub(super) fn new_multiset_nodes(after: &Chunked<Var, 5>, before: &Chunked<Var, 5>) -> usize {
    multiset_nodes(after)
        .difference(&multiset_nodes(before))
        .count()
}

/// The height of the tallest multiset of `tree`, the root's.
pub(super) fn multiset_height(tree: &Chunked<Var, 5>) -> usize {
    tree.summary()
        .and_then(|summary| summary.group.entries().root.as_ref())
        .map_or(0, |root| root.height())
}

/// The position of the first item of the first leaf (in order) whose width satisfies `fits`.
fn leaf_where(tree: &Chunked<Var, 5>, fits: impl Fn(usize) -> bool) -> usize {
    let mut position = 0;
    let mut pending: Vec<&Arc<Node<Var>>> = tree.root.iter().collect();
    while let Some(node) = pending.pop() {
        match &**node {
            Node::Leaf { items, .. } if fits(items.len()) => return position,
            Node::Leaf { items, .. } => position += items.len(),
            Node::Internal { children, .. } => pending.extend(children.iter().rev()),
        }
    }
    panic!("no such leaf")
}

/// 2,401 distinct variables: 481 leaves of 4 or 5 items at B = 5.
pub(super) fn many_variables() -> Chunked<Var, 5> {
    Chunked::from_vec((0..2401).map(|v| Var(2 * v)).collect())
}

// An insertion into a leaf with room changes the width of no node, so it copies the `h + 1`
// nodes on the path, and each adds the one variable to its multiset: a path copy of that
// multiset, at most `2 (m + 1) + 1` nodes for a multiset of height `m` (an insertion into it).
// Recombining the copied nodes' children instead would copy most of the root's multiset.
#[test]
fn an_insertion_adds_its_variables_to_each_multiset_on_the_path() {
    let tree = many_variables();
    let index = leaf_where(&tree, |width| width < 5);
    let inserted = tree.insert_at(index, Var(2 * 9999 + 1));
    check_invariants(&inserted);
    let bound = (height(&tree) + 1) * (2 * (multiset_height(&inserted) + 1) + 1);
    assert!(new_multiset_nodes(&inserted, &tree) <= bound);
}

// A removal from a leaf above the minimum fill likewise copies the path, and each multiset on
// it loses the variable: at most `2 (m + 1)` new multiset nodes per copied node.
#[test]
fn a_removal_takes_its_variables_out_of_each_multiset_on_the_path() {
    let tree = many_variables();
    let index = leaf_where(&tree, |width| width > Chunked::<Var, 5>::MIN_FILL);
    let (removed, _) = tree.remove_at(index);
    check_invariants(&removed);
    let bound = (height(&tree) + 1) * 2 * (multiset_height(&tree) + 1);
    assert!(new_multiset_nodes(&removed, &tree) <= bound);
}

// Joining a one-item tree after a tree whose last leaf has room merges it into that leaf and
// changes no width above: each node of the right spine gains one variable.
#[test]
fn a_join_adds_the_shorter_trees_variables_along_the_spine() {
    let tree = many_variables();
    let one = Chunked::from_vec(vec![Var(9_999_999)]);
    let joined = tree.join(&one);
    check_invariants(&joined);
    let bound = (height(&tree) + 1) * (2 * (multiset_height(&joined) + 1) + 1);
    assert!(new_multiset_nodes(&joined, &tree) <= bound);
}

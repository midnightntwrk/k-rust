//! Model tests of seeks, ranges and item-wise rebuilds: the items a seek finds against a
//! filter of the `Vec`, the nodes its descent reads, a range against a slice, and each rebuild
//! against mapping (and, for an ordered sequence, sorting) the `Vec`, with the nodes it copies
//! counted exactly where nothing moves.

use std::{
    cell::Cell,
    collections::{BTreeSet, VecDeque},
    ops::Bound,
    sync::Arc,
};

use proptest::prelude::*;

use super::edit::{check, height, unshared};
use super::summary::{Var, many_variables, multiset_height, new_multiset_nodes};
use super::{DEFAULT, Entry, check_invariants, choices, entries, shaped};
use crate::term::chunked::{
    Chunked, Item, Node, NodeSummary,
    seek::{At, Seek, Where},
};

/// A seek that counts the subtrees it is asked about.
struct Counting<'a, S> {
    seek: S,
    asked: &'a Cell<usize>,
}

impl<I: Item, S: Seek<I>> Seek<I> for Counting<'_, S> {
    fn admits(&self, position: usize, summary: &NodeSummary<I>) -> bool {
        self.asked.set(self.asked.get() + 1);
        self.seek.admits(position, summary)
    }

    fn wants(&self, position: usize, item: &I) -> bool {
        self.seek.wants(position, item)
    }
}

/// The seek for the items failing the first flag, by the count of such items.
fn failing_first_flag() -> impl Seek<Entry> {
    Where::new(
        |summary: &NodeSummary<Entry>| summary.extra.1.failing(0) > 0,
        |item: &Entry| !item.flags()[0],
    )
}

/// The seek for the items mentioning a variable of `variables`, by the multiset of the
/// variables below a node (a substitution's seek).
fn mentioning(variables: BTreeSet<u8>) -> impl Seek<Entry> {
    let wanted = variables.clone();
    Where::new(
        move |summary: &NodeSummary<Entry>| {
            variables
                .iter()
                .any(|variable| summary.group.count(variable) > 0)
        },
        move |item: &Entry| {
            item.variables()
                .iter()
                .any(|variable| wanted.contains(variable))
        },
    )
}

/// The items `seek` finds are the wanted items of the `Vec`, with their positions; and since
/// it admits exactly the subtrees holding a wanted item, the descent is asked about the root
/// and the children of the wanted items' internal ancestors only: at most `1 + B (1 + s h)`
/// subtrees for `s` wanted items and height `h`.
fn finds<const B: usize>(items: &[Entry], shape: Vec<u8>, seek: impl Seek<Entry>) {
    let tree = shaped::<Entry, B>(items.to_vec(), shape);
    let asked = Cell::new(0);
    let found: Vec<(usize, Entry)> = tree
        .seek(Counting {
            seek: &seek,
            asked: &asked,
        })
        .map(|(position, item)| (position, item.clone()))
        .collect();
    let expected: Vec<(usize, Entry)> = items
        .iter()
        .cloned()
        .enumerate()
        .filter(|(position, item)| seek.wants(*position, item))
        .collect();
    assert_eq!(found, expected);
    assert!(asked.get() <= 1 + B * (1 + expected.len() * height(&tree)));
}

fn seeks<const B: usize>(items: &[Entry], shape: Vec<u8>, variables: &BTreeSet<u8>, at: usize) {
    finds::<B>(items, shape.clone(), failing_first_flag());
    finds::<B>(items, shape.clone(), mentioning(variables.clone()));
    finds::<B>(items, shape, At(at % (items.len() + 1)));
}

/// `range` from random bounds, read from random ends, against the slice.
fn range<const B: usize>(items: &[Entry], shape: Vec<u8>, bounds: (usize, usize), ends: &[bool]) {
    let tree = shaped::<Entry, B>(items.to_vec(), shape);
    let a = bounds.0 % (items.len() + 1);
    let b = bounds.1 % (items.len() + 1);
    let (start, end) = (a.min(b), a.max(b));
    let read = |mut iter: crate::term::chunked::Iter<'_, Entry>| {
        let mut model: VecDeque<&Entry> = items[start..end].iter().collect();
        assert_eq!(iter.len(), model.len());
        for &front in ends.iter().cycle().take(model.len() + 1) {
            let (got, expected) = if front {
                (iter.next(), model.pop_front())
            } else {
                (iter.next_back(), model.pop_back())
            };
            assert_eq!(got, expected);
            assert_eq!(iter.len(), model.len());
        }
    };
    read(tree.range(start..end));
    if let Some(before) = start.checked_sub(1) {
        read(tree.range((Bound::Excluded(before), Bound::Excluded(end))));
    }
    if end > start {
        read(tree.range(start..=end - 1));
    }
    if start == 0 && end == items.len() {
        read(tree.range(..));
    }
}

/// The number of nodes of `tree` whose items include one at a position of `positions`.
fn nodes_holding<I: Item, const B: usize>(
    tree: &Chunked<I, B>,
    positions: &BTreeSet<usize>,
) -> usize {
    let mut count = 0;
    let mut pending: Vec<(&Arc<Node<I>>, usize)> = tree.root.iter().map(|root| (root, 0)).collect();
    while let Some((node, start)) = pending.pop() {
        if positions
            .range(start..start + node.summary().count)
            .next()
            .is_none()
        {
            continue;
        }
        count += 1;
        if let Node::Internal { children, .. } = &**node {
            let mut position = start;
            for child in children {
                pending.push((child, position));
                position += child.summary().count;
            }
        }
    }
    count
}

/// The change the rebuild tests apply: a new value for an item with an odd value, a new key
/// (moved by `shift`) for one with an even value, unless that leaves it equal.
fn change(item: &Entry, shift: u8, keys: bool) -> Option<Entry> {
    let changed = if item.value % 2 == 1 || !keys {
        Entry {
            key: item.key,
            value: item.value.wrapping_add(shift | 1),
        }
    } else {
        Entry {
            key: ((u16::from(item.key) + u16::from(shift)) % 40) as u8,
            value: item.value,
        }
    };
    (changed != *item).then_some(changed)
}

// `map_where` changes in place exactly the wanted items `change` returns a replacement for and
// copies exactly the nodes holding one of them.
fn map_where<const B: usize>(items: &[Entry], shape: Vec<u8>, variables: &BTreeSet<u8>, shift: u8) {
    let tree = shaped::<Entry, B>(items.to_vec(), shape);
    let seek = mentioning(variables.clone());
    let mut model = items.to_vec();
    let mut changed = BTreeSet::new();
    for (position, item) in model.iter_mut().enumerate() {
        if seek.wants(position, item)
            && let Some(new) = change(item, shift, true)
        {
            *item = new;
            changed.insert(position);
        }
    }
    let mapped = tree.map_where(&seek, |item| change(item, shift, true));
    check(&mapped, &model);
    check(&tree, items);
    assert_eq!(unshared(&mapped, &[&tree]), nodes_holding(&tree, &changed));
}

// `rebuild_where` on an ordered sequence is mapping the wanted items, then sorting. A changed
// item that stays in order is replaced in place; one that does not is removed, at most
// `2 (h + 1)` new nodes, and the moved ones are put back by a union, about what inserting them
// copies, at most `5 (h + 1) + 1` each; the tree may grow by a level on the way.
fn rebuild_where<const B: usize>(
    mut items: Vec<Entry>,
    shape: Vec<u8>,
    variables: &BTreeSet<u8>,
    shift: u8,
) {
    items.sort();
    let tree = shaped::<Entry, B>(items.clone(), shape);
    let seek = mentioning(variables.clone());
    let mut model = items.clone();
    let mut changed = BTreeSet::new();
    for (position, item) in model.iter_mut().enumerate() {
        if seek.wants(position, item)
            && let Some(new) = change(item, shift, true)
        {
            *item = new;
            changed.insert(position);
        }
    }
    let in_place: Vec<Entry> = model.clone();
    model.sort();
    let rebuilt = tree.rebuild_where(&seek, |item| change(item, shift, true));
    check(&rebuilt, &model);
    check(&tree, &items);
    if in_place == model {
        // Nothing is out of order, so nothing moves.
        assert_eq!(unshared(&rebuilt, &[&tree]), nodes_holding(&tree, &changed));
    }
    let levels = height(&tree) + 2;
    assert!(
        unshared(&rebuilt, &[&tree])
            <= nodes_holding(&tree, &changed) + changed.len() * (7 * levels + 1)
    );
}

// With distinct keys, a change of values keeps the order: the rebuild is the in-place map and
// copies exactly the nodes holding a changed item.
fn rebuild_in_place<const B: usize>(
    items: Vec<Entry>,
    shape: Vec<u8>,
    variables: &BTreeSet<u8>,
    shift: u8,
) {
    let mut items = items;
    items.sort();
    items.dedup_by_key(|item| item.key);
    let tree = shaped::<Entry, B>(items.clone(), shape);
    let seek = mentioning(variables.clone());
    let mut model = items.clone();
    let mut changed = BTreeSet::new();
    for (position, item) in model.iter_mut().enumerate() {
        if seek.wants(position, item)
            && let Some(new) = change(item, shift, false)
        {
            *item = new;
            changed.insert(position);
        }
    }
    let rebuilt = tree.rebuild_where(&seek, |item| change(item, shift, false));
    check(&rebuilt, &model);
    assert_eq!(unshared(&rebuilt, &[&tree]), nodes_holding(&tree, &changed));
}

// Replacing one item copies the path to it.
fn replace_at<const B: usize>(items: &[Entry], shape: Vec<u8>, at: usize, item: Entry) {
    if items.is_empty() {
        return;
    }
    let tree = shaped::<Entry, B>(items.to_vec(), shape);
    let index = at % items.len();
    let replaced = tree.replace_at(index, item.clone());
    let mut model = items.to_vec();
    model[index] = item;
    check(&replaced, &model);
    check(&tree, items);
    assert_eq!(unshared(&replaced, &[&tree]), height(&tree) + 1);
}

fn variables() -> impl Strategy<Value = BTreeSet<u8>> {
    prop::collection::btree_set(0u8..32, 0..4)
}

proptest! {
    #[test]
    fn a_seek_finds_the_wanted_items(items in entries(300), shape in choices(), variables in variables(), at in any::<usize>()) {
        seeks::<5>(&items, shape.clone(), &variables, at);
        seeks::<6>(&items, shape.clone(), &variables, at);
        seeks::<DEFAULT>(&items, shape, &variables, at);
    }

    #[test]
    fn a_range_yields_the_items_at_its_positions(items in entries(300), shape in choices(), bounds in any::<(usize, usize)>(), ends in prop::collection::vec(any::<bool>(), 1..40)) {
        range::<5>(&items, shape.clone(), bounds, &ends);
        range::<6>(&items, shape.clone(), bounds, &ends);
        range::<DEFAULT>(&items, shape, bounds, &ends);
    }

    #[test]
    fn map_where_replaces_the_wanted_items_in_place(items in entries(300), shape in choices(), variables in variables(), shift in any::<u8>()) {
        map_where::<5>(&items, shape.clone(), &variables, shift);
        map_where::<6>(&items, shape.clone(), &variables, shift);
        map_where::<DEFAULT>(&items, shape, &variables, shift);
    }

    #[test]
    fn rebuild_where_is_map_then_sort(items in entries(300), shape in choices(), variables in variables(), shift in 1u8..40) {
        rebuild_where::<5>(items.clone(), shape.clone(), &variables, shift);
        rebuild_where::<6>(items.clone(), shape.clone(), &variables, shift);
        rebuild_where::<DEFAULT>(items, shape, &variables, shift);
    }

    #[test]
    fn a_rebuild_that_keeps_the_order_copies_only_the_changed_paths(items in entries(300), shape in choices(), variables in variables(), shift in any::<u8>()) {
        rebuild_in_place::<5>(items.clone(), shape.clone(), &variables, shift);
        rebuild_in_place::<6>(items.clone(), shape.clone(), &variables, shift);
        rebuild_in_place::<DEFAULT>(items, shape, &variables, shift);
    }

    #[test]
    fn replace_at_replaces_one_item(items in entries(300), shape in choices(), at in any::<usize>(), item in super::edit::entry()) {
        replace_at::<5>(&items, shape.clone(), at, item.clone());
        replace_at::<6>(&items, shape.clone(), at, item.clone());
        replace_at::<DEFAULT>(&items, shape, at, item);
    }
}

// A rebuild changing one variable copies the path to it, and each multiset on the path loses
// the old variable and gains the new one: at most `2 (m + 1)` and `2 (m + 1) + 1` new nodes.
#[test]
fn a_rebuild_changes_each_multiset_on_the_path_by_the_difference() {
    let tree = many_variables();
    let rebuilt = tree.map_where(&At(1200), |_| Some(Var(2 * 9999 + 1)));
    check_invariants(&rebuilt);
    let bound = (height(&tree) + 1) * (4 * (multiset_height(&rebuilt) + 1) + 1);
    assert!(new_multiset_nodes(&rebuilt, &tree) <= bound);
}

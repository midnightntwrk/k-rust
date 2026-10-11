//! Model tests of the persistent edits: each against a `Vec` (positional edits) or a
//! `BTreeMap` multiset (ordered edits), with the operands checked unchanged afterwards, the
//! nodes the result does not share with them counted, and random histories of edits whose
//! every version is checked against its model at the end.

use std::{collections::BTreeMap, collections::HashSet, sync::Arc};

use proptest::prelude::*;

use super::{DEFAULT, Entry, check_invariants, choices, entries, shaped};
use crate::term::chunked::{Chunked, Item, Node, multiset::Multiset, variables::Variables};

pub(super) fn entry() -> impl Strategy<Value = Entry> {
    (0u8..40, any::<u8>()).prop_map(|(key, value)| Entry { key, value })
}

/// The height of a tree's root; 0 for the empty tree.
pub(super) fn height<I: Item, const B: usize>(tree: &Chunked<I, B>) -> usize {
    tree.root.as_ref().map_or(0, |root| root.height())
}

fn collect_nodes<I: Item>(node: &Arc<Node<I>>, into: &mut HashSet<*const Node<I>>) {
    into.insert(Arc::as_ptr(node));
    if let Node::Internal { children, .. } = &**node {
        for child in children {
            collect_nodes(child, into);
        }
    }
}

/// The number of nodes of `tree` that none of `sources` holds: a node one of them holds is
/// shared with its whole subtree and not entered.
pub(super) fn unshared<I: Item, const B: usize>(
    tree: &Chunked<I, B>,
    sources: &[&Chunked<I, B>],
) -> usize {
    let mut known = HashSet::new();
    for source in sources {
        if let Some(root) = &source.root {
            collect_nodes(root, &mut known);
        }
    }
    let mut count = 0;
    let mut pending: Vec<&Arc<Node<I>>> = tree.root.iter().collect();
    while let Some(node) = pending.pop() {
        if known.contains(&Arc::as_ptr(node)) {
            continue;
        }
        count += 1;
        if let Node::Internal { children, .. } = &**node {
            pending.extend(children);
        }
    }
    count
}

/// The checks every result of an edit passes: the invariant, its model, and a hash and an
/// equality that are those of the bulk-loaded model.
pub(super) fn check<const B: usize>(tree: &Chunked<Entry, B>, model: &[Entry]) {
    check_invariants(tree);
    assert_eq!(tree.to_vec(), model);
    let loaded = Chunked::<Entry, B>::from_vec(model.to_vec());
    assert_eq!(tree.hash_value(), loaded.hash_value());
    assert_eq!(tree, &loaded);
    check_variables(tree, model);
}

/// Every node's multiset of variables keeps its own invariant (the edits change it by
/// difference), and the root's counts each variable once per item of the model mentioning it;
/// the root's variable set, a view of that multiset, holds the variables of the model.
fn check_variables<const B: usize>(tree: &Chunked<Entry, B>, model: &[Entry]) {
    let mut pending: Vec<&Arc<Node<Entry>>> = tree.root.iter().collect();
    while let Some(node) = pending.pop() {
        check_invariants(node.summary().group.entries());
        if let Node::Internal { children, .. } = &**node {
            pending.extend(children);
        }
    }
    let mut counts: BTreeMap<u8, usize> = BTreeMap::new();
    for item in model {
        for variable in item.variables() {
            *counts.entry(variable).or_insert(0) += 1;
        }
    }
    let root = tree
        .summary()
        .map_or_else(Multiset::new, |summary| summary.group.clone());
    assert!(
        root.entries()
            .iter()
            .map(|entry| (&entry.element, &entry.count))
            .eq(counts.iter())
    );
    let set = Variables::of_multiset(&root);
    assert!(set.entries().shares_root(root.entries()));
    assert_eq!(set.to_btree_set(), counts.into_keys().collect());
}

/// The items of a multiset model in order, each as often as it is counted.
fn flatten(model: &BTreeMap<Entry, usize>) -> Vec<Entry> {
    model
        .iter()
        .flat_map(|(item, count)| std::iter::repeat_n(item.clone(), *count))
        .collect()
}

fn multiset(items: &[Entry]) -> BTreeMap<Entry, usize> {
    let mut model = BTreeMap::new();
    for item in items {
        *model.entry(item.clone()).or_insert(0) += 1;
    }
    model
}

/// An ordered tree of the items, of a random shape, and their multiset.
fn ordered<const B: usize>(
    mut items: Vec<Entry>,
    shape: Vec<u8>,
) -> (Chunked<Entry, B>, BTreeMap<Entry, usize>) {
    items.sort();
    let model = multiset(&items);
    (shaped(items, shape), model)
}

// A one-item insertion copies, at each level, the node on the path and at most one half split
// off it, and may add a root: at most `2 (h + 1) + 1` new nodes for a tree of height `h`.
fn insert_at<const B: usize>(items: Vec<Entry>, shape: Vec<u8>, at: usize, item: Entry) {
    let tree = shaped::<Entry, B>(items.clone(), shape);
    let index = at % (items.len() + 1);
    let inserted = tree.insert_at(index, item.clone());
    let mut model = items.clone();
    model.insert(index, item);
    check(&inserted, &model);
    check(&tree, &items);
    assert!(unshared(&inserted, &[&tree]) <= 2 * (height(&tree) + 1) + 1);
}

// A one-item removal copies, at each level, the node on the path, or concatenates it with a
// sibling into one or two nodes: at most `2 (h + 1)` new nodes.
fn remove_at<const B: usize>(items: Vec<Entry>, shape: Vec<u8>, at: usize) {
    if items.is_empty() {
        return;
    }
    let tree = shaped::<Entry, B>(items.clone(), shape);
    let index = at % items.len();
    let (removed, item) = tree.remove_at(index);
    let mut model = items.clone();
    assert_eq!(item, model.remove(index));
    check(&removed, &model);
    check(&tree, &items);
    assert!(unshared(&removed, &[&tree]) <= 2 * (height(&tree) + 1));
}

// A join copies, at each level from the taller root down to the shorter tree's height, one
// node and at most one half split off it, and may add a root.
fn join<const B: usize>(left: Vec<Entry>, right: Vec<Entry>, shapes: (Vec<u8>, Vec<u8>)) {
    let a = shaped::<Entry, B>(left.clone(), shapes.0);
    let b = shaped::<Entry, B>(right.clone(), shapes.1);
    let joined = a.join(&b);
    check(&joined, &[left.clone(), right.clone()].concat());
    check(&a, &left);
    check(&b, &right);
    let levels = height(&a).abs_diff(height(&b)) + 1;
    assert!(unshared(&joined, &[&a, &b]) <= 2 * levels + 1);
}

// Each side of a split is built level by level: at a level of height `l`, at most one node
// over the children beside the path, joined with the side built below, whose height is at
// least `l - 2` when that node exists. Each join copies at most `2 (d + 1) + 1` nodes for a
// height difference `d`, and the differences sum to at most `2h` over the levels, so a side
// holds at most `8 (h + 1)` nodes not in the tree it was split from.
fn split_at<const B: usize>(items: Vec<Entry>, shape: Vec<u8>, at: usize) {
    let tree = shaped::<Entry, B>(items.clone(), shape);
    let index = at % (items.len() + 1);
    let (left, right) = tree.split_at(index);
    check(&left, &items[..index]);
    check(&right, &items[index..]);
    check(&tree, &items);
    let bound = 8 * (height(&tree) + 1);
    assert!(unshared(&left, &[&tree]) <= bound);
    assert!(unshared(&right, &[&tree]) <= bound);
    check(&left.join(&right), &items);
}

fn partition_point<const B: usize>(mut items: Vec<Entry>, shape: Vec<u8>, key: u8) {
    items.sort();
    let tree = shaped::<Entry, B>(items.clone(), shape);
    assert_eq!(
        tree.partition_point(|item| item.key <= key),
        items.partition_point(|item| item.key <= key)
    );
    assert_eq!(
        tree.partition_point(|item| item.key < key),
        items.partition_point(|item| item.key < key)
    );
}

fn split_at_key<const B: usize>(items: Vec<Entry>, shape: Vec<u8>, key: u8) {
    let (tree, model) = ordered::<B>(items, shape);
    let (below, rest) = tree.split_at_key(&key);
    let all = flatten(&model);
    let (expected_below, expected_rest): (Vec<_>, Vec<_>) =
        all.iter().cloned().partition(|item| item.key < key);
    check(&below, &expected_below);
    check(&rest, &expected_rest);
    check(&tree, &all);
}

fn insert<const B: usize>(items: Vec<Entry>, shape: Vec<u8>, item: Entry) {
    let (tree, mut model) = ordered::<B>(items, shape);
    let before = flatten(&model);
    let inserted = tree.insert(item.clone());
    *model.entry(item).or_insert(0) += 1;
    check(&inserted, &flatten(&model));
    check(&tree, &before);
    assert!(unshared(&inserted, &[&tree]) <= 2 * (height(&tree) + 1) + 1);
}

fn remove<const B: usize>(items: Vec<Entry>, shape: Vec<u8>, pick: usize, absent: Entry) {
    let (tree, mut model) = ordered::<B>(items, shape);
    let before = flatten(&model);
    // An item the tree holds, when it holds any, and one it may not hold.
    let present = (!before.is_empty()).then(|| before[pick % before.len()].clone());
    for item in present.into_iter().chain([absent]) {
        let removed = tree.remove(&item);
        match model.get(&item) {
            None => assert!(removed.is_none()),
            Some(&count) => {
                let mut expected = model.clone();
                if count == 1 {
                    expected.remove(&item);
                } else {
                    expected.insert(item.clone(), count - 1);
                }
                let removed = removed.expect("a held item is removed");
                check(&removed, &flatten(&expected));
                assert!(unshared(&removed, &[&tree]) <= 2 * (height(&tree) + 1));
            }
        }
    }
    check(&tree, &before);
    model.clear();
}

fn union<const B: usize>(left: Vec<Entry>, right: Vec<Entry>, shapes: (Vec<u8>, Vec<u8>)) {
    let (a, mut model) = ordered::<B>(left, shapes.0);
    let (b, other) = ordered::<B>(right, shapes.1);
    let (before_a, before_b) = (flatten(&model), flatten(&other));
    let united = a.union(&b);
    for (item, count) in other {
        *model.entry(item).or_insert(0) += count;
    }
    check(&united, &flatten(&model));
    check(&b.union(&a), &flatten(&model));
    check(&a, &before_a);
    check(&b, &before_b);
}

// A union with one item copies what an insertion of it copies, plus the run of children kept
// on either side of the path at each level, which is at most one node per level and side, and
// at most two more nodes per level where a join concatenates or splits: `5 (h + 1) + 1`.
fn union_with_one<const B: usize>(items: Vec<Entry>, shape: Vec<u8>, item: Entry) {
    let (tree, mut model) = ordered::<B>(items, shape);
    let one = Chunked::<Entry, B>::from_vec(vec![item.clone()]);
    let united = tree.union(&one);
    *model.entry(item).or_insert(0) += 1;
    check(&united, &flatten(&model));
    assert!(unshared(&united, &[&tree, &one]) <= 5 * (height(&tree) + 1) + 1);
}

proptest! {
    #[test]
    fn insert_at_matches_the_vec_and_shares_the_rest(items in entries(400), shape in choices(), at in any::<usize>(), item in entry()) {
        insert_at::<5>(items.clone(), shape.clone(), at, item.clone());
        insert_at::<6>(items.clone(), shape.clone(), at, item.clone());
        insert_at::<DEFAULT>(items, shape, at, item);
    }

    #[test]
    fn remove_at_matches_the_vec_and_shares_the_rest(items in entries(400), shape in choices(), at in any::<usize>()) {
        remove_at::<5>(items.clone(), shape.clone(), at);
        remove_at::<6>(items.clone(), shape.clone(), at);
        remove_at::<DEFAULT>(items, shape, at);
    }

    #[test]
    fn join_concatenates_and_shares_both_sides(left in entries(300), right in entries(300), shapes in (choices(), choices())) {
        join::<5>(left.clone(), right.clone(), shapes.clone());
        join::<6>(left.clone(), right.clone(), shapes.clone());
        join::<DEFAULT>(left, right, shapes);
    }

    #[test]
    fn join_of_trees_of_very_different_heights(small in entries(8), large in entries(800), shapes in (choices(), choices()), large_first in any::<bool>()) {
        let (left, right) = if large_first { (large, small) } else { (small, large) };
        join::<5>(left.clone(), right.clone(), shapes.clone());
        join::<DEFAULT>(left, right, shapes);
    }

    #[test]
    fn split_at_cuts_the_vec_and_shares_both_sides(items in entries(400), shape in choices(), at in any::<usize>()) {
        split_at::<5>(items.clone(), shape.clone(), at);
        split_at::<6>(items.clone(), shape.clone(), at);
        split_at::<DEFAULT>(items, shape, at);
    }

    #[test]
    fn partition_point_matches_the_vec(items in entries(300), shape in choices(), key in 0u8..42) {
        partition_point::<5>(items.clone(), shape.clone(), key);
        partition_point::<6>(items.clone(), shape.clone(), key);
        partition_point::<DEFAULT>(items, shape, key);
    }

    #[test]
    fn split_at_key_cuts_the_multiset(items in entries(300), shape in choices(), key in 0u8..42) {
        split_at_key::<5>(items.clone(), shape.clone(), key);
        split_at_key::<6>(items.clone(), shape.clone(), key);
        split_at_key::<DEFAULT>(items, shape, key);
    }

    #[test]
    fn insert_keeps_order_and_repeats(items in entries(300), shape in choices(), item in entry()) {
        insert::<5>(items.clone(), shape.clone(), item.clone());
        insert::<6>(items.clone(), shape.clone(), item.clone());
        insert::<DEFAULT>(items, shape, item);
    }

    #[test]
    fn remove_takes_one_copy_of_an_item(items in entries(300), shape in choices(), pick in any::<usize>(), absent in entry()) {
        remove::<5>(items.clone(), shape.clone(), pick, absent.clone());
        remove::<6>(items.clone(), shape.clone(), pick, absent.clone());
        remove::<DEFAULT>(items, shape, pick, absent);
    }

    #[test]
    fn union_adds_the_multisets(left in entries(300), right in entries(300), shapes in (choices(), choices())) {
        union::<5>(left.clone(), right.clone(), shapes.clone());
        union::<6>(left.clone(), right.clone(), shapes.clone());
        union::<DEFAULT>(left, right, shapes);
    }

    #[test]
    fn union_of_a_large_and_a_small_tree(large in entries(800), small in entries(12), shapes in (choices(), choices())) {
        union::<5>(large.clone(), small.clone(), shapes.clone());
        union::<DEFAULT>(large, small, shapes);
    }

    #[test]
    fn union_with_one_item_shares_the_rest(items in entries(400), shape in choices(), item in entry()) {
        union_with_one::<5>(items.clone(), shape.clone(), item.clone());
        union_with_one::<6>(items.clone(), shape.clone(), item.clone());
        union_with_one::<DEFAULT>(items, shape, item);
    }
}

/// One edit of a history over a pool of versions; the numbers pick versions, positions and
/// counts modulo what is available.
#[derive(Clone, Debug)]
enum Edit {
    InsertAt(usize, usize, Entry),
    RemoveAt(usize, usize),
    Split(usize, usize),
    Join(usize, usize),
    /// `k` removals from one version, then a join with another: the frame of a match.
    Frame(usize, usize, usize, usize),
}

fn edits() -> impl Strategy<Value = Vec<Edit>> {
    let edit = prop_oneof![
        (any::<usize>(), any::<usize>(), entry()).prop_map(|(v, i, e)| Edit::InsertAt(v, i, e)),
        (any::<usize>(), any::<usize>()).prop_map(|(v, i)| Edit::RemoveAt(v, i)),
        (any::<usize>(), any::<usize>()).prop_map(|(v, i)| Edit::Split(v, i)),
        (any::<usize>(), any::<usize>()).prop_map(|(v, w)| Edit::Join(v, w)),
        (any::<usize>(), any::<usize>(), 1usize..6, any::<usize>())
            .prop_map(|(v, w, k, i)| Edit::Frame(v, w, k, i)),
    ];
    prop::collection::vec(edit, 0..60)
}

/// The largest version a history builds; a join that would exceed it joins the second version
/// with an empty one instead, so that histories of joins stay small.
const LARGEST: usize = 3000;

fn positional_history<const B: usize>(start: Vec<Entry>, shape: Vec<u8>, history: &[Edit]) {
    let mut versions = vec![(shaped::<Entry, B>(start.clone(), shape), start)];
    for edit in history {
        let pick = |v: &usize| v % versions.len();
        let mut made = Vec::new();
        match edit {
            Edit::InsertAt(v, i, item) => {
                let (tree, model) = &versions[pick(v)];
                let index = i % (model.len() + 1);
                let mut model = model.clone();
                model.insert(index, item.clone());
                made.push((tree.insert_at(index, item.clone()), model));
            }
            Edit::RemoveAt(v, i) => {
                let (tree, model) = &versions[pick(v)];
                if !model.is_empty() {
                    let index = i % model.len();
                    let mut model = model.clone();
                    model.remove(index);
                    made.push((tree.remove_at(index).0, model));
                }
            }
            Edit::Split(v, i) => {
                let (tree, model) = &versions[pick(v)];
                let index = i % (model.len() + 1);
                let (left, right) = tree.split_at(index);
                made.push((left, model[..index].to_vec()));
                made.push((right, model[index..].to_vec()));
            }
            Edit::Join(v, w) => {
                let (left, left_model) = &versions[pick(v)];
                let (right, right_model) = &versions[pick(w)];
                if left_model.len() + right_model.len() <= LARGEST {
                    let model = [left_model.clone(), right_model.clone()].concat();
                    made.push((left.join(right), model));
                } else {
                    made.push((right.join(&Chunked::new()), right_model.clone()));
                }
            }
            Edit::Frame(v, w, k, i) => {
                let (tree, model) = &versions[pick(v)];
                let (mut tree, mut model) = (tree.clone(), model.clone());
                for removal in 0..*k {
                    if model.is_empty() {
                        break;
                    }
                    let index = i.wrapping_mul(removal + 1) % model.len();
                    model.remove(index);
                    tree = tree.remove_at(index).0;
                }
                let (other, other_model) = &versions[pick(w)];
                if model.len() + other_model.len() <= LARGEST {
                    model.extend(other_model.iter().cloned());
                    tree = tree.join(other);
                }
                made.push((tree, model));
            }
        }
        for (tree, model) in &made {
            check_invariants(tree);
            assert_eq!(&tree.to_vec(), model);
        }
        versions.extend(made);
    }
    // Every version, old ones included, still holds its items.
    for (tree, model) in &versions {
        check(tree, model);
    }
}

/// One edit of a history of ordered versions.
#[derive(Clone, Debug)]
enum OrderedEdit {
    Insert(usize, Entry),
    Remove(usize, usize),
    SplitAtKey(usize, u8),
    /// Cut at a key and join the two parts again: the version itself.
    Rejoin(usize, u8),
    Union(usize, usize),
    /// `k` removals from one version, then a union with another.
    Frame(usize, usize, usize, usize),
}

fn ordered_edits() -> impl Strategy<Value = Vec<OrderedEdit>> {
    let edit = prop_oneof![
        (any::<usize>(), entry()).prop_map(|(v, e)| OrderedEdit::Insert(v, e)),
        (any::<usize>(), any::<usize>()).prop_map(|(v, i)| OrderedEdit::Remove(v, i)),
        (any::<usize>(), 0u8..42).prop_map(|(v, k)| OrderedEdit::SplitAtKey(v, k)),
        (any::<usize>(), 0u8..42).prop_map(|(v, k)| OrderedEdit::Rejoin(v, k)),
        (any::<usize>(), any::<usize>()).prop_map(|(v, w)| OrderedEdit::Union(v, w)),
        (any::<usize>(), any::<usize>(), 1usize..6, any::<usize>())
            .prop_map(|(v, w, k, i)| OrderedEdit::Frame(v, w, k, i)),
    ];
    prop::collection::vec(edit, 0..60)
}

fn ordered_history<const B: usize>(
    starts: (Vec<Entry>, Vec<Entry>),
    shapes: (Vec<u8>, Vec<u8>),
    history: &[OrderedEdit],
) {
    let mut versions = vec![
        ordered::<B>(starts.0, shapes.0),
        ordered::<B>(starts.1, shapes.1),
    ];
    let size = |model: &BTreeMap<Entry, usize>| model.values().sum::<usize>();
    for edit in history {
        let pick = |v: &usize| v % versions.len();
        let mut made = Vec::new();
        match edit {
            OrderedEdit::Insert(v, item) => {
                let (tree, model) = &versions[pick(v)];
                let mut model = model.clone();
                *model.entry(item.clone()).or_insert(0) += 1;
                made.push((tree.insert(item.clone()), model));
            }
            OrderedEdit::Remove(v, i) => {
                let (tree, model) = &versions[pick(v)];
                let items = flatten(model);
                if !items.is_empty() {
                    let item = &items[i % items.len()];
                    let mut model = model.clone();
                    let count = model.get_mut(item).expect("a held item");
                    *count -= 1;
                    if *count == 0 {
                        model.remove(item);
                    }
                    made.push((tree.remove(item).expect("a held item"), model));
                }
            }
            OrderedEdit::SplitAtKey(v, key) => {
                let (tree, model) = &versions[pick(v)];
                let (below, rest) = tree.split_at_key(key);
                let (low, high): (BTreeMap<_, _>, BTreeMap<_, _>) = model
                    .iter()
                    .map(|(item, count)| (item.clone(), *count))
                    .partition(|(item, _)| item.key < *key);
                made.push((below, low));
                made.push((rest, high));
            }
            OrderedEdit::Rejoin(v, key) => {
                let (tree, model) = &versions[pick(v)];
                let (below, rest) = tree.split_at_key(key);
                made.push((below.join(&rest), model.clone()));
            }
            OrderedEdit::Union(v, w) => {
                let (left, left_model) = &versions[pick(v)];
                let (right, right_model) = &versions[pick(w)];
                if size(left_model) + size(right_model) <= LARGEST {
                    let mut model = left_model.clone();
                    for (item, count) in right_model {
                        *model.entry(item.clone()).or_insert(0) += count;
                    }
                    made.push((left.union(right), model));
                }
            }
            OrderedEdit::Frame(v, w, k, i) => {
                let (tree, model) = &versions[pick(v)];
                let (mut tree, mut model) = (tree.clone(), model.clone());
                for removal in 0..*k {
                    let items = flatten(&model);
                    if items.is_empty() {
                        break;
                    }
                    let item = &items[i.wrapping_mul(removal + 1) % items.len()];
                    tree = tree.remove(item).expect("a held item");
                    let count = model.get_mut(item).expect("a held item");
                    *count -= 1;
                    if *count == 0 {
                        model.remove(item);
                    }
                }
                let (other, other_model) = &versions[pick(w)];
                if size(&model) + size(other_model) <= LARGEST {
                    for (item, count) in other_model {
                        *model.entry(item.clone()).or_insert(0) += count;
                    }
                    tree = tree.union(other);
                }
                made.push((tree, model));
            }
        }
        for (tree, model) in &made {
            check_invariants(tree);
            assert_eq!(tree.to_vec(), flatten(model));
        }
        versions.extend(made);
    }
    for (tree, model) in &versions {
        check(tree, &flatten(model));
    }
}

proptest! {
    #[test]
    fn every_version_of_a_positional_history_keeps_its_items(start in entries(300), shape in choices(), history in edits()) {
        positional_history::<5>(start.clone(), shape.clone(), &history);
        positional_history::<6>(start.clone(), shape.clone(), &history);
        positional_history::<DEFAULT>(start, shape, &history);
    }

    #[test]
    fn every_version_of_an_ordered_history_keeps_its_items(starts in (entries(300), entries(300)), shapes in (choices(), choices()), history in ordered_edits()) {
        ordered_history::<5>(starts.clone(), shapes.clone(), &history);
        ordered_history::<6>(starts.clone(), shapes.clone(), &history);
        ordered_history::<DEFAULT>(starts, shapes, &history);
    }
}

/// Removing every item one at a time from either end, or from the middle, keeps the invariant
/// down to the empty tree, and the tree shrinks back to a single leaf.
#[test]
fn removing_every_item_keeps_the_invariant() {
    let items: Vec<Entry> = (0..500u32)
        .map(|n| Entry {
            key: (n % 40) as u8,
            value: (n % 251) as u8,
        })
        .collect();
    for end in 0..3 {
        let mut tree = Chunked::<Entry, 5>::from_vec(items.clone());
        let mut model = items.clone();
        while !model.is_empty() {
            let index = match end {
                0 => 0,
                1 => model.len() - 1,
                _ => model.len() / 2,
            };
            model.remove(index);
            tree = tree.remove_at(index).0;
            check_invariants(&tree);
            assert_eq!(tree.len(), model.len());
            if model.len() <= 5 {
                assert_eq!(
                    height(&tree),
                    0,
                    "a sequence of at most B items is one leaf"
                );
            }
        }
        assert!(tree.root.is_none());
    }
}

/// A split at the boundary of two subtrees keeps both whole: no side copies more nodes than a
/// split anywhere else may, whichever level the boundary is at. The tree is large enough for
/// each child of the root to hold far more nodes than that bound.
#[test]
fn a_split_at_a_subtree_boundary_shares_the_subtrees() {
    let items: Vec<Entry> = (0..5000u32)
        .map(|n| Entry {
            key: (n / 125) as u8,
            value: (n % 251) as u8,
        })
        .collect();
    let tree = Chunked::<Entry, 5>::from_vec(items.clone());
    let bound = 8 * (height(&tree) + 1);
    // The positions where a child of the root, or a child of one of them, begins or ends.
    let mut boundaries = vec![0];
    let Some(Node::Internal { children, .. }) = tree.root.as_deref() else {
        panic!("5000 items fill more than one leaf");
    };
    let mut position = 0;
    for child in children {
        if let Node::Internal { children, .. } = &**child {
            for grandchild in children {
                position += grandchild.summary().count;
                boundaries.push(position);
            }
        }
    }
    assert_eq!(position, items.len());
    for index in boundaries {
        let (left, right) = tree.split_at(index);
        check(&left, &items[..index]);
        check(&right, &items[index..]);
        assert!(unshared(&left, &[&tree]) <= bound);
        assert!(unshared(&right, &[&tree]) <= bound);
    }
}

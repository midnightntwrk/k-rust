//! Tests of the shared variable sets against a `BTreeSet`, and of the work an edit of an item
//! tree does on its nodes' multisets of variables, counted in multiset entries.

use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use proptest::prelude::*;

use super::edit::{height, unshared};
use super::{DEFAULT, VARIABLES, check_invariants, choices, fx_hash, shaped};
use crate::term::{
    VariableLookup,
    chunked::{
        Chunked, Item, Node,
        multiset::{ENTRY_UPDATES, Multiset},
        variables::Variables,
    },
};

type Set<const B: usize> = Variables<u8, B>;

/// Whether `set`, made from `multiset`, is its view as it must be: sharing the multiset's tree
/// when it has more than `B` elements, holding a copy of the elements otherwise.
pub(super) fn views<V: Ord + Clone + std::hash::Hash + std::fmt::Debug, const B: usize>(
    set: &Variables<V, B>,
    multiset: &Multiset<V, B>,
) -> bool {
    set.iter().eq(multiset.elements())
        && set
            .tree()
            .is_some_and(|tree| tree.shares_root(multiset.entries()))
            == (multiset.len() > B)
}

/// The checks every set passes: its backing (a tree exactly when it holds more than `B`
/// variables), its tree's invariant, and every reading against the model.
fn check_set<const B: usize>(set: &Set<B>, model: &BTreeSet<u8>) {
    assert_eq!(set.tree().is_some(), model.len() > B);
    if let Some(tree) = set.tree() {
        check_invariants(tree);
    }
    assert!(set.iter().eq(model.iter()));
    assert!(set.iter().rev().eq(model.iter().rev()));
    assert_eq!(set.iter().len(), model.len());
    assert_eq!(set.len(), model.len());
    assert_eq!(set.is_empty(), model.is_empty());
    for variable in 0..64 {
        assert_eq!(set.contains(&variable), model.contains(&variable));
    }
    assert_eq!(&set.to_btree_set(), model);
    assert_eq!(format!("{set:?}"), format!("{model:?}"));
    assert_eq!(set, &Set::<B>::of(model.iter().copied()));
    let other: BTreeSet<u8> = model.symmetric_difference(&[7].into()).copied().collect();
    assert_ne!(set, &Set::<B>::of(other));
}

/// One step of a history of sets: a new set, a view of a multiset, an insertion into an earlier
/// version, or the union of earlier versions.
#[derive(Clone, Debug)]
enum Step {
    Of(Vec<u8>),
    View(Vec<u8>),
    Insert(usize, u8),
    Union(Vec<usize>),
}

fn step() -> impl Strategy<Value = Step> {
    prop_oneof![
        prop::collection::vec(0u8..64, 0..40).prop_map(Step::Of),
        prop::collection::vec(0u8..64, 0..40).prop_map(Step::View),
        (any::<usize>(), 0u8..64).prop_map(|(which, variable)| Step::Insert(which, variable)),
        prop::collection::vec(any::<usize>(), 0..5).prop_map(Step::Union),
    ]
}

fn history<const B: usize>(steps: &[Step], pairs: &[(usize, usize)]) {
    let mut versions: Vec<(Set<B>, BTreeSet<u8>)> = vec![(Set::new(), BTreeSet::new())];
    for step in steps {
        let pick = |which: usize| &versions[which % versions.len()];
        let next = match step {
            Step::Of(variables) => (
                Set::of(variables.iter().copied()),
                variables.iter().copied().collect(),
            ),
            Step::View(variables) => {
                let multiset = Multiset::<u8, B>::of(variables.iter().copied());
                let set = Set::of_multiset(&multiset);
                assert!(views(&set, &multiset));
                (set, variables.iter().copied().collect())
            }
            Step::Insert(which, variable) => {
                let (set, model) = pick(*which);
                let inserted = set.insert(variable);
                // Inserting a variable the set holds keeps its handle.
                assert_eq!(inserted.shares_handle(set), model.contains(variable));
                let mut model = model.clone();
                model.insert(*variable);
                (inserted, model)
            }
            Step::Union(which) => {
                let operands: Vec<&(Set<B>, BTreeSet<u8>)> =
                    which.iter().map(|&which| pick(which)).collect();
                let union = Set::union_all(operands.iter().map(|(set, _)| set));
                let model: BTreeSet<u8> = operands
                    .iter()
                    .flat_map(|(_, model)| model.iter().copied())
                    .collect();
                if let [(left, _), (right, _)] = operands[..] {
                    assert_eq!(left.union(right), union);
                }
                check_union_sharing(&operands, &union, &model);
                (union, model)
            }
        };
        check_set(&next.0, &next.1);
        versions.push(next);
    }
    for (set, model) in &versions {
        check_set(set, model);
    }
    for &(left, right) in pairs {
        let (left, left_model) = &versions[left % versions.len()];
        let (right, right_model) = &versions[right % versions.len()];
        let subset = left_model.is_subset(right_model);
        let disjoint = left_model.is_disjoint(right_model);
        assert_eq!(left.is_subset(right), subset);
        assert_eq!(left.is_subset(right_model), subset);
        assert_eq!(left.is_disjoint(right), disjoint);
        assert_eq!(left.is_disjoint(right_model), disjoint);
        let lookup: &dyn VariableLookup<u8> = right_model;
        assert_eq!(left.is_subset(lookup), subset);
        assert_eq!(left.is_disjoint(lookup), disjoint);
        assert_eq!(left == right, left_model == right_model);
    }
}

/// A union is the handle of its first largest operand with the others' missing variables added:
/// the same handle when nothing is missing, otherwise, when that operand is a tree, at most the
/// nodes that many one-item insertions copy (`2 (h + 1) + 1` each, `h` the result's height).
fn check_union_sharing<const B: usize>(
    operands: &[&(Set<B>, BTreeSet<u8>)],
    union: &Set<B>,
    model: &BTreeSet<u8>,
) {
    let Some(largest) = operands.iter().map(|(set, _)| set.len()).max() else {
        assert!(union.is_empty());
        return;
    };
    let (kept, kept_model) = operands
        .iter()
        .find(|(set, _)| set.len() == largest)
        .expect("a largest operand");
    let missing = model.len() - kept_model.len();
    if missing == 0 {
        assert!(union.shares_handle(kept));
    }
    // A union into a tree copies paths; one of sets of at most `B` variables is a new set.
    if let (Some(union), Some(kept)) = (union.tree(), kept.tree()) {
        let bound = missing * (2 * (height(union) + 1) + 1);
        assert!(unshared(union, &[kept]) <= bound);
    }
}

/// A lookup that counts the variables it is asked about or shows.
struct Counted<'a> {
    set: &'a BTreeSet<u8>,
    lookups: Cell<usize>,
}

impl VariableLookup<u8> for Counted<'_> {
    fn variable_count(&self) -> usize {
        self.set.len()
    }

    fn holds_variable(&self, variable: &u8) -> bool {
        self.lookups.set(self.lookups.get() + 1);
        self.set.contains(variable)
    }

    fn any_variable(&self, test: &mut dyn FnMut(&u8) -> bool) -> bool {
        self.set.iter().any(|variable| {
            self.lookups.set(self.lookups.get() + 1);
            test(variable)
        })
    }
}

// `is_disjoint` touches at most the smaller set's variables; `is_subset` at most the set's own,
// and none when it holds more than the other.
fn lookups_follow_the_smaller_set<const B: usize>(left: &[u8], right: &[u8]) {
    let set = Set::<B>::of(left.iter().copied());
    let model: BTreeSet<u8> = right.iter().copied().collect();
    let counted = Counted {
        set: &model,
        lookups: Cell::new(0),
    };
    set.is_disjoint(&counted);
    assert!(counted.lookups.get() <= set.len().min(model.len()));
    counted.lookups.set(0);
    set.is_subset(&counted);
    if set.len() > model.len() {
        assert_eq!(counted.lookups.get(), 0);
    } else {
        assert!(counted.lookups.get() <= set.len());
    }
}

proptest! {
    #[test]
    fn a_variable_set_follows_its_model(
        steps in prop::collection::vec(step(), 0..30),
        pairs in prop::collection::vec((any::<usize>(), any::<usize>()), 0..20),
    ) {
        history::<5>(&steps, &pairs);
        history::<6>(&steps, &pairs);
        history::<VARIABLES>(&steps, &pairs);
    }

    #[test]
    fn set_comparisons_look_up_the_smaller_set(
        left in prop::collection::vec(0u8..64, 0..40),
        right in prop::collection::vec(0u8..64, 0..40),
    ) {
        lookups_follow_the_smaller_set::<5>(&left, &right);
        lookups_follow_the_smaller_set::<VARIABLES>(&left, &right);
    }
}

#[test]
fn a_union_keeps_the_handle_of_the_first_largest_operand() {
    let small = Set::<5>::of([1, 2]);
    let large = Set::<5>::of(0..40);
    let tie = Set::<5>::of(10..50);
    assert!(large.union(&small).shares_handle(&large));
    assert!(small.union(&large).shares_handle(&large));
    assert!(large.union(&large).shares_handle(&large));
    let union = Set::union_all([&small, &large, &tie]);
    // The tie's variables 40..50 are inserted into the first largest operand's tree.
    assert!(!union.shares_handle(&large));
    assert!(!union.shares_handle(&tie));
    assert_eq!(union, Set::of(0..50));
    assert!(Set::union_all([&small]).shares_handle(&small));
    assert!(Set::<5>::union_all([]).is_empty());
    // Sets of at most `B` variables: the larger one's handle when it holds the other's
    // variables, a merged set otherwise, which becomes a tree past `B`.
    let within = Set::<5>::of([1, 2, 3]);
    assert!(within.union(&small).shares_handle(&within));
    assert!(small.union(&within).shares_handle(&within));
    let past = within.union(&Set::of([0, 4, 5]));
    assert!(past.tree().is_some());
    assert_eq!(past, Set::of(0..6));
    let merged = small.union(&Set::of([0, 4]));
    assert!(merged.tree().is_none());
    assert_eq!(merged, Set::of([0, 1, 2, 4]));
}

/// An item mentioning a few variables of a large domain, so that a node's multiset is much
/// larger than an item's. Ordered by key first, as an ordered collection's items are.
#[derive(Clone, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
struct Mentions {
    key: u32,
    variables: Vec<u32>,
}

impl Item for Mentions {
    type Key = u32;
    type Summary = ();
    type Group = Multiset<u32, 5>;

    fn key(&self) -> &u32 {
        &self.key
    }

    fn hash64(&self) -> u64 {
        fx_hash(self)
    }

    fn summary(&self) {}

    fn group(&self) -> Multiset<u32, 5> {
        Multiset::of(self.variables.iter().copied())
    }
}

/// Items with distinct keys, each mentioning up to four distinct variables among 100,000.
fn mentions(max_len: usize) -> impl Strategy<Value = Vec<Mentions>> {
    prop::collection::vec(
        prop::collection::btree_set(0u32..100_000, 0..5),
        50..max_len,
    )
    .prop_map(|sets| {
        sets.into_iter()
            .enumerate()
            .map(|(key, variables)| Mentions {
                key: u32::try_from(key).expect("few items"),
                variables: variables.into_iter().collect(),
            })
            .collect()
    })
}

fn mention(variables: &BTreeSet<u32>) -> Mentions {
    Mentions {
        key: u32::MAX,
        variables: variables.iter().copied().collect(),
    }
}

/// The variable counts of `items`, each the number of items that mention the variable.
fn counts(items: &[Mentions]) -> BTreeMap<u32, usize> {
    let mut counts = BTreeMap::new();
    for item in items {
        for variable in &item.variables {
            *counts.entry(*variable).or_insert(0) += 1;
        }
    }
    counts
}

/// The checks of an edited tree of mentions: the invariant (every node's multiset is the fold
/// of its items'), every multiset's own invariant, and the root's multiset and variable set
/// against the model.
fn check_mentions<const B: usize>(tree: &Chunked<Mentions, B>, model: &[Mentions]) {
    check_invariants(tree);
    assert_eq!(tree.to_vec(), model);
    let mut pending: Vec<&Arc<Node<Mentions>>> = tree.root.iter().collect();
    while let Some(node) = pending.pop() {
        check_invariants(node.summary().group.entries());
        if let Node::Internal { children, .. } = &**node {
            pending.extend(children);
        }
    }
    let root = tree
        .summary()
        .map_or_else(Multiset::new, |summary| summary.group.clone());
    let expected = counts(model);
    assert!(
        root.entries()
            .iter()
            .map(|entry| (&entry.element, &entry.count))
            .eq(expected.iter())
    );
    let set = Variables::of_multiset(&root);
    assert!(set.iter().eq(expected.keys()));
}

/// A leaf of a tree: the position of its first item, its width, and its place among its
/// parent's children (slot and width), absent for a root leaf.
#[derive(Clone, Copy)]
struct Leaf {
    position: usize,
    width: usize,
    parent: Parent,
}

/// A node's slot among its parent's children and their number; `None` for the root.
type Parent = Option<(usize, usize)>;

/// The leaves of `tree`, in order.
fn leaves<I: Item, const B: usize>(tree: &Chunked<I, B>) -> Vec<Leaf> {
    let mut found = Vec::new();
    let mut position = 0;
    let mut pending: Vec<(&Arc<Node<I>>, Parent)> =
        tree.root.iter().map(|root| (root, None)).collect();
    while let Some((node, parent)) = pending.pop() {
        match &**node {
            Node::Leaf { items, .. } => {
                found.push(Leaf {
                    position,
                    width: items.len(),
                    parent,
                });
                position += items.len();
            }
            Node::Internal { children, .. } => pending.extend(
                children
                    .iter()
                    .enumerate()
                    .rev()
                    .map(|(slot, child)| (child, Some((slot, children.len())))),
            ),
        }
    }
    found
}

/// The index, among `leaves`, of the leaf picked by `pick` among those satisfying `fits`.
fn some_leaf(leaves: &[Leaf], pick: usize, fits: impl Fn(&Leaf) -> bool) -> Option<usize> {
    let candidates: Vec<usize> = (0..leaves.len()).filter(|&i| fits(&leaves[i])).collect();
    (!candidates.is_empty()).then(|| candidates[pick % candidates.len()])
}

/// The multiset entries `edit` creates, changes or removes.
fn entry_updates<T>(edit: impl FnOnce() -> T) -> (T, usize) {
    ENTRY_UPDATES.with(|count| count.set(0));
    let result = edit();
    (result, ENTRY_UPDATES.with(Cell::get))
}

/// The variables `items` mention, with repeats: the weight of their multisets.
fn weight(items: &[Mentions]) -> usize {
    items.iter().map(|item| item.variables.len()).sum()
}

/// The entry updates of packing `contents` into a node: none when they fit, otherwise the
/// multisets of all of them (to weigh the two halves), the fold of the lighter half, and its
/// subtraction from the whole.
fn pack_updates<const B: usize>(contents: &[Mentions]) -> usize {
    if contents.len() <= B {
        return 0;
    }
    let (left, right) = contents.split_at(contents.len().div_ceil(2));
    weight(contents) + 2 * weight(left).min(weight(right))
}

// Inserting an item that mentions `d` variables into a leaf with room changes no width: the
// item's own multiset is `d` entries, and each of the `h + 1` copied nodes adds those `d`
// entries to its multiset (or its own entries to the item's, when it holds fewer): at most
// `d (h + 2)` entry updates, whatever the number of variables below the copied nodes.
//
// Into a full leaf whose parent has room, the leaf splits in two (`pack_updates`): work
// proportional to the leaf's mentions, from the lighter half for the halves' multisets.
fn insertion<const B: usize>(model: Vec<Mentions>, shape: Vec<u8>, pick: usize, item: &Mentions) {
    let tree: Chunked<Mentions, B> = shaped(model.clone(), shape);
    let all = leaves(&tree);
    let d = item.variables.len();
    let h = height(&tree);
    for full in [false, true] {
        let Some(index) = some_leaf(&all, pick, |leaf| {
            if full {
                leaf.width == B && leaf.parent.is_some_and(|(_, width)| width < B)
            } else {
                leaf.width < B
            }
        }) else {
            continue;
        };
        let leaf = all[index];
        // A position before one of the leaf's items: the position after its last item is the
        // first of the next leaf's.
        let at = leaf.position + pick % leaf.width;
        let (inserted, updates) = entry_updates(|| tree.insert_at(at, item.clone()));
        let mut expected = model.clone();
        expected.insert(at, item.clone());
        check_mentions(&inserted, &expected);
        let split = pack_updates::<B>(&expected[leaf.position..=leaf.position + leaf.width]);
        assert!(
            updates <= d * (h + 2) + split,
            "{updates} entry updates for {d} variables at height {h} (split {split})"
        );
    }
}

// Removing an item that mentions `d` variables from a leaf above the minimum fill changes no
// width: `d` entries for the item's multiset and `d` per copied node. From a leaf at the
// minimum fill whose parent is above it, the leaf is concatenated with its next sibling (its
// previous one when it is the last child): the lighter of the two multisets is added to the
// heavier, and the concatenation is packed (`pack_updates`).
fn removal<const B: usize>(model: Vec<Mentions>, shape: Vec<u8>, pick: usize) {
    let tree: Chunked<Mentions, B> = shaped(model.clone(), shape);
    let all = leaves(&tree);
    let h = height(&tree);
    let min = Chunked::<Mentions, B>::MIN_FILL;
    for underflow in [false, true] {
        let Some(index) = some_leaf(&all, pick, |leaf| {
            if underflow {
                leaf.width == min && leaf.parent.is_some_and(|(_, width)| width > min)
            } else {
                leaf.width > min
            }
        }) else {
            continue;
        };
        let leaf = all[index];
        let at = leaf.position + pick % leaf.width;
        let d = model[at].variables.len();
        let ((removed, item), updates) = entry_updates(|| tree.remove_at(at));
        assert_eq!(item, model[at]);
        let mut expected = model.clone();
        expected.remove(at);
        check_mentions(&removed, &expected);
        let merge = match leaf.parent {
            Some((slot, width)) if underflow => {
                let (first, second) = if slot + 1 < width {
                    (leaf, all[index + 1])
                } else {
                    (all[index - 1], leaf)
                };
                // The two leaves' items after the removal.
                let start = first.position;
                let middle =
                    first.position + first.width - usize::from(first.position == leaf.position);
                let end = second.position + second.width - 1;
                weight(&expected[start..middle]).min(weight(&expected[middle..end]))
                    + pack_updates::<B>(&expected[start..end])
            }
            _ => 0,
        };
        assert!(
            updates <= d * (h + 2) + merge,
            "{updates} entry updates for {d} variables at height {h} (merge {merge})"
        );
    }
}

// Replacing one item changes no width: each copied node adds the new item's `d'` entries and
// subtracts the old item's `d`, after building both items' multisets.
fn replacement<const B: usize>(model: Vec<Mentions>, shape: Vec<u8>, pick: usize, item: &Mentions) {
    let tree: Chunked<Mentions, B> = shaped(model.clone(), shape);
    let h = height(&tree);
    let at = pick % model.len();
    let item = Mentions {
        key: model[at].key,
        variables: item.variables.clone(),
    };
    let d = model[at].variables.len() + item.variables.len();
    let (replaced, updates) = entry_updates(|| tree.replace_at(at, item.clone()));
    let mut expected = model;
    expected[at] = item;
    check_mentions(&replaced, &expected);
    assert!(
        updates <= d * (h + 2),
        "{updates} entry updates for {d} variables at height {h}"
    );
}

// Joining a one-item tree after a tree whose last leaf has room merges it into that leaf: each
// node of the right spine adds the item's `d` entries.
fn join_one<const B: usize>(model: Vec<Mentions>, shape: Vec<u8>, item: &Mentions) {
    let tree: Chunked<Mentions, B> = shaped(model.clone(), shape);
    if leaves(&tree).last().is_none_or(|leaf| leaf.width == B) {
        return;
    }
    let h = height(&tree);
    let d = item.variables.len();
    let one = Chunked::from_vec(vec![item.clone()]);
    let (joined, updates) = entry_updates(|| tree.join(&one));
    let mut expected = model;
    expected.push(item.clone());
    check_mentions(&joined, &expected);
    assert!(
        updates <= d * (h + 2),
        "{updates} entry updates for {d} variables at height {h}"
    );
}

proptest! {
    #[test]
    fn an_insertion_updates_the_items_variables_at_each_level(
        model in mentions(400),
        shape in choices(),
        pick in any::<usize>(),
        variables in prop::collection::btree_set(0u32..100_000, 0..5),
    ) {
        let item = mention(&variables);
        insertion::<5>(model.clone(), shape.clone(), pick, &item);
        insertion::<6>(model.clone(), shape.clone(), pick, &item);
        insertion::<DEFAULT>(model, shape, pick, &item);
    }

    #[test]
    fn a_removal_updates_the_items_variables_at_each_level(
        model in mentions(400),
        shape in choices(),
        pick in any::<usize>(),
    ) {
        removal::<5>(model.clone(), shape.clone(), pick);
        removal::<6>(model.clone(), shape.clone(), pick);
        removal::<DEFAULT>(model, shape, pick);
    }

    #[test]
    fn a_replacement_updates_both_items_variables_at_each_level(
        model in mentions(400),
        shape in choices(),
        pick in any::<usize>(),
        variables in prop::collection::btree_set(0u32..100_000, 0..5),
    ) {
        let item = mention(&variables);
        replacement::<5>(model.clone(), shape.clone(), pick, &item);
        replacement::<6>(model.clone(), shape.clone(), pick, &item);
        replacement::<DEFAULT>(model, shape, pick, &item);
    }

    #[test]
    fn a_join_of_one_item_updates_its_variables_along_the_spine(
        model in mentions(400),
        shape in choices(),
        variables in prop::collection::btree_set(0u32..100_000, 0..5),
    ) {
        let item = mention(&variables);
        join_one::<5>(model.clone(), shape.clone(), &item);
        join_one::<6>(model.clone(), shape.clone(), &item);
        join_one::<DEFAULT>(model, shape, &item);
    }
}

// A rebuild that changes one item's key so that it no longer fits where it was replaces it in
// place, takes it out and inserts it where the order puts it: its group work is that of the
// replacement, the removal and the insertion, each a path copy whatever the variables below
// the copied nodes.
fn moving_rebuild<const B: usize>(model: Vec<Mentions>, shape: Vec<u8>, pick: usize) {
    let tree: Chunked<Mentions, B> = shaped(model.clone(), shape);
    let index = pick % model.len();
    let moved = Mentions {
        key: u32::MAX,
        variables: model[index].variables.clone(),
    };
    let wanted = model[index].key;
    let seek = crate::term::chunked::seek::Where::new(
        |_: &crate::term::chunked::NodeSummary<Mentions>| true,
        move |item: &Mentions| item.key == wanted,
    );
    let (rebuilt, updates) = entry_updates(|| tree.rebuild_where(&seek, |_| Some(moved.clone())));
    let mut expected = model;
    expected.remove(index);
    expected.push(moved.clone());
    check_mentions(&rebuilt, &expected);
    let (replaced, replace) = entry_updates(|| tree.replace_at(index, moved.clone()));
    let ((rest, item), remove) = entry_updates(|| replaced.remove_at(index));
    let (_, insert) = entry_updates(|| rest.insert(item));
    assert!(
        updates <= replace + remove + insert,
        "{updates} entry updates, against {replace} + {remove} + {insert} for the path copies"
    );
}

proptest! {
    #[test]
    fn a_rebuild_moving_one_item_does_the_work_of_its_path_copies(
        model in mentions(400),
        shape in choices(),
        pick in any::<usize>(),
    ) {
        moving_rebuild::<5>(model.clone(), shape.clone(), pick);
        moving_rebuild::<6>(model.clone(), shape.clone(), pick);
        moving_rebuild::<DEFAULT>(model, shape, pick);
    }
}

/// A bulk-loaded ordered tree of `n` items at `B = 5`, each mentioning two variables that no
/// other item mentions, so the root's multiset has `2n` entries. Keys are even, so an odd key
/// falls between two items.
fn symbolic(n: u32) -> (Chunked<Mentions, 5>, Vec<Mentions>) {
    let items: Vec<Mentions> = (0..n)
        .map(|i| Mentions {
            key: 2 * i,
            variables: vec![2 * i, 2 * i + 1],
        })
        .collect();
    (Chunked::from_vec(items.clone()), items)
}

/// The entry updates of `edit` on symbolic trees of 1,000, 4,000 and 16,000 items, with each
/// tree's height, after checking each result against its model.
fn tallies(
    edit: impl Fn(&Chunked<Mentions, 5>, &[Mentions]) -> Vec<(Chunked<Mentions, 5>, Vec<Mentions>)>,
) -> Vec<(usize, usize)> {
    [1_000, 4_000, 16_000]
        .into_iter()
        .map(|n| {
            let (tree, model) = symbolic(n);
            let (results, updates) = entry_updates(|| edit(&tree, &model));
            for (result, expected) in &results {
                check_mentions(result, expected);
            }
            (height(&tree), updates)
        })
        .collect()
}

/// An edit whose group work is that of the nodes on one path, each changed by the few items
/// the edit adds or cuts away, costs `a + b (h + 1)` entry updates on a tree of height `h`
/// (`a` for the items' own multisets, `b` per copied node): from one size to the next, the
/// count may grow at most as the number of nodes on a path, `h + 1`, does. Work over the
/// multisets of whole runs of children grows with the variables below them, four times from one
/// size to the next, against a path that grows by a level.
fn assert_grows_with_the_depth(edit: &str, tallies: &[(usize, usize)]) {
    eprintln!("{edit}: (height, entry updates) at n = 1k, 4k, 16k: {tallies:?}");
    for pair in tallies.windows(2) {
        let ((low, fewer), (high, more)) = (pair[0], pair[1]);
        assert!(
            more * (low + 1) <= fewer * (high + 1),
            "{edit}: {fewer} entry updates at height {low}, {more} at height {high}"
        );
    }
}

#[test]
fn a_split_cutting_one_item_away_does_the_work_of_a_path() {
    let first = tallies(|tree, model| {
        let (left, right) = tree.split_at(1);
        vec![(left, model[..1].to_vec()), (right, model[1..].to_vec())]
    });
    assert_grows_with_the_depth("split_at(1)", &first);
    let last = tallies(|tree, model| {
        let (left, right) = tree.split_at(model.len() - 1);
        let cut = model.len() - 1;
        vec![
            (left, model[..cut].to_vec()),
            (right, model[cut..].to_vec()),
        ]
    });
    assert_grows_with_the_depth("split_at(n - 1)", &last);
    let key = tallies(|tree, model| {
        let (left, right) = tree.split_at_key(&model[model.len() - 1].key);
        let cut = model.len() - 1;
        vec![
            (left, model[..cut].to_vec()),
            (right, model[cut..].to_vec()),
        ]
    });
    assert_grows_with_the_depth("split_at_key(last key)", &key);
}

#[test]
fn a_union_with_one_item_does_the_work_of_a_path() {
    let middle = tallies(|tree, model| {
        let at = model.len() / 2;
        let item = Mentions {
            key: model[at].key + 1,
            variables: vec![u32::MAX - 1, u32::MAX],
        };
        let one = Chunked::from_vec(vec![item.clone()]);
        let mut expected = model.to_vec();
        expected.insert(at + 1, item);
        vec![
            (tree.union(&one), expected.clone()),
            (one.union(tree), expected),
        ]
    });
    assert_grows_with_the_depth("union with one item (both ways)", &middle);
}

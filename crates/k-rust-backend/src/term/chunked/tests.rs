//! Model tests of [`Chunked`]: every operation against a `Vec` or `BTreeMap` holding the same
//! items, at branching factors small enough for many levels (5, the smallest allowed, and 6)
//! and at the default. Every tree a test builds goes through [`check_invariants`].

use std::{
    cell::Cell,
    cmp::Ordering,
    collections::{BTreeMap, VecDeque},
    hash::{Hash, Hasher},
    sync::Arc,
};

use proptest::prelude::*;
use rustc_hash::FxHasher;

mod edit;
mod seek;
mod summary;
mod variables;

use super::{
    Chunked, DEFAULT_BRANCHING, Dismantle, Item, Node, NodeSummary, SequenceHash, Summary,
    VARIABLE_BRANCHING,
    multiset::Multiset,
    summary::{Any, Count, Failing, Saturating, Uniform},
};

/// An item with a small key domain, so that keys repeat, and a value.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Entry {
    key: u8,
    value: u8,
}

/// The test items' own summary: a sum and a count, and the first odd value, which makes the
/// monoid depend on the order of the items.
#[derive(Clone, Debug, PartialEq)]
struct Tally {
    sum: u64,
    odd: usize,
    first_odd: Option<u8>,
}

impl Summary for Tally {
    fn identity() -> Self {
        Self {
            sum: 0,
            odd: 0,
            first_odd: None,
        }
    }

    fn combine(self, right: &Self) -> Self {
        Self {
            sum: self.sum + right.sum,
            odd: self.odd + right.odd,
            first_odd: self.first_odd.or(right.first_odd),
        }
    }
}

fn fx_hash(value: &impl Hash) -> u64 {
    let mut hasher = FxHasher::default();
    value.hash(&mut hasher);
    hasher.finish()
}

/// The test items' summary: the [`Tally`], then one of each generic summary over some
/// arithmetic property of the item (see [`Entry::summary`]).
type EntrySummary = (Tally, Failing<2>, Count, Saturating<2>, Any, Uniform<u8>);

/// The test items' group summary: the multiset of the "variables" an item mentions.
type Variables = Multiset<u8, 5>;

impl Entry {
    /// Whether the item satisfies each of two flags.
    fn flags(&self) -> [bool; 2] {
        [!self.value.is_multiple_of(5), !self.value.is_multiple_of(7)]
    }

    /// Whether the item's key counts as symbolic.
    fn symbolic_key(&self) -> bool {
        self.key.is_multiple_of(4)
    }

    /// What the item adds to a saturating count.
    fn cells(&self) -> usize {
        usize::from(self.value % 4)
    }

    fn marked(&self) -> bool {
        self.value.is_multiple_of(11)
    }

    /// The value all items of a uniform run share.
    fn header(&self) -> u8 {
        self.key / 8
    }

    /// The variables the item mentions: none for a third of the values (ground items), two
    /// otherwise, from small domains so that items share them.
    fn variables(&self) -> Vec<u8> {
        if self.value.is_multiple_of(3) {
            Vec::new()
        } else {
            vec![self.value % 23, 23 + self.key % 9]
        }
    }
}

impl Item for Entry {
    type Key = u8;
    type Summary = EntrySummary;
    type Group = Variables;

    fn key(&self) -> &u8 {
        &self.key
    }

    fn hash64(&self) -> u64 {
        fx_hash(self)
    }

    fn summary(&self) -> EntrySummary {
        let odd = self.value % 2 == 1;
        (
            Tally {
                sum: u64::from(self.value),
                odd: usize::from(odd),
                first_odd: odd.then_some(self.value),
            },
            Failing::of(self.flags()),
            Count::of(self.symbolic_key()),
            Saturating::of(self.cells()),
            Any(self.marked()),
            Uniform::One(self.header()),
        )
    }

    fn group(&self) -> Variables {
        Multiset::of(self.variables())
    }
}

const DEFAULT: usize = DEFAULT_BRANCHING;

/// The branching factor of the production trees of variables (multisets and sets).
const VARIABLES: usize = VARIABLE_BRANCHING;

/// Check the fill invariant, the heights, and that every node's summary is the fold of its
/// items' summaries; return the root's fold.
fn check_invariants<I: Item, const B: usize>(tree: &Chunked<I, B>) -> NodeSummary<I> {
    match &tree.root {
        None => NodeSummary::identity(),
        Some(root) => {
            let fold = check_node::<I, B>(root, true);
            assert!(
                fold.count > B || root.height() == 0,
                "a sequence of at most B items is one leaf"
            );
            fold
        }
    }
}

fn check_node<I: Item, const B: usize>(node: &Node<I>, is_root: bool) -> NodeSummary<I> {
    let (width, lowest, fold) = match node {
        Node::Leaf { items, .. } => (
            items.len(),
            1,
            items.iter().fold(NodeSummary::identity(), |fold, item| {
                fold.combine(&NodeSummary::of_item(item))
            }),
        ),
        Node::Internal {
            height, children, ..
        } => {
            for child in children {
                assert_eq!(
                    child.height() + 1,
                    *height,
                    "a child one level below its parent"
                );
            }
            (
                children.len(),
                2,
                children
                    .iter()
                    .fold(NodeSummary::identity(), |fold, child| {
                        fold.combine(&check_node::<I, B>(child, false))
                    }),
            )
        }
    };
    let lowest = if is_root {
        lowest
    } else {
        Chunked::<I, B>::MIN_FILL
    };
    assert!(
        (lowest..=B).contains(&width),
        "a node of width {width} outside {lowest}..={B} (root: {is_root})"
    );
    assert_eq!(
        node.summary(),
        &fold,
        "a node's summary is the fold of its items"
    );
    fold
}

/// A source of shape decisions drawn from proptest bytes; all zeros when there are none.
struct Choices {
    bytes: Vec<u8>,
    at: usize,
}

impl Choices {
    fn new(bytes: Vec<u8>) -> Self {
        Self { bytes, at: 0 }
    }

    /// A number below `bound`.
    fn below(&mut self, bound: usize) -> usize {
        if self.bytes.is_empty() || bound == 0 {
            return 0;
        }
        let byte = self.bytes[self.at % self.bytes.len()];
        self.at += 1;
        usize::from(byte) % bound
    }
}

/// A random cut of `n ≥ 1` things into parts of `min..=max`, or one part of `n` below `min`.
fn random_parts(n: usize, min: usize, max: usize, choices: &mut Choices) -> Vec<usize> {
    let mut parts = Vec::new();
    let mut left = n;
    while left > max || (left >= 2 * min && choices.below(3) != 0) {
        // Leave at least `min` behind for the next part.
        let highest = max.min(left - min);
        let part = min + choices.below(highest - min + 1);
        parts.push(part);
        left -= part;
    }
    parts.push(left);
    parts
}

/// The items cut into leaves of a random valid shape.
fn random_leaves<I: Item, const B: usize>(
    items: Vec<I>,
    choices: &mut Choices,
) -> Vec<Arc<Node<I>>> {
    if items.is_empty() {
        return Vec::new();
    }
    if items.len() <= B {
        return vec![Arc::new(Node::leaf(items))];
    }
    let mut items = items.into_iter();
    random_parts(items.len(), Chunked::<I, B>::MIN_FILL, B, choices)
        .into_iter()
        .map(|part| Arc::new(Node::leaf(items.by_ref().take(part).collect())))
        .collect()
}

/// The nodes of one level grouped under parents of a random valid shape.
fn random_parents<I: Item, const B: usize>(
    level: Vec<Arc<Node<I>>>,
    choices: &mut Choices,
) -> Vec<Arc<Node<I>>> {
    let height = level[0].height() + 1;
    let mut nodes = level.into_iter();
    random_parts(nodes.len(), Chunked::<I, B>::MIN_FILL, B, choices)
        .into_iter()
        .map(|part| Arc::new(Node::internal(height, nodes.by_ref().take(part).collect())))
        .collect()
}

/// A tree over the nodes of one level, grouped at random up to a single root.
fn random_tree<I: Item, const B: usize>(
    mut level: Vec<Arc<Node<I>>>,
    choices: &mut Choices,
) -> Chunked<I, B> {
    while level.len() > 1 {
        level = random_parents::<I, B>(level, choices);
    }
    Chunked { root: level.pop() }
}

/// The items in a tree of a random valid shape.
fn shaped<I: Item, const B: usize>(items: Vec<I>, choices: Vec<u8>) -> Chunked<I, B> {
    let mut choices = Choices::new(choices);
    let leaves = random_leaves::<I, B>(items, &mut choices);
    let tree = random_tree(leaves, &mut choices);
    check_invariants(&tree);
    tree
}

/// A copy of `node` that shares no node with it.
fn deep_copy<I: Item>(node: &Node<I>) -> Arc<Node<I>> {
    Arc::new(match node {
        Node::Leaf { items, .. } => Node::leaf(items.clone()),
        Node::Internal {
            height, children, ..
        } => Node::internal(
            *height,
            children.iter().map(|child| deep_copy(child)).collect(),
        ),
    })
}

/// A copy of `node` sharing no node with it, whose last item has another value if `change`.
fn copy_changing_last(node: &Node<Entry>, change: bool) -> Arc<Node<Entry>> {
    Arc::new(match node {
        Node::Leaf { items, .. } => {
            let mut items = items.clone();
            if change {
                let last = items.last_mut().expect("a leaf has an item");
                last.value = last.value.wrapping_add(1);
            }
            Node::leaf(items)
        }
        Node::Internal {
            height, children, ..
        } => {
            let last = children.len() - 1;
            let children = children
                .iter()
                .enumerate()
                .map(|(index, child)| copy_changing_last(child, change && index == last))
                .collect();
            Node::internal(*height, children)
        }
    })
}

fn entries(max_len: usize) -> impl Strategy<Value = Vec<Entry>> {
    prop::collection::vec(
        (0u8..40, any::<u8>()).prop_map(|(key, value)| Entry { key, value }),
        0..max_len,
    )
}

fn choices() -> impl Strategy<Value = Vec<u8>> {
    prop::collection::vec(any::<u8>(), 0..48)
}

fn bulk_load<const B: usize>(items: &[Entry]) {
    let tree = Chunked::<Entry, B>::from_vec(items.to_vec());
    let fold = check_invariants(&tree);
    let expected = NodeSummary::of_items(items);
    assert_eq!(fold, expected);
    assert_eq!(
        tree.summary()
            .cloned()
            .unwrap_or_else(NodeSummary::identity),
        expected
    );
    assert_eq!(tree.len(), items.len());
    assert_eq!(tree.is_empty(), items.is_empty());
    assert_eq!(tree.to_vec(), items);
    assert_eq!(format!("{tree:?}"), format!("{items:?}"));
}

fn iterate<const B: usize>(items: &[Entry], ends: &[bool]) {
    let tree = Chunked::<Entry, B>::from_vec(items.to_vec());
    check_invariants(&tree);
    let mut model: VecDeque<&Entry> = items.iter().collect();
    let mut iter = tree.iter();
    for &from_back in ends.iter().cycle().take(items.len() + 2) {
        assert_eq!(iter.len(), model.len());
        if from_back {
            assert_eq!(iter.next_back(), model.pop_back());
        } else {
            assert_eq!(iter.next(), model.pop_front());
        }
    }
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
    assert!(tree.iter().rev().eq(items.iter().rev()));
    assert!((&tree).into_iter().eq(items));
}

fn get<const B: usize>(items: &[Entry], shape: Vec<u8>) {
    let tree = shaped::<Entry, B>(items.to_vec(), shape);
    for index in 0..items.len() + 2 {
        assert_eq!(tree.get(index), items.get(index), "at {index}");
    }
}

fn search<const B: usize>(mut items: Vec<Entry>, shape: Vec<u8>) {
    items.sort();
    let mut model = BTreeMap::<u8, usize>::new();
    for item in &items {
        *model.entry(item.key).or_default() += 1;
    }
    let tree = shaped::<Entry, B>(items, shape);
    for key in 0..45 {
        let below = model.range(..key).map(|(_, count)| count).sum::<usize>();
        let expected = if model.contains_key(&key) {
            Ok(below)
        } else {
            Err(below)
        };
        assert_eq!(tree.search(&key), expected, "key {key}");
    }
}

fn shapes<const B: usize>(items: &[Entry], left: Vec<u8>, right: Vec<u8>) {
    let a = shaped::<Entry, B>(items.to_vec(), left);
    let b = shaped::<Entry, B>(items.to_vec(), right);
    assert_eq!(a, b);
    assert_eq!(a.cmp(&b), Ordering::Equal);
    assert_eq!(a.hash_value(), b.hash_value());
    assert_eq!(fx_hash(&a), fx_hash(&b));
    let bulk = Chunked::<Entry, B>::from_vec(items.to_vec());
    assert_eq!(a.hash_value(), bulk.hash_value());
    assert_eq!(a.summary(), bulk.summary());
}

fn order<const B: usize>(left: &[Entry], right: &[Entry], shape: (Vec<u8>, Vec<u8>)) {
    let a = shaped::<Entry, B>(left.to_vec(), shape.0);
    let b = shaped::<Entry, B>(right.to_vec(), shape.1);
    assert_eq!(a.cmp(&b), left.cmp(right));
    assert_eq!(b.cmp(&a), right.cmp(left));
    assert_eq!(a.partial_cmp(&b), left.partial_cmp(right));
    assert_eq!(a == b, left == right);
    assert_eq!(a.eq_by(&b, Entry::eq), left == right);
    if left == right {
        assert_eq!(a.hash_value(), b.hash_value());
    }
}

/// Two trees over the same items that share every node of one level but one, which the second
/// holds as an equal copy, possibly grouped differently above that level. Comparing them calls
/// the item comparison only on the copy's items.
fn sharing<const B: usize>(
    items: Vec<Entry>,
    shape: (Vec<u8>, Vec<u8>),
    level: usize,
    copied: usize,
    changed: bool,
) {
    if items.is_empty() {
        return;
    }
    let mut choices = (Choices::new(shape.0), Choices::new(shape.1));
    let mut nodes = random_leaves::<Entry, B>(items.clone(), &mut choices.0);
    for _ in 0..level {
        if nodes.len() < 2 {
            break;
        }
        nodes = random_parents::<Entry, B>(nodes, &mut choices.0);
    }
    let mut other = nodes.clone();
    let copied = copied % other.len();
    let start: usize = other[..copied]
        .iter()
        .map(|node| node.summary().count)
        .sum();
    let width = other[copied].summary().count;
    other[copied] = copy_changing_last(&other[copied], changed);
    let mut expected = items.clone();
    if changed {
        let last = &mut expected[start + width - 1];
        last.value = last.value.wrapping_add(1);
    }
    let a = random_tree::<Entry, B>(nodes, &mut choices.0);
    let b = random_tree::<Entry, B>(other, &mut choices.1);
    check_invariants(&a);
    check_invariants(&b);
    assert_eq!(b.to_vec(), expected);
    let mut calls = 0;
    let order = a.cmp_by(&b, |l, r| {
        calls += 1;
        l.cmp(r)
    });
    assert_eq!(order, items.cmp(&expected));
    assert_eq!(calls, width, "only the copied node's items are compared");
    let mut calls = 0;
    let equal = a.eq_by(&b, |l, r| {
        calls += 1;
        l == r
    });
    assert_eq!(equal, !changed);
    assert_eq!(calls, width);
    assert_eq!(a == b, !changed);
}

proptest! {
    #[test]
    fn bulk_load_keeps_the_items_and_the_invariant(items in entries(400)) {
        bulk_load::<5>(&items);
        bulk_load::<6>(&items);
        bulk_load::<DEFAULT>(&items);
    }

    #[test]
    fn iteration_from_both_ends_yields_the_items(items in entries(300), ends in prop::collection::vec(any::<bool>(), 1..40)) {
        iterate::<5>(&items, &ends);
        iterate::<6>(&items, &ends);
        iterate::<DEFAULT>(&items, &ends);
    }

    #[test]
    fn get_returns_the_item_at_a_position(items in entries(300), shape in choices()) {
        get::<5>(&items, shape.clone());
        get::<6>(&items, shape.clone());
        get::<DEFAULT>(&items, shape);
    }

    #[test]
    fn search_finds_the_first_item_of_a_key(items in entries(300), shape in choices()) {
        search::<5>(items.clone(), shape.clone());
        search::<6>(items.clone(), shape.clone());
        search::<DEFAULT>(items, shape);
    }

    #[test]
    fn equal_items_in_different_shapes_are_equal_and_hash_alike(items in entries(300), left in choices(), right in choices()) {
        shapes::<5>(&items, left.clone(), right.clone());
        shapes::<6>(&items, left.clone(), right.clone());
        shapes::<DEFAULT>(&items, left, right);
    }

    #[test]
    fn order_and_equality_are_those_of_the_items(prefix in entries(200), left in entries(30), right in entries(30), shape in (choices(), choices())) {
        let left = [prefix.clone(), left].concat();
        let right = [prefix, right].concat();
        order::<5>(&left, &right, shape.clone());
        order::<5>(&left, &left, shape.clone());
        order::<6>(&left, &right, shape.clone());
        order::<DEFAULT>(&left, &right, shape);
    }

    #[test]
    fn a_shared_node_is_compared_without_its_items(
        items in entries(300),
        shape in (choices(), choices()),
        level in 0usize..3,
        copied in any::<usize>(),
        changed in any::<bool>(),
    ) {
        sharing::<5>(items.clone(), shape.clone(), level, copied, changed);
        sharing::<6>(items.clone(), shape.clone(), level, copied, changed);
        sharing::<DEFAULT>(items, shape, level, copied, changed);
    }

    #[test]
    fn node_summaries_form_a_monoid(a in entries(20), b in entries(20), c in entries(20)) {
        let [a, b, c] = [&a, &b, &c].map(|items| NodeSummary::of_items(items));
        let identity = NodeSummary::<Entry>::identity();
        prop_assert_eq!(identity.clone().combine(&a), a.clone());
        prop_assert_eq!(a.clone().combine(&identity), a.clone());
        prop_assert_eq!(
            a.clone().combine(&b).combine(&c),
            a.combine(&b.combine(&c))
        );
    }
}

#[test]
fn the_hash_follows_the_order_of_the_items() {
    let item = |key| Entry { key, value: 0 };
    let forward = Chunked::<Entry, 5>::from_vec(vec![item(1), item(2)]);
    let backward = Chunked::<Entry, 5>::from_vec(vec![item(2), item(1)]);
    assert_ne!(forward.hash_value(), backward.hash_value());
    assert_ne!(forward, backward);
    assert_eq!(
        Chunked::<Entry, 5>::new().hash_value(),
        SequenceHash::EMPTY.value()
    );
}

#[test]
fn the_hash_arithmetic_is_modular() {
    use super::{MODULUS, add, multiply, reduce};
    let top = MODULUS - 1;
    assert_eq!(multiply(top, top), 1, "(-1)·(-1) = 1");
    assert_eq!(add(top, 1), 0);
    assert_eq!(reduce(u128::from(MODULUS)), 0);
    assert_eq!(reduce(u128::from(MODULUS) * u128::from(MODULUS) - 1), top);
    assert_eq!(
        reduce((1 << 122) - 1),
        ((1u128 << 122) - 1).rem_euclid(u128::from(MODULUS)) as u64
    );
}

thread_local! {
    /// The number of [`Counted`] values alive on this thread.
    static LIVE: Cell<isize> = const { Cell::new(0) };
}

fn live() -> isize {
    LIVE.with(Cell::get)
}

/// An item that counts its live values, to see that a drop frees every item exactly once.
#[derive(Debug, Eq, PartialEq)]
struct Counted(u32);

impl Counted {
    fn new(value: u32) -> Self {
        LIVE.with(|live| live.set(live.get() + 1));
        Self(value)
    }
}

impl Clone for Counted {
    fn clone(&self) -> Self {
        Self::new(self.0)
    }
}

impl Drop for Counted {
    fn drop(&mut self) {
        LIVE.with(|live| live.set(live.get() - 1));
    }
}

impl Item for Counted {
    type Key = u32;
    type Summary = ();
    type Group = ();

    fn key(&self) -> &u32 {
        &self.0
    }

    fn hash64(&self) -> u64 {
        u64::from(self.0)
    }

    fn summary(&self) {}

    fn group(&self) {}
}

/// A stack far too small for a recursion as deep as the nestings below.
const SMALL_STACK: usize = 128 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(SMALL_STACK)
        .spawn(test)
        .expect("a test thread starts")
        .join()
        .expect("the test thread does not panic");
}

#[test]
fn a_million_items_drop_on_a_small_stack() {
    on_small_stack(|| {
        let tree = Chunked::<Counted, 5>::from_vec((0..1_000_000).map(Counted::new).collect());
        assert_eq!(tree.len(), 1_000_000);
        drop(tree);
        assert_eq!(live(), 0, "every item and every summary's clone is freed");
    });
}

#[test]
fn a_drop_frees_only_the_nodes_it_holds_the_last_handle_of() {
    on_small_stack(|| {
        let items: Vec<u32> = (0..500).collect();
        let tree =
            Chunked::<Counted, 5>::from_vec(items.iter().copied().map(Counted::new).collect());
        let clone = tree.clone();
        drop(tree);
        check_invariants(&clone);
        assert!(clone.iter().map(|item| item.0).eq(items.iter().copied()));
        // Share every leaf of `clone` but one with a tree grouped differently.
        let Some(root) = &clone.root else {
            unreachable!("the tree is not empty")
        };
        let mut leaves = vec![Arc::clone(root)];
        while leaves[0].height() > 0 {
            leaves = leaves
                .iter()
                .flat_map(|node| match &**node {
                    Node::Internal { children, .. } => children.clone(),
                    Node::Leaf { .. } => unreachable!("leaves lie at one depth"),
                })
                .collect();
        }
        leaves[3] = deep_copy(&leaves[3]);
        let regrouped = random_tree::<Counted, 5>(leaves, &mut Choices::new(vec![7, 1, 200, 3]));
        check_invariants(&regrouped);
        drop(clone);
        check_invariants(&regrouped);
        assert!(
            regrouped
                .iter()
                .map(|item| item.0)
                .eq(items.iter().copied())
        );
        drop(regrouped);
        assert_eq!(live(), 0);
    });
}

/// An item that may hold a tree of items of its own type, and frees such a tree through the
/// work list of the tree it is an item of.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Nest {
    Atom(u32),
    Tree(Chunked<Nest, 5>),
}

impl Item for Nest {
    type Key = ();
    type Summary = ();
    type Group = ();

    fn key(&self) -> &() {
        &()
    }

    fn hash64(&self) -> u64 {
        match self {
            Self::Atom(value) => u64::from(*value),
            Self::Tree(tree) => !tree.hash_value(),
        }
    }

    fn summary(&self) {}

    fn group(&self) {}
}

impl Drop for Nest {
    fn drop(&mut self) {
        let Self::Tree(tree) = self else { return };
        let mut work = Dismantle::new();
        work.push(std::mem::take(tree));
        while let Some(mut item) = work.next() {
            if let Self::Tree(inner) = &mut item {
                work.push(std::mem::take(inner));
            }
        }
    }
}

#[test]
fn a_deep_nesting_of_trees_drops_on_a_small_stack() {
    on_small_stack(|| {
        let mut nest = Nest::Atom(0);
        let mut innermost = None;
        for depth in 0..200_000 {
            let tree = Chunked::from_vec(vec![Nest::Atom(depth), nest, Nest::Atom(depth)]);
            if innermost.is_none() {
                innermost = tree.root.as_ref().map(Arc::downgrade);
            }
            nest = Nest::Tree(tree);
        }
        drop(nest);
        let innermost = innermost.expect("the innermost tree is not empty");
        assert!(innermost.upgrade().is_none(), "the innermost tree is freed");
    });
}

#[test]
fn a_deep_nesting_held_by_a_tree_drops_on_a_small_stack() {
    on_small_stack(|| {
        let mut nest = Nest::Atom(0);
        for depth in 0..200_000 {
            nest = Nest::Tree(Chunked::from_vec(vec![nest, Nest::Atom(depth)]));
        }
        let outer = Chunked::<Nest, 5>::from_vec(vec![nest]);
        drop(outer);
    });
}

/// The widths of the nodes other than the root.
fn inner_widths<I: Item>(node: &Node<I>, is_root: bool, widths: &mut Vec<usize>) {
    match node {
        Node::Leaf { items, .. } => {
            if !is_root {
                widths.push(items.len());
            }
        }
        Node::Internal { children, .. } => {
            if !is_root {
                widths.push(children.len());
            }
            for child in children {
                inner_widths(child, false, widths);
            }
        }
    }
}

/// A bulk-loaded tree leaves room in every node other than the root for an insertion and a
/// removal, so its first edits split or merge nothing. The part count nearest `n/target` alone
/// would miss some lengths (at `B = 5`, nine items cut into 5 and 4; at `B = 9`, 17 cut into 9
/// and 8), so both are checked with the default.
fn bulk_load_leaves_room<const B: usize>(max: usize) {
    for n in B + 1..max {
        let tree: Chunked<Entry, B> = Chunked::from_vec(
            (0..n)
                .map(|key| Entry {
                    key: u8::try_from(key % 256).expect("below 256"),
                    value: 0,
                })
                .collect(),
        );
        let mut widths = Vec::new();
        inner_widths(tree.root.as_deref().expect("items"), true, &mut widths);
        assert!(
            widths
                .iter()
                .all(|&width| Chunked::<Entry, B>::MIN_FILL < width && width < B),
            "{n} items: widths {widths:?}"
        );
    }
}

#[test]
fn a_bulk_load_leaves_room_in_every_node_but_the_root() {
    bulk_load_leaves_room::<5>(3_000);
    bulk_load_leaves_room::<6>(3_000);
    bulk_load_leaves_room::<9>(3_000);
    bulk_load_leaves_room::<DEFAULT>(3_000);
}

/// What one check of `tree` hands over: the items, the adjacent pairs, and the visited nodes.
#[cfg(debug_assertions)]
fn checked_once<const B: usize>(
    tree: &Chunked<Entry, B>,
) -> (Vec<Entry>, Vec<(Entry, Entry)>, super::Unchecked<'_, Entry>) {
    let (mut items, mut pairs) = (Vec::new(), Vec::new());
    let visited = tree.check_unchecked(
        |leaf| items.extend_from_slice(leaf),
        |left, right| pairs.push((left.clone(), right.clone())),
    );
    (items, pairs, visited)
}

/// Debug builds: a check hands over each item and each adjacent pair of a tree it has not
/// marked, and nothing once the visited nodes are marked; after one edit it hands over at most
/// the two leaves the edit rebuilds, and the two checks together cover every item and adjacent
/// pair of the edited tree. Without marking, a check hands everything over again.
#[cfg(debug_assertions)]
fn check_unchecked_after_edit<const B: usize>(
    items: &[Entry],
    shape: Vec<u8>,
    place: usize,
    inserted: Option<Entry>,
) {
    let tree = shaped::<Entry, B>(items.to_vec(), shape);
    let (first_items, first_pairs, visited) = checked_once(&tree);
    assert_eq!(first_items.len(), items.len());
    assert_eq!(first_pairs.len(), items.len().saturating_sub(1));
    let (again, _, unmarked) = checked_once(&tree);
    assert_eq!(
        again.len(),
        items.len(),
        "an unmarked tree is handed over again"
    );
    unmarked.mark();
    drop(visited);
    let (none, no_pairs, _) = checked_once(&tree);
    assert!(none.is_empty() && no_pairs.is_empty());
    let edited = match inserted {
        Some(item) => tree.insert_at(place % (items.len() + 1), item),
        None if items.is_empty() => return,
        None => tree.remove_at(place % items.len()).0,
    };
    let (second_items, second_pairs, _) = checked_once(&edited);
    assert!(
        second_items.len() <= 2 * B,
        "{} items handed over after one edit",
        second_items.len()
    );
    let all = edited.to_vec();
    for item in &all {
        assert!(first_items.contains(item) || second_items.contains(item));
    }
    for pair in all.windows(2) {
        let pair = (pair[0].clone(), pair[1].clone());
        assert!(
            first_pairs.contains(&pair) || second_pairs.contains(&pair),
            "the adjacent pair {pair:?} is never handed over"
        );
    }
}

#[cfg(debug_assertions)]
proptest! {
    #[test]
    fn a_check_hands_over_what_the_edits_since_the_last_one_built(
        items in entries(300),
        shape in choices(),
        place in any::<usize>(),
        inserted in prop::option::of(edit::entry()),
    ) {
        check_unchecked_after_edit::<5>(&items, shape.clone(), place, inserted.clone());
        check_unchecked_after_edit::<DEFAULT>(&items, shape, place, inserted);
    }
}

/// The `(height, width)` of each node of `node`'s subtree, in preorder: equal for two trees
/// exactly when they have one shape.
fn shape<I: Item>(node: &Node<I>, out: &mut Vec<(usize, usize)>) {
    match node {
        Node::Leaf { items, .. } => out.push((0, items.len())),
        Node::Internal {
            height, children, ..
        } => {
            out.push((*height, children.len()));
            for child in children {
                shape(child, out);
            }
        }
    }
}

/// The number of distinct nodes (by address) of each height in `tree`, from the leaves up.
fn distinct_nodes<I: Item, const B: usize>(tree: &Chunked<I, B>) -> Vec<usize> {
    let mut seen = std::collections::HashSet::new();
    let mut per_height = vec![0; tree.levels()];
    let mut pending: Vec<&Arc<Node<I>>> = tree.root.iter().collect();
    while let Some(node) = pending.pop() {
        if !seen.insert(Arc::as_ptr(node)) {
            continue;
        }
        per_height[node.height()] += 1;
        if let Node::Internal { children, .. } = &**node {
            pending.extend(children);
        }
    }
    per_height
}

fn repeat_is_from_vec<const B: usize>(count: usize) {
    let item = Entry { key: 1, value: 3 };
    let repeated = Chunked::<Entry, B>::repeat(&item, count);
    let loaded = Chunked::<Entry, B>::from_vec(vec![item; count]);
    assert_eq!(check_invariants(&repeated), check_invariants(&loaded));
    let (mut left, mut right) = (Vec::new(), Vec::new());
    if let (Some(repeated), Some(loaded)) = (&repeated.root, &loaded.root) {
        shape(repeated, &mut left);
        shape(loaded, &mut right);
    }
    assert_eq!(left, right, "the shape from_vec gives, at {count} items");
    assert_eq!(repeated, loaded);
    assert_eq!(repeated.hash_value(), loaded.hash_value());
}

/// `repeat` builds the tree `from_vec` builds of the same items, node for node.
#[test]
fn repeating_an_item_builds_the_tree_of_its_copies() {
    for count in (0..=2_000).chain([4_095, 4_096, 4_097, 30_000, 100_003]) {
        repeat_is_from_vec::<5>(count);
        repeat_is_from_vec::<6>(count);
        repeat_is_from_vec::<DEFAULT_BRANCHING>(count);
    }
}

/// The distinct nodes of a repeated item at each height `h` are at most `3h + 4`, whatever the
/// length: the junctions where a level changes node lie in clusters of at most two mixed nodes,
/// one cluster per level below plus one (each level's switch of part size), and between the
/// clusters lie runs of one pure node each. So up to `usize::MAX` items the tree is a few
/// hundred nodes, `O(log² n)`, against `n/B` leaves for the copies loaded one by one.
#[test]
fn repeating_an_item_shares_its_nodes() {
    fn check<const B: usize>(count: usize) {
        let tree = Chunked::<Entry, B>::repeat(&Entry { key: 1, value: 0 }, count);
        assert_eq!(tree.len(), count);
        for (height, nodes) in distinct_nodes(&tree).into_iter().enumerate() {
            assert!(
                nodes <= 3 * height + 4,
                "{nodes} distinct nodes at height {height} of {count} items (B = {B})"
            );
        }
    }
    // Lengths of every magnitude, from a xorshift sequence, and the extremes.
    let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
    let lengths = std::iter::repeat_with(move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state >> (state % 64)) as usize
    });
    for count in lengths
        .take(2_000)
        .chain([0, 1, usize::MAX - 1, usize::MAX])
    {
        check::<5>(count);
        check::<6>(count);
        check::<DEFAULT_BRANCHING>(count);
    }
}

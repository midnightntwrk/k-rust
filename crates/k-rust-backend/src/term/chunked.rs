//! A persistent sequence stored as a B-tree of chunks, with a summary in every node.
//!
//! [`Chunked`] holds a sequence of items in a tree whose leaves are vectors of at most `B` items
//! and whose internal nodes hold at most `B` children. Nodes are shared behind [`Arc`], so a
//! clone shares the whole tree and a persistent edit copies only the nodes it changes. The tree is the representation planned for the items of a map, a
//! set and a list term, and for the variable sets of term attributes (design K22, revision 2).
//!
//! # State of this module
//!
//! The tree has nodes, the fill invariant, bulk loading, length, double-ended iteration, access
//! by position, ordered search, equality, order, a hash independent of the tree's shape, a drop
//! that needs only constant stack, the persistent edits of [`edit`] (inserting and removing one
//! item by path copy, splitting at a position or a key, joining, and the union of two ordered
//! sequences), the per-node summaries of [`summary`] and the group summaries kept by difference
//! ([`Group`], [`multiset`]), and the seeks, ranges and item-wise rebuilds of [`seek`]. Nothing
//! outside this module and its tests uses it until terms move to it, so its declaration in
//! `term.rs` allows dead code outside test builds; test builds keep the lint, so every item here
//! is at least tested.
//!
//! # Items
//!
//! The module is generic over the item type through [`Item`]: an item gives its key (for an
//! ordered collection), a 64-bit hash, and its own [`Summary`] contribution. When terms move to
//! the tree, three item types implement it:
//!
//! - `Term`, the element of a set and the item of a list. Its key is the term itself (a set is
//!   ordered by `Term`'s `Ord`; a list is ordered by position and never searched by key), and
//!   its hash is the hash the term stores. Its summary is a tuple of the generic summaries of
//!   [`summary`]: a [`Failing`](summary::Failing) over the attribute flags (`evaluated`,
//!   `value_claimed`, `constructor_like`, `concrete_after_normalization`, `can_be_evaluated`,
//!   `ceil_free`), a [`Uniform`](summary::Uniform) key header, an [`Any`](summary::Any) for
//!   `has_macro_or_alias`, a [`Saturating`](summary::Saturating) count of `k` cells at 2, and a
//!   [`Count`](summary::Count) of symbolic keys (not `constructor_like`). Its group summary is
//!   the [`Multiset`](multiset::Multiset) of the variables it mentions, empty for a ground term.
//!   [`NodeSummary`] adds the repeated-key flag (`collision`) for every item type.
//! - `(Term, Term)`, the entry of a map. Its key is the map key: entries are ordered by
//!   `(key, value)`, which orders keys as `Term`'s `Ord` does, so a search by key finds the
//!   first entry of that key. Its hash mixes the two terms' hashes; its summary and group
//!   summary are the entry's share of the same fields (the symbolic-key count reads the key).
//! - `Variable`, the element of a persistent variable set (and, in a
//!   [`Multiset`](multiset::Multiset), paired with its number of occurrences, keyed by the
//!   variable). Its key is itself, its hash is the variable's `FxHasher` hash, and its summary
//!   and group summary are `()`.
//!
//! # Fill invariant
//!
//! Every node except the root holds between `a = (B - 1) / 2` and `B` items (a leaf) or children
//! (an internal node). The root holds between 1 and `B` items when it is a leaf and between 2 and
//! `B` children otherwise; the empty sequence has no root. Every leaf lies at the same depth:
//! an internal node records its height, one more than its children's. Since `B > 2a`, a node
//! split from one that overflowed, or merged from one that underflowed and a neighbour, ends away
//! from both bounds, which keeps rebalancing amortized constant under updates. `B` must be at
//! least 5: below it `a` is 1, a non-root internal node may then have a single child, and the
//! height is no longer bounded by the logarithm of the length.
//!
//! A sequence of at most `B` items is a single leaf, whatever built it, so a small collection is
//! one node. Only a root of height 1 can hold that few items over several leaves (a tree of
//! height 2 holds at least `2a²` items, more than `B`), and the edits replace such a root by the
//! one leaf of its items.
//!
//! # Summaries
//!
//! Every node stores a [`NodeSummary`]: the number of items below it, its first and last item,
//! whether two adjacent items share a key, the [`SequenceHash`] of its items, the item type's
//! own [`Summary`], and its [`Group`] summary. Each of these is a monoid, and a node's summary is
//! the fold of its items' summaries in order, so a summary of any concatenation of subtrees is
//! the combination of theirs. The first and last items let an ordered search pick a child by its
//! keys alone, and give the repeated-key flag at a junction.
//!
//! All fields but the group summary have a constant size, and a copied node recomputes them from
//! its children. The group summary can grow with the items (the variables they mention), so a
//! copied node gets it by difference from the node it replaces: [`Group`] says when and why
//! that is exact, and [`edit`] and [`seek`] which operations do so.
//!
//! # Equality, order and hash
//!
//! Equality and order are those of the item sequence, as for the flattened `Vec`: two trees of
//! different shapes holding equal sequences are equal. The comparison walks both sequences with
//! a cursor each and skips, without looking at its items, a node that both cursors reach at the
//! same position, since a shared node holds the same items in both. The hash is a polynomial
//! hash of the item sequence modulo the prime `2^61 - 1`, so it does not depend on the shape
//! either, and equal sequences hash alike whichever history built them.
//!
//! # Drop
//!
//! Dropping a tree frees, through a work list, every node of which it holds the last handle and
//! only releases a shared one ([`Arc::into_inner`]), so the stack it needs does not grow with
//! the tree. An item type whose values hold trees of their own (a list of lists) takes them apart
//! through the same work list, [`Dismantle`], so a deep nesting is freed in constant stack too.

mod edit;
pub(crate) mod multiset;
pub(crate) mod seek;
pub(crate) mod summary;
#[cfg(test)]
mod tests;

use std::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    iter::FusedIterator,
    slice,
    sync::Arc,
    vec,
};

/// The branching factor of a [`Chunked`] that names none. Provisional: it is to be chosen by
/// measuring the collection workloads once terms use the tree.
pub(crate) const DEFAULT_BRANCHING: usize = 32;

/// A monoid: an associative [`combine`](Summary::combine) with an [`identity`](Summary::identity)
/// on either side. A node stores the fold of its items' summaries, so combining the summaries of
/// adjacent subtrees gives the summary of their concatenation.
pub(crate) trait Summary: Clone + PartialEq + fmt::Debug {
    /// The summary of the empty sequence.
    fn identity() -> Self;

    /// The summary of the items `self` summarizes followed by those `right` summarizes.
    #[must_use]
    fn combine(self, right: &Self) -> Self;
}

impl Summary for () {
    fn identity() -> Self {}

    fn combine(self, _right: &Self) -> Self {}
}

/// A [`Summary`] whose [`combine`](Summary::combine) is commutative and can be undone:
/// [`subtract`](Group::subtract) takes out of a summary the share of some of the items it
/// summarizes. Counts and multisets are such summaries.
///
/// A node keeps its group summary by the difference an edit makes below it, the summaries of the
/// items the edit adds and removes, instead of recombining its children's summaries: a node
/// holds the same items as the node it replaces up to that difference, and since the group is
/// commutative, where in the node the items went does not matter. A summary whose size grows with
/// the items below the node (the multiset of the variables they mention) then costs an edit only
/// the difference, at each node it copies; recombining would cost everything below the node.
pub(crate) trait Group: Summary {
    /// The summary of the items `self` summarizes without those `part` summarizes, which are
    /// among them.
    #[must_use]
    fn subtract(self, part: &Self) -> Self;

    /// The work of combining with or subtracting this summary, in the units its operations are
    /// linear in (the entries of a multiset). Of two summaries to combine, the heavier is kept
    /// and the lighter added to it; of two parts of a node to compute, the lighter is folded and
    /// the heavier subtracted from the node's.
    fn weight(&self) -> usize;
}

impl Group for () {
    fn subtract(self, _part: &Self) -> Self {}

    fn weight(&self) -> usize {
        0
    }
}

/// The group summary of `groups`, combined in order. Each combination keeps the heavier side,
/// so the work is that of the lighter sides.
fn fold_groups<G: Group>(groups: impl IntoIterator<Item = G>) -> G {
    groups
        .into_iter()
        .fold(G::identity(), |fold, group| fold.combine(&group))
}

/// An item of a [`Chunked`] sequence.
///
/// The sequence relies on two agreements. [`hash64`](Item::hash64) agrees with `Eq`: equal
/// items hash alike, so sequences whose hashes differ are unequal. And the items of a sequence
/// used as an ordered collection are in nondecreasing order of [`key`](Item::key), which is all
/// an ordered search reads; an item order (`Ord`, when the item has one) that sorts such a
/// sequence must therefore order items of different keys as their keys are ordered.
pub(crate) trait Item: Clone + Eq + fmt::Debug {
    /// What an ordered collection is searched by.
    type Key: Ord + ?Sized;

    /// The item type's own share of a node's summary, recombined from a copied node's children
    /// (its combination must cost a constant, not grow with the items).
    type Summary: Summary;

    /// The item type's share of a node's summary that is kept by difference ([`Group`]): one
    /// whose size grows with the items, such as the multiset of the variables they mention.
    type Group: Group;

    fn key(&self) -> &Self::Key;

    /// A hash of the item that agrees with `Eq`.
    fn hash64(&self) -> u64;

    /// The summary of the one-item sequence holding this item.
    fn summary(&self) -> Self::Summary;

    /// The group summary of the one-item sequence holding this item.
    fn group(&self) -> Self::Group;
}

/// The prime `2^61 - 1`, the modulus of [`SequenceHash`].
const MODULUS: u64 = (1 << 61) - 1;

/// The radix `r` of [`SequenceHash`]: a fixed residue other than 0 and 1.
const RADIX: u64 = 0x1f3d_5b79_a2c4_e681 % MODULUS;

/// `x` modulo [`MODULUS`], for `x < 2^122`. Since `2^61 = 1` modulo `2^61 - 1`, adding the bits
/// above position 61 to the bits below it keeps the residue.
fn reduce(x: u128) -> u64 {
    let modulus = u128::from(MODULUS);
    // Below 2^61 + 2^61: both halves are below 2^61 since x < 2^122.
    let folded = ((x & modulus) + (x >> 61)) as u64;
    let folded = (folded & MODULUS) + (folded >> 61);
    if folded >= MODULUS {
        folded - MODULUS
    } else {
        folded
    }
}

fn multiply(left: u64, right: u64) -> u64 {
    reduce(u128::from(left) * u128::from(right))
}

fn add(left: u64, right: u64) -> u64 {
    let sum = left + right;
    if sum >= MODULUS { sum - MODULUS } else { sum }
}

/// An item's hash spread over all 64 bits (the finalizer of SplitMix64), then reduced: item
/// hashes of nearby values differ in few bits, and the polynomial hash below sums residues.
fn mix(hash: u64) -> u64 {
    let mut z = hash;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    reduce(u128::from(z ^ (z >> 31)))
}

/// A polynomial hash of an item sequence: for items with mixed hashes `x_1 … x_n`, the value
/// `x_1·r^(n-1) + … + x_n` and the power `r^n`, modulo the prime `2^61 - 1`.
///
/// `h(a ++ b) = h(a)·r^|b| + h(b)`, so the hash of a concatenation follows from the two parts'
/// values and powers, and the hash of a tree is the same for every shape holding its sequence.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct SequenceHash {
    value: u64,
    power: u64,
}

impl SequenceHash {
    /// The hash of the empty sequence.
    pub(crate) const EMPTY: Self = Self { value: 0, power: 1 };

    /// The hash of the one-item sequence of an item that hashes to `hash`.
    pub(crate) fn of_item(hash: u64) -> Self {
        Self {
            value: mix(hash),
            power: RADIX,
        }
    }

    pub(crate) fn value(self) -> u64 {
        self.value
    }
}

impl Summary for SequenceHash {
    fn identity() -> Self {
        Self::EMPTY
    }

    fn combine(self, right: &Self) -> Self {
        Self {
            value: add(multiply(self.value, right.power), right.value),
            power: multiply(self.power, right.power),
        }
    }
}

/// The summary every node stores: the number of items, the first and last item (absent only in
/// the identity), whether two adjacent items have the same key, the hash of the item sequence,
/// and the item type's own summary and group summary.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct NodeSummary<I: Item> {
    pub(crate) count: usize,
    pub(crate) first: Option<I>,
    pub(crate) last: Option<I>,
    /// Two adjacent items share a key. In an ordered collection, equal keys are adjacent, so
    /// this says whether a key is repeated; a list records it too, and nothing reads it there.
    pub(crate) collision: bool,
    pub(crate) hash: SequenceHash,
    pub(crate) extra: I::Summary,
    pub(crate) group: I::Group,
}

/// Whether the junction of a run ending with `last` and a run starting with `first` puts two
/// items of one key side by side.
fn collides<I: Item>(last: Option<&I>, first: Option<&I>) -> bool {
    matches!((last, first), (Some(last), Some(first)) if last.key() == first.key())
}

impl<I: Item> NodeSummary<I> {
    /// The summary of the one-item sequence holding `item`.
    pub(crate) fn of_item(item: &I) -> Self {
        Self {
            count: 1,
            first: Some(item.clone()),
            last: Some(item.clone()),
            collision: false,
            hash: SequenceHash::of_item(item.hash64()),
            extra: item.summary(),
            group: item.group(),
        }
    }

    /// The fold of the items' summaries, cloning only the first and the last item.
    fn of_items(items: &[I]) -> Self {
        Self::of_items_with(items, fold_groups(items.iter().map(Item::group)))
    }

    /// The fold of the items' summaries, but for the group summary, which is `group`.
    fn of_items_with(items: &[I], group: I::Group) -> Self {
        Self {
            count: items.len(),
            first: items.first().cloned(),
            last: items.last().cloned(),
            collision: items
                .windows(2)
                .any(|pair| collides(Some(&pair[0]), Some(&pair[1]))),
            hash: items.iter().fold(SequenceHash::EMPTY, |hash, item| {
                hash.combine(&SequenceHash::of_item(item.hash64()))
            }),
            extra: items.iter().fold(I::Summary::identity(), |extra, item| {
                extra.combine(&item.summary())
            }),
            group,
        }
    }

    /// The fold of the children's summaries, cloning only the first and the last item.
    fn of_children(children: &[Arc<Node<I>>]) -> Self {
        Self::of_children_with(
            children,
            fold_groups(children.iter().map(|child| child.summary().group.clone())),
        )
    }

    /// The fold of the children's summaries, but for the group summary, which is `group`.
    fn of_children_with(children: &[Arc<Node<I>>], group: I::Group) -> Self {
        Self {
            count: children.iter().map(|child| child.summary().count).sum(),
            first: children
                .first()
                .and_then(|child| child.summary().first.clone()),
            last: children
                .last()
                .and_then(|child| child.summary().last.clone()),
            collision: children.iter().any(|child| child.summary().collision)
                || children.windows(2).any(|pair| {
                    collides(
                        pair[0].summary().last.as_ref(),
                        pair[1].summary().first.as_ref(),
                    )
                }),
            hash: children.iter().fold(SequenceHash::EMPTY, |hash, child| {
                hash.combine(&child.summary().hash)
            }),
            extra: children
                .iter()
                .fold(I::Summary::identity(), |extra, child| {
                    extra.combine(&child.summary().extra)
                }),
            group,
        }
    }

    /// The key of the last item, which a node's summary always has.
    fn last_key(&self) -> &I::Key {
        self.last
            .as_ref()
            .expect("the summary of a node has a last item")
            .key()
    }
}

impl<I: Item> Summary for NodeSummary<I> {
    fn identity() -> Self {
        Self {
            count: 0,
            first: None,
            last: None,
            collision: false,
            hash: SequenceHash::EMPTY,
            extra: I::Summary::identity(),
            group: I::Group::identity(),
        }
    }

    fn combine(self, right: &Self) -> Self {
        Self {
            count: self.count + right.count,
            collision: self.collision
                || right.collision
                || collides(self.last.as_ref(), right.first.as_ref()),
            first: self.first.or_else(|| right.first.clone()),
            last: right.last.clone().or(self.last),
            hash: self.hash.combine(&right.hash),
            extra: self.extra.combine(&right.extra),
            group: self.group.combine(&right.group),
        }
    }
}

/// A node of the tree: a leaf holding items, or an internal node holding the roots of subtrees
/// one level lower. Neither is ever empty.
enum Node<I: Item> {
    Leaf {
        items: Vec<I>,
        summary: NodeSummary<I>,
    },
    Internal {
        /// One more than the children's height; a leaf's height is 0.
        height: usize,
        children: Vec<Arc<Node<I>>>,
        summary: NodeSummary<I>,
    },
}

impl<I: Item> Node<I> {
    fn leaf(items: Vec<I>) -> Self {
        let summary = NodeSummary::of_items(&items);
        Self::Leaf { items, summary }
    }

    fn internal(height: usize, children: Vec<Arc<Self>>) -> Self {
        let summary = NodeSummary::of_children(&children);
        Self::Internal {
            height,
            children,
            summary,
        }
    }

    /// A leaf whose group summary the caller knows: `group` is that of `items`.
    fn leaf_with(items: Vec<I>, group: I::Group) -> Self {
        let summary = NodeSummary::of_items_with(&items, group);
        Self::Leaf { items, summary }
    }

    /// An internal node whose group summary the caller knows: `group` is that of the items
    /// below `children`.
    fn internal_with(height: usize, children: Vec<Arc<Self>>, group: I::Group) -> Self {
        let summary = NodeSummary::of_children_with(&children, group);
        Self::Internal {
            height,
            children,
            summary,
        }
    }

    fn summary(&self) -> &NodeSummary<I> {
        match self {
            Self::Leaf { summary, .. } | Self::Internal { summary, .. } => summary,
        }
    }

    fn height(&self) -> usize {
        match self {
            Self::Leaf { .. } => 0,
            Self::Internal { height, .. } => *height,
        }
    }
}

/// The sizes of the parts of `n` things cut into as few parts of at most `b` as possible, as
/// even as possible: `⌈n/b⌉` parts of `⌊n/parts⌋` or one more. With two parts or more each part
/// holds more than `b/2` things (`n > (parts - 1)·b`), so at least `(b - 1)/2`.
fn even_parts(n: usize, b: usize) -> impl Iterator<Item = usize> {
    let parts = n.div_ceil(b);
    // No parts (and no division) for nothing.
    let base = n.checked_div(parts).unwrap_or(0);
    let longer = n.checked_rem(parts).unwrap_or(0);
    (0..parts).map(move |part| base + usize::from(part < longer))
}

/// A persistent sequence of items in a B-tree of branching factor `B`; see the module
/// documentation.
pub(crate) struct Chunked<I: Item, const B: usize = DEFAULT_BRANCHING> {
    root: Option<Arc<Node<I>>>,
}

impl<I: Item, const B: usize> Chunked<I, B> {
    /// The fewest items or children a node other than the root holds.
    pub(crate) const MIN_FILL: usize = {
        assert!(
            B >= 5,
            "a branching factor below 5 allows single-child internal nodes"
        );
        (B - 1) / 2
    };

    /// The empty sequence.
    pub(crate) const fn new() -> Self {
        Self { root: None }
    }

    /// The sequence of `items`, in their order, built bottom-up in time linear in their number.
    /// For an ordered collection the caller passes them in nondecreasing order of key.
    pub(crate) fn from_vec(items: Vec<I>) -> Self {
        let _ = Self::MIN_FILL;
        let mut items = items.into_iter();
        let mut level: Vec<Arc<Node<I>>> = even_parts(items.len(), B)
            .map(|size| Arc::new(Node::leaf(items.by_ref().take(size).collect())))
            .collect();
        let mut height = 0;
        while level.len() > 1 {
            height += 1;
            let mut nodes = level.into_iter();
            level = even_parts(nodes.len(), B)
                .map(|size| Arc::new(Node::internal(height, nodes.by_ref().take(size).collect())))
                .collect();
        }
        Self { root: level.pop() }
    }

    pub(crate) fn len(&self) -> usize {
        self.root.as_ref().map_or(0, |root| root.summary().count)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// The summary of the whole sequence; `None` for the empty one, whose summary is
    /// [`Summary::identity`].
    pub(crate) fn summary(&self) -> Option<&NodeSummary<I>> {
        self.root.as_ref().map(|root| root.summary())
    }

    /// The [`SequenceHash`] value of the items: equal for equal sequences, whatever their shape.
    pub(crate) fn hash_value(&self) -> u64 {
        self.summary()
            .map_or(SequenceHash::EMPTY, |summary| summary.hash)
            .value()
    }

    pub(crate) fn iter(&self) -> Iter<'_, I> {
        Iter::new(self.root.as_ref())
    }

    /// The item at `index`, in time logarithmic in the length.
    pub(crate) fn get(&self, mut index: usize) -> Option<&I> {
        let mut node = self.root.as_deref()?;
        if index >= node.summary().count {
            return None;
        }
        loop {
            match node {
                Node::Leaf { items, .. } => return items.get(index),
                Node::Internal { children, .. } => {
                    for child in children {
                        let count = child.summary().count;
                        if index < count {
                            node = child;
                            break;
                        }
                        index -= count;
                    }
                }
            }
        }
    }

    /// In a sequence in nondecreasing order of key, `Ok` with the position of the first item
    /// whose key is `key`, or `Err` with the position at which an item of that key would go:
    /// the number of items whose key is below `key`. Logarithmic in the length.
    pub(crate) fn search(&self, key: &I::Key) -> Result<usize, usize> {
        let Some(mut node) = self.root.as_deref() else {
            return Err(0);
        };
        let mut position = 0;
        loop {
            match node {
                Node::Internal { children, .. } => {
                    // The first child whose last key is not below `key` holds the first item
                    // that is not below it; every child before it lies wholly below `key`.
                    let index = children.partition_point(|child| child.summary().last_key() < key);
                    position += children[..index]
                        .iter()
                        .map(|child| child.summary().count)
                        .sum::<usize>();
                    match children.get(index) {
                        Some(child) => node = child,
                        None => return Err(position),
                    }
                }
                Node::Leaf { items, .. } => {
                    let offset = items.partition_point(|item| item.key() < key);
                    position += offset;
                    return match items.get(offset) {
                        Some(item) if item.key() == key => Ok(position),
                        _ => Err(position),
                    };
                }
            }
        }
    }

    pub(crate) fn to_vec(&self) -> Vec<I> {
        self.iter().cloned().collect()
    }

    /// The order of the two item sequences, lexicographic as for slices, with `compare` ordering
    /// two items. A node both sequences hold at the same position is skipped without calling
    /// `compare` on its items.
    pub(crate) fn cmp_by(
        &self,
        other: &Self,
        mut compare: impl FnMut(&I, &I) -> Ordering,
    ) -> Ordering {
        let mut left = Cursor::new(self.root.as_ref());
        let mut right = Cursor::new(other.root.as_ref());
        loop {
            let (step_left, step_right) = match (left.peek(), right.peek()) {
                (None, None) => return Ordering::Equal,
                (None, Some(_)) => return Ordering::Less,
                (Some(_), None) => return Ordering::Greater,
                (Some(Next::Node(l)), Some(Next::Node(r))) if Arc::ptr_eq(l, r) => {
                    left.skip();
                    right.skip();
                    continue;
                }
                (Some(Next::Item(l)), Some(Next::Item(r))) => match compare(l, r) {
                    Ordering::Equal => {
                        left.skip();
                        right.skip();
                        continue;
                    }
                    unequal => return unequal,
                },
                // Open the taller of the two (both at an equal height), until both stand at
                // items or at one shared node.
                (Some(l), Some(r)) => (l.level() >= r.level(), r.level() >= l.level()),
            };
            if step_left {
                left.open();
            }
            if step_right {
                right.open();
            }
        }
    }

    /// Whether the two item sequences are equal, with `equal` deciding two items. A node both
    /// sequences hold at the same position is skipped without calling `equal` on its items.
    pub(crate) fn eq_by(&self, other: &Self, mut equal: impl FnMut(&I, &I) -> bool) -> bool {
        self.len() == other.len()
            && self.cmp_by(other, |l, r| {
                if equal(l, r) {
                    Ordering::Equal
                } else {
                    Ordering::Less
                }
            }) == Ordering::Equal
    }
}

impl<I: Item, const B: usize> Default for Chunked<I, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: Item, const B: usize> Clone for Chunked<I, B> {
    fn clone(&self) -> Self {
        Self {
            root: self.root.clone(),
        }
    }
}

impl<I: Item, const B: usize> fmt::Debug for Chunked<I, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Equal when the item sequences are. The lengths and the hashes are compared first: both are
/// properties of the sequence, so a difference in either decides inequality.
impl<I: Item, const B: usize> PartialEq for Chunked<I, B> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (None, None) => true,
            (Some(l), Some(r)) if Arc::ptr_eq(l, r) => true,
            (Some(l), Some(r)) => {
                let (l, r) = (l.summary(), r.summary());
                l.count == r.count && l.hash == r.hash && self.eq_by(other, I::eq)
            }
            _ => false,
        }
    }
}

impl<I: Item, const B: usize> Eq for Chunked<I, B> {}

/// The lexicographic order of the item sequences, as for the flattened `Vec`.
impl<I: Item + Ord, const B: usize> Ord for Chunked<I, B> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (&self.root, &other.root) {
            (Some(l), Some(r)) if Arc::ptr_eq(l, r) => Ordering::Equal,
            _ => self.cmp_by(other, I::cmp),
        }
    }
}

impl<I: Item + Ord, const B: usize> PartialOrd for Chunked<I, B> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<I: Item, const B: usize> Hash for Chunked<I, B> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash_value());
    }
}

impl<'a, I: Item, const B: usize> IntoIterator for &'a Chunked<I, B> {
    type Item = &'a I;
    type IntoIter = Iter<'a, I>;

    fn into_iter(self) -> Iter<'a, I> {
        self.iter()
    }
}

/// Frees the nodes of which this is the last handle through [`Dismantle`], so in constant stack;
/// a shared root is only released.
impl<I: Item, const B: usize> Drop for Chunked<I, B> {
    fn drop(&mut self) {
        let Some(root) = self.root.take() else {
            return;
        };
        let Some(root) = Arc::into_inner(root) else {
            return;
        };
        let mut work = Dismantle::new();
        work.open(root);
        work.for_each(drop);
    }
}

/// The items of a [`Chunked`] in order, from either end.
///
/// The front and the back each descend from the root on their own; the number of items left
/// stops them before they cross.
pub(crate) struct Iter<'a, I: Item> {
    front: Vec<slice::Iter<'a, Arc<Node<I>>>>,
    front_items: slice::Iter<'a, I>,
    back: Vec<slice::Iter<'a, Arc<Node<I>>>>,
    back_items: slice::Iter<'a, I>,
    remaining: usize,
}

impl<'a, I: Item> Iter<'a, I> {
    fn new(root: Option<&'a Arc<Node<I>>>) -> Self {
        let roots = root.map_or(&[][..], slice::from_ref);
        Self {
            front: vec![roots.iter()],
            front_items: [].iter(),
            back: vec![roots.iter()],
            back_items: [].iter(),
            remaining: root.map_or(0, |root| root.summary().count),
        }
    }
}

impl<'a, I: Item> Iter<'a, I> {
    /// The items at positions `start..end` below `root`, with `start <= end <=` its count. Each
    /// end descends once to its first item, keeping the siblings beside its path.
    fn between(root: Option<&'a Arc<Node<I>>>, start: usize, end: usize) -> Self {
        let mut iter = Self {
            front: Vec::new(),
            front_items: [].iter(),
            back: Vec::new(),
            back_items: [].iter(),
            remaining: end - start,
        };
        let Some(root) = root.filter(|_| start < end) else {
            return iter;
        };
        let (mut node, mut index) = (root, start);
        iter.front_items = loop {
            match &**node {
                Node::Leaf { items, .. } => break items[index..].iter(),
                Node::Internal { children, .. } => {
                    let (slot, offset) = slot_of(children, index);
                    iter.front.push(children[slot + 1..].iter());
                    (node, index) = (&children[slot], offset);
                }
            }
        };
        let (mut node, mut index) = (root, end - 1);
        iter.back_items = loop {
            match &**node {
                Node::Leaf { items, .. } => break items[..=index].iter(),
                Node::Internal { children, .. } => {
                    let (slot, offset) = slot_of(children, index);
                    iter.back.push(children[..slot].iter());
                    (node, index) = (&children[slot], offset);
                }
            }
        };
        iter
    }
}

/// The child of `children` holding position `index`, below their total count, and the position
/// within it.
fn slot_of<I: Item>(children: &[Arc<Node<I>>], mut index: usize) -> (usize, usize) {
    for (slot, child) in children.iter().enumerate() {
        let count = child.summary().count;
        if index < count {
            return (slot, index);
        }
        index -= count;
    }
    unreachable!("a position below the count")
}

impl<'a, I: Item> Iterator for Iter<'a, I> {
    type Item = &'a I;

    fn next(&mut self) -> Option<&'a I> {
        if self.remaining == 0 {
            return None;
        }
        loop {
            if let Some(item) = self.front_items.next() {
                self.remaining -= 1;
                return Some(item);
            }
            let nodes = self
                .front
                .last_mut()
                .expect("an item that is left lies below the front");
            match nodes.next().map(|node| &**node) {
                None => {
                    self.front.pop();
                }
                Some(Node::Leaf { items, .. }) => self.front_items = items.iter(),
                Some(Node::Internal { children, .. }) => self.front.push(children.iter()),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<I: Item> DoubleEndedIterator for Iter<'_, I> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        loop {
            if let Some(item) = self.back_items.next_back() {
                self.remaining -= 1;
                return Some(item);
            }
            let nodes = self
                .back
                .last_mut()
                .expect("an item that is left lies below the back");
            match nodes.next_back().map(|node| &**node) {
                None => {
                    self.back.pop();
                }
                Some(Node::Leaf { items, .. }) => self.back_items = items.iter(),
                Some(Node::Internal { children, .. }) => self.back.push(children.iter()),
            }
        }
    }
}

impl<I: Item> ExactSizeIterator for Iter<'_, I> {}

impl<I: Item> FusedIterator for Iter<'_, I> {}

/// What a [`Cursor`] stands at: a node, all of whose items come next, or an item.
enum Next<'a, I: Item> {
    Node(&'a Arc<Node<I>>),
    Item(&'a I),
}

impl<I: Item> Next<'_, I> {
    /// How far above the items this stands: 0 for an item, one more than its height for a node.
    fn level(&self) -> usize {
        match self {
            Self::Node(node) => node.height() + 1,
            Self::Item(_) => 0,
        }
    }
}

/// The rest of a sequence being walked: a stack of slices of nodes or items, the innermost on
/// top, whose concatenation is what is left.
struct Cursor<'a, I: Item> {
    stack: Vec<Rest<'a, I>>,
}

enum Rest<'a, I: Item> {
    Nodes(&'a [Arc<Node<I>>]),
    Items(&'a [I]),
}

impl<'a, I: Item> Cursor<'a, I> {
    fn new(root: Option<&'a Arc<Node<I>>>) -> Self {
        Self {
            stack: root
                .map(|root| Rest::Nodes(slice::from_ref(root)))
                .into_iter()
                .collect(),
        }
    }

    /// The node or item that comes next, if any.
    fn peek(&mut self) -> Option<Next<'a, I>> {
        loop {
            match self.stack.last()? {
                Rest::Nodes([node, ..]) => return Some(Next::Node(node)),
                Rest::Items([item, ..]) => return Some(Next::Item(item)),
                Rest::Nodes([]) | Rest::Items([]) => {
                    self.stack.pop();
                }
            }
        }
    }

    /// Step past what [`peek`](Self::peek) returned.
    fn skip(&mut self) {
        match self.stack.last_mut() {
            Some(Rest::Nodes(nodes)) => *nodes = &nodes[1..],
            Some(Rest::Items(items)) => *items = &items[1..],
            None => {}
        }
    }

    /// Replace the node [`peek`](Self::peek) returned by its contents.
    fn open(&mut self) {
        let Some(Next::Node(node)) = self.peek() else {
            return;
        };
        self.skip();
        self.stack.push(match &**node {
            Node::Leaf { items, .. } => Rest::Items(items),
            Node::Internal { children, .. } => Rest::Nodes(children),
        });
    }
}

/// A work list taking trees apart: it opens each node of which it holds the last handle, only
/// releases a shared one, and yields the items of the leaves it opened, by value.
///
/// A tree's drop runs one and drops each item it yields. An item type whose values hold trees
/// takes those trees out of a yielded item and [`push`](Self::push)es them onto the same work
/// list before dropping the item, so a nesting of trees of any depth is freed in constant stack.
/// A node's summary, which holds clones of its first and last item, is dropped when the node is
/// opened, before its items are yielded, so a yielded item is not kept shared by the summary of
/// the leaf that held it.
pub(crate) struct Dismantle<I: Item> {
    nodes: Vec<Arc<Node<I>>>,
    items: vec::IntoIter<I>,
}

impl<I: Item> Dismantle<I> {
    pub(crate) fn new() -> Self {
        Self {
            nodes: Vec::new(),
            items: Vec::new().into_iter(),
        }
    }

    /// Add `tree`'s nodes to the work list. Its root is opened when the list reaches it, if
    /// this is then its last handle, and only released otherwise.
    pub(crate) fn push<const B: usize>(&mut self, mut tree: Chunked<I, B>) {
        self.nodes.extend(tree.root.take());
    }

    /// Open `node`, whose last handle this was, once the items of the leaf opened before it are
    /// all yielded.
    fn open(&mut self, node: Node<I>) {
        debug_assert_eq!(
            self.items.len(),
            0,
            "a leaf is opened only after the previous one"
        );
        match node {
            Node::Leaf { items, summary } => {
                drop(summary);
                self.items = items.into_iter();
            }
            Node::Internal {
                children, summary, ..
            } => {
                drop(summary);
                self.nodes.extend(children);
            }
        }
    }
}

impl<I: Item> Default for Dismantle<I> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: Item> Iterator for Dismantle<I> {
    type Item = I;

    fn next(&mut self) -> Option<I> {
        loop {
            if let Some(item) = self.items.next() {
                return Some(item);
            }
            let node = self.nodes.pop()?;
            if let Some(node) = Arc::into_inner(node) {
                self.open(node);
            }
        }
    }
}

/// Yields what is left, so that the nodes still on the list are freed through it rather than by
/// their glue.
impl<I: Item> Drop for Dismantle<I> {
    fn drop(&mut self) {
        self.by_ref().for_each(drop);
    }
}

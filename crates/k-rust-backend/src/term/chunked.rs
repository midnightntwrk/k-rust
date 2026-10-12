//! A persistent sequence stored as a B-tree of chunks, with a summary in every node.
//!
//! [`Chunked`] holds a sequence of items in a tree whose leaves are vectors of at most `B` items
//! and whose internal nodes hold at most `B` children. Nodes are shared behind [`Arc`], so a
//! clone shares the whole tree and a persistent edit copies only the nodes it changes. It is the
//! representation of the items of every map, set and list term ([`Items`](crate::term::Items))
//! and of the variable sets of term attributes ([`Variables`](crate::term::Variables)) (design
//! K22, revision 2):
//!
//! ```toml algorithm
//! id = "backend.term.chunked"
//! name = "persistent B+-tree of item chunks with monoid summaries per node"
//! sites = ["Chunked", "Chunked::from_vec", "Chunked::repeat", "Chunked::get", "Chunked::search", "Chunked::search_by", "Chunked::iter", "Chunked::aligned", "Chunked::eq_by", "Chunked::cmp_by", "Chunked::drop", "NodeSummary", "SequenceHash", "Dismantle"]
//! variable = "n = items of the tree (of the larger operand of a join or union); k = items of the smaller operand of a union; s = items a seek wants; u = items a rebuild changes; D = items of two compared versions outside the nodes they share; d = distinct variables of the items an edit adds or removes; V = distinct variables of the tree's items; m = variables of a union of variable sets outside its largest operand. The branching factor B is a constant (32 for collection items, 64 for variable trees), so a node is O(1) work"
//! counters = []
//! no_counter = "a tree operation is part of the hook, match, substitution or simplification that calls it, which carry the counters; test builds bound the summaries an operation computes (entry and multiset-entry counts), and tests/size_weighted_growth.rs bounds the bytes a rewrite step allocates on a larger collection"
//! span = "none"
//! tests = ["crates/k-rust-backend/src/term/chunked/tests.rs", "crates/k-rust-backend/src/term/items.rs", "crates/k-rust-backend/tests/size_weighted_growth.rs"]
//!
//! [[cost]]
//! mode = "insert, remove or replace one item (a path copy)"
//! bound = "O(log n) nodes copied, plus O(d log V) per copied node for its variable multiset (a rebalanced node amortized over the edits below it)"
//!
//! [[cost]]
//! mode = "search by key, access by position, a cursor or range start"
//! bound = "O(log n)"
//!
//! [[cost]]
//! mode = "length, hash, root summary (what a collection term's attributes read)"
//! bound = "O(1)"
//!
//! [[cost]]
//! mode = "split at a position or key; join two trees"
//! bound = "O(log n) nodes, plus at each level of a split the variables of its lighter side"
//!
//! [[cost]]
//! mode = "union of two ordered trees (a map or set built on a tree rest, _Map_, _Set_)"
//! bound = "O(k log(n/k + 1)) nodes copied, plus the added items' variables at each copied node"
//!
//! [[cost]]
//! mode = "seek by summary (unevaluated, failing ceil_free, symbolic key, k cell, variables meeting a substitution)"
//! bound = "O(s log n) nodes read, O(1) when the root summary admits nothing"
//!
//! [[cost]]
//! mode = "map_where, rebuild_where (substitution and simplifier rebuilds)"
//! bound = "O(u log n) nodes copied, plus one insertion per changed item no longer in order"
//!
//! [[cost]]
//! mode = "equality or order of two versions (aligned walk)"
//! bound = "O(D + log n) item comparisons and node visits; nodes both reach at one position are skipped"
//!
//! [[cost]]
//! mode = "drop of a version"
//! bound = "its unshared nodes (O(log n) after a one-item edit), in constant stack"
//!
//! [[cost]]
//! mode = "bulk load, full iteration, to_vec"
//! bound = "O(n)"
//!
//! [[cost]]
//! mode = "bulk load of n copies of one item (LIST.make)"
//! bound = "O(log² n) nodes, each a node of the tree from_vec builds of the copies"
//!
//! [[cost]]
//! mode = "variable set of a term built above its children (Variables, Union)"
//! bound = "O(1) when one child holds them all; O(m log V) when the largest child's set is a tree; O(V) merge when every operand has at most B variables"
//! ```
//!
//! Every operation is persistent: it returns new trees and leaves its operands valid, sharing
//! with them every node it did not change. The costs above count nodes, each `O(B)` items or
//! handles and its summary; the group summary of a copied node costs the difference the edit
//! makes ([`Group`]), not what lies below it. A few general operations (a split or a removal by
//! key, some methods of the persistent variable set) have no caller outside the tests, which
//! check every operation against a `Vec`, `BTreeMap` or multiset model, so the declaration in
//! `term.rs` allows dead code outside test builds.
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
//! - `Variable`, through [`Occurrences`](multiset::Occurrences)`<Variable>`: the entry of a
//!   [`Multiset`](multiset::Multiset) of variables and of a
//!   [`Variables`](variables::Variables) set, which share one tree (the variables of a
//!   collection are the elements of its root's multiset). `Variable` brings the `Ord`, `Hash`
//!   and `Debug` the entry needs; the entry's key is the variable, its hash the `FxHasher` hash
//!   of the variable and count, and its summary and group summary are `()`. The term attribute
//!   `variables` is a [`Variables`](variables::Variables) (a set of at most `B` variables is a
//!   shared slice instead of a tree), and `Substitution` implements
//!   [`VariableLookup`](crate::term::VariableLookup) over its domain.
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
//! That leaf is behind an [`Arc`] like any node, not held inline in the term. Holding it inline
//! would save one allocation and one indirection per small collection, at the price of a second
//! representation in every edit, seek and walk. Measured on the small workloads (K22 step 7b:
//! IMP and KEVM execution, the KEVM one-slot control, the WASM execution gate), the whole of this
//! module's code is about 0.1 % of a WASM program's instructions (0.2 % at most on the KEVM
//! workloads), and the allocations of collection trees about 3 % of its allocations, so the
//! saving is bounded by a few tenths of a percent; the small-workload costs were in the variable
//! sets and in the walks around the trees, and were removed there.
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
pub(crate) mod variables;

use std::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    iter::FusedIterator,
    slice,
    sync::Arc,
    vec,
};

/// The branching factor of a [`Chunked`] that names none: that of a map's entries, of a set's
/// elements and of a list's items.
///
/// An edit copies one node per level, `B` handles or items each, over `log_B n` levels, so a
/// smaller `B` copies less per level and a larger one has fewer levels and fewer summaries. Chosen
/// by `instructions:u` (K22 step 3e, 16, 32 and 64 with variable trees at 64): the KEVM storage
/// loop, which holds a map of up to 16,384 slots but spends most of its size-dependent cost in a
/// set, does not separate the three (totals within 0.05 %, its run-to-run spread); 16 costs 5.7 %
/// less than 32 on 16,000 `MAP.update`s and 3.9 % more on the symbolic map class test, 64 costs
/// 10.6 % more on the updates and its root, which every edit copies, widens in proportion to the
/// map up to `B²` entries (the map class test then fails). 32 is kept.
///
/// Sets use it too (K22 step 5a, 32 against 64, the variable trees' factor): a set's elements are
/// edited by path copies as a map's entries are, so the same trade holds. At 64, a benchmark of
/// 20,000 insertions, searches, removals and one-element unions each on sets of 256, 2,048 and
/// 16,384 elements costs 45 % more instructions, 16,000 `S SetItem(N)` steps 12 % more (41 % more
/// on the set's part over a counter control), and the set class test 36 % more bytes at 2,048
/// elements; the KEVM storage
/// loop at 16,384 slots does not separate the two (size-dependent part 53.7 G at 32, 52.7 G at
/// 64, within its run-to-run spread).
///
/// Lists use it too (K22 step 6a, 32 against 64): appending or prepending an item joins a
/// one-item tree to the list's, which copies the nodes along one edge of the tree, `B` handles
/// each, so the trade is again a node's width against the number of levels. At 64, 16,000
/// appends and 16,000 prepends cost 45 % more instructions over a counter control (1.04 G against
/// 0.72 G, 1.05 G against 0.73 G), and reading every item of a 16,000-item list by `LIST.get`,
/// one descent per read, 0.3 % more.
pub(crate) const DEFAULT_BRANCHING: usize = 32;

/// The branching factor of the trees of variables: a [`Multiset`](multiset::Multiset) of
/// variables and a [`Variables`](variables::Variables) set, which share one tree, and the size up
/// to which a set of variables is a flat slice.
///
/// A rule's or a function call's variable set often holds more than 32 variables and is built,
/// united and searched far more often than it is edited, so a larger leaf keeps such sets flat;
/// a symbolic collection's multiset is edited by path copies, where a larger node copies more.
/// Chosen by `instructions:u` (K22 step 3e, 32, 64 and 128 with map entries at 32): 64 costs
/// 0.8 % less than 32 on KEVM `gfob-min`, 0.4 % less on the KEVM storage loop and 5 % more on the
/// symbolic map class test, whose map holds up to 2,048 variables; 128 costs within 0.05 % of 64
/// on the KEVM workloads.
pub(crate) const VARIABLE_BRANCHING: usize = 64;

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
    pub(crate) fn of_items(items: &[I]) -> Self {
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
        checked: Checked,
    },
    Internal {
        /// One more than the children's height; a leaf's height is 0.
        height: usize,
        children: Vec<Arc<Node<I>>>,
        summary: NodeSummary<I>,
        checked: Checked,
    },
}

/// Debug builds: whether the one check that reads it, `definedness::check_ceil_free`, has passed
/// the items below a node and the pairs of adjacent items there ([`Chunked::check_unchecked`],
/// and [`Chunked::check_passed_over`] at the subtrees the definedness walk skips), so that a
/// later check of a tree sharing the node skips it (a list's check has no pair condition:
/// `definedness::check_list_items`); nothing in other builds. A node is never changed once
/// built, so the mark stays true of it. The mark is not part of the node's value: a copy of a
/// node is built unmarked.
#[derive(Default)]
struct Checked(#[cfg(debug_assertions)] std::sync::atomic::AtomicBool);

#[cfg(test)]
thread_local! {
    /// Test builds: the internal nodes this thread has built.
    static INTERNAL_NODES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Test builds: the number of internal nodes `run` builds on this thread. An edit of one item
/// copies the internal nodes on one path and, where a node splits or merges, a sibling at each
/// level: at most two per internal level, whatever the number of items.
#[cfg(test)]
pub(crate) fn internal_nodes_during(run: impl FnOnce()) -> usize {
    let before = INTERNAL_NODES.with(std::cell::Cell::get);
    run();
    INTERNAL_NODES.with(std::cell::Cell::get) - before
}

impl<I: Item> Node<I> {
    fn leaf(items: Vec<I>) -> Self {
        let summary = NodeSummary::of_items(&items);
        Self::Leaf {
            items,
            summary,
            checked: Checked::default(),
        }
    }

    fn internal(height: usize, children: Vec<Arc<Self>>) -> Self {
        #[cfg(test)]
        INTERNAL_NODES.with(|count| count.set(count.get() + 1));
        let summary = NodeSummary::of_children(&children);
        Self::Internal {
            height,
            children,
            summary,
            checked: Checked::default(),
        }
    }

    /// A leaf whose group summary the caller knows: `group` is that of `items`.
    fn leaf_with(items: Vec<I>, group: I::Group) -> Self {
        let summary = NodeSummary::of_items_with(&items, group);
        Self::Leaf {
            items,
            summary,
            checked: Checked::default(),
        }
    }

    /// An internal node whose group summary the caller knows: `group` is that of the items
    /// below `children`.
    fn internal_with(height: usize, children: Vec<Arc<Self>>, group: I::Group) -> Self {
        #[cfg(test)]
        INTERNAL_NODES.with(|count| count.set(count.get() + 1));
        let summary = NodeSummary::of_children_with(&children, group);
        Self::Internal {
            height,
            children,
            summary,
            checked: Checked::default(),
        }
    }

    fn summary(&self) -> &NodeSummary<I> {
        match self {
            Self::Leaf { summary, .. } | Self::Internal { summary, .. } => summary,
        }
    }

    #[cfg(debug_assertions)]
    fn checked(&self) -> &std::sync::atomic::AtomicBool {
        match self {
            Self::Leaf { checked, .. } | Self::Internal { checked, .. } => &checked.0,
        }
    }

    fn height(&self) -> usize {
        match self {
            Self::Leaf { .. } => 0,
            Self::Internal { height, .. } => *height,
        }
    }
}

/// Debug builds: checks that read only what changed since the last check.
#[cfg(debug_assertions)]
impl<I: Item, const B: usize> Chunked<I, B> {
    /// Hand the items of each leaf not marked checked to `items`, and to `adjacent` each pair of
    /// adjacent items within such a leaf or straddling two children of an internal node not
    /// marked checked; a marked node is skipped with everything below it. The nodes visited are
    /// returned, for the caller to mark once what it checks of the items has passed.
    ///
    /// Every pair of adjacent items of the sequence is within one leaf or straddles two
    /// children of the lowest node above both, as the last item of one child and the first of the
    /// next, which the children's summaries give. So once a tree has been checked, every item and
    /// every pair of adjacent items has been handed over, and checking a tree made from it by
    /// edits visits only the nodes the edits built: the paths they copied.
    pub(crate) fn check_unchecked<'t>(
        &'t self,
        mut items: impl FnMut(&'t [I]),
        mut adjacent: impl FnMut(&'t I, &'t I),
    ) -> Unchecked<'t, I> {
        let mut visited = Vec::new();
        if let Some(root) = &self.root {
            check_subtree(root, &mut items, &mut adjacent, &mut visited);
        }
        Unchecked(visited)
    }

    /// Hand to `passed` the items a descent by `seek` ([`Chunked::seek`]) passes over without
    /// reading them: every item of a subtree the seek does not admit, and each item of an
    /// admitted leaf that it does not want. Within each subtree not admitted, the pairs of
    /// adjacent items go to `apart`, as [`check_unchecked`](Self::check_unchecked) hands them
    /// over; a node marked checked is skipped with everything below it, there and at the admitted
    /// nodes. Returned, for the caller to mark once the items have passed, are the nodes of each
    /// subtree not admitted in which `apart` accepted every pair. An admitted node is never
    /// returned: it holds an item the descent reads, which a check of the items passed over does
    /// not reach.
    ///
    /// The seek decides which subtrees it skips from their summaries alone, so a summary that
    /// claimed of a subtree what one of its items does not satisfy would hide that item from the
    /// descent; handing the subtree's items over lets the caller check the claim on each of them.
    /// Once a subtree not admitted has passed and is marked, a later descent of a tree sharing it
    /// skips it again without a check, so a tree edited since its last check hands over the
    /// nodes the edits built and the leaves the descent enters.
    pub(crate) fn check_passed_over<'t, S: seek::Seek<I>>(
        &'t self,
        seek: &S,
        mut passed: impl FnMut(&'t I),
        mut apart: impl FnMut(&'t I, &'t I) -> bool,
    ) -> Unchecked<'t, I> {
        use std::sync::atomic::Ordering::Relaxed;
        let mut pending = self.root.iter().map(|root| (root, 0)).collect::<Vec<_>>();
        let mut visited = Vec::new();
        while let Some((node, start)) = pending.pop() {
            if node.checked().load(Relaxed) {
                continue;
            }
            if !seek.admits(start, node.summary()) {
                let mut every_pair_apart = true;
                let mut subtree = Vec::new();
                check_subtree(
                    node,
                    &mut |items: &'t [I]| items.iter().for_each(&mut passed),
                    &mut |left, right| {
                        every_pair_apart = every_pair_apart && apart(left, right);
                    },
                    &mut subtree,
                );
                if every_pair_apart {
                    visited.append(&mut subtree);
                }
                continue;
            }
            match &**node {
                Node::Leaf { items, .. } => {
                    for (offset, item) in items.iter().enumerate() {
                        if !seek.wants(start + offset, item) {
                            passed(item);
                        }
                    }
                }
                Node::Internal { children, .. } => {
                    let mut position = start;
                    for child in children {
                        pending.push((child, position));
                        position += child.summary().count;
                    }
                }
            }
        }
        Unchecked(visited)
    }
}

/// Debug builds: [`Chunked::check_unchecked`] below `root`, appending the nodes visited to
/// `visited`.
#[cfg(debug_assertions)]
fn check_subtree<'t, I: Item>(
    root: &'t Arc<Node<I>>,
    items: &mut impl FnMut(&'t [I]),
    adjacent: &mut impl FnMut(&'t I, &'t I),
    visited: &mut Vec<&'t Arc<Node<I>>>,
) {
    use std::sync::atomic::Ordering::Relaxed;
    // A node shared by several positions of the subtree (`Chunked::repeat`) holds the same items
    // and pairs at each of them, so it is handed over once.
    let mut seen = std::collections::HashSet::new();
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        if node.checked().load(Relaxed) || !seen.insert(Arc::as_ptr(node)) {
            continue;
        }
        match &**node {
            Node::Leaf { items: leaf, .. } => {
                items(leaf);
                for pair in leaf.windows(2) {
                    adjacent(&pair[0], &pair[1]);
                }
            }
            Node::Internal { children, .. } => {
                for pair in children.windows(2) {
                    let (Some(last), Some(first)) =
                        (&pair[0].summary().last, &pair[1].summary().first)
                    else {
                        unreachable!("a node has items")
                    };
                    adjacent(last, first);
                }
                pending.extend(children);
            }
        }
        visited.push(node);
    }
}

/// Debug builds: the nodes a check visited ([`Chunked::check_unchecked`]), to be marked once
/// the check has passed them.
#[cfg(debug_assertions)]
#[must_use]
pub(crate) struct Unchecked<'t, I: Item>(Vec<&'t Arc<Node<I>>>);

#[cfg(debug_assertions)]
impl<I: Item> Unchecked<'_, I> {
    /// No node.
    pub(crate) fn none() -> Self {
        Self(Vec::new())
    }

    /// Mark the nodes checked.
    pub(crate) fn mark(self) {
        for node in self.0 {
            node.checked()
                .store(true, std::sync::atomic::Ordering::Relaxed);
        }
    }
}

/// The sizes of the parts of `n` things cut into parts of `min + 1..b` things, strictly
/// between the fill bounds (one part of all of them when `n <= b`), as even as possible: the
/// number of parts nearest `n/target`, kept between `⌈n/(b-1)⌉` (so no part is full) and
/// `⌊n/(min+1)⌋` (so none is at the minimum), of `⌊n/parts⌋` or one more. For `n > b` that range
/// is not empty when `b > 2·min` and `min >= 2`: `p` parts cover the lengths
/// `p·(min+1)..=p·(b-1)`, two parts start at `2·min + 2 <= b + 1`, and the ranges of `p` and
/// `p + 1` parts (`p >= 2`) meet, since `p·(b - 1) + 1 >= p·2·min + 1 >= (p + 1)·(min + 1)`.
fn even_parts(n: usize, b: usize, min: usize, target: usize) -> impl Iterator<Item = usize> {
    let (parts, base, longer) = even_cut(n, b, min, target);
    (0..parts).map(move |part| base + usize::from(part < longer))
}

/// [`even_parts`] as runs of equal parts, `(size, number of parts)` in order: the longer parts
/// first, then the shorter ones; either run may hold no parts.
fn even_part_runs(n: usize, b: usize, min: usize, target: usize) -> [(usize, usize); 2] {
    let (parts, base, longer) = even_cut(n, b, min, target);
    [(base + 1, longer), (base, parts - longer)]
}

/// The cut [`even_parts`] makes: the number of parts, the size of the shorter parts, and the
/// number of parts one longer than that, which come first.
fn even_cut(n: usize, b: usize, min: usize, target: usize) -> (usize, usize, usize) {
    let parts = if n <= b {
        n.min(1)
    } else {
        // `n / target` rounded to the nearest, without overflowing at `usize::MAX` items.
        let nearest = n / target + (n % target + target / 2) / target;
        nearest.clamp(n.div_ceil(b - 1), n / (min + 1))
    };
    // No parts (and no division) for nothing.
    let base = n.checked_div(parts).unwrap_or(0);
    let longer = n.checked_rem(parts).unwrap_or(0);
    (parts, base, longer)
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

    /// The width a node built from many items or children is given when nothing else decides
    /// it: about midway between `MIN_FILL` and `B` (see [`from_vec`](Self::from_vec)).
    const FILL_TARGET: usize = (Self::MIN_FILL + 1 + B) / 2;

    /// The empty sequence.
    pub(crate) const fn new() -> Self {
        Self { root: None }
    }

    /// The sequence of `items`, in their order, built bottom-up in time linear in their number.
    /// For an ordered collection the caller passes them in nondecreasing order of key.
    ///
    /// Nodes other than the root are filled to about midway between `MIN_FILL` and `B`, not to
    /// `B`: a full node splits at the first insertion below it, so a tree of full nodes would
    /// pay, at its first insertion (and again in each successor of a state that holds it), a
    /// split at every level up to the first node with room, each folding the group summary of
    /// half a node.
    pub(crate) fn from_vec(items: Vec<I>) -> Self {
        let target = Self::FILL_TARGET;
        let mut items = items.into_iter();
        let mut level: Vec<Arc<Node<I>>> = even_parts(items.len(), B, Self::MIN_FILL, target)
            .map(|size| Arc::new(Node::leaf(items.by_ref().take(size).collect())))
            .collect();
        let mut height = 0;
        while level.len() > 1 {
            height += 1;
            let mut nodes = level.into_iter();
            level = even_parts(nodes.len(), B, Self::MIN_FILL, target)
                .map(|size| Arc::new(Node::internal(height, nodes.by_ref().take(size).collect())))
                .collect();
        }
        Self { root: level.pop() }
    }

    /// The sequence of `count` copies of `item`, in the shape [`from_vec`](Self::from_vec) gives
    /// it, built in `O(log² count)` nodes: one node stands for every subtree that holds the same
    /// items in the same shape, so the tree of `count` copies holds `O(log² count)` nodes where
    /// loading the copies one by one fills `count / B` leaves.
    ///
    /// `from_vec` cuts each level into parts of two sizes, the longer ones first
    /// ([`even_part_runs`]). Each level is built here as runs of one node repeated: the parts of
    /// one size that lie within one run are one node, built once, and a part holding a junction
    /// of two runs is built on its own. The leaves are two nodes, with one junction. A cluster of
    /// adjacent junctions spanning at most two nodes falls within at most two parts of the level
    /// above (a part spans at least three), so it stays a cluster of at most two mixed nodes; and
    /// each level adds one junction, its switch of part size. So the level at height `h` holds
    /// at most `h + 1` clusters and the runs between them: at most `3h + 4` distinct nodes
    /// (`repeating_an_item_shares_its_nodes` checks it, and finds at most four).
    pub(crate) fn repeat(item: &I, count: usize) -> Self {
        let target = Self::FILL_TARGET;
        let mut level: Vec<(Arc<Node<I>>, usize)> =
            even_part_runs(count, B, Self::MIN_FILL, target)
                .into_iter()
                .filter(|&(_, parts)| parts > 0)
                .map(|(size, parts)| (Arc::new(Node::leaf(vec![item.clone(); size])), parts))
                .collect();
        let mut height = 0;
        while level.iter().map(|(_, copies)| copies).sum::<usize>() > 1 {
            height += 1;
            level = Self::group_runs(height, level);
        }
        Self {
            root: level.pop().map(|(node, _)| node),
        }
    }

    /// The level above `runs` (nodes of height `height - 1`, each repeated the given number of
    /// times), cut as [`from_vec`](Self::from_vec) cuts it, as runs of nodes of height `height`.
    fn group_runs(height: usize, runs: Vec<(Arc<Node<I>>, usize)>) -> Vec<(Arc<Node<I>>, usize)> {
        let nodes = runs.iter().map(|(_, copies)| copies).sum();
        let mut runs = runs.into_iter();
        // The run being consumed and the copies of its node not yet placed.
        let mut current: Option<(Arc<Node<I>>, usize)> = None;
        let mut level = Vec::new();
        for (size, mut parts) in even_part_runs(nodes, B, Self::MIN_FILL, Self::FILL_TARGET) {
            while parts > 0 {
                let (node, left) =
                    current.get_or_insert_with(|| runs.next().expect("the parts cover the level"));
                if *left >= size {
                    // Parts within the run: one node, repeated.
                    let copies = (*left / size).min(parts);
                    level.push((
                        Arc::new(Node::internal(height, vec![node.clone(); size])),
                        copies,
                    ));
                    *left -= copies * size;
                    parts -= copies;
                    if *left == 0 {
                        current = None;
                    }
                    continue;
                }
                // One part straddling runs.
                let mut children = Vec::with_capacity(size);
                while children.len() < size {
                    let (node, left) = current
                        .get_or_insert_with(|| runs.next().expect("the parts cover the level"));
                    let take = (*left).min(size - children.len());
                    children.extend(std::iter::repeat_n(node.clone(), take));
                    *left -= take;
                    if *left == 0 {
                        current = None;
                    }
                }
                level.push((Arc::new(Node::internal(height, children)), 1));
                parts -= 1;
            }
        }
        level
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

    /// In a sequence ordered as `compare` orders its items against a probe (`Less` for those
    /// before it, `Greater` for those after it), `Ok` with the position of an item `compare`
    /// finds equal to the probe, or `Err` with the position at which the probe would go, as
    /// `slice::binary_search_by` answers. Each internal node on the path picks its child by a
    /// binary search over the children's last items, and the leaf by one over its items, so
    /// `compare` is called about `log2` of the width of each node on one path.
    pub(crate) fn search_by(
        &self,
        mut compare: impl FnMut(&I) -> Ordering,
    ) -> Result<usize, usize> {
        let Some(mut node) = self.root.as_deref() else {
            return Err(0);
        };
        let mut position = 0;
        loop {
            match node {
                Node::Internal { children, .. } => {
                    // Every child before the first whose last item is not below the probe lies
                    // wholly below it.
                    let index = children.partition_point(|child| {
                        compare(child.summary().last.as_ref().expect("a node has items"))
                            == Ordering::Less
                    });
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
                    return items
                        .binary_search_by(compare)
                        .map(|offset| position + offset)
                        .map_err(|offset| position + offset);
                }
            }
        }
    }

    pub(crate) fn to_vec(&self) -> Vec<I> {
        self.iter().cloned().collect()
    }

    /// The number of nodes on a path from the root to a leaf: 0 for the empty sequence.
    #[cfg(test)]
    pub(crate) fn levels(&self) -> usize {
        self.root.as_ref().map_or(0, |root| root.height() + 1)
    }

    /// Whether the sequence is a single leaf: not empty, and at most `B` items with no node
    /// above them.
    pub(crate) fn is_one_leaf(&self) -> bool {
        self.root
            .as_ref()
            .is_some_and(|root| matches!(**root, Node::Leaf { .. }))
    }

    /// Whether this is the only handle of the root: dropping it then frees the root, and the
    /// nodes below it that no other tree shares.
    pub(crate) fn owns_root(&self) -> bool {
        self.root
            .as_ref()
            .is_some_and(|root| Arc::strong_count(root) == 1)
    }

    /// Whether the two sequences are one tree: both empty, or holding the same root node.
    pub(crate) fn shares_root(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (None, None) => true,
            (Some(l), Some(r)) => Arc::ptr_eq(l, r),
            _ => false,
        }
    }

    /// The order of the two item sequences, lexicographic as for slices, with `compare` ordering
    /// two items. A node both sequences hold at the same position is skipped without calling
    /// `compare` on its items.
    pub(crate) fn cmp_by(
        &self,
        other: &Self,
        mut compare: impl FnMut(&I, &I) -> Ordering,
    ) -> Ordering {
        for (left, right) in self.aligned(other) {
            match compare(left, right) {
                Ordering::Equal => {}
                unequal => return unequal,
            }
        }
        self.len().cmp(&other.len())
    }

    /// The pairs of items the two sequences hold at the same positions, in order, up to the end
    /// of the shorter one, but for the items of a node both hold at the same position, which are
    /// the same items and are skipped: the walk opens a node only where the two differ, so two
    /// versions that share all but a few paths cost those paths.
    pub(crate) fn aligned<'a>(&'a self, other: &'a Self) -> Aligned<'a, I> {
        Aligned {
            left: Cursor::new(self.root.as_ref()),
            right: Cursor::new(other.root.as_ref()),
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
        if self.shares_root(other) {
            return true;
        }
        match (&self.root, &other.root) {
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
#[derive(Clone)]
pub(crate) struct Iter<'a, I: Item> {
    front: Vec<slice::Iter<'a, Arc<Node<I>>>>,
    front_items: slice::Iter<'a, I>,
    back: Vec<slice::Iter<'a, Arc<Node<I>>>>,
    back_items: slice::Iter<'a, I>,
    remaining: usize,
}

impl<'a, I: Item> Iter<'a, I> {
    /// The items below `root`. A leaf root is opened at once at both ends, so iterating a tree
    /// of one leaf (a collection of at most `B` items) keeps no stack of levels and allocates
    /// nothing; the count of items left keeps the two ends from crossing, as in a shared leaf
    /// further down.
    fn new(root: Option<&'a Arc<Node<I>>>) -> Self {
        let mut iter = Self {
            front: Vec::new(),
            front_items: [].iter(),
            back: Vec::new(),
            back_items: [].iter(),
            remaining: root.map_or(0, |root| root.summary().count),
        };
        match root.map(|root| &**root) {
            None => {}
            Some(Node::Leaf { items, .. }) => {
                iter.front_items = items.iter();
                iter.back_items = items.iter();
            }
            Some(Node::Internal { children, .. }) => {
                iter.front.push(children.iter());
                iter.back.push(children.iter());
            }
        }
        iter
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

/// The rest of a sequence being walked: a stack of slices of nodes or items, whose
/// concatenation, innermost first, is what is left. The innermost slice is held apart from the
/// stack, and opening a node that was the last of its slice replaces that slice instead of
/// stacking an empty one, so walking a tree of one leaf (a collection of at most `B` items)
/// allocates nothing.
struct Cursor<'a, I: Item> {
    top: Rest<'a, I>,
    stack: Vec<Rest<'a, I>>,
}

enum Rest<'a, I: Item> {
    Nodes(&'a [Arc<Node<I>>]),
    Items(&'a [I]),
}

impl<'a, I: Item> Cursor<'a, I> {
    fn new(root: Option<&'a Arc<Node<I>>>) -> Self {
        Self {
            top: Rest::Nodes(root.map_or(&[][..], slice::from_ref)),
            stack: Vec::new(),
        }
    }

    /// The node or item that comes next, if any.
    fn peek(&mut self) -> Option<Next<'a, I>> {
        loop {
            match self.top {
                Rest::Nodes([node, ..]) => return Some(Next::Node(node)),
                Rest::Items([item, ..]) => return Some(Next::Item(item)),
                Rest::Nodes([]) | Rest::Items([]) => self.top = self.stack.pop()?,
            }
        }
    }

    /// Step past what [`peek`](Self::peek) returned.
    fn skip(&mut self) {
        match &mut self.top {
            Rest::Nodes(nodes) => *nodes = &nodes[1..],
            Rest::Items(items) => *items = &items[1..],
        }
    }

    /// Replace the node [`peek`](Self::peek) returned by its contents.
    fn open(&mut self) {
        let Some(Next::Node(node)) = self.peek() else {
            return;
        };
        self.skip();
        let contents = match &**node {
            Node::Leaf { items, .. } => Rest::Items(items),
            Node::Internal { children, .. } => Rest::Nodes(children),
        };
        let outer = std::mem::replace(&mut self.top, contents);
        if !matches!(outer, Rest::Nodes([]) | Rest::Items([])) {
            self.stack.push(outer);
        }
    }
}

/// The pairs of items two sequences hold at the same positions ([`Chunked::aligned`]).
pub(crate) struct Aligned<'a, I: Item> {
    left: Cursor<'a, I>,
    right: Cursor<'a, I>,
}

impl<'a, I: Item> Iterator for Aligned<'a, I> {
    type Item = (&'a I, &'a I);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (open_left, open_right) = match (self.left.peek()?, self.right.peek()?) {
                (Next::Node(left), Next::Node(right)) if Arc::ptr_eq(left, right) => {
                    self.left.skip();
                    self.right.skip();
                    continue;
                }
                (Next::Item(left), Next::Item(right)) => {
                    self.left.skip();
                    self.right.skip();
                    return Some((left, right));
                }
                // Open the taller of the two (both at an equal height), until both stand at
                // items or at one shared node.
                (left, right) => (left.level() >= right.level(), right.level() >= left.level()),
            };
            if open_left {
                self.left.open();
            }
            if open_right {
                self.right.open();
            }
        }
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
            Node::Leaf { items, summary, .. } => {
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

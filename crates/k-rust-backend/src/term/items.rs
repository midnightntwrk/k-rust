//! The items of a map, list or set term, behind the interface of their tree.
//!
//! [`Items`] is the type of the item fields of [`TermKind::Map`](super::TermKind::Map),
//! [`TermKind::List`](super::TermKind::List) and [`TermKind::Set`](super::TermKind::Set): a
//! map's entries, a list's heads and tails, a set's elements. Its methods are those of the
//! persistent tree `Chunked` (design K22, revision 2, §11): length, iteration from either end,
//! access by position, ordered search, and edits that return a new sequence and leave the old one
//! as it is. Code that reads or builds a collection does so through these methods only, so the
//! representation behind them can change without touching it.
//!
//! # Two backings
//!
//! Each item type chooses its backing (`Stored::IN_TREE`), so every sequence of one item type
//! has the same one:
//!
//! - a map's entries, `(Term, Term)`, are a `Chunked` tree. An edit copies the path to the
//!   items it changes and shares the rest with the sequence it was made from, and the summary of
//!   the root (`Items::summary`) gives what the attributes of the map term need without
//!   reading the entries (`ItemSummary`, and the multiset of the variables they mention);
//! - a list's and a set's items, `Term`, are still one vector, whose edits copy it.
//!
//! Equality and order are those of the item sequence under both backings, as for the vector. The
//! hash is the vector's for a vector and the tree's sequence hash for a tree: a polynomial hash
//! of the sequence that does not depend on the tree's shape, so equal sequences built by
//! different edits hash alike, and computing it costs a node's summary rather than a pass over
//! the items.
//!
//! # Crate-private bound
//!
//! The item types are bounded by the crate's own `Stored`, whose supertrait `Item` names the
//! tree's summary types; neither is part of the public interface. A dependent crate uses
//! `Items<Term>` and `Items<(Term, Term)>`, whose bounds hold, and never names the trait, so the
//! `private_bounds` lint, which warns that such a crate cannot write the bound itself, is allowed
//! here.
#![allow(private_bounds)]

use std::{
    borrow::Cow,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    iter::FusedIterator,
    ops::RangeBounds,
    slice, vec,
};

use rustc_hash::FxHasher;

use super::{
    KeyHeader, Sort, Term, Variable,
    chunked::{
        self, Chunked, Item, NodeSummary, Summary,
        multiset::Multiset,
        summary::{Any, Count, Failing, Saturating, Uniform},
    },
    key_header,
};

/// An item type of a collection term, and the backing its sequences use.
pub(crate) trait Stored: Item {
    /// Whether the sequences of this item type are [`Chunked`] trees rather than vectors.
    const IN_TREE: bool;
}

impl Stored for (Term, Term) {
    const IN_TREE: bool = true;
}

impl Stored for Term {
    const IN_TREE: bool = false;
}

/// A sequence of collection items (see the [module documentation](self)).
///
/// The items of a map or a set are in nondecreasing order (map entries by key, then value); the
/// methods called ordered rely on it, and a constructor that does not establish it is the
/// caller's responsibility, as for [`Term::map`] and [`Term::set`], which order what they are
/// given. A list's items are in the list's order.
pub struct Items<T: Stored>(Backing<T>);

enum Backing<T: Item> {
    Vec(Vec<T>),
    Tree(Chunked<T>),
}

/// What an ordered sequence of items is searched by: a map entry's key, a set element itself.
pub trait Keyed {
    type Key: Ord + ?Sized;

    fn key(&self) -> &Self::Key;
}

impl Keyed for Term {
    type Key = Term;

    fn key(&self) -> &Term {
        self
    }
}

impl Keyed for (Term, Term) {
    type Key = Term;

    fn key(&self) -> &Term {
        &self.0
    }
}

impl<T: Stored> Items<T> {
    /// The empty sequence.
    pub const fn new() -> Self {
        Self(if T::IN_TREE {
            Backing::Tree(Chunked::new())
        } else {
            Backing::Vec(Vec::new())
        })
    }

    /// The sequence of `items`, in the order given. A tree is built bottom-up, in time linear in
    /// the number of items.
    pub fn from_vec(items: Vec<T>) -> Self {
        Self(if T::IN_TREE {
            Backing::Tree(Chunked::from_vec(items))
        } else {
            Backing::Vec(items)
        })
    }

    pub fn len(&self) -> usize {
        match &self.0 {
            Backing::Vec(items) => items.len(),
            Backing::Tree(tree) => tree.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        match &self.0 {
            Backing::Vec(items) => items.is_empty(),
            Backing::Tree(tree) => tree.is_empty(),
        }
    }

    /// The items in order; the iterator also runs from the back.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter(match &self.0 {
            Backing::Vec(items) => IterBacking::Slice(items.iter()),
            Backing::Tree(tree) => IterBacking::Tree(tree.iter()),
        })
    }

    /// The items at the positions of `range`, which lies within the sequence, in order.
    pub fn range(&self, range: impl RangeBounds<usize>) -> Iter<'_, T> {
        Iter(match &self.0 {
            Backing::Vec(items) => {
                let range = (range.start_bound().cloned(), range.end_bound().cloned());
                IterBacking::Slice(items[range].iter())
            }
            Backing::Tree(tree) => IterBacking::Tree(tree.range(range)),
        })
    }

    /// The item at position `index`, if the sequence is that long.
    pub fn get(&self, index: usize) -> Option<&T> {
        match &self.0 {
            Backing::Vec(items) => items.get(index),
            Backing::Tree(tree) => tree.get(index),
        }
    }

    pub fn first(&self) -> Option<&T> {
        match &self.0 {
            Backing::Vec(items) => items.first(),
            Backing::Tree(tree) => tree.summary().and_then(|summary| summary.first.as_ref()),
        }
    }

    pub fn last(&self) -> Option<&T> {
        match &self.0 {
            Backing::Vec(items) => items.last(),
            Backing::Tree(tree) => tree.summary().and_then(|summary| summary.last.as_ref()),
        }
    }

    /// In a sequence ordered as `compare` orders its items against a probe (`Less` for those
    /// before it, `Greater` for those after it), `Ok` with the position of an item `compare`
    /// finds equal to the probe, or `Err` with the position at which the probe would go.
    pub fn search_by(&self, compare: impl FnMut(&T) -> Ordering) -> Result<usize, usize> {
        match &self.0 {
            Backing::Vec(items) => items.binary_search_by(compare),
            Backing::Tree(tree) => tree.search_by(compare),
        }
    }

    /// The number of leading items for which `before` holds, when it holds for a prefix of the
    /// sequence and for no item after it.
    pub fn partition_point(&self, before: impl FnMut(&T) -> bool) -> usize {
        match &self.0 {
            Backing::Vec(items) => items.partition_point(before),
            Backing::Tree(tree) => tree.partition_point(before),
        }
    }

    pub fn to_vec(&self) -> Vec<T> {
        match &self.0 {
            Backing::Vec(items) => items.clone(),
            Backing::Tree(tree) => tree.to_vec(),
        }
    }

    /// The first `index` items and the rest; `index` is at most the length.
    pub fn split_at(&self, index: usize) -> (Self, Self) {
        match &self.0 {
            Backing::Vec(items) => {
                let (left, right) = items.split_at(index);
                (
                    Self(Backing::Vec(left.to_vec())),
                    Self(Backing::Vec(right.to_vec())),
                )
            }
            Backing::Tree(tree) => {
                let (left, right) = tree.split_at(index);
                (Self(Backing::Tree(left)), Self(Backing::Tree(right)))
            }
        }
    }

    /// The items of this sequence followed by those of `other`.
    pub fn join(&self, other: &Self) -> Self {
        match (&self.0, &other.0) {
            (Backing::Tree(left), Backing::Tree(right)) => Self(Backing::Tree(left.join(right))),
            _ => Self::from_vec(self.iter().chain(other).cloned().collect()),
        }
    }

    /// The sequence with `item` inserted at position `index`, which is at most the length.
    pub fn insert_at(&self, index: usize, item: T) -> Self {
        match &self.0 {
            Backing::Vec(items) => {
                let mut items = items.clone();
                items.insert(index, item);
                Self(Backing::Vec(items))
            }
            Backing::Tree(tree) => Self(Backing::Tree(tree.insert_at(index, item))),
        }
    }

    /// The sequence without the item at position `index`, which is below the length, and that
    /// item.
    pub fn remove_at(&self, index: usize) -> (Self, T) {
        match &self.0 {
            Backing::Vec(items) => {
                let mut items = items.clone();
                let item = items.remove(index);
                (Self(Backing::Vec(items)), item)
            }
            Backing::Tree(tree) => {
                let (tree, item) = tree.remove_at(index);
                (Self(Backing::Tree(tree)), item)
            }
        }
    }

    /// The sequence with the item at position `index`, which is below the length, replaced by
    /// `item`.
    pub fn replace_at(&self, index: usize, item: T) -> Self {
        match &self.0 {
            Backing::Vec(items) => {
                let mut items = items.clone();
                items[index] = item;
                Self(Backing::Vec(items))
            }
            Backing::Tree(tree) => Self(Backing::Tree(tree.replace_at(index, item))),
        }
    }

    /// The pairs of items the two sequences hold at the same positions, in order, up to the end
    /// of the shorter one. Two trees skip the nodes they hold at the same position, whose items
    /// are the same (`Chunked::aligned`), so comparing two versions of a collection reads the
    /// paths where they differ.
    pub(crate) fn aligned<'a>(&'a self, other: &'a Self) -> Aligned<'a, T> {
        Aligned(match (&self.0, &other.0) {
            (Backing::Tree(left), Backing::Tree(right)) => {
                AlignedBacking::Tree(left.aligned(right))
            }
            _ => AlignedBacking::Zip(self.iter().zip(other.iter())),
        })
    }

    /// The most item comparisons [`search_by`](Self::search_by) makes: a binary search makes at
    /// most `⌈log2 w⌉ + 1` over `w` items, a vector's is one over all of them, and a tree's is one
    /// on each node of a path from the root, over at most `B` children or items.
    #[cfg(test)]
    pub(crate) fn search_comparison_bound(&self) -> usize {
        let binary = |width: usize| width.next_power_of_two().ilog2() as usize + 1;
        match &self.0 {
            Backing::Vec(items) => binary(items.len()),
            Backing::Tree(tree) => tree.levels() * binary(chunked::DEFAULT_BRANCHING),
        }
    }

    /// The most item comparisons one insertion or removal at a position makes: none in a
    /// vector, and in a tree those of the summaries of the nodes it builds on one path, each of
    /// which compares the keys of its adjacent items or children (`collision`); a node built
    /// from a node and its sibling, when one would fall below the fill minimum, holds fewer than
    /// `2B` of them.
    #[cfg(test)]
    pub(crate) fn path_copy_comparison_bound(&self) -> usize {
        match &self.0 {
            Backing::Vec(_) => 0,
            Backing::Tree(tree) => tree.levels() * 2 * chunked::DEFAULT_BRANCHING,
        }
    }

    /// Whether the two sequences are trees holding the same root node.
    #[cfg(test)]
    pub(crate) fn shares_root(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Backing::Tree(left), Backing::Tree(right)) => left.shares_root(right),
            _ => false,
        }
    }

    /// The summary of the whole sequence: the root's for a tree, the identity for the empty
    /// sequence, and the fold of the items for a vector (which reads every item).
    pub(crate) fn summary(&self) -> Cow<'_, NodeSummary<T>> {
        match &self.0 {
            Backing::Vec(items) => Cow::Owned(NodeSummary::of_items(items)),
            Backing::Tree(tree) => tree
                .summary()
                .map_or_else(|| Cow::Owned(NodeSummary::identity()), Cow::Borrowed),
        }
    }

    /// Whether dropping this sequence may free an item: its vector, or the root of its tree, is
    /// not shared with another sequence. An item a shared root holds is held by that other
    /// sequence too.
    pub(crate) fn may_free_items(&self) -> bool {
        match &self.0 {
            Backing::Vec(items) => !items.is_empty(),
            Backing::Tree(tree) => tree.owns_root(),
        }
    }

    /// Debug builds: hand the items a check has not passed to `items`, and the pairs of
    /// adjacent items among them or next to them to `adjacent`. A tree hands over the leaves
    /// and junctions not marked checked and returns their nodes, which the caller marks once the
    /// items have passed (`Chunked::check_unchecked`), so a sequence edited since its last check
    /// hands over the paths the edits copied; a vector hands over all of its items every time.
    #[cfg(debug_assertions)]
    pub(crate) fn check_unchecked<'t>(
        &'t self,
        mut items: impl FnMut(&'t [T]),
        mut adjacent: impl FnMut(&'t T, &'t T),
    ) -> chunked::Unchecked<'t, T> {
        match &self.0 {
            Backing::Vec(vector) => {
                items(vector);
                for pair in vector.windows(2) {
                    adjacent(&pair[0], &pair[1]);
                }
                chunked::Unchecked::none()
            }
            Backing::Tree(tree) => tree.check_unchecked(items, adjacent),
        }
    }

    /// Hand each item of which this sequence held the last handle to `each`, in no particular
    /// order, through a work list: a tree node shared with another sequence is only released.
    pub(crate) fn dismantle(self, each: impl FnMut(T)) {
        match self.0 {
            Backing::Vec(items) => items.into_iter().for_each(each),
            Backing::Tree(tree) => {
                let mut work = chunked::Dismantle::new();
                work.push(tree);
                work.for_each(each);
            }
        }
    }
}

impl<T: Stored + Keyed> Items<T> {
    /// In an ordered sequence, `Ok` with the position of the first item whose key is `key`, or
    /// `Err` with the position at which an item of that key would go.
    pub fn search(&self, key: &<T as Keyed>::Key) -> Result<usize, usize> {
        let position = self.partition_point(|item| Keyed::key(item) < key);
        match self.get(position) {
            Some(item) if Keyed::key(item) == key => Ok(position),
            _ => Err(position),
        }
    }

    /// In an ordered sequence, the items whose key is below `key` and the rest.
    pub fn split_at_key(&self, key: &<T as Keyed>::Key) -> (Self, Self) {
        self.split_at(self.partition_point(|item| Keyed::key(item) < key))
    }
}

impl<T: Stored + Keyed<Key = Term> + Item<Summary = ItemSummary>> Items<T> {
    /// The number of items whose key is not constructor-like: the root summary's count for a
    /// tree, a pass over the items for a vector.
    pub(crate) fn symbolic_keys(&self) -> usize {
        match &self.0 {
            Backing::Vec(items) => items.iter().filter(|item| symbolic_key(*item)).count(),
            Backing::Tree(tree) => tree
                .summary()
                .map_or(0, |summary| summary.extra.symbolic_keys()),
        }
    }

    /// The items whose key is not constructor-like, in order. A tree is descended only into the
    /// subtrees whose summary counts such a key, so the `s` items are reached through their
    /// ancestors, `O(s log n)` nodes; a vector is filtered.
    pub(crate) fn symbolic_keyed(&self) -> impl Iterator<Item = &T> {
        self.symbolic_keyed_at().map(|(_, item)| item)
    }

    /// [`symbolic_keyed`](Self::symbolic_keyed), each item with its position.
    pub(crate) fn symbolic_keyed_at(&self) -> impl Iterator<Item = (usize, &T)> {
        let (vector, tree) = match &self.0 {
            // No descent when the root's summary counts none.
            Backing::Tree(_) if self.symbolic_keys() == 0 => (None, None),
            Backing::Vec(items) => (
                Some(
                    items
                        .iter()
                        .enumerate()
                        .filter(|(_, item)| symbolic_key(*item)),
                ),
                None,
            ),
            Backing::Tree(tree) => (
                None,
                Some(tree.seek(chunked::seek::Where::new(
                    |summary: &NodeSummary<T>| summary.extra.symbolic_keys() > 0,
                    |item: &T| symbolic_key(item),
                ))),
            ),
        };
        vector
            .into_iter()
            .flatten()
            .chain(tree.into_iter().flatten())
    }
}

/// Whether `item`'s key is not constructor-like.
fn symbolic_key<T: Keyed<Key = Term>>(item: &T) -> bool {
    !Keyed::key(item).attributes().constructor_like
}

impl<T: Stored + Ord> Items<T> {
    /// In an ordered sequence, the sequence with each item `wants` picks replaced by `change`'s
    /// result, when it returns one, and in order again. A tree is entered only where `admits`
    /// holds of a subtree's summary, which it must wherever an item `wants` picks is below; it
    /// copies the paths to the changed items and moves those that are no longer in order
    /// (`Chunked::rebuild_where`), so the work is that of the items reached. A vector is
    /// rebuilt and sorted.
    pub(crate) fn rebuild_where(
        &self,
        admits: impl Fn(&NodeSummary<T>) -> bool,
        wants: impl Fn(&T) -> bool,
        mut change: impl FnMut(&T) -> Option<T>,
    ) -> Self {
        match &self.0 {
            Backing::Vec(items) => {
                let mut items = items
                    .iter()
                    .map(|item| {
                        wants(item)
                            .then(|| change(item))
                            .flatten()
                            .unwrap_or_else(|| item.clone())
                    })
                    .collect::<Vec<_>>();
                items.sort();
                Self(Backing::Vec(items))
            }
            Backing::Tree(tree) => Self(Backing::Tree(
                tree.rebuild_where(&chunked::seek::Where::new(admits, wants), change),
            )),
        }
    }

    /// In an ordered sequence, the sequence with `item` added after the items not above it.
    pub fn insert(&self, item: T) -> Self {
        self.insert_at(self.partition_point(|other| *other <= item), item)
    }

    /// In an ordered sequence, the sequence without one item equal to `item`; `None` when it
    /// holds none.
    pub fn remove(&self, item: &T) -> Option<Self> {
        let index = self.partition_point(|other| other < item);
        (self.get(index) == Some(item)).then(|| self.remove_at(index).0)
    }

    /// The ordered sequence of the items of the two ordered sequences, each kept as often as
    /// the two hold it together. Two trees share the nodes of the taller one whose range
    /// receives none of the other's items (`Chunked::union`).
    pub fn union(&self, other: &Self) -> Self {
        if let (Backing::Tree(left), Backing::Tree(right)) = (&self.0, &other.0) {
            return Self(Backing::Tree(left.union(right)));
        }
        let mut items = Vec::with_capacity(self.len() + other.len());
        let (mut left, mut right) = (self.iter().peekable(), other.iter().peekable());
        loop {
            let next = match (left.peek(), right.peek()) {
                (Some(l), Some(r)) => {
                    if r < l {
                        right.next()
                    } else {
                        left.next()
                    }
                }
                (Some(_), None) => left.next(),
                (None, _) => right.next(),
            };
            match next {
                Some(item) => items.push(item.clone()),
                None => return Self::from_vec(items),
            }
        }
    }
}

impl<T: Stored> Clone for Items<T> {
    fn clone(&self) -> Self {
        Self(match &self.0 {
            Backing::Vec(items) => Backing::Vec(items.clone()),
            Backing::Tree(tree) => Backing::Tree(tree.clone()),
        })
    }
}

/// Equal when the item sequences are. One item type has one backing, so two sequences compared
/// here have the same one; the comparison of the items in order covers any other case.
impl<T: Stored> PartialEq for Items<T> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Backing::Vec(left), Backing::Vec(right)) => left == right,
            (Backing::Tree(left), Backing::Tree(right)) => left == right,
            _ => self.len() == other.len() && self.iter().eq(other.iter()),
        }
    }
}

impl<T: Stored> Eq for Items<T> {}

/// The lexicographic order of the item sequences, as for the vector.
impl<T: Stored + Ord> Ord for Items<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (&self.0, &other.0) {
            (Backing::Vec(left), Backing::Vec(right)) => left.cmp(right),
            (Backing::Tree(left), Backing::Tree(right)) => left.cmp(right),
            _ => self.iter().cmp(other.iter()),
        }
    }
}

impl<T: Stored + Ord> PartialOrd for Items<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// A vector hashes as a vector does; a tree writes its sequence hash, which equal sequences share
/// whatever the tree's shape (see the [module documentation](self)).
impl<T: Stored + Hash> Hash for Items<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self.0 {
            Backing::Vec(items) => items.hash(state),
            Backing::Tree(tree) => tree.hash(state),
        }
    }
}

impl<T: Stored> Default for Items<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// The items' own debug form, as a vector of them prints it.
impl<T: Stored> fmt::Debug for Items<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_list().entries(self.iter()).finish()
    }
}

impl<T: Stored> From<Vec<T>> for Items<T> {
    fn from(items: Vec<T>) -> Self {
        Self::from_vec(items)
    }
}

/// The items in order, as a vector.
impl<T: Stored> From<Items<T>> for Vec<T> {
    fn from(items: Items<T>) -> Self {
        match items.0 {
            Backing::Vec(items) => items,
            Backing::Tree(tree) => tree.to_vec(),
        }
    }
}

impl<T: Stored> FromIterator<T> for Items<T> {
    fn from_iter<I: IntoIterator<Item = T>>(items: I) -> Self {
        Self::from_vec(items.into_iter().collect())
    }
}

impl<'a, T: Stored> IntoIterator for &'a Items<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

/// The items in order, taken out of the sequence (a tree's are copied out of it first).
impl<T: Stored> IntoIterator for Items<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter(Vec::from(self).into_iter())
    }
}

/// The items of an [`Items`] in order, from either end.
pub struct Iter<'a, T: Stored>(IterBacking<'a, T>);

enum IterBacking<'a, T: Item> {
    Slice(slice::Iter<'a, T>),
    Tree(chunked::Iter<'a, T>),
}

impl<T: Stored> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Self(match &self.0 {
            IterBacking::Slice(items) => IterBacking::Slice(items.clone()),
            IterBacking::Tree(items) => IterBacking::Tree(items.clone()),
        })
    }
}

impl<T: Stored> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Iter")
            .field("remaining", &self.len())
            .finish_non_exhaustive()
    }
}

impl<'a, T: Stored> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match &mut self.0 {
            IterBacking::Slice(items) => items.next(),
            IterBacking::Tree(items) => items.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.0 {
            IterBacking::Slice(items) => items.size_hint(),
            IterBacking::Tree(items) => items.size_hint(),
        }
    }

    fn nth(&mut self, n: usize) -> Option<&'a T> {
        match &mut self.0 {
            IterBacking::Slice(items) => items.nth(n),
            IterBacking::Tree(items) => items.nth(n),
        }
    }
}

impl<T: Stored> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            IterBacking::Slice(items) => items.next_back(),
            IterBacking::Tree(items) => items.next_back(),
        }
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        match &mut self.0 {
            IterBacking::Slice(items) => items.nth_back(n),
            IterBacking::Tree(items) => items.nth_back(n),
        }
    }
}

impl<T: Stored> ExactSizeIterator for Iter<'_, T> {}

impl<T: Stored> FusedIterator for Iter<'_, T> {}

/// The pairs of items two sequences hold at the same positions ([`Items::aligned`]).
pub(crate) struct Aligned<'a, T: Stored>(AlignedBacking<'a, T>);

enum AlignedBacking<'a, T: Stored> {
    Zip(std::iter::Zip<Iter<'a, T>, Iter<'a, T>>),
    Tree(chunked::Aligned<'a, T>),
}

impl<'a, T: Stored> Iterator for Aligned<'a, T> {
    type Item = (&'a T, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        let pair = match &mut self.0 {
            AlignedBacking::Zip(pairs) => pairs.next(),
            AlignedBacking::Tree(pairs) => pairs.next(),
        };
        #[cfg(test)]
        if pair.is_some() {
            ALIGNED_PAIRS.with(|count| count.set(count.get() + 1));
        }
        pair
    }
}

#[cfg(test)]
thread_local! {
    /// Test builds: the pairs of items this thread's [`Aligned`] walks have handed over.
    static ALIGNED_PAIRS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The items of an [`Items`] in order, taken out of it.
#[derive(Debug)]
pub struct IntoIter<T>(vec::IntoIter<T>);

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.0.next_back()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> FusedIterator for IntoIter<T> {}

/// A flag of [`TermAttributes`](super::TermAttributes) that holds of a collection term only if
/// it holds of each of its items; an [`ItemSummary`] counts the items failing each.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Flag {
    Evaluated,
    ValueClaimed,
    ConstructorLike,
    ConcreteAfterNormalization,
    CanBeEvaluated,
    CeilFree,
}

/// The number of [`Flag`]s.
const FLAGS: usize = 6;

impl Flag {
    /// Whether every term of `terms` has this flag.
    fn of_all(self, terms: &[&Term]) -> bool {
        terms.iter().all(|term| {
            let attributes = term.attributes();
            match self {
                Self::Evaluated => attributes.evaluated,
                Self::ValueClaimed => attributes.value_claimed,
                Self::ConstructorLike => attributes.constructor_like,
                Self::ConcreteAfterNormalization => attributes.concrete_after_normalization,
                Self::CanBeEvaluated => attributes.can_be_evaluated,
                Self::CeilFree => attributes.ceil_free,
            }
        })
    }
}

/// [`KeyHeader`] as a value a summary holds: the class of a key whose distinctness from another
/// key of the class `structurally_distinct_after_normalization` decides.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Header {
    DomainValue,
    Injection { source: Sort, target: Sort },
}

impl Header {
    fn of(key: &Term) -> Option<Self> {
        key_header(key).map(|header| match header {
            KeyHeader::DomainValue => Self::DomainValue,
            KeyHeader::Injection { source, target } => Self::Injection {
                source: source.clone(),
                target: target.clone(),
            },
        })
    }
}

/// What the attributes of a collection term need from its items, as a [`Summary`] of constant
/// size: the attributes that are a conjunction, a disjunction or a saturating sum over the
/// item terms, the key header all keys share, and the number of keys that are not
/// constructor-like. With the item count, the repeated-key flag and the hash every node keeps
/// ([`NodeSummary`]) and the multiset of the variables the items mention (the group summary),
/// the root's summary gives every attribute of a map term but those its rest adds, without
/// reading the entries.
///
/// An item is a set or list element (one term, which is its own key) or a map entry (the key
/// and the value; the key alone gives the header and the symbolic-key count).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct ItemSummary {
    failing: Failing<FLAGS>,
    header: Uniform<Option<Header>>,
    macro_or_alias: Any,
    k_cells: Saturating<2>,
    symbolic_keys: Count,
    /// Debug builds: the sorts of an item's first and last term (a map entry's key and value, an
    /// element twice), shared by all items or `Mixed`.
    #[cfg(debug_assertions)]
    sorts: Uniform<(Sort, Sort)>,
}

impl ItemSummary {
    /// The summary of the item whose terms are `terms` and whose key is `key`, one of them.
    fn of(key: &Term, terms: &[&Term]) -> Self {
        let flags = [
            Flag::Evaluated,
            Flag::ValueClaimed,
            Flag::ConstructorLike,
            Flag::ConcreteAfterNormalization,
            Flag::CanBeEvaluated,
            Flag::CeilFree,
        ];
        Self {
            failing: Failing::of(flags.map(|flag| flag.of_all(terms))),
            header: Uniform::One(Header::of(key)),
            macro_or_alias: Any(terms
                .iter()
                .any(|term| term.attributes().has_macro_or_alias)),
            k_cells: Saturating::of(
                terms
                    .iter()
                    .map(|term| usize::from(term.attributes().k_cells))
                    .sum(),
            ),
            symbolic_keys: Count::of(!key.attributes().constructor_like),
            #[cfg(debug_assertions)]
            sorts: Uniform::One((
                terms.first().map_or_else(|| key.sort(), |term| term.sort()),
                terms.last().map_or_else(|| key.sort(), |term| term.sort()),
            )),
        }
    }

    /// Debug builds: whether each item's first term is of sort `first` and its last of sort
    /// `last` (a map entry's key and value sorts, an element's sort twice); true for no item.
    #[cfg(debug_assertions)]
    pub(crate) fn all_of_sorts(&self, first: &Sort, last: &Sort) -> bool {
        match &self.sorts {
            Uniform::Empty => true,
            Uniform::One((one, other)) => one == first && other == last,
            Uniform::Mixed => false,
        }
    }

    /// Whether every item has `flag`: of a map entry, both its key and its value.
    pub(crate) fn holds(&self, flag: Flag) -> bool {
        self.failing.holds(flag as usize)
    }

    /// Whether every key has a [`Header`] and all share one (`oneHeader` in the Lean model);
    /// true for no key.
    pub(crate) fn keys_share_one_header(&self) -> bool {
        matches!(self.header, Uniform::Empty | Uniform::One(Some(_)))
    }

    pub(crate) fn has_macro_or_alias(&self) -> bool {
        self.macro_or_alias.0
    }

    /// The `k_cells` attributes of the item terms, summed and saturated at 2.
    pub(crate) fn k_cells(&self) -> u8 {
        u8::try_from(self.k_cells.get()).expect("a count saturated at 2")
    }

    /// The number of items whose key is not constructor-like.
    pub(crate) fn symbolic_keys(&self) -> usize {
        self.symbolic_keys.0
    }
}

impl Summary for ItemSummary {
    fn identity() -> Self {
        Self {
            failing: Failing::identity(),
            header: Uniform::identity(),
            macro_or_alias: Any::identity(),
            k_cells: Saturating::identity(),
            symbolic_keys: Count::identity(),
            #[cfg(debug_assertions)]
            sorts: Uniform::identity(),
        }
    }

    fn combine(self, right: &Self) -> Self {
        Self {
            failing: self.failing.combine(&right.failing),
            header: self.header.combine(&right.header),
            macro_or_alias: self.macro_or_alias.combine(&right.macro_or_alias),
            k_cells: self.k_cells.combine(&right.k_cells),
            symbolic_keys: self.symbolic_keys.combine(&right.symbolic_keys),
            #[cfg(debug_assertions)]
            sorts: self.sorts.combine(&right.sorts),
        }
    }
}

/// The variables the terms mention, each once: an item's share of the multiset that counts, for
/// each variable, the items mentioning it.
fn mentioned(terms: &[&Term]) -> Multiset<Variable> {
    match terms {
        [term] => Multiset::of(term.attributes().variables.iter().cloned()),
        _ => {
            let mut variables: Vec<Variable> = terms
                .iter()
                .flat_map(|term| term.attributes().variables.iter().cloned())
                .collect();
            variables.sort_unstable();
            variables.dedup();
            Multiset::of(variables)
        }
    }
}

/// A set or list element: its own key, hashed by the hash the term stores.
impl Item for Term {
    type Key = Term;
    type Summary = ItemSummary;
    type Group = Multiset<Variable>;

    fn key(&self) -> &Term {
        self
    }

    fn hash64(&self) -> u64 {
        self.attributes().hash
    }

    fn summary(&self) -> ItemSummary {
        ItemSummary::of(self, &[self])
    }

    fn group(&self) -> Multiset<Variable> {
        mentioned(&[self])
    }
}

#[cfg(test)]
thread_local! {
    /// Test builds: the map entries whose own summary this thread has computed, which a node
    /// does for each entry it holds when it is built from its entries.
    static ENTRY_SUMMARIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Test builds: the number of map entries whose own summary `run` computes on this thread.
#[cfg(test)]
pub(crate) fn entry_summaries_during(run: impl FnOnce()) -> usize {
    let before = ENTRY_SUMMARIES.with(std::cell::Cell::get);
    run();
    ENTRY_SUMMARIES.with(std::cell::Cell::get) - before
}

/// A map entry: searched by its key, hashed by the hashes its two terms store.
impl Item for (Term, Term) {
    type Key = Term;
    type Summary = ItemSummary;
    type Group = Multiset<Variable>;

    fn key(&self) -> &Term {
        &self.0
    }

    fn hash64(&self) -> u64 {
        let mut hasher = FxHasher::default();
        hasher.write_u64(self.0.attributes().hash);
        hasher.write_u64(self.1.attributes().hash);
        hasher.finish()
    }

    fn summary(&self) -> ItemSummary {
        #[cfg(test)]
        ENTRY_SUMMARIES.with(|count| count.set(count.get() + 1));
        ItemSummary::of(&self.0, &[&self.0, &self.1])
    }

    fn group(&self) -> Multiset<Variable> {
        if self.0.attributes().variables.is_empty() && self.1.attributes().variables.is_empty() {
            return Multiset::new();
        }
        mentioned(&[&self.0, &self.1])
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::term::{CollectionSymbols, MapDefinition, TermKind, chunked::DEFAULT_BRANCHING};

    fn definition() -> Arc<MapDefinition> {
        Arc::new(MapDefinition {
            symbols: CollectionSymbols {
                unit: "SortMap-unit".into(),
                element: "SortMap-element".into(),
                concat: "SortMap-concat".into(),
            },
            key_sort: Sort::simple("SortKey"),
            value_sort: Sort::simple("SortValue"),
            map_sort: "SortMap".into(),
        })
    }

    fn key(index: usize) -> Term {
        Term::domain_value(Sort::simple("SortKey"), format!("{index:06}").as_str())
    }

    fn value(index: usize) -> Term {
        Term::domain_value(Sort::simple("SortValue"), index.to_string().as_str())
    }

    fn variable(name: &str, sort: &str) -> Term {
        Term::variable(Variable::new(name, Sort::simple(sort)))
    }

    fn entries(map: &Term) -> &Items<(Term, Term)> {
        let TermKind::Map { entries, .. } = map.kind() else {
            panic!("a map term")
        };
        entries
    }

    /// A map built on a map rest of its definition, whose tree takes the new entries in, is the
    /// map of all the entries built at once: equal, equally ordered, with equal attributes, and
    /// with one hash although the two trees have different shapes. Entries with variables
    /// included, so the root's variables come from the summary's multiset too.
    #[test]
    fn a_map_built_on_a_map_rest_is_the_map_of_all_its_entries() {
        const ENTRIES: usize = 3000;
        let all: Vec<(Term, Term)> = (0..ENTRIES)
            .map(|index| {
                let value = if index % 7 == 0 {
                    variable(&format!("V{index}"), "SortValue")
                } else {
                    value(index)
                };
                (key(index), value)
            })
            .collect();
        let at_once = Term::map(definition(), all.clone(), None);
        for added in [
            vec![0],
            vec![ENTRIES / 2],
            vec![ENTRIES - 1],
            vec![3, 500, 2999],
        ] {
            let (new, old): (Vec<_>, Vec<_>) = all
                .iter()
                .cloned()
                .enumerate()
                .partition(|(index, _)| added.contains(index));
            let rest = Term::map(
                definition(),
                old.into_iter().map(|(_, entry)| entry).collect(),
                None,
            );
            let map = Term::map(
                definition(),
                new.into_iter().map(|(_, entry)| entry).collect(),
                Some(rest.clone()),
            );
            assert_eq!(map, at_once, "{added:?}");
            assert_eq!(map.cmp(&at_once), std::cmp::Ordering::Equal, "{added:?}");
            assert_eq!(map.attributes(), at_once.attributes(), "{added:?}");
            assert_eq!(entries(&map).to_vec(), all, "{added:?}");
            assert_eq!(entries(&rest).len(), ENTRIES - added.len(), "{added:?}");
        }
    }

    /// Adding one entry to an `n`-entry map computes the own summary of the entries of one leaf,
    /// the one the entry lands in (at most `B` entries before it, `B + 1` after, whether or not
    /// it is then cut in two), and of the new entry when its own sequence is built: not one per
    /// entry of the map, which a copy of the entries would compute.
    #[test]
    fn adding_one_entry_to_a_map_summarizes_one_leaf_of_its_rest() {
        const ENTRIES: usize = 4096;
        let map = Term::map(
            definition(),
            (0..ENTRIES)
                .map(|index| (key(2 * index), value(index)))
                .collect(),
            None,
        );
        for place in [0, 1, ENTRIES, 2 * ENTRIES + 1] {
            ENTRY_SUMMARIES.with(|count| count.set(0));
            let added = Term::map(
                definition(),
                vec![(key(place), value(0))],
                Some(map.clone()),
            );
            let summaries = ENTRY_SUMMARIES.with(std::cell::Cell::get);
            assert!(
                summaries <= DEFAULT_BRANCHING + 2,
                "key {place}: {summaries} entry summaries"
            );
            assert_eq!(entries(&added).len(), ENTRIES + 1, "key {place}");
            assert_eq!(entries(&map).len(), ENTRIES, "key {place}");
        }
    }

    /// The summary of a map's entries counts the keys that are not constructor-like and records a
    /// repeated key, which makes the map `\bottom` and is then found among its entries.
    #[test]
    fn the_entries_summary_counts_symbolic_keys_and_records_a_repeat() {
        let symbolic =
            (0..5).map(|index| (variable(&format!("K{index}"), "SortKey"), value(index)));
        let ground = (0..100).map(|index| (key(index), value(index)));
        let map = Term::map(definition(), symbolic.chain(ground).collect(), None);
        let summary = entries(&map).summary();
        assert_eq!(summary.extra.symbolic_keys(), 5);
        assert!(!summary.collision);
        assert_eq!(map.repeated_map_key(), None);
        assert!(!summary.extra.keys_share_one_header());

        let repeated = Term::map(definition(), vec![(key(50), value(1))], Some(map));
        assert!(entries(&repeated).summary().collision);
        assert_eq!(repeated.repeated_map_key(), Some(&key(50)));
        assert!(!repeated.attributes().evaluated);
        assert!(!repeated.attributes().ceil_free());

        // Ground keys of one header: the repeat alone keeps the map from being `ceil_free`.
        let ground = Term::map(
            definition(),
            (0..100).map(|index| (key(index), value(index))).collect(),
            None,
        );
        assert!(ground.attributes().ceil_free());
        let repeated = Term::map(definition(), vec![(key(50), value(1))], Some(ground));
        assert!(entries(&repeated).summary().collision);
        assert_eq!(repeated.repeated_map_key(), Some(&key(50)));
        assert!(!repeated.attributes().ceil_free());
        assert!(!repeated.attributes().constructor_like);
    }

    /// Substituting into a map rebuilds only the entries that mention a bound variable: a value
    /// is replaced in place, an entry whose key changes is moved to its place, and the result is
    /// the map built from the substituted entries. The substitution summarizes at most the
    /// entries of the leaves its three edits rebuild (the two rebuilt leaves, then the removal and
    /// the insertion of the moved entry, each at most a leaf and a neighbour), whatever the
    /// map's size.
    #[test]
    fn substitution_rebuilds_only_the_entries_that_mention_a_bound_variable() {
        const ENTRIES: usize = 4096;
        let mut bindings = (0..ENTRIES)
            .map(|index| (key(2 * index), value(index)))
            .collect::<Vec<_>>();
        bindings.push((variable("K", "SortKey"), value(1)));
        bindings.push((key(7), variable("V", "SortValue")));
        let map = Term::map(definition(), bindings.clone(), None);
        let substitution = std::collections::BTreeMap::from([
            (Variable::new("K", Sort::simple("SortKey")), key(4097)),
            (Variable::new("V", Sort::simple("SortValue")), value(5)),
        ]);
        let substitute = |term: &Term| crate::substitution::substitute(term, &substitution);
        let mut substituted = None;
        let summaries = entry_summaries_during(|| substituted = Some(substitute(&map)));
        let expected = Term::map(
            definition(),
            bindings
                .iter()
                .map(|(key, value)| (substitute(key), substitute(value)))
                .collect(),
            None,
        );
        let substituted = substituted.expect("substituted");
        assert_eq!(substituted, expected);
        assert_eq!(entries(&substituted).to_vec(), entries(&expected).to_vec());
        assert!(
            summaries <= 3 * 2 * DEFAULT_BRANCHING,
            "{summaries} entry summaries"
        );
    }

    /// Two versions of a map that share all but the path to one entry are compared on the
    /// comparison work lists through the items of that path only: a map whose value was changed
    /// and changed back is equal to the original, and the changed one is ordered by the value.
    #[test]
    fn the_comparison_work_lists_read_only_where_two_versions_of_a_map_differ() {
        const ENTRIES: usize = 4096;
        let map = Term::map(
            definition(),
            (0..ENTRIES)
                .map(|index| (key(2 * index), value(index)))
                .collect(),
            None,
        );
        let with_value = |map: &Term, value: Term| {
            let entries = entries(map);
            let index = entries.search(&key(2000)).expect("a bound key");
            Term::map_of_items(
                definition(),
                entries.replace_at(index, (key(2000), value)),
                None,
            )
        };
        let changed = with_value(&map, value(ENTRIES));
        let changed_back = with_value(&changed, value(1000));
        assert!(!Arc::ptr_eq(&map.0, &changed_back.0));
        let pairs_during = |run: &dyn Fn()| {
            ALIGNED_PAIRS.with(|count| count.set(0));
            run();
            ALIGNED_PAIRS.with(std::cell::Cell::get)
        };
        let equal = pairs_during(&|| {
            assert!(crate::term::equal_terms_on_work_list(&map, &changed_back));
        });
        let ordered = pairs_during(&|| {
            assert_eq!(
                crate::term::order_terms_on_work_list(&map, &changed),
                entries(&map).to_vec().cmp(&entries(&changed).to_vec())
            );
        });
        for (comparison, pairs) in [("equality", equal), ("order", ordered)] {
            assert!(
                pairs <= 2 * DEFAULT_BRANCHING,
                "{comparison}: {pairs} pairs of entries compared"
            );
        }
    }

    /// One version of `base` per edit list: each edit sets the value of the entry at a position
    /// (`Some`) or removes it (`None`).
    fn edited(base: &Term, edits: &[(usize, Option<usize>)]) -> Term {
        let mut items = entries(base).clone();
        for &(place, value_index) in edits {
            if items.is_empty() {
                break;
            }
            let index = place % items.len();
            items = match value_index {
                Some(new) => {
                    let key = items.get(index).expect("an entry").0.clone();
                    items.replace_at(index, (key, value(new)))
                }
                None => items.remove_at(index).0,
            };
        }
        Term::map_of_items(definition(), items, None)
    }

    proptest::proptest! {
        /// The comparison work lists, which skip the tree nodes two maps share, agree with the
        /// comparison of the entry sequences on versions of one map that share most of their
        /// nodes.
        #[test]
        fn the_comparison_work_lists_agree_on_versions_of_one_map(
            size in 0usize..400,
            left in proptest::collection::vec((proptest::prelude::any::<usize>(), proptest::option::of(0usize..3)), 0..4),
            right in proptest::collection::vec((proptest::prelude::any::<usize>(), proptest::option::of(0usize..3)), 0..4),
        ) {
            let base = Term::map(
                definition(),
                (0..size).map(|index| (key(index), value(index % 3))).collect(),
                None,
            );
            let (left, right) = (edited(&base, &left), edited(&base, &right));
            let (left_entries, right_entries) = (entries(&left).to_vec(), entries(&right).to_vec());
            proptest::prop_assert_eq!(
                crate::term::equal_terms_on_work_list(&left, &right),
                left_entries == right_entries
            );
            proptest::prop_assert_eq!(
                crate::term::order_terms_on_work_list(&left, &right),
                left_entries.cmp(&right_entries)
            );
        }
    }

    /// A map's variables are the support of its entries' variable multiset, sharing its tree,
    /// and a term whose only symbolic child is the map shares the map's set: building it copies
    /// none of the map's variables. A term with another symbolic child holds the union. A small
    /// set is shared the same way: a term around one variable holds that variable's set.
    #[test]
    fn a_term_around_a_symbolic_map_shares_its_variable_set() {
        let map = Term::map(
            definition(),
            (0..1000)
                .map(|index| (key(index), variable(&format!("V{index}"), "SortValue")))
                .collect(),
            None,
        );
        let variables = &map.attributes().variables;
        assert_eq!(variables.len(), 1000);
        assert!(
            variables.shares_handle(&crate::term::Variables::of_multiset(
                &entries(&map).summary().group
            ))
        );
        let ground = Term::and(map.clone(), value(0));
        assert!(ground.attributes().variables.shares_handle(variables));
        let x = variable("X", "SortValue");
        let symbolic = Term::and(map.clone(), x.clone());
        let union = &symbolic.attributes().variables;
        assert_eq!(union.len(), 1001);
        assert_eq!(
            union.to_btree_set(),
            variables
                .iter()
                .chain(x.attributes().variables.iter())
                .cloned()
                .collect()
        );
        let around = Term::and(value(0), x.clone());
        assert!(
            around
                .attributes()
                .variables
                .shares_handle(&x.attributes().variables)
        );
    }
}

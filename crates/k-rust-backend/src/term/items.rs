//! The items of a map, list or set term, behind the interface of their tree.
//!
//! [`Items`] is the type of the item fields of [`TermKind::Map`](super::TermKind::Map),
//! [`TermKind::List`](super::TermKind::List) and [`TermKind::Set`](super::TermKind::Set): a
//! map's entries, a list's heads and tails, a set's elements. Its methods are those of the
//! persistent tree `Chunked` (design K22, revision 2, §11): length, iteration from either end,
//! access by position, ordered search, and edits that return a new sequence and leave the old one
//! as it is. Code that reads or builds a collection does so through these methods only.
//!
//! # The tree
//!
//! Every sequence is a `Chunked` tree. An edit copies the path to the items it changes and
//! shares the rest with the sequence it was made from, and the summary of the root
//! (`Items::summary`) gives what the attributes of the collection term need without reading the
//! items (`ItemSummary`, and the multiset of the variables they mention).
//!
//! A map's entries and a set's elements are ordered by the items' `Ord` (the ordered methods:
//! [`search`](Items::search), [`insert`](Items::insert), [`union`](Items::union),
//! `rebuild_where`); a list's items are ordered by position only, and
//! are edited by position ([`split_at`](Items::split_at), [`join`](Items::join),
//! `map_where`). The tree is the same for both: its count summary locates a
//! position, and its first and last items an ordered key. A list's summary also holds the
//! fields only an ordered collection reads (the key header, the symbolic-key count, the
//! repeated-key flag); nothing reads them of a list.
//!
//! Equality and order are those of the item sequence, as for a vector. The hash is the tree's
//! sequence hash: a polynomial hash of the sequence that does not depend on the tree's shape, so
//! equal sequences built by different edits hash alike, and computing it costs a node's summary
//! rather than a pass over the items.
//!
//! What every value holds, whichever edit built it:
//!
//! ```toml algorithm-representation
//! id = "representation.backend.items"
//! name = "the items of a collection term in a persistent tree with a root summary"
//! type = "k_rust_backend::term::Items"
//! sites = ["Items", "Items::from_vec", "Items::summary", "Items::insert", "Items::remove", "Items::union", "Items::rebuild_where", "Items::map_where", "Items::insert_at", "Items::remove_at", "Items::replace_at", "Items::split_at", "Items::join"]
//! invariant = """\
//! An Items is a Chunked tree under its fill invariant, and every node's summary is the fold of \
//! its items' summaries: the count, the first and last item, the repeated-key flag, the sequence \
//! hash, the ItemSummary (the counts of items failing each attribute flag, the key header, the \
//! symbolic-key count, the macro flag and the saturated k-cell count) and the multiset of the \
//! variables the items mention, so the root summary is that of the whole sequence and the \
//! attributes of a collection term read it in place of its items. The ordered edits (insert, \
//! remove, union, rebuild_where) keep the items in nondecreasing item order with repeated items \
//! and keys adjacent, which is the order of a map's entries and of a set's elements; the \
//! positional edits keep the given order of a list's items. Equality, order and hash are those of \
//! the item sequence, whatever the tree's shape."""
//! tests = ["crates/k-rust-backend/src/term/items.rs", "crates/k-rust-backend/src/term/chunked/tests.rs"]
//! ```
//!
//! # Crate-private bound
//!
//! The item types are bounded by the crate's own `Item`, which names the tree's summary types
//! and is not part of the public interface. A dependent crate uses `Items<Term>` and
//! `Items<(Term, Term)>`, whose bounds hold, and never names the trait, so the `private_bounds`
//! lint, which warns that such a crate cannot write the bound itself, is allowed here.
#![allow(private_bounds)]

use std::{
    borrow::Cow,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    iter::FusedIterator,
    ops::RangeBounds,
    vec,
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

/// A sequence of collection items (see the [module documentation](self)).
///
/// The items of a map or a set are in nondecreasing order (map entries by key, then value); the
/// methods called ordered rely on it, and a constructor that does not establish it is the
/// caller's responsibility, as for [`Term::map`] and [`Term::set`], which order what they are
/// given. A list's items are in the list's order.
pub struct Items<T: Item>(Chunked<T>);

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

impl<T: Item> Items<T> {
    /// The empty sequence.
    pub const fn new() -> Self {
        Self(Chunked::new())
    }

    /// The sequence of `items`, in the order given, built bottom-up in time linear in the number
    /// of items.
    pub fn from_vec(items: Vec<T>) -> Self {
        Self(Chunked::from_vec(items))
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The items in order; the iterator also runs from the back.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter(self.0.iter())
    }

    /// The items at the positions of `range`, which lies within the sequence, in order.
    pub fn range(&self, range: impl RangeBounds<usize>) -> Iter<'_, T> {
        Iter(self.0.range(range))
    }

    /// The item at position `index`, if the sequence is that long.
    pub fn get(&self, index: usize) -> Option<&T> {
        self.0.get(index)
    }

    pub fn first(&self) -> Option<&T> {
        self.0.summary().and_then(|summary| summary.first.as_ref())
    }

    pub fn last(&self) -> Option<&T> {
        self.0.summary().and_then(|summary| summary.last.as_ref())
    }

    /// In a sequence ordered as `compare` orders its items against a probe (`Less` for those
    /// before it, `Greater` for those after it), `Ok` with the position of an item `compare`
    /// finds equal to the probe, or `Err` with the position at which the probe would go.
    pub fn search_by(&self, compare: impl FnMut(&T) -> Ordering) -> Result<usize, usize> {
        self.0.search_by(compare)
    }

    /// The number of leading items for which `before` holds, when it holds for a prefix of the
    /// sequence and for no item after it.
    pub fn partition_point(&self, before: impl FnMut(&T) -> bool) -> usize {
        self.0.partition_point(before)
    }

    pub fn to_vec(&self) -> Vec<T> {
        self.0.to_vec()
    }

    /// The first `index` items and the rest; `index` is at most the length.
    pub fn split_at(&self, index: usize) -> (Self, Self) {
        let (left, right) = self.0.split_at(index);
        (Self(left), Self(right))
    }

    /// The items of this sequence followed by those of `other`.
    pub fn join(&self, other: &Self) -> Self {
        Self(self.0.join(&other.0))
    }

    /// The sequence with `item` inserted at position `index`, which is at most the length.
    pub fn insert_at(&self, index: usize, item: T) -> Self {
        Self(self.0.insert_at(index, item))
    }

    /// The sequence without the item at position `index`, which is below the length, and that
    /// item.
    pub fn remove_at(&self, index: usize) -> (Self, T) {
        let (tree, item) = self.0.remove_at(index);
        (Self(tree), item)
    }

    /// The sequence with the item at position `index`, which is below the length, replaced by
    /// `item`.
    pub fn replace_at(&self, index: usize, item: T) -> Self {
        Self(self.0.replace_at(index, item))
    }

    /// The sequence with each item `wants` picks replaced, where it stands, by `change`'s
    /// result when it returns one (`None` keeps the item): a list's rebuild. The tree is entered
    /// only where `admits` holds of a subtree's summary, which it must wherever an item `wants`
    /// picks is below, and only the paths to the replaced items are copied
    /// (`Chunked::map_where`), so the work is that of the items reached.
    pub(crate) fn map_where(
        &self,
        admits: impl Fn(&NodeSummary<T>) -> bool,
        wants: impl Fn(&T) -> bool,
        change: impl FnMut(&T) -> Option<T>,
    ) -> Self {
        Self(
            self.0
                .map_where(&chunked::seek::Where::new(admits, wants), change),
        )
    }

    /// The pairs of items the two sequences hold at the same positions, in order, up to the end
    /// of the shorter one. The walk skips the nodes the trees hold at the same position, whose
    /// items are the same (`Chunked::aligned`), so comparing two versions of a collection reads
    /// the paths where they differ.
    pub(crate) fn aligned<'a>(&'a self, other: &'a Self) -> Aligned<'a, T> {
        Aligned(self.0.aligned(&other.0))
    }

    /// The most item comparisons [`search_by`](Self::search_by) makes: one binary search on each
    /// node of a path from the root, over at most `B` children or items, and a binary search
    /// makes at most `⌈log2 w⌉ + 1` comparisons over `w` items.
    #[cfg(test)]
    pub(crate) fn search_comparison_bound(&self) -> usize {
        let binary = |width: usize| width.next_power_of_two().ilog2() as usize + 1;
        self.0.levels() * binary(chunked::DEFAULT_BRANCHING)
    }

    /// The most item comparisons one insertion or removal at a position makes: those of the
    /// summaries of the nodes it builds on one path, each of which compares the keys of its
    /// adjacent items or children (`collision`); a node built from a node and its sibling, when
    /// one would fall below the fill minimum, holds fewer than `2B` of them.
    #[cfg(test)]
    pub(crate) fn path_copy_comparison_bound(&self) -> usize {
        self.0.levels() * 2 * chunked::DEFAULT_BRANCHING
    }

    /// Whether the two sequences hold the same root node.
    #[cfg(test)]
    pub(crate) fn shares_root(&self, other: &Self) -> bool {
        self.0.shares_root(&other.0)
    }

    /// The summary of the whole sequence: the root's, or the identity for the empty sequence.
    pub(crate) fn summary(&self) -> Cow<'_, NodeSummary<T>> {
        self.0
            .summary()
            .map_or_else(|| Cow::Owned(NodeSummary::identity()), Cow::Borrowed)
    }

    /// Whether dropping this sequence may free an item: the root of its tree is not shared with
    /// another sequence. An item a shared root holds is held by that other sequence too.
    pub(crate) fn may_free_items(&self) -> bool {
        self.0.owns_root()
    }

    /// Debug builds: hand the items a check has not passed to `items`, and the pairs of
    /// adjacent items among them or next to them to `adjacent`. The leaves and junctions not
    /// marked checked are handed over and their nodes returned, which the caller marks once the
    /// items have passed (`Chunked::check_unchecked`), so a sequence edited since its last check
    /// hands over the paths the edits copied.
    #[cfg(debug_assertions)]
    pub(crate) fn check_unchecked<'t>(
        &'t self,
        items: impl FnMut(&'t [T]),
        adjacent: impl FnMut(&'t T, &'t T),
    ) -> chunked::Unchecked<'t, T> {
        self.0.check_unchecked(items, adjacent)
    }

    /// Hand each item of which this sequence held the last handle to `each`, in no particular
    /// order, through a work list: a tree node shared with another sequence is only released.
    pub(crate) fn dismantle(self, each: impl FnMut(T)) {
        let mut work = chunked::Dismantle::new();
        work.push(self.0);
        work.for_each(each);
    }
}

impl<T: Item + Keyed> Items<T> {
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

impl<T: Item<Summary = ItemSummary> + Keyed<Key = Term>> Items<T> {
    /// The number of items whose key is not constructor-like: the root summary's count.
    pub(crate) fn symbolic_keys(&self) -> usize {
        self.0
            .summary()
            .map_or(0, |summary| summary.extra.symbolic_keys())
    }

    /// The items whose key is not constructor-like, in order. The tree is descended only into
    /// the subtrees whose summary counts such a key, so the `s` items are reached through their
    /// ancestors, `O(s log n)` nodes.
    pub(crate) fn symbolic_keyed(&self) -> impl Iterator<Item = &T> {
        self.symbolic_keyed_at().map(|(_, item)| item)
    }

    /// [`symbolic_keyed`](Self::symbolic_keyed), each item with its position.
    pub(crate) fn symbolic_keyed_at(&self) -> impl Iterator<Item = (usize, &T)> {
        // No descent when the root's summary counts none.
        (self.symbolic_keys() > 0)
            .then(|| {
                self.0.seek(chunked::seek::Where::new(
                    |summary: &NodeSummary<T>| summary.extra.symbolic_keys() > 0,
                    |item: &T| !Keyed::key(item).attributes().constructor_like,
                ))
            })
            .into_iter()
            .flatten()
    }
}

impl<T: Item<Summary = ItemSummary> + ItemTerms> Items<T> {
    /// The items one of whose terms lacks `flag`, in order. The tree is descended only into the
    /// subtrees whose summary counts such an item, so the `f` items are reached through their
    /// ancestors, `O(f log n)` nodes; a sequence whose every item has the flag costs one look
    /// at its root.
    pub(crate) fn lacking(&self, flag: Flag) -> impl Iterator<Item = &T> {
        self.0
            .summary()
            .is_some_and(|summary| !summary.extra.holds(flag))
            .then(|| {
                self.0.seek(chunked::seek::Where::new(
                    move |summary: &NodeSummary<T>| !summary.extra.holds(flag),
                    move |item: &T| !item.every_term(|term| flag.holds_of(term)),
                ))
            })
            .into_iter()
            .flatten()
            .map(|(_, item)| item)
    }
}

impl<T: Item<Summary = ItemSummary> + ItemTerms> Items<T> {
    /// The first item one of whose terms holds a `<k>` cell (a nonzero `k_cells`), reached
    /// through the subtrees whose summary counts one: `O(log n)` nodes.
    pub(crate) fn first_with_k_cells(&self) -> Option<&T> {
        self.0
            .summary()
            .is_some_and(|summary| summary.extra.k_cells() > 0)
            .then(|| {
                self.0.seek(chunked::seek::Where::new(
                    |summary: &NodeSummary<T>| summary.extra.k_cells() > 0,
                    |item: &T| !item.every_term(|term| term.attributes().k_cells() == 0),
                ))
            })
            .into_iter()
            .flatten()
            .map(|(_, item)| item)
            .next()
    }
}

/// The terms of an item whose attributes its [`ItemSummary`] combines: an element itself, a map
/// entry's key and value.
pub(crate) trait ItemTerms {
    /// Whether `test` holds of each of the item's terms.
    fn every_term(&self, test: impl Fn(&Term) -> bool) -> bool;
}

impl ItemTerms for Term {
    fn every_term(&self, test: impl Fn(&Term) -> bool) -> bool {
        test(self)
    }
}

impl ItemTerms for (Term, Term) {
    fn every_term(&self, test: impl Fn(&Term) -> bool) -> bool {
        test(&self.0) && test(&self.1)
    }
}

impl<T: Item + Ord> Items<T> {
    /// In an ordered sequence, the sequence with each item `wants` picks replaced by `change`'s
    /// result, when it returns one, and in order again. The tree is entered only where `admits`
    /// holds of a subtree's summary, which it must wherever an item `wants` picks is below; it
    /// copies the paths to the changed items and moves those that are no longer in order
    /// (`Chunked::rebuild_where`), so the work is that of the items reached.
    pub(crate) fn rebuild_where(
        &self,
        admits: impl Fn(&NodeSummary<T>) -> bool,
        wants: impl Fn(&T) -> bool,
        change: impl FnMut(&T) -> Option<T>,
    ) -> Self {
        Self(
            self.0
                .rebuild_where(&chunked::seek::Where::new(admits, wants), change),
        )
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
    /// the two hold it together. The nodes of the taller tree whose range receives none of the
    /// other's items are shared (`Chunked::union`).
    pub fn union(&self, other: &Self) -> Self {
        Self(self.0.union(&other.0))
    }
}

impl<T: Item> Clone for Items<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

/// Equal when the item sequences are, whatever the trees' shapes.
impl<T: Item> PartialEq for Items<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: Item> Eq for Items<T> {}

/// The lexicographic order of the item sequences, as for a vector.
impl<T: Item + Ord> Ord for Items<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T: Item + Ord> PartialOrd for Items<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// The tree's sequence hash, which equal sequences share whatever the tree's shape (see the
/// [module documentation](self)).
impl<T: Item> Hash for Items<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T: Item> Default for Items<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// The items' own debug form, as a vector of them prints it.
impl<T: Item> fmt::Debug for Items<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_list().entries(self.iter()).finish()
    }
}

impl<T: Item> From<Vec<T>> for Items<T> {
    fn from(items: Vec<T>) -> Self {
        Self::from_vec(items)
    }
}

/// The items in order, as a vector.
impl<T: Item> From<Items<T>> for Vec<T> {
    fn from(items: Items<T>) -> Self {
        items.to_vec()
    }
}

impl<T: Item> FromIterator<T> for Items<T> {
    fn from_iter<I: IntoIterator<Item = T>>(items: I) -> Self {
        Self::from_vec(items.into_iter().collect())
    }
}

impl<'a, T: Item> IntoIterator for &'a Items<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

/// The items in order, copied out of the sequence.
impl<T: Item> IntoIterator for Items<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter(Vec::from(self).into_iter())
    }
}

/// The items of an [`Items`] in order, from either end.
pub struct Iter<'a, T: Item>(chunked::Iter<'a, T>);

impl<T: Item> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: Item> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Iter")
            .field("remaining", &self.len())
            .finish_non_exhaustive()
    }
}

impl<'a, T: Item> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    fn nth(&mut self, n: usize) -> Option<&'a T> {
        self.0.nth(n)
    }
}

impl<T: Item> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth_back(n)
    }
}

impl<T: Item> ExactSizeIterator for Iter<'_, T> {}

impl<T: Item> FusedIterator for Iter<'_, T> {}

/// The pairs of items two sequences hold at the same positions ([`Items::aligned`]).
pub(crate) struct Aligned<'a, T: Item>(chunked::Aligned<'a, T>);

impl<'a, T: Item> Iterator for Aligned<'a, T> {
    type Item = (&'a T, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        let pair = self.0.next();
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
        terms.iter().all(|term| self.holds_of(term))
    }

    /// Whether `term`'s stored attributes have this flag.
    pub(crate) fn holds_of(self, term: &Term) -> bool {
        let attributes = term.attributes();
        match self {
            Self::Evaluated => attributes.evaluated,
            Self::ValueClaimed => attributes.value_claimed,
            Self::ConstructorLike => attributes.constructor_like,
            Self::ConcreteAfterNormalization => attributes.concrete_after_normalization,
            Self::CanBeEvaluated => attributes.can_be_evaluated,
            Self::CeilFree => attributes.ceil_free,
        }
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
        #[cfg(test)]
        ELEMENT_SUMMARIES.with(|count| count.set(count.get() + 1));
        ItemSummary::of(self, &[self])
    }

    fn group(&self) -> Multiset<Variable> {
        if self.attributes().variables.is_empty() {
            return Multiset::new();
        }
        mentioned(&[self])
    }
}

#[cfg(test)]
thread_local! {
    /// Test builds: the set or list elements whose own summary this thread has computed, which a
    /// node does for each element it holds when it is built from its elements.
    static ELEMENT_SUMMARIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Test builds: the number of set or list elements whose own summary `run` computes on this
/// thread.
#[cfg(test)]
pub(crate) fn element_summaries_during(run: impl FnOnce()) -> usize {
    let before = ELEMENT_SUMMARIES.with(std::cell::Cell::get);
    run();
    ELEMENT_SUMMARIES.with(std::cell::Cell::get) - before
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

    /// The tests of a set's elements, which a tree holds as it holds a map's entries.
    mod sets {
        use super::*;
        use crate::term::{ListDefinition, SetDefinition};

        fn set_definition() -> Arc<SetDefinition> {
            Arc::new(ListDefinition {
                symbols: CollectionSymbols {
                    unit: "SortSet-unit".into(),
                    element: "SortSet-element".into(),
                    concat: "SortSet-concat".into(),
                },
                element_sort: Sort::simple("SortKey"),
                list_sort: "SortSet".into(),
            })
        }

        fn set(elements: Vec<Term>, rest: Option<Term>) -> Term {
            Term::set(set_definition(), elements, rest)
        }

        fn elements(set: &Term) -> &Items<Term> {
            let TermKind::Set { elements, .. } = set.kind() else {
                panic!("a set term")
            };
            elements
        }

        /// A set built on a set rest of its definition, whose tree takes the new elements in, is
        /// the set of all the elements built at once: equal, equally ordered, with equal
        /// attributes (the hash and the variables included) although the two trees have
        /// different shapes.
        #[test]
        fn a_set_built_on_a_set_rest_is_the_set_of_all_its_elements() {
            const ELEMENTS: usize = 3000;
            let all: Vec<Term> = (0..ELEMENTS)
                .map(|index| {
                    if index % 7 == 0 {
                        variable(&format!("E{index:06}"), "SortKey")
                    } else {
                        key(index)
                    }
                })
                .collect();
            let at_once = set(all.clone(), None);
            let mut ordered = all.clone();
            ordered.sort();
            for added in [
                vec![0],
                vec![ELEMENTS / 2],
                vec![ELEMENTS - 1],
                vec![3, 500, 2999],
            ] {
                let (new, old): (Vec<_>, Vec<_>) = all
                    .iter()
                    .cloned()
                    .enumerate()
                    .partition(|(index, _)| added.contains(index));
                let rest = set(old.into_iter().map(|(_, element)| element).collect(), None);
                let built = set(
                    new.into_iter().map(|(_, element)| element).collect(),
                    Some(rest.clone()),
                );
                assert_eq!(built, at_once, "{added:?}");
                assert_eq!(built.cmp(&at_once), std::cmp::Ordering::Equal, "{added:?}");
                assert_eq!(built.attributes(), at_once.attributes(), "{added:?}");
                assert_eq!(elements(&built).to_vec(), ordered, "{added:?}");
                assert_eq!(elements(&rest).len(), ELEMENTS - added.len(), "{added:?}");
            }
        }

        /// Adding one element to an `n`-element set computes the own summary of the elements of
        /// one leaf, the one the element lands in, and of the new element: not one per element
        /// of the set, which a copy of the elements would compute.
        #[test]
        fn adding_one_element_to_a_set_summarizes_one_leaf_of_its_rest() {
            const ELEMENTS: usize = 4096;
            let base = set((0..ELEMENTS).map(|index| key(2 * index)).collect(), None);
            for place in [0, 1, ELEMENTS, 2 * ELEMENTS + 1] {
                let mut added = None;
                let summaries = element_summaries_during(|| {
                    added = Some(set(vec![key(place)], Some(base.clone())));
                });
                assert!(
                    summaries <= DEFAULT_BRANCHING + 2,
                    "element {place}: {summaries} element summaries"
                );
                assert_eq!(elements(&added.expect("added")).len(), ELEMENTS + 1);
                assert_eq!(elements(&base).len(), ELEMENTS);
            }
        }

        /// The summary of a set's elements counts the elements that are not constructor-like and
        /// records a repeated element, which makes the set `\bottom` and is then found among its
        /// elements; the repeat alone keeps a set of ground elements of one header from being
        /// `ceil_free`.
        #[test]
        fn the_elements_summary_counts_symbolic_elements_and_records_a_repeat() {
            let symbolic = (0..5).map(|index| variable(&format!("E{index}"), "SortKey"));
            let base = set(symbolic.chain((0..100).map(key)).collect(), None);
            let summary = elements(&base).summary();
            assert_eq!(summary.extra.symbolic_keys(), 5);
            assert!(!summary.collision);
            assert_eq!(base.repeated_set_element(), None);
            assert!(!summary.extra.keys_share_one_header());

            let repeated = set(vec![key(50)], Some(base));
            assert!(elements(&repeated).summary().collision);
            assert_eq!(repeated.repeated_set_element(), Some(&key(50)));
            assert!(!repeated.attributes().evaluated);
            assert!(!repeated.attributes().ceil_free());

            let ground = set((0..100).map(key).collect(), None);
            assert!(ground.attributes().ceil_free());
            assert!(ground.attributes().constructor_like);
            let repeated = set(vec![key(50)], Some(ground));
            assert!(elements(&repeated).summary().collision);
            assert_eq!(repeated.repeated_set_element(), Some(&key(50)));
            assert!(!repeated.attributes().ceil_free());
            assert!(!repeated.attributes().constructor_like);
        }

        /// Substituting into a set rebuilds only the elements that mention a bound variable: an
        /// element that changes is moved to its place, and the result is the set built from the
        /// substituted elements. The substitution summarizes at most the elements of the leaves
        /// its edits rebuild, whatever the set's size.
        #[test]
        fn substitution_rebuilds_only_the_elements_that_mention_a_bound_variable() {
            const ELEMENTS: usize = 4096;
            let mut all = (0..ELEMENTS)
                .map(|index| key(2 * index))
                .collect::<Vec<_>>();
            all.push(variable("E", "SortKey"));
            let base = set(all.clone(), None);
            let substitution = std::collections::BTreeMap::from([(
                Variable::new("E", Sort::simple("SortKey")),
                key(4097),
            )]);
            let substitute = |term: &Term| crate::substitution::substitute(term, &substitution);
            let mut substituted = None;
            let summaries = element_summaries_during(|| substituted = Some(substitute(&base)));
            let expected = set(all.iter().map(substitute).collect(), None);
            let substituted = substituted.expect("substituted");
            assert_eq!(substituted, expected);
            assert_eq!(
                elements(&substituted).to_vec(),
                elements(&expected).to_vec()
            );
            assert!(
                summaries <= 3 * 2 * DEFAULT_BRANCHING,
                "{summaries} element summaries"
            );
        }

        /// The variables of a set of at most `B` elements are united from its elements' own sets
        /// as any node's children's are, so a set around one symbolic element holds that
        /// element's set; a larger set's are read from its summary's multiset.
        #[test]
        fn a_small_set_shares_the_variable_set_of_its_one_symbolic_element() {
            let x = variable("X", "SortKey");
            let small = set((0..10).map(key).chain([x.clone()]).collect(), None);
            assert!(
                small
                    .attributes()
                    .variables
                    .shares_handle(&x.attributes().variables)
            );
            let symbolic = (0..2 * DEFAULT_BRANCHING)
                .map(|index| variable(&format!("E{index:03}"), "SortKey"))
                .collect::<Vec<_>>();
            let large = set(symbolic.clone(), None);
            assert_eq!(
                large.attributes().variables.to_btree_set(),
                symbolic
                    .iter()
                    .flat_map(|element| element.attributes().variables.iter().cloned())
                    .collect()
            );
        }

        /// Two versions of a set that share all but the path to one element are compared on the
        /// comparison work lists through the elements of that path only.
        #[test]
        fn the_comparison_work_lists_read_only_where_two_versions_of_a_set_differ() {
            const ELEMENTS: usize = 4096;
            let base = set((0..ELEMENTS).map(|index| key(2 * index)).collect(), None);
            let replaced = |set: &Term, old: usize, new: usize| {
                let elements = elements(set);
                let index = elements.search(&key(old)).expect("an element");
                Term::set_of_items(
                    set_definition(),
                    elements.remove_at(index).0.insert(key(new)),
                    None,
                )
            };
            let changed = replaced(&base, 2000, 2001);
            let changed_back = replaced(&changed, 2001, 2000);
            assert!(!Arc::ptr_eq(&base.0, &changed_back.0));
            let pairs_during = |run: &dyn Fn()| {
                ALIGNED_PAIRS.with(|count| count.set(0));
                run();
                ALIGNED_PAIRS.with(std::cell::Cell::get)
            };
            let equal = pairs_during(&|| {
                assert!(crate::term::equal_terms_on_work_list(&base, &changed_back));
            });
            let ordered = pairs_during(&|| {
                assert_eq!(
                    crate::term::order_terms_on_work_list(&base, &changed),
                    elements(&base).to_vec().cmp(&elements(&changed).to_vec())
                );
            });
            for (comparison, pairs) in [("equality", equal), ("order", ordered)] {
                assert!(
                    pairs <= 2 * DEFAULT_BRANCHING,
                    "{comparison}: {pairs} pairs of elements compared"
                );
            }
        }
    }

    mod lists {
        use super::*;
        use crate::term::ListDefinition;

        fn list_definition() -> Arc<ListDefinition> {
            Arc::new(ListDefinition {
                symbols: CollectionSymbols {
                    unit: "SortList-unit".into(),
                    element: "SortList-element".into(),
                    concat: "SortList-concat".into(),
                },
                element_sort: Sort::simple("SortKey"),
                list_sort: "SortList".into(),
            })
        }

        fn list(heads: Vec<Term>, rest: Option<(Term, Vec<Term>)>) -> Term {
            Term::list(list_definition(), heads, rest)
        }

        /// The heads, and the middle and tails, of a list term.
        fn parts(list: &Term) -> (&Items<Term>, Option<&(Term, Items<Term>)>) {
            let TermKind::List { heads, rest, .. } = list.kind() else {
                panic!("a list term")
            };
            (heads, rest.as_ref())
        }

        /// Items `0..n`, every seventh a variable, so that the trees carry variables.
        fn items(range: std::ops::Range<usize>) -> Vec<Term> {
            range
                .map(|index| {
                    if index % 7 == 0 {
                        variable(&format!("E{index:06}"), "SortKey")
                    } else {
                        key(index)
                    }
                })
                .collect()
        }

        /// A list whose middle is a list of its definition, whose trees are joined with the
        /// given ones, is the list of all the items in order built at once: equal, equally
        /// ordered, with equal attributes (the hash and the variables included) although the
        /// trees have different shapes. A nested middle with an opaque middle of its own keeps
        /// that one, its heads joined after the outer heads and its tails before the outer tails.
        #[test]
        fn a_list_built_on_a_list_middle_is_the_list_of_all_its_items() {
            const ITEMS: usize = 3000;
            let all = items(0..ITEMS);
            let at_once = list(all.clone(), None);
            for (start, end) in [(0, ITEMS), (0, 1), (1, ITEMS), (1500, 1501), (40, 2960)] {
                let middle = list(all[start..end].to_vec(), None);
                let built = list(all[..start].to_vec(), Some((middle, all[end..].to_vec())));
                assert_eq!(built, at_once, "{start}..{end}");
                assert_eq!(built.cmp(&at_once), std::cmp::Ordering::Equal);
                assert_eq!(built.attributes(), at_once.attributes(), "{start}..{end}");
                assert_eq!(parts(&built).0.to_vec(), all, "{start}..{end}");
                assert!(parts(&built).1.is_none());
            }
            let opaque = variable("L", "SortList");
            let expected = list(
                all[..1000].to_vec(),
                Some((opaque.clone(), all[1500..].to_vec())),
            );
            let nested = list(
                all[..300].to_vec(),
                Some((
                    list(
                        all[300..1000].to_vec(),
                        Some((opaque, all[1500..2000].to_vec())),
                    ),
                    all[2000..].to_vec(),
                )),
            );
            assert_eq!(nested, expected);
            assert_eq!(nested.attributes(), expected.attributes());
            let (heads, rest) = parts(&nested);
            assert_eq!(heads.len(), 1000);
            assert_eq!(rest.expect("a middle").1.to_vec(), all[1500..].to_vec());
        }

        /// Appending or prepending one item to an `n`-item list joins a one-item tree to its
        /// tree, which computes the own summary of the items of one leaf, the one at the
        /// junction: not one per item, which a copy of the items would compute.
        #[test]
        fn adding_one_item_to_a_list_summarizes_one_leaf() {
            const ITEMS: usize = 4096;
            let base = list(items(0..ITEMS), None);
            let item = key(ITEMS);
            for (heads, tails) in [(vec![], vec![item.clone()]), (vec![item.clone()], vec![])] {
                let mut added = None;
                let summaries = element_summaries_during(|| {
                    added = Some(list(heads.clone(), Some((base.clone(), tails.clone()))));
                });
                assert!(
                    summaries <= DEFAULT_BRANCHING + 2,
                    "{summaries} item summaries"
                );
                let added = added.expect("added");
                assert_eq!(parts(&added).0.len(), ITEMS + 1);
                assert_eq!(parts(&base).0.len(), ITEMS);
            }
        }

        /// Substituting into a list replaces the items that mention a bound variable where they
        /// stand, in its heads and its tails, and the result is the list built from the
        /// substituted items. It summarizes at most the items of the leaf each replacement
        /// rebuilds, whatever the list's length.
        #[test]
        fn substitution_rebuilds_only_the_items_that_mention_a_bound_variable() {
            const ITEMS: usize = 4096;
            let mut heads = (0..ITEMS).map(key).collect::<Vec<_>>();
            heads[2000] = variable("E", "SortKey");
            let mut tails = (0..ITEMS).map(key).collect::<Vec<_>>();
            tails[10] = variable("E", "SortKey");
            let middle = variable("L", "SortList");
            let base = list(heads.clone(), Some((middle.clone(), tails.clone())));
            let substitution = std::collections::BTreeMap::from([(
                Variable::new("E", Sort::simple("SortKey")),
                key(ITEMS),
            )]);
            let substitute = |term: &Term| crate::substitution::substitute(term, &substitution);
            let mut substituted = None;
            let summaries = element_summaries_during(|| substituted = Some(substitute(&base)));
            let expected = list(
                heads.iter().map(substitute).collect(),
                Some((middle, tails.iter().map(substitute).collect())),
            );
            let substituted = substituted.expect("substituted");
            assert_eq!(substituted, expected);
            assert_eq!(substituted.attributes(), expected.attributes());
            assert!(
                summaries <= 2 * DEFAULT_BRANCHING,
                "{summaries} item summaries"
            );
        }

        /// Two versions of a list that share all but the paths to one head and one tail are
        /// compared on the comparison work lists through the items of those paths only.
        #[test]
        fn the_comparison_work_lists_read_only_where_two_versions_of_a_list_differ() {
            const ITEMS: usize = 4096;
            let middle = variable("L", "SortList");
            let base = list(
                (0..ITEMS).map(key).collect(),
                Some((middle.clone(), (0..ITEMS).map(key).collect())),
            );
            let replaced = |list: &Term, head: usize, tail: usize| {
                let (heads, rest) = parts(list);
                let (middle, tails) = rest.expect("a middle");
                Term::list_of_items(
                    list_definition(),
                    heads.replace_at(2000, key(head)),
                    Some((middle.clone(), tails.replace_at(3000, key(tail)))),
                )
            };
            let changed = replaced(&base, 1, 2);
            let changed_back = replaced(&changed, 2000, 3000);
            assert!(!Arc::ptr_eq(&base.0, &changed_back.0));
            let pairs_during = |run: &dyn Fn()| {
                ALIGNED_PAIRS.with(|count| count.set(0));
                run();
                ALIGNED_PAIRS.with(std::cell::Cell::get)
            };
            let equal = pairs_during(&|| {
                assert!(crate::term::equal_terms_on_work_list(&base, &changed_back));
            });
            let ordered = pairs_during(&|| {
                assert_eq!(
                    crate::term::order_terms_on_work_list(&base, &changed),
                    parts(&base).0.to_vec().cmp(&parts(&changed).0.to_vec())
                );
            });
            // Some pairs: the items are walked by the aligned walk, not compared at once.
            for (comparison, pairs) in [("equality", equal), ("order", ordered)] {
                assert!(
                    0 < pairs && pairs <= 2 * DEFAULT_BRANCHING,
                    "{comparison}: {pairs} pairs of items compared"
                );
            }
        }
    }

    /// `children_lacking` gives the children `immediate_children` gives that lack a flag, in the
    /// same order, on a map, a set and a list of 4,096 items whose few non-constructor-like
    /// items (variables) stand at either end, in the middle and nowhere, with and without a
    /// rest; reaching them through the summaries leaves out exactly the items that have it.
    #[test]
    fn the_children_lacking_a_flag_are_those_of_all_children_lacking_it() {
        use crate::term::{ListDefinition, children_lacking, immediate_children};
        const ITEMS: usize = 4096;
        let collection = |sort: &str| {
            Arc::new(ListDefinition {
                symbols: CollectionSymbols {
                    unit: format!("{sort}-unit").into(),
                    element: format!("{sort}-element").into(),
                    concat: format!("{sort}-concat").into(),
                },
                element_sort: Sort::simple("SortKey"),
                list_sort: sort.into(),
            })
        };
        let item = |index: usize, symbolic: &[usize]| {
            if symbolic.contains(&index) {
                variable(&format!("X{index:06}"), "SortKey")
            } else {
                key(index)
            }
        };
        for symbolic in [
            vec![],
            vec![0],
            vec![ITEMS - 1],
            vec![7, ITEMS / 2, ITEMS - 3],
        ] {
            for with_rest in [false, true] {
                let rest = |sort: &str| with_rest.then(|| variable("R", sort));
                let map = Term::map(
                    definition(),
                    (0..ITEMS)
                        .map(|index| (key(index), item(index, &symbolic)))
                        .collect(),
                    rest("SortMap"),
                );
                let set = Term::set(
                    collection("SortSet"),
                    (0..ITEMS).map(|index| item(index, &symbolic)).collect(),
                    rest("SortSet"),
                );
                // Without a middle, the heads are all the items; with one, the first half.
                let heads = if with_rest { ITEMS / 2 } else { ITEMS };
                let list = Term::list(
                    collection("SortList"),
                    (0..heads).map(|index| item(index, &symbolic)).collect(),
                    rest("SortList").map(|middle| {
                        (
                            middle,
                            (ITEMS / 2..ITEMS)
                                .map(|index| item(index, &symbolic))
                                .collect(),
                        )
                    }),
                );
                for term in [map, set, list] {
                    let expected: Vec<&Term> = immediate_children(term.kind())
                        .into_iter()
                        .filter(|child| !child.attributes().constructor_like)
                        .collect();
                    assert_eq!(
                        children_lacking(term.kind(), Flag::ConstructorLike),
                        expected,
                        "{symbolic:?}, rest {with_rest}"
                    );
                    assert_eq!(
                        expected.len(),
                        symbolic.len() + usize::from(with_rest),
                        "{symbolic:?}, rest {with_rest}"
                    );
                }
            }
        }
    }
}

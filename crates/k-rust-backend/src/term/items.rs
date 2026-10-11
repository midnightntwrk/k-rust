//! The items of a map, list or set term, behind the interface their tree will have.
//!
//! [`Items`] is the type of the item fields of [`TermKind::Map`](super::TermKind::Map),
//! [`TermKind::List`](super::TermKind::List) and [`TermKind::Set`](super::TermKind::Set): a
//! map's entries, a list's heads and tails, a set's elements. It holds them in one vector, and
//! its methods are those a persistent tree of the items provides (design K22, revision 2, §11):
//! length, iteration from either end, access by position, ordered search, and edits that return
//! a new sequence and leave the old one as it is. Reading the items through these methods only,
//! and building new sequences through them, lets the representation change without touching the
//! code that reads or builds a collection.
//!
//! The edits copy the vector, so each costs `O(n)` here, where the tree will copy one path.
//!
//! Equality, order and hash are those of the item sequence, as for the vector itself: the
//! derived implementations of the newtype hand the vector to the vector's.

use std::{
    cmp::Ordering,
    fmt,
    iter::FusedIterator,
    ops::{Deref, RangeBounds},
    slice, vec,
};

use super::Term;

/// A sequence of collection items (see the [module documentation](self)).
///
/// The items of a map or a set are in nondecreasing order (map entries by key, then value); the
/// methods called ordered rely on it, and a constructor that does not establish it is the
/// caller's responsibility, as for [`Term::map`] and [`Term::set`], which order what they are
/// given. A list's items are in the list's order.
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Items<T>(Vec<T>);

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

impl<T> Items<T> {
    /// The empty sequence.
    pub const fn new() -> Self {
        Self(Vec::new())
    }

    /// The sequence of `items`, in the order given.
    pub fn from_vec(items: Vec<T>) -> Self {
        Self(items)
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
        let range = (range.start_bound().cloned(), range.end_bound().cloned());
        Iter(self.0[range].iter())
    }

    /// The item at position `index`, if the sequence is that long.
    pub fn get(&self, index: usize) -> Option<&T> {
        self.0.get(index)
    }

    pub fn first(&self) -> Option<&T> {
        self.0.first()
    }

    pub fn last(&self) -> Option<&T> {
        self.0.last()
    }

    /// In a sequence ordered as `compare` orders its items against a probe (`Less` for those
    /// before it, `Greater` for those after it), `Ok` with the position of an item `compare`
    /// finds equal to the probe, or `Err` with the position at which the probe would go.
    pub fn search_by(&self, compare: impl FnMut(&T) -> Ordering) -> Result<usize, usize> {
        self.0.binary_search_by(compare)
    }

    /// The number of leading items for which `before` holds, when it holds for a prefix of the
    /// sequence and for no item after it.
    pub fn partition_point(&self, before: impl FnMut(&T) -> bool) -> usize {
        self.0.partition_point(before)
    }
}

impl<T: Clone> Items<T> {
    pub fn to_vec(&self) -> Vec<T> {
        self.0.clone()
    }

    /// The first `index` items and the rest; `index` is at most the length.
    pub fn split_at(&self, index: usize) -> (Self, Self) {
        let (left, right) = self.0.split_at(index);
        (Self(left.to_vec()), Self(right.to_vec()))
    }

    /// The items of this sequence followed by those of `other`.
    pub fn join(&self, other: &Self) -> Self {
        let mut items = Vec::with_capacity(self.len() + other.len());
        items.extend_from_slice(&self.0);
        items.extend_from_slice(&other.0);
        Self(items)
    }

    /// The sequence with `item` inserted at position `index`, which is at most the length.
    pub fn insert_at(&self, index: usize, item: T) -> Self {
        let mut items = self.0.clone();
        items.insert(index, item);
        Self(items)
    }

    /// The sequence without the item at position `index`, which is below the length, and that
    /// item.
    pub fn remove_at(&self, index: usize) -> (Self, T) {
        let mut items = self.0.clone();
        let item = items.remove(index);
        (Self(items), item)
    }

    /// The sequence with the item at position `index`, which is below the length, replaced by
    /// `item`.
    pub fn replace_at(&self, index: usize, item: T) -> Self {
        let mut items = self.0.clone();
        items[index] = item;
        Self(items)
    }
}

impl<T: Keyed> Items<T> {
    /// In an ordered sequence, `Ok` with the position of the first item whose key is `key`, or
    /// `Err` with the position at which an item of that key would go.
    pub fn search(&self, key: &T::Key) -> Result<usize, usize> {
        let position = self.partition_point(|item| item.key() < key);
        match self.get(position) {
            Some(item) if item.key() == key => Ok(position),
            _ => Err(position),
        }
    }
}

impl<T: Keyed + Clone> Items<T> {
    /// In an ordered sequence, the items whose key is below `key` and the rest.
    pub fn split_at_key(&self, key: &T::Key) -> (Self, Self) {
        self.split_at(self.partition_point(|item| item.key() < key))
    }
}

impl<T: Ord + Clone> Items<T> {
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
    /// the two hold it together.
    pub fn union(&self, other: &Self) -> Self {
        let mut items = Vec::with_capacity(self.len() + other.len());
        let (mut left, mut right) = (self.0.iter().peekable(), other.0.iter().peekable());
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
                None => return Self(items),
            }
        }
    }
}

impl<T> Default for Items<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// The items' own debug form, as the vector prints them.
impl<T: fmt::Debug> fmt::Debug for Items<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

impl<T> From<Vec<T>> for Items<T> {
    fn from(items: Vec<T>) -> Self {
        Self(items)
    }
}

/// The items in order, as a vector.
impl<T> From<Items<T>> for Vec<T> {
    fn from(items: Items<T>) -> Self {
        items.0
    }
}

impl<T> FromIterator<T> for Items<T> {
    fn from_iter<I: IntoIterator<Item = T>>(items: I) -> Self {
        Self(items.into_iter().collect())
    }
}

impl<'a, T> IntoIterator for &'a Items<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

/// The items in order, taken out of the sequence.
impl<T> IntoIterator for Items<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter(self.0.into_iter())
    }
}

// Temporary, while the sites that read the items as a slice move to the methods above.
impl<T> Deref for Items<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.0
    }
}

/// The items of an [`Items`] in order, from either end.
#[derive(Clone, Debug)]
pub struct Iter<'a, T>(slice::Iter<'a, T>);

impl<'a, T> Iterator for Iter<'a, T> {
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

impl<T> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth_back(n)
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}

impl<T> FusedIterator for Iter<'_, T> {}

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

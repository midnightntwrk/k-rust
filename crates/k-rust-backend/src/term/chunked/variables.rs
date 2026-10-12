//! A persistent ordered set of variables, shared by handle: the representation of a term's
//! `variables` attribute.
//!
//! A term's variables are the union of its children's. Kept as an owned ordered set, that union
//! copies every child's variables at every term built above them, so a step that rebuilds the
//! cells around a symbolic collection copies the collection's variables once per cell. A
//! [`Variables`] is a handle instead: a clone shares it, and a [`Union`] keeps the largest
//! operand's handle and adds the other operands' variables to it. A term whose variables all come
//! from one child (a cell around a symbolic map) shares that child's set in constant time.
//!
//! # Two backings
//!
//! A set of at most `B` variables, the number one leaf of the tree holds, is that leaf's items
//! alone: a shared sorted slice, without the tree node and its summary. Most sets are of this
//! kind (a variable, a rule's pattern, a cell around a few symbolic subterms); for them the node,
//! the summary's first and last item and its sequence hash, which nothing reads for a set, would
//! be pure overhead on every term built. A larger set is a [`Chunked`] tree, so adding a few
//! variables to it copies one path per variable instead of the whole set. Which backing a set has
//! follows from its size alone (empty, at most `B`, more), so two equal sets have the same
//! backing and the backing is not part of the set's value.
//!
//! A union whose largest operand is a tree inserts the other operands' missing variables into
//! that tree, each by a path copy: `O(m log V)` for the `m` variables outside it, among `V`. A
//! union whose largest operand is a slice has at most `B` variables per operand and nothing large
//! to share, so it merges the operands' variables into one sorted sequence.
//!
//! The tree holds the same entries as a [`Multiset`] (an element and a count), ordered by
//! element, and reads only the elements. The variables of a collection are the elements of its
//! root's multiset of variables, so [`Variables::of_multiset`] makes that set by sharing the
//! multiset's tree when it has more than `B` elements (and copies the at most `B` otherwise);
//! entries the set adds itself carry the count 1, which nothing reads.

use std::{collections::BTreeSet, fmt, hash::Hash, iter::FusedIterator, slice, sync::Arc};

use super::{
    Chunked, VARIABLE_BRANCHING,
    multiset::{Multiset, Occurrences},
};
use crate::term::variables::{VariableLookup, disjoint};

/// A persistent ordered set of variables; see the module documentation. Two sets are equal when
/// they hold the same variables, whatever history built them.
pub(crate) struct Variables<V: Ord + Clone + Hash + fmt::Debug, const B: usize = VARIABLE_BRANCHING>
{
    backing: Backing<V, B>,
}

/// The backing of a [`Variables`], fixed by its size: `Empty` holds none, `Slice` from one to `B`
/// variables in order, `Tree` more than `B`.
enum Backing<V: Ord + Clone + Hash + fmt::Debug, const B: usize> {
    Empty,
    Slice(Arc<[V]>),
    Tree(Chunked<Occurrences<V>, B>),
}

impl<V: Ord + Clone + Hash + fmt::Debug, const B: usize> Variables<V, B> {
    /// The empty set.
    pub(crate) const fn new() -> Self {
        Self {
            backing: Backing::Empty,
        }
    }

    /// The set holding `variable` alone.
    pub(crate) fn singleton(variable: V) -> Self {
        Self {
            backing: Backing::Slice(Arc::from([variable])),
        }
    }

    /// The set of `variables`, in time `O(n log n)` for `n` of them (a sort, then a bulk load).
    pub(crate) fn of(variables: impl IntoIterator<Item = V>) -> Self {
        let mut variables: Vec<V> = variables.into_iter().collect();
        variables.sort();
        variables.dedup();
        Self::of_ordered(variables)
    }

    /// The set of `variables`, distinct and in order: the backing their number calls for.
    fn of_ordered(variables: Vec<V>) -> Self {
        let backing = if variables.is_empty() {
            Backing::Empty
        } else if variables.len() <= B {
            Backing::Slice(Arc::from(variables))
        } else {
            Backing::Tree(Chunked::from_vec(
                variables
                    .into_iter()
                    .map(|element| Occurrences { element, count: 1 })
                    .collect(),
            ))
        };
        Self { backing }
    }

    /// The elements of `multiset`: its tree, shared, when it has more than `B` elements, otherwise
    /// a copy of the at most `B` elements.
    pub(crate) fn of_multiset(multiset: &Multiset<V, B>) -> Self {
        if multiset.len() <= B {
            return Self::of_ordered(multiset.elements().cloned().collect());
        }
        Self {
            backing: Backing::Tree(multiset.entries().clone()),
        }
    }

    /// The number of variables.
    pub(crate) fn len(&self) -> usize {
        match &self.backing {
            Backing::Empty => 0,
            Backing::Slice(variables) => variables.len(),
            Backing::Tree(entries) => entries.len(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        matches!(self.backing, Backing::Empty)
    }

    /// The variables, in order.
    pub(crate) fn iter(&self) -> Iter<'_, V> {
        match &self.backing {
            Backing::Empty => Iter::Slice([].iter()),
            Backing::Slice(variables) => Iter::Slice(variables.iter()),
            Backing::Tree(entries) => Iter::Tree(entries.iter()),
        }
    }

    /// Whether the set holds `variable`, in time logarithmic in its size.
    pub(crate) fn contains(&self, variable: &V) -> bool {
        match &self.backing {
            Backing::Empty => false,
            Backing::Slice(variables) => variables.binary_search(variable).is_ok(),
            Backing::Tree(entries) => entries.search(variable).is_ok(),
        }
    }

    /// The variable at `index` in order, in time logarithmic in the set's size.
    pub(crate) fn get(&self, index: usize) -> Option<&V> {
        match &self.backing {
            Backing::Empty => None,
            Backing::Slice(variables) => variables.get(index),
            Backing::Tree(entries) => entries.get(index).map(|entry| &entry.element),
        }
    }

    /// The number of leading variables for which `before` holds, when it holds for a prefix of
    /// the ordered variables and for none after it, in time logarithmic in the set's size.
    pub(crate) fn partition_point(&self, mut before: impl FnMut(&V) -> bool) -> usize {
        match &self.backing {
            Backing::Empty => 0,
            Backing::Slice(variables) => variables.partition_point(before),
            Backing::Tree(entries) => entries.partition_point(|entry| before(&entry.element)),
        }
    }

    /// The variables as an owned ordered set, in time linear in their number.
    pub(crate) fn to_btree_set(&self) -> BTreeSet<V> {
        self.iter().cloned().collect()
    }

    /// Whether `other` holds every variable of this set: one lookup in `other` per variable of
    /// this set, none when this set holds more variables than `other`.
    pub(crate) fn is_subset<L: VariableLookup<V> + ?Sized>(&self, other: &L) -> bool {
        self.len() <= other.variable_count() && self.iter().all(|v| other.holds_variable(v))
    }

    /// Whether the two sets share no variable: the smaller set's variables are looked up in the
    /// larger one.
    pub(crate) fn is_disjoint<L: VariableLookup<V> + ?Sized>(&self, other: &L) -> bool {
        disjoint(self, other)
    }

    /// The set with `variable` added; this set's handle when it already holds it.
    #[must_use]
    pub(crate) fn insert(&self, variable: &V) -> Self {
        let mut union = Union::new();
        union.add(self);
        union.add_variables(slice::from_ref(variable));
        union.finish()
    }

    /// The union of the two sets; see [`Union`].
    #[must_use]
    pub(crate) fn union(&self, other: &Self) -> Self {
        Self::union_all([self, other])
    }

    /// The union of `operands`; see [`Union`].
    pub(crate) fn union_all<'a>(operands: impl IntoIterator<Item = &'a Self>) -> Self
    where
        V: 'a,
    {
        let mut union = Union::new();
        for operand in operands {
            union.add(operand);
        }
        union.finish()
    }

    /// Whether the two sets are one handle: the same slice or the same tree (or both empty).
    pub(crate) fn shares_handle(&self, other: &Self) -> bool {
        match (&self.backing, &other.backing) {
            (Backing::Empty, Backing::Empty) => true,
            (Backing::Slice(left), Backing::Slice(right)) => Arc::ptr_eq(left, right),
            (Backing::Tree(left), Backing::Tree(right)) => left.shares_root(right),
            _ => false,
        }
    }

    /// The tree of entries of a set of more than `B` variables, shared with a multiset when the
    /// set was made from one; `None` for a smaller set.
    pub(crate) fn tree(&self) -> Option<&Chunked<Occurrences<V>, B>> {
        match &self.backing {
            Backing::Tree(entries) => Some(entries),
            Backing::Empty | Backing::Slice(_) => None,
        }
    }
}

/// The union of a sequence of [`Variables`], given one operand at a time.
///
/// It keeps the first largest operand and copies the variables of the others. An operand that is
/// the largest one's handle adds nothing, so the union of a set with itself, or with nothing
/// else, is that set's handle. [`finish`](Union::finish) drops the copied variables the largest
/// operand holds, and then:
///
/// - when none is left, returns the largest operand's handle;
/// - when the largest operand is a tree, inserts each one left into it, by a path copy;
/// - otherwise (every operand has at most `B` variables) merges the ones left with the largest
///   operand's into one ordered sequence.
///
/// Copying the other operands' variables as they come lets a union of many small operands sort
/// their variables once, instead of merging them one operand at a time.
pub(crate) struct Union<'a, V: Ord + Clone + Hash + fmt::Debug, const B: usize = VARIABLE_BRANCHING>
{
    largest: Option<&'a Variables<V, B>>,
    others: Vec<V>,
}

impl<'a, V: Ord + Clone + Hash + fmt::Debug, const B: usize> Union<'a, V, B> {
    pub(crate) const fn new() -> Self {
        Self {
            largest: None,
            others: Vec::new(),
        }
    }

    /// Add `operand`'s variables to the union.
    pub(crate) fn add(&mut self, operand: &'a Variables<V, B>) {
        if operand.is_empty() {
            return;
        }
        match self.largest {
            None => self.largest = Some(operand),
            Some(largest) if largest.shares_handle(operand) => {}
            Some(largest) if operand.len() > largest.len() => {
                self.others.extend(largest.iter().cloned());
                self.largest = Some(operand);
            }
            Some(_) => self.others.extend(operand.iter().cloned()),
        }
    }

    /// Add `variables` to the union, as the variables of an operand that is not the largest.
    fn add_variables(&mut self, variables: &[V]) {
        self.others.extend_from_slice(variables);
    }

    /// The union of what was added; see the type's documentation.
    pub(crate) fn finish(self) -> Variables<V, B> {
        let Self {
            largest,
            mut others,
        } = self;
        let Some(largest) = largest else {
            return Variables::of(others);
        };
        others.retain(|variable| !largest.contains(variable));
        if others.is_empty() {
            return largest.clone();
        }
        others.sort();
        others.dedup();
        match &largest.backing {
            Backing::Tree(entries) => {
                let mut entries = entries.clone();
                for element in others {
                    let index = entries
                        .search(&element)
                        .expect_err("a variable the largest operand lacks");
                    entries = entries.insert_at(index, Occurrences { element, count: 1 });
                }
                Variables {
                    backing: Backing::Tree(entries),
                }
            }
            Backing::Empty | Backing::Slice(_) => {
                Variables::of_ordered(merge(largest.iter().cloned(), others))
            }
        }
    }
}

/// Two ordered sequences of distinct variables, with no variable in both, merged in order.
fn merge<V: Ord>(left: impl Iterator<Item = V>, right: Vec<V>) -> Vec<V> {
    let mut merged = Vec::with_capacity(left.size_hint().0 + right.len());
    let mut left = left.peekable();
    for variable in right {
        while let Some(before) = left.next_if(|next| *next < variable) {
            merged.push(before);
        }
        merged.push(variable);
    }
    merged.extend(left);
    merged
}

impl<V: Ord + Clone + Hash + fmt::Debug, const B: usize> VariableLookup<V> for Variables<V, B> {
    fn variable_count(&self) -> usize {
        self.len()
    }

    fn holds_variable(&self, variable: &V) -> bool {
        self.contains(variable)
    }

    fn any_variable(&self, test: &mut dyn FnMut(&V) -> bool) -> bool {
        self.iter().any(test)
    }
}

impl<V: Ord + Clone + Hash + fmt::Debug, const B: usize> Clone for Variables<V, B> {
    fn clone(&self) -> Self {
        let backing = match &self.backing {
            Backing::Empty => Backing::Empty,
            Backing::Slice(variables) => Backing::Slice(Arc::clone(variables)),
            Backing::Tree(entries) => Backing::Tree(entries.clone()),
        };
        Self { backing }
    }
}

impl<V: Ord + Clone + Hash + fmt::Debug, const B: usize> Default for Variables<V, B> {
    fn default() -> Self {
        Self::new()
    }
}

/// Equal when they hold the same variables. The backing follows from the size, so sets of
/// different backings differ; the counts of entries shared with a multiset are not part of the
/// set, and a part of a tree both sets share is not compared.
impl<V: Ord + Clone + Hash + fmt::Debug, const B: usize> PartialEq for Variables<V, B> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.backing, &other.backing) {
            (Backing::Empty, Backing::Empty) => true,
            (Backing::Slice(left), Backing::Slice(right)) => {
                Arc::ptr_eq(left, right) || left == right
            }
            (Backing::Tree(left), Backing::Tree(right)) => {
                left.eq_by(right, |left, right| left.element == right.element)
            }
            _ => false,
        }
    }
}

impl<V: Ord + Clone + Hash + fmt::Debug, const B: usize> Eq for Variables<V, B> {}

impl<V: Ord + Clone + Hash + fmt::Debug, const B: usize> fmt::Debug for Variables<V, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

/// The variables of a [`Variables`], in order, from either end.
#[derive(Clone)]
pub(crate) enum Iter<'a, V: Ord + Clone + Hash + fmt::Debug> {
    Slice(slice::Iter<'a, V>),
    Tree(super::Iter<'a, Occurrences<V>>),
}

impl<'a, V: Ord + Clone + Hash + fmt::Debug> Iterator for Iter<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> {
        match self {
            Self::Slice(variables) => variables.next(),
            Self::Tree(entries) => entries.next().map(|entry| &entry.element),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::Slice(variables) => variables.size_hint(),
            Self::Tree(entries) => entries.size_hint(),
        }
    }
}

impl<V: Ord + Clone + Hash + fmt::Debug> DoubleEndedIterator for Iter<'_, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            Self::Slice(variables) => variables.next_back(),
            Self::Tree(entries) => entries.next_back().map(|entry| &entry.element),
        }
    }
}

impl<V: Ord + Clone + Hash + fmt::Debug> ExactSizeIterator for Iter<'_, V> {}

impl<V: Ord + Clone + Hash + fmt::Debug> FusedIterator for Iter<'_, V> {}

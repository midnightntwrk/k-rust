//! A persistent ordered set of variables, shared by handle: the planned type of a term's
//! `variables` attribute.
//!
//! A term's variables are the union of its children's. Kept as an owned ordered set, that union
//! copies every child's variables at every term built above them, so a step that rebuilds the
//! cells around a symbolic collection copies the collection's variables once per cell. A
//! [`Variables`] is a handle to a [`Chunked`] tree instead: a clone shares it, and
//! [`Variables::union_all`] keeps the largest operand's handle and inserts the other operands'
//! variables into it, each by a path copy of the shared tree. A term whose variables all come from
//! one child (a cell around a symbolic map) shares that child's set in constant time; otherwise
//! the work is `O(m log V)` for the `m` variables outside the largest child, among `V`.
//!
//! The set's tree holds the same entries as a [`Multiset`] (an element and a count), ordered by
//! element, and reads only the elements. The variables of a collection are the elements of its
//! root's multiset of variables, so [`Variables::of_multiset`] makes that set in constant time by
//! sharing the multiset's tree; entries the set adds itself carry the count 1, which nothing
//! reads.

use std::{collections::BTreeSet, fmt, hash::Hash};

use super::{
    Chunked, DEFAULT_BRANCHING,
    multiset::{Multiset, Occurrences},
};

/// A set of variables that can be asked whether it holds one, and how many it holds:
/// [`Variables::is_subset`] and [`Variables::is_disjoint`] take any of them, so a caller can test
/// a term's variables against the set it already has (an ordered set, another term's variables,
/// and, once terms use [`Variables`], a substitution's domain).
pub(crate) trait VariableLookup<V> {
    /// The number of distinct variables.
    fn variable_count(&self) -> usize;

    fn holds_variable(&self, variable: &V) -> bool;

    /// Whether some variable satisfies `test`, stopping at the first that does.
    fn any_variable(&self, test: &mut dyn FnMut(&V) -> bool) -> bool;
}

impl<V: Ord> VariableLookup<V> for BTreeSet<V> {
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

/// A persistent ordered set of variables; see the module documentation. Two sets are equal when
/// they hold the same variables, whatever history built them.
pub(crate) struct Variables<V: Ord + Clone + Hash + fmt::Debug, const B: usize = DEFAULT_BRANCHING>
{
    entries: Chunked<Occurrences<V>, B>,
}

impl<V: Ord + Clone + Hash + fmt::Debug, const B: usize> Variables<V, B> {
    /// The empty set.
    pub(crate) const fn new() -> Self {
        Self {
            entries: Chunked::new(),
        }
    }

    /// The set of `variables`, in time `O(n log n)` for `n` of them (a sort, then a bulk load).
    pub(crate) fn of(variables: impl IntoIterator<Item = V>) -> Self {
        let mut variables: Vec<V> = variables.into_iter().collect();
        variables.sort();
        variables.dedup();
        Self {
            entries: Chunked::from_vec(
                variables
                    .into_iter()
                    .map(|element| Occurrences { element, count: 1 })
                    .collect(),
            ),
        }
    }

    /// The elements of `multiset`, sharing its tree: constant time.
    pub(crate) fn of_multiset(multiset: &Multiset<V, B>) -> Self {
        Self {
            entries: multiset.entries().clone(),
        }
    }

    /// The number of variables.
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The variables, in order.
    pub(crate) fn iter(&self) -> impl DoubleEndedIterator<Item = &V> + ExactSizeIterator {
        self.entries.iter().map(|entry| &entry.element)
    }

    /// Whether the set holds `variable`, in time logarithmic in its size.
    pub(crate) fn contains(&self, variable: &V) -> bool {
        self.entries.search(variable).is_ok()
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
        if self.len() <= other.variable_count() {
            !self.iter().any(|v| other.holds_variable(v))
        } else {
            !other.any_variable(&mut |v| self.contains(v))
        }
    }

    /// The set with `variable` added, by a path copy; this set's handle when it already holds it.
    #[must_use]
    pub(crate) fn insert(&self, variable: &V) -> Self {
        let mut set = self.clone();
        set.add(variable);
        set
    }

    /// Add `variable` to this handle's set, unless it holds it already.
    fn add(&mut self, variable: &V) {
        if let Err(index) = self.entries.search(variable) {
            self.entries = self.entries.insert_at(
                index,
                Occurrences {
                    element: variable.clone(),
                    count: 1,
                },
            );
        }
    }

    /// The union of the two sets; see [`Variables::union_all`].
    #[must_use]
    pub(crate) fn union(&self, other: &Self) -> Self {
        Self::union_all([self, other])
    }

    /// The union of `operands`: the handle of the largest one (the first of the largest), with
    /// the variables of the others it lacks inserted into it. An operand that shares the largest
    /// one's tree adds nothing and is skipped without a lookup, so the union of a set with itself
    /// or with nothing else is that set's handle.
    pub(crate) fn union_all<'a>(operands: impl IntoIterator<Item = &'a Self>) -> Self
    where
        V: 'a,
    {
        let operands: Vec<&Self> = operands.into_iter().collect();
        let Some(largest) = operands
            .iter()
            .enumerate()
            .rev()
            .max_by_key(|(_, operand)| operand.len())
            .map(|(index, _)| index)
        else {
            return Self::new();
        };
        let mut union = operands[largest].clone();
        for (index, operand) in operands.iter().enumerate() {
            if index == largest || operand.entries.shares_root(&operands[largest].entries) {
                continue;
            }
            for variable in operand.iter() {
                union.add(variable);
            }
        }
        union
    }

    /// The tree of entries, shared with a multiset when the set was made from one.
    pub(crate) fn entries(&self) -> &Chunked<Occurrences<V>, B> {
        &self.entries
    }
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
        Self {
            entries: self.entries.clone(),
        }
    }
}

impl<V: Ord + Clone + Hash + fmt::Debug, const B: usize> Default for Variables<V, B> {
    fn default() -> Self {
        Self::new()
    }
}

/// Equal when they hold the same variables: the counts of entries shared with a multiset are not
/// part of the set, and a part of the tree both sets share is not compared.
impl<V: Ord + Clone + Hash + fmt::Debug, const B: usize> PartialEq for Variables<V, B> {
    fn eq(&self, other: &Self) -> bool {
        self.entries
            .eq_by(&other.entries, |left, right| left.element == right.element)
    }
}

impl<V: Ord + Clone + Hash + fmt::Debug, const B: usize> Eq for Variables<V, B> {}

impl<V: Ord + Clone + Hash + fmt::Debug, const B: usize> fmt::Debug for Variables<V, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

//! The free variables of a term, behind the interface their shared set will have.
//!
//! [`Variables`] is the type of [`TermAttributes::variables`](super::TermAttributes::variables).
//! It holds the variables in one ordered set, and its methods are those a persistent ordered set
//! shared by handle provides (design K22, revision 2, §6 and §11): iteration in order, size,
//! membership, a copy as an owned set, union, and the subset and disjointness tests against any
//! [`VariableLookup`]. Reading a term's variables through these methods only lets the
//! representation change without touching the code that reads them.
//!
//! The set is owned here, so a term's set is a copy of its children's: building a term costs the
//! number of variables beneath it, where the shared set will copy only the variables outside its
//! largest child.
//!
//! Equality is that of the variable sets; `Debug` prints the set as the ordered set prints it.

use std::{
    collections::{BTreeMap, BTreeSet, btree_set},
    fmt,
    iter::FusedIterator,
};

use super::Variable;

/// A set of variables that can be asked whether it holds one, and how many it holds:
/// [`Variables::is_subset`] and [`Variables::is_disjoint`] take any of them, so a caller can test
/// a term's variables against the set it already has: an ordered set, another term's variables,
/// or a substitution's domain.
///
/// The variable type is a parameter so that the shared set's own tests can use small elements;
/// every lookup outside them is over [`Variable`], the default.
pub trait VariableLookup<V = Variable> {
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

/// The domain of a map: a substitution's bound variables.
impl<V: Ord, T> VariableLookup<V> for BTreeMap<V, T> {
    fn variable_count(&self) -> usize {
        self.len()
    }

    fn holds_variable(&self, variable: &V) -> bool {
        self.contains_key(variable)
    }

    fn any_variable(&self, test: &mut dyn FnMut(&V) -> bool) -> bool {
        self.keys().any(test)
    }
}

/// The free variables of a term (see the [module documentation](self)).
#[derive(Clone, Default, Eq, PartialEq)]
pub struct Variables(BTreeSet<Variable>);

impl Variables {
    /// The empty set.
    pub const fn new() -> Self {
        Self(BTreeSet::new())
    }

    /// The set holding `variable` alone.
    pub(crate) fn singleton(variable: Variable) -> Self {
        Self(BTreeSet::from([variable]))
    }

    /// The number of variables.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The variables, in order.
    pub fn iter(&self) -> Iter<'_> {
        Iter(self.0.iter())
    }

    pub fn contains(&self, variable: &Variable) -> bool {
        self.0.contains(variable)
    }

    /// The variables as an owned ordered set.
    pub fn to_btree_set(&self) -> BTreeSet<Variable> {
        self.0.clone()
    }

    /// Whether `other` holds every variable of this set: one lookup in `other` per variable of
    /// this set, none when this set holds more variables than `other`.
    pub fn is_subset<L: VariableLookup + ?Sized>(&self, other: &L) -> bool {
        self.len() <= other.variable_count() && self.iter().all(|v| other.holds_variable(v))
    }

    /// Whether the two sets share no variable: the smaller set's variables are looked up in the
    /// larger one.
    pub fn is_disjoint<L: VariableLookup + ?Sized>(&self, other: &L) -> bool {
        disjoint(self, other)
    }

    /// The variables both sets hold: the smaller set's variables are looked up in the larger one.
    pub fn intersection(&self, other: &Self) -> BTreeSet<Variable> {
        let (smaller, larger) = if self.len() <= other.len() {
            (self, other)
        } else {
            (other, self)
        };
        smaller
            .iter()
            .filter(|variable| larger.contains(variable))
            .cloned()
            .collect()
    }

    /// The union of the two sets.
    #[must_use]
    pub fn union(&self, other: &Self) -> Self {
        let mut union = self.clone();
        union.add_all(other);
        union
    }

    /// Add the variables of `other` to this set: a copy of `other` when this set is empty.
    pub(crate) fn add_all(&mut self, other: &Self) {
        if self.0.is_empty() {
            self.0.clone_from(&other.0);
        } else {
            self.0.extend(other.0.iter().cloned());
        }
    }
}

/// Whether `left` and `right` share no variable: the smaller one's variables are looked up in the
/// larger one.
pub(crate) fn disjoint<V>(
    left: &(impl VariableLookup<V> + ?Sized),
    right: &(impl VariableLookup<V> + ?Sized),
) -> bool {
    if left.variable_count() <= right.variable_count() {
        !left.any_variable(&mut |v| right.holds_variable(v))
    } else {
        !right.any_variable(&mut |v| left.holds_variable(v))
    }
}

impl VariableLookup for Variables {
    fn variable_count(&self) -> usize {
        self.len()
    }

    fn holds_variable(&self, variable: &Variable) -> bool {
        self.contains(variable)
    }

    fn any_variable(&self, test: &mut dyn FnMut(&Variable) -> bool) -> bool {
        self.iter().any(test)
    }
}

impl FromIterator<Variable> for Variables {
    fn from_iter<I: IntoIterator<Item = Variable>>(variables: I) -> Self {
        Self(variables.into_iter().collect())
    }
}

impl<'a> IntoIterator for &'a Variables {
    type Item = &'a Variable;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Iter<'a> {
        self.iter()
    }
}

impl fmt::Debug for Variables {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

/// The variables of a [`Variables`], in order.
#[derive(Clone, Debug)]
pub struct Iter<'a>(btree_set::Iter<'a, Variable>);

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Variable;

    fn next(&mut self) -> Option<&'a Variable> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl DoubleEndedIterator for Iter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl ExactSizeIterator for Iter<'_> {}

impl FusedIterator for Iter<'_> {}

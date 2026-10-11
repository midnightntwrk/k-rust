//! The free variables of a term, in a persistent set shared by handle.
//!
//! [`Variables`] is the type of [`TermAttributes::variables`](super::TermAttributes::variables).
//! Its methods are those of a persistent ordered set (design K22, revision 2, §6 and §11):
//! iteration in order, size, membership, a copy as an owned set, union, and the subset and
//! disjointness tests against any [`VariableLookup`].
//!
//! The set is a handle to the persistent set of `chunked::variables`, so a term's set shares its
//! children's: their union keeps the largest child set's handle and adds the variables of the
//! others to it. A term whose variables all come from one child (a cell around a symbolic
//! map, an injection) shares that child's set in constant time; otherwise building it costs the
//! variables outside its largest child. A map's set is the support of the multiset of variables
//! its entries' tree keeps, shared with it.
//!
//! Equality is that of the variable sets; `Debug` prints the set as an ordered set prints it.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    iter::FusedIterator,
};

use super::{
    Variable,
    chunked::{multiset::Multiset, variables},
};

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
pub struct Variables(variables::Variables<Variable>);

impl Variables {
    /// The empty set.
    pub const fn new() -> Self {
        Self(variables::Variables::new())
    }

    /// The set holding `variable` alone.
    pub(crate) fn singleton(variable: Variable) -> Self {
        Self(variables::Variables::singleton(variable))
    }

    /// The variables `multiset` counts: its tree, shared, unless it is small enough for the set
    /// to copy it (see `chunked::variables`).
    pub(crate) fn of_multiset(multiset: &Multiset<Variable>) -> Self {
        Self(variables::Variables::of_multiset(multiset))
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
        self.0.to_btree_set()
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

    /// The union of the two sets: the larger one's handle when it holds the other's variables,
    /// otherwise that set with the other's variables added.
    #[must_use]
    pub fn union(&self, other: &Self) -> Self {
        Self(self.0.union(&other.0))
    }

    /// Test builds: whether the two sets are one handle.
    #[cfg(test)]
    pub(crate) fn shares_handle(&self, other: &Self) -> bool {
        self.0.shares_handle(&other.0)
    }
}

/// The union of a term's children's variable sets, given one set at a time: the handle of the
/// first largest set when it holds the others' variables, otherwise that set with the others'
/// variables added (`chunked::variables::Union`).
pub(crate) struct Union<'a>(variables::Union<'a, Variable>);

impl<'a> Union<'a> {
    pub(crate) const fn new() -> Self {
        Self(variables::Union::new())
    }

    pub(crate) fn add(&mut self, operand: &'a Variables) {
        self.0.add(&operand.0);
    }

    pub(crate) fn finish(self) -> Variables {
        Variables(self.0.finish())
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
    fn from_iter<I: IntoIterator<Item = Variable>>(set: I) -> Self {
        Self(variables::Variables::of(set))
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
#[derive(Clone)]
pub struct Iter<'a>(variables::Iter<'a, Variable>);

impl fmt::Debug for Iter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

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

//! Sequences whose order is fixed by each element's canonical key.

use std::ops::Deref;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{GroupAssociativitySentence, ModuleId, PrecedenceRelation};

/// Supplies the canonical ordering key for a sequence element.
pub trait SortKey {
    /// The key used for stable ordering.
    type Key: Ord + ?Sized;

    /// Returns the element's ordering key.
    fn sort_key(&self) -> &Self::Key;
}

impl SortKey for ModuleId {
    type Key = Self;

    fn sort_key(&self) -> &Self::Key {
        self
    }
}

impl SortKey for PrecedenceRelation {
    type Key = Self;
    fn sort_key(&self) -> &Self::Key {
        self
    }
}

impl SortKey for GroupAssociativitySentence {
    type Key = Self;
    fn sort_key(&self) -> &Self::Key {
        self
    }
}

/// A sequence kept in stable key order, including equal-key elements.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SortedByKey<T>(Vec<T>);

impl<T: SortKey> SortedByKey<T> {
    /// Sorts elements by their canonical key.
    #[must_use]
    pub fn new(mut elements: Vec<T>) -> Self {
        elements.sort_by(|left, right| left.sort_key().cmp(right.sort_key()));
        Self(elements)
    }

    /// Adds an element after existing elements with the same key.
    pub fn push(&mut self, element: T) {
        let index = self
            .0
            .partition_point(|existing| existing.sort_key() <= element.sort_key());
        self.0.insert(index, element);
    }
}

impl<T: SortKey> From<Vec<T>> for SortedByKey<T> {
    fn from(elements: Vec<T>) -> Self {
        Self::new(elements)
    }
}

impl<T: SortKey> FromIterator<T> for SortedByKey<T> {
    fn from_iter<I: IntoIterator<Item = T>>(elements: I) -> Self {
        Self::new(elements.into_iter().collect())
    }
}

impl<T> Deref for SortedByKey<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a, T> IntoIterator for &'a SortedByKey<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<T: Serialize> Serialize for SortedByKey<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

impl<'de, T: Deserialize<'de> + SortKey> Deserialize<'de> for SortedByKey<T> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Vec::<T>::deserialize(deserializer).map(Self::new)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serde_keeps_the_sequence_shape_and_sorts_input() {
        let modules: SortedByKey<ModuleId> = serde_json::from_str(r#"["Z", "A"]"#).unwrap();
        assert_eq!(serde_json::to_string(&modules).unwrap(), r#"["A","Z"]"#);
    }
}

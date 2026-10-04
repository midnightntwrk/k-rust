//! Ordered collections with a minimum structural cardinality.

use serde::{Deserialize, Serialize};

/// A sequence contains fewer than two elements.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AtLeastTwoError;

impl std::fmt::Display for AtLeastTwoError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("collection requires at least two elements")
    }
}

impl std::error::Error for AtLeastTwoError {}

/// An ordered sequence with at least two elements.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    try_from = "Vec<T>",
    into = "Vec<T>",
    bound(
        serialize = "T: Serialize + Clone",
        deserialize = "T: Deserialize<'de>"
    )
)]
pub struct AtLeastTwo<T> {
    first: Box<T>,
    second: Box<T>,
    rest: Vec<T>,
}

impl<T> AtLeastTwo<T> {
    /// Creates the mandatory pair followed by any remaining elements.
    #[must_use]
    pub fn new(first: T, second: T, rest: Vec<T>) -> Self {
        Self {
            first: Box::new(first),
            second: Box::new(second),
            rest,
        }
    }
    /// Returns the first operand.
    #[must_use]
    pub fn first(&self) -> &T {
        &self.first
    }
    /// Traverses all operands after the first.
    pub fn tail(&self) -> impl Iterator<Item = &T> {
        std::iter::once(self.second.as_ref()).chain(&self.rest)
    }
    /// Traverses all operands in source order.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        std::iter::once(self.first.as_ref()).chain(self.tail())
    }
    /// Returns the number of operands.
    #[must_use]
    pub fn len(&self) -> usize {
        2 + self.rest.len()
    }
    /// Reports whether there are no operands.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        false
    }
    /// Maps every element without changing cardinality or order.
    /// # Errors
    /// Returns the first mapping error.
    pub fn try_map<U, E>(self, mut map: impl FnMut(T) -> Result<U, E>) -> Result<AtLeastTwo<U>, E> {
        Ok(AtLeastTwo {
            first: Box::new(map(*self.first)?),
            second: Box::new(map(*self.second)?),
            rest: self.rest.into_iter().map(map).collect::<Result<_, _>>()?,
        })
    }
    /// Maps borrowed elements without changing cardinality or order.
    /// # Errors
    /// Returns the first mapping error.
    pub fn try_map_ref<U, E>(
        &self,
        mut map: impl FnMut(&T) -> Result<U, E>,
    ) -> Result<AtLeastTwo<U>, E> {
        Ok(AtLeastTwo::new(
            map(&self.first)?,
            map(&self.second)?,
            self.rest.iter().map(map).collect::<Result<_, _>>()?,
        ))
    }
    /// Separates the first element from the remaining nonempty sequence.
    pub fn into_head_tail(self) -> (T, impl Iterator<Item = T>) {
        (*self.first, std::iter::once(*self.second).chain(self.rest))
    }
}

impl<T> TryFrom<Vec<T>> for AtLeastTwo<T> {
    type Error = AtLeastTwoError;
    fn try_from(values: Vec<T>) -> Result<Self, Self::Error> {
        let mut values = values.into_iter();
        match (values.next(), values.next()) {
            (Some(first), Some(second)) => Ok(Self::new(first, second, values.collect())),
            _ => Err(AtLeastTwoError),
        }
    }
}

impl<T> From<AtLeastTwo<T>> for Vec<T> {
    fn from(value: AtLeastTwo<T>) -> Self {
        std::iter::once(*value.first)
            .chain(std::iter::once(*value.second))
            .chain(value.rest)
            .collect()
    }
}

impl<'a, T> IntoIterator for &'a AtLeastTwo<T> {
    type Item = &'a T;
    type IntoIter = std::iter::Chain<
        std::iter::Once<&'a T>,
        std::iter::Chain<std::iter::Once<&'a T>, std::slice::Iter<'a, T>>,
    >;
    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self.first.as_ref())
            .chain(std::iter::once(self.second.as_ref()).chain(&self.rest))
    }
}

/// An ordered sequence with at least one element.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NonEmpty<T> {
    first: T,
    rest: Vec<T>,
}

impl<T> NonEmpty<T> {
    /// Creates the mandatory first element followed by any remaining elements.
    #[must_use]
    pub fn new(first: T, rest: Vec<T>) -> Self {
        Self { first, rest }
    }
    /// Returns the first element.
    #[must_use]
    pub const fn first(&self) -> &T {
        &self.first
    }
    /// Returns mutable access to the first element without changing cardinality.
    #[must_use]
    pub const fn first_mut(&mut self) -> &mut T {
        &mut self.first
    }
    /// Returns the number of elements.
    #[must_use]
    pub fn len(&self) -> usize {
        1 + self.rest.len()
    }
    /// Reports whether there are no elements.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        false
    }
    /// Traverses elements in source order.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        std::iter::once(&self.first).chain(&self.rest)
    }
    /// Maps every element without changing cardinality or order.
    /// # Errors
    /// Returns the first mapping error.
    pub fn try_map<U, E>(self, mut map: impl FnMut(T) -> Result<U, E>) -> Result<NonEmpty<U>, E> {
        Ok(NonEmpty::new(
            map(self.first)?,
            self.rest.into_iter().map(map).collect::<Result<_, _>>()?,
        ))
    }
    /// Maps borrowed elements without changing cardinality or order.
    /// # Errors
    /// Returns the first mapping error.
    pub fn try_map_ref<U, E>(
        &self,
        mut map: impl FnMut(&T) -> Result<U, E>,
    ) -> Result<NonEmpty<U>, E> {
        Ok(NonEmpty::new(
            map(&self.first)?,
            self.rest.iter().map(map).collect::<Result<_, _>>()?,
        ))
    }
    /// Separates the first element from the remaining elements.
    pub fn into_head_tail(self) -> (T, std::vec::IntoIter<T>) {
        (self.first, self.rest.into_iter())
    }
}

impl<T> IntoIterator for NonEmpty<T> {
    type Item = T;
    type IntoIter = std::iter::Chain<std::iter::Once<T>, std::vec::IntoIter<T>>;
    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self.first).chain(self.rest)
    }
}

impl<'a, T> IntoIterator for &'a NonEmpty<T> {
    type Item = &'a T;
    type IntoIter = std::iter::Chain<std::iter::Once<&'a T>, std::slice::Iter<'a, T>>;
    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(&self.first).chain(&self.rest)
    }
}

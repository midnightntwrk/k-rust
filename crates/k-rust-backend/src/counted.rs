//! A test item whose comparisons are counted, for tests that hold an algorithm to the number of
//! comparisons its search makes.

use std::{cell::Cell, cmp::Ordering};

/// An item that counts the comparisons made on it in a shared cell.
#[derive(Clone, Debug)]
pub(crate) struct Counted<'a> {
    pub(crate) value: u32,
    pub(crate) comparisons: &'a Cell<usize>,
}

impl PartialEq for Counted<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Counted<'_> {}

impl PartialOrd for Counted<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Counted<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.comparisons.set(self.comparisons.get() + 1);
        self.value.cmp(&other.value)
    }
}

//! A test item whose comparisons are counted, for tests that hold an algorithm to the number of
//! comparisons its search makes.

use std::{cell::Cell, cmp::Ordering};

use crate::term::{chunked::Item, items::Stored};

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

/// A map entry of counted keys, stored as map entries are, in a tree ([`Stored`]), so a test of
/// a search over map entries searches the tree. Its key is the counted item; the tree's own
/// summaries need nothing of it but its hash, which agrees with `Eq` as both read the values.
impl<'a> Item for (Counted<'a>, u32) {
    type Key = Counted<'a>;
    type Summary = ();
    type Group = ();

    fn key(&self) -> &Counted<'a> {
        &self.0
    }

    fn hash64(&self) -> u64 {
        (u64::from(self.0.value) << 32) | u64::from(self.1)
    }

    fn summary(&self) {}

    fn group(&self) {}
}

impl Stored for (Counted<'_>, u32) {
    const IN_TREE: bool = true;
}

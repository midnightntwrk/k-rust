//! A persistent multiset as a [`Chunked`] sequence of distinct elements, each with its number of
//! occurrences, ordered by element: the group summary that records, per node, how many items
//! below it mention each variable.
//!
//! Adding or removing a few occurrences copies a path of the multiset's own tree, so the
//! multisets of a node before and after an edit share all but that path. Combining two multisets
//! adds the lighter one's entries to the heavier one in one batch, so its work is the lighter
//! one's size plus the nodes of the heavier one those entries reach, each copied once.
//!
//! Test builds count the entries each thread creates, changes or removes (`ENTRY_UPDATES`), so
//! the tests can hold an edit of an item tree to the entries its difference names.

use std::{
    fmt,
    hash::{BuildHasher, Hash},
};

use super::{Chunked, Group, Item, Summary, VARIABLE_BRANCHING};
use crate::term::variables::VariableLookup;

#[cfg(test)]
thread_local! {
    /// The multiset entries this thread has created, changed or removed: one per element of
    /// [`Multiset::of`], one per [`Multiset::add`] and per [`Multiset::remove`]. Combining and
    /// subtracting count one per entry of the lighter operand.
    pub(crate) static ENTRY_UPDATES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Count `entries` entry updates (test builds only).
fn tally(entries: usize) {
    #[cfg(test)]
    ENTRY_UPDATES.with(|count| count.set(count.get() + entries));
    #[cfg(not(test))]
    let _ = entries;
}

/// An element of a [`Multiset`] and its number of occurrences, at least one.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Occurrences<E> {
    pub(crate) element: E,
    pub(crate) count: usize,
}

impl<E: Ord + Clone + Hash + fmt::Debug> Item for Occurrences<E> {
    type Key = E;
    type Summary = ();
    type Group = ();

    fn key(&self) -> &E {
        &self.element
    }

    fn hash64(&self) -> u64 {
        rustc_hash::FxBuildHasher.hash_one(self)
    }

    fn summary(&self) {}

    fn group(&self) {}
}

/// A multiset of elements: a [`Group`] whose combination adds occurrences and whose subtraction
/// removes them. Two multisets with the same occurrences are equal, whatever history built them
/// (the sequence of entries is ordered by element and has one entry per element).
#[derive(Clone, PartialEq)]
pub(crate) struct Multiset<E: Ord + Clone + Hash + fmt::Debug, const B: usize = VARIABLE_BRANCHING>
{
    entries: Chunked<Occurrences<E>, B>,
}

/// The variable multiset each node keeps by difference (module documentation).
///
/// ```toml algorithm-site
/// id = "backend.term.chunked"
/// role = "part"
/// sites = ["Multiset", "Multiset::add", "Multiset::remove"]
/// ```
impl<E: Ord + Clone + Hash + fmt::Debug, const B: usize> Multiset<E, B> {
    pub(crate) const fn new() -> Self {
        Self {
            entries: Chunked::new(),
        }
    }

    /// The multiset holding each of `elements` once per time it occurs among them.
    pub(crate) fn of(elements: impl IntoIterator<Item = E>) -> Self {
        let mut elements: Vec<E> = elements.into_iter().collect();
        elements.sort();
        let mut entries: Vec<Occurrences<E>> = Vec::new();
        for element in elements {
            match entries.last_mut() {
                Some(last) if last.element == element => last.count += 1,
                _ => entries.push(Occurrences { element, count: 1 }),
            }
        }
        tally(entries.len());
        Self {
            entries: Chunked::from_vec(entries),
        }
    }

    /// The number of distinct elements.
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The number of occurrences of `element`.
    pub(crate) fn count(&self, element: &E) -> usize {
        self.entries
            .search(element)
            .ok()
            .and_then(|index| self.entries.get(index))
            .map_or(0, |entry| entry.count)
    }

    /// The distinct elements, in order: the set the multiset is the support of.
    pub(crate) fn elements(&self) -> impl DoubleEndedIterator<Item = &E> {
        self.entries.iter().map(|entry| &entry.element)
    }

    /// The entries, in order of element.
    pub(crate) fn entries(&self) -> &Chunked<Occurrences<E>, B> {
        &self.entries
    }

    /// The multiset with `count` more occurrences of `element`.
    #[must_use]
    pub(crate) fn add(&self, element: &E, count: usize) -> Self {
        tally(1);
        let entries = match self.entries.search(element) {
            Ok(index) => {
                let entry = self.entries.get(index).expect("a found entry");
                self.entries.replace_at(
                    index,
                    Occurrences {
                        element: element.clone(),
                        count: entry.count + count,
                    },
                )
            }
            Err(index) => self.entries.insert_at(
                index,
                Occurrences {
                    element: element.clone(),
                    count,
                },
            ),
        };
        Self { entries }
    }

    /// The multiset with `count` fewer occurrences of `element`, which has at least that many.
    #[must_use]
    pub(crate) fn remove(&self, element: &E, count: usize) -> Self {
        tally(1);
        let index = self
            .entries
            .search(element)
            .expect("a multiset removes only an element it holds");
        let entry = self.entries.get(index).expect("a found entry");
        let entries = match entry.count.checked_sub(count) {
            Some(0) => self.entries.remove_at(index).0,
            Some(left) => self.entries.replace_at(
                index,
                Occurrences {
                    element: element.clone(),
                    count: left,
                },
            ),
            None => panic!("a multiset removes at most the occurrences it holds"),
        };
        Self { entries }
    }
}

/// The support of the multiset: the distinct elements, looked up by search.
impl<E: Ord + Clone + Hash + fmt::Debug, const B: usize> VariableLookup<E> for Multiset<E, B> {
    fn variable_count(&self) -> usize {
        self.len()
    }

    fn holds_variable(&self, element: &E) -> bool {
        self.count(element) > 0
    }

    fn any_variable(&self, test: &mut dyn FnMut(&E) -> bool) -> bool {
        self.elements().any(test)
    }
}

impl<E: Ord + Clone + Hash + fmt::Debug, const B: usize> fmt::Debug for Multiset<E, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map()
            .entries(
                self.entries
                    .iter()
                    .map(|entry| (&entry.element, entry.count)),
            )
            .finish()
    }
}

impl<E: Ord + Clone + Hash + fmt::Debug, const B: usize> Summary for Multiset<E, B> {
    fn identity() -> Self {
        Self::new()
    }

    /// The lighter multiset's entries added to the heavier one, in one batch
    /// ([`Chunked::add_by_key`]): each node of the heavier one's tree whose range receives
    /// entries is copied once, so the work is the lighter one's size plus the nodes it reaches,
    /// not a path copy per entry.
    fn combine(self, right: &Self) -> Self {
        let (heavier, lighter) = if self.len() >= right.len() {
            (self, right)
        } else {
            (right.clone(), &self)
        };
        if lighter.is_empty() {
            return heavier;
        }
        tally(lighter.len());
        let added = lighter.entries.iter().cloned().collect::<Vec<_>>();
        Self {
            entries: heavier
                .entries
                .add_by_key(&added, |held, added| Occurrences {
                    element: held.element.clone(),
                    count: held.count + added.count,
                }),
        }
    }
}

impl<E: Ord + Clone + Hash + fmt::Debug, const B: usize> Group for Multiset<E, B> {
    /// `part`'s occurrences removed, in one batch ([`Chunked::reduce_by_key`]), as
    /// [`combine`](Summary::combine) adds them.
    fn subtract(self, part: &Self) -> Self {
        if part.is_empty() {
            return self;
        }
        tally(part.len());
        let removed = part.entries.iter().cloned().collect::<Vec<_>>();
        Self {
            entries: self.entries.reduce_by_key(&removed, |held, removed| {
                let count = held
                    .count
                    .checked_sub(removed.count)
                    .expect("a multiset removes at most the occurrences it holds");
                (count > 0).then(|| Occurrences {
                    element: held.element.clone(),
                    count,
                })
            }),
        }
    }

    fn weight(&self) -> usize {
        self.len()
    }
}

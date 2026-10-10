//! A sequence built by appending whole sequences, which shares what it appends instead of copying
//! it.
//!
//! The simplifier's results carry what each node of a term contributed (the equations applied,
//! the effects performed, the conditions conjoined), and a node's result is its own contribution
//! with its children's results appended in order. On a chain of nested applications, appending
//! by copying would copy at each level everything the levels below produced, so the pass would be
//! quadratic in the depth; a [`Log`] appends a whole log in constant time, so each level pays for
//! its own node. The flat sequence is built once, where it is read.

use std::{fmt, sync::Arc};

/// A sequence of `T`, appended to in constant time per appended log, cloned in constant time, and
/// read in order ([`Log::iter`]) or flattened once ([`Log::into_vec`]).
///
/// Invariant: `len` is the number of items, and a log is empty exactly when it has no root; both
/// parts of a `Join` are nonempty.
pub struct Log<T> {
    len: usize,
    root: Option<Arc<Node<T>>>,
}

enum Node<T> {
    Items(Vec<T>),
    /// The items of the first part, then those of the second.
    Join(Log<T>, Log<T>),
}

impl<T> Log<T> {
    /// The empty log; it allocates nothing.
    pub const fn new() -> Self {
        Self { len: 0, root: None }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The items in order.
    pub fn iter(&self) -> Iter<'_, T> {
        let mut iter = Iter {
            items: [].iter(),
            pending: Vec::new(),
            remaining: self.len,
        };
        match self.root.as_deref() {
            Some(Node::Items(items)) => iter.items = items.iter(),
            Some(node) => iter.pending.push(node),
            None => {}
        }
        iter
    }

    /// Append `item`.
    pub fn push(&mut self, item: T) {
        if let Some(Node::Items(items)) = self.root.as_mut().and_then(Arc::get_mut) {
            items.push(item);
            self.len += 1;
        } else {
            self.append(Self::from(vec![item]));
        }
    }

    /// Append the items of `other`, sharing them: constant time, apart from a part no longer than
    /// this one that only these two logs hold, whose items move into this one's.
    ///
    /// An item moves only into a sequence at least twice as long as the one it was in, so it moves
    /// at most logarithmically often; every other append allocates one node.
    pub fn append(&mut self, mut other: Self) {
        if other.len == 0 {
            return;
        }
        if self.len == 0 {
            *self = other;
            return;
        }
        let len = self.len + other.len;
        if other.len <= self.len
            && let Some(Node::Items(items)) = self.root.as_mut().and_then(Arc::get_mut)
            && let Some(Node::Items(appended)) = other.root.as_mut().and_then(Arc::get_mut)
        {
            items.append(appended);
            self.len = len;
            return;
        }
        let first = std::mem::take(self);
        *self = Self {
            len,
            root: Some(Arc::new(Node::Join(first, other))),
        };
    }

    /// The items appended to `earlier` to give this log: `earlier` is a clone this log was
    /// extended from by [`Log::append`] and [`Log::push`] only.
    ///
    /// Cost: one node per append since `earlier`; nothing is copied. Held by `earlier`, the parts
    /// it shares are not changed in place, so they are still the left parts of the joins made
    /// since.
    pub fn since(&self, earlier: &Self) -> Self {
        let Some(target) = &earlier.root else {
            return self.clone();
        };
        let mut appended = Vec::new();
        let mut node = self
            .root
            .as_ref()
            .expect("a log extended from a nonempty one is nonempty");
        while !Arc::ptr_eq(node, target) {
            let Node::Join(first, second) = &**node else {
                unreachable!("a log is extended from an earlier state only by appending to it")
            };
            appended.push(second.clone());
            node = first
                .root
                .as_ref()
                .expect("both parts of a join are nonempty");
        }
        let mut since = Self::new();
        for part in appended.into_iter().rev() {
            since.append(part);
        }
        debug_assert_eq!(since.len, self.len - earlier.len);
        since
    }
}

impl<T: Clone> Log<T> {
    /// The items in order, moved out of every part only this log holds and cloned from the
    /// others.
    pub fn into_vec(mut self) -> Vec<T> {
        let mut items = Vec::with_capacity(self.len);
        let Some(root) = self.root.take() else {
            return items;
        };
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            match Arc::try_unwrap(node) {
                Ok(Node::Items(mut own)) if items.is_empty() => {
                    std::mem::swap(&mut items, &mut own)
                }
                Ok(Node::Items(own)) => items.extend(own),
                Ok(Node::Join(mut first, mut second)) => {
                    pending.extend(second.root.take());
                    pending.extend(first.root.take());
                }
                Err(shared) => match &*shared {
                    Node::Items(own) => items.extend(own.iter().cloned()),
                    Node::Join(first, second) => {
                        pending.extend(second.root.clone());
                        pending.extend(first.root.clone());
                    }
                },
            }
        }
        items
    }

    /// The items in order, cloned.
    pub fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }
}

/// Dropped with a work list, not by recursion: a log appended to once per level of a deep term is
/// as deep as the term.
impl<T> Drop for Log<T> {
    fn drop(&mut self) {
        if let Some(root) = self.root.take() {
            drop_root(root);
        }
    }
}

/// The work list of [`Log`]'s `Drop`, out of line: most logs dropped are empty or one part.
#[inline(never)]
fn drop_root<T>(root: Arc<Node<T>>) {
    let Ok(Node::Join(mut first, mut second)) = Arc::try_unwrap(root) else {
        return;
    };
    let mut pending = Vec::new();
    pending.extend(first.root.take());
    pending.extend(second.root.take());
    while let Some(node) = pending.pop() {
        if let Ok(Node::Join(mut first, mut second)) = Arc::try_unwrap(node) {
            pending.extend(first.root.take());
            pending.extend(second.root.take());
        }
    }
}

impl<T> Default for Log<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Clone for Log<T> {
    fn clone(&self) -> Self {
        Self {
            len: self.len,
            root: self.root.clone(),
        }
    }
}

impl<T> From<Vec<T>> for Log<T> {
    fn from(items: Vec<T>) -> Self {
        if items.is_empty() {
            Self::new()
        } else {
            Self {
                len: items.len(),
                root: Some(Arc::new(Node::Items(items))),
            }
        }
    }
}

impl<T> FromIterator<T> for Log<T> {
    fn from_iter<I: IntoIterator<Item = T>>(items: I) -> Self {
        Self::from(items.into_iter().collect::<Vec<_>>())
    }
}

impl<T: fmt::Debug> fmt::Debug for Log<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_list().entries(self.iter()).finish()
    }
}

impl<T: PartialEq<U>, U> PartialEq<Log<U>> for Log<T> {
    fn eq(&self, other: &Log<U>) -> bool {
        self.len == other.len && self.iter().eq(other.iter())
    }
}

impl<T: Eq> Eq for Log<T> {}

impl<T: PartialEq<U>, U> PartialEq<[U]> for Log<T> {
    fn eq(&self, other: &[U]) -> bool {
        self.len == other.len() && self.iter().eq(other.iter())
    }
}

impl<T: PartialEq<U>, U> PartialEq<&[U]> for Log<T> {
    fn eq(&self, other: &&[U]) -> bool {
        *self == **other
    }
}

impl<T: PartialEq<U>, U, const N: usize> PartialEq<[U; N]> for Log<T> {
    fn eq(&self, other: &[U; N]) -> bool {
        *self == other[..]
    }
}

impl<T: PartialEq<U>, U> PartialEq<Vec<U>> for Log<T> {
    fn eq(&self, other: &Vec<U>) -> bool {
        *self == other[..]
    }
}

impl<'a, T> IntoIterator for &'a Log<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T: Clone> IntoIterator for Log<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> std::vec::IntoIter<T> {
        self.into_vec().into_iter()
    }
}

/// The items of a [`Log`] in order ([`Log::iter`]).
pub struct Iter<'a, T> {
    items: std::slice::Iter<'a, T>,
    /// The parts still to read, the next one last.
    pending: Vec<&'a Node<T>>,
    remaining: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            if let Some(item) = self.items.next() {
                self.remaining -= 1;
                return Some(item);
            }
            match self.pending.pop()? {
                Node::Items(items) => self.items = items.iter(),
                Node::Join(first, second) => {
                    self.pending.extend(second.root.as_deref());
                    self.pending.extend(first.root.as_deref());
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}

#[cfg(test)]
mod tests {
    use super::Log;

    fn log(items: &[u32]) -> Log<u32> {
        Log::from(items.to_vec())
    }

    #[test]
    fn appending_keeps_the_order_of_every_part() {
        let mut built = Log::new();
        built.append(log(&[1, 2]));
        built.push(3);
        let mut tail = log(&[4]);
        tail.append(log(&[5, 6, 7]));
        built.append(tail);
        built.append(Log::new());
        assert_eq!(built.len(), 7);
        assert_eq!(built, [1, 2, 3, 4, 5, 6, 7]);
        assert_eq!(built.iter().len(), 7);
        assert_eq!(built.clone().into_vec(), [1, 2, 3, 4, 5, 6, 7]);
        assert_eq!(built.to_vec(), [1, 2, 3, 4, 5, 6, 7]);
    }

    #[test]
    fn a_shared_part_is_not_changed_by_appending_to_a_log_that_holds_it() {
        let shared = log(&[1, 2, 3]);
        let mut extended = shared.clone();
        extended.push(4);
        extended.append(log(&[5]));
        assert_eq!(shared, [1, 2, 3]);
        assert_eq!(extended, [1, 2, 3, 4, 5]);
    }

    #[test]
    fn since_gives_what_was_appended_after_an_earlier_state() {
        let mut built = log(&[1]);
        let empty = Log::new();
        let mut from_empty = empty.clone();
        from_empty.append(log(&[9]));
        assert_eq!(from_empty.since(&empty), [9]);
        let earlier = built.clone();
        assert_eq!(built.since(&earlier), [0_u32; 0]);
        built.push(2);
        built.append(log(&[3, 4]));
        let middle = built.clone();
        built.push(5);
        assert_eq!(built.since(&earlier), [2, 3, 4, 5]);
        assert_eq!(built.since(&middle), [5]);
        assert_eq!(earlier, [1]);
    }

    /// A log as deep as a chain of a million appends is read, flattened and dropped without
    /// recursion.
    #[test]
    fn a_deep_log_is_read_and_dropped_without_recursion() {
        let depth = 1_000_000;
        let mut built = Log::new();
        for item in 0..depth {
            let mut level = log(&[item]);
            level.append(built);
            built = level;
        }
        assert_eq!(built.iter().count(), depth as usize);
        assert_eq!(built.iter().next(), Some(&(depth - 1)));
        let copy = built.clone();
        assert_eq!(copy.into_vec().len(), depth as usize);
        drop(built);
    }
}

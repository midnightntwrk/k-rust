//! Seeks: descents that pick subtrees by their summaries, the enumeration of the items a seek
//! wants, iteration over a range of positions, and the item-wise rebuilds that copy only the
//! paths to the items they change.
//!
//! A [`Seek`] is the extension point of the tree: a new query on a collection is one summary
//! field (a count of items with some property, a multiset of what the items mention) and one
//! seek that admits a subtree when that field says the subtree may hold a wanted item. A descent
//! enters only the admitted subtrees, so when the seek admits exactly the subtrees holding a
//! wanted item, it visits the `s` wanted items' ancestors: `O(s log n)` nodes, each read in
//! `O(B)`. Ordered and positional descents ([`search`](Chunked::search), [`get`](Chunked::get),
//! [`partition_point`](Chunked::partition_point)) pick one child per level and are written out
//! on their own.
//!
//! # Rebuilds
//!
//! [`map_where`](Chunked::map_where) applies a function to the items a seek wants, in place, and
//! copies the nodes on the paths to the items it changes; every other node stays shared. The
//! group summary of each copied node is its old one plus the changed items' new group summaries
//! minus their old ones, so the work on a symbolic collection is that of the difference, not of
//! the variables below the node. [`rebuild_where`](Chunked::rebuild_where) does the same for an
//! ordered collection, then takes out the changed items that are no longer in order with their
//! neighbours and puts them back where the order places them.

use std::{
    ops::{Bound, RangeBounds},
    slice,
    sync::Arc,
};

use super::{Chunked, Group, Item, Iter, Node, NodeSummary, Summary, fold_groups};

/// A descent's choice of subtrees and items, by their summaries and positions.
pub(crate) trait Seek<I: Item> {
    /// Whether the subtree whose items start at `position` and have the summary `summary` may
    /// hold an item the seek wants. It must admit every subtree holding such an item; the fewer
    /// other subtrees it admits, the fewer nodes a descent visits.
    fn admits(&self, position: usize, summary: &NodeSummary<I>) -> bool;

    /// Whether the seek wants `item`, at `position`.
    fn wants(&self, position: usize, item: &I) -> bool;
}

impl<I: Item, S: Seek<I>> Seek<I> for &S {
    fn admits(&self, position: usize, summary: &NodeSummary<I>) -> bool {
        (**self).admits(position, summary)
    }

    fn wants(&self, position: usize, item: &I) -> bool {
        (**self).wants(position, item)
    }
}

/// The seek given by a test on a subtree's summary and a test on an item, which ignore
/// positions.
pub(crate) struct Where<A, W> {
    admits: A,
    wants: W,
}

impl<A, W> Where<A, W> {
    pub(crate) fn new(admits: A, wants: W) -> Self {
        Self { admits, wants }
    }
}

impl<I: Item, A, W> Seek<I> for Where<A, W>
where
    A: Fn(&NodeSummary<I>) -> bool,
    W: Fn(&I) -> bool,
{
    fn admits(&self, _position: usize, summary: &NodeSummary<I>) -> bool {
        (self.admits)(summary)
    }

    fn wants(&self, _position: usize, item: &I) -> bool {
        (self.wants)(item)
    }
}

/// The seek for the one item at a position.
pub(crate) struct At(pub(crate) usize);

impl<I: Item> Seek<I> for At {
    fn admits(&self, position: usize, summary: &NodeSummary<I>) -> bool {
        (position..position + summary.count).contains(&self.0)
    }

    fn wants(&self, position: usize, _item: &I) -> bool {
        position == self.0
    }
}

/// The items a seek wants, in order, each with its position.
pub(crate) struct Sought<'a, I: Item, S> {
    seek: S,
    /// The siblings left at each level of the descent, innermost last, with the position of the
    /// first item of the next one.
    nodes: Vec<(slice::Iter<'a, Arc<Node<I>>>, usize)>,
    items: slice::Iter<'a, I>,
    /// The position of the next item of `items`.
    position: usize,
}

impl<'a, I: Item, S: Seek<I>> Iterator for Sought<'a, I, S> {
    type Item = (usize, &'a I);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(item) = self.items.next() {
                let position = self.position;
                self.position += 1;
                if self.seek.wants(position, item) {
                    return Some((position, item));
                }
                continue;
            }
            let (nodes, position) = self.nodes.last_mut()?;
            let Some(node) = nodes.next() else {
                self.nodes.pop();
                continue;
            };
            let start = *position;
            *position += node.summary().count;
            if !self.seek.admits(start, node.summary()) {
                continue;
            }
            match &**node {
                Node::Leaf { items, .. } => {
                    self.items = items.iter();
                    self.position = start;
                }
                Node::Internal { children, .. } => self.nodes.push((children.iter(), start)),
            }
        }
    }
}

/// The difference an item-wise rebuild makes below a node: the group summaries of the items it
/// replaced and of their replacements.
struct Difference<G> {
    removed: G,
    added: G,
}

impl<G: Group> Difference<G> {
    /// `group` changed by the difference. The removed items are among those `group` and the
    /// added ones summarize together, so the subtraction is defined.
    fn apply(&self, group: &G) -> G {
        group.clone().combine(&self.added).subtract(&self.removed)
    }
}

impl<I: Item, const B: usize> Chunked<I, B> {
    /// The items `seek` wants, with their positions, in order. The descent enters only the
    /// subtrees `seek` admits.
    pub(crate) fn seek<S: Seek<I>>(&self, seek: S) -> Sought<'_, I, S> {
        Sought {
            seek,
            nodes: vec![(self.root.as_slice().iter(), 0)],
            items: [].iter(),
            position: 0,
        }
    }

    /// The items at the positions of `range`, from either end. The iterator starts in time
    /// logarithmic in the length.
    pub(crate) fn range(&self, range: impl RangeBounds<usize>) -> Iter<'_, I> {
        let start = match range.start_bound() {
            Bound::Included(&start) => start,
            Bound::Excluded(&start) => start + 1,
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(&end) => end + 1,
            Bound::Excluded(&end) => end,
            Bound::Unbounded => self.len(),
        };
        assert!(
            start <= end && end <= self.len(),
            "a range within the sequence"
        );
        Iter::between(self.root.as_ref(), start, end)
    }

    /// The sequence with each item `seek` wants replaced by `change`'s result, when `change`
    /// returns one (`None` keeps the item). Only the paths to the replaced items are copied.
    pub(crate) fn map_where(
        &self,
        seek: &impl Seek<I>,
        mut change: impl FnMut(&I) -> Option<I>,
    ) -> Self {
        self.map_where_recording(seek, &mut change, &mut Vec::new())
    }

    /// [`map_where`](Self::map_where), also recording the positions of the replaced items, in
    /// order, in `changed`.
    fn map_where_recording(
        &self,
        seek: &impl Seek<I>,
        change: &mut impl FnMut(&I) -> Option<I>,
        changed: &mut Vec<usize>,
    ) -> Self {
        match &self.root {
            Some(root) if seek.admits(0, root.summary()) => {
                match Self::map_node(root, 0, seek, change, changed) {
                    Some((node, _)) => Self {
                        root: Some(Arc::new(node)),
                    },
                    None => self.clone(),
                }
            }
            _ => self.clone(),
        }
    }

    /// `node`, whose first item is at `position`, with the wanted items replaced, and the
    /// difference; `None` when no item changed.
    fn map_node(
        node: &Node<I>,
        position: usize,
        seek: &impl Seek<I>,
        change: &mut impl FnMut(&I) -> Option<I>,
        changed: &mut Vec<usize>,
    ) -> Option<(Node<I>, Difference<I::Group>)> {
        match node {
            Node::Leaf { items, summary } => {
                let mut replaced: Option<Vec<I>> = None;
                let mut removed = Vec::new();
                let mut added = Vec::new();
                for (offset, item) in items.iter().enumerate() {
                    if !seek.wants(position + offset, item) {
                        continue;
                    }
                    if let Some(new) = change(item) {
                        removed.push(item.group());
                        added.push(new.group());
                        replaced.get_or_insert_with(|| items.clone())[offset] = new;
                        changed.push(position + offset);
                    }
                }
                let items = replaced?;
                let difference = Difference {
                    removed: fold_groups(removed),
                    added: fold_groups(added),
                };
                let group = difference.apply(&summary.group);
                Some((Node::leaf_with(items, group), difference))
            }
            Node::Internal {
                height,
                children,
                summary,
            } => {
                let mut replaced: Option<Vec<Arc<Node<I>>>> = None;
                let mut difference = Difference {
                    removed: I::Group::identity(),
                    added: I::Group::identity(),
                };
                let mut start = position;
                for (slot, child) in children.iter().enumerate() {
                    if seek.admits(start, child.summary())
                        && let Some((child, below)) =
                            Self::map_node(child, start, seek, change, changed)
                    {
                        replaced.get_or_insert_with(|| children.clone())[slot] = Arc::new(child);
                        difference.removed = difference.removed.combine(&below.removed);
                        difference.added = difference.added.combine(&below.added);
                    }
                    start += child.summary().count;
                }
                let children = replaced?;
                let group = difference.apply(&summary.group);
                Some((Node::internal_with(*height, children, group), difference))
            }
        }
    }

    /// The sequence with the item at `index`, which is below the length, replaced by `item`.
    /// A path copy.
    pub(crate) fn replace_at(&self, index: usize, item: I) -> Self {
        assert!(index < self.len(), "a replacement within the sequence");
        let mut item = Some(item);
        self.map_where(&At(index), |_| item.take())
    }
}

impl<I: Item + Ord, const B: usize> Chunked<I, B> {
    /// In an ordered sequence, the sequence with each item `seek` wants replaced by `change`'s
    /// result, when it returns one, and in order again.
    ///
    /// The replacements are made in place, copying the paths to them. A replaced item stays
    /// where it is when it is still in order with the unchanged items around it and with the
    /// replaced items kept before it; the others are taken out and put back by a union, which
    /// places them as the order says. So the result is the sorted sequence of the changed items,
    /// and a rebuild that keeps the order (a value of a map changed, not its key) copies only the
    /// paths to the changed items.
    pub(crate) fn rebuild_where(
        &self,
        seek: &impl Seek<I>,
        mut change: impl FnMut(&I) -> Option<I>,
    ) -> Self {
        let mut changed = Vec::new();
        let mut tree = self.map_where_recording(seek, &mut change, &mut changed);
        let out_of_order = tree.out_of_order(&changed);
        let mut moved = Vec::with_capacity(out_of_order.len());
        for &position in out_of_order.iter().rev() {
            let (rest, item) = tree.remove_at(position);
            tree = rest;
            moved.push(item);
        }
        moved.sort();
        tree.union(&Self::from_vec(moved))
    }

    /// Among the positions `changed` (in increasing order) of an otherwise ordered sequence, those
    /// to take out so that the rest is ordered. Each run of adjacent changed positions lies
    /// between two unchanged items (or an end); an item of the run stays when it is not below the
    /// last item kept before it (the unchanged one at first) and not above the unchanged one
    /// after the run.
    fn out_of_order(&self, changed: &[usize]) -> Vec<usize> {
        let mut out = Vec::new();
        let mut run = 0;
        while run < changed.len() {
            let mut end = run + 1;
            while end < changed.len() && changed[end] == changed[end - 1] + 1 {
                end += 1;
            }
            let mut low = changed[run]
                .checked_sub(1)
                .and_then(|before| self.get(before));
            let high = self.get(changed[end - 1] + 1);
            for &position in &changed[run..end] {
                let item = self
                    .get(position)
                    .expect("a changed position is in the sequence");
                if low.is_none_or(|low| low <= item) && high.is_none_or(|high| item <= high) {
                    low = Some(item);
                } else {
                    out.push(position);
                }
            }
            run = end;
        }
        out
    }
}

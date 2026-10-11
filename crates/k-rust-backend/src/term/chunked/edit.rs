//! Persistent edits of a [`Chunked`]: inserting and removing one item, splitting, joining and
//! the union of two ordered sequences.
//!
//! Every edit reads its operands and returns new trees; the operands stay valid and share with
//! the result every node the edit did not change. A one-item edit copies the nodes on the path
//! from the root to the item, and the siblings a rebalancing merges or redistributes, so it
//! copies a number of nodes proportional to the height. Every result satisfies the fill
//! invariant of the module documentation.
//!
//! # Rebalancing
//!
//! A node that overflows (`B + 1` items or children after an insertion, at most `2B` after a
//! join merges two nodes) is cut into two even halves, each holding more than `B / 2`, so at
//! least `MIN_FILL + 1`. A node that underflows after a removal is concatenated with an adjacent
//! sibling and the concatenation is either one node, when it fits in `B`, or two even halves:
//! both outcomes are at least `MIN_FILL`, since the sibling alone holds that many.
//!
//! # Joining
//!
//! A join descends the taller tree's spine on the junction side to the other tree's height and
//! puts the other tree's root beside the node it reaches, when that root is full enough to be a
//! node other than the root; otherwise it concatenates the two nodes, as a removal does. A root
//! is the only node whose fill may be below `MIN_FILL`, so this is the one place a join copies a
//! node of the shorter tree, and the junction then holds no underfilled node: a sequence of
//! removals and joins cannot accumulate small leaves. Nodes both trees keep are shared, and the
//! work is proportional to the difference of the heights, plus one.
//!
//! # Ordered sequences
//!
//! [`insert`](Chunked::insert), [`remove`](Chunked::remove), [`split_at_key`](Chunked::split_at_key)
//! and [`union`](Chunked::union) treat the sequence as an ordered collection: its items are in
//! nondecreasing order of the item's `Ord`, which orders items of different keys by their keys
//! ([`Item`]). They place items by the whole item order, not by the key alone, so a sequence is
//! determined by its items whatever history built it, and two ordered collections holding the
//! same items are equal as sequences. A repeated item or key is kept: an inserted item goes after
//! the items equal to it, and a union keeps both operands' items, so a collection that holds a
//! key twice stays visibly so.

use std::{cmp::Ordering, sync::Arc};

use super::{Chunked, Item, Node};

/// One node, or two adjacent nodes of the same height, that take the place of one node after
/// an edit.
type Replacement<I> = (Arc<Node<I>>, Option<Arc<Node<I>>>);

impl<I: Item> Node<I> {
    /// The number of items of a leaf or of children of an internal node.
    fn width(&self) -> usize {
        match self {
            Self::Leaf { items, .. } => items.len(),
            Self::Internal { children, .. } => children.len(),
        }
    }
}

/// The child of `children` holding position `index` of their concatenation, and the position
/// within it. A position at the end of all of them is placed at the end of the last child.
fn locate<I: Item>(children: &[Arc<Node<I>>], mut index: usize) -> (usize, usize) {
    let last = children.len() - 1;
    for (slot, child) in children.iter().enumerate() {
        let count = child.summary().count;
        if index < count || slot == last {
            return (slot, index);
        }
        index -= count;
    }
    unreachable!("a node has children")
}

/// The root above the replacement of a root: the root itself, or a new root over the two.
fn grow<I: Item>((left, right): Replacement<I>) -> Arc<Node<I>> {
    match right {
        None => left,
        Some(right) => {
            let height = left.height() + 1;
            Arc::new(Node::internal(height, vec![left, right]))
        }
    }
}

impl<I: Item, const B: usize> Chunked<I, B> {
    /// The tree whose root is `node`. Any node is a valid root: a node other than the root
    /// holds at least `MIN_FILL` items or children, and `MIN_FILL` is at least 2. A node of
    /// height 1 over at most `B` items is replaced by the one leaf of its items.
    fn rooted(node: Arc<Node<I>>) -> Self {
        let node = match &*node {
            Node::Internal {
                height: 1,
                children,
                summary,
            } if summary.count <= B => Arc::new(Node::leaf(
                children
                    .iter()
                    .flat_map(|child| match &**child {
                        Node::Leaf { items, .. } => items.iter().cloned(),
                        Node::Internal { .. } => unreachable!("height 1 is over leaves"),
                    })
                    .collect(),
            )),
            _ => node,
        };
        Self { root: Some(node) }
    }

    /// `contents` as one node, or as two even halves when it does not fit in one.
    fn pack<T>(mut contents: Vec<T>, build: impl Fn(Vec<T>) -> Node<I>) -> Replacement<I> {
        debug_assert!(contents.len() <= 2 * B, "at most two nodes' worth");
        if contents.len() <= B {
            return (Arc::new(build(contents)), None);
        }
        let right = contents.split_off(contents.len().div_ceil(2));
        (Arc::new(build(contents)), Some(Arc::new(build(right))))
    }

    /// The contents of two adjacent nodes of the same height, as one node or two.
    fn concatenate(left: &Node<I>, right: &Node<I>) -> Replacement<I> {
        match (left, right) {
            (Node::Leaf { items: l, .. }, Node::Leaf { items: r, .. }) => {
                Self::pack(l.iter().chain(r).cloned().collect(), Node::leaf)
            }
            (
                Node::Internal {
                    height,
                    children: l,
                    ..
                },
                Node::Internal { children: r, .. },
            ) => Self::pack(l.iter().chain(r).cloned().collect(), |children| {
                Node::internal(*height, children)
            }),
            _ => unreachable!("nodes of the same height"),
        }
    }

    /// The tree of the subtrees `nodes`, adjacent and of the same height, in order.
    fn of_nodes(nodes: &[Arc<Node<I>>]) -> Self {
        match nodes {
            [] => Self::new(),
            [node] => Self::rooted(node.clone()),
            [first, ..] => {
                Self::rooted(Arc::new(Node::internal(first.height() + 1, nodes.to_vec())))
            }
        }
    }

    /// The sequence with `item` inserted at position `index`, which is at most the length.
    pub(crate) fn insert_at(&self, index: usize, item: I) -> Self {
        assert!(index <= self.len(), "an insertion within the sequence");
        match &self.root {
            None => Self::rooted(Arc::new(Node::leaf(vec![item]))),
            Some(root) => Self::rooted(grow(Self::insert_into(root, index, item))),
        }
    }

    fn insert_into(node: &Node<I>, index: usize, item: I) -> Replacement<I> {
        match node {
            Node::Leaf { items, .. } => {
                let mut items = items.clone();
                items.insert(index, item);
                Self::pack(items, Node::leaf)
            }
            Node::Internal {
                height, children, ..
            } => {
                let (slot, offset) = locate(children, index);
                let (left, right) = Self::insert_into(&children[slot], offset, item);
                let mut children = children.clone();
                children[slot] = left;
                if let Some(right) = right {
                    children.insert(slot + 1, right);
                }
                Self::pack(children, |children| Node::internal(*height, children))
            }
        }
    }

    /// The sequence without the item at position `index`, which is below the length, and that
    /// item.
    pub(crate) fn remove_at(&self, index: usize) -> (Self, I) {
        assert!(index < self.len(), "a removal within the sequence");
        let root = self.root.as_ref().expect("a nonempty sequence has a root");
        let (root, item) = Self::remove_from(root, index);
        let tree = match root {
            Node::Leaf { ref items, .. } if items.is_empty() => Self::new(),
            Node::Internal { mut children, .. } if children.len() == 1 => {
                Self::rooted(children.pop().expect("one child"))
            }
            root => Self::rooted(Arc::new(root)),
        };
        (tree, item)
    }

    /// `node` without the item at `index`, which may hold one item or child fewer than
    /// `MIN_FILL`, and that item.
    fn remove_from(node: &Node<I>, index: usize) -> (Node<I>, I) {
        match node {
            Node::Leaf { items, .. } => {
                let mut items = items.clone();
                let item = items.remove(index);
                (Node::leaf(items), item)
            }
            Node::Internal {
                height, children, ..
            } => {
                let (slot, offset) = locate(children, index);
                let (child, item) = Self::remove_from(&children[slot], offset);
                let mut children = children.clone();
                if child.width() >= Self::MIN_FILL {
                    children[slot] = Arc::new(child);
                } else {
                    // An internal node has at least two children, so `child` has a sibling;
                    // `left` is the first of the two adjacent nodes concatenated.
                    let left = if slot + 1 < children.len() {
                        slot
                    } else {
                        slot - 1
                    };
                    let (first, second) = if left == slot {
                        (&child, &*children[slot + 1])
                    } else {
                        (&*children[left], &child)
                    };
                    let (one, two) = Self::concatenate(first, second);
                    children.splice(left..left + 2, std::iter::once(one).chain(two));
                }
                (Node::internal(*height, children), item)
            }
        }
    }

    /// The items of `self` followed by those of `other`.
    pub(crate) fn join(&self, other: &Self) -> Self {
        match (&self.root, &other.root) {
            (None, _) => other.clone(),
            (_, None) => self.clone(),
            (Some(left), Some(right)) => Self::rooted(grow(Self::join_nodes(left, right))),
        }
    }

    /// The items below `left` followed by those below `right`, as nodes of the taller one's
    /// height. Either may be underfilled (a root); every node below them is not.
    fn join_nodes(left: &Arc<Node<I>>, right: &Arc<Node<I>>) -> Replacement<I> {
        match left.height().cmp(&right.height()) {
            Ordering::Equal => {
                if left.width() >= Self::MIN_FILL && right.width() >= Self::MIN_FILL {
                    (left.clone(), Some(right.clone()))
                } else {
                    Self::concatenate(left, right)
                }
            }
            Ordering::Greater => {
                let Node::Internal {
                    height, children, ..
                } = &**left
                else {
                    unreachable!("the taller node is internal")
                };
                let last = children.len() - 1;
                let (one, two) = Self::join_nodes(&children[last], right);
                let mut children = children.clone();
                children[last] = one;
                children.extend(two);
                Self::pack(children, |children| Node::internal(*height, children))
            }
            Ordering::Less => {
                let Node::Internal {
                    height, children, ..
                } = &**right
                else {
                    unreachable!("the taller node is internal")
                };
                let (one, two) = Self::join_nodes(left, &children[0]);
                let mut children = children.clone();
                children[0] = one;
                if let Some(two) = two {
                    children.insert(1, two);
                }
                Self::pack(children, |children| Node::internal(*height, children))
            }
        }
    }

    /// The first `index` items and the rest; `index` is at most the length.
    pub(crate) fn split_at(&self, index: usize) -> (Self, Self) {
        assert!(index <= self.len(), "a split within the sequence");
        match &self.root {
            None => (Self::new(), Self::new()),
            Some(root) => Self::split_node(root, index),
        }
    }

    fn split_node(node: &Arc<Node<I>>, index: usize) -> (Self, Self) {
        if index == 0 {
            return (Self::new(), Self::rooted(node.clone()));
        }
        if index == node.summary().count {
            return (Self::rooted(node.clone()), Self::new());
        }
        match &**node {
            Node::Leaf { items, .. } => (
                Self::rooted(Arc::new(Node::leaf(items[..index].to_vec()))),
                Self::rooted(Arc::new(Node::leaf(items[index..].to_vec()))),
            ),
            Node::Internal { children, .. } => {
                let (slot, offset) = locate(children, index);
                let (left, right) = Self::split_node(&children[slot], offset);
                (
                    Self::of_nodes(&children[..slot]).join(&left),
                    right.join(&Self::of_nodes(&children[slot + 1..])),
                )
            }
        }
    }

    /// The number of leading items for which `before` holds, when it holds for a prefix of the
    /// sequence and for no item after it. Logarithmic in the length.
    pub(crate) fn partition_point(&self, mut before: impl FnMut(&I) -> bool) -> usize {
        let Some(mut node) = self.root.as_deref() else {
            return 0;
        };
        let mut position = 0;
        loop {
            match node {
                Node::Internal { children, .. } => {
                    // Every child before the first whose last item fails `before` lies wholly
                    // in the prefix.
                    let slot = children.partition_point(|child| {
                        before(child.summary().last.as_ref().expect("a node has items"))
                    });
                    position += children[..slot]
                        .iter()
                        .map(|child| child.summary().count)
                        .sum::<usize>();
                    match children.get(slot) {
                        Some(child) => node = child,
                        None => return position,
                    }
                }
                Node::Leaf { items, .. } => {
                    return position + items.partition_point(|item| before(item));
                }
            }
        }
    }

    /// In an ordered sequence, the items whose key is below `key` and the rest.
    pub(crate) fn split_at_key(&self, key: &I::Key) -> (Self, Self) {
        self.split_at(self.partition_point(|item| item.key() < key))
    }
}

impl<I: Item + Ord, const B: usize> Chunked<I, B> {
    /// In an ordered sequence, the sequence with `item` added after the items not above it.
    pub(crate) fn insert(&self, item: I) -> Self {
        self.insert_at(self.partition_point(|other| *other <= item), item)
    }

    /// In an ordered sequence, the sequence without one item equal to `item`; `None` when it
    /// holds none.
    pub(crate) fn remove(&self, item: &I) -> Option<Self> {
        let index = self.partition_point(|other| other < item);
        (self.get(index) == Some(item)).then(|| self.remove_at(index).0)
    }

    /// The ordered sequence of the items of the two ordered sequences, each kept as often as
    /// the two hold it together.
    ///
    /// The taller tree's root is the pivot: the other tree is cut at the first item of each of
    /// its children but the first, each child is united with its part, and the results are
    /// joined in order. A child whose part is empty is kept as it is, and a run of such children
    /// is joined as one subtree over them, so the union visits only the nodes of the taller tree
    /// whose range holds items of the other, and a union with a few items copies about what
    /// inserting them one by one would.
    pub(crate) fn union(&self, other: &Self) -> Self {
        match (&self.root, &other.root) {
            (None, _) => other.clone(),
            (_, None) => self.clone(),
            (Some(left), Some(right)) => {
                if left.height() >= right.height() {
                    Self::union_node(left, other)
                } else {
                    Self::union_node(right, self)
                }
            }
        }
    }

    /// The union of the subtree `node` with `other`, no taller than it.
    fn union_node(node: &Arc<Node<I>>, other: &Self) -> Self {
        if other.is_empty() {
            return Self::rooted(node.clone());
        }
        match &**node {
            // `other` is a leaf too: merge the two runs.
            Node::Leaf { items, .. } => {
                let mut merged = Vec::with_capacity(items.len() + other.len());
                let mut mine = items.iter().peekable();
                for theirs in other.iter() {
                    while let Some(item) = mine.next_if(|item| *item <= theirs) {
                        merged.push(item.clone());
                    }
                    merged.push(theirs.clone());
                }
                merged.extend(mine.cloned());
                Self::from_vec(merged)
            }
            Node::Internal { children, .. } => {
                let mut rest = other.clone();
                let mut united = Self::new();
                // The children from `kept` on are, so far, united with nothing; they are joined
                // as one run, without copying them.
                let mut kept = 0;
                for (slot, child) in children.iter().enumerate() {
                    if rest.is_empty() {
                        break;
                    }
                    let part = match children.get(slot + 1) {
                        Some(next) => {
                            let bound = next.summary().first.as_ref().expect("a node has items");
                            let (part, after) =
                                rest.split_at(rest.partition_point(|item| item < bound));
                            rest = after;
                            part
                        }
                        None => std::mem::take(&mut rest),
                    };
                    let piece = match &part.root {
                        None => continue,
                        Some(root) if root.height() > child.height() => {
                            Self::union_node(root, &Self::rooted(child.clone()))
                        }
                        Some(_) => Self::union_node(child, &part),
                    };
                    united = united
                        .join(&Self::of_nodes(&children[kept..slot]))
                        .join(&piece);
                    kept = slot + 1;
                }
                united.join(&Self::of_nodes(&children[kept..]))
            }
        }
    }
}

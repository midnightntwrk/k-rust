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
//!
//! # Group summaries
//!
//! A copied node's group summary ([`Group`]) is the summary of the node it replaces changed by
//! the edit's difference: an insertion adds the item's, a removal subtracts it, and a join adds
//! the shorter tree's summary to each node of the taller one's spine that it copies, so each
//! costs what the difference costs at each copied node, not what lies below it. A node that
//! rebalancing creates is the exception: when a node splits in two, the lighter half's summary is
//! folded from its children and the heavier half's is the rest; when two nodes are concatenated,
//! the lighter one's summary is added to the heavier one's. Under the fill invariant, a node made by
//! a split or a concatenation is away from both bounds, so in a linear history it is split or
//! concatenated again only after a number of edits below it proportional to its width, and that
//! work is shared among them.
//!
//! A split and a union keep group summaries by difference too. A split builds, for each side,
//! one node per level on the path to the cut, which replaces the node the path passes through:
//! the lighter side's summary is added up from the children it keeps and the side built below,
//! and the heavier side's is the replaced node's without it, so a level costs the variables of
//! its lighter side, and a cut near either end costs the variables of the items it cuts away at
//! each level. A union copies the nodes of the taller tree whose range receives items of the
//! other, and each copy's summary is the replaced node's plus that of the items added below
//! it. A node that a union's overflow cuts into several gets its summary as a split in two
//! does: the heaviest of them by subtraction, the others folded.

use std::{cmp::Ordering, sync::Arc};

use super::{Chunked, Group, Item, Node, Summary, even_parts, fold_groups};

/// One node, or two adjacent nodes of the same height, that take the place of one node after
/// an edit.
type Replacement<I> = (Arc<Node<I>>, Option<Arc<Node<I>>>);

/// The roots of the two sides of a split node, `None` for an empty side.
type Sides<I> = (Option<Arc<Node<I>>>, Option<Arc<Node<I>>>);

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

/// The root above the replacement of a root, whose items have the group summary `group()`: the
/// root itself, or a new root over the two. The group summary is computed only for a new root,
/// since the replacement's nodes carry their own.
fn grow<I: Item>((left, right): Replacement<I>, group: impl FnOnce() -> I::Group) -> Arc<Node<I>> {
    match right {
        None => left,
        Some(right) => {
            let height = left.height() + 1;
            Arc::new(Node::internal_with(height, vec![left, right], group()))
        }
    }
}

/// The group summary of a child, a cheap clone (a multiset is a shared tree).
fn child_group<I: Item>(child: &Arc<Node<I>>) -> I::Group {
    child.summary().group.clone()
}

/// The persistent edits of the tree (module documentation).
///
/// ```toml algorithm-site
/// id = "backend.term.chunked"
/// role = "part"
/// sites = ["Chunked::insert_at", "Chunked::remove_at", "Chunked::join", "Chunked::split_at", "Chunked::split_at_key", "Chunked::insert", "Chunked::remove", "Chunked::union", "Chunked::cut"]
/// ```
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
                ..
            } if summary.count <= B => Arc::new(Node::leaf_with(
                children
                    .iter()
                    .flat_map(|child| match &**child {
                        Node::Leaf { items, .. } => items.iter().cloned(),
                        Node::Internal { .. } => unreachable!("height 1 is over leaves"),
                    })
                    .collect(),
                summary.group.clone(),
            )),
            _ => node,
        };
        Self { root: Some(node) }
    }

    /// The group summaries of two adjacent parts of contents whose group summary is `whole`,
    /// from the group summaries of each part's contents: the lighter part's is folded from its
    /// contents', and the heavier's is the rest of `whole`, so the work is the lighter part's.
    fn divide(whole: I::Group, left: Vec<I::Group>, right: Vec<I::Group>) -> (I::Group, I::Group) {
        let weight = |groups: &[I::Group]| groups.iter().map(Group::weight).sum::<usize>();
        if weight(&left) <= weight(&right) {
            let left = fold_groups(left);
            let right = whole.subtract(&left);
            (left, right)
        } else {
            let right = fold_groups(right);
            (whole.subtract(&right), right)
        }
    }

    /// `contents`, whose items have the group summary `group`, as one node, or as two even
    /// halves when it does not fit in one. The lighter half's group summary is folded from its
    /// contents' (`group_of`), and the heavier half's is the rest of `group`.
    fn pack<T>(
        mut contents: Vec<T>,
        group: I::Group,
        group_of: impl Fn(&T) -> I::Group,
        build: impl Fn(Vec<T>, I::Group) -> Node<I>,
    ) -> Replacement<I> {
        debug_assert!(contents.len() <= 2 * B, "at most two nodes' worth");
        if contents.len() <= B {
            return (Arc::new(build(contents, group)), None);
        }
        let right = contents.split_off(contents.len().div_ceil(2));
        let (left_group, right_group) = Self::divide(
            group,
            contents.iter().map(&group_of).collect(),
            right.iter().map(&group_of).collect(),
        );
        (
            Arc::new(build(contents, left_group)),
            Some(Arc::new(build(right, right_group))),
        )
    }

    /// `contents`, whose items have the group summary `group`, as one node when they fit in
    /// one, otherwise cut into nodes strictly between the fill bounds, as even as possible. The
    /// heaviest node's group summary is the rest of `group` and every other one's is folded from
    /// its contents' (`group_of`), so the work is that of all the nodes but the heaviest: the
    /// nodes a node's overflow creates, as [`pack`](Self::pack) does for two.
    fn cut<T>(
        contents: Vec<T>,
        group: I::Group,
        group_of: impl Fn(&T) -> I::Group,
        build: impl Fn(Vec<T>, I::Group) -> Node<I>,
    ) -> Vec<Arc<Node<I>>> {
        if contents.len() <= B {
            return vec![Arc::new(build(contents, group))];
        }
        let mut contents = contents.into_iter();
        let parts: Vec<Vec<T>> = even_parts(contents.len(), B, Self::MIN_FILL, Self::FILL_TARGET)
            .map(|size| contents.by_ref().take(size).collect())
            .collect();
        let groups: Vec<Vec<I::Group>> = parts
            .iter()
            .map(|part| part.iter().map(&group_of).collect())
            .collect();
        let weight = |groups: &Vec<I::Group>| groups.iter().map(Group::weight).sum::<usize>();
        let heaviest = (0..groups.len())
            .max_by_key(|&part| weight(&groups[part]))
            .expect("more than one part");
        let mut rest = group;
        let mut folded: Vec<Option<I::Group>> = groups
            .into_iter()
            .enumerate()
            .map(|(part, groups)| {
                (part != heaviest).then(|| {
                    let group = fold_groups(groups);
                    rest = std::mem::replace(&mut rest, I::Group::identity()).subtract(&group);
                    group
                })
            })
            .collect();
        folded[heaviest] = Some(rest);
        parts
            .into_iter()
            .zip(folded)
            .map(|(part, group)| Arc::new(build(part, group.expect("every part's group"))))
            .collect()
    }

    /// The items of a leaf, with the group summary `group`, as one leaf or two.
    fn pack_items(items: Vec<I>, group: I::Group) -> Replacement<I> {
        Self::pack(items, group, Item::group, Node::leaf_with)
    }

    /// The children of an internal node of height `height`, with the group summary `group`, as
    /// one node or two.
    fn pack_children(
        height: usize,
        children: Vec<Arc<Node<I>>>,
        group: I::Group,
    ) -> Replacement<I> {
        Self::pack(children, group, child_group, |children, group| {
            Node::internal_with(height, children, group)
        })
    }

    /// The contents of two adjacent nodes of the same height, as one node or two.
    fn concatenate(left: &Node<I>, right: &Node<I>) -> Replacement<I> {
        let group = left.summary().group.clone().combine(&right.summary().group);
        match (left, right) {
            (Node::Leaf { items: l, .. }, Node::Leaf { items: r, .. }) => {
                Self::pack_items(l.iter().chain(r).cloned().collect(), group)
            }
            (
                Node::Internal {
                    height,
                    children: l,
                    ..
                },
                Node::Internal { children: r, .. },
            ) => Self::pack_children(*height, l.iter().chain(r).cloned().collect(), group),
            _ => unreachable!("nodes of the same height"),
        }
    }

    /// The tree over `nodes`, adjacent nodes of height `height`, each holding between
    /// `MIN_FILL` and `B` items or children when there are several, whose items have the group
    /// summary `group`: the one node, or levels of new nodes above them, cut as
    /// [`cut`](Self::cut) cuts, whose root gets `group`.
    fn over(mut height: usize, mut nodes: Vec<Arc<Node<I>>>, group: I::Group) -> Self {
        while nodes.len() > 1 {
            height += 1;
            let level = height;
            nodes = Self::cut(nodes, group.clone(), child_group, |children, group| {
                Node::internal_with(level, children, group)
            });
        }
        Self::rooted(nodes.pop().expect("a node"))
    }

    /// The sequence with `item` inserted at position `index`, which is at most the length.
    pub(crate) fn insert_at(&self, index: usize, item: I) -> Self {
        assert!(index <= self.len(), "an insertion within the sequence");
        match &self.root {
            None => Self::rooted(Arc::new(Node::leaf(vec![item]))),
            Some(root) => {
                let added = item.group();
                let replacement = Self::insert_into(root, index, item, &added);
                Self::rooted(grow(replacement, || {
                    root.summary().group.clone().combine(&added)
                }))
            }
        }
    }

    /// `node` with `item`, whose group summary is `added`, inserted at `index`. Every node on
    /// the path gains `added` in its group summary.
    fn insert_into(node: &Node<I>, index: usize, item: I, added: &I::Group) -> Replacement<I> {
        let group = node.summary().group.clone().combine(added);
        match node {
            Node::Leaf { items, .. } => {
                let mut items = items.clone();
                items.insert(index, item);
                Self::pack_items(items, group)
            }
            Node::Internal {
                height, children, ..
            } => {
                let (slot, offset) = locate(children, index);
                let (left, right) = Self::insert_into(&children[slot], offset, item, added);
                let mut children = children.clone();
                children[slot] = left;
                if let Some(right) = right {
                    children.insert(slot + 1, right);
                }
                Self::pack_children(*height, children, group)
            }
        }
    }

    /// The sequence without the item at position `index`, which is below the length, and that
    /// item.
    pub(crate) fn remove_at(&self, index: usize) -> (Self, I) {
        assert!(index < self.len(), "a removal within the sequence");
        let root = self.root.as_ref().expect("a nonempty sequence has a root");
        let (root, item, _) = Self::remove_from(root, index);
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
    /// `MIN_FILL`, that item, and its group summary, which every node on the path loses.
    fn remove_from(node: &Node<I>, index: usize) -> (Node<I>, I, I::Group) {
        match node {
            Node::Leaf { items, summary, .. } => {
                let mut items = items.clone();
                let item = items.remove(index);
                let removed = item.group();
                let group = summary.group.clone().subtract(&removed);
                (Node::leaf_with(items, group), item, removed)
            }
            Node::Internal {
                height,
                children,
                summary,
                ..
            } => {
                let (slot, offset) = locate(children, index);
                let (child, item, removed) = Self::remove_from(&children[slot], offset);
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
                let group = summary.group.clone().subtract(&removed);
                (Node::internal_with(*height, children, group), item, removed)
            }
        }
    }

    /// The items of `self` followed by those of `other`.
    pub(crate) fn join(&self, other: &Self) -> Self {
        match (&self.root, &other.root) {
            (None, _) => other.clone(),
            (_, None) => self.clone(),
            (Some(left), Some(right)) => {
                let group = || left.summary().group.clone().combine(&right.summary().group);
                Self::rooted(grow(Self::join_nodes(left, right), group))
            }
        }
    }

    /// The items below `left` followed by those below `right`, as nodes of the taller one's
    /// height. Either may be underfilled (a root); every node below them is not. Each node of
    /// the taller one's spine that is copied gains the shorter one's group summary.
    fn join_nodes(left: &Arc<Node<I>>, right: &Arc<Node<I>>) -> Replacement<I> {
        let group = || left.summary().group.clone().combine(&right.summary().group);
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
                Self::pack_children(*height, children, group())
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
                Self::pack_children(*height, children, group())
            }
        }
    }

    /// The first `index` items and the rest; `index` is at most the length.
    pub(crate) fn split_at(&self, index: usize) -> (Self, Self) {
        assert!(index <= self.len(), "a split within the sequence");
        let root = match &self.root {
            Some(root) if 0 < index && index < root.summary().count => root,
            _ if index == 0 => return (Self::new(), self.clone()),
            _ => return (self.clone(), Self::new()),
        };
        let (left, right) = Self::split_node(root, index);
        let side = |node: Option<Arc<Node<I>>>| node.map_or_else(Self::new, Self::rooted);
        (side(left), side(right))
    }

    /// The roots of the trees of the items below `node` before `index` and from it, where
    /// `index` lies strictly inside `node`.
    ///
    /// Only the nodes on the path to the cut are built: at each level, the node the path passes
    /// through gives a node to each side, made of the children before (after) the cut and the
    /// side built below, which is attached as a child when it is a node of the children's height
    /// with enough of them, and otherwise joined to the adjacent child. A side with nothing but
    /// what was built below is that. The two new nodes' group summaries are obtained from the
    /// node they replace ([`divide`](Self::divide)): the lighter side's is added up from its
    /// children's and the heavier side's is the node's without it, so a level costs the variables
    /// of its lighter side, and a cut near either end costs the few items cut away.
    fn split_node(node: &Arc<Node<I>>, index: usize) -> Sides<I> {
        match &**node {
            Node::Leaf { items, summary, .. } => {
                let (left, right) = items.split_at(index);
                let (left_group, right_group) = Self::divide(
                    summary.group.clone(),
                    left.iter().map(Item::group).collect(),
                    right.iter().map(Item::group).collect(),
                );
                (
                    Some(Arc::new(Node::leaf_with(left.to_vec(), left_group))),
                    Some(Arc::new(Node::leaf_with(right.to_vec(), right_group))),
                )
            }
            Node::Internal {
                height,
                children,
                summary,
                ..
            } => {
                let (slot, offset) = locate(children, index);
                let (before, after) = if offset == 0 {
                    (None, Some(children[slot].clone()))
                } else {
                    Self::split_node(&children[slot], offset)
                };
                let (run_before, run_after) = (&children[..slot], &children[slot + 1..]);
                let (left_group, right_group) = Self::divide(
                    summary.group.clone(),
                    run_before.iter().chain(&before).map(child_group).collect(),
                    after.iter().chain(run_after).map(child_group).collect(),
                );
                (
                    Self::side(*height, run_before, before, true, left_group),
                    Self::side(*height, run_after, after, false, right_group),
                )
            }
        }
    }

    /// One side of a split node of height `height`: the children `run`, which lie beside the
    /// cut, and the side `piece` built below, after the run when `piece_last` and before it
    /// otherwise; `group` is the summary of all their items. `piece` is the root of a tree no
    /// taller than the run's children; it becomes one of the children when it is as tall as them
    /// and holds at least `MIN_FILL` items or children, and is otherwise joined to the child
    /// beside it, which copies that child's spine down to `piece`'s height, each copied node
    /// gaining `piece`'s group summary. A side of one child is that child.
    fn side(
        height: usize,
        run: &[Arc<Node<I>>],
        piece: Option<Arc<Node<I>>>,
        piece_last: bool,
        group: I::Group,
    ) -> Option<Arc<Node<I>>> {
        let mut children = run.to_vec();
        if let Some(piece) = piece {
            if children.is_empty() {
                return Some(piece);
            }
            if piece.height() + 1 == height && piece.width() >= Self::MIN_FILL {
                let at = if piece_last { children.len() } else { 0 };
                children.insert(at, piece);
            } else if piece_last {
                let last = children.pop().expect("a nonempty run");
                let (one, two) = Self::join_nodes(&last, &piece);
                children.push(one);
                children.extend(two);
            } else {
                let (one, two) = Self::join_nodes(&piece, &children[0]);
                children.splice(0..1, std::iter::once(one).chain(two));
            }
        }
        match children.len() {
            0 => None,
            1 => children.pop(),
            _ => Some(Arc::new(Node::internal_with(height, children, group))),
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
    /// The taller tree is copied and the other's items are added to it: the other tree is cut
    /// at the first item of each child of the taller root but the first, and each child is
    /// united with its part, down to the leaves, where the items are merged. A child whose part
    /// is empty is kept as it is, so the union copies only the nodes of the taller tree whose
    /// range holds items of the other: for trees of `n` and `m` items, `O(m log(n/m + 1))`
    /// nodes. Each copied node's group summary is the one of the node it replaces plus that of
    /// the items added below it; a node that overflows is cut as [`cut`](Self::cut) cuts.
    pub(crate) fn union(&self, other: &Self) -> Self {
        match (&self.root, &other.root) {
            (None, _) => other.clone(),
            (_, None) => self.clone(),
            (Some(left), Some(right)) => {
                let (pivot, added) = if left.height() >= right.height() {
                    (left, other)
                } else {
                    (right, self)
                };
                let (nodes, group) = Self::union_node(pivot, added);
                Self::over(pivot.height(), nodes, group)
            }
        }
    }

    /// The nodes of `node`'s height holding the items below `node` and those of `other`, which
    /// is no taller than `node`, and the group summary of all of them. When `other` is empty
    /// that is `node` itself; otherwise it is `node`'s copy, holding at least as many items or
    /// children, or the nodes its overflow is cut into, each between the fill bounds.
    fn union_node(node: &Arc<Node<I>>, other: &Self) -> (Vec<Arc<Node<I>>>, I::Group) {
        let Some(added) = other.summary() else {
            return (vec![node.clone()], node.summary().group.clone());
        };
        let group = node.summary().group.clone().combine(&added.group);
        let nodes = match &**node {
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
                Self::cut(merged, group.clone(), Item::group, Node::leaf_with)
            }
            Node::Internal {
                height, children, ..
            } => {
                let mut rest = other.clone();
                let mut united = Vec::with_capacity(children.len());
                for (slot, child) in children.iter().enumerate() {
                    if rest.is_empty() {
                        united.extend(children[slot..].iter().cloned());
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
                    match &part.root {
                        None => united.push(child.clone()),
                        // The part is as tall as `node`: it is the one copied, and its nodes'
                        // children take the child's place.
                        Some(root) if root.height() == *height => {
                            let child = Self {
                                root: Some(child.clone()),
                            };
                            for node in Self::union_node(root, &child).0 {
                                let Node::Internal { children, .. } = &*node else {
                                    unreachable!("a node as tall as an internal node")
                                };
                                united.extend(children.iter().cloned());
                            }
                        }
                        Some(_) => united.extend(Self::union_node(child, &part).0),
                    }
                }
                Self::cut(united, group.clone(), child_group, |children, group| {
                    Node::internal_with(*height, children, group)
                })
            }
        };
        (nodes, group)
    }
}

/// The keyed edits of a sequence ordered by key with one item per key and no group summaries:
/// a [`Multiset`](super::multiset::Multiset)'s entries.
///
/// A batch of `k` edits descends once: each internal node splits the batch by its children's
/// first keys, so a node is copied once whatever number of the batch's keys fall in its range,
/// and a node whose range receives none is shared. A batch applied one edit at a time copies a
/// path per edit instead, `k` copies of the nodes the batch's keys share, which for keys that
/// fall together (variables named alike, a collection's own) is most of the work.
///
/// ```toml algorithm-site
/// id = "backend.term.chunked"
/// role = "part"
/// sites = ["Chunked::add_by_key", "Chunked::reduce_by_key"]
/// ```
impl<I: Item<Group = ()>, const B: usize> Chunked<I, B> {
    /// The part of `batch`, ordered by key, that falls in `children[slot]`'s range: the keys
    /// below the next child's first key, all of the rest for the last child. `batch` keeps what
    /// is left.
    fn part_for<'b>(children: &[Arc<Node<I>>], slot: usize, batch: &mut &'b [I]) -> &'b [I] {
        let part = match children.get(slot + 1) {
            Some(next) => {
                let bound = next
                    .summary()
                    .first
                    .as_ref()
                    .expect("a node has items")
                    .key();
                batch.partition_point(|item| item.key() < bound)
            }
            None => batch.len(),
        };
        let (part, rest) = batch.split_at(part);
        *batch = rest;
        part
    }

    /// The sequence with the items of `added`, ordered by key with one per key, put in: an item
    /// whose key the sequence holds is merged into that item by `merge(held, added)`, the others
    /// are inserted in order. Each node whose range receives an item is copied once, and one
    /// that overflows is cut as [`cut`](Self::cut) cuts.
    pub(crate) fn add_by_key(&self, added: &[I], merge: impl Fn(&I, &I) -> I) -> Self {
        match &self.root {
            _ if added.is_empty() => self.clone(),
            None => Self::from_vec(added.to_vec()),
            Some(root) => Self::over(root.height(), Self::add_into(root, added, &merge), ()),
        }
    }

    /// The nodes of `node`'s height, each between the fill bounds when there are several,
    /// holding `node`'s items with `added`'s put in.
    fn add_into(
        node: &Arc<Node<I>>,
        added: &[I],
        merge: &impl Fn(&I, &I) -> I,
    ) -> Vec<Arc<Node<I>>> {
        match &**node {
            Node::Leaf { items, .. } => {
                let mut merged = Vec::with_capacity(items.len() + added.len());
                let mut added = added.iter().peekable();
                for item in items {
                    while let Some(before) = added.next_if(|new| new.key() < item.key()) {
                        merged.push(before.clone());
                    }
                    merged.push(match added.next_if(|new| new.key() == item.key()) {
                        Some(same) => merge(item, same),
                        None => item.clone(),
                    });
                }
                merged.extend(added.cloned());
                Self::cut(merged, (), Item::group, Node::leaf_with)
            }
            Node::Internal {
                height, children, ..
            } => {
                let mut batch = added;
                let mut united = Vec::with_capacity(children.len());
                for (slot, child) in children.iter().enumerate() {
                    let part = Self::part_for(children, slot, &mut batch);
                    if part.is_empty() {
                        united.push(child.clone());
                    } else {
                        united.extend(Self::add_into(child, part, merge));
                    }
                }
                Self::cut(united, (), child_group, |children, ()| {
                    Node::internal_with(*height, children, ())
                })
            }
        }
    }

    /// The sequence with the item of each key of `reduced`, ordered by key with one per key,
    /// replaced by `reduce(held, reduced)`, or removed when that is `None`. The sequence holds
    /// every key of `reduced`. Each node whose range holds one of the keys is copied once; a
    /// node left below the fill minimum is joined to an adjacent sibling, as
    /// [`join`](Self::join) joins two trees.
    pub(crate) fn reduce_by_key(
        &self,
        reduced: &[I],
        reduce: impl Fn(&I, &I) -> Option<I>,
    ) -> Self {
        match &self.root {
            _ if reduced.is_empty() => self.clone(),
            None => panic!("a reduction names only keys the sequence holds"),
            Some(root) => match Self::reduce_in(root, reduced, &reduce) {
                None => Self::new(),
                Some(root) => Self::rooted(root),
            },
        }
    }

    /// `node` with `reduced`'s items reduced: `None` when no item is left, otherwise one node
    /// of `node`'s height or lower, which may hold fewer than `MIN_FILL` items or children while
    /// every node below it holds at least that many.
    ///
    /// The children left are taken in order and a child that is lower than its siblings or
    /// below the minimum is joined to the one before it (or the one after it, for the first):
    /// a join keeps the taller or full node's width, so only the last node taken may be short,
    /// and it is joined to the one before it at the end. Two full nodes a join of two short ones
    /// returns become one node a level up, itself short. A node left with one child is replaced
    /// by that child, one level lower, which its parent joins in turn.
    fn reduce_in(
        node: &Arc<Node<I>>,
        reduced: &[I],
        reduce: &impl Fn(&I, &I) -> Option<I>,
    ) -> Option<Arc<Node<I>>> {
        match &**node {
            Node::Leaf { items, .. } => {
                let mut left = Vec::with_capacity(items.len());
                let mut reduced = reduced.iter().peekable();
                for item in items {
                    match reduced.next_if(|old| old.key() == item.key()) {
                        Some(old) => left.extend(reduce(item, old)),
                        None => left.push(item.clone()),
                    }
                }
                assert!(
                    reduced.next().is_none(),
                    "a reduction names only keys the sequence holds"
                );
                (!left.is_empty()).then(|| Arc::new(Node::leaf_with(left, ())))
            }
            Node::Internal {
                height, children, ..
            } => {
                let level = height - 1;
                let short =
                    |node: &Arc<Node<I>>| node.height() < level || node.width() < Self::MIN_FILL;
                // Two nodes a join returns below the children's level are full: they become
                // the two children of one node a level up, short again.
                let join_last = |kept: &mut Vec<Arc<Node<I>>>, next: &Arc<Node<I>>| {
                    let last = kept.pop().expect("a node to join");
                    match Self::join_nodes(&last, next) {
                        (one, Some(two)) if one.height() < level => {
                            let height = one.height() + 1;
                            kept.push(Arc::new(Node::internal_with(height, vec![one, two], ())));
                        }
                        (one, two) => {
                            kept.push(one);
                            kept.extend(two);
                        }
                    }
                };
                let mut batch = reduced;
                let mut kept: Vec<Arc<Node<I>>> = Vec::with_capacity(children.len());
                for (slot, child) in children.iter().enumerate() {
                    let part = Self::part_for(children, slot, &mut batch);
                    let child = if part.is_empty() {
                        child.clone()
                    } else {
                        match Self::reduce_in(child, part, reduce) {
                            Some(child) => child,
                            None => continue,
                        }
                    };
                    match kept.last() {
                        Some(last) if short(last) || short(&child) => join_last(&mut kept, &child),
                        _ => kept.push(child),
                    }
                }
                if kept.len() > 1 && kept.last().is_some_and(short) {
                    let last = kept.pop().expect("a last node");
                    join_last(&mut kept, &last);
                }
                match kept.len() {
                    0 | 1 => kept.pop(),
                    _ => Some(Arc::new(Node::internal_with(*height, kept, ()))),
                }
            }
        }
    }
}

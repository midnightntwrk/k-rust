//! Origin sets: the ordered, duplicate-free link lists of receipts, held as an immutable DAG.
//!
//! A receipt's origin set is the first-occurrence ordered union of the sets and links it derives
//! from. That union is associative and idempotent and satisfies `x · y · x = x · y` (it is the
//! free left-regular band on links), so a set can name the sets it unites instead of copying
//! their links: a node of an [`OriginSet`] is an ordered list of parts, each a link or another
//! set, and it denotes `dedup₁(concat(parts))`, where a `Set` part contributes its own denotation
//! and `dedup₁` keeps the first occurrence of each link. Naming a set costs one part however many
//! links it denotes, so the sets a pass builds for a deep or wide term cost constant memory per
//! node, where materialised lists cost the size of everything above or around the node.
//!
//! Every node satisfies, by construction, the local rules that make its parts a normal form: it
//! has at least one part, no `Set` part names the empty set, no link is repeated, no set
//! allocation is named twice, and a node that would consist of one `Set` part alone is that set.
//! Each rule removes only parts that add no link, so the denotation is unchanged; together they
//! make the empty set the only node without parts, so emptiness is decided in constant time.
//!
//! Nodes are immutable and shared: a set built at one pass keeps denoting what it denoted then,
//! whatever later passes do to the term it was built for. Flattening ([`OriginSet::links`]),
//! comparison, formatting and dropping are iterative, so a chain of sets of any length is
//! handled on any thread.

use std::{
    collections::HashSet,
    fmt,
    hash::{BuildHasherDefault, Hash},
    sync::Arc,
};

use k_rust_kore::measure::{self, Counter};
use rustc_hash::FxHasher;

use super::ProvenanceLink;

type FxHashSet<T> = HashSet<T, BuildHasherDefault<FxHasher>>;

/// An immutable, shared, ordered and duplicate-free set of provenance links.
///
/// Its value is the link list [`OriginSet::links`] returns: equality, ordering and `Debug` are
/// those of that list, so how the set is represented (which sets it names, which allocations it
/// shares) never shows in a comparison.
#[derive(Clone, Default)]
pub struct OriginSet(Option<Arc<[OriginPart]>>);

/// One part of an origin-set node.
#[derive(Clone)]
pub(crate) enum OriginPart {
    Link(ProvenanceLink),
    Set(OriginSet),
}

/// Building a node from its parts, reading a node's parts and flattening a set to its links are
/// the set work of recording receipts, which that algorithm's counters count.
///
/// ```toml algorithm-site
/// id = "definition.provenance.record"
/// role = "part"
/// sites = ["OriginSet::from_parts", "OriginSet::parts", "OriginSet::links"]
/// ```
impl OriginSet {
    /// The empty set.
    pub fn new() -> Self {
        Self(None)
    }

    fn flat(links: Vec<ProvenanceLink>) -> Self {
        if links.is_empty() {
            return Self::new();
        }
        Self(Some(links.into_iter().map(OriginPart::Link).collect()))
    }

    /// The set whose denotation is the first-occurrence union of `parts` in order, built from
    /// the parts that add a link: a `Set` part naming the empty set, a `Set` part naming an
    /// allocation already named, and a link already present are dropped. The empty list gives
    /// the empty set, and a single remaining `Set` part gives that set itself.
    ///
    /// The drops compare links by value and sets by allocation only; they read no link of a
    /// named set, so building a node costs time in the square of the number of its parts alone
    /// (at most five for a term receipt).
    pub(crate) fn from_parts(parts: impl IntoIterator<Item = OriginPart>) -> Self {
        let mut kept = Vec::<OriginPart>::new();
        // Invariant: `kept` holds the parts already accepted, none of them the empty set, no
        // link twice and no allocation twice.
        for part in parts {
            let repeated = match &part {
                OriginPart::Link(link) => kept
                    .iter()
                    .any(|seen| matches!(seen, OriginPart::Link(seen) if seen == link)),
                OriginPart::Set(set) => {
                    set.is_empty()
                        || kept
                            .iter()
                            .any(|seen| matches!(seen, OriginPart::Set(seen) if seen.ptr_eq(set)))
                }
            };
            if !repeated {
                kept.push(part);
            }
        }
        match kept.as_slice() {
            [] => Self::new(),
            [OriginPart::Set(set)] => set.clone(),
            [_, ..] => {
                measure::bump(Counter::ProvenanceSetNodesBuilt);
                measure::add(Counter::ProvenanceSetPartsBuilt, kept.len() as u64);
                Self(Some(kept.into()))
            }
        }
    }

    /// The node whose parts are `parts`, which already satisfy the node rules: at least one
    /// part, no empty set, no repeated link or allocation, not a single set. Checked in debug
    /// builds only; the reader checks them on the document before building.
    pub(crate) fn from_normal_parts(parts: Vec<OriginPart>) -> Self {
        debug_assert!(!parts.is_empty() && !matches!(parts.as_slice(), [OriginPart::Set(_)]));
        debug_assert!(parts.iter().all(|part| match part {
            OriginPart::Link(_) => true,
            OriginPart::Set(set) => !set.is_empty(),
        }));
        Self(Some(parts.into()))
    }

    /// The node whose parts are exactly `parts`, applying none of the node rules: test support
    /// for showing that the bytes of a document do not depend on whether they were applied.
    #[cfg(test)]
    pub(crate) fn from_raw_parts(parts: Vec<OriginPart>) -> Self {
        Self(Some(parts.into()))
    }

    /// Whether the set holds no link.
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// Whether `self` and `other` are one allocation; two empty sets are.
    pub fn ptr_eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            (None, None) => true,
            (Some(_), None) | (None, Some(_)) => false,
        }
    }

    /// The address of the set's node, null for the empty set: an identity for memo tables that
    /// also hold the set, so that the address cannot be reused while they live.
    pub(crate) fn address(&self) -> usize {
        self.0
            .as_ref()
            .map_or(0, |parts| Arc::as_ptr(parts).cast::<OriginPart>() as usize)
    }

    /// The parts of the set's node, none for the empty set.
    ///
    /// This hands the sets the node names to its caller, so it is counted as [`OriginSet::links`]
    /// counts a node it enters: one for the node and one per part. A walk over the DAG through it
    /// shows in `provenance.links_steps` wherever it is written (design §14.3); the walks of this
    /// module read nodes through `node_parts`, which counts nothing, and count their own steps.
    /// The one exception is work run under `measure::without_counting`, which no counter sees:
    /// only validations that debug and `kompile-invariant-checks` builds compile in run there.
    pub(crate) fn parts(&self) -> &[OriginPart] {
        let parts = self.node_parts();
        if !parts.is_empty() {
            measure::add(Counter::ProvenanceLinksSteps, 1 + parts.len() as u64);
        }
        parts
    }

    fn node_parts(&self) -> &[OriginPart] {
        self.0.as_deref().unwrap_or_default()
    }

    /// Whether every part of the set's node is a link, so that its parts are its links. It reads
    /// one node and hands out none of the sets it names.
    pub fn is_flat(&self) -> bool {
        self.node_parts()
            .iter()
            .all(|part| matches!(part, OriginPart::Link(_)))
    }

    /// The links the set denotes, in order, each once.
    ///
    /// A depth-first walk over the parts in order, emitting each link the first time it is
    /// reached. A set node is entered when the walk reaches a part naming it and is marked then;
    /// a part naming a marked node is skipped, because a marked node is finished (in an acyclic
    /// structure it cannot be on the walk's own stack), so all its links are already emitted
    /// and emitting them again would add nothing. Marking on entry rather than when the parent
    /// is entered keeps the first-occurrence order: a set named by a later part may first be
    /// reached through an earlier one. The walk enters each reachable node once and examines
    /// each part of an entered node once, whatever the number of paths through the DAG.
    pub fn links(&self) -> Vec<ProvenanceLink> {
        let parts = self.node_parts();
        if self.is_flat() {
            measure::add(Counter::ProvenanceLinksSteps, 1 + parts.len() as u64);
            return parts
                .iter()
                .map(|part| match part {
                    OriginPart::Link(link) => link.clone(),
                    OriginPart::Set(_) => unreachable!("a flat node has only links"),
                })
                .collect();
        }
        measure::bump(Counter::ProvenanceNonflatFlattens);
        let mut links = Vec::new();
        let mut emitted = FxHashSet::<&ProvenanceLink>::default();
        let mut entered = FxHashSet::<usize>::default();
        entered.insert(self.address());
        let mut stack = vec![(parts, 0usize)];
        // One for the root node; then one per part examined and one per node entered.
        let mut steps = 1u64;
        // Invariant: `links` is the first-occurrence union of the parts already examined, in
        // order, and `entered` names every node pushed so far.
        while let Some((parts, next)) = stack.last_mut() {
            let Some(part) = parts.get(*next) else {
                stack.pop();
                continue;
            };
            *next += 1;
            match part {
                OriginPart::Link(link) => {
                    steps += 1;
                    if emitted.insert(link) {
                        links.push(link.clone());
                    }
                }
                OriginPart::Set(set) => {
                    steps += 1;
                    if entered.insert(set.address()) {
                        steps += 1;
                        stack.push((set.node_parts(), 0));
                    }
                }
            }
        }
        measure::add(Counter::ProvenanceLinksSteps, steps);
        links
    }

    /// Whether `link` is one of the set's links.
    pub fn contains(&self, link: &ProvenanceLink) -> bool {
        self.links().contains(link)
    }
}

impl From<Vec<ProvenanceLink>> for OriginSet {
    /// The set of `links`, each kept at its first occurrence.
    fn from(links: Vec<ProvenanceLink>) -> Self {
        let mut seen = FxHashSet::default();
        let unique = links
            .iter()
            .filter(|link| seen.insert(*link))
            .cloned()
            .collect::<Vec<_>>();
        drop(seen);
        Self::flat(unique)
    }
}

impl<const N: usize> From<[ProvenanceLink; N]> for OriginSet {
    fn from(links: [ProvenanceLink; N]) -> Self {
        Self::from(Vec::from(links))
    }
}

impl PartialEq for OriginSet {
    fn eq(&self, other: &Self) -> bool {
        self.ptr_eq(other) || self.links() == other.links()
    }
}

impl Eq for OriginSet {}

impl PartialOrd for OriginSet {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OriginSet {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.ptr_eq(other) {
            return std::cmp::Ordering::Equal;
        }
        self.links().cmp(&other.links())
    }
}

impl Hash for OriginSet {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.links().hash(state);
    }
}

impl fmt::Debug for OriginSet {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_list().entries(self.links()).finish()
    }
}

impl Drop for OriginSet {
    fn drop(&mut self) {
        // Dropping the last reference to a node drops the sets its parts name, and so on down:
        // take those sets out of every node this drop owns alone and free them from a work list,
        // so that no drop recurses.
        let mut pending = Vec::new();
        let mut next = self.0.take();
        while let Some(mut node) = next {
            if let Some(parts) = Arc::get_mut(&mut node) {
                for part in parts.iter_mut() {
                    if let OriginPart::Set(set) = part
                        && let Some(child) = set.0.take()
                    {
                        pending.push(child);
                    }
                }
            }
            drop(node);
            next = pending.pop();
        }
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::{kast::TermSpan, provenance::SourceId};

    fn link(value: u32) -> ProvenanceLink {
        ProvenanceLink::Source {
            span: TermSpan {
                source: SourceId(0),
                start: value as usize,
                end: value as usize + 1,
            },
        }
    }

    fn set(parts: Vec<OriginPart>) -> OriginSet {
        OriginSet::from_parts(parts)
    }

    /// A part of a test DAG: a link, or a reference to an earlier node.
    #[derive(Clone, Debug)]
    enum Spec {
        Link(u32),
        Set(usize),
    }

    /// The denotation of node `index`, computed from the definition with no memo and no
    /// visited-node skip: the first-occurrence union of the full unfolding of its parts.
    fn oracle(nodes: &[Vec<Spec>], index: usize) -> Vec<ProvenanceLink> {
        let mut links = Vec::new();
        for part in &nodes[index] {
            let unfolded = match part {
                Spec::Link(value) => vec![link(*value)],
                Spec::Set(child) => oracle(nodes, *child),
            };
            for link in unfolded {
                if !links.contains(&link) {
                    links.push(link);
                }
            }
        }
        links
    }

    /// Random DAGs of up to eight nodes over a five-link alphabet, each node naming any earlier
    /// node, so that a node is often reachable along several paths (a diamond) and links repeat.
    fn dags() -> impl Strategy<Value = Vec<Vec<Spec>>> {
        prop::collection::vec(
            prop::collection::vec(
                (any::<bool>(), 0_u32..5, any::<prop::sample::Index>()),
                0..5,
            ),
            1..8,
        )
        .prop_map(|nodes| {
            nodes
                .into_iter()
                .enumerate()
                .map(|(index, parts)| {
                    parts
                        .into_iter()
                        .map(|(is_set, value, pick)| {
                            if is_set && index > 0 {
                                Spec::Set(pick.index(index))
                            } else {
                                Spec::Link(value)
                            }
                        })
                        .collect()
                })
                .collect()
        })
    }

    fn build(nodes: &[Vec<Spec>]) -> Vec<OriginSet> {
        let mut sets = Vec::<OriginSet>::new();
        for parts in nodes {
            let built = set(parts
                .iter()
                .map(|part| match part {
                    Spec::Link(value) => OriginPart::Link(link(*value)),
                    Spec::Set(child) => OriginPart::Set(sets[*child].clone()),
                })
                .collect());
            sets.push(built);
        }
        sets
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        /// `links` of every node equals the naive unfolding of the parts it was built from,
        /// whatever the construction dropped or collapsed and however the DAG shares nodes.
        #[test]
        fn links_equal_the_naive_unfolding(nodes in dags()) {
            let sets = build(&nodes);
            for (index, set) in sets.iter().enumerate() {
                let expected = oracle(&nodes, index);
                prop_assert_eq!(set.links(), expected.clone());
                prop_assert_eq!(set.is_empty(), expected.is_empty());
                prop_assert_eq!(set, &OriginSet::from(expected));
            }
        }
    }

    /// A set named by a later part may be reached first through an earlier one: the walk marks a
    /// node when it enters it, not when its parent is entered, so `l2` (reached through `A`)
    /// precedes `l1`.
    #[test]
    fn a_set_reached_first_through_an_earlier_part_keeps_its_place() {
        let b = set(vec![OriginPart::Link(link(2))]);
        let a = set(vec![OriginPart::Set(b.clone()), OriginPart::Link(link(1))]);
        let x = set(vec![OriginPart::Set(a), OriginPart::Set(b)]);
        assert_eq!(x.links(), [link(2), link(1)]);
    }

    /// The construction's local rules: a repeated link, a set named twice, and the empty set add
    /// no part; one remaining set part is that set; no part is the empty set.
    #[test]
    fn from_parts_drops_parts_that_add_no_link() {
        let flat = OriginSet::from(vec![link(1), link(2)]);
        assert!(set(Vec::new()).is_empty());
        assert!(
            set(vec![
                OriginPart::Set(OriginSet::new()),
                OriginPart::Set(flat.clone())
            ])
            .ptr_eq(&flat)
        );
        let node = set(vec![
            OriginPart::Link(link(3)),
            OriginPart::Set(flat.clone()),
            OriginPart::Link(link(3)),
            OriginPart::Set(flat.clone()),
        ]);
        assert_eq!(node.parts().len(), 2);
        assert_eq!(node.links(), [link(3), link(1), link(2)]);
        assert_eq!(
            OriginSet::from(vec![link(1), link(1), link(2)])
                .parts()
                .len(),
            2
        );
    }

    /// A chain of 100,000 sets, each naming the one before, is flattened, compared, ordered,
    /// formatted and dropped on a 256 KiB thread.
    #[test]
    fn a_long_chain_of_sets_is_handled_on_a_small_stack() {
        const LENGTH: u32 = 100_000;
        std::thread::Builder::new()
            .stack_size(256 << 10)
            .spawn(|| {
                let chain = |offset: u32| {
                    let mut chain = OriginSet::new();
                    for value in 0..LENGTH {
                        chain = set(vec![
                            OriginPart::Link(link(value + offset)),
                            OriginPart::Set(chain),
                        ]);
                    }
                    chain
                };
                let (left, right) = (chain(0), chain(0));
                let links = left.links();
                assert_eq!(links.len(), LENGTH as usize);
                assert_eq!(links[0], link(LENGTH - 1));
                assert_eq!(left, right);
                assert_eq!(left.cmp(&chain(1)), std::cmp::Ordering::Less);
                assert!(format!("{left:?}").len() > LENGTH as usize);
                drop(left);
                drop(right);
            })
            .expect("the worker should spawn")
            .join()
            .expect("the worker should finish");
    }
}

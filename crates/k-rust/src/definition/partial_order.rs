//! ```toml algorithm
//! id = "definition.order.partial"
//! name = "finite partial-order construction and closure"
//! sites = ["PartialOrder", "PartialOrder::new", "find_cycle"]
//! variable = "V = elements; E = direct relations; C = sum over direct relations (a, b) of 1 + |closure(b)|, the elements cloned and inserted into closure sets"
//! counters = ["KompilePartialOrdersBuilt"]
//!
//! [[cost]]
//! mode = "one partial order"
//! bound = "O((V + E) log V + C log V)"
//!
//! [[cost]]
//! mode = "upper_bounds or lower_bounds of a nonempty set S"
//! bound = "O(|S| x (1 + b) x log V) with b the strict successors (upper) or predecessors (lower) of the member of S with the fewest; the first lower_bounds of an order also inverts the closure once, O(C log V)"
//! ```
//!
//! Finite partial orders use Kahn topological sorting, reverse-order transitive closure, and set-intersection bounds.
//! Construction is O(V + E + closure); `Counter::KompilePartialOrdersBuilt` measures builds.
//!
//! A deterministic, `petgraph`-backed finite partial order.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

use k_rust_kore::measure::{self, Counter};
use petgraph::Direction::{Incoming, Outgoing};
use petgraph::algo::toposort;
use petgraph::graph::{DiGraph, NodeIndex};

/// An invalid strict relation containing a directed cycle.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cycle<T> {
    pub path: Vec<T>,
}

impl<T: std::fmt::Display> std::fmt::Display for Cycle<T> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "illegal circular relation: ")?;
        for (index, element) in self.path.iter().enumerate() {
            if index != 0 {
                write!(formatter, " < ")?;
            }
            write!(formatter, "{element}")?;
        }
        Ok(())
    }
}

impl<T: std::fmt::Debug + std::fmt::Display> std::error::Error for Cycle<T> {}

/// A finite partial order constructed from strict `(lesser, greater)` pairs.
///
/// Like K's Java `POSet`, elements which occur in no relation are not members of
/// the set. Direct relations are retained separately from their transitive closure.
#[derive(Clone)]
pub struct PartialOrder<T> {
    direct: BTreeSet<(T, T)>,
    closure: BTreeMap<T, BTreeSet<T>>,
    sorted: Vec<T>,
    // The inverse of `closure`, with an entry for every element, built on the first query that
    // needs the strict predecessors of an element.
    predecessors: OnceLock<BTreeMap<T, BTreeSet<T>>>,
}

impl<T: std::fmt::Debug> std::fmt::Debug for PartialOrder<T> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("PartialOrder")
            .field("direct", &self.direct)
            .field("closure", &self.closure)
            .field("sorted", &self.sorted)
            .finish()
    }
}

impl<T: Ord> PartialEq for PartialOrder<T> {
    fn eq(&self, other: &Self) -> bool {
        self.closure == other.closure
    }
}

impl<T: Ord> Eq for PartialOrder<T> {}

impl<T: Clone + Ord> PartialOrder<T> {
    pub fn new(relations: impl IntoIterator<Item = (T, T)>) -> Result<Self, Cycle<T>> {
        let direct = relations.into_iter().collect::<BTreeSet<_>>();
        let elements = direct
            .iter()
            .flat_map(|(lesser, greater)| [lesser.clone(), greater.clone()])
            .collect::<BTreeSet<_>>();

        let mut graph = DiGraph::<T, ()>::new();
        let nodes = elements
            .iter()
            .cloned()
            .map(|element| {
                let node = graph.add_node(element.clone());
                (element, node)
            })
            .collect::<BTreeMap<_, _>>();
        for (lesser, greater) in &direct {
            graph.add_edge(nodes[lesser], nodes[greater], ());
        }

        if toposort(&graph, None).is_err() {
            return Err(Cycle {
                path: find_cycle(&graph).expect("toposort reported a cycle"),
            });
        }

        // Kahn's algorithm with an ordered ready set makes unrelated elements
        // deterministic without changing the lesser-to-greater edge direction.
        let mut indegree = graph
            .node_indices()
            .map(|node| (node, graph.neighbors_directed(node, Incoming).count()))
            .collect::<BTreeMap<_, _>>();
        let mut ready = graph
            .node_indices()
            .filter(|node| indegree[node] == 0)
            .map(|node| (graph[node].clone(), node))
            .collect::<BTreeSet<_>>();
        let mut order = Vec::with_capacity(graph.node_count());
        // Invariant: `ready` contains exactly the unprocessed zero-indegree nodes and `order` is
        // a prefix of a linear extension; each pop permanently appends one node.
        while let Some((element, node)) = ready.pop_first() {
            order.push(node);
            let mut successors = graph.neighbors_directed(node, Outgoing).collect::<Vec<_>>();
            successors.sort_by(|left, right| graph[*left].cmp(&graph[*right]));
            for successor in successors {
                indegree.entry(successor).and_modify(|degree| *degree -= 1);
                if indegree[&successor] == 0 {
                    ready.insert((graph[successor].clone(), successor));
                }
            }
            drop(element);
        }

        let mut closure = elements
            .iter()
            .cloned()
            .map(|element| (element, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        // Invariant: successors of each node visited in reverse topological order already have
        // complete strict-successor closures.
        for &node in order.iter().rev() {
            let mut successors = graph.neighbors_directed(node, Outgoing).collect::<Vec<_>>();
            successors.sort_by(|left, right| graph[*left].cmp(&graph[*right]));
            for successor in successors {
                let successor_element = graph[successor].clone();
                let inherited = closure[&successor_element].clone();
                closure
                    .get_mut(&graph[node])
                    .expect("every graph node has a closure entry")
                    .extend(std::iter::once(successor_element).chain(inherited));
            }
        }

        let order = Self {
            direct,
            closure,
            sorted: order.into_iter().map(|node| graph[node].clone()).collect(),
            predecessors: OnceLock::new(),
        };
        measure::bump(Counter::KompilePartialOrdersBuilt);
        Ok(order)
    }

    pub fn elements(&self) -> impl ExactSizeIterator<Item = &T> {
        self.closure.keys()
    }

    pub fn direct_relations(&self) -> &BTreeSet<(T, T)> {
        &self.direct
    }

    pub fn relations_from(&self, element: &T) -> Option<&BTreeSet<T>> {
        self.closure.get(element)
    }

    /// A deterministic topological order with lesser elements first.
    pub fn sorted_elements(&self) -> &[T] {
        &self.sorted
    }

    pub fn contains(&self, element: &T) -> bool {
        self.closure.contains_key(element)
    }

    pub fn directly_less_than(&self, lesser: &T, greater: &T) -> bool {
        self.direct.contains(&(lesser.clone(), greater.clone()))
    }

    pub fn less_than(&self, lesser: &T, greater: &T) -> bool {
        self.closure
            .get(lesser)
            .is_some_and(|successors| successors.contains(greater))
    }

    pub fn less_than_eq(&self, lesser: &T, greater: &T) -> bool {
        lesser == greater || self.less_than(lesser, greater)
    }

    pub fn greater_than(&self, greater: &T, lesser: &T) -> bool {
        self.less_than(lesser, greater)
    }

    pub fn greater_than_eq(&self, greater: &T, lesser: &T) -> bool {
        self.less_than_eq(lesser, greater)
    }

    pub fn in_some_relation(&self, first: &T, second: &T) -> bool {
        self.less_than(first, second) || self.greater_than(first, second)
    }

    pub fn in_some_relation_eq(&self, first: &T, second: &T) -> bool {
        first == second || self.in_some_relation(first, second)
    }

    pub fn upper_bounds<'a>(&self, elements: impl IntoIterator<Item = &'a T>) -> BTreeSet<T>
    where
        T: 'a,
    {
        self.bounds(
            elements,
            |element| self.closure.get(element),
            |order, candidate, element| order.less_than_eq(element, candidate),
        )
    }

    pub fn lower_bounds<'a>(&self, elements: impl IntoIterator<Item = &'a T>) -> BTreeSet<T>
    where
        T: 'a,
    {
        self.bounds(
            elements,
            |element| self.predecessors().get(element),
            |order, candidate, element| order.less_than_eq(candidate, element),
        )
    }

    pub fn minimal<'a>(&self, elements: impl IntoIterator<Item = &'a T>) -> BTreeSet<T>
    where
        T: 'a,
    {
        let elements = elements.into_iter().collect::<Vec<_>>();
        elements
            .iter()
            .filter(|candidate| {
                !elements
                    .iter()
                    // Invariant: no entry of `elements` before `other` is strictly less than `candidate`; the scan consumes one entry per step, so `minimal` makes at most |elements|^2 `less_than` queries.
                    .any(|other| self.less_than(other, candidate))
            })
            .map(|element| (*element).clone())
            .collect()
    }

    pub fn maximal<'a>(&self, elements: impl IntoIterator<Item = &'a T>) -> BTreeSet<T>
    where
        T: 'a,
    {
        let elements = elements.into_iter().collect::<Vec<_>>();
        elements
            .iter()
            .filter(|candidate| {
                !elements
                    .iter()
                    // Invariant: no entry of `elements` before `other` is strictly greater than `candidate`; the scan consumes one entry per step, so `maximal` makes at most |elements|^2 `less_than` queries.
                    .any(|other| self.less_than(candidate, other))
            })
            .map(|element| (*element).clone())
            .collect()
    }

    pub fn minimum<'a>(&self, elements: impl IntoIterator<Item = &'a T>) -> Option<T>
    where
        T: 'a,
    {
        unique(self.minimal(elements))
    }

    pub fn maximum<'a>(&self, elements: impl IntoIterator<Item = &'a T>) -> Option<T>
    where
        T: 'a,
    {
        unique(self.maximal(elements))
    }

    /// Connected components of the relation when edge direction is ignored.
    pub fn connected_components(&self) -> Vec<BTreeSet<T>> {
        let mut unseen = self.elements().cloned().collect::<BTreeSet<_>>();
        let mut components = Vec::new();
        // Invariant: `unseen` contains exactly the elements not assigned to a completed component.
        while let Some(start) = unseen.pop_first() {
            let mut component = BTreeSet::new();
            let mut pending = vec![start];
            // Invariant: `pending` is the unexpanded frontier of the current component and every
            // element in `component` has been removed from `unseen`.
            while let Some(element) = pending.pop() {
                if !component.insert(element.clone()) {
                    continue;
                }
                unseen.remove(&element);
                // Invariant: `pending` has gained every element of `self.elements()` before `candidate` that is related to `element` in either direction and absent from `component`; each iteration consumes one element, so each expansion scans all of `self.elements()`.
                for candidate in self.elements() {
                    if (self.less_than(&element, candidate) || self.less_than(candidate, &element))
                        && !component.contains(candidate)
                    {
                        pending.push(candidate.clone());
                    }
                }
            }
            components.push(component);
        }
        components
    }

    fn predecessors(&self) -> &BTreeMap<T, BTreeSet<T>> {
        self.predecessors.get_or_init(|| {
            let mut predecessors = self
                .closure
                .keys()
                .map(|element| (element.clone(), BTreeSet::new()))
                .collect::<BTreeMap<_, _>>();
            for (lesser, successors) in &self.closure {
                for greater in successors {
                    predecessors
                        .get_mut(greater)
                        .expect("every successor is an element")
                        .insert(lesser.clone());
                }
            }
            predecessors
        })
    }

    /// The elements in `relation` to every member of `elements`, where `neighbours` gives the
    /// elements strictly in that relation to one member (`None` for a non-member of the order).
    fn bounds<'a, 'b>(
        &'b self,
        elements: impl IntoIterator<Item = &'a T>,
        neighbours: impl Fn(&T) -> Option<&'b BTreeSet<T>>,
        relation: impl Fn(&Self, &T, &T) -> bool,
    ) -> BTreeSet<T>
    where
        T: 'a,
    {
        let elements = elements.into_iter().collect::<Vec<_>>();
        if elements.is_empty() {
            return self.elements().cloned().collect();
        }
        // A bound is an element related or equal to every member, so it is a member itself or one
        // of the member's neighbours; a non-member of the order has neither, so no bound exists.
        // Testing the candidates of the member with the fewest neighbours finds every bound.
        let mut seed = None::<(&T, &BTreeSet<T>)>;
        for element in &elements {
            let Some(candidates) = neighbours(element) else {
                return BTreeSet::new();
            };
            if seed.is_none_or(|(_, fewest)| candidates.len() < fewest.len()) {
                seed = Some((element, candidates));
            }
        }
        let (member, candidates) = seed.expect("a nonempty set has a seed");
        std::iter::once(member)
            .chain(candidates)
            .filter(|candidate| {
                elements
                    .iter()
                    // Invariant: every entry of `elements` before `element` satisfies `relation(self, candidate, _)`; the scan consumes one entry per step, so `bounds` makes at most (1 + |neighbours(seed)|) * |elements| `relation` calls.
                    .all(|element| relation(self, candidate, element))
            })
            .cloned()
            .collect()
    }
}

fn unique<T: Ord>(mut elements: BTreeSet<T>) -> Option<T> {
    (elements.len() == 1).then(|| elements.pop_first().expect("length was one"))
}

fn find_cycle<T: Clone + Ord>(graph: &DiGraph<T, ()>) -> Option<Vec<T>> {
    // Invariant: `stack` is the current depth-first path, whose nodes have `state` 1, and finished nodes have `state` 2; each recursive call is made only on a node with `state` 0 and sets it to 1, so the node count of `graph` bounds the calls.
    fn visit<T: Clone + Ord>(
        graph: &DiGraph<T, ()>,
        node: NodeIndex,
        state: &mut [u8],
        stack: &mut Vec<NodeIndex>,
    ) -> Option<Vec<T>> {
        state[node.index()] = 1;
        stack.push(node);
        let mut successors = graph.neighbors_directed(node, Outgoing).collect::<Vec<_>>();
        successors.sort_by(|left, right| graph[*left].cmp(&graph[*right]));
        // Invariant: every entry of `successors` before `successor` has `state` 2, since a visit that returns `None` finishes its node; each iteration consumes one successor.
        for successor in successors {
            if state[successor.index()] == 0 {
                if let Some(cycle) = visit(graph, successor, state, stack) {
                    return Some(cycle);
                }
            } else if state[successor.index()] == 1 {
                let start = stack
                    .iter()
                    // Invariant: no entry of `stack` before `candidate` equals `successor`, which has `state` 1 and so lies on `stack`; the scan consumes one stack entry per step.
                    .position(|candidate| *candidate == successor)
                    .expect("active node is in DFS stack");
                return Some(
                    stack[start..]
                        .iter()
                        .chain(std::iter::once(&successor))
                        .map(|node| graph[*node].clone())
                        .collect(),
                );
            }
        }
        stack.pop();
        state[node.index()] = 2;
        None
    }

    let mut state = vec![0; graph.node_count()];
    let mut stack = Vec::new();
    let mut nodes = graph.node_indices().collect::<Vec<_>>();
    nodes.sort_by(|left, right| graph[*left].cmp(&graph[*right]));
    // Invariant: every entry of `nodes` before `node` has `state` 2 and `stack` is empty; each iteration consumes one node.
    for node in nodes {
        if state[node.index()] == 0
            && let Some(cycle) = visit(graph, node, &mut state, &mut stack)
        {
            return Some(cycle);
        }
    }
    None
}

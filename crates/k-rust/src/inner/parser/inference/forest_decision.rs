//! ```toml algorithm-site
//! id = "parser.inference.portable"
//! role = "part"
//! sites = ["Grammar::decide_forest", "ForestDecision::summaries", "ForestDecision::close", "ForestDecision::eval", "ForestDecision::apply"]
//! ```
//!
//! The portable decision of an ambiguous monomorphic forest, computed on the forest without
//! listing its trees (`Grammar::decide_forest`).
//!
//! The decision is the one `Grammar::infer_ambiguous_sorts_portable` states: the well-sorted
//! trees whose variable typing no other tree's typing strictly exceeds, one group per maximal
//! typing. It rests on what one tree's constraint graph is (`Solver::infer`):
//! - a variable's upper bounds are `K` and, for each occurrence, the expected sort at its
//!   parent edge, or, through a chain of parameter positions, the concrete sorts the chain's
//!   parameter slots reach; its lower bounds are the sort of a strict cast directly above an
//!   occurrence, and, for an anonymous variable, the expected sort itself;
//! - a parameter slot reaches the concrete sorts its production's position reaches (when its
//!   result is the parameter and the position is not a scaffolding sort), `K` when an anonymous
//!   variable stands at one of its positions, and the left-hand side's sort at the top rewrite of
//!   an anywhere rule. Its value is the greatest sort below all of them, or `K` when it reaches
//!   none; the concrete sorts below it are only checked against that value.
//!
//! So everything a node's constraints say depends on the node and on its **context**, the part
//! of its ancestors' constraints that reaches it (`Context`), and a variable's realized sort is
//! the greatest element of the meet of one interval per occurrence (`Sorts`): the sorts below
//! every upper bound, above every lower bound, and not below `KBott`. A tree's well-sorted
//! typings are the product of its variables' intervals, so a subforest's trees are summarized by
//! the distinct maps from variables to intervals they have (`Summary`), computed once per node
//! and context, bottom-up: a production meets its children's summaries, an ambiguity unites its
//! alternatives'. The root's summaries are the forest's typings; the maximal ones are kept, and
//! each is applied to the forest top-down to build the trees well-sorted under it, packed as the
//! forest was.
//!
//! Of the instances of a bracket that read one text at an ambiguity, the trees keep the one at
//! the sort the position gives (`ForestDecision::shadowed_bracket_instances`).
//!
//! The decision assumes what the per-tree decision does, and refuses where the context does not
//! determine a parameter slot: a slot whose bounds have several greatest common lower bounds, a
//! slot with no concrete upper bound one of whose lower bounds is not below `K`, a slot an
//! anonymous variable bounds by `K` in some trees only where its value is not below `K`, a
//! parametric left-hand side of an anywhere rule whose own positions bound it, and a cast whose
//! sorts are parameters. A refusal is reported only when a tree that is otherwise well-sorted
//! carries it.
//!
//! A summary that another summary of the same node and context exceeds on the variables that
//! occur only below the node, and equals elsewhere, is dropped (`ForestDecision::close`), so
//! independent ambiguities that choose sorts for their own variables keep one summary each and
//! the decision stays linear in the forest where listing its trees would be exponential.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;
use std::sync::OnceLock;

use crate::definition::{PartialOrder, ProductionItem};
use crate::kast::{FrontendSort, GeneratedLabel, InternalLabel, Label, Sort, Term};

use super::super::{
    Grammar, Item, PackedNode, PackedTerm, ParseError, ParsedTerm, TermMetadata,
    inferred_variable_name, variable_with_inferred_sort,
};
use super::{PortableError, TypingVariable, inference_error, is_anonymous};

/// A set of sorts, one bit per sort of a [`SortIndex`], without trailing zero words, so that
/// equal sets are equal values.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Sorts(Box<[u64]>);

impl Sorts {
    fn from_words(mut words: Vec<u64>) -> Self {
        while words.last() == Some(&0) {
            words.pop();
        }
        Self(words.into_boxed_slice())
    }

    fn from_indices(indices: impl IntoIterator<Item = usize>) -> Self {
        let mut words = Vec::new();
        for index in indices {
            if words.len() <= index / 64 {
                words.resize(index / 64 + 1, 0);
            }
            words[index / 64] |= 1 << (index % 64);
        }
        Self::from_words(words)
    }

    fn and(&self, other: &Self) -> Self {
        Self::from_words(
            self.0
                .iter()
                .zip(other.0.iter())
                .map(|(left, right)| left & right)
                .collect(),
        )
    }

    fn and_not(&self, other: &Self) -> Self {
        Self::from_words(
            self.0
                .iter()
                .enumerate()
                .map(|(index, word)| word & !other.0.get(index).copied().unwrap_or(0))
                .collect(),
        )
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn contains(&self, index: usize) -> bool {
        self.0
            .get(index / 64)
            .is_some_and(|word| word & (1 << (index % 64)) != 0)
    }

    fn highest(&self) -> Option<usize> {
        let last = self.0.len().checked_sub(1)?;
        Some(last * 64 + 63 - self.0[last].leading_zeros() as usize)
    }
}

/// The sorts of a subsort order, numbered so that a sort's number exceeds the number of every
/// sort below it: the order's elements in its linear extension (`PartialOrder::sorted_elements`,
/// lesser first), then `K` and `KBott` when the order does not hold them, each related only to
/// itself. Each sort's down and up sets are computed when a decision first asks for them.
///
/// Everything here is a function of the order alone, so a grammar builds one table beside its
/// order and every forest decision over that grammar shares it
/// (`SubsortRelations::sort_table`); a decision numbers the sorts it meets outside the table
/// after it ([`SortIndex`]).
#[derive(Clone, Debug)]
pub(in crate::inner::parser) struct SortTable {
    sorts: Vec<Sort>,
    ids: HashMap<Sort, usize>,
    down: Box<[OnceLock<Sorts>]>,
    up: Box<[OnceLock<Sorts>]>,
    /// The sorts below `K` and not below `KBott`, the interval every variable starts from.
    variable: OnceLock<Sorts>,
    k: usize,
    k_bott: usize,
}

impl SortTable {
    pub(in crate::inner::parser) fn new(order: &PartialOrder<Sort>) -> Self {
        let mut sorts = order.sorted_elements().to_vec();
        let mut ids = sorts
            .iter()
            .enumerate()
            .map(|(index, sort)| (sort.clone(), index))
            .collect::<HashMap<_, _>>();
        let mut number = |sort: Sort| {
            *ids.entry(sort.clone()).or_insert_with(|| {
                sorts.push(sort);
                sorts.len() - 1
            })
        };
        let k = number(Sort::new("K"));
        let k_bott = number(Sort::frontend(FrontendSort::KBott));
        let unset = || (0..sorts.len()).map(|_| OnceLock::new()).collect();
        Self {
            down: unset(),
            up: unset(),
            sorts,
            ids,
            variable: OnceLock::new(),
            k,
            k_bott,
        }
    }

    /// The number of down and up sets computed so far.
    #[cfg(test)]
    pub(in crate::inner::parser) fn computed_sets(&self) -> usize {
        self.down
            .iter()
            .chain(self.up.iter())
            .filter(|set| set.get().is_some())
            .count()
    }

    /// The sorts at most `id`, or at least `id` when `up`, of the table's sort `id`.
    fn bounds(&self, order: &PartialOrder<Sort>, id: usize, up: bool) -> &Sorts {
        let sets = if up { &self.up } else { &self.down };
        sets[id].get_or_init(|| {
            let sort = &self.sorts[id];
            if !order.contains(sort) {
                return Sorts::from_indices([id]);
            }
            let bounds = if up {
                order.upper_bounds([sort])
            } else {
                order.lower_bounds([sort])
            };
            Sorts::from_indices(bounds.iter().map(|sort| self.ids[sort]))
        })
    }
}

/// The sorts of one decision: the grammar's [`SortTable`], then each sort outside it as the
/// decision meets it, which is related only to itself.
struct SortIndex<'o> {
    order: &'o PartialOrder<Sort>,
    table: &'o SortTable,
    outside: Vec<Sort>,
    outside_ids: HashMap<Sort, usize>,
    k: usize,
    k_bott: usize,
}

/// The greatest element of an interval, when it has one.
enum Realized {
    Empty,
    One(usize),
    Several,
}

impl<'o> SortIndex<'o> {
    fn new(order: &'o PartialOrder<Sort>, table: &'o SortTable) -> Self {
        Self {
            order,
            table,
            outside: Vec::new(),
            outside_ids: HashMap::new(),
            k: table.k,
            k_bott: table.k_bott,
        }
    }

    fn id(&mut self, sort: &Sort) -> usize {
        if let Some(id) = self
            .table
            .ids
            .get(sort)
            .or_else(|| self.outside_ids.get(sort))
        {
            return *id;
        }
        let id = self.table.sorts.len() + self.outside.len();
        self.outside.push(sort.clone());
        self.outside_ids.insert(sort.clone(), id);
        id
    }

    fn sort(&self, id: usize) -> &Sort {
        match id.checked_sub(self.table.sorts.len()) {
            None => &self.table.sorts[id],
            Some(outside) => &self.outside[outside],
        }
    }

    fn le(&self, lesser: usize, greater: usize) -> bool {
        lesser == greater || self.down(greater).contains(lesser)
    }

    fn domain(&self, id: usize) -> bool {
        self.sort(id).in_inference_domain()
    }

    fn bounds(&self, id: usize, up: bool) -> Cow<'o, Sorts> {
        if id < self.table.sorts.len() {
            Cow::Borrowed(self.table.bounds(self.order, id, up))
        } else {
            Cow::Owned(Sorts::from_indices([id]))
        }
    }

    /// The sorts at most `id`.
    fn down(&self, id: usize) -> Cow<'o, Sorts> {
        self.bounds(id, false)
    }

    /// The sorts at least `id`.
    fn up(&self, id: usize) -> Cow<'o, Sorts> {
        self.bounds(id, true)
    }

    /// The interval of a variable before any occurrence: below `K` and not below `KBott`.
    fn variable_interval(&self) -> Sorts {
        self.table
            .variable
            .get_or_init(|| self.down(self.k).and_not(&self.down(self.k_bott)))
            .clone()
    }

    /// The greatest element of `interval`: the highest-numbered element is maximal, and it is
    /// the greatest exactly when every element is below it.
    fn realize(&self, interval: &Sorts) -> Realized {
        let Some(top) = interval.highest() else {
            return Realized::Empty;
        };
        if interval.and_not(&self.down(top)).is_empty() {
            Realized::One(top)
        } else {
            Realized::Several
        }
    }
}

/// What a node's parent requires of the node's result.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Expected {
    /// The result is at most `sort`. A result that is a parameter slot reaches `sort` unless
    /// `exempts`: the position is a concrete scaffolding sort, which bounds no parameter.
    Sort { sort: usize, exempts: bool },
    /// The parent's parameter slot reaches no concrete sort: its value is `K` when every lower
    /// bound it receives is below `K`, which the decision requires.
    Unbounded,
}

/// Where a node stands with respect to the top rewrite of an anywhere rule
/// (`Grammar::top_rewrite_node`, `Grammar::function_lhs`).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Top {
    Off,
    /// On the path the top-rewrite search follows: through brackets, the first child of a
    /// `#RuleContent` production and of a `#withConfig` body.
    Search,
    /// Under the left-hand side of the top rewrite, kept only in trees whose left-hand side has
    /// `class`; `outer` is the result of the left-hand side's outermost node once it is known.
    Lhs {
        class: LhsClass,
        outer: Option<Outer>,
    },
}

/// What the left-hand side of a top rewrite makes of the rewrite.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum LhsClass {
    /// The rule is no anywhere rule.
    Plain,
    /// The rule is an anywhere rule whose rewrite is bounded by the left-hand side's sort, or
    /// (`None`) by a parameter slot, which the decision refuses.
    Anywhere(Option<usize>),
}

/// The result of a node: a sort, or one of its production's parameter slots.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Outer {
    Sort(usize),
    Parameter,
}

/// The part of a node's ancestors' constraints that reaches the node.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Context {
    expected: Expected,
    /// The `#Rule` scaffolding sort the grammar widened the position to: a result of exactly
    /// that sort is expected at it instead.
    widened: Option<usize>,
    /// The sort of a strict cast directly above, a lower bound of the result.
    pin: Option<usize>,
    /// The sort of a semantic cast directly above, which a variable under it records.
    semantic_cast: Option<usize>,
    /// An anonymous variable at the position has exactly the expected sort (false at the root).
    exact: bool,
    top: Top,
}

/// The distinct typings of the trees of one node in one context: each variable's interval, and
/// whether a tree holds an anonymous variable with no span or a refusal.
#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Summary {
    intervals: BTreeMap<TypingVariable, Sorts>,
    unidentified: bool,
    refused: bool,
}

impl Summary {
    /// The typings of the trees whose parts have `self` and `other`, or `None` when some variable
    /// has no sort in both: intervals only shrink, so such trees are ill-sorted.
    fn meet(&self, other: &Self) -> Option<Self> {
        let mut intervals = self.intervals.clone();
        for (variable, interval) in &other.intervals {
            match intervals.get_mut(variable) {
                Some(own) => {
                    *own = own.and(interval);
                    if own.is_empty() {
                        return None;
                    }
                }
                None => {
                    intervals.insert(variable.clone(), interval.clone());
                }
            }
        }
        Some(Self {
            intervals,
            unidentified: self.unidentified || other.unidentified,
            refused: self.refused || other.refused,
        })
    }
}

/// The summaries of a node in a context, each with the number of trees it stands for
/// (saturating); a tree dropped because another tree of the same summary elsewhere exceeds it
/// (`ForestDecision::close`) is still counted.
type Summaries = Rc<BTreeMap<Rc<Summary>, u64>>;

/// How a production node's constraints come out in one context.
enum NodeEval {
    /// A constraint between concrete sorts fails: no tree through the node is well-sorted.
    Ill,
    Node {
        refused: bool,
        /// The value of each parameter slot, `None` for a slot that reaches no concrete sort.
        parameters: Vec<Option<usize>>,
        children: Vec<Context>,
    },
}

/// A tree count's sum and product, saturating.
fn add(left: u64, right: u64) -> u64 {
    left.saturating_add(right)
}

/// The groups the forest decision keeps: one packed forest per maximal typing, with whether its
/// trees instantiate the formal parameters of their productions in more than one way.
pub(super) struct DecidedGroup {
    pub(super) term: Rc<PackedTerm>,
    pub(super) parameter_split: bool,
}

/// The instantiations of the parametric productions of a tree, as a sorted list.
type Instantiations = Rc<Vec<(usize, Vec<usize>)>>;

/// One application of a typing to the forest: the forest of the trees well-sorted under it, and
/// up to two distinct instantiation lists of those trees.
type Applied = Option<(Rc<PackedTerm>, Vec<Instantiations>)>;

struct ForestDecision<'g> {
    grammar: &'g Grammar,
    index: SortIndex<'g>,
    explicitly_anywhere: bool,
    summaries: HashMap<(*const PackedTerm, Context), Summaries>,
    /// The variables that occur in some tree of each node.
    variables: HashMap<*const PackedTerm, Rc<BTreeSet<TypingVariable>>>,
    /// The variables that occur outside a node in some tree through it.
    outside: HashMap<*const PackedTerm, BTreeSet<TypingVariable>>,
    semantic_casts: HashMap<usize, Option<usize>>,
}

impl Grammar {
    /// The portable decision of an ambiguous monomorphic forest: the groups of kept trees, one
    /// per maximal typing, or the rejection the per-tree decision gives (module documentation).
    /// `required` is the refusal.
    pub(super) fn decide_forest(
        &self,
        term: &Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
        required: &impl Fn() -> ParseError,
    ) -> Result<Vec<DecidedGroup>, ParseError> {
        let order = self.sort_order().map_err(PortableError::into_parse_error)?;
        let table = self
            .subsort_relations
            .sort_table()
            .expect("a relation with an order has a sort table");
        let mut decision = ForestDecision {
            grammar: self,
            index: SortIndex::new(order, table),
            explicitly_anywhere,
            summaries: HashMap::new(),
            variables: HashMap::new(),
            outside: HashMap::new(),
            semantic_casts: HashMap::new(),
        };
        decision.variables_of(term);
        decision.outside_of(term);
        let top = decision.index.id(top_sort);
        let root = Context {
            expected: Expected::Sort {
                sort: top,
                exempts: !decision.index.domain(top),
            },
            widened: None,
            pin: None,
            semantic_cast: None,
            exact: false,
            top: Top::Search,
        };
        let summaries = decision.summaries(term, root)?;
        if summaries.is_empty() {
            return Err(self.first_tree_rejection(term, top_sort, explicitly_anywhere, required));
        }
        let mut typings = Vec::new();
        let mut trees = 0u64;
        let mut unidentified = false;
        for (summary, count) in summaries.iter() {
            if summary.refused {
                return Err(required());
            }
            unidentified |= summary.unidentified;
            trees = add(trees, *count);
            let mut typing = BTreeMap::new();
            for (variable, interval) in &summary.intervals {
                // A variable at `K` is recorded as absent, as a variable a tree lacks is: two
                // trees that differ only in which variables they have at `K` have one typing.
                match decision.index.realize(interval) {
                    Realized::One(sort) => {
                        if sort != decision.index.k {
                            typing.insert(variable.clone(), sort);
                        }
                    }
                    Realized::Several => return Err(required()),
                    Realized::Empty => unreachable!("a summary has no empty interval"),
                }
            }
            for sort in typing.values() {
                decision.semantic_cast(*sort)?;
            }
            typings.push(typing);
        }
        if trees > 1 && unidentified {
            return Err(required());
        }
        let k = decision.index.k;
        let maximal = typings
            .iter()
            .filter(|typing| {
                !typings
                    .iter()
                    .any(|other| decision.strictly_exceeds(k, other, typing))
            })
            .cloned()
            .collect::<BTreeSet<_>>();
        maximal
            .into_iter()
            .map(|typing| {
                let mut memo = HashMap::new();
                let (term, instantiations) = decision
                    .apply(term, root, &typing, &mut memo)?
                    .expect("a maximal typing's trees are well-sorted under it");
                Ok(DecidedGroup {
                    term,
                    parameter_split: instantiations.len() > 1,
                })
            })
            .collect()
    }

    /// The rejection of a forest none of whose trees is well-sorted: the per-tree decision's
    /// rejection of its first tree, the one of every ambiguity's first alternative.
    fn first_tree_rejection(
        &self,
        term: &Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
        required: &impl Fn() -> ParseError,
    ) -> ParseError {
        fn first(term: &Rc<PackedTerm>) -> ParsedTerm {
            crate::stack::guarded(|| match &term.node {
                PackedNode::Term(leaf) => ParsedTerm::Term(leaf.clone()),
                PackedNode::Ambiguity(alternatives) => first(
                    alternatives
                        .first()
                        .expect("an ambiguity has an alternative"),
                ),
                PackedNode::Production {
                    production,
                    children,
                    metadata,
                } => ParsedTerm::Production {
                    production: *production,
                    children: children.iter().map(first).collect(),
                    metadata: metadata.clone(),
                },
                PackedNode::InstantiatedProduction { .. } => {
                    unreachable!("a forest is decided before inference")
                }
            })
        }
        match self.infer_typed_sorts_portable(first(term), top_sort, explicitly_anywhere) {
            Err(PortableError::Unsatisfiable(error) | PortableError::Malformed(error)) => error,
            Err(PortableError::Incomparable(_)) | Ok(_) => required(),
        }
    }
}

impl ForestDecision<'_> {
    fn variables_of(&mut self, term: &Rc<PackedTerm>) -> Rc<BTreeSet<TypingVariable>> {
        if let Some(known) = self.variables.get(&Rc::as_ptr(term)) {
            return Rc::clone(known);
        }
        let set = crate::stack::guarded(|| match &term.node {
            PackedNode::Term(leaf) => Rc::new(
                inferred_variable_name(leaf)
                    .and_then(|name| typing_variable(leaf, name))
                    .into_iter()
                    .collect(),
            ),
            PackedNode::Ambiguity(alternatives) => {
                let mut set = BTreeSet::new();
                for alternative in alternatives {
                    set.extend(self.variables_of(alternative).iter().cloned());
                }
                Rc::new(set)
            }
            PackedNode::Production { children, .. }
            | PackedNode::InstantiatedProduction { children, .. } => {
                let mut set = BTreeSet::new();
                for child in children {
                    set.extend(self.variables_of(child).iter().cloned());
                }
                Rc::new(set)
            }
        });
        self.variables.insert(Rc::as_ptr(term), Rc::clone(&set));
        set
    }

    /// For every node, the variables that occur outside it in some tree through it: those of
    /// the siblings at each production on some path from the root to it. A variable of a node
    /// that is not among them occurs, in every tree through the node, only in one copy of it.
    fn outside_of(&mut self, root: &Rc<PackedTerm>) {
        // Parents before children: a node's set is complete once every path to it is seen, so
        // the nodes are visited in reverse post-order of the forest DAG.
        let mut post = Vec::new();
        let mut seen = BTreeSet::new();
        let mut stack = vec![(Rc::clone(root), false)];
        // Invariant: `post` holds the finished nodes, each after every node reachable from it;
        // a node enters `stack` unexpanded once per edge and is expanded on its first pop.
        while let Some((node, expanded)) = stack.pop() {
            if expanded {
                post.push(node);
                continue;
            }
            if !seen.insert(Rc::as_ptr(&node)) {
                continue;
            }
            stack.push((Rc::clone(&node), true));
            match &node.node {
                PackedNode::Ambiguity(alternatives) => {
                    stack.extend(alternatives.iter().map(|child| (Rc::clone(child), false)));
                }
                PackedNode::Production { children, .. }
                | PackedNode::InstantiatedProduction { children, .. } => {
                    stack.extend(children.iter().map(|child| (Rc::clone(child), false)));
                }
                PackedNode::Term(_) => {}
            }
        }
        self.outside.insert(Rc::as_ptr(root), BTreeSet::new());
        for node in post.iter().rev() {
            let own = self
                .outside
                .get(&Rc::as_ptr(node))
                .cloned()
                .unwrap_or_default();
            match &node.node {
                PackedNode::Ambiguity(alternatives) => {
                    for alternative in alternatives {
                        self.outside
                            .entry(Rc::as_ptr(alternative))
                            .or_default()
                            .extend(own.iter().cloned());
                    }
                }
                PackedNode::Production { children, .. }
                | PackedNode::InstantiatedProduction { children, .. } => {
                    for (index, child) in children.iter().enumerate() {
                        let mut set = own.clone();
                        for (other, sibling) in children.iter().enumerate() {
                            if other != index {
                                set.extend(self.variables[&Rc::as_ptr(sibling)].iter().cloned());
                            }
                        }
                        self.outside
                            .entry(Rc::as_ptr(child))
                            .or_default()
                            .extend(set);
                    }
                }
                PackedNode::Term(_) => {}
            }
        }
    }

    /// The semantic-cast production that records `sort` on a variable.
    fn semantic_cast(&mut self, sort: usize) -> Result<usize, ParseError> {
        if let Some(known) = self.semantic_casts.get(&sort) {
            return known.ok_or_else(|| missing_semantic_cast(self.index.sort(sort)));
        }
        let label = Label::semantic_cast(self.index.sort(sort)).name;
        let production =
            self.grammar
                .productions
                .iter()
                .enumerate()
                .find_map(|(index, production)| {
                    (production
                        .label
                        .as_ref()
                        .is_some_and(|candidate| candidate.name == label)
                        && super::production_arity(production) == 1)
                        .then_some(index)
                });
        self.semantic_casts.insert(sort, production);
        production.ok_or_else(|| missing_semantic_cast(self.index.sort(sort)))
    }

    fn strictly_exceeds(
        &self,
        k: usize,
        greater: &BTreeMap<TypingVariable, usize>,
        lesser: &BTreeMap<TypingVariable, usize>,
    ) -> bool {
        let mut distinct = false;
        for variable in greater.keys().chain(lesser.keys()) {
            let lesser = lesser.get(variable).copied().unwrap_or(k);
            let greater = greater.get(variable).copied().unwrap_or(k);
            if lesser != greater {
                if !self.index.le(lesser, greater) {
                    return false;
                }
                distinct = true;
            }
        }
        distinct
    }

    /// The summaries of `term`'s trees in `context`.
    fn summaries(
        &mut self,
        term: &Rc<PackedTerm>,
        context: Context,
    ) -> Result<Summaries, ParseError> {
        let key = (Rc::as_ptr(term), context);
        if let Some(known) = self.summaries.get(&key) {
            return Ok(Rc::clone(known));
        }
        let summaries = crate::stack::guarded(|| -> Result<_, ParseError> {
            let mut summaries = BTreeMap::new();
            match &term.node {
                PackedNode::Ambiguity(alternatives) => {
                    for alternative in alternatives {
                        for (summary, count) in self.summaries(alternative, context)?.iter() {
                            let total = summaries.entry(Rc::clone(summary)).or_insert(0);
                            *total = add(*total, *count);
                        }
                    }
                }
                PackedNode::Term(leaf) => {
                    if let Some(summary) = self.leaf_summary(leaf, context)? {
                        summaries.insert(Rc::new(summary), 1);
                    }
                }
                PackedNode::Production {
                    production,
                    children,
                    ..
                } => {
                    for class in self.classes(*production, children, context) {
                        let NodeEval::Node {
                            refused,
                            children: contexts,
                            ..
                        } = self.eval(*production, children, context, class)?
                        else {
                            continue;
                        };
                        let mut product = BTreeMap::from([(
                            Rc::new(Summary {
                                refused,
                                ..Summary::default()
                            }),
                            1u64,
                        )]);
                        for (child, child_context) in children.iter().zip(contexts) {
                            let child_summaries = self.summaries(child, child_context)?;
                            let mut next = BTreeMap::new();
                            for (left, left_count) in &product {
                                for (right, right_count) in child_summaries.iter() {
                                    if let Some(met) = left.meet(right) {
                                        let total = next.entry(Rc::new(met)).or_insert(0u64);
                                        *total =
                                            add(*total, left_count.saturating_mul(*right_count));
                                    }
                                }
                            }
                            product = next;
                            if product.is_empty() {
                                break;
                            }
                        }
                        for (summary, count) in product {
                            let total = summaries.entry(summary).or_insert(0);
                            *total = add(*total, count);
                        }
                    }
                }
                PackedNode::InstantiatedProduction { .. } => {
                    unreachable!("a forest is decided before inference")
                }
            }
            Ok(self.close(term, summaries))
        })?;
        let summaries = Rc::new(summaries);
        self.summaries.insert(key, Rc::clone(&summaries));
        Ok(summaries)
    }

    /// Drop the summaries whose typing of the variables that occur only in `term` another
    /// summary, equal on every other variable, strictly exceeds: whatever the rest of a tree,
    /// the tree through the other summary is well-sorted exactly when the tree through the
    /// dropped one is, and its typing strictly exceeds the dropped one's. The dropped trees are
    /// counted with the summary that exceeds them. Summaries with a refusal or an unidentified
    /// variable, and those whose closed variables have no greatest sort, are kept as they are.
    fn close(
        &mut self,
        term: &Rc<PackedTerm>,
        summaries: BTreeMap<Rc<Summary>, u64>,
    ) -> BTreeMap<Rc<Summary>, u64> {
        if summaries.len() < 2 {
            return summaries;
        }
        let outside = &self.outside[&Rc::as_ptr(term)];
        // Each comparable summary's open part and closed typing.
        let mut candidates = Vec::new();
        let mut kept = BTreeMap::new();
        for (summary, count) in summaries {
            if summary.refused || summary.unidentified {
                kept.insert(summary, count);
                continue;
            }
            let mut open = BTreeMap::new();
            let mut typing = BTreeMap::new();
            let mut comparable = true;
            for (variable, interval) in &summary.intervals {
                if outside.contains(variable) {
                    open.insert(variable.clone(), interval.clone());
                } else {
                    match self.index.realize(interval) {
                        Realized::One(sort) => {
                            typing.insert(variable.clone(), sort);
                        }
                        Realized::Several | Realized::Empty => comparable = false,
                    }
                }
            }
            if comparable && !typing.is_empty() {
                candidates.push((summary, count, open, typing));
            } else {
                kept.insert(summary, count);
            }
        }
        let k = self.index.k;
        let exceeds = |greater: usize, lesser: usize| {
            candidates[greater].2 == candidates[lesser].2
                && self.strictly_exceeds(k, &candidates[greater].3, &candidates[lesser].3)
        };
        // A summary some other exceeds is dropped and counted with a maximal one that exceeds it,
        // which exists since the order is finite and strict exceeding is transitive.
        let maximal = (0..candidates.len())
            .map(|index| !(0..candidates.len()).any(|other| exceeds(other, index)))
            .collect::<Vec<_>>();
        let mut absorbed = vec![0u64; candidates.len()];
        for index in (0..candidates.len()).filter(|index| !maximal[*index]) {
            let other = (0..candidates.len())
                .find(|other| maximal[*other] && exceeds(*other, index))
                .expect("a maximal summary exceeds every other");
            absorbed[other] = add(absorbed[other], candidates[index].1);
        }
        for (index, (summary, count, _, _)) in candidates.into_iter().enumerate() {
            if maximal[index] {
                kept.insert(summary, add(count, absorbed[index]));
            }
        }
        kept
    }

    /// The summary of one leaf in `context`, or `None` when the leaf is ill-sorted there.
    fn leaf_summary(
        &mut self,
        leaf: &Term,
        context: Context,
    ) -> Result<Option<Summary>, ParseError> {
        if let Some(class) = self.leaf_class_mismatch(leaf, context) {
            return Ok(class);
        }
        if let Some(name) = inferred_variable_name(leaf) {
            let interval = self.variable_occurrence(leaf, context);
            if interval.is_empty() {
                return Ok(None);
            }
            return Ok(Some(match typing_variable(leaf, name) {
                Some(variable) => Summary {
                    intervals: BTreeMap::from([(variable, interval)]),
                    ..Summary::default()
                },
                None => match self.index.realize(&interval) {
                    Realized::Empty => return Ok(None),
                    Realized::One(_) => Summary {
                        unidentified: true,
                        ..Summary::default()
                    },
                    Realized::Several => Summary {
                        unidentified: true,
                        refused: true,
                        ..Summary::default()
                    },
                },
            }));
        }
        let Term::Token { sort, .. } = leaf.unannotated() else {
            return Err(inference_error(
                "unexpected lowered KAST node in the concrete parse forest",
            ));
        };
        let sort = self.index.id(sort);
        Ok(self
            .result_checks(Outer::Sort(sort), context)
            .map(|refused| Summary {
                refused,
                ..Summary::default()
            }))
    }

    /// For a leaf at the left-hand side of a top rewrite, `Some(None)` when its tree has another
    /// class than the context keeps.
    fn leaf_class_mismatch(&mut self, leaf: &Term, context: Context) -> Option<Option<Summary>> {
        let Top::Lhs { class, outer } = context.top else {
            return None;
        };
        (self.leaf_class(leaf, outer) != class).then_some(None)
    }

    fn leaf_class(&mut self, leaf: &Term, outer: Option<Outer>) -> LhsClass {
        if matches!(leaf.unannotated(), Term::Variable { .. }) {
            return if self.explicitly_anywhere {
                LhsClass::Anywhere(Some(self.index.k))
            } else {
                LhsClass::Plain
            };
        }
        if !self.explicitly_anywhere {
            return LhsClass::Plain;
        }
        let own = match leaf.unannotated() {
            Term::Token { sort, .. } => Outer::Sort(self.index.id(sort)),
            _ => Outer::Parameter,
        };
        LhsClass::Anywhere(match outer.unwrap_or(own) {
            Outer::Sort(sort) => Some(sort),
            Outer::Parameter => None,
        })
    }

    /// The interval one occurrence of a variable allows, met with the interval every variable
    /// starts from.
    fn variable_occurrence(&mut self, leaf: &Term, context: Context) -> Sorts {
        let mut interval = self.index.variable_interval();
        let anonymous_leaf = context.exact
            && matches!(leaf.unannotated(), Term::Variable { name, .. } if is_anonymous(name));
        match context.expected {
            Expected::Sort { sort, .. } => {
                interval = interval.and(&self.index.down(sort));
                if anonymous_leaf {
                    interval = interval.and(&self.index.up(sort));
                }
            }
            Expected::Unbounded => {
                // An anonymous variable at an unbounded slot gives the slot the bound `K`, and
                // has the slot's sort; the slot is treated as unbounded only when some trees
                // put another node there, which refuses every lower bound not below `K`.
                if anonymous_leaf {
                    let k = self.index.k;
                    interval = interval.and(&self.index.up(k));
                }
            }
        }
        if let Some(pin) = context.pin {
            interval = interval.and(&self.index.up(pin));
        }
        interval
    }

    /// The constraints a node's parent puts on a node whose result is `result`: `None` when
    /// they fail, otherwise whether they need a refusal. A parameter result's constraints are
    /// checked by its production (`Self::eval`).
    fn result_checks(&mut self, result: Outer, context: Context) -> Option<bool> {
        let Outer::Sort(sort) = result else {
            return Some(false);
        };
        let mut refused = false;
        if context.widened != Some(sort) {
            match context.expected {
                Expected::Sort { sort: expected, .. } => {
                    if !self.index.le(sort, expected) {
                        return None;
                    }
                }
                Expected::Unbounded => refused |= !self.index.le(sort, self.index.k),
            }
        }
        if let Some(pin) = context.pin
            && self.index.domain(sort)
            && !self.index.le(pin, sort)
        {
            return None;
        }
        Some(refused)
    }

    /// The classes a production node is evaluated under: one `None`, or, at the top rewrite of
    /// a forest whose trees can make it an anywhere rule, one per class of its left-hand side.
    fn classes(
        &mut self,
        production: usize,
        children: &[Rc<PackedTerm>],
        context: Context,
    ) -> Vec<Option<LhsClass>> {
        if context.top != Top::Search || !self.is_top_rewrite(production, children) {
            return vec![None];
        }
        let mut classes = BTreeSet::new();
        self.lhs_classes(&children[0], None, &mut classes);
        if classes.len() == 1 && classes.contains(&LhsClass::Plain) {
            return vec![None];
        }
        classes.into_iter().map(Some).collect()
    }

    fn is_top_rewrite(&self, production: usize, children: &[Rc<PackedTerm>]) -> bool {
        self.grammar.productions[production]
            .label
            .as_ref()
            .is_some_and(|label| label.is(InternalLabel::KRewrite))
            && children.len() == 2
    }

    fn lhs_classes(
        &mut self,
        term: &Rc<PackedTerm>,
        outer: Option<Outer>,
        classes: &mut BTreeSet<LhsClass>,
    ) {
        crate::stack::guarded(|| match &term.node {
            PackedNode::Ambiguity(alternatives) => {
                for alternative in alternatives {
                    self.lhs_classes(alternative, outer, classes);
                }
            }
            PackedNode::Term(leaf) => {
                classes.insert(self.leaf_class(leaf, outer));
            }
            PackedNode::Production {
                production,
                children,
                ..
            } => {
                let outer = Some(outer.unwrap_or(self.production_result(*production)));
                if self.grammar.productions[*production].bracket && children.len() == 1 {
                    self.lhs_classes(&children[0], outer, classes);
                } else {
                    classes.insert(self.production_class(*production, outer));
                }
            }
            PackedNode::InstantiatedProduction { .. } => {
                unreachable!("a forest is decided before inference")
            }
        })
    }

    fn production_class(&self, production: usize, outer: Option<Outer>) -> LhsClass {
        let descriptor = &self.grammar.productions[production];
        if !(self.explicitly_anywhere || descriptor.function || descriptor.macro_like) {
            return LhsClass::Plain;
        }
        LhsClass::Anywhere(match outer {
            Some(Outer::Sort(sort)) => Some(sort),
            Some(Outer::Parameter) | None => None,
        })
    }

    fn production_result(&mut self, production: usize) -> Outer {
        let descriptor = &self.grammar.productions[production];
        match &descriptor.parametric_origin {
            Some(origin) if origin.parameters.contains(&origin.result) => Outer::Parameter,
            Some(origin) => Outer::Sort(self.index.id(&origin.result)),
            None => Outer::Sort(self.index.id(&descriptor.result)),
        }
    }

    /// A production node's constraints in `context`, under the top-rewrite class `class`
    /// (`Solver::infer` gives the constraints).
    fn eval(
        &mut self,
        production: usize,
        children: &[Rc<PackedTerm>],
        context: Context,
        class: Option<LhsClass>,
    ) -> Result<NodeEval, ParseError> {
        let grammar = self.grammar;
        let descriptor = &grammar.productions[production];
        // Each nonterminal's declared sort or parameter slot, and the result's.
        let (declared, actual) = match &descriptor.parametric_origin {
            Some(origin) => {
                let mut slot = |sort: &Sort| match origin.parameters.iter().position(|p| p == sort)
                {
                    Some(slot) => Err(slot),
                    None => Ok(self.index.id(sort)),
                };
                let declared = origin
                    .items
                    .iter()
                    .filter_map(|item| match item {
                        ProductionItem::NonTerminal { sort, .. } => Some(slot(sort)),
                        ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
                    })
                    .collect::<Vec<_>>();
                (declared, slot(&origin.result))
            }
            None => (
                descriptor
                    .items
                    .iter()
                    .filter_map(|item| match item {
                        Item::NonTerminal(sort) => Some(Ok(self.index.id(sort))),
                        Item::Terminal(_) | Item::Regex { .. } => None,
                    })
                    .collect::<Vec<_>>(),
                Ok(self.index.id(&descriptor.result)),
            ),
        };
        if declared.len() != children.len() {
            return Err(inference_error(format!(
                "production {:?} has {} nonterminals but its parse node has {} children",
                descriptor.parse_label,
                declared.len(),
                children.len()
            )));
        }
        let widened = descriptor
            .items
            .iter()
            .zip(&descriptor.item_sort_ids)
            .filter_map(|(item, sort_id)| match item {
                Item::NonTerminal(sort) => {
                    let parse = &grammar.sorts[sort_id.expect("nonterminal has a sort id")];
                    Some((parse != sort).then(|| self.index.id(parse)))
                }
                Item::Terminal(_) | Item::Regex { .. } => None,
            })
            .collect::<Vec<_>>();
        let slots = descriptor
            .parametric_origin
            .as_ref()
            .map_or(0, |origin| origin.parameters.len());
        let mut bases = vec![BTreeSet::new(); slots];
        let mut slot_pins = Vec::new();
        let mut refused = false;
        // The parent's constraint on this node, and the left-hand side filter.
        match actual {
            Ok(sort) => match self.result_checks(Outer::Sort(sort), context) {
                Some(refusal) => refused |= refusal,
                None => return Ok(NodeEval::Ill),
            },
            Err(slot) => {
                if let Expected::Sort { sort, exempts } = context.expected
                    && !exempts
                {
                    bases[slot].insert(sort);
                }
                if let Some(pin) = context.pin {
                    slot_pins.push((slot, pin));
                }
            }
        }
        let mut child_top = vec![Top::Off; children.len()];
        // The slot of the outermost node of a parametric left-hand side, which bounds the
        // rewrite of its anywhere rule.
        let mut lhs_slot = None;
        match context.top {
            Top::Off => {}
            Top::Search => {
                if let Some(class) = class {
                    child_top[0] = Top::Lhs { class, outer: None };
                } else if !self.is_top_rewrite(production, children) && !children.is_empty() {
                    let through = (descriptor.bracket && children.len() == 1)
                        || descriptor.result.is_frontend(FrontendSort::RuleContent)
                        || (descriptor.result.is_frontend(FrontendSort::RuleBody)
                            && descriptor
                                .label
                                .as_ref()
                                .is_some_and(|label| label.is(InternalLabel::WithConfig)));
                    if through {
                        child_top[0] = Top::Search;
                    }
                }
            }
            Top::Lhs { class, outer } => {
                if outer.is_none()
                    && class == LhsClass::Anywhere(None)
                    && let Err(slot) = actual
                {
                    lhs_slot = Some(slot);
                }
                let outer = Some(outer.unwrap_or(match actual {
                    Ok(sort) => Outer::Sort(sort),
                    Err(_) => Outer::Parameter,
                }));
                if descriptor.bracket && children.len() == 1 {
                    child_top[0] = Top::Lhs { class, outer };
                } else if self.production_class(production, outer) != class {
                    return Ok(NodeEval::Ill);
                }
            }
        }
        let anywhere_lhs = match class {
            Some(LhsClass::Anywhere(Some(sort))) => Some(sort),
            Some(LhsClass::Anywhere(None)) => None,
            Some(LhsClass::Plain) | None => None,
        };
        if let Some(lhs) = anywhere_lhs {
            match actual {
                Ok(sort) => {
                    if self.index.domain(sort) && !self.index.le(sort, lhs) {
                        return Ok(NodeEval::Ill);
                    }
                }
                Err(slot) => {
                    bases[slot].insert(lhs);
                }
            }
        }
        let cast = descriptor.label.as_ref().is_some_and(|label| {
            label.is(InternalLabel::SyntacticCast) || label.is(InternalLabel::SyntacticCastBraced)
        }) && !declared.is_empty();
        let mut child_pin = None;
        if cast {
            match (actual, declared[0]) {
                (Ok(result), Ok(inner)) => {
                    if !(self.index.le(result, inner) && self.index.le(inner, result)) {
                        return Ok(NodeEval::Ill);
                    }
                    child_pin = Some(inner);
                }
                _ => refused = true,
            }
        }
        // An anonymous variable at a slot's position gives the slot the upper bound `K`: in
        // every tree when one position holds one in every alternative, in some trees when one
        // position holds one in some alternative.
        let mut anonymous = vec![(false, false); slots];
        for (index, (child, declared)) in children.iter().zip(&declared).enumerate() {
            if let Err(slot) = declared
                && !(index == 1 && anywhere_lhs.is_some())
            {
                let (some, every) = anonymous_alternatives(child);
                anonymous[*slot].0 |= some;
                anonymous[*slot].1 |= every;
            }
        }
        let k = self.index.k;
        let k_bott = self.index.k_bott;
        let mut parameters = Vec::with_capacity(slots);
        for (slot, mut base) in bases.into_iter().enumerate() {
            let (some, every) = anonymous[slot];
            if every {
                base.insert(k);
            }
            if base.is_empty() {
                parameters.push(None);
                continue;
            }
            let interval = base
                .iter()
                .fold(None::<Sorts>, |met, sort| {
                    let below = self.index.down(*sort);
                    Some(match met {
                        Some(met) => met.and(&below),
                        None => below.into_owned(),
                    })
                })
                .expect("a nonempty base")
                .and_not(&self.index.down(k_bott));
            match self.index.realize(&interval) {
                Realized::Empty => return Ok(NodeEval::Ill),
                Realized::One(value) => {
                    // The trees with an anonymous variable there have `K` among the bounds too,
                    // which leaves the value unchanged only when it is below `K`.
                    refused |= some && !every && !self.index.le(value, k);
                    parameters.push(Some(value));
                }
                Realized::Several => {
                    refused = true;
                    parameters.push(interval.highest());
                }
            }
        }
        // The outermost node of a parametric left-hand side has the value its position gives
        // it unless its own positions bound it further, which the decision refuses: the
        // rewrite has already given its right-hand side that value (`lhs_parameter_value`).
        if let Some(slot) = lhs_slot {
            refused |= parameters[slot] != bounded_value(context.expected);
        }
        // A parametric left-hand side's slot bounds the rewrite from above and its right-hand
        // side; it has the value the left-hand side's position gives it, checked there.
        let mut rhs_expected = None;
        if class == Some(LhsClass::Anywhere(None)) {
            let value = match declared[0] {
                Ok(sort) => self.index.domain(sort).then_some(sort),
                Err(slot) => parameters[slot],
            };
            if let Ok(result) = actual
                && self.index.domain(result)
            {
                match value {
                    Some(value) => {
                        if !self.index.le(result, value) {
                            return Ok(NodeEval::Ill);
                        }
                    }
                    None => refused |= !self.index.le(result, k),
                }
            }
            // An anonymous right-hand side bounds the slot by `K` too.
            refused |= anonymous_alternatives(&children[1]).0
                && value.is_some_and(|value| !self.index.le(value, k));
            rhs_expected = Some(match value {
                Some(sort) => Expected::Sort {
                    sort,
                    exempts: false,
                },
                None => Expected::Unbounded,
            });
        }
        for (slot, pin) in slot_pins {
            match parameters[slot] {
                Some(value) => {
                    if !self.index.le(pin, value) {
                        return Ok(NodeEval::Ill);
                    }
                }
                None => refused |= !self.index.le(pin, k),
            }
        }
        let semantic_cast = descriptor
            .label
            .as_ref()
            .is_some_and(|label| {
                matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. }))
            })
            .then(|| self.index.id(&descriptor.result));
        let contexts = declared
            .iter()
            .enumerate()
            .map(|(index, declared)| {
                let mut expected = match declared {
                    Ok(sort) => Expected::Sort {
                        sort: *sort,
                        exempts: !self.index.domain(*sort),
                    },
                    Err(slot) => match parameters[*slot] {
                        Some(sort) => Expected::Sort {
                            sort,
                            exempts: false,
                        },
                        None => Expected::Unbounded,
                    },
                };
                let mut widened = widened.get(index).copied().flatten();
                if index == 1
                    && let Some(rhs) = rhs_expected
                {
                    expected = rhs;
                    widened = None;
                }
                if index == 1
                    && let Some(lhs) = anywhere_lhs
                {
                    expected = Expected::Sort {
                        sort: lhs,
                        exempts: !self.index.domain(lhs),
                    };
                    widened = None;
                }
                Context {
                    expected,
                    widened,
                    pin: if index == 0 { child_pin } else { None },
                    semantic_cast,
                    exact: true,
                    top: child_top[index],
                }
            })
            .collect();
        Ok(NodeEval::Node {
            refused,
            parameters,
            children: contexts,
        })
    }

    /// Among the kept alternatives of an ambiguity, the positions of the instances of a bracket
    /// family other than the instance at the value the context gives a parameter (the context's
    /// sort, or `K` where it bounds none), when that instance is kept too.
    ///
    /// A bracket's sort is not written: the parser reads `( t )` through the family's instance
    /// at every sort the position admits, and the readings are one reading, parsed exactly as
    /// without the brackets (`docs/compatibility.md`, "Formal parameter preference"), which puts
    /// `t` at the context. The instance at the context's value is that reading: its child is
    /// expected at the context's sort, so the instance admits every reading of `t` a smaller
    /// instance admits, and a parametric production directly inside it takes the value it takes
    /// without the brackets. A smaller instance would instead bound that production's parameter
    /// by its own sort, which no text states.
    fn shadowed_bracket_instances<'t>(
        &mut self,
        alternatives: impl Iterator<Item = &'t Rc<PackedTerm>>,
        context: Context,
    ) -> BTreeSet<usize> {
        let target = bounded_value(context.expected).unwrap_or(self.index.k);
        let mut families = BTreeMap::<Option<String>, Vec<(usize, bool)>>::new();
        for (index, alternative) in alternatives.enumerate() {
            let PackedNode::Production {
                production,
                children,
                ..
            } = &alternative.node
            else {
                continue;
            };
            let descriptor = &self.grammar.productions[*production];
            if !descriptor.bracket || children.len() != 1 || descriptor.parametric_origin.is_some()
            {
                continue;
            }
            let at_target = self.index.id(&descriptor.result) == target;
            families
                .entry(descriptor.parse_label.clone())
                .or_default()
                .push((index, at_target));
        }
        families
            .into_values()
            .filter(|members| members.len() > 1 && members.iter().any(|(_, at)| *at))
            .flat_map(|members| {
                members
                    .into_iter()
                    .filter(|(_, at)| !at)
                    .map(|(index, _)| index)
            })
            .collect()
    }

    /// The trees of `term` in `context` well-sorted under `typing`, built as the per-tree
    /// decision builds an inferred tree (`Grammar::insert_inferred_casts`), packed as `term`
    /// is, with up to two distinct instantiation lists of those trees; `None` when there are
    /// none.
    fn apply(
        &mut self,
        term: &Rc<PackedTerm>,
        context: Context,
        typing: &BTreeMap<TypingVariable, usize>,
        memo: &mut HashMap<(*const PackedTerm, Context), Applied>,
    ) -> Result<Applied, ParseError> {
        let key = (Rc::as_ptr(term), context);
        if let Some(known) = memo.get(&key) {
            return Ok(known.clone());
        }
        let applied = crate::stack::guarded(|| -> Result<Applied, ParseError> {
            match &term.node {
                PackedNode::Ambiguity(alternatives) => {
                    let mut applied = Vec::with_capacity(alternatives.len());
                    for alternative in alternatives {
                        if let Some(result) = self.apply(alternative, context, typing, memo)? {
                            applied.push((alternative, result));
                        }
                    }
                    let shadowed = self.shadowed_bracket_instances(
                        applied.iter().map(|(alternative, _)| *alternative),
                        context,
                    );
                    let mut kept = BTreeSet::new();
                    let mut instantiations = Vec::new();
                    for (index, (_, (applied, lists))) in applied.into_iter().enumerate() {
                        if !shadowed.contains(&index) {
                            match &applied.node {
                                PackedNode::Ambiguity(nested) => {
                                    kept.extend(nested.iter().cloned());
                                }
                                _ => {
                                    kept.insert(applied);
                                }
                            }
                            union_instantiations(&mut instantiations, lists);
                        }
                    }
                    Ok((!kept.is_empty()).then(|| (PackedTerm::ambiguity(kept), instantiations)))
                }
                PackedNode::Term(leaf) => {
                    if self.leaf_class_mismatch(leaf, context).is_some() {
                        return Ok(None);
                    }
                    let Some(name) = inferred_variable_name(leaf) else {
                        return Ok(self
                            .leaf_summary(leaf, context)?
                            .map(|_| (Rc::clone(term), vec![Rc::new(Vec::new())])));
                    };
                    let interval = self.variable_occurrence(leaf, context);
                    let sort = match typing_variable(leaf, name) {
                        Some(variable) => typing.get(&variable).copied().unwrap_or(self.index.k),
                        None => match self.index.realize(&interval) {
                            Realized::One(sort) => sort,
                            Realized::Empty | Realized::Several => return Ok(None),
                        },
                    };
                    if !interval.contains(sort) {
                        return Ok(None);
                    }
                    let built = if let Some(bound) = context.semantic_cast
                        && bound == sort
                    {
                        Rc::clone(term)
                    } else if context.semantic_cast.is_some()
                        && let Some(variable) =
                            variable_with_inferred_sort(leaf, self.index.sort(sort))
                    {
                        PackedTerm::leaf(variable)
                    } else {
                        let cast = self.semantic_cast(sort)?;
                        PackedTerm::production(cast, vec![Rc::clone(term)], TermMetadata::default())
                    };
                    Ok(Some((built, vec![Rc::new(Vec::new())])))
                }
                PackedNode::Production {
                    production,
                    children,
                    metadata,
                } => {
                    let mut built = BTreeSet::new();
                    let mut instantiations = Vec::new();
                    for class in self.classes(*production, children, context) {
                        let NodeEval::Node {
                            parameters,
                            children: contexts,
                            ..
                        } = self.eval(*production, children, context, class)?
                        else {
                            continue;
                        };
                        let mut applied_children = Vec::with_capacity(children.len());
                        let mut lists = vec![Rc::new(Vec::new())];
                        let mut complete = true;
                        for (child, child_context) in children.iter().zip(contexts) {
                            let Some((applied, child_lists)) =
                                self.apply(child, child_context, typing, memo)?
                            else {
                                complete = false;
                                break;
                            };
                            applied_children.push(applied);
                            lists = sum_instantiations(&lists, &child_lists);
                        }
                        if !complete {
                            continue;
                        }
                        let node = if self.grammar.productions[*production]
                            .parametric_origin
                            .is_some()
                        {
                            let values = parameters
                                .iter()
                                .map(|value| value.unwrap_or(self.index.k))
                                .collect::<Vec<_>>();
                            let own = Rc::new(vec![(*production, values.clone())]);
                            lists = sum_instantiations(&lists, &[own]);
                            PackedTerm::instantiated_production(
                                *production,
                                values
                                    .iter()
                                    .map(|value| self.index.sort(*value).clone())
                                    .collect(),
                                applied_children,
                                metadata.clone(),
                            )
                        } else if applied_children
                            .iter()
                            .zip(children)
                            .all(|(applied, child)| Rc::ptr_eq(applied, child))
                        {
                            Rc::clone(term)
                        } else {
                            PackedTerm::production(*production, applied_children, metadata.clone())
                        };
                        built.insert(node);
                        union_instantiations(&mut instantiations, lists);
                    }
                    Ok((!built.is_empty()).then(|| (PackedTerm::ambiguity(built), instantiations)))
                }
                PackedNode::InstantiatedProduction { .. } => {
                    unreachable!("a forest is decided before inference")
                }
            }
        })?;
        memo.insert(key, applied.clone());
        Ok(applied)
    }
}

/// The value of a parameter slot whose only bound is `expected`.
fn bounded_value(expected: Expected) -> Option<usize> {
    match expected {
        Expected::Sort {
            sort,
            exempts: false,
        } => Some(sort),
        Expected::Sort { exempts: true, .. } | Expected::Unbounded => None,
    }
}

/// Whether some and whether every alternative of `term` is an anonymous variable leaf.
fn anonymous_alternatives(term: &Rc<PackedTerm>) -> (bool, bool) {
    crate::stack::guarded(|| match &term.node {
        PackedNode::Term(leaf) => {
            let anonymous =
                matches!(leaf.unannotated(), Term::Variable { name, .. } if is_anonymous(name));
            (anonymous, anonymous)
        }
        PackedNode::Ambiguity(alternatives) => {
            alternatives
                .iter()
                .fold((false, true), |(some, all), alternative| {
                    let (one, every) = anonymous_alternatives(alternative);
                    (some || one, all && every)
                })
        }
        PackedNode::Production { .. } | PackedNode::InstantiatedProduction { .. } => (false, false),
    })
}

/// The identity of a variable occurrence across the trees of a forest, `None` for an anonymous
/// variable without a span.
fn typing_variable(leaf: &Term, name: &str) -> Option<TypingVariable> {
    if !is_anonymous(name) {
        return Some(TypingVariable::Named(name.to_owned()));
    }
    leaf.metadata()
        .and_then(|metadata| metadata.span)
        .map(|span| TypingVariable::Anonymous(span, name.to_owned()))
}

/// Add `lists` to `into`, keeping at most two distinct lists: two distinct lists below a node
/// give two distinct lists above it, since adding the same siblings to both keeps them apart.
fn union_instantiations(into: &mut Vec<Instantiations>, lists: Vec<Instantiations>) {
    for list in lists {
        if into.len() >= 2 {
            return;
        }
        if !into.contains(&list) {
            into.push(list);
        }
    }
}

/// Every sum of one list of `left` and one of `right`, at most two distinct.
fn sum_instantiations(left: &[Instantiations], right: &[Instantiations]) -> Vec<Instantiations> {
    let mut sums = Vec::new();
    for left in left {
        for right in right {
            let mut sum = Vec::with_capacity(left.len() + right.len());
            sum.extend(left.iter().cloned());
            sum.extend(right.iter().cloned());
            sum.sort_unstable();
            union_instantiations(&mut sums, vec![Rc::new(sum)]);
            if sums.len() >= 2 {
                return sums;
            }
        }
    }
    sums
}

fn missing_semantic_cast(sort: &Sort) -> ParseError {
    inference_error(format!(
        "cannot record inferred sort {sort}: missing semantic-cast production"
    ))
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};
    use std::rc::Rc;

    use proptest::prelude::*;

    use super::super::super::{Grammar, PackedTerm, ParametricOrigin, ParseError};
    use super::super::tests::assert_forest_decision_agrees;
    use crate::definition::{Attributes, ProductionItem};
    use crate::kast::{Label, Sort, Term, TermMetadata, TermSpan};

    fn nonterminal(sort: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(sort),
            name: None,
        }
    }

    /// The sorts of the generated grammar: a chain `Nat < Int < Exp < KItem < K`, `Bool < Exp`,
    /// `Lo` below `Int` and `Bool` (their one greatest common lower bound), and `Lo1`, `Lo2`
    /// below `Nat` and `Bool` (two of them).
    const SORTS: [&str; 9] = [
        "Nat", "Int", "Bool", "Exp", "KItem", "K", "Lo", "Lo1", "Lo2",
    ];

    /// A grammar with monomorphic productions over those sorts, a strict cast, a semantic cast
    /// per sort, a function, a bracket at four sorts, and the parametric `#And{S}: S ::= S S`, `#Ceil{S1, S2}: S2 ::= S1`
    /// and `#KRewrite{P}: P ::= P P`. Each production is listed with its arity.
    fn grammar() -> (Grammar, Vec<(usize, usize)>) {
        let mut grammar = Grammar::default();
        let mut productions = Vec::new();
        // Every production has a terminal, as a written one does: a production of one
        // nonterminal and nothing else would also state a subsort, here of a sort below itself.
        let mut add = |grammar: &mut Grammar, result: &str, items: &[&str], label: &str| {
            let index = grammar.productions.len();
            grammar
                .add(
                    Sort::new(result),
                    std::iter::once(ProductionItem::Terminal(label.into()))
                        .chain(items.iter().map(|sort| nonterminal(sort)))
                        .collect(),
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
            productions.push((index, items.len()));
            index
        };
        add(&mut grammar, "Int", &["Int", "Int"], "plus");
        add(&mut grammar, "Int", &["Int"], "neg");
        add(&mut grammar, "Bool", &["Bool"], "neg");
        add(&mut grammar, "Exp", &["Exp", "Exp"], "pair");
        add(&mut grammar, "KItem", &["K"], "wrap");
        add(&mut grammar, "Nat", &["Lo1"], "low");
        add(&mut grammar, "Bool", &["Lo2", "Int"], "mix");
        add(&mut grammar, "Int", &["Int"], "#SyntacticCast");
        let function = add(&mut grammar, "Int", &["Int"], "f");
        grammar.productions[function].function = true;
        for sort in SORTS {
            let index = grammar.productions.len();
            grammar
                .add(
                    Sort::new(sort),
                    vec![
                        nonterminal(sort),
                        ProductionItem::Terminal(format!(":{sort}")),
                    ],
                    Some(Label::semantic_cast(&Sort::new(sort))),
                    false,
                    false,
                )
                .unwrap();
            if sort == "Int" || sort == "Bool" {
                productions.push((index, 1));
            }
        }
        // A bracket family: one instance per sort, as `syntax {S} S ::= "(" S ")" [bracket]`
        // has in a grammar.
        for sort in ["Int", "Exp", "KItem", "K"] {
            let index = grammar.productions.len();
            grammar
                .add(
                    Sort::new(sort),
                    vec![
                        ProductionItem::Terminal("(".into()),
                        nonterminal(sort),
                        ProductionItem::Terminal(")".into()),
                    ],
                    None,
                    false,
                    true,
                )
                .unwrap();
            grammar.productions[index].bracket = true;
            grammar.productions[index].parse_label = Some("(_)".into());
        }
        let mut parametric = |grammar: &mut Grammar,
                              label: &str,
                              parameters: &[&str],
                              result: &str,
                              items: &[&str]| {
            let index = grammar.productions.len();
            grammar
                .add(
                    Sort::new("K"),
                    std::iter::once(ProductionItem::Terminal(label.into()))
                        .chain(items.iter().map(|_| nonterminal("K")))
                        .collect(),
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
            grammar.productions[index].parametric_origin = Some(ParametricOrigin {
                label: Some(Label::new(label)),
                parameters: parameters.iter().map(|sort| Sort::new(*sort)).collect(),
                result: Sort::new(result),
                items: std::iter::once(ProductionItem::Terminal(label.into()))
                    .chain(items.iter().map(|sort| nonterminal(sort)))
                    .collect(),
                attributes: Attributes::default(),
                substitution: parameters
                    .iter()
                    .map(|sort| (Sort::new(*sort), Sort::new("K")))
                    .collect::<BTreeMap<_, _>>(),
            });
            productions.push((index, items.len()));
        };
        parametric(&mut grammar, "#And", &["S"], "S", &["S", "S"]);
        parametric(&mut grammar, "#Ceil", &["S1", "S2"], "S2", &["S1"]);
        parametric(&mut grammar, "#KRewrite", &["P"], "P", &["P", "P"]);
        grammar.subsort_relations.extend(
            [
                ("Nat", "Int"),
                ("Int", "Exp"),
                ("Bool", "Exp"),
                ("Exp", "KItem"),
                ("KItem", "K"),
                ("Lo", "Int"),
                ("Lo", "Bool"),
                ("Lo1", "Nat"),
                ("Lo1", "Bool"),
                ("Lo2", "Nat"),
                ("Lo2", "Bool"),
            ]
            .map(|(lesser, greater)| (Sort::new(lesser), Sort::new(greater))),
        );
        (grammar, productions)
    }

    #[derive(Clone, Debug)]
    enum Tree {
        Leaf(u8),
        Node(u8, Vec<Tree>),
        Ambiguity(Vec<Tree>),
        /// `( t )` read through the bracket instances the mask selects (at least one), all
        /// over the one forest of `t`, as the parser reads one text at several instances.
        Bracket(u8, Box<Tree>),
    }

    fn tree() -> impl Strategy<Value = Tree> {
        (0u8..9)
            .prop_map(Tree::Leaf)
            .prop_recursive(5, 40, 3, |inner| {
                prop_oneof![
                    3 => (any::<u8>(), prop::collection::vec(inner.clone(), 1..3))
                        .prop_map(|(production, children)| Tree::Node(production, children)),
                    2 => prop::collection::vec(inner.clone(), 2..4).prop_map(Tree::Ambiguity),
                    1 => (1u8..16, inner).prop_map(|(mask, child)| Tree::Bracket(mask, Box::new(child))),
                ]
            })
    }

    /// The forest of `tree`: a leaf is a variable `X`, `Y`, `Z`, an anonymous variable with or
    /// without a span, or a token; a node applies a production of its arity.
    fn pack(
        tree: &Tree,
        productions: &[(usize, usize)],
        brackets: &[usize],
        next_span: &mut usize,
    ) -> Rc<PackedTerm> {
        match tree {
            Tree::Leaf(leaf) => PackedTerm::leaf(match leaf {
                0 => Term::variable("X"),
                1 | 2 => Term::variable("Y"),
                3 => Term::variable("Z"),
                4 | 5 => {
                    *next_span += 1;
                    Term::variable("_").with_metadata(TermMetadata {
                        span: Some(TermSpan {
                            source: crate::provenance::SourceId(0),
                            start: *next_span,
                            end: *next_span + 1,
                        }),
                        ..TermMetadata::default()
                    })
                }
                6 => Term::Token {
                    token: "1".into(),
                    sort: Sort::new("Int"),
                },
                7 => Term::Token {
                    token: "true".into(),
                    sort: Sort::new("Bool"),
                },
                _ => Term::variable("_"),
            }),
            Tree::Node(production, children) => {
                let candidates = productions
                    .iter()
                    .filter(|(_, arity)| *arity == children.len())
                    .collect::<Vec<_>>();
                let (production, _) = candidates[usize::from(*production) % candidates.len()];
                PackedTerm::production(
                    *production,
                    children
                        .iter()
                        .map(|child| pack(child, productions, brackets, next_span))
                        .collect(),
                    TermMetadata::default(),
                )
            }
            // An ambiguity reads one text, so it holds at most one bracket reading; the others
            // would read other texts at the same span.
            Tree::Ambiguity(alternatives) => PackedTerm::ambiguity(
                alternatives
                    .iter()
                    .enumerate()
                    .filter(|(index, alternative)| {
                        !matches!(alternative, Tree::Bracket(..))
                            || !alternatives[..*index]
                                .iter()
                                .any(|earlier| matches!(earlier, Tree::Bracket(..)))
                    })
                    .map(|(_, alternative)| pack(alternative, productions, brackets, next_span))
                    .collect::<BTreeSet<_>>(),
            ),
            Tree::Bracket(mask, child) => {
                let child = pack(child, productions, brackets, next_span);
                PackedTerm::ambiguity(
                    brackets
                        .iter()
                        .enumerate()
                        .filter(|(bit, _)| mask & (1 << bit) != 0)
                        .map(|(_, bracket)| {
                            PackedTerm::production(
                                *bracket,
                                vec![Rc::clone(&child)],
                                TermMetadata::default(),
                            )
                        })
                        .collect(),
                )
            }
        }
    }

    /// The variables of a tree, each with its span; `None` when it applies a function, which
    /// can make it an anywhere rule.
    #[cfg(feature = "z3-inference")]
    fn variables(
        grammar: &Grammar,
        tree: &super::super::super::ParsedTerm,
    ) -> Option<BTreeSet<(String, Option<TermSpan>)>> {
        use super::super::super::ParsedTerm;
        let mut found = BTreeSet::new();
        let mut pending = vec![tree];
        while let Some(term) = pending.pop() {
            match term {
                ParsedTerm::Term(leaf) => {
                    if let Some(name) = super::super::super::inferred_variable_name(leaf) {
                        found.insert((name.to_owned(), leaf.metadata().and_then(|m| m.span)));
                    }
                }
                ParsedTerm::Production {
                    production,
                    children,
                    ..
                }
                | ParsedTerm::InstantiatedProduction {
                    production,
                    children,
                    ..
                } => {
                    if grammar.productions[*production].function {
                        return None;
                    }
                    pending.extend(children);
                }
                ParsedTerm::Ambiguity(alternatives) => pending.extend(alternatives),
            }
        }
        Some(found)
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        /// The forest decision keeps the trees the per-tree decision keeps, on forests with
        /// subsorts, casts, functions, parametric productions, anonymous and shared variables
        /// (`Grammar::check_forest_decision` compares them inside the decision).
        #[test]
        fn the_forest_decision_agrees_with_the_per_tree_decision(
            tree in tree(),
            top in 0usize..4,
            anywhere in any::<bool>(),
        ) {
            let (grammar, productions) = grammar();
            prop_assert!(grammar.subsort_relations.order().is_ok());
            prop_assert!(grammar.syntactic_subsort_relations.order().is_ok());
            let brackets = (0..grammar.productions.len())
                .filter(|index| grammar.productions[*index].bracket)
                .collect::<Vec<_>>();
            let forest = pack(&tree, &productions, &brackets, &mut 0);
            // The trees read one at a time are the expanded trees, in order.
            prop_assert_eq!(
                super::super::packed_trees(&forest)
                    .expect("a generated forest has few trees")
                    .collect::<Vec<_>>(),
                super::super::expand_packed_trees(&forest)
            );
            let top = Sort::new(["K", "Int", "Exp", "Bool"][top]);
            assert_forest_decision_agrees(&grammar, &forest, &top, anywhere);
            // Each kept group's trees lowered each alone on the forest, as the parameter split
            // reads them, against each tree built and lowered alone.
            let lower = super::super::super::InferredLowering {
                grammar: &grammar,
                start: &top,
            };
            let required = || ParseError::Z3InferenceRequired {
                ambiguity: true,
                parametric_sorts: false,
            };
            for group in grammar
                .decide_forest(&forest, &top, anywhere, &required)
                .into_iter()
                .flatten()
            {
                let each = grammar.lower_each_inferred_tree(&group.term, &top);
                let alone = super::super::lower_each_tree_by_listing(&lower, &group.term);
                prop_assert!(
                    match (&each, &alone) {
                        (Some(each), Some(alone)) => each.identical(alone),
                        (None, None) => true,
                        _ => false,
                    },
                    "{each:?}\n{alone:?}"
                );
            }
            // Z3 compares typings over the variables of the whole forest, while the portable
            // decision gives a variable absent from a tree the top sort there, and Z3 does not
            // decide an anywhere rule whose left-hand side is ambiguous; so the engines are
            // compared on forests whose trees all have the same variables, of rules that are
            // not anywhere rules.
            #[cfg(feature = "z3-inference")]
            if !anywhere
                && super::super::expand_packed_trees(&forest)
                    .iter()
                    .map(|tree| variables(&grammar, tree))
                    .collect::<Option<BTreeSet<_>>>()
                    .is_some_and(|sets| sets.len() == 1)
                && let Some(checked) =
                    grammar.checked_ambiguous_parse(&forest, &top, anywhere, &lower)
            {
                prop_assert!(
                    !matches!(checked, Err(ParseError::InferenceEngineDisagreement { .. })),
                    "{checked:?}"
                );
            }
        }
    }
}

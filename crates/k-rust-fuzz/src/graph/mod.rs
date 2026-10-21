//! The rule enablement graph (ARCHITECTURE 6.3): rewrite rules as nodes, and an edge from rule
//! A to rule B when B's left-hand side may match a configuration that A's right-hand side
//! produces.
//!
//! # Edges
//!
//! The backend selects the candidate rules of a step by keys: the subject's root, and the head
//! of its one `<k>` cell with the item after it (`k_rust_backend::rule`, "single-symbol rule
//! selection"). A rule is tried on a configuration only when its left-hand side's keys
//! (`IndexedRewriteRule::index`) cover the configuration's subject-side keys (`subject_index`).
//! The configuration after a step of A is an instance of A's right-hand side, after its function
//! applications are evaluated and its `anywhere` heads normalized. The graph therefore keys A's
//! right-hand side on the subject side, where everything that evaluation may still change keys
//! nothing: a variable, a function application, and an `anywhere` head that equations may
//! rewrite are `Anything` there, while the rule-side key would read an `anywhere` head as rigid
//! (`CellIndex::Anywhere`) and miss the rules its equations enable.
//!
//! A term that keys nothing still has a sort, and the value it denotes has that sort: a function
//! application denotes a value of the function's result sort, an `anywhere` head the value of its
//! normal form, of the production's sort, and a variable a value of its declared sort. At each
//! keyed position (the `<k>` head and the item after it), B's left-hand side has a rigid key
//! there (a constructor, a domain value or a collection) only when its term there has a root
//! that a matching value must have, and such a value is injected from the root's sort. So B can
//! match only if the sort of its term there is a subsort of the sort of A's term there; the graph
//! adds that filter to the key test. Overloaded and `anywhere` keys of B are not filtered, since
//! overload resolution may change the root's production and with it the sort.
//!
//! The subject's root is keyed as the backend keys it: when A's right-hand side has a free
//! constructor at the root, every instance keeps that root, and only B stored under that root's
//! bucket or the `Variable` bucket is tried.
//!
//! Both tests are necessary conditions for B to apply to a successor of A, so the graph
//! over-approximates the enablement relation; it never claims that B fires. It ignores
//! priorities, conditions and `owise`.
//!
//! # More than one `<k>` cell
//!
//! The keys follow one `<k>` cell. When some rule's left- or right-hand side holds a `<k>` cell
//! inside a collection (a cell of multiplicity `*`) or more than one `<k>` cell, consecutive steps
//! may rewrite different cells, so a right-hand side's cell says nothing about the cell the next
//! step reads. In such a definition every right-hand side keys its cells as `Anything` (only
//! the root is keyed), and the `statically-unreachable` warning is withheld.
//!
//! # Use
//!
//! The graph is a scheduling heuristic, never evidence. Its consumers are the guidance
//! proposers: the dictionary (ARCHITECTURE 8.3) reads the rules within a radius of the target
//! ([`RuleGraph::distances_to`]) and the functions their conditions call
//! ([`RuleGraph::requires_functions`], [`FunctionCalls`]); the climb (8.4) scores a case by
//! the distance from the rules it applied to the target, read from one
//! [`RuleGraph::distances_to`] computed per campaign. On real definitions many rules end with a
//! bare continuation in `<k>` (`=> .K ...`), which enables every rule, so distances there are
//! mostly 1 or 2; the proposers should not be tuned on the GRAPH fixture alone.
//!
//! The campaign computes one [`entry::Entry`] from the hole template ([`RuleGraph::entry`],
//! [`entry::hole_template`]), reports an unreachable target as a warning
//! ([`RuleGraph::statically_unreachable`]) and continues, and checks every case's coverage
//! against the same entry ([`RuleGraph::unreachable_applied`]); a violation is an engine defect.
//!
//! Every output is ordered (rule ids are sorted, sets are `BTreeSet`s), so the graph and every
//! answer are a function of the definition.

mod calls;
pub(crate) mod entry;
#[cfg(test)]
mod tests;

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::atomic::{AtomicU64, Ordering},
};

pub(crate) use calls::FunctionCalls;
use calls::Part;
use sha2::{Digest as _, Sha256};

use k_rust::{
    backend::{Backend, BackendError},
    k_rust_backend::{
        definition::BackendDefinition,
        rule::{
            CellIndex, ClassifiedAxiom, IndexedRewriteRule, RuleIndex, RuleRhs, SubjectKey,
            TermIndex, subject_index, term_index,
        },
        term::{HeadRole, Sort, Term, TermKind},
    },
    names::WellKnownSymbol,
};

/// The source of [`RuleGraph::identity`].
static NEXT_GRAPH: AtomicU64 = AtomicU64::new(0);

/// The rule enablement graph of one definition, built once per definition.
#[derive(Clone, Debug)]
pub(crate) struct RuleGraph {
    /// The rule ids, sorted; a node is an index into this list. Rules that share an id (a
    /// collapsed axiom, the generated `UNKNOWN`) are one node, as coverage records them.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the guidance API of the dictionary and climb proposers (ARCHITECTURE 8.3, 8.4), which M1 does not provide; the graph tests use it"
        )
    )]
    ids: Vec<String>,
    /// The node of each id.
    nodes: BTreeMap<String, usize>,
    /// The executable rewrite rules of each node, in the rewrite theory's order.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the guidance API of the dictionary and climb proposers (ARCHITECTURE 8.3, 8.4), which M1 does not provide; the graph tests use it"
        )
    )]
    rules: Vec<Vec<IndexedRewriteRule>>,
    /// The left-hand-side keys of every executable rule, with its node.
    targets: Vec<Target>,
    /// The nodes each node enables, and the nodes that enable it.
    successors: Vec<BTreeSet<usize>>,
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the guidance API of the dictionary and climb proposers (ARCHITECTURE 8.3, 8.4), which M1 does not provide; the graph tests use it"
        )
    )]
    predecessors: Vec<BTreeSet<usize>>,
    /// Some rule holds a `<k>` cell inside a collection or more than one `<k>` cell.
    shared_k: bool,
    /// The function-call edges of the definition's function theory.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the guidance API of the dictionary and climb proposers (ARCHITECTURE 8.3, 8.4), which M1 does not provide; the graph tests use it"
        )
    )]
    calls: FunctionCalls,
    /// The ids of the definition's equations (function, simplification and definedness
    /// axioms, `BackendDefinition::classified_axioms`), which coverage also names.
    equation_ids: BTreeSet<String>,
    /// The definition's main module and a digest of its axioms' ids and kinds
    /// ([`definition_fingerprint`]), which an entry's definition must match.
    fingerprint: [u8; 32],
    /// Distinguishes this graph from every other built in the process, so that an [`entry::Entry`]
    /// is used only with the graph that computed it. A clone keeps it, being the same graph.
    identity: u64,
}

/// One executable rule's left-hand-side keys.
#[derive(Clone, Debug)]
struct Target {
    node: usize,
    /// The rewrite theory's bucket of the rule: the left-hand side's term index.
    bucket: TermIndex,
    index: RuleIndex,
    /// At each cell position (the `<k>` head, the item after it) where the rule's key is rigid
    /// and its term there has a root, that term's sort.
    rigid_sorts: [Option<Sort>; 2],
}

/// What a configuration, or the right-hand side of a rule, offers the next step's selection.
#[derive(Clone, Debug)]
struct Subject {
    /// The root's bucket when the root is a free constructor, which every instance keeps.
    fixed_root: Option<TermIndex>,
    /// The subject-side cell keys and, at each position, the sort of the term there; `None`
    /// when the cells are not keyed (more than one `<k>` cell may exist, or the right-hand side
    /// has no term).
    cells: Option<(SubjectKey, [Option<Sort>; 2])>,
}

impl Subject {
    /// A subject that every rule may match.
    const OPEN: Self = Self {
        fixed_root: None,
        cells: None,
    };
}

/// The edge test over one definition, with its subsort answers cached.
struct Selection<'d> {
    definition: &'d BackendDefinition,
    shared_k: bool,
    subsorts: BTreeMap<(Sort, Sort), bool>,
}

impl<'d> Selection<'d> {
    fn new(definition: &'d BackendDefinition, shared_k: bool) -> Self {
        Self {
            definition,
            shared_k,
            subsorts: BTreeMap::new(),
        }
    }

    fn subject(&self, term: &Term) -> Subject {
        let fixed_root = match term.kind() {
            TermKind::Application { symbol, .. }
                if symbol.attributes.head_role() == HeadRole::FreeConstructor =>
            {
                Some(TermIndex::Symbol(symbol.name.clone()))
            }
            _ => None,
        };
        let cells = (!self.shared_k).then(|| {
            let sorts = cell_terms(term).map(|position| position.map(|at| unwrapped(at).sort()));
            (subject_index(self.definition, term), sorts)
        });
        Subject { fixed_root, cells }
    }

    /// Whether `target`'s rule may match a configuration `subject` describes.
    fn enables(&mut self, subject: &Subject, target: &Target) -> bool {
        if let Some(root) = &subject.fixed_root
            && target.bucket != *root
            && target.bucket != TermIndex::Variable
        {
            return false;
        }
        let Some((key, sorts)) = &subject.cells else {
            return true;
        };
        if !target.index.covers(key) {
            return false;
        }
        target.rigid_sorts.iter().zip(sorts).all(|pair| match pair {
            (Some(rigid), Some(sort)) => self.subsort(*rigid, *sort),
            _ => true,
        })
    }

    /// `sub` is a subsort of `sup`; an undecidable question (a sort variable) answers yes.
    fn subsort(&mut self, sub: Sort, sup: Sort) -> bool {
        let definition = self.definition;
        *self.subsorts.entry((sub, sup)).or_insert_with(|| {
            definition
                .sort_graph()
                .check_subsort(&sub, &sup)
                .unwrap_or(true)
        })
    }
}

impl RuleGraph {
    /// The graph of `definition`'s executable rewrite rules
    /// (`BackendDefinition::rewrite_theory()`), with the function-call edges of its function
    /// theory.
    pub(crate) fn new(definition: &BackendDefinition) -> Self {
        let mut by_id: BTreeMap<String, Vec<IndexedRewriteRule>> = BTreeMap::new();
        for groups in definition.rewrite_theory().values() {
            for rules in groups.values() {
                for rule in rules {
                    // A non-executable rule never applies, so it enables nothing and nothing
                    // enables it.
                    if rule.attributes.executable {
                        by_id
                            .entry(rule.attributes.unique_id.clone())
                            .or_default()
                            .push(rule.clone());
                    }
                }
            }
        }
        let ids: Vec<String> = by_id.keys().cloned().collect();
        let nodes: BTreeMap<String, usize> = ids
            .iter()
            .enumerate()
            .map(|(node, id)| (id.clone(), node))
            .collect();
        let rules: Vec<Vec<IndexedRewriteRule>> = by_id.into_values().collect();
        let shared_k = rules.iter().flatten().any(|rule| {
            shares_k(&rule.lhs) || right_hand_terms(&rule.rhs).into_iter().any(shares_k)
        });
        let targets: Vec<Target> = rules
            .iter()
            .enumerate()
            .flat_map(|(node, rules)| {
                rules.iter().map(move |rule| Target {
                    node,
                    bucket: term_index(&rule.lhs),
                    index: rule.index.clone(),
                    rigid_sorts: rigid_sorts(&rule.lhs, &rule.index),
                })
            })
            .collect();
        let equation_ids = equation_ids(definition);
        let mut selection = Selection::new(definition, shared_k);
        let mut successors = vec![BTreeSet::new(); ids.len()];
        let mut predecessors = vec![BTreeSet::new(); ids.len()];
        for (node, node_rules) in rules.iter().enumerate() {
            for rule in node_rules {
                for subject in right_hand_subjects(&selection, &rule.rhs) {
                    for target in &targets {
                        if !successors[node].contains(&target.node)
                            && selection.enables(&subject, target)
                        {
                            successors[node].insert(target.node);
                            predecessors[target.node].insert(node);
                        }
                    }
                }
            }
        }
        Self {
            ids,
            nodes,
            rules,
            targets,
            successors,
            predecessors,
            shared_k,
            calls: FunctionCalls::new(definition),
            equation_ids,
            fingerprint: definition_fingerprint(definition),
            identity: NEXT_GRAPH.fetch_add(1, Ordering::Relaxed),
        }
    }

    /// The graph of `backend`'s default module.
    ///
    /// # Errors
    ///
    /// When the backend cannot select its definition.
    pub(crate) fn of_backend(backend: &mut Backend) -> Result<Self, BackendError> {
        backend.with_solver_over(None, &[], |definition, _| Ok(Self::new(definition)))
    }

    /// Whether `definition` is the one the graph was built from.
    fn is_definition_of(&self, definition: &BackendDefinition) -> bool {
        definition_fingerprint(definition) == self.fingerprint
    }
}

/// The guidance API: rule lookup, edges, distances and the functions a rule calls, for the
/// proposers that read the graph (module documentation, "Use").
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "the guidance API of the dictionary and climb proposers (ARCHITECTURE 8.3, 8.4), which M1 does not provide; the graph tests use it"
    )
)]
impl RuleGraph {
    /// The rule ids, sorted.
    pub(crate) fn rule_ids(&self) -> impl Iterator<Item = &str> {
        self.ids.iter().map(String::as_str)
    }

    /// Whether `id` names an executable rewrite rule of the graph (equations are no nodes).
    pub(crate) fn contains(&self, id: &str) -> bool {
        self.nodes.contains_key(id)
    }

    /// The executable rewrite rules with id `id`, with their left-hand-side keys; empty for an
    /// id that is no node.
    pub(crate) fn rules(&self, id: &str) -> &[IndexedRewriteRule] {
        self.nodes
            .get(id)
            .map_or(&[], |node| self.rules[*node].as_slice())
    }

    /// Whether a step of `from` may enable `to`.
    pub(crate) fn has_edge(&self, from: &str, to: &str) -> bool {
        match (self.nodes.get(from), self.nodes.get(to)) {
            (Some(from), Some(to)) => self.successors[*from].contains(to),
            _ => false,
        }
    }

    /// Every edge, ordered by source id, then target id.
    pub(crate) fn edges(&self) -> Vec<(String, String)> {
        self.successors
            .iter()
            .enumerate()
            .flat_map(|(from, targets)| {
                targets
                    .iter()
                    .map(move |to| (self.ids[from].clone(), self.ids[*to].clone()))
            })
            .collect()
    }

    /// The rules a step of `id` may enable.
    pub(crate) fn successors(&self, id: &str) -> BTreeSet<String> {
        self.nodes
            .get(id)
            .map(|node| self.named(&self.successors[*node]))
            .unwrap_or_default()
    }

    /// The rules whose step may enable `id`: its direct predecessors.
    pub(crate) fn enablers(&self, id: &str) -> BTreeSet<String> {
        self.nodes
            .get(id)
            .map(|node| self.named(&self.predecessors[*node]))
            .unwrap_or_default()
    }

    /// For every rule from which `target` is reachable, the least number of edges from it to
    /// `target` (`target` itself at 0); empty when `target` is no node.
    pub(crate) fn distances_to(&self, target: &str) -> BTreeMap<String, usize> {
        let Some(&target) = self.nodes.get(target) else {
            return BTreeMap::new();
        };
        let mut distances = vec![None; self.ids.len()];
        distances[target] = Some(0);
        let mut queue = VecDeque::from([target]);
        while let Some(node) = queue.pop_front() {
            let next = distances[node].map_or(0, |distance: usize| distance + 1);
            for &predecessor in &self.predecessors[node] {
                if distances[predecessor].is_none() {
                    distances[predecessor] = Some(next);
                    queue.push_back(predecessor);
                }
            }
        }
        distances
            .into_iter()
            .enumerate()
            .filter_map(|(node, distance)| {
                distance.map(|distance| (self.ids[node].clone(), distance))
            })
            .collect()
    }

    /// The least number of edges from `from` to `to`, `None` when `to` is unreachable from it.
    ///
    /// Each call runs a breadth-first search over the whole graph; a consumer that scores many
    /// cases against one target (the climb) computes [`Self::distances_to`] once per campaign
    /// and looks the applied rules up in it.
    pub(crate) fn distance(&self, from: &str, to: &str) -> Option<usize> {
        self.distances_to(to).get(from).copied()
    }

    /// The function-call edges of the definition's function theory.
    pub(crate) fn calls(&self) -> &FunctionCalls {
        &self.calls
    }

    /// The symbols with equations that the rule `id` applies in its `requires`, right-hand side
    /// or `ensures`, and those their equations apply, transitively.
    pub(crate) fn called_functions(&self, id: &str) -> BTreeSet<String> {
        self.functions(id, Part::All)
    }

    /// The symbols with equations that the rule `id`'s `requires` applies, and those their
    /// equations apply, transitively: the equations whose conditions the dictionary harvests
    /// for the rule (ARCHITECTURE 8.3).
    pub(crate) fn requires_functions(&self, id: &str) -> BTreeSet<String> {
        self.functions(id, Part::Requires)
    }

    fn functions(&self, id: &str, part: Part) -> BTreeSet<String> {
        let mut called = BTreeSet::new();
        for rule in self.rules(id) {
            self.calls.collect_rule(rule, part, &mut called);
        }
        self.calls.closure(called)
    }

    fn named(&self, nodes: &BTreeSet<usize>) -> BTreeSet<String> {
        nodes.iter().map(|node| self.ids[*node].clone()).collect()
    }
}

/// The subjects a step of a rule with right-hand side `rhs` may produce: one per term
/// alternative, none for `\bottom`, and an open subject for a right-hand side without a term.
fn right_hand_subjects(selection: &Selection<'_>, rhs: &RuleRhs) -> Vec<Subject> {
    match rhs {
        RuleRhs::Term(_) | RuleRhs::Disjunction(_) => right_hand_terms(rhs)
            .into_iter()
            .map(|term| selection.subject(term))
            .collect(),
        RuleRhs::Bottom => Vec::new(),
        RuleRhs::Top | RuleRhs::Predicates(_) => vec![Subject::OPEN],
    }
}

fn right_hand_terms(rhs: &RuleRhs) -> Vec<&Term> {
    match rhs {
        RuleRhs::Term(term) => vec![term],
        RuleRhs::Disjunction(alternatives) => alternatives
            .iter()
            .map(|alternative| &alternative.term)
            .collect(),
        RuleRhs::Top | RuleRhs::Bottom | RuleRhs::Predicates(_) => Vec::new(),
    }
}

/// At each cell position of `lhs` where `index` is rigid (a constructor, a domain value or a
/// collection), the sort of the term there whose root gave the key ([`rooted`]): a value that
/// matches it has that root, at that sort.
fn rigid_sorts(lhs: &Term, index: &RuleIndex) -> [Option<Sort>; 2] {
    let terms = cell_terms(lhs);
    let mut sorts = [None, None];
    for (position, sort) in sorts.iter_mut().enumerate() {
        let rigid = matches!(
            index.cells().get(position),
            Some(
                CellIndex::Constructor(_)
                    | CellIndex::Value(_)
                    | CellIndex::Map
                    | CellIndex::List
                    | CellIndex::Set
            )
        );
        *sort = terms[position]
            .filter(|_| rigid)
            .zip(index.cells().get(position))
            .and_then(|(term, key)| rooted(term, key))
            .map(Term::sort);
    }
    sorts
}

/// The term under `term`'s injections and conjunctions whose root gave the rigid key `key`: an
/// application of the key's constructor, the key's domain value, or a collection of the key's
/// kind. A conjunction (an `#as` pattern) matches a value only if each conjunct does, and its
/// key is the meet of the conjuncts' keys (`CellIndex::meet`), so a rigid key comes from a
/// conjunct with that root; a matching value has that root, at that conjunct's sort. `None`
/// when no conjunct agrees with the key, or two of different sorts do.
fn rooted<'t>(term: &'t Term, key: &CellIndex) -> Option<&'t Term> {
    let mut found: Vec<&Term> = Vec::new();
    agreeing(term, key, &mut found);
    let (first, rest) = found.split_first()?;
    rest.iter()
        .all(|other| other.sort() == first.sort())
        .then_some(*first)
}

fn agreeing<'t>(term: &'t Term, key: &CellIndex, found: &mut Vec<&'t Term>) {
    let agrees = match (term.kind(), key) {
        (TermKind::Injection { term, .. }, _) => return agreeing(term, key, found),
        (TermKind::And(left, right), _) => {
            agreeing(left, key, found);
            agreeing(right, key, found);
            return;
        }
        (TermKind::Application { symbol, .. }, CellIndex::Constructor(name)) => {
            symbol.name == *name
        }
        (TermKind::DomainValue { value, .. }, CellIndex::Value(written)) => value == written,
        (TermKind::Map { .. }, CellIndex::Map)
        | (TermKind::List { .. }, CellIndex::List)
        | (TermKind::Set { .. }, CellIndex::Set) => true,
        _ => false,
    };
    if agrees {
        found.push(term);
    }
}

/// A digest of `definition`'s main module and of the id and kind of each of its axioms, in the
/// definition's order.
fn definition_fingerprint(definition: &BackendDefinition) -> [u8; 32] {
    let mut digest = Sha256::new();
    digest.update(definition.main_module().as_bytes());
    for axiom in definition.classified_axioms() {
        let kind: &[u8] = match axiom {
            ClassifiedAxiom::Rewrite { .. } => b"\nr ",
            _ => b"\ne ",
        };
        digest.update(kind);
        digest.update(axiom.attributes().unique_id.as_bytes());
    }
    digest.finalize().into()
}

/// The ids of the definition's axioms other than rewrite rules.
fn equation_ids(definition: &BackendDefinition) -> BTreeSet<String> {
    definition
        .classified_axioms()
        .iter()
        .filter(|axiom| !matches!(axiom, ClassifiedAxiom::Rewrite { .. }))
        .map(|axiom| axiom.attributes().unique_id.clone())
        .collect()
}

/// The terms the backend's cell keys are computed from: the head of the one `<k>` cell not
/// nested in a `<k>` cell, when its contents are `kseq(head, _)` or `.K`, and the item after
/// the head, when the contents are `kseq(head, kseq(next, _))`. Both `None` when `term` has no
/// such cell or several.
fn cell_terms(term: &Term) -> [Option<&Term>; 2] {
    if term.attributes().k_cells() != 1 {
        return [None, None];
    }
    let Some(TermKind::Application { arguments, .. }) = first_k_cell(term).map(Term::kind) else {
        return [None, None];
    };
    let [contents] = arguments.as_slice() else {
        return [None, None];
    };
    match contents.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } if symbol.is(WellKnownSymbol::KSeq) => {
            let [head, tail] = arguments.as_slice() else {
                return [None, None];
            };
            let next = match tail.kind() {
                TermKind::Application {
                    symbol, arguments, ..
                } if symbol.is(WellKnownSymbol::KSeq) => match arguments.as_slice() {
                    [next, _rest] => Some(next),
                    _ => None,
                },
                _ => None,
            };
            [Some(head), next]
        }
        TermKind::Application {
            symbol, arguments, ..
        } if symbol.is(WellKnownSymbol::DotK) && arguments.is_empty() => [Some(contents), None],
        _ => [None, None],
    }
}

/// The first `<k>` cell of `term` in preorder, not descending into a `<k>` cell. With one such
/// cell (`k_cells() == 1`) any order finds the same one.
fn first_k_cell(term: &Term) -> Option<&Term> {
    if term.attributes().k_cells() == 0 {
        return None;
    }
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            if symbol.is(WellKnownSymbol::KCell) {
                return Some(term);
            }
            arguments.iter().find_map(first_k_cell)
        }
        TermKind::And(left, right) => first_k_cell(left).or_else(|| first_k_cell(right)),
        TermKind::Injection { term, .. } => first_k_cell(term),
        TermKind::Map { entries, rest, .. } => entries
            .into_iter()
            .find_map(|(key, value)| first_k_cell(key).or_else(|| first_k_cell(value)))
            .or_else(|| rest.as_ref().and_then(first_k_cell)),
        TermKind::List { heads, rest, .. } => {
            heads.into_iter().find_map(first_k_cell).or_else(|| {
                rest.as_ref().and_then(|(middle, tails)| {
                    first_k_cell(middle).or_else(|| tails.into_iter().find_map(first_k_cell))
                })
            })
        }
        TermKind::Set { elements, rest, .. } => elements
            .into_iter()
            .find_map(first_k_cell)
            .or_else(|| rest.as_ref().and_then(first_k_cell)),
        TermKind::DomainValue { .. } | TermKind::Variable(_) => None,
    }
}

/// Whether `term` may share the configuration with another `<k>` cell: it holds more than one
/// `<k>` cell, or a `<k>` cell inside a collection.
fn shares_k(term: &Term) -> bool {
    term.attributes().k_cells() > 1 || k_cell_in_collection(term, false)
}

fn k_cell_in_collection(term: &Term, in_collection: bool) -> bool {
    if term.attributes().k_cells() == 0 {
        return false;
    }
    let inside = |term: &Term| k_cell_in_collection(term, true);
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            (in_collection && symbol.is(WellKnownSymbol::KCell))
                || arguments
                    .iter()
                    .any(|argument| k_cell_in_collection(argument, in_collection))
        }
        TermKind::And(left, right) => {
            k_cell_in_collection(left, in_collection) || k_cell_in_collection(right, in_collection)
        }
        TermKind::Injection { term, .. } => k_cell_in_collection(term, in_collection),
        TermKind::Map { entries, rest, .. } => {
            entries
                .into_iter()
                .any(|(key, value)| inside(key) || inside(value))
                || rest.as_ref().is_some_and(inside)
        }
        TermKind::List { heads, rest, .. } => {
            heads.into_iter().any(inside)
                || rest
                    .as_ref()
                    .is_some_and(|(middle, tails)| inside(middle) || tails.into_iter().any(inside))
        }
        TermKind::Set { elements, rest, .. } => {
            elements.into_iter().any(inside) || rest.as_ref().is_some_and(inside)
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => false,
    }
}

/// `term` under its injections.
fn unwrapped(mut term: &Term) -> &Term {
    while let TermKind::Injection { term: inner, .. } = term.kind() {
        term = inner;
    }
    term
}

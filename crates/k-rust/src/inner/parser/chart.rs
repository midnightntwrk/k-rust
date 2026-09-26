//! ```toml algorithm
//! id = "parser.chart.insert"
//! name = "coverage-aware Earley chart insertion"
//! sites = ["Chart::add_with_status", "Derivations::insert"]
//! variable = "D = stored derivations; W = child width"
//! counters = ["ParserChartAddCalls", "ParserChartStateChanges"]
//!
//! [[cost]]
//! mode = "one insertion"
//! bound = "O(D x W) with O(D log D) boundary factoring"
//! ```
//!
//! ```toml algorithm
//! id = "parser.chart.completed_memo"
//! name = "completed-node memoization for Earley charts"
//! sites = ["completed_nodes", "Chart::invalidate_completed_node"]
//! variable = "S = completed states of the sort at this chart; C = derivations of the completed states whose origin matches; b = work of build_packed_term plus filter_or_defer_packed_priority for one derivation"
//! counters = ["ParserCompletedNodesHits", "ParserCompletedNodesMisses", "ParserCompletedNodesInvalidated", "ParserChartCompletionCandidates"]
//!
//! [[cost]]
//! mode = "memo hit"
//! bound = "O(1) expected: one hashed lookup returning the shared result"
//!
//! [[cost]]
//! mode = "memo miss"
//! bound = "O(S + C x b)"
//! ```
//!
//! Earley chart insertion with coverage-aware derivations and completed-node memoization.
//!
//! An insertion costs O(stored derivations * child width), with boundary factoring at O(d log d).
//! Completed-node lookup is one hashed lookup on a hit and scans matching completed states on a miss.
//! Chart adds, state changes, memo hits, misses, and completion candidates have dedicated counters.

#[cfg(test)]
use std::cell::Cell;
use std::cell::RefCell;
#[cfg(any(test, feature = "measure"))]
use std::collections::HashSet;
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::hash::{BuildHasherDefault, Hasher};
use std::rc::Rc;

use k_rust_kore::measure::{self, Counter};

use crate::kast::TermSpan;

use super::disambiguation::PackedPriorityMemos;
use super::forest::{
    Derivation, PackedNode, PackedTerm, build_packed_term, cmp_packed_structurally,
    pack_alternatives,
};
use super::{Grammar, ParseError, ParseProvenance};

#[cfg(test)]
thread_local! {
    static CHART_WORK_COUNTERS: Cell<ChartWorkCounters> = const { Cell::new(ChartWorkCounters::ZERO) };
}

#[cfg(test)]
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ChartWorkCounters {
    pub(super) add_calls: usize,
    pub(super) new_state_changes: usize,
    pub(super) existing_state_growth_changes: usize,
    pub(super) agenda_enqueues: usize,
    pub(super) agenda_pops: usize,
    pub(super) revisit_pops: usize,
    pub(super) derivations_read: usize,
    pub(super) revisit_derivations_read: usize,
    pub(super) relocation_derivations_read: usize,
    pub(super) relocation_revisit_derivations_read: usize,
    pub(super) nonterminal_derivations_read: usize,
    pub(super) nonterminal_revisit_derivations_read: usize,
    pub(super) scan_derivations_read: usize,
    pub(super) scan_revisit_derivations_read: usize,
    pub(super) completion_derivations_read: usize,
    pub(super) completion_revisit_derivations_read: usize,
    pub(super) primary_completion_candidates: usize,
    pub(super) helper_completion_candidates: usize,
    pub(super) completed_nodes_calls: usize,
    pub(super) completed_nodes_hits: usize,
    pub(super) completed_nodes_misses: usize,
    pub(super) completed_nodes_invalidation_entries: usize,
    pub(super) completion_caller_derivations_read: usize,
}

#[cfg(test)]
impl ChartWorkCounters {
    pub(super) const ZERO: Self = Self {
        add_calls: 0,
        new_state_changes: 0,
        existing_state_growth_changes: 0,
        agenda_enqueues: 0,
        agenda_pops: 0,
        revisit_pops: 0,
        derivations_read: 0,
        revisit_derivations_read: 0,
        relocation_derivations_read: 0,
        relocation_revisit_derivations_read: 0,
        nonterminal_derivations_read: 0,
        nonterminal_revisit_derivations_read: 0,
        scan_derivations_read: 0,
        scan_revisit_derivations_read: 0,
        completion_derivations_read: 0,
        completion_revisit_derivations_read: 0,
        primary_completion_candidates: 0,
        helper_completion_candidates: 0,
        completed_nodes_calls: 0,
        completed_nodes_hits: 0,
        completed_nodes_misses: 0,
        completed_nodes_invalidation_entries: 0,
        completion_caller_derivations_read: 0,
    };
}

#[cfg(test)]
#[derive(Clone, Copy)]
pub(super) enum ChartDispatchKind {
    Relocation,
    Nonterminal,
    Scan,
    Completion,
}

#[cfg(test)]
pub(super) fn update_chart_work_counters(update: impl FnOnce(&mut ChartWorkCounters)) {
    let mut counters = CHART_WORK_COUNTERS.get();
    update(&mut counters);
    CHART_WORK_COUNTERS.set(counters);
}

#[cfg(test)]
pub(super) fn reset_chart_work_counters() {
    CHART_WORK_COUNTERS.set(ChartWorkCounters::ZERO);
}

#[cfg(test)]
pub(super) fn chart_work_counters() -> ChartWorkCounters {
    CHART_WORK_COUNTERS.get()
}

#[cfg(test)]
pub(super) fn record_chart_dispatch(kind: ChartDispatchKind, derivations: usize, revisit: bool) {
    update_chart_work_counters(|counters| match kind {
        ChartDispatchKind::Relocation => {
            counters.relocation_derivations_read += derivations;
            if revisit {
                counters.relocation_revisit_derivations_read += derivations;
            }
        }
        ChartDispatchKind::Nonterminal => {
            counters.nonterminal_derivations_read += derivations;
            if revisit {
                counters.nonterminal_revisit_derivations_read += derivations;
            }
        }
        ChartDispatchKind::Scan => {
            counters.scan_derivations_read += derivations;
            if revisit {
                counters.scan_revisit_derivations_read += derivations;
            }
        }
        ChartDispatchKind::Completion => {
            counters.completion_derivations_read += derivations;
            if revisit {
                counters.completion_revisit_derivations_read += derivations;
            }
        }
    });
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct State {
    pub(super) production: usize,
    pub(super) dot: usize,
    pub(super) origin: usize,
}

/// Multiplicative word hasher for chart keys.
///
/// Chart keys are indices the parser assigns (a state's production, dot and origin; sort ids;
/// origins), so the flooding resistance of the default hasher buys nothing, while every agenda
/// pop, chart insertion and completion hashes some. No result depends on the order of a hashed
/// chart map: the only walk over one collects into an ordered set.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct IndexHasher(u64);

impl Hasher for IndexHasher {
    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.write_u64(u64::from(*byte));
        }
    }

    fn write_u64(&mut self, word: u64) {
        const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;
        self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(SEED);
    }

    fn write_usize(&mut self, word: usize) {
        self.write_u64(word as u64);
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

pub(super) type IndexMap<K, V> = HashMap<K, V, BuildHasherDefault<IndexHasher>>;
#[cfg(any(test, feature = "measure"))]
pub(super) type StateSet = HashSet<State, BuildHasherDefault<IndexHasher>>;

type CompletedNodeKey = (usize, usize);

/// The packed terms completed for one `(sort_id, origin)` boundary and the first priority
/// violation met while building them.
///
/// The memo shares one result among every caller of the boundary; callers read it in place.
#[derive(Debug)]
pub(super) struct CompletedNodes {
    pub(super) nodes: BTreeSet<Rc<PackedTerm>>,
    pub(super) violation: Option<ParseError>,
}

#[derive(Clone, Debug)]
pub(super) struct Chart {
    pub(super) states: IndexMap<State, Derivations>,
    // Each bucket is considered once at this position. Its marker also permits omission of
    // impossible callers that would not expand the same bucket again. Caller-specific nullable
    // completion must still run on every request.
    pub(super) predicted: Vec<bool>,
    pub(super) waiting: IndexMap<usize, Vec<State>>,
    pub(super) completed: IndexMap<usize, Vec<State>>,
    pub(super) agenda: VecDeque<State>,
    // Revisit accounting (`parser.chart_revisit_pops`) needs the set of states popped so far;
    // it is kept only where something reads it.
    #[cfg(any(test, feature = "measure"))]
    pub(super) popped: StateSet,
    // Java exposes one completed node for each stable (sort, origin, end) chart boundary.
    pub(super) completed_nodes: RefCell<IndexMap<CompletedNodeKey, Rc<CompletedNodes>>>,
}

impl Default for Chart {
    fn default() -> Self {
        Self::new(0)
    }
}

impl Chart {
    pub(super) fn new(sort_count: usize) -> Self {
        Self {
            states: IndexMap::default(),
            predicted: vec![false; sort_count],
            waiting: IndexMap::default(),
            completed: IndexMap::default(),
            agenda: VecDeque::new(),
            #[cfg(any(test, feature = "measure"))]
            popped: StateSet::default(),
            completed_nodes: RefCell::new(IndexMap::default()),
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) enum Derivations {
    #[default]
    Empty,
    One(Derivation),
    Many(BTreeSet<Derivation>),
}

impl Derivations {
    pub(super) fn insert(&mut self, candidate: Derivation) -> bool {
        match std::mem::take(self) {
            Self::Empty => {
                *self = Self::One(candidate);
                true
            }
            Self::One(existing) => {
                if derivation_covers(&existing, &candidate) {
                    *self = Self::One(existing);
                    false
                } else if derivation_covers(&candidate, &existing) {
                    *self = Self::One(candidate);
                    true
                } else {
                    let mut stored = BTreeSet::from([existing, candidate]);
                    factor_derivations(&mut stored);
                    *self = Self::from_set(stored);
                    true
                }
            }
            Self::Many(mut stored) => {
                if stored
                    .iter()
                    .any(|existing| derivation_covers(existing, &candidate))
                {
                    *self = Self::Many(stored);
                    return false;
                }
                stored.retain(|existing| !derivation_covers(&candidate, existing));
                stored.insert(candidate);
                factor_derivations(&mut stored);
                *self = Self::from_set(stored);
                true
            }
        }
    }

    fn from_set(mut stored: BTreeSet<Derivation>) -> Self {
        if stored.len() == 1 {
            Self::One(stored.pop_first().expect("one derivation exists"))
        } else if stored.is_empty() {
            Self::Empty
        } else {
            Self::Many(stored)
        }
    }

    pub(super) fn iter(&self) -> DerivationIter<'_> {
        match self {
            Self::Empty => DerivationIter::Empty,
            Self::One(derivation) => DerivationIter::One(Some(derivation)),
            Self::Many(derivations) => DerivationIter::Many(derivations.iter()),
        }
    }

    pub(super) fn len(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::One(_) => 1,
            Self::Many(derivations) => derivations.len(),
        }
    }
}

pub(super) enum DerivationIter<'a> {
    Empty,
    One(Option<&'a Derivation>),
    Many(std::collections::btree_set::Iter<'a, Derivation>),
}

impl<'a> Iterator for DerivationIter<'a> {
    type Item = &'a Derivation;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Empty => None,
            Self::One(derivation) => derivation.take(),
            Self::Many(derivations) => derivations.next(),
        }
    }
}

impl<'a> IntoIterator for &'a Derivations {
    type Item = &'a Derivation;
    type IntoIter = DerivationIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub(super) enum DerivationIntoIter {
    Empty,
    One(Option<Derivation>),
    Many(std::collections::btree_set::IntoIter<Derivation>),
}

impl Iterator for DerivationIntoIter {
    type Item = Derivation;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Empty => None,
            Self::One(derivation) => derivation.take(),
            Self::Many(derivations) => derivations.next(),
        }
    }
}

impl IntoIterator for Derivations {
    type Item = Derivation;
    type IntoIter = DerivationIntoIter;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Self::Empty => DerivationIntoIter::Empty,
            Self::One(derivation) => DerivationIntoIter::One(Some(derivation)),
            Self::Many(derivations) => DerivationIntoIter::Many(derivations.into_iter()),
        }
    }
}

impl Chart {
    pub(super) fn invalidate_completed_node(&mut self, sort_id: usize, origin: usize) {
        let removed = self.completed_nodes.get_mut().remove(&(sort_id, origin));
        measure::add(
            Counter::ParserCompletedNodesInvalidated,
            u64::from(removed.is_some()),
        );
        #[cfg(test)]
        if removed.is_some() {
            update_chart_work_counters(|counters| {
                counters.completed_nodes_invalidation_entries += 1;
            });
        }
    }

    #[cfg(test)]
    pub(super) fn add(
        &mut self,
        state: State,
        derivations: impl IntoIterator<Item = Derivation>,
    ) -> Result<bool, ParseError> {
        self.add_with_status(state, derivations)
            .map(|(changed, _new_state)| changed)
    }

    pub(super) fn add_with_status(
        &mut self,
        state: State,
        derivations: impl IntoIterator<Item = Derivation>,
    ) -> Result<(bool, bool), ParseError> {
        measure::bump(Counter::ParserChartAddCalls);
        #[cfg(test)]
        update_chart_work_counters(|counters| counters.add_calls += 1);
        let mut derivations = derivations.into_iter().peekable();
        if derivations.peek().is_none() {
            return Ok((false, !self.states.contains_key(&state)));
        }
        let (stored, new_state) = match self.states.entry(state) {
            Entry::Occupied(entry) => (entry.into_mut(), false),
            Entry::Vacant(entry) => (entry.insert(Derivations::Empty), true),
        };
        let mut changed = false;
        // Invariant: `stored` is an antichain under derivation coverage after every insertion;
        // `changed` is true exactly when the represented parse set grows.
        for derivation in derivations {
            changed |= stored.insert(derivation);
        }
        if !changed {
            return Ok((false, new_state));
        }
        measure::bump(Counter::ParserChartStateChanges);
        #[cfg(test)]
        update_chart_work_counters(|counters| {
            if new_state {
                counters.new_state_changes += 1;
            } else {
                counters.existing_state_growth_changes += 1;
            }
            counters.agenda_enqueues += 1;
        });
        self.agenda.push_back(state);
        Ok((true, new_state))
    }
}

fn derivation_covers(existing: &[Rc<PackedTerm>], candidate: &[Rc<PackedTerm>]) -> bool {
    existing.len() == candidate.len()
        && existing
            .iter()
            .zip(candidate)
            .all(|(existing, candidate)| parsed_term_covers(existing.as_ref(), candidate.as_ref()))
}

fn parsed_term_covers(existing: &PackedTerm, candidate: &PackedTerm) -> bool {
    match (&existing.node, &candidate.node) {
        (PackedNode::Ambiguity(existing), PackedNode::Ambiguity(candidate)) => {
            candidate.is_subset(existing)
        }
        (PackedNode::Ambiguity(existing), _) => existing.contains(candidate),
        (_, PackedNode::Ambiguity(candidate)) => {
            candidate.len() == 1 && candidate.contains(existing)
        }
        (existing, candidate) => existing == candidate,
    }
}

/// Pack derivations that use the same child boundaries.
///
/// For a fixed production and a fixed sequence of child spans, every parse of one child can be
/// combined independently with every parse of the other children. Keeping those combinations as
/// separate vectors materializes the Cartesian product that a packed parse forest is meant to
/// share. Different boundary sequences remain separate because combining those could splice
/// overlapping parses into a tree the grammar never recognized. A derivation with an unspanned
/// child has no boundaries to compare and is retained as it is.
///
/// Coverage-aware insertion and factoring are complementary: coverage removes whole derivations
/// subsumed by an existing ambiguity, while factoring creates that shared ambiguity from sibling
/// derivations with identical boundaries.
fn factor_derivations(derivations: &mut BTreeSet<Derivation>) {
    if derivations.len() < 2 {
        return;
    }

    let mut groups = BTreeMap::<Vec<TermSpan>, Vec<Derivation>>::new();
    let mut unspanned = BTreeSet::new();
    // Invariant: drained derivations are partitioned by an identical child-span vector, while
    // unspanned derivations remain separate and no recognized boundary correlation is lost.
    for derivation in std::mem::take(derivations) {
        match derivation
            .iter()
            .map(|node| packed_term_span(node))
            .collect::<Option<Vec<_>>>()
        {
            Some(spans) => groups.entry(spans).or_default().push(derivation),
            None => {
                unspanned.insert(derivation);
            }
        }
    }
    for (spans, group) in groups {
        if group.len() == 1 {
            derivations.extend(group);
            continue;
        }
        let packed = (0..spans.len())
            .map(|index| {
                pack_alternatives(
                    &group
                        .iter()
                        .map(|derivation| Rc::clone(&derivation[index]))
                        .collect(),
                )
            })
            .collect();
        derivations.insert(packed);
    }
    derivations.extend(unspanned);
}

fn packed_term_span(term: &PackedTerm) -> Option<TermSpan> {
    match &term.node {
        PackedNode::Production { metadata, .. }
        | PackedNode::InstantiatedProduction { metadata, .. } => metadata.span,
        PackedNode::Term(term) => term.metadata().and_then(|metadata| metadata.span),
        PackedNode::Ambiguity(alternatives) => {
            let mut spans = alternatives
                .iter()
                .map(|alternative| packed_term_span(alternative));
            let span = spans.next().flatten()?;
            spans
                .all(|candidate| candidate == Some(span))
                .then_some(span)
        }
    }
}

#[allow(clippy::too_many_arguments)]
/// Returns one canonical set of packed terms per version of a `(sort_id, origin)` boundary.
///
/// Repeated requests reuse the same `Rc` allocations until a completed state or derivation for
/// that boundary changes. The chart fixes `end` and the parse attempt fixes `provenance`, so neither
/// belongs in the memo key.
pub(super) fn completed_nodes(
    chart: &Chart,
    grammar: &Grammar,
    sort_id: usize,
    origin: usize,
    end: usize,
    input: &str,
    provenance: ParseProvenance,
    priority_memos: &RefCell<PackedPriorityMemos>,
) -> Rc<CompletedNodes> {
    // Invariant: on a cache miss, every completed state for this exact boundary contributes each
    // derivation once; the memo is populated only with the complete packed result and first error.
    #[cfg(test)]
    update_chart_work_counters(|counters| counters.completed_nodes_calls += 1);
    let key = (sort_id, origin);
    if let Some(completed) = chart.completed_nodes.borrow().get(&key) {
        measure::bump(Counter::ParserCompletedNodesHits);
        #[cfg(test)]
        update_chart_work_counters(|counters| counters.completed_nodes_hits += 1);
        return Rc::clone(completed);
    }
    measure::bump(Counter::ParserCompletedNodesMisses);
    #[cfg(test)]
    update_chart_work_counters(|counters| counters.completed_nodes_misses += 1);
    let mut nodes = BTreeSet::new();
    let mut invalid = Vec::new();
    for state in chart.completed.get(&sort_id).into_iter().flatten() {
        if state.origin != origin {
            continue;
        }
        let derivations = &chart.states[state];
        let production = &grammar.productions[state.production];
        for children in derivations {
            measure::bump(Counter::ParserChartCompletionCandidates);
            #[cfg(test)]
            update_chart_work_counters(|counters| {
                counters.helper_completion_candidates += 1;
            });
            let term = build_packed_term(
                state.production,
                production,
                children,
                input,
                state.origin,
                end,
                provenance,
            );
            match grammar.filter_or_defer_packed_priority(Rc::clone(&term), priority_memos) {
                Ok(term) => {
                    nodes.insert(term);
                }
                Err(error) => {
                    invalid.push((term, error));
                }
            }
        }
    }
    let violation = (!invalid.is_empty()).then(|| canonical_packed_error(invalid));
    let completed = Rc::new(CompletedNodes { nodes, violation });
    chart
        .completed_nodes
        .borrow_mut()
        .insert(key, Rc::clone(&completed));
    completed
}

pub(super) fn canonical_packed_error(errors: Vec<(Rc<PackedTerm>, ParseError)>) -> ParseError {
    errors
        .into_iter()
        .min_by(|(left, _), (right, _)| cmp_packed_structurally(left, right))
        .map(|(_, error)| error)
        .expect("an empty packed ambiguity had no invalid alternative")
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::super::*;
    use super::*;

    fn variable(name: &str) -> ParsedTerm {
        ParsedTerm::Term(Term::Variable {
            name: name.to_owned(),
            sort: None,
        })
    }

    fn ambiguity(names: &[&str]) -> ParsedTerm {
        ParsedTerm::Ambiguity(names.iter().map(|name| variable(name)).collect())
    }

    fn derivation(term: ParsedTerm) -> Derivation {
        fn pack(term: ParsedTerm) -> Rc<PackedTerm> {
            match term {
                ParsedTerm::Term(term) => PackedTerm::leaf(term),
                ParsedTerm::Production {
                    production,
                    children,
                    metadata,
                } => PackedTerm::production(
                    production,
                    children.into_iter().map(pack).collect(),
                    metadata,
                ),
                ParsedTerm::Ambiguity(alternatives) => {
                    PackedTerm::ambiguity(alternatives.into_iter().map(pack).collect())
                }
                ParsedTerm::InstantiatedProduction { .. } => {
                    panic!("chart tests do not construct post-inference productions")
                }
            }
        }
        vec![pack(term)]
    }

    fn spanned_node(production: usize, start: usize, end: usize) -> Rc<PackedTerm> {
        PackedTerm::production(
            production,
            Vec::new(),
            TermMetadata {
                span: Some(TermSpan {
                    source: SourceId(0),
                    start,
                    end,
                }),
                ..TermMetadata::default()
            },
        )
    }

    fn generated_derivation(masks: &[u8]) -> Derivation {
        masks
            .iter()
            .map(|mask| {
                let alternatives = (0..3)
                    .filter(|bit| mask & (1 << bit) != 0)
                    .map(|bit| {
                        PackedTerm::leaf(Term::Variable {
                            name: format!("V{bit}"),
                            sort: None,
                        })
                    })
                    .collect();
                PackedTerm::ambiguity(alternatives)
            })
            .collect()
    }

    proptest! {
        #[test]
        fn derivation_insertion_is_idempotent_and_retains_an_antichain(
            sequence in prop::collection::vec(
                prop::collection::vec(1u8..8, 0..4),
                0..24,
            ),
        ) {
            let mut stored = Derivations::default();
            for masks in sequence {
                let candidate = generated_derivation(&masks);
                stored.insert(candidate.clone());
                let once = stored.clone();
                prop_assert!(!stored.insert(candidate));
                prop_assert_eq!(&stored, &once);

                let derivations = stored.iter().collect::<Vec<_>>();
                for left in 0..derivations.len() {
                    for right in left + 1..derivations.len() {
                        prop_assert!(!derivation_covers(derivations[left], derivations[right]));
                        prop_assert!(!derivation_covers(derivations[right], derivations[left]));
                    }
                }
            }
        }
    }

    #[test]
    fn completed_parent_reuses_its_packed_child_allocation() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Parent"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Child"),
                    name: None,
                }],
                Some(Label::new("parent")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                Sort::new("Child"),
                Vec::new(),
                Some(Label::new("child")),
                false,
                false,
            )
            .unwrap();
        let child = PackedTerm::production(1, Vec::new(), TermMetadata::default());
        let parent = build_packed_term(
            0,
            &grammar.productions[0],
            std::slice::from_ref(&child),
            "child",
            0,
            5,
            ParseProvenance {
                source: SourceId(0),
                base_offset: 0,
            },
        );
        let parent = grammar
            .filter_or_defer_packed_priority(parent, &RefCell::new(PackedPriorityMemos::default()))
            .expect("packed parent satisfies priority");
        let PackedNode::Production { children, .. } = &parent.node else {
            panic!("expected packed production");
        };

        assert!(Rc::ptr_eq(&children[0], &child));
    }

    #[test]
    fn completed_nodes_are_canonical_for_their_chart_boundary() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("S"),
                vec![ProductionItem::NonTerminal {
                    sort: Sort::new("Child"),
                    name: None,
                }],
                Some(Label::new("unit")),
                false,
                false,
            )
            .unwrap();
        let state = State {
            production: 0,
            dot: 1,
            origin: 0,
        };
        let mut chart = Chart::new(grammar.sorts.len());
        grammar
            .add_chart_state(&mut chart, state, [derivation(variable("A"))])
            .unwrap();
        let sort_id = grammar.sort_id(&Sort::new("S")).unwrap();
        let provenance = ParseProvenance {
            source: SourceId(0),
            base_offset: 0,
        };

        let memos = RefCell::new(PackedPriorityMemos::default());
        let first = completed_nodes(&chart, &grammar, sort_id, 0, 0, "", provenance, &memos);
        let second = completed_nodes(&chart, &grammar, sort_id, 0, 0, "", provenance, &memos);
        assert!(Rc::ptr_eq(&first, &second));
        let first = first
            .nodes
            .first()
            .cloned()
            .expect("first completed node exists");
        let second = second
            .nodes
            .first()
            .cloned()
            .expect("second completed node exists");

        assert!(Rc::ptr_eq(&first, &second));

        grammar
            .add_chart_state(
                &mut chart,
                State { origin: 1, ..state },
                [derivation(variable("A"))],
            )
            .unwrap();
        let after_other_boundary =
            completed_nodes(&chart, &grammar, sort_id, 0, 0, "", provenance, &memos);
        let after_other_boundary = after_other_boundary
            .nodes
            .first()
            .cloned()
            .expect("completed node survives another boundary change");
        assert!(Rc::ptr_eq(&first, &after_other_boundary));

        grammar
            .add_chart_state(&mut chart, state, [derivation(variable("B"))])
            .unwrap();
        let after_same_boundary =
            completed_nodes(&chart, &grammar, sort_id, 0, 0, "", provenance, &memos);
        assert_eq!(after_same_boundary.nodes.len(), 2);
        assert!(
            after_same_boundary
                .nodes
                .iter()
                .all(|completed| !Rc::ptr_eq(&first, completed))
        );
    }

    #[test]
    fn does_not_enqueue_a_derivation_covered_by_a_stored_ambiguity() {
        let state = State {
            production: 0,
            dot: 1,
            origin: 0,
        };
        let mut chart = Chart::default();
        assert!(
            chart
                .add(state, [derivation(ambiguity(&["A", "B"]))])
                .unwrap()
        );
        assert_eq!(chart.agenda.pop_front(), Some(state));

        assert!(!chart.add(state, [derivation(variable("A"))]).unwrap());
        assert!(chart.agenda.is_empty());
        assert_eq!(chart.states[&state].len(), 1);
    }

    #[test]
    fn replaces_covered_derivations_with_a_superseding_ambiguity() {
        let state = State {
            production: 0,
            dot: 1,
            origin: 0,
        };
        let mut chart = Chart::default();
        assert!(chart.add(state, [derivation(variable("A"))]).unwrap());
        chart.agenda.clear();

        assert!(
            chart
                .add(state, [derivation(ambiguity(&["A", "B"]))])
                .unwrap()
        );
        assert_eq!(chart.agenda.into_iter().collect::<Vec<_>>(), vec![state]);
        assert_eq!(
            chart.states[&state]
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([derivation(ambiguity(&["A", "B"]))]),
        );
    }

    #[test]
    fn packs_growing_completed_node_alternatives_in_one_derivation() {
        let state = State {
            production: 0,
            dot: 1,
            origin: 0,
        };
        let mut chart = Chart::default();

        for count in 1..=70 {
            let alternatives = (0..count)
                .map(|index| {
                    ParsedTerm::Term(Term::Variable {
                        name: format!("V{index}"),
                        sort: None,
                    })
                })
                .collect();
            chart
                .add(state, [derivation(ParsedTerm::Ambiguity(alternatives))])
                .expect("growing subsets should be packed, not counted as separate derivations");
        }

        let stored = &chart.states[&state];
        assert_eq!(stored.len(), 1);
        assert!(matches!(
            &stored.iter().next().expect("one derivation exists")[0].node,
            PackedNode::Ambiguity(alternatives)
                if alternatives.len() == 70
        ));
    }

    #[test]
    fn chart_accepts_more_than_sixty_four_boundary_distinct_derivations() {
        let state = State {
            production: 0,
            dot: 2,
            origin: 0,
        };
        let mut chart = Chart::default();
        let derivations = (0..70).map(|index| {
            vec![
                derivation(variable(&format!("L{index}"))).pop().unwrap(),
                derivation(variable(&format!("R{index}"))).pop().unwrap(),
            ]
        });

        assert_eq!(chart.add(state, derivations), Ok(true));
        assert_eq!(chart.states[&state].len(), 70);
    }

    #[test]
    fn packs_independent_child_choices_with_matching_boundaries() {
        let mut derivations = BTreeSet::from([
            vec![spanned_node(0, 0, 1), spanned_node(2, 1, 2)],
            vec![spanned_node(1, 0, 1), spanned_node(3, 1, 2)],
        ]);

        factor_derivations(&mut derivations);

        let packed = derivations.first().expect("one packed derivation");
        assert_eq!(derivations.len(), 1);
        assert!(matches!(&packed[0].node, PackedNode::Ambiguity(items) if items.len() == 2));
        assert!(matches!(&packed[1].node, PackedNode::Ambiguity(items) if items.len() == 2));
    }

    #[test]
    fn keeps_different_child_boundaries_correlated() {
        let mut derivations = BTreeSet::from([
            vec![spanned_node(0, 0, 1), spanned_node(1, 1, 3)],
            vec![spanned_node(2, 0, 2), spanned_node(3, 2, 3)],
        ]);

        factor_derivations(&mut derivations);

        assert_eq!(derivations.len(), 2);
    }
}

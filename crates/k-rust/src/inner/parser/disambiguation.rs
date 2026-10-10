//! ```toml algorithm
//! id = "parser.disambiguation.priority"
//! name = "priority and associativity filtering of packed terms"
//! sites = ["Grammar::filter_packed_priority", "Grammar::filter_or_defer_packed_priority"]
//! variable = "N = packed nodes per memo lifetime"
//! counters = ["ParserPackedPriorityComputations"]
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one parse forest"
//! bound = "O(N)"
//!
//! [[cost]]
//! mode = "one completion candidate (filter_or_defer_packed_priority)"
//! bound = "one memoized packed filter; a Scope error under KRewrite, KSequence or Let is deferred, and the candidate kept"
//! ```
//!
//! ```toml algorithm
//! id = "parser.disambiguation.resolve_applications"
//! name = "resolution of application nodes against visible productions"
//! sites = ["Grammar::resolve_packed_applications"]
//! variable = "N = application nodes; R = productions in the grammar; K = KList nodes below the applications; a = distinct argument vectors of one application no longer than its label's longest arity"
//! counters = ["ParserPackedApplicationResolutions"]
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one parse forest"
//! bound = "O(N x R) to find each label's arities, plus O(N x a x R) candidates, plus each KList node's bounded argument vectors and shortest length computed once (O(K) nodes, each combining its children's vectors), plus the structural ordering of each ambiguity's alternatives, whose pair comparisons the pass shares"
//! ```
//!
//! ```toml algorithm
//! id = "parser.disambiguation.factor_packed"
//! name = "factoring of packed ambiguities"
//! sites = ["Grammar::factor_pre_inference_packed_ambiguities"]
//! variable = "N = packed nodes; A = ambiguity alternatives"
//! counters = []
//! no_counter = "packed-ambiguity factoring has no dedicated counter"
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one parse forest"
//! bound = "O(N x A)"
//! ```
//!
//! ```toml algorithm
//! id = "parser.disambiguation.lift_top_lhs"
//! name = "lifting of top-level left-hand-side ambiguities"
//! sites = ["Grammar::push_top_lhs_packed_ambiguity_up"]
//! variable = "N = packed or owned nodes"
//! counters = []
//! no_counter = "top-LHS ambiguity lifting has no dedicated counter"
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one parse forest"
//! bound = "O(N)"
//! ```
//!
//! ```toml algorithm
//! id = "parser.disambiguation.resolve_terminators"
//! name = "resolution of overloaded list terminators"
//! sites = ["Grammar::resolve_overloaded_terminators", "Grammar::resolve_overloaded_terminators_node"]
//! variable = "N = owned nodes; L = user lists; R = productions in the grammar; K = nullary nodes whose source production is overloaded"
//! counters = []
//! no_counter = "overloaded-terminator resolution has no dedicated counter"
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one parsed tree"
//! bound = "O(N x L + K x R)"
//! ```
//!
//! ```toml algorithm
//! id = "parser.disambiguation.filter_overloads"
//! name = "overload and prefer-or-avoid filtering"
//! sites = ["Grammar::filter_overloads_prefer_avoid", "Grammar::filter_overloads_prefer_avoid_node", "Grammar::select_at_frontier"]
//! variable = "N = owned nodes; R = productions in the grammar; t = Term-leaf alternatives of the ambiguities; f = work of one factor_ambiguities call; A = alternatives of one ambiguity; P = nodes of their common prefix; F = their frontier positions"
//! counters = []
//! no_counter = "overload and preference filtering has no dedicated counter"
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one parsed tree"
//! bound = "O(N + t x R) plus one clone, f and one equality test per ambiguity with more than one surviving alternative, and a further pass when factoring changed it"
//!
//! [[cost]]
//! mode = "frontier step of one ambiguity that factoring leaves with A >= 2 alternatives"
//! bound = "fewer than A rounds of O(A x P) header comparisons and O(A x F x R) token classifications, then one clone, f and equality test when it removed an alternative"
//! ```
//!
//! The frontier step decides `prefer`/`avoid` between alternatives that diverge at several
//! positions: an alternative is classified by its nodes just below the alternatives' common prefix
//! of equal node headers. At a single divergence point that is the node the per-node step already
//! classifies (the root when top productions differ; the one differing child, after factoring,
//! when they share it), so the frontier step changes only ambiguities the per-node step leaves
//! undecided; see `Grammar::filter_overloads_prefer_avoid_node`.
//!
//! ```toml algorithm
//! id = "parser.disambiguation.remove_brackets_casts"
//! name = "removal of brackets and syntactic casts"
//! sites = ["Grammar::remove_brackets_and_syntactic_casts", "Grammar::remove_brackets_and_syntactic_casts_node"]
//! variable = "N = owned nodes"
//! counters = []
//! no_counter = "bracket and syntactic-cast removal has no dedicated counter"
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one parsed tree"
//! bound = "O(N)"
//! ```
//!
//! ```toml algorithm
//! id = "parser.disambiguation.resolve_ambiguity"
//! name = "resolution and reporting of remaining ambiguity"
//! sites = ["Grammar::resolve_ambiguities", "Grammar::resolve_ambiguities_node", "Grammar::factor_ambiguities"]
//! variable = "N = owned nodes; A = ambiguity alternatives"
//! counters = []
//! no_counter = "final ambiguity resolution has no dedicated counter"
//! consumes = [{ type = "k_rust::inner::parser::forest::ParsedTerm", role = "sorted tree" }]
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one parsed tree"
//! bound = "O(N) lowering (parser.lower.term) when every ambiguity has one reading; otherwise an ambiguity whose alternatives have several readings, and a node whose lowering joins or drops children over several readings, expand their readings, at most one term per tree below them, while independent choices below a node that keeps its children stay unexpanded; the report then renders each reading of each place once"
//! ```
//!
//! Packed-DAG and owned-tree disambiguation in the following pipeline order.
//! 1. Reserve variable names (packed DAG, O(nodes)).
//! 2. Collapse record syntax (packed DAG, O(nodes + fields)).
//! 3. Filter priority and associativity (packed DAG, O(nodes per memo lifetime)).
//! 4. Resolve `#KApply` (packed DAG, O(nodes * argument lists * productions)).
//! 5. Factor packed ambiguities (packed DAG, O(nodes * alternatives)).
//! 6. Lift top-LHS ambiguities (packed DAG, O(nodes)).
//! 7. Infer sorts and unpack (packed DAG to owned tree).
//! 8. Resolve overloaded terminators (owned tree, O(nodes * list candidates)).
//! 9. Apply prefer/avoid and overload filtering (owned tree, O(nodes) plus re-factoring of each
//!    surviving ambiguity), then the prefer/avoid frontier step on an ambiguity whose alternatives
//!    still diverge at several positions.
//! 10. Remove brackets and syntactic casts (owned tree, O(nodes)).
//! 11. Factor and report remaining ambiguities (owned tree, O(nodes * alternatives)).
//!
//! One node/child memo pair is shared through recognition and packed-forest preparation for each
//! parse attempt; child keys are `(identity, parent production, side)`.
//! `Counter::ParserPackedPriorityComputations` counts priority memo misses. Portable and Z3
//! inference paths remain independent oracles and must produce the same accepted tree.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use k_rust_kore::measure::{self, Algorithm, Counter};

use super::{
    AmbiguityPlace, AmbiguousParse, Grammar, Item, PackedNode, PackedTerm, ParseError, ParsedParts,
    ParsedTerm, Production, StructuralOrder, cmp_packed_structurally, lower_term,
};
use crate::kast::{FrontendSort, GeneratedLabel, InternalLabel, Sort, Term, TermSpan, string};

use super::canonical_packed_error;

fn packed_sets_share_nodes(
    left: &BTreeSet<Rc<PackedTerm>>,
    right: &BTreeSet<Rc<PackedTerm>>,
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| Rc::ptr_eq(left, right))
}

type PackedTransformResult = Result<Rc<PackedTerm>, ParseError>;
type PackedTransformMemo = HashMap<*const PackedTerm, (Rc<PackedTerm>, PackedTransformResult)>;
/// Argument vectors, each a sequence of packed nodes.
type ArgumentLists = Rc<Vec<Vec<Rc<PackedTerm>>>>;
/// What one application-resolution pass keeps: the argument vectors of a `#KList` node up to
/// a length, and its shortest one's length, by node identity (each entry keeps its node alive
/// so that its address is not reused), and the structural comparisons its orderings made.
#[derive(Default)]
struct KListMemo {
    flattened: HashMap<(*const PackedTerm, usize), (Rc<PackedTerm>, ArgumentLists)>,
    shortest: HashMap<*const PackedTerm, (Rc<PackedTerm>, usize)>,
    order: StructuralOrder,
}
type PackedPriorityChildMemo =
    HashMap<(*const PackedTerm, usize, Option<Side>), (Rc<PackedTerm>, PackedTransformResult)>;

#[derive(Default)]
pub(super) struct PackedPriorityMemos {
    nodes: PackedTransformMemo,
    children: PackedPriorityChildMemo,
}

/// The parent labels a nested `#KRewrite` may appear under.
const SCOPE_REWRITE: [InternalLabel; 6] = [
    InternalLabel::RuleRequires,
    InternalLabel::RuleEnsures,
    InternalLabel::RuleRequiresEnsures,
    InternalLabel::KRewrite,
    InternalLabel::WithConfig,
    InternalLabel::KList,
];

/// The parent labels a nested `#KSequence` may appear under.
const SCOPE_SEQUENCE: [InternalLabel; 6] = [
    InternalLabel::RuleRequires,
    InternalLabel::RuleEnsures,
    InternalLabel::RuleRequiresEnsures,
    InternalLabel::KRewrite,
    InternalLabel::KSequence,
    InternalLabel::KList,
];

/// The parent labels a nested `#let` may appear under.
const SCOPE_LET: [InternalLabel; 7] = [
    InternalLabel::RuleRequires,
    InternalLabel::RuleEnsures,
    InternalLabel::RuleRequiresEnsures,
    InternalLabel::KRewrite,
    InternalLabel::KSequence,
    InternalLabel::Let,
    InternalLabel::KList,
];

impl Grammar {
    /// Factor the forest's ambiguities before inference. Nested ambiguities are flattened into
    /// their parent. An ambiguity whose alternatives all apply one production (with the same sort
    /// parameters, for an instantiated production) to children that agree at every position but
    /// one becomes that production over the shared children and, at that position, an ambiguity
    /// of the differing children, factored in turn: its trees are exactly the alternatives, and
    /// inference sees the shared children once. Alternatives that differ at two or more positions
    /// stay as they are, since an ambiguity at each position would also admit the trees that mix
    /// the children of different alternatives. Runs after record and application syntax has
    /// already been resolved, retaining identity sharing until the forest is compressed.
    pub(super) fn factor_pre_inference_packed_ambiguities(
        &self,
        term: Rc<PackedTerm>,
    ) -> Rc<PackedTerm> {
        let _span = measure::algorithm_span(Algorithm::ParserDisambiguationFactorPacked);
        self.factor_packed_ambiguities(term, &mut HashMap::new())
    }

    fn factor_packed_ambiguities(
        &self,
        term: Rc<PackedTerm>,
        memo: &mut HashMap<*const PackedTerm, (Rc<PackedTerm>, Rc<PackedTerm>)>,
    ) -> Rc<PackedTerm> {
        crate::stack::guarded(|| {
            // Invariant: every memoized identity has a complete factored result; recursion only visits
            // unrecorded children or alternatives.
            let identity = Rc::as_ptr(&term);
            if let Some((_, factored)) = memo.get(&identity) {
                return Rc::clone(factored);
            }
            let factored = match &term.node {
                PackedNode::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                    metadata,
                } => {
                    let factored_children = children
                        .iter()
                        .map(|child| self.factor_packed_ambiguities(Rc::clone(child), memo))
                        .collect::<Vec<_>>();
                    if factored_children
                        .iter()
                        .zip(children)
                        .all(|(factored, original)| Rc::ptr_eq(factored, original))
                    {
                        Rc::clone(&term)
                    } else {
                        PackedTerm::instantiated_production(
                            *production,
                            parameters.clone(),
                            factored_children,
                            metadata.clone(),
                        )
                    }
                }
                PackedNode::Term(_) => Rc::clone(&term),
                PackedNode::Production {
                    production,
                    children,
                    metadata,
                } => {
                    let factored_children = children
                        .iter()
                        .map(|child| self.factor_packed_ambiguities(Rc::clone(child), memo))
                        .collect::<Vec<_>>();
                    if factored_children
                        .iter()
                        .zip(children)
                        .all(|(factored, original)| Rc::ptr_eq(factored, original))
                    {
                        Rc::clone(&term)
                    } else {
                        PackedTerm::production(*production, factored_children, metadata.clone())
                    }
                }
                PackedNode::Ambiguity(alternatives) => {
                    let mut flattened = BTreeSet::new();
                    for alternative in alternatives {
                        let alternative =
                            self.factor_packed_ambiguities(Rc::clone(alternative), memo);
                        match &alternative.node {
                            PackedNode::Ambiguity(nested) => {
                                flattened.extend(nested.iter().cloned());
                            }
                            _ => {
                                flattened.insert(alternative);
                            }
                        }
                    }
                    let factored = self.factor_packed_production_alternatives(flattened, memo);
                    if matches!(
                        &factored.node,
                        PackedNode::Ambiguity(factored_alternatives)
                            if packed_sets_share_nodes(factored_alternatives, alternatives)
                    ) {
                        Rc::clone(&term)
                    } else {
                        factored
                    }
                }
            };
            // Retain the input allocation as part of the entry. Factoring recursively creates
            // temporary ambiguity nodes; allowing one to drop while its raw address remains a key
            // would let a later allocation reuse the address and receive the wrong cached result.
            memo.insert(identity, (term, Rc::clone(&factored)));
            factored
        })
    }

    fn factor_packed_production_alternatives(
        &self,
        alternatives: BTreeSet<Rc<PackedTerm>>,
        memo: &mut HashMap<*const PackedTerm, (Rc<PackedTerm>, Rc<PackedTerm>)>,
    ) -> Rc<PackedTerm> {
        // Invariant: retained alternatives agree on the factored production prefix, and each
        // recursive difference occupies one child ambiguity.
        if alternatives.len() <= 1 {
            return PackedTerm::ambiguity(alternatives);
        }
        let Some(first) = alternatives
            .iter()
            .min_by(|left, right| cmp_packed_structurally(left, right))
        else {
            return PackedTerm::ambiguity(alternatives);
        };
        let PackedNode::Production {
            production,
            children,
            metadata,
        } = &first.node
        else {
            if let PackedNode::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } = &first.node
            {
                let production = *production;
                let parameters = parameters.clone();
                let children = children.clone();
                let metadata = metadata.clone();
                if !alternatives.iter().all(|alternative| {
                    matches!(
                        &alternative.node,
                        PackedNode::InstantiatedProduction {
                            production: candidate,
                            parameters: candidate_parameters,
                            children: candidate_children,
                            ..
                        } if *candidate == production
                            && candidate_parameters == &parameters
                            && candidate_children.len() == children.len()
                    )
                }) {
                    return PackedTerm::ambiguity(alternatives);
                }
                let differing = (0..children.len())
                    .filter(|index| {
                        alternatives.iter().any(|alternative| {
                            let PackedNode::InstantiatedProduction {
                                children: candidate_children,
                                ..
                            } = &alternative.node
                            else {
                                unreachable!()
                            };
                            candidate_children[*index] != children[*index]
                        })
                    })
                    .collect::<Vec<_>>();
                let [index] = differing.as_slice() else {
                    return PackedTerm::ambiguity(alternatives);
                };
                let mut factored_children = children;
                let child_alternatives = alternatives
                    .iter()
                    .map(|alternative| {
                        let PackedNode::InstantiatedProduction {
                            children: candidate_children,
                            ..
                        } = &alternative.node
                        else {
                            unreachable!()
                        };
                        Rc::clone(&candidate_children[*index])
                    })
                    .collect();
                factored_children[*index] =
                    self.factor_packed_ambiguities(PackedTerm::ambiguity(child_alternatives), memo);
                return PackedTerm::instantiated_production(
                    production,
                    parameters,
                    factored_children,
                    metadata,
                );
            }
            return PackedTerm::ambiguity(alternatives);
        };
        if !alternatives.iter().all(|alternative| {
            matches!(
                &alternative.node,
                PackedNode::Production {
                    production: candidate,
                    children: candidate_children,
                    ..
                } if candidate == production
                    && candidate_children.len() == children.len()
            )
        }) {
            return PackedTerm::ambiguity(alternatives);
        }
        let differing = (0..children.len())
            .filter(|index| {
                alternatives.iter().any(|alternative| {
                    let PackedNode::Production {
                        children: candidate_children,
                        ..
                    } = &alternative.node
                    else {
                        unreachable!()
                    };
                    candidate_children[*index] != children[*index]
                })
            })
            .collect::<Vec<_>>();
        let [index] = differing.as_slice() else {
            return PackedTerm::ambiguity(alternatives);
        };
        let mut factored_children = children.clone();
        let child_alternatives = alternatives
            .iter()
            .map(|alternative| {
                let PackedNode::Production {
                    children: candidate_children,
                    ..
                } = &alternative.node
                else {
                    unreachable!()
                };
                Rc::clone(&candidate_children[*index])
            })
            .collect();
        factored_children[*index] =
            self.factor_packed_ambiguities(PackedTerm::ambiguity(child_alternatives), memo);
        PackedTerm::production(*production, factored_children, metadata.clone())
    }

    pub(super) fn filter_or_defer_packed_priority(
        &self,
        term: Rc<PackedTerm>,
        memos: &RefCell<PackedPriorityMemos>,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let mut memos = memos.borrow_mut();
        let PackedPriorityMemos { nodes, children } = &mut *memos;
        match self.filter_packed_priority_memo(Rc::clone(&term), nodes, children) {
            Ok(term) => Ok(term),
            // A locally invalid nested rewrite/sequence/let may be the losing view of an
            // ambiguity whose sibling has that operation at the root. Retain only those failures
            // until the packed root preference can select the sibling.
            Err(ParseError::Scope { child, .. })
                if [
                    InternalLabel::KRewrite,
                    InternalLabel::KSequence,
                    InternalLabel::Let,
                ]
                .iter()
                .any(|label| child == label.as_str()) =>
            {
                Ok(term)
            }
            Err(error) => Err(error),
        }
    }

    pub(super) fn filter_packed_priority(
        &self,
        term: Rc<PackedTerm>,
        memos: &RefCell<PackedPriorityMemos>,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let _span = measure::algorithm_span(Algorithm::ParserDisambiguationPriority);
        let mut memos = memos.borrow_mut();
        let PackedPriorityMemos { nodes, children } = &mut *memos;
        self.filter_packed_priority_memo(term, nodes, children)
    }

    #[cfg(test)]
    pub(super) fn filter_or_defer_packed_priority_fresh(
        &self,
        term: Rc<PackedTerm>,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        self.filter_or_defer_packed_priority(term, &RefCell::new(PackedPriorityMemos::default()))
    }

    /// Filter a packed node against the priority and associativity relations.
    fn filter_packed_priority_memo(
        &self,
        term: Rc<PackedTerm>,
        memo: &mut PackedTransformMemo,
        child_memo: &mut PackedPriorityChildMemo,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        crate::stack::guarded(|| {
            // Invariant: node entries are complete context-free results and child entries are complete
            // for the `(identity, parent, side)` context.
            let identity = Rc::as_ptr(&term);
            if let Some((_, filtered)) = memo.get(&identity) {
                return filtered.clone();
            }
            measure::bump(Counter::ParserPackedPriorityComputations);
            let filtered = (|| -> PackedTransformResult {
                match &term.node {
                    PackedNode::InstantiatedProduction { .. } => {
                        unreachable!("instantiated productions are created after packed priority")
                    }
                    PackedNode::Term(_) => Ok(Rc::clone(&term)),
                    PackedNode::Ambiguity(original_alternatives) => {
                        let mut alternatives = original_alternatives.clone();
                        for preferred in [
                            InternalLabel::KRewrite,
                            InternalLabel::KSequence,
                            InternalLabel::Let,
                        ]
                        .map(InternalLabel::as_str)
                        {
                            let matching = alternatives
                                .iter()
                                .filter(|alternative| {
                                    self.packed_top_parse_label(alternative) == Some(preferred)
                                })
                                .cloned()
                                .collect::<BTreeSet<_>>();
                            if !matching.is_empty() {
                                alternatives = matching;
                            }
                        }
                        let mut retained = BTreeSet::new();
                        let mut errors = Vec::new();
                        for alternative in alternatives {
                            match self.filter_packed_priority_memo(
                                Rc::clone(&alternative),
                                memo,
                                child_memo,
                            ) {
                                Ok(alternative) => match &alternative.node {
                                    PackedNode::Ambiguity(nested) => {
                                        retained.extend(nested.iter().cloned())
                                    }
                                    _ => {
                                        retained.insert(alternative);
                                    }
                                },
                                Err(error) => {
                                    errors.push((alternative, error));
                                }
                            }
                        }
                        if retained.is_empty() {
                            Err(canonical_packed_error(errors))
                        } else if packed_sets_share_nodes(&retained, original_alternatives) {
                            Ok(Rc::clone(&term))
                        } else {
                            Ok(PackedTerm::ambiguity(retained))
                        }
                    }
                    PackedNode::Production {
                        production,
                        children,
                        metadata,
                    } => {
                        let descriptor = &self.productions[*production];
                        let checked = if descriptor.record.is_some() || descriptor.syntactic_subsort
                        {
                            BTreeSet::new()
                        } else {
                            descriptor.apply_priority.clone().unwrap_or_else(|| {
                                let mut positions = BTreeSet::new();
                                if matches!(descriptor.items.first(), Some(Item::NonTerminal(_))) {
                                    positions.insert(1);
                                }
                                if matches!(descriptor.items.last(), Some(Item::NonTerminal(_))) {
                                    positions.insert(children.len());
                                }
                                positions
                            })
                        };
                        let child_count = children.len();
                        let filtered_children = children
                            .iter()
                            .enumerate()
                            .map(|(index, child)| {
                                let position = index + 1;
                                let side = checked.contains(&position).then(|| {
                                    if position == 1
                                        && matches!(
                                            descriptor.items.first(),
                                            Some(Item::NonTerminal(_))
                                        )
                                    {
                                        Side::Left
                                    } else if position == child_count
                                        && matches!(
                                            descriptor.items.last(),
                                            Some(Item::NonTerminal(_))
                                        )
                                    {
                                        Side::Right
                                    } else {
                                        Side::Middle
                                    }
                                });
                                self.filter_packed_priority_child(
                                    *production,
                                    Rc::clone(child),
                                    side,
                                    memo,
                                    child_memo,
                                )
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        if filtered_children
                            .iter()
                            .zip(children)
                            .all(|(filtered, original)| Rc::ptr_eq(filtered, original))
                        {
                            Ok(Rc::clone(&term))
                        } else {
                            Ok(PackedTerm::production(
                                *production,
                                filtered_children,
                                metadata.clone(),
                            ))
                        }
                    }
                }
            })();
            memo.insert(identity, (Rc::clone(&term), filtered.clone()));
            filtered
        })
    }

    pub(super) fn packed_top_parse_label<'a>(&'a self, term: &'a PackedTerm) -> Option<&'a str> {
        crate::stack::guarded(|| {
            let PackedNode::Production {
                production,
                children,
                ..
            } = &term.node
            else {
                return None;
            };
            let descriptor = &self.productions[*production];
            descriptor.parse_label.as_deref().or_else(|| {
                if descriptor.syntactic_subsort
                    || (descriptor.parse_label.is_none() && children.len() == 1)
                {
                    children
                        .first()
                        .and_then(|child| self.packed_top_parse_label(child))
                } else {
                    None
                }
            })
        })
    }

    fn filter_packed_priority_child(
        &self,
        parent: usize,
        child: Rc<PackedTerm>,
        side: Option<Side>,
        memo: &mut PackedTransformMemo,
        child_memo: &mut PackedPriorityChildMemo,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        // Invariant: a cache hit has the same identity, parent production, and associativity side
        // as the requested decision.
        let identity = Rc::as_ptr(&child);
        let key = (identity, parent, side);
        if let Some((_, filtered)) = child_memo.get(&key) {
            return filtered.clone();
        }
        let filtered = self.filter_packed_priority_child_uncached(
            parent,
            Rc::clone(&child),
            side,
            memo,
            child_memo,
        );
        child_memo.insert(key, (child, filtered.clone()));
        filtered
    }

    fn filter_packed_priority_child_uncached(
        &self,
        parent: usize,
        child: Rc<PackedTerm>,
        side: Option<Side>,
        memo: &mut PackedTransformMemo,
        child_memo: &mut PackedPriorityChildMemo,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        // Invariant: every processed alternative contributes one filtered result or one
        // diagnostic, and retained results remain ordered and unique.
        if let PackedNode::Ambiguity(alternatives) = &child.node {
            let mut retained = BTreeSet::new();
            let mut errors = Vec::new();
            for alternative in alternatives {
                match self.filter_packed_priority_child(
                    parent,
                    Rc::clone(alternative),
                    side,
                    memo,
                    child_memo,
                ) {
                    Ok(alternative) => match &alternative.node {
                        PackedNode::Ambiguity(nested) => retained.extend(nested.iter().cloned()),
                        _ => {
                            retained.insert(alternative);
                        }
                    },
                    Err(error) => {
                        errors.push((Rc::clone(alternative), error));
                    }
                }
            }
            return if retained.is_empty() {
                Err(canonical_packed_error(errors))
            } else if packed_sets_share_nodes(&retained, alternatives) {
                Ok(child)
            } else {
                Ok(PackedTerm::ambiguity(retained))
            };
        }
        if let Some(side) = side
            && let PackedNode::Production { production, .. } = &child.node
        {
            let shallow = ParsedTerm::Production {
                production: *production,
                children: Vec::new(),
                metadata: crate::kast::TermMetadata::default(),
            };
            if let Some(error) = self.child_violation(&self.productions[parent], &shallow, side) {
                return Err(error);
            }
        }
        self.filter_packed_priority_memo(child, memo, child_memo)
    }

    /// Apply priority and associativity to every packed ambiguity branch.
    ///
    /// An ambiguity denotes a set of alternative trees, and priority and associativity judge each
    /// tree separately, so the filter removes exactly the invalid alternatives beneath an
    /// ambiguity. Treating a packed child as one opaque node either retained invalid associations
    /// or discarded valid siblings, so this transformation performs the same branch-wise filter.
    /// This owned pass is a test-only (`#[cfg(test)]`) counterpart of the packed pass for edges
    /// that generated record productions expose after they collapse, which their parser-only
    /// wrappers deliberately exempt from priority checking.
    #[cfg(test)]
    pub(super) fn filter_priority(&self, term: ParsedTerm) -> Result<ParsedTerm, ParseError> {
        crate::stack::guarded(|| {
            match term.into_parts() {
                ParsedParts::Term(leaf) => Ok(ParsedTerm::Term(leaf)),
                ParsedParts::Ambiguity(mut alternatives) => {
                    // A rule body's rewrite, sequence and `#let` scope over the user syntax around
                    // them, so these three structural forms take precedence over every other
                    // top-level interpretation, in this order. This is what makes
                    // `lhs => rhs #And condition` scope as a rewrite whose RHS contains `#And`
                    // instead of retaining the competing `#And(rewrite(lhs, rhs), condition)` tree.
                    for preferred in ["#KRewrite", "#KSequence", "#let"] {
                        let matching = alternatives
                            .iter()
                            .filter(|alternative| {
                                self.top_parse_label(alternative) == Some(preferred)
                            })
                            .cloned()
                            .collect::<BTreeSet<_>>();
                        if !matching.is_empty() {
                            alternatives = matching;
                        }
                    }
                    let mut retained = BTreeSet::new();
                    let mut first_error = None;
                    for alternative in alternatives {
                        match self
                            .filter_priority(alternative)
                            .map(ParsedTerm::into_parts)
                        {
                            Ok(ParsedParts::Ambiguity(nested)) => retained.extend(nested),
                            Ok(alternative) => {
                                retained.insert(ParsedTerm::from(alternative));
                            }
                            Err(error) => {
                                first_error.get_or_insert(error);
                            }
                        }
                    }
                    match retained.len() {
                        0 => Err(first_error.expect("an empty ambiguity had no valid alternative")),
                        1 => Ok(retained.pop_first().expect("length was one")),
                        _ => Ok(ParsedTerm::Ambiguity(retained)),
                    }
                }
                ParsedParts::Production {
                    production,
                    children,
                    metadata,
                } => {
                    let descriptor = &self.productions[production];
                    let checked = if descriptor.record.is_some() || descriptor.syntactic_subsort {
                        BTreeSet::new()
                    } else {
                        descriptor.apply_priority.clone().unwrap_or_else(|| {
                            let mut positions = BTreeSet::new();
                            if matches!(descriptor.items.first(), Some(Item::NonTerminal(_))) {
                                positions.insert(1);
                            }
                            if matches!(descriptor.items.last(), Some(Item::NonTerminal(_))) {
                                positions.insert(children.len());
                            }
                            positions
                        })
                    };
                    let child_count = children.len();
                    let children = children
                        .into_iter()
                        .enumerate()
                        .map(|(index, child)| {
                            let position = index + 1;
                            let side = checked.contains(&position).then(|| {
                                if position == 1
                                    && matches!(
                                        descriptor.items.first(),
                                        Some(Item::NonTerminal(_))
                                    )
                                {
                                    Side::Left
                                } else if position == child_count
                                    && matches!(descriptor.items.last(), Some(Item::NonTerminal(_)))
                                {
                                    Side::Right
                                } else {
                                    Side::Middle
                                }
                            });
                            self.filter_priority_child(descriptor, child, side)
                        })
                        .collect::<Result<_, _>>()?;
                    Ok(ParsedTerm::Production {
                        production,
                        children,
                        metadata,
                    })
                }
                ParsedParts::InstantiatedProduction { .. } => {
                    unreachable!("instantiated productions are created after priority filtering")
                }
            }
        })
    }

    #[cfg(test)]
    fn top_parse_label<'a>(&'a self, term: &'a ParsedTerm) -> Option<&'a str> {
        crate::stack::guarded(|| {
            let (production, children) = match term {
                ParsedTerm::Production {
                    production,
                    children,
                    ..
                }
                | ParsedTerm::InstantiatedProduction {
                    production,
                    children,
                    ..
                } => (*production, children),
                ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => return None,
            };
            let descriptor = &self.productions[production];
            descriptor.parse_label.as_deref().or_else(|| {
                if descriptor.syntactic_subsort
                    || (descriptor.parse_label.is_none() && children.len() == 1)
                {
                    children
                        .first()
                        .and_then(|child| self.top_parse_label(child))
                } else {
                    None
                }
            })
        })
    }

    #[cfg(test)]
    fn filter_priority_child(
        &self,
        parent: &Production,
        child: ParsedTerm,
        side: Option<Side>,
    ) -> Result<ParsedTerm, ParseError> {
        crate::stack::guarded(|| {
            let mut child = child;
            if let ParsedTerm::Ambiguity(alternatives) = &mut child {
                let alternatives = std::mem::take(alternatives);
                let mut retained = BTreeSet::new();
                let mut first_error = None;
                for alternative in alternatives {
                    match self
                        .filter_priority_child(parent, alternative, side)
                        .map(ParsedTerm::into_parts)
                    {
                        Ok(ParsedParts::Ambiguity(nested)) => retained.extend(nested),
                        Ok(alternative) => {
                            retained.insert(ParsedTerm::from(alternative));
                        }
                        Err(error) => {
                            first_error.get_or_insert(error);
                        }
                    }
                }
                return match retained.len() {
                    0 => Err(first_error.expect("an empty ambiguity had no valid alternative")),
                    1 => Ok(retained.pop_first().expect("length was one")),
                    _ => Ok(ParsedTerm::Ambiguity(retained)),
                };
            }
            if let Some(side) = side
                && let Some(error) = self.child_violation(parent, &child, side)
            {
                return Err(error);
            }
            self.filter_priority(child)
        })
    }

    /// Whether the priority filter rejects a node of production `child` as the child of a node
    /// of production `parent` at child position `position` (1-based, among the parent's
    /// nonterminals), whatever the two nodes' children are: the check
    /// [`Self::filter_packed_priority_memo`] makes at that edge finds a scope, cast, priority or
    /// associativity violation, so no reading the filter accepts has that edge. Both
    /// productions are those of the nodes: a production whose node is its child's
    /// (`build_packed_term`) has no parse label and is never rejected, and a token production
    /// builds no production node. A record production's edges are checked only after its
    /// node is collapsed into another production's, so for one the answer is `false`.
    pub(super) fn edge_rejects(&self, parent: usize, child: usize, position: usize) -> bool {
        let descriptor = &self.productions[parent];
        let child_descriptor = &self.productions[child];
        if descriptor.record.is_some()
            || descriptor.syntactic_subsort
            || child_descriptor.record.is_some()
            || child_descriptor.token
        {
            return false;
        }
        let child_count = descriptor
            .items
            .iter()
            .filter(|item| matches!(item, Item::NonTerminal(_)))
            .count();
        let first = position == 1 && matches!(descriptor.items.first(), Some(Item::NonTerminal(_)));
        let last = position == child_count
            && matches!(descriptor.items.last(), Some(Item::NonTerminal(_)));
        let checked = match &descriptor.apply_priority {
            Some(positions) => positions.contains(&position),
            None => first || last,
        };
        if !checked {
            return false;
        }
        let side = if first {
            Side::Left
        } else if last {
            Side::Right
        } else {
            Side::Middle
        };
        let shallow = ParsedTerm::Production {
            production: child,
            children: Vec::new(),
            metadata: crate::kast::TermMetadata::default(),
        };
        self.child_violation(descriptor, &shallow, side).is_some()
    }

    fn child_violation(
        &self,
        parent: &Production,
        child: &ParsedTerm,
        side: Side,
    ) -> Option<ParseError> {
        let ParsedTerm::Production {
            production: child, ..
        } = child
        else {
            return None;
        };
        let child = &self.productions[*child];
        let (Some(parent_label), Some(child_label)) = (&parent.parse_label, &child.parse_label)
        else {
            return None;
        };
        let allowed_parent = |exceptions: &[InternalLabel]| {
            // A bracket has a parse label for priority checks but no semantic klabel.
            // The reference restricts rewrite/sequence/let scope only under klabels.
            parent.syntactic_subsort
                || parent.label.is_none()
                || exceptions
                    .iter()
                    .any(|label| parent_label == label.as_str())
        };
        if child_label == InternalLabel::KRewrite.as_str() && !allowed_parent(&SCOPE_REWRITE) {
            return Some(ParseError::Scope {
                parent: parent_label.clone(),
                child: child_label.clone(),
            });
        }
        if child_label == InternalLabel::KSequence.as_str() && !allowed_parent(&SCOPE_SEQUENCE) {
            return Some(ParseError::Scope {
                parent: parent_label.clone(),
                child: child_label.clone(),
            });
        }
        if child_label == InternalLabel::Let.as_str() && !allowed_parent(&SCOPE_LET) {
            return Some(ParseError::Scope {
                parent: parent_label.clone(),
                child: child_label.clone(),
            });
        }
        if (parent_label == InternalLabel::SyntacticCast.as_str()
            || matches!(
                GeneratedLabel::of_name(parent_label),
                Some(GeneratedLabel::SemanticCast { .. })
            ))
            && matches!(child.items.last(), Some(Item::NonTerminal(_)))
        {
            return Some(ParseError::CastPriority {
                cast: parent_label.clone(),
                child: child_label.clone(),
            });
        }
        if self.priorities.less_than(parent_label, child_label) {
            return Some(ParseError::Priority {
                parent: parent_label.clone(),
                child: child_label.clone(),
            });
        }
        if side == Side::Right && self.associativity_forbids(parent_label, child_label, false) {
            return Some(ParseError::Associativity {
                parent: parent_label.clone(),
                child: child_label.clone(),
                side: "right",
            });
        }
        if side == Side::Left && self.associativity_forbids(parent_label, child_label, true) {
            return Some(ParseError::Associativity {
                parent: parent_label.clone(),
                child: child_label.clone(),
                side: "left",
            });
        }
        None
    }

    /// Lower an inferred tree to the one term it denotes, or report the readings it still has.
    ///
    /// A tree with ambiguity nodes denotes a set of readings: the distinct terms its choices
    /// lower to, compared without their metadata as parse results are. When the set has one
    /// element the result is that term, as the first choice lowers it. Otherwise the report is
    /// a function of the set, so two packings of one set report alike (`ambiguity_report`).
    pub(super) fn resolve_ambiguities(&self, term: ParsedTerm) -> Result<Term, ParseError> {
        let _span = measure::algorithm_span(Algorithm::ParserDisambiguationResolveAmbiguity);
        let mut products = Vec::new();
        match self.resolve_ambiguities_node(term, &mut products)? {
            Readings::One(term) => Ok(term),
            readings => Err(self.ambiguity_report(&readings, &products)),
        }
    }

    /// The readings of one node of an inferred tree, with the nodes of its products in
    /// `products`.
    ///
    /// A production node over children of one reading each is lowered as it stands. Over a
    /// child of several readings, its readings are one per combination of its children's
    /// readings; when its lowering tells distinct children apart (`lowering_keeps_children`),
    /// distinct combinations are distinct readings and the combinations are kept unexpanded
    /// as a product. An ambiguity node's readings are the union of its alternatives'; a union
    /// can hold one term twice, so the alternatives are expanded and their terms compared,
    /// keeping each distinct term as the first alternative lowers it. An expansion lowers at
    /// most one term per tree below the node. A tree with one reading expands nothing it did
    /// not lower already: an alternative with several readings makes the union several, so the
    /// expansions of products happen only for a tree that is reported, or below a node whose
    /// lowering joins its children.
    ///
    /// ```toml algorithm-site
    /// id = "parser.diagnostic.ambiguity"
    /// role = "part"
    /// sites = ["Grammar::resolve_ambiguities_node", "Grammar::ambiguity_report", "Grammar::factor_readings", "Grammar::ambiguity_place"]
    /// ```
    fn resolve_ambiguities_node(
        &self,
        term: ParsedTerm,
        products: &mut Vec<ProductNode>,
    ) -> Result<Readings, ParseError> {
        crate::stack::guarded(|| match term.into_parts() {
            ParsedParts::Term(term) => Ok(Readings::One(term)),
            ParsedParts::Production {
                production,
                children,
                metadata,
            } => self.resolve_production_node(production, None, children, metadata, products),
            ParsedParts::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => self.resolve_production_node(
                production,
                Some(parameters),
                children,
                metadata,
                products,
            ),
            ParsedParts::Ambiguity(alternatives) => {
                let mut readings = DistinctReadings::default();
                for alternative in alternatives {
                    let alternative = self.resolve_ambiguities_node(alternative, products)?;
                    self.expand_readings(alternative, products, &mut readings)?;
                }
                Ok(readings.into_readings())
            }
        })
    }

    fn resolve_production_node(
        &self,
        production: usize,
        parameters: Option<Vec<Sort>>,
        children: Vec<ParsedTerm>,
        metadata: crate::kast::TermMetadata,
        products: &mut Vec<ProductNode>,
    ) -> Result<Readings, ParseError> {
        let children = children
            .into_iter()
            .map(|child| self.resolve_ambiguities_node(child, products))
            .collect::<Result<Vec<_>, _>>()?;
        if children
            .iter()
            .all(|child| matches!(child, Readings::One(_)))
        {
            let children = children
                .into_iter()
                .map(|child| match child {
                    Readings::One(term) => term,
                    Readings::Listed(_) | Readings::Product(_) => {
                        unreachable!("every child has one reading")
                    }
                })
                .collect();
            return self
                .lower_production(production, parameters.as_deref(), children, metadata)
                .map(Readings::One);
        }
        let node = ProductNode {
            production,
            parameters,
            metadata,
            children,
        };
        if lowering_keeps_children(&self.productions[production], node.children.len()) {
            products.push(node);
            return Ok(Readings::Product(products.len() - 1));
        }
        let mut readings = DistinctReadings::default();
        self.expand_product(&node, products, &mut readings)?;
        Ok(readings.into_readings())
    }

    /// Add every term of `readings` to `into`.
    fn expand_readings(
        &self,
        readings: Readings,
        products: &[ProductNode],
        into: &mut DistinctReadings,
    ) -> Result<(), ParseError> {
        match readings {
            Readings::One(term) => into.insert(term),
            Readings::Listed(terms) => terms.into_iter().for_each(|term| into.insert(term)),
            Readings::Product(index) => self.expand_product(&products[index], products, into)?,
        }
        Ok(())
    }

    /// Add to `into` the lowering of every combination of `node`'s children's readings, the
    /// first child's varying slowest.
    fn expand_product(
        &self,
        node: &ProductNode,
        products: &[ProductNode],
        into: &mut DistinctReadings,
    ) -> Result<(), ParseError> {
        crate::stack::guarded(|| {
            let mut choices = Vec::with_capacity(node.children.len());
            for child in &node.children {
                let mut readings = DistinctReadings::default();
                self.expand_readings(child.clone(), products, &mut readings)?;
                choices.push(readings.terms);
            }
            let mut position = vec![0; choices.len()];
            loop {
                let children = position
                    .iter()
                    .zip(&choices)
                    .map(|(index, terms)| terms[*index].clone())
                    .collect();
                into.insert(self.lower_production(
                    node.production,
                    node.parameters.as_deref(),
                    children,
                    node.metadata.clone(),
                )?);
                let Some(next) = (0..choices.len())
                    .rev()
                    .find(|child| position[*child] + 1 < choices[*child].len())
                else {
                    return Ok(());
                };
                position[next] += 1;
                position[next + 1..].fill(0);
            }
        })
    }

    /// The diagnostic of a tree with several readings: the smallest subterm outside which
    /// every reading agrees, and the number of distinct readings.
    ///
    /// The readings are narrowed to that subterm (`Grammar::factor_readings`). When the
    /// readings of the subterm are every combination of the readings of several of its
    /// children, they differ independently at several places, and each place is reported with
    /// its own readings, the count being their product; otherwise the subterm's readings are
    /// listed. Both are properties of the set of readings, read the same way from a product
    /// left unexpanded and from its expansion, so two packings of one set of readings give one
    /// diagnostic.
    fn ambiguity_report(&self, readings: &Readings, products: &[ProductNode]) -> ParseError {
        match self.factor_readings(readings, products) {
            FactoredReadings::Place(place) => ParseError::Ambiguous {
                parses: place.alternatives.len(),
                alternatives: place.alternatives,
                span: place.span,
                places: Vec::new(),
            },
            FactoredReadings::Independent { span, places } => ParseError::Ambiguous {
                parses: places.iter().fold(1usize, |count, place| {
                    count.saturating_mul(place.alternatives.len())
                }),
                alternatives: Vec::new(),
                span,
                places,
            },
        }
    }

    /// The smallest subterm outside which several `readings` agree, as one place or as
    /// independent places.
    ///
    /// Below a product whose children all have one reading but one, every reading agrees
    /// outside that child. A product with several such children has as readings every
    /// combination of theirs, so its places are theirs. A listed set is narrowed down its terms
    /// while they share a head and differ at one child only; where they differ at several
    /// children and are every combination of the distinct terms at those children, they are a
    /// product of those children's readings as well.
    fn factor_readings(&self, readings: &Readings, products: &[ProductNode]) -> FactoredReadings {
        crate::stack::guarded(|| match readings {
            Readings::One(_) => unreachable!("only several readings are factored"),
            Readings::Product(index) => {
                let node = &products[*index];
                let several = node
                    .children
                    .iter()
                    .filter(|child| !matches!(child, Readings::One(_)))
                    .collect::<Vec<_>>();
                if let [only] = several[..] {
                    return self.factor_readings(only, products);
                }
                let places = several
                    .into_iter()
                    .flat_map(|child| self.factor_readings(child, products).into_places())
                    .collect();
                FactoredReadings::Independent {
                    span: node.metadata.span,
                    places,
                }
            }
            Readings::Listed(terms) => {
                let mut place = terms.iter().collect::<Vec<_>>();
                while let Some((positions, children)) = differing_children(&place) {
                    if let [position] = positions[..] {
                        place = children[position].clone();
                        continue;
                    }
                    let distinct = positions
                        .iter()
                        .map(|position| {
                            children[*position].iter().copied().collect::<BTreeSet<_>>()
                        })
                        .collect::<Vec<_>>();
                    let combinations = distinct
                        .iter()
                        .try_fold(1usize, |count, terms| count.checked_mul(terms.len()));
                    if combinations != Some(place.len()) {
                        break;
                    }
                    let places = distinct
                        .into_iter()
                        .flat_map(|terms| {
                            let terms = terms.into_iter().cloned().collect();
                            self.factor_readings(&Readings::Listed(terms), products)
                                .into_places()
                        })
                        .collect();
                    return FactoredReadings::Independent {
                        span: covered_span(&place),
                        places,
                    };
                }
                FactoredReadings::Place(self.ambiguity_place(place))
            }
        })
    }

    /// The distinct readings of one place, in term order, with the span they cover.
    fn ambiguity_place(&self, mut terms: Vec<&Term>) -> AmbiguityPlace {
        terms.sort();
        terms.dedup();
        AmbiguityPlace {
            span: covered_span(&terms),
            alternatives: terms
                .into_iter()
                .map(|term| AmbiguousParse {
                    production: self.reading_production_text(term),
                    term: term.to_string(),
                })
                .collect(),
        }
    }

    /// The text of the production a reading's root came from: the source production its
    /// metadata names, or, for a production the grammar generated, the one text of the
    /// grammar's productions of the root's label.
    fn reading_production_text(&self, term: &Term) -> Option<String> {
        if let Some(text) = term
            .metadata()
            .and_then(|metadata| metadata.production)
            .and_then(|production| self.source_production_texts.get(&production))
        {
            return Some(text.as_str().to_owned());
        }
        let Term::Apply { label, .. } = term.unannotated() else {
            return None;
        };
        let mut texts = self
            .productions
            .iter()
            .filter(|production| {
                production
                    .label
                    .as_ref()
                    .is_some_and(|own| own.name == label.name)
            })
            .filter_map(|production| production.source_production_text.as_ref())
            .map(|text| text.as_str());
        let first = texts.next()?;
        texts.all(|text| text == first).then(|| first.to_owned())
    }

    fn lower_production(
        &self,
        production: usize,
        parameters: Option<&[Sort]>,
        children: Vec<Term>,
        mut metadata: crate::kast::TermMetadata,
    ) -> Result<Term, ParseError> {
        let production = &self.productions[production];
        metadata.production = production.source_production;
        let span = metadata.span;
        let term = if let Some(parameters) = parameters {
            let mut instantiated = production.clone();
            if let Some(label) = &mut instantiated.label {
                label.parameters = parameters.to_vec();
            }
            lower_term(&instantiated, children, span, &self.sort_denotations)?
        } else {
            lower_term(production, children, span, &self.sort_denotations)?
        };
        Ok(term.with_metadata(metadata))
    }

    /// Remove the nodes that only shaped the parse: a bracket denotes its child, and a syntactic
    /// cast only restricted the sort the parser chose. Semantic and outer casts constrain the
    /// term itself and are retained.
    pub(super) fn remove_brackets_and_syntactic_casts(&self, term: ParsedTerm) -> ParsedTerm {
        let _span = measure::algorithm_span(Algorithm::ParserDisambiguationRemoveBracketsCasts);
        self.remove_brackets_and_syntactic_casts_node(term)
    }

    fn remove_brackets_and_syntactic_casts_node(&self, term: ParsedTerm) -> ParsedTerm {
        crate::stack::guarded(|| match term.into_parts() {
            ParsedParts::Term(leaf) => ParsedTerm::Term(leaf),
            ParsedParts::Ambiguity(alternatives) => ParsedTerm::Ambiguity(
                alternatives
                    .into_iter()
                    .map(|alternative| self.remove_brackets_and_syntactic_casts_node(alternative))
                    .collect(),
            ),
            ParsedParts::Production {
                production,
                mut children,
                metadata,
            } => {
                let descriptor = &self.productions[production];
                let syntactic_cast = descriptor.label.as_ref().is_some_and(|label| {
                    [
                        InternalLabel::SyntacticCast,
                        InternalLabel::SyntacticCastBraced,
                    ]
                    .iter()
                    .any(|cast| label.is(*cast))
                });
                if (descriptor.bracket || syntactic_cast) && children.len() == 1 {
                    return self.remove_brackets_and_syntactic_casts_node(children.remove(0));
                }
                ParsedTerm::Production {
                    production,
                    metadata,
                    children: children
                        .into_iter()
                        .map(|child| self.remove_brackets_and_syntactic_casts_node(child))
                        .collect(),
                }
            }
            ParsedParts::InstantiatedProduction {
                production,
                parameters,
                mut children,
                metadata,
            } => {
                let descriptor = &self.productions[production];
                let syntactic_cast = descriptor.label.as_ref().is_some_and(|label| {
                    [
                        InternalLabel::SyntacticCast,
                        InternalLabel::SyntacticCastBraced,
                    ]
                    .iter()
                    .any(|cast| label.is(*cast))
                });
                if (descriptor.bracket || syntactic_cast) && children.len() == 1 {
                    return self.remove_brackets_and_syntactic_casts_node(children.remove(0));
                }
                ParsedTerm::InstantiatedProduction {
                    production,
                    parameters,
                    metadata,
                    children: children
                        .into_iter()
                        .map(|child| self.remove_brackets_and_syntactic_casts_node(child))
                        .collect(),
                }
            }
        })
    }

    /// Resolve `#KApply` nodes to every visible production with the same label and arity.
    pub(super) fn resolve_packed_applications(
        &self,
        term: Rc<PackedTerm>,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let _span = measure::algorithm_span(Algorithm::ParserDisambiguationResolveApplications);
        self.resolve_packed_applications_memo(term, &mut HashMap::new(), &mut KListMemo::default())
    }

    fn resolve_packed_applications_memo(
        &self,
        term: Rc<PackedTerm>,
        memo: &mut PackedTransformMemo,
        klists: &mut KListMemo,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        crate::stack::guarded(|| {
            // Invariant: every memoized identity has its complete `#KApply` resolution; recursion only
            // visits identities absent from the memo.
            let identity = Rc::as_ptr(&term);
            if let Some((_, resolved)) = memo.get(&identity) {
                return resolved.clone();
            }
            let resolved = (|| -> PackedTransformResult {
                match &term.node {
                    PackedNode::InstantiatedProduction { .. } => {
                        unreachable!(
                            "instantiated productions are created after application resolution"
                        )
                    }
                    PackedNode::Term(_) => Ok(Rc::clone(&term)),
                    PackedNode::Ambiguity(alternatives) => {
                        let mut resolved = BTreeSet::new();
                        let mut first_error = None;
                        for alternative in klists.order.sorted(alternatives) {
                            match self.resolve_packed_applications_memo(
                                Rc::clone(&alternative),
                                memo,
                                klists,
                            ) {
                                Ok(alternative) => match &alternative.node {
                                    PackedNode::Ambiguity(nested) => {
                                        resolved.extend(nested.iter().cloned())
                                    }
                                    _ => {
                                        resolved.insert(alternative);
                                    }
                                },
                                Err(error) => {
                                    first_error.get_or_insert(error);
                                }
                            }
                        }
                        if resolved.is_empty() {
                            Err(first_error.expect("an empty ambiguity had no resolution result"))
                        } else {
                            Ok(PackedTerm::ambiguity(resolved))
                        }
                    }
                    PackedNode::Production {
                        production,
                        children,
                        metadata,
                    } => {
                        if self.productions[*production]
                            .label
                            .as_ref()
                            .is_some_and(|label| label.is(InternalLabel::KApply))
                        {
                            measure::bump(Counter::ParserPackedApplicationResolutions);
                        }
                        let children = children
                            .iter()
                            .map(|child| {
                                self.resolve_packed_applications_memo(
                                    Rc::clone(child),
                                    memo,
                                    klists,
                                )
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        if self.productions[*production]
                            .label
                            .as_ref()
                            .map(|label| label.name.as_str())
                            != Some(InternalLabel::KApply.as_str())
                        {
                            Ok(PackedTerm::production(
                                *production,
                                children,
                                metadata.clone(),
                            ))
                        } else {
                            let [label, arguments] = children.as_slice() else {
                                return Err(ParseError::UnknownApplication {
                                    label: "<malformed>".into(),
                                    arity: children.len().saturating_sub(1),
                                });
                            };
                            let label = packed_klabel_name(label).ok_or_else(|| {
                                ParseError::UnknownApplication {
                                    label: "<malformed>".into(),
                                    arity: 0,
                                }
                            })?;
                            // Only argument vectors as long as some production of the label
                            // can match; an application with none reports the shortest
                            // reading of its arguments.
                            let longest = self
                                .productions
                                .iter()
                                .enumerate()
                                .filter(|(candidate, candidate_production)| {
                                    *candidate != *production
                                        && candidate_production.record.is_none()
                                        && candidate_production.label.as_ref().is_some_and(
                                            |candidate_label| candidate_label.name == label,
                                        )
                                })
                                .map(|(_, candidate_production)| {
                                    production_arity(candidate_production)
                                })
                                .max();
                            let argument_lists = match longest {
                                Some(longest) => {
                                    self.flatten_packed_klist(arguments, longest, klists)?
                                }
                                None => Rc::default(),
                            };
                            let mut candidates = BTreeSet::new();
                            for arguments in argument_lists.iter() {
                                for (candidate, candidate_production) in
                                    self.productions.iter().enumerate()
                                {
                                    if candidate != *production
                                        && candidate_production.record.is_none()
                                        && candidate_production.label.as_ref().is_some_and(
                                            |candidate_label| candidate_label.name == label,
                                        )
                                        && production_arity(candidate_production) == arguments.len()
                                    {
                                        let candidate = candidate_production
                                            .term_production
                                            .unwrap_or(candidate);
                                        let mut candidate_metadata = metadata.clone();
                                        candidate_metadata.production =
                                            self.productions[candidate].source_production;
                                        candidates.insert(PackedTerm::production(
                                            candidate,
                                            arguments.clone(),
                                            candidate_metadata,
                                        ));
                                    }
                                }
                            }
                            if candidates.is_empty() {
                                Err(ParseError::UnknownApplication {
                                    label,
                                    arity: self.shortest_packed_klist(arguments, klists),
                                })
                            } else {
                                Ok(PackedTerm::ambiguity(candidates))
                            }
                        }
                    }
                }
            })();
            memo.insert(identity, (term, resolved.clone()));
            resolved
        })
    }

    /// The argument vectors that the readings of `term`, a `#KList` reading of an
    /// application's arguments, flatten to, those at most `longest` long, each once.
    ///
    /// The readings of a comma list are an ambiguous `K "," K` tree whose sublists may also
    /// read as single elements, so their number is exponential in the list's length, while
    /// the packed forest shares every sublist. Each node's vectors are computed once
    /// (`klists`), and a vector longer than every arity of the label is dropped as soon as it
    /// is built, since appending never shortens it.
    fn flatten_packed_klist(
        &self,
        term: &Rc<PackedTerm>,
        longest: usize,
        klists: &mut KListMemo,
    ) -> Result<ArgumentLists, ParseError> {
        crate::stack::guarded(|| {
            let key = (Rc::as_ptr(term), longest);
            if let Some((_, flattened)) = klists.flattened.get(&key) {
                return Ok(Rc::clone(flattened));
            }
            let mut seen = HashSet::new();
            let mut flattened = Vec::new();
            let mut keep = |arguments: Vec<Rc<PackedTerm>>| {
                if arguments.len() <= longest
                    && seen.insert(arguments.iter().map(Rc::as_ptr).collect::<Vec<_>>())
                {
                    flattened.push(arguments);
                }
            };
            match &term.node {
                PackedNode::InstantiatedProduction { .. } => {
                    unreachable!("instantiated productions are created after K-list flattening")
                }
                // The vectors are a set (an application's candidates are), so the
                // alternatives are read in any order.
                PackedNode::Ambiguity(alternatives) => {
                    for alternative in alternatives {
                        for arguments in self
                            .flatten_packed_klist(alternative, longest, klists)?
                            .iter()
                        {
                            keep(arguments.clone());
                        }
                    }
                }
                PackedNode::Production {
                    production,
                    children,
                    ..
                } => match self.productions[*production]
                    .label
                    .as_ref()
                    .map(|label| label.name.as_str())
                {
                    Some("#EmptyKList") => keep(Vec::new()),
                    Some(name) if name == InternalLabel::KList.as_str() && children.len() == 2 => {
                        let left = self.flatten_packed_klist(&children[0], longest, klists)?;
                        let right = self.flatten_packed_klist(&children[1], longest, klists)?;
                        for left in left.iter() {
                            for right in right.iter() {
                                if left.len() + right.len() <= longest {
                                    keep(left.iter().chain(right).cloned().collect());
                                }
                            }
                        }
                    }
                    _ => keep(vec![Rc::clone(term)]),
                },
                PackedNode::Term(_) => keep(vec![Rc::clone(term)]),
            }
            let flattened = Rc::new(flattened);
            klists
                .flattened
                .insert(key, (Rc::clone(term), Rc::clone(&flattened)));
            Ok(flattened)
        })
    }

    /// The length of the shortest argument vector a reading of `term`, a `#KList` reading of an
    /// application's arguments, flattens to (as [`Self::flatten_packed_klist`] without a bound),
    /// computed once per node.
    fn shortest_packed_klist(&self, term: &Rc<PackedTerm>, klists: &mut KListMemo) -> usize {
        crate::stack::guarded(|| {
            if let Some((_, shortest)) = klists.shortest.get(&Rc::as_ptr(term)) {
                return *shortest;
            }
            let shortest = match &term.node {
                PackedNode::InstantiatedProduction { .. } => {
                    unreachable!("instantiated productions are created after K-list flattening")
                }
                PackedNode::Ambiguity(alternatives) => alternatives
                    .iter()
                    .map(|alternative| self.shortest_packed_klist(alternative, klists))
                    .min()
                    .unwrap_or(0),
                PackedNode::Production {
                    production,
                    children,
                    ..
                } => match self.productions[*production]
                    .label
                    .as_ref()
                    .map(|label| label.name.as_str())
                {
                    Some("#EmptyKList") => 0,
                    Some(name) if name == InternalLabel::KList.as_str() && children.len() == 2 => {
                        self.shortest_packed_klist(&children[0], klists)
                            + self.shortest_packed_klist(&children[1], klists)
                    }
                    _ => 1,
                },
                PackedNode::Term(_) => 1,
            };
            klists
                .shortest
                .insert(Rc::as_ptr(term), (Rc::clone(term), shortest));
            shortest
        })
    }

    #[cfg(test)]
    pub(super) fn resolve_applications(&self, term: ParsedTerm) -> Result<ParsedTerm, ParseError> {
        crate::stack::guarded(|| match term.into_parts() {
            ParsedParts::Term(leaf) => Ok(ParsedTerm::Term(leaf)),
            ParsedParts::Ambiguity(alternatives) => {
                let mut resolved = BTreeSet::new();
                let mut first_error = None;
                for alternative in alternatives {
                    match self
                        .resolve_applications(alternative)
                        .map(ParsedTerm::into_parts)
                    {
                        Ok(ParsedParts::Ambiguity(nested)) => resolved.extend(nested),
                        Ok(alternative) => {
                            resolved.insert(ParsedTerm::from(alternative));
                        }
                        Err(error) => {
                            first_error.get_or_insert(error);
                        }
                    }
                }
                match resolved.len() {
                    0 => Err(first_error.expect("an empty ambiguity had no resolution result")),
                    1 => Ok(resolved.pop_first().expect("length was one")),
                    _ => Ok(ParsedTerm::Ambiguity(resolved)),
                }
            }
            ParsedParts::Production {
                production,
                children,
                metadata,
            } => {
                let children = children
                    .into_iter()
                    .map(|child| self.resolve_applications(child))
                    .collect::<Result<Vec<_>, _>>()?;
                if self.productions[production]
                    .label
                    .as_ref()
                    .map(|label| label.name.as_str())
                    != Some(InternalLabel::KApply.as_str())
                {
                    return Ok(ParsedTerm::Production {
                        production,
                        children,
                        metadata,
                    });
                }
                let [label, arguments] = children.as_slice() else {
                    return Err(ParseError::UnknownApplication {
                        label: "<malformed>".into(),
                        arity: children.len().saturating_sub(1),
                    });
                };
                let label = klabel_name(label).ok_or_else(|| ParseError::UnknownApplication {
                    label: "<malformed>".into(),
                    arity: 0,
                })?;
                let argument_lists = self.flatten_klist(arguments)?;
                let arities = argument_lists.iter().map(Vec::len).collect::<BTreeSet<_>>();
                let mut candidates = BTreeSet::new();
                for arguments in argument_lists {
                    for (candidate, candidate_production) in self.productions.iter().enumerate() {
                        if candidate != production
                            && candidate_production.record.is_none()
                            && candidate_production
                                .label
                                .as_ref()
                                .is_some_and(|candidate_label| candidate_label.name == label)
                            && production_arity(candidate_production) == arguments.len()
                        {
                            let candidate =
                                candidate_production.term_production.unwrap_or(candidate);
                            let mut candidate_metadata = metadata.clone();
                            candidate_metadata.production =
                                self.productions[candidate].source_production;
                            candidates.insert(ParsedTerm::Production {
                                production: candidate,
                                children: arguments.clone(),
                                metadata: candidate_metadata,
                            });
                        }
                    }
                }
                match candidates.len() {
                    0 => Err(ParseError::UnknownApplication {
                        label,
                        arity: arities.first().copied().unwrap_or(0),
                    }),
                    1 => Ok(candidates.pop_first().expect("length was one")),
                    _ => Ok(ParsedTerm::Ambiguity(candidates)),
                }
            }
            ParsedParts::InstantiatedProduction { .. } => {
                unreachable!("applications are resolved before sort inference")
            }
        })
    }

    #[cfg(test)]
    fn flatten_klist(&self, term: &ParsedTerm) -> Result<Vec<Vec<ParsedTerm>>, ParseError> {
        crate::stack::guarded(|| {
            let flattened = match term {
                ParsedTerm::Ambiguity(alternatives) => {
                    let mut flattened = Vec::new();
                    for alternative in alternatives {
                        flattened.extend(self.flatten_klist(alternative)?);
                    }
                    flattened
                }
                ParsedTerm::Production {
                    production,
                    children,
                    ..
                } => match self.productions[*production]
                    .label
                    .as_ref()
                    .map(|label| label.name.as_str())
                {
                    Some("#EmptyKList") => vec![Vec::new()],
                    Some(name) if name == InternalLabel::KList.as_str() && children.len() == 2 => {
                        let left = self.flatten_klist(&children[0])?;
                        let right = self.flatten_klist(&children[1])?;
                        left.into_iter()
                            .flat_map(|left| {
                                right.iter().map(move |right| {
                                    let mut combined = left.clone();
                                    combined.extend(right.iter().cloned());
                                    combined
                                })
                            })
                            .collect()
                    }
                    _ => vec![vec![term.clone()]],
                },
                ParsedTerm::Term(_) => vec![vec![term.clone()]],
                ParsedTerm::InstantiatedProduction { .. } => {
                    unreachable!("K lists are flattened before sort inference")
                }
            };
            Ok(flattened)
        })
    }

    /// Factor alternatives with a shared production into one differing child.
    pub(super) fn factor_ambiguities(&self, term: ParsedTerm) -> ParsedTerm {
        crate::stack::guarded(|| match term.into_parts() {
            ParsedParts::Term(leaf) => ParsedTerm::Term(leaf),
            ParsedParts::Production {
                production,
                children,
                metadata,
            } => ParsedTerm::Production {
                production,
                metadata,
                children: children
                    .into_iter()
                    .map(|child| self.factor_ambiguities(child))
                    .collect(),
            },
            ParsedParts::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                metadata,
                children: children
                    .into_iter()
                    .map(|child| self.factor_ambiguities(child))
                    .collect(),
            },
            ParsedParts::Ambiguity(alternatives) => {
                let mut flattened = BTreeSet::new();
                for alternative in alternatives {
                    match self.factor_ambiguities(alternative).into_parts() {
                        ParsedParts::Ambiguity(nested) => flattened.extend(nested),
                        alternative => {
                            flattened.insert(ParsedTerm::from(alternative));
                        }
                    }
                }
                let mut alternatives = flattened;
                if alternatives.len() == 1 {
                    return alternatives.pop_first().expect("length was one");
                }
                if let Some(ParsedTerm::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                    metadata,
                }) = alternatives.first()
                {
                    let production = *production;
                    let parameters = parameters.clone();
                    let children = children.clone();
                    let metadata = metadata.clone();
                    if !alternatives.iter().all(|alternative| {
                        matches!(
                            alternative,
                            ParsedTerm::InstantiatedProduction {
                                production: candidate,
                                parameters: candidate_parameters,
                                children: candidate_children,
                                ..
                            } if *candidate == production
                                && candidate_parameters == &parameters
                                && candidate_children.len() == children.len()
                        )
                    }) {
                        return ParsedTerm::Ambiguity(alternatives);
                    }
                    let differing = (0..children.len())
                        .filter(|index| {
                            alternatives.iter().any(|alternative| {
                                let ParsedTerm::InstantiatedProduction {
                                    children: candidate_children,
                                    ..
                                } = alternative
                                else {
                                    unreachable!()
                                };
                                candidate_children[*index] != children[*index]
                            })
                        })
                        .collect::<Vec<_>>();
                    let [index] = differing.as_slice() else {
                        return ParsedTerm::Ambiguity(alternatives);
                    };
                    let mut factored_children = children;
                    let child_alternatives = alternatives
                        .into_iter()
                        .map(|alternative| {
                            let ParsedParts::InstantiatedProduction { mut children, .. } =
                                alternative.into_parts()
                            else {
                                unreachable!()
                            };
                            children.remove(*index)
                        })
                        .collect();
                    factored_children[*index] =
                        self.factor_ambiguities(ParsedTerm::Ambiguity(child_alternatives));
                    return ParsedTerm::InstantiatedProduction {
                        production,
                        parameters,
                        children: factored_children,
                        metadata,
                    };
                }
                let Some(ParsedTerm::Production {
                    production,
                    children,
                    metadata,
                }) = alternatives.first()
                else {
                    return ParsedTerm::Ambiguity(alternatives);
                };
                let production = *production;
                let children = children.clone();
                let metadata = metadata.clone();
                if !alternatives.iter().all(|alternative| {
                    matches!(
                        alternative,
                        ParsedTerm::Production {
                            production: candidate,
                            children: candidate_children,
                            ..
                        } if *candidate == production && candidate_children.len() == children.len()
                    )
                }) {
                    return ParsedTerm::Ambiguity(alternatives);
                }
                let differing = (0..children.len())
                    .filter(|index| {
                        alternatives.iter().any(|alternative| {
                            let ParsedTerm::Production {
                                children: candidate_children,
                                ..
                            } = alternative
                            else {
                                unreachable!()
                            };
                            candidate_children[*index] != children[*index]
                        })
                    })
                    .collect::<Vec<_>>();
                let [index] = differing.as_slice() else {
                    return ParsedTerm::Ambiguity(alternatives);
                };
                let mut factored_children = children;
                let child_alternatives = alternatives
                    .into_iter()
                    .map(|alternative| {
                        let ParsedParts::Production { mut children, .. } = alternative.into_parts()
                        else {
                            unreachable!()
                        };
                        children.remove(*index)
                    })
                    .collect();
                factored_children[*index] =
                    self.factor_ambiguities(ParsedTerm::Ambiguity(child_alternatives));
                ParsedTerm::Production {
                    production,
                    children: factored_children,
                    metadata,
                }
            }
        })
    }

    /// Resolve a nullary overloaded production to the unique least production with the same
    /// label. Overloads of one label denote one operation at different sorts; a nullary
    /// application has no argument to select among them, so it is read at the most specific
    /// one, whose value injects into every other.
    pub(super) fn resolve_overloaded_terminators(
        &self,
        term: ParsedTerm,
    ) -> Result<ParsedTerm, ParseError> {
        let _span = measure::algorithm_span(Algorithm::ParserDisambiguationResolveTerminators);
        self.resolve_overloaded_terminators_node(term)
    }

    fn resolve_overloaded_terminators_node(
        &self,
        term: ParsedTerm,
    ) -> Result<ParsedTerm, ParseError> {
        crate::stack::guarded(|| match term.into_parts() {
            ParsedParts::Term(leaf) => Ok(ParsedTerm::Term(leaf)),
            ParsedParts::Ambiguity(alternatives) => Ok(ParsedTerm::Ambiguity(
                alternatives
                    .into_iter()
                    .map(|alternative| self.resolve_overloaded_terminators_node(alternative))
                    .collect::<Result<_, _>>()?,
            )),
            ParsedParts::Production {
                production,
                children,
                metadata,
            } => {
                let children = children
                    .into_iter()
                    .enumerate()
                    .map(|(child_index, child)| {
                        if let Some(terminator) =
                            self.program_list_terminator(production, child_index, &child)
                        {
                            Ok(terminator)
                        } else {
                            self.resolve_overloaded_terminators_node(child)
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let current = &self.productions[production];
                let Some(source) = current.source_production else {
                    return Ok(ParsedTerm::Production {
                        production,
                        children,
                        metadata,
                    });
                };
                if !children.is_empty() || !self.overloads.contains(&source) {
                    return Ok(ParsedTerm::Production {
                        production,
                        children,
                        metadata,
                    });
                }

                let candidates = self
                    .productions
                    .iter()
                    .filter_map(|candidate| {
                        let candidate_source = candidate.source_production?;
                        (candidate.label == current.label
                            && production_arity(candidate) == 0
                            && self.overloads.less_than_eq(&candidate_source, &source))
                        .then_some(candidate_source)
                    })
                    .collect::<BTreeSet<_>>();
                let least = self.overloads.minimal(candidates.iter());
                if least.len() != 1 {
                    let possible_sorts = self
                        .productions
                        .iter()
                        .filter(|candidate| {
                            candidate
                                .source_production
                                .is_some_and(|candidate| least.contains(&candidate))
                        })
                        .map(|candidate| candidate.result.clone())
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect();
                    return Err(ParseError::OverloadedTerminator { possible_sorts });
                }
                let selected = *least.first().expect("length was checked above");
                let selected = self
                    .productions
                    .iter()
                    .enumerate()
                    .find_map(|(index, candidate)| {
                        (candidate.source_production == Some(selected)
                            && candidate.label == current.label
                            && production_arity(candidate) == 0)
                            .then_some(index)
                    })
                    .expect("a least source production came from a parser production");
                Ok(ParsedTerm::Production {
                    production: selected,
                    children,
                    metadata,
                })
            }
            ParsedParts::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => Ok(ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                metadata,
                children: children
                    .into_iter()
                    .map(|child| self.resolve_overloaded_terminators_node(child))
                    .collect::<Result<_, _>>()?,
            }),
        })
    }

    /// Apply post-inference overload and `prefer`/`avoid` selection at every ambiguity, pushing
    /// shared-production ambiguity into its one differing child; see
    /// [`Self::filter_overloads_prefer_avoid_node`] for the rule.
    pub(super) fn filter_overloads_prefer_avoid(&self, term: ParsedTerm) -> ParsedTerm {
        let _span = measure::algorithm_span(Algorithm::ParserDisambiguationFilterOverloads);
        self.filter_overloads_prefer_avoid_node(term)
    }

    /// Select among the alternatives of each ambiguity of a sort-inferred tree.
    ///
    /// The input trees are well-sorted and maximal, so every alternative is a reading the
    /// definition admits; this pass only chooses between them and always keeps a non-empty
    /// subset. At an ambiguity node, in order:
    /// 1. drop an alternative whose top production is a less specific overload of another's;
    /// 2. classify each alternative by its top production: keep the `prefer` alternatives if there
    ///    are any, otherwise drop the `avoid` alternatives if some others remain;
    /// 3. filter every surviving alternative recursively;
    /// 4. factor: when the alternatives share their top production and differ in exactly one child,
    ///    the ambiguity moves into that child and the pass continues there;
    /// 5. the frontier step, for an ambiguity that steps 1-4 leave with two or more alternatives.
    ///
    /// Step 2 reads the attribute of the production an alternative uses at the point where the
    /// alternatives diverge. The frontier step ([`Self::select_at_frontier`]) extends that reading
    /// to alternatives that diverge at several positions. The common prefix is the set of
    /// positions whose node header (production, instantiated parameters and arity, or the leaf
    /// itself) is equal in every alternative, together with their ancestors; the frontier is the
    /// set of positions just below it, or the root when the headers already differ there. An
    /// alternative is preferred when its node at some frontier position is `prefer`, and avoided
    /// when one is `avoid`; a node that is itself an ambiguity is neither. The preferred
    /// alternatives are kept if there are any, otherwise the avoided ones are dropped if some
    /// others remain, otherwise all are kept; this repeats over the survivors until nothing
    /// changes, and the result is factored again. Overload specificity stays the per-node step 1.
    ///
    /// At a single divergence point the frontier step is step 2: when the top productions differ
    /// the frontier is the root, and when the alternatives share their top production and differ
    /// in one child, step 4 has already moved the ambiguity there. It therefore acts only on an
    /// ambiguity that steps 1-4 cannot decide, one whose alternatives diverge at two or more
    /// positions, such as a rewrite whose sides both depend on a variable's sort. Because it keeps
    /// a subset, and `resolve_ambiguities` reports only distinct lowered terms, a rule that lowers
    /// to one term without it lowers to the same term with it. An `avoid` production below a
    /// frontier node does not count, as it does not below the top production in step 2.
    fn filter_overloads_prefer_avoid_node(&self, term: ParsedTerm) -> ParsedTerm {
        crate::stack::guarded(|| {
            // Invariant: recursion strictly descends the owned tree (factoring moves an ambiguity
            // strictly downward) and retains exactly the maximal overload choices after prefer/avoid
            // classification.
            match term.into_parts() {
                ParsedParts::Term(leaf) => ParsedTerm::Term(leaf),
                ParsedParts::Production {
                    production,
                    children,
                    metadata,
                } => ParsedTerm::Production {
                    production,
                    metadata,
                    children: children
                        .into_iter()
                        .map(|child| self.filter_overloads_prefer_avoid_node(child))
                        .collect(),
                },
                ParsedParts::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                    metadata,
                } => ParsedTerm::InstantiatedProduction {
                    production,
                    parameters,
                    metadata,
                    children: children
                        .into_iter()
                        .map(|child| self.filter_overloads_prefer_avoid_node(child))
                        .collect(),
                },
                ParsedParts::Ambiguity(mut alternatives) => {
                    if alternatives.len() == 1 {
                        return self.filter_overloads_prefer_avoid_node(
                            alternatives.pop_first().expect("length was one"),
                        );
                    }

                    alternatives = self.remove_overloads(alternatives);
                    if alternatives.len() == 1 {
                        return self.filter_overloads_prefer_avoid_node(
                            alternatives.pop_first().expect("length was one"),
                        );
                    }

                    let preferred = alternatives
                        .iter()
                        .filter(|alternative| self.is_preferred(alternative))
                        .cloned()
                        .collect::<BTreeSet<_>>();
                    if !preferred.is_empty() {
                        alternatives = preferred;
                    } else {
                        let retained = alternatives
                            .iter()
                            .filter(|alternative| !self.is_avoided(alternative))
                            .cloned()
                            .collect::<BTreeSet<_>>();
                        if !retained.is_empty() {
                            alternatives = retained;
                        }
                    }

                    let alternatives = alternatives
                        .into_iter()
                        .map(|alternative| self.filter_overloads_prefer_avoid_node(alternative))
                        .collect::<BTreeSet<_>>();
                    if alternatives.len() == 1 {
                        return alternatives.into_iter().next().expect("length was one");
                    }
                    let ambiguity = ParsedTerm::Ambiguity(alternatives);
                    let factored = self.factor_ambiguities(ambiguity.clone());
                    if factored != ambiguity {
                        return self.filter_overloads_prefer_avoid_node(factored);
                    }
                    let ParsedParts::Ambiguity(alternatives) = ambiguity.into_parts() else {
                        unreachable!("the ambiguity was built above")
                    };
                    let count = alternatives.len();
                    let mut selected = self.select_at_frontier(alternatives);
                    if selected.len() == count {
                        return ParsedTerm::Ambiguity(selected);
                    }
                    if selected.len() == 1 {
                        return selected.pop_first().expect("length was one");
                    }
                    // The survivors are already filtered, and a subset of mutually non-dominated
                    // overloads is unchanged by step 1 and a fixpoint of step 2 and of the frontier
                    // step, so only a factoring change needs another pass.
                    let ambiguity = ParsedTerm::Ambiguity(selected);
                    let factored = self.factor_ambiguities(ambiguity.clone());
                    if factored == ambiguity {
                        ambiguity
                    } else {
                        self.filter_overloads_prefer_avoid_node(factored)
                    }
                }
            }
        })
    }

    /// The frontier step of [`Self::filter_overloads_prefer_avoid_node`]: repeatedly classify the
    /// alternatives by their nodes just below their common prefix and keep the preferred ones,
    /// otherwise drop the avoided ones while some others remain, until a round changes nothing.
    /// Each round either removes an alternative or stops, so there are fewer rounds than
    /// alternatives.
    fn select_at_frontier(&self, mut alternatives: BTreeSet<ParsedTerm>) -> BTreeSet<ParsedTerm> {
        // Invariant: `alternatives` is a non-empty subset of the input, and every round that does
        // not return removes at least one alternative.
        loop {
            if alternatives.len() < 2 {
                return alternatives;
            }
            let keep = {
                let nodes = alternatives.iter().collect::<Vec<_>>();
                let mut frontier = Vec::new();
                collect_frontier(&nodes, &mut frontier);
                let classify = |predicate: &dyn Fn(&ParsedTerm) -> bool| {
                    (0..nodes.len())
                        .map(|index| frontier.iter().any(|position| predicate(position[index])))
                        .collect::<Vec<_>>()
                };
                let preferred = classify(&|node| self.is_preferred(node));
                if preferred.contains(&true) {
                    preferred
                } else {
                    let avoided = classify(&|node| self.is_avoided(node));
                    if !avoided.contains(&false) {
                        return alternatives;
                    }
                    avoided.into_iter().map(|avoided| !avoided).collect()
                }
            };
            if !keep.contains(&false) {
                return alternatives;
            }
            alternatives = alternatives
                .into_iter()
                .zip(keep)
                .filter_map(|(alternative, keep)| keep.then_some(alternative))
                .collect();
        }
    }

    fn remove_overloads(&self, alternatives: BTreeSet<ParsedTerm>) -> BTreeSet<ParsedTerm> {
        let alternatives = self.remove_bracket_overloads(alternatives);
        if alternatives.len() == 1 {
            return alternatives;
        }
        let Some(productions) = alternatives
            .iter()
            .map(|alternative| {
                let production = match alternative {
                    ParsedTerm::Production { production, .. }
                    | ParsedTerm::InstantiatedProduction { production, .. } => production,
                    ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => return None,
                };
                self.productions[*production].source_production
            })
            .collect::<Option<BTreeSet<_>>>()
        else {
            return alternatives;
        };
        let minimal = self.overloads.minimal(productions.iter());
        alternatives
            .into_iter()
            .filter(|alternative| {
                let production = match alternative {
                    ParsedTerm::Production { production, .. }
                    | ParsedTerm::InstantiatedProduction { production, .. } => production,
                    ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => {
                        unreachable!("non-production alternatives were returned above")
                    }
                };
                self.productions[*production]
                    .source_production
                    .is_some_and(|production| minimal.contains(&production))
            })
            .collect()
    }

    fn remove_bracket_overloads(&self, alternatives: BTreeSet<ParsedTerm>) -> BTreeSet<ParsedTerm> {
        let Some(productions) = alternatives
            .iter()
            .map(|alternative| match alternative {
                ParsedTerm::Production { production, .. }
                | ParsedTerm::InstantiatedProduction { production, .. }
                    if self.productions[*production].bracket =>
                {
                    Some(*production)
                }
                ParsedTerm::Production { .. }
                | ParsedTerm::InstantiatedProduction { .. }
                | ParsedTerm::Term(_)
                | ParsedTerm::Ambiguity(_) => None,
            })
            .collect::<Option<BTreeSet<_>>>()
        else {
            return alternatives;
        };
        let order = self
            .syntactic_subsort_relations
            .order()
            .expect("the grammar rejected syntactic subsort cycles during construction");
        let minimal = productions
            .iter()
            .filter(|candidate| {
                !productions.iter().any(|other| {
                    other != *candidate
                        && bracket_production_less_than(
                            &self.productions[*other],
                            &self.productions[**candidate],
                            order,
                        )
                })
            })
            .copied()
            .collect::<BTreeSet<_>>();
        alternatives
            .into_iter()
            .filter(|alternative| {
                let production = match alternative {
                    ParsedTerm::Production { production, .. }
                    | ParsedTerm::InstantiatedProduction { production, .. } => production,
                    ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => unreachable!(),
                };
                minimal.contains(production)
            })
            .collect()
    }

    fn is_preferred(&self, term: &ParsedTerm) -> bool {
        match term {
            ParsedTerm::Production { production, .. }
            | ParsedTerm::InstantiatedProduction { production, .. } => {
                self.productions[*production].prefer
            }
            // Token leaves retain the source production in their metadata. A token is an
            // application of its token production, so token-level prefer must participate in
            // the same ambiguity filtering as ordinary production nodes.
            ParsedTerm::Term(term) => term
                .metadata()
                .and_then(|metadata| metadata.production)
                .is_some_and(|source| {
                    self.productions.iter().any(|production| {
                        production
                            .source_production
                            .is_some_and(|candidate| candidate == source && production.prefer)
                    })
                }),
            ParsedTerm::Ambiguity(_) => false,
        }
    }

    fn is_avoided(&self, term: &ParsedTerm) -> bool {
        match term {
            ParsedTerm::Production { production, .. }
            | ParsedTerm::InstantiatedProduction { production, .. } => {
                self.productions[*production].avoid
            }
            ParsedTerm::Term(term) => term
                .metadata()
                .and_then(|metadata| metadata.production)
                .is_some_and(|source| {
                    self.productions.iter().any(|production| {
                        production
                            .source_production
                            .is_some_and(|candidate| candidate == source && production.avoid)
                    })
                }),
            ParsedTerm::Ambiguity(_) => false,
        }
    }

    /// Lift ambiguity in a top-level rewrite LHS above its `#RuleContent` wrapper.
    pub(super) fn push_top_lhs_packed_ambiguity_up(&self, term: Rc<PackedTerm>) -> Rc<PackedTerm> {
        let _span = measure::algorithm_span(Algorithm::ParserDisambiguationLiftTopLhs);
        self.push_top_lhs_packed_ambiguity_up_memo(term, &mut HashMap::new())
    }

    fn push_top_lhs_packed_ambiguity_up_memo(
        &self,
        term: Rc<PackedTerm>,
        expansion_memo: &mut HashMap<*const PackedTerm, (Rc<PackedTerm>, BTreeSet<Rc<PackedTerm>>)>,
    ) -> Rc<PackedTerm> {
        crate::stack::guarded(|| {
            // Invariant: every visited identity is memoized completely, and an ambiguity moves only
            // toward the rule-content root.
            if let PackedNode::Ambiguity(alternatives) = &term.node {
                let mut lifted = BTreeSet::new();
                for alternative in alternatives {
                    let alternative = self.push_top_lhs_packed_ambiguity_up_memo(
                        Rc::clone(alternative),
                        expansion_memo,
                    );
                    match &alternative.node {
                        PackedNode::Ambiguity(nested) => lifted.extend(nested.iter().cloned()),
                        _ => {
                            lifted.insert(alternative);
                        }
                    }
                }
                return PackedTerm::ambiguity(lifted);
            }
            let PackedNode::Production {
                production,
                children,
                metadata,
            } = &term.node
            else {
                return term;
            };
            if !self.productions[*production]
                .result
                .is_frontend(FrontendSort::RuleContent)
                || children.is_empty()
            {
                return term;
            }
            let bodies = self.expand_packed_rule_body_lhs(Rc::clone(&children[0]), expansion_memo);
            if bodies.len() == 1 {
                let body = bodies.into_iter().next().expect("length was one");
                if Rc::ptr_eq(&body, &children[0]) {
                    return term;
                }
                let mut rebuilt_children = children.clone();
                rebuilt_children[0] = body;
                return PackedTerm::production(*production, rebuilt_children, metadata.clone());
            }
            PackedTerm::ambiguity(
                bodies
                    .into_iter()
                    .map(|body| {
                        let mut alternative_children = children.clone();
                        alternative_children[0] = body;
                        PackedTerm::production(*production, alternative_children, metadata.clone())
                    })
                    .collect(),
            )
        })
    }

    fn expand_packed_rule_body_lhs(
        &self,
        body: Rc<PackedTerm>,
        memo: &mut HashMap<*const PackedTerm, (Rc<PackedTerm>, BTreeSet<Rc<PackedTerm>>)>,
    ) -> BTreeSet<Rc<PackedTerm>> {
        crate::stack::guarded(|| {
            // Invariant: every memoized identity has all rewrite-LHS alternatives expanded once while
            // shared descendants remain shared.
            let identity = Rc::as_ptr(&body);
            if let Some((_, expanded)) = memo.get(&identity) {
                return expanded.clone();
            }
            let expanded = match &body.node {
                PackedNode::Ambiguity(alternatives) => alternatives
                    .iter()
                    .flat_map(|alternative| {
                        self.expand_packed_rule_body_lhs(Rc::clone(alternative), memo)
                    })
                    .collect(),
                PackedNode::Production {
                    production,
                    children,
                    metadata,
                } => {
                    let label = self.productions[*production]
                        .label
                        .as_ref()
                        .map(|label| label.name.as_str());
                    if label == Some(InternalLabel::WithConfig.as_str()) && !children.is_empty() {
                        self.expand_packed_rule_body_lhs(Rc::clone(&children[0]), memo)
                            .into_iter()
                            .map(|child| {
                                let mut alternative_children = children.clone();
                                alternative_children[0] = child;
                                PackedTerm::production(
                                    *production,
                                    alternative_children,
                                    metadata.clone(),
                                )
                            })
                            .collect()
                    } else if label == Some(InternalLabel::KRewrite.as_str())
                        && children.len() == 2
                        && matches!(&children[0].node, PackedNode::Ambiguity(_))
                    {
                        let PackedNode::Ambiguity(alternatives) = &children[0].node else {
                            unreachable!()
                        };
                        alternatives
                            .iter()
                            .map(|left| {
                                PackedTerm::production(
                                    *production,
                                    vec![Rc::clone(left), Rc::clone(&children[1])],
                                    metadata.clone(),
                                )
                            })
                            .collect()
                    } else {
                        BTreeSet::from([Rc::clone(&body)])
                    }
                }
                PackedNode::Term(_) | PackedNode::InstantiatedProduction { .. } => {
                    BTreeSet::from([Rc::clone(&body)])
                }
            };
            memo.insert(identity, (body, expanded.clone()));
            expanded
        })
    }

    #[cfg(test)]
    pub(super) fn push_top_lhs_ambiguity_up(&self, term: ParsedTerm) -> ParsedTerm {
        crate::stack::guarded(|| {
            let (production, mut children, metadata) = match term.into_parts() {
                ParsedParts::Ambiguity(alternatives) => {
                    let lifted = alternatives
                        .into_iter()
                        .map(|alternative| self.push_top_lhs_ambiguity_up(alternative))
                        .flat_map(|alternative| match alternative.into_parts() {
                            ParsedParts::Ambiguity(nested) => nested,
                            alternative => BTreeSet::from([ParsedTerm::from(alternative)]),
                        })
                        .collect();
                    return ParsedTerm::Ambiguity(lifted);
                }
                ParsedParts::Production {
                    production,
                    children,
                    metadata,
                } => (production, children, metadata),
                term => return ParsedTerm::from(term),
            };
            if self.productions[production].result.name != "#RuleContent" || children.is_empty() {
                return ParsedTerm::Production {
                    production,
                    children,
                    metadata,
                };
            }
            let bodies = self.expand_rule_body_lhs(children.remove(0));
            if bodies.len() == 1 {
                children.insert(0, bodies.into_iter().next().expect("length was one"));
                return ParsedTerm::Production {
                    production,
                    children,
                    metadata,
                };
            }
            ParsedTerm::Ambiguity(
                bodies
                    .into_iter()
                    .map(|body| {
                        let mut alternative_children = children.clone();
                        alternative_children.insert(0, body);
                        ParsedTerm::Production {
                            production,
                            children: alternative_children,
                            metadata: metadata.clone(),
                        }
                    })
                    .collect(),
            )
        })
    }

    #[cfg(test)]
    fn expand_rule_body_lhs(&self, body: ParsedTerm) -> BTreeSet<ParsedTerm> {
        crate::stack::guarded(|| {
            let (production, mut children, metadata) = match body.into_parts() {
                ParsedParts::Ambiguity(alternatives) => {
                    return alternatives
                        .into_iter()
                        .flat_map(|alternative| self.expand_rule_body_lhs(alternative))
                        .collect();
                }
                ParsedParts::Production {
                    production,
                    children,
                    metadata,
                } => (production, children, metadata),
                body => return BTreeSet::from([ParsedTerm::from(body)]),
            };
            let label = self.productions[production]
                .label
                .as_ref()
                .map(|label| label.name.as_str());
            if label == Some("#withConfig") && !children.is_empty() {
                let expanded = self.expand_rule_body_lhs(children.remove(0));
                return expanded
                    .into_iter()
                    .map(|child| {
                        let mut alternative_children = children.clone();
                        alternative_children.insert(0, child);
                        ParsedTerm::Production {
                            production,
                            children: alternative_children,
                            metadata: metadata.clone(),
                        }
                    })
                    .collect();
            }
            if label != Some("#KRewrite") || children.len() != 2 {
                return BTreeSet::from([ParsedTerm::Production {
                    production,
                    children,
                    metadata,
                }]);
            }
            let left = children.remove(0);
            let right = children.remove(0);
            match left.into_parts() {
                ParsedParts::Ambiguity(alternatives) => alternatives
                    .into_iter()
                    .map(|left| ParsedTerm::Production {
                        production,
                        children: vec![left, right.clone()],
                        metadata: metadata.clone(),
                    })
                    .collect(),
                left => BTreeSet::from([ParsedTerm::Production {
                    production,
                    children: vec![ParsedTerm::from(left), right],
                    metadata,
                }]),
            }
        })
    }

    #[cfg(test)]
    pub(super) fn ambiguity_count(term: &ParsedTerm) -> usize {
        crate::stack::guarded(|| match term {
            ParsedTerm::Term(_) => 1,
            ParsedTerm::Production { children, .. } => {
                children.iter().fold(1usize, |count, child| {
                    count.saturating_mul(Self::ambiguity_count(child))
                })
            }
            ParsedTerm::InstantiatedProduction { children, .. } => {
                children.iter().fold(1usize, |count, child| {
                    count.saturating_mul(Self::ambiguity_count(child))
                })
            }
            ParsedTerm::Ambiguity(alternatives) => {
                alternatives.iter().fold(0usize, |count, item| {
                    count.saturating_add(Self::ambiguity_count(item))
                })
            }
        })
    }
}

/// The readings of one node of an inferred tree (`Grammar::resolve_ambiguities_node`): the set
/// of terms it lowers to, compared without their metadata.
#[derive(Clone)]
enum Readings {
    One(Term),
    /// At least two distinct terms.
    Listed(Vec<Term>),
    /// A node of `ProductNode`s by index: the lowering of every combination of its children's
    /// readings, all distinct.
    Product(usize),
}

/// A production node with a child of several readings, whose lowering tells distinct children
/// apart (`lowering_keeps_children`).
struct ProductNode {
    production: usize,
    parameters: Option<Vec<Sort>>,
    metadata: crate::kast::TermMetadata,
    children: Vec<Readings>,
}

/// Distinct terms in the order they were met, each as first met.
#[derive(Default)]
struct DistinctReadings {
    terms: Vec<Term>,
    seen: BTreeSet<Term>,
}

impl DistinctReadings {
    fn insert(&mut self, term: Term) {
        if !self.seen.contains(&term) {
            self.seen.insert(term.clone());
            self.terms.push(term);
        }
    }

    fn into_readings(mut self) -> Readings {
        if self.terms.len() == 1 {
            Readings::One(self.terms.pop().expect("one term"))
        } else {
            Readings::Listed(self.terms)
        }
    }
}

/// Whether `lower_term` gives distinct terms for distinct vectors of `arity` children of
/// `production`. It does unless it drops a child (a bracket over several), joins the children
/// into one value (a `#KToken` of a string and a sort) or splices them (a `~>` sequence, which
/// flattens a child that is itself a sequence).
fn lowering_keeps_children(production: &Production, arity: usize) -> bool {
    if production.transparent {
        return arity == 1;
    }
    !production
        .label
        .as_ref()
        .is_some_and(|label| label.is(InternalLabel::KToken) || label.is(InternalLabel::KSequence))
}

/// The head of a lowered term that has children, and its children: two terms with the same
/// head and as many children differ only in their children.
#[derive(PartialEq)]
enum TermHead<'a> {
    Rewrite,
    As,
    Sequence,
    Apply(&'a crate::kast::Label),
}

fn term_children(term: &Term) -> Option<(TermHead<'_>, Vec<&Term>)> {
    match term.unannotated() {
        Term::Rewrite { left, right } => Some((TermHead::Rewrite, vec![&**left, &**right])),
        Term::As { pattern, alias } => Some((TermHead::As, vec![&**pattern, &**alias])),
        Term::Sequence(items) => Some((TermHead::Sequence, items.iter().collect())),
        Term::Apply { label, arguments } => {
            Some((TermHead::Apply(label), arguments.iter().collect()))
        }
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => None,
        Term::Annotated { .. } => unreachable!("an unannotated term"),
    }
}

/// When `terms` all have one head and arity: the child positions at which they differ, and
/// every term's children by position.
fn differing_children<'a>(terms: &[&'a Term]) -> Option<(Vec<usize>, Vec<Vec<&'a Term>>)> {
    let (first, _) = terms.split_first()?;
    let (head, arity) = term_children(first).map(|(head, children)| (head, children.len()))?;
    let mut by_position = vec![Vec::with_capacity(terms.len()); arity];
    for term in terms {
        let (other_head, children) = term_children(term)?;
        if other_head != head || children.len() != arity {
            return None;
        }
        for (position, child) in children.into_iter().enumerate() {
            by_position[position].push(child);
        }
    }
    let positions = (0..arity)
        .filter(|position| {
            let (first, rest) = by_position[*position]
                .split_first()
                .expect("a position of every term");
            rest.iter().any(|child| child != first)
        })
        .collect();
    Some((positions, by_position))
}

/// The span the spanned `terms` cover together.
fn covered_span(terms: &[&Term]) -> Option<TermSpan> {
    terms
        .iter()
        .filter_map(|term| term.metadata().and_then(|metadata| metadata.span))
        .reduce(|covered, span| TermSpan {
            source: covered.source,
            start: covered.start.min(span.start),
            end: covered.end.max(span.end),
        })
}

/// Several readings, narrowed to the smallest subterm outside which they agree
/// (`Grammar::factor_readings`).
enum FactoredReadings {
    /// The subterm's readings, listed.
    Place(AmbiguityPlace),
    /// The subterm's readings are every combination of those of the places, which lie in it.
    Independent {
        span: Option<TermSpan>,
        places: Vec<AmbiguityPlace>,
    },
}

impl FactoredReadings {
    fn into_places(self) -> Vec<AmbiguityPlace> {
        match self {
            Self::Place(place) => vec![place],
            Self::Independent { places, .. } => places,
        }
    }
}

fn bracket_production_less_than(
    lesser: &Production,
    greater: &Production,
    sorts: &crate::definition::PartialOrder<crate::kast::Sort>,
) -> bool {
    if lesser.items.len() != greater.items.len()
        || !sorts.less_than_eq(&lesser.result, &greater.result)
    {
        return false;
    }
    let mut strict = lesser.result != greater.result;
    for (lesser, greater) in lesser.items.iter().zip(&greater.items) {
        match (lesser, greater) {
            (Item::NonTerminal(lesser), Item::NonTerminal(greater))
                if sorts.less_than_eq(lesser, greater) =>
            {
                strict |= lesser != greater;
            }
            (Item::Terminal(lesser), Item::Terminal(greater)) if lesser == greater => {}
            (
                Item::Regex { source: lesser, .. },
                Item::Regex {
                    source: greater, ..
                },
            ) if lesser == greater => {}
            _ => return false,
        }
    }
    strict
}

fn production_arity(production: &Production) -> usize {
    production
        .items
        .iter()
        .filter(|item| matches!(item, Item::NonTerminal(_)))
        .count()
}

#[cfg(test)]
fn klabel_name(term: &ParsedTerm) -> Option<String> {
    let Term::Token { token, sort } = term.leaf()? else {
        return None;
    };
    if sort.name != "KLabel" {
        return None;
    }
    if token.starts_with('`') {
        string::unquote_label(token).ok()
    } else {
        Some(token.clone())
    }
}

fn packed_klabel_name(term: &PackedTerm) -> Option<String> {
    let PackedNode::Term(term) = &term.node else {
        return None;
    };
    let Term::Token { token, sort } = term.unannotated() else {
        return None;
    };
    if !sort.is_frontend(FrontendSort::KLabel) {
        return None;
    }
    if token.starts_with('`') {
        string::unquote_label(token).ok()
    } else {
        Some(token.clone())
    }
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
enum Side {
    Left,
    Right,
    Middle,
}

pub(crate) fn parse_apply_priority(source: &str) -> Result<BTreeSet<usize>, ParseError> {
    source
        .split(|character: char| character == ',' || character.is_ascii_whitespace())
        .filter(|piece| !piece.is_empty())
        .map(|piece| {
            piece
                .parse::<usize>()
                .map_err(|_| ParseError::InvalidApplyPriority {
                    value: source.to_owned(),
                    position: piece.to_owned(),
                })
        })
        .collect()
}

/// Push onto `frontier`, for each frontier position below `nodes` (the nodes the alternatives have
/// at one common-prefix position, in alternative order), the node every alternative has there.
///
/// A position is in the common prefix when its node headers are equal: the same production with
/// the same instantiated parameters and arity, or equal leaves (a leaf or ambiguity is compared
/// whole, so equal ones have nothing below them). Otherwise the position is a frontier position.
fn collect_frontier<'a>(nodes: &[&'a ParsedTerm], frontier: &mut Vec<Vec<&'a ParsedTerm>>) {
    crate::stack::guarded(|| {
        // Invariant: `nodes` holds one node per alternative at one common-prefix position, so every
        // pushed position has one node per alternative, in alternative order; recursion descends
        // only through shared headers, whose arity is equal.
        let (first, rest) = nodes.split_first().expect("an ambiguity has alternatives");
        let children = |node: &'a ParsedTerm| match node {
            ParsedTerm::Production { children, .. }
            | ParsedTerm::InstantiatedProduction { children, .. } => children.as_slice(),
            ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => &[],
        };
        let shared_header = rest.iter().all(|node| match (*first, *node) {
            (
                ParsedTerm::Production {
                    production,
                    children,
                    ..
                },
                ParsedTerm::Production {
                    production: other,
                    children: other_children,
                    ..
                },
            ) => production == other && children.len() == other_children.len(),
            (
                ParsedTerm::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                    ..
                },
                ParsedTerm::InstantiatedProduction {
                    production: other,
                    parameters: other_parameters,
                    children: other_children,
                    ..
                },
            ) => {
                production == other
                    && parameters == other_parameters
                    && children.len() == other_children.len()
            }
            (ParsedTerm::Term(_), ParsedTerm::Term(_))
            | (ParsedTerm::Ambiguity(_), ParsedTerm::Ambiguity(_)) => first == node,
            _ => false,
        });
        if !shared_header {
            frontier.push(nodes.to_vec());
            return;
        }
        for index in 0..children(first).len() {
            let below = nodes
                .iter()
                .map(|node| &children(node)[index])
                .collect::<Vec<_>>();
            collect_frontier(&below, frontier);
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::{PartialOrder, ProductionItem, Sentence};
    use crate::kast::{Label, ProductionIdentity, Sort};
    use crate::provenance::SourceId;
    use k_rust_kore::measure::{Counter, snapshot};
    use proptest::prelude::*;
    use std::collections::BTreeMap;

    fn identity(value: usize) -> ProductionIdentity {
        ProductionIdentity::from_hex(&format!("{value:032x}")).unwrap()
    }

    fn nonterminal(sort: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(sort),
            name: None,
        }
    }

    fn add_production(
        grammar: &mut Grammar,
        result: &str,
        arguments: &[&str],
        label: &str,
    ) -> usize {
        let index = grammar.productions.len();
        grammar
            .add(
                Sort::new(result),
                arguments.iter().map(|sort| nonterminal(sort)).collect(),
                Some(Label::new(label)),
                false,
                false,
            )
            .unwrap();
        index
    }

    fn variable(name: &str) -> ParsedTerm {
        ParsedTerm::Term(Term::variable(name))
    }

    fn terminal_production(result: &str, terminal: &str, label: &str) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(label)),
            parameters: Vec::new(),
            sort: Sort::new(result),
            items: vec![ProductionItem::Terminal(terminal.into())],
            attributes: Default::default(),
        }
    }

    fn subsort(result: &str, child: &str) -> Sentence {
        Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new(result),
            items: vec![nonterminal(child)],
            attributes: Default::default(),
        }
    }

    fn render(grammar: &Grammar, term: &ParsedTerm) -> String {
        match term {
            ParsedTerm::Term(term) => term.to_string(),
            ParsedTerm::Production {
                production,
                children,
                ..
            } => {
                let label = grammar.productions[*production]
                    .label
                    .as_ref()
                    .map_or("<unlabeled>", |label| label.name.as_str());
                format!(
                    "{label}({})",
                    children
                        .iter()
                        .map(|child| render(grammar, child))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
                ..
            } => {
                let label = grammar.productions[*production]
                    .label
                    .as_ref()
                    .map_or("<unlabeled>", |label| label.name.as_str());
                format!(
                    "{label}{{{}}}({})",
                    parameters
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", "),
                    children
                        .iter()
                        .map(|child| render(grammar, child))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            ParsedTerm::Ambiguity(alternatives) => format!(
                "amb{{{}}}",
                alternatives
                    .iter()
                    .map(|alternative| render(grammar, alternative))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }

    fn priority_fixture() -> (Grammar, [usize; 2], Rc<PackedTerm>) {
        let mut grammar = Grammar::default();
        let low = add_production(&mut grammar, "Exp", &[], "low");
        let high = add_production(&mut grammar, "Exp", &[], "high");
        let left = add_production(&mut grammar, "Exp", &["Exp"], "left");
        let right = add_production(&mut grammar, "Exp", &["Exp"], "right");
        grammar.priorities = PartialOrder::new([
            ("left".to_owned(), "low".to_owned()),
            ("right".to_owned(), "high".to_owned()),
        ])
        .unwrap();
        let shared = PackedTerm::ambiguity(BTreeSet::from([
            PackedTerm::production(low, vec![], Default::default()),
            PackedTerm::production(high, vec![], Default::default()),
        ]));
        (grammar, [left, right], shared)
    }

    fn wrapped(parent: usize, child: &Rc<PackedTerm>) -> Rc<PackedTerm> {
        PackedTerm::production(parent, vec![Rc::clone(child)], Default::default())
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]

        #[test]
        fn priority_child_memo_key_is_complete(
            target_parent in 0usize..2,
            target_side in 0usize..3,
            prefill in prop::collection::vec((0usize..2, 0usize..3), 0..12),
        ) {
            let (grammar, parents, shared) = priority_fixture();
            let sides = [None, Some(Side::Left), Some(Side::Right)];
            let mut shared_memos = PackedPriorityMemos::default();
            for (parent, side) in prefill {
                let _ = grammar.filter_packed_priority_child(
                    parents[parent],
                    Rc::clone(&shared),
                    sides[side],
                    &mut shared_memos.nodes,
                    &mut shared_memos.children,
                );
            }
            let actual = grammar.filter_packed_priority_child(
                parents[target_parent],
                Rc::clone(&shared),
                sides[target_side],
                &mut shared_memos.nodes,
                &mut shared_memos.children,
            );
            let mut fresh = PackedPriorityMemos::default();
            let expected = grammar.filter_packed_priority_child(
                parents[target_parent],
                shared,
                sides[target_side],
                &mut fresh.nodes,
                &mut fresh.children,
            );
            prop_assert_eq!(actual, expected);
        }

        #[test]
        fn shared_priority_memos_match_fresh_results(
            parents_to_filter in prop::collection::vec(0usize..2, 1..24),
        ) {
            let (grammar, parents, shared) = priority_fixture();
            let memos = RefCell::new(PackedPriorityMemos::default());
            for parent in parents_to_filter {
                let root = wrapped(parents[parent], &shared);
                let actual = grammar.filter_or_defer_packed_priority(Rc::clone(&root), &memos);
                let expected = grammar.filter_or_defer_packed_priority_fresh(root);
                prop_assert_eq!(actual, expected);
            }
        }

        #[test]
        fn sharing_never_increases_priority_computations(repetitions in 1usize..24) {
            let (grammar, parents, shared) = priority_fixture();
            let root = wrapped(parents[0], &shared);
            let before = snapshot();
            let memos = RefCell::new(PackedPriorityMemos::default());
            for _ in 0..repetitions {
                grammar
                    .filter_or_defer_packed_priority(Rc::clone(&root), &memos)
                    .unwrap();
            }
            let shared_work = snapshot().delta(&before).get(Counter::ParserPackedPriorityComputations);
            let before = snapshot();
            for _ in 0..repetitions {
                grammar
                    .filter_or_defer_packed_priority_fresh(Rc::clone(&root))
                    .unwrap();
            }
            let fresh_work = snapshot().delta(&before).get(Counter::ParserPackedPriorityComputations);
            prop_assert!(shared_work <= fresh_work);
            prop_assert!(shared_work <= 4);
        }
    }

    #[test]
    fn factors_a_shared_production_into_the_differing_child() {
        let mut grammar = Grammar::default();
        let pair = add_production(&mut grammar, "Exp", &["Exp", "Exp"], "pair");
        let alternatives = BTreeSet::from([
            ParsedTerm::Production {
                production: pair,
                children: vec![variable("A"), variable("C")],
                metadata: Default::default(),
            },
            ParsedTerm::Production {
                production: pair,
                children: vec![variable("B"), variable("C")],
                metadata: Default::default(),
            },
        ]);

        let factored = grammar.factor_ambiguities(ParsedTerm::Ambiguity(alternatives));
        let ParsedParts::Production { children, .. } = factored.into_parts() else {
            panic!("expected the shared production to be factored")
        };
        assert!(matches!(children[0], ParsedTerm::Ambiguity(ref items) if items.len() == 2));
        assert_eq!(children[1], variable("C"));
    }

    #[test]
    fn flattens_nested_ambiguities_while_factoring() {
        let grammar = Grammar::default();
        let nested = ParsedTerm::Ambiguity(BTreeSet::from([
            variable("A"),
            ParsedTerm::Ambiguity(BTreeSet::from([variable("B"), variable("C")])),
        ]));

        let factored = grammar.factor_ambiguities(nested);

        assert!(matches!(factored, ParsedTerm::Ambiguity(ref items) if items.len() == 3));
        assert_eq!(render(&grammar, &factored), "amb{A, B, C}");
    }

    #[test]
    fn lifts_top_level_rewrite_lhs_ambiguity_above_rule_content() {
        let mut grammar = Grammar::default();
        let rewrite = add_production(&mut grammar, "#RuleExp", &["Exp", "Exp"], "#KRewrite");
        let rule = add_production(
            &mut grammar,
            "#RuleContent",
            &["#RuleExp"],
            "#ruleNoConditions",
        );
        let root = ParsedTerm::Production {
            production: rule,
            children: vec![ParsedTerm::Production {
                production: rewrite,
                children: vec![
                    ParsedTerm::Ambiguity(BTreeSet::from([variable("A"), variable("B")])),
                    variable("C"),
                ],
                metadata: Default::default(),
            }],
            metadata: Default::default(),
        };

        let lifted = grammar.push_top_lhs_ambiguity_up(root);
        assert!(matches!(lifted, ParsedTerm::Ambiguity(ref items) if items.len() == 2));
    }

    #[test]
    fn lifts_a_direct_packed_rule_content_child_ambiguity() {
        let mut grammar = Grammar::default();
        let rewrite = add_production(&mut grammar, "#RuleExp", &["Exp", "Exp"], "#KRewrite");
        let rule = add_production(
            &mut grammar,
            "#RuleContent",
            &["#RuleExp"],
            "#ruleNoConditions",
        );
        let rewrite = |left: &str| {
            PackedTerm::production(
                rewrite,
                vec![
                    PackedTerm::leaf(Term::variable(left)),
                    PackedTerm::leaf(Term::variable("C")),
                ],
                Default::default(),
            )
        };
        let body = PackedTerm::ambiguity(BTreeSet::from([rewrite("A"), rewrite("B")]));
        let root = PackedTerm::production(rule, vec![body], Default::default());

        let lifted = grammar.push_top_lhs_packed_ambiguity_up(root);
        let PackedNode::Ambiguity(alternatives) = &lifted.node else {
            panic!("expected the child ambiguity above #RuleContent")
        };
        assert_eq!(alternatives.len(), 2);
        assert!(alternatives.iter().all(|alternative| {
            matches!(
                &alternative.node,
                PackedNode::Production { production, .. } if *production == rule
            )
        }));
    }

    /// A grammar of `wrapper(Exp)`, `pair(Exp, Exp)` and constants `a` to `d` and `outer`, and
    /// a builder of its production nodes over `start..start + 1`.
    fn readings_fixture() -> (Grammar, impl Fn(&str, Vec<ParsedTerm>, usize) -> ParsedTerm) {
        let mut grammar = Grammar::default();
        let mut productions = BTreeMap::new();
        productions.insert(
            "wrapper",
            add_production(&mut grammar, "Exp", &["Exp"], "wrapper"),
        );
        productions.insert(
            "pair",
            add_production(&mut grammar, "Exp", &["Exp", "Exp"], "pair"),
        );
        for name in ["a", "b", "c", "d", "outer"] {
            productions.insert(name, add_production(&mut grammar, "Exp", &[], name));
        }
        let node = move |name: &str, children, start| ParsedTerm::Production {
            production: productions[name],
            children,
            metadata: crate::kast::TermMetadata {
                span: Some(TermSpan {
                    source: SourceId(0),
                    start,
                    end: start + 1,
                }),
                ..Default::default()
            },
        };
        (grammar, node)
    }

    fn ambiguity(alternatives: impl IntoIterator<Item = ParsedTerm>) -> ParsedTerm {
        ParsedTerm::Ambiguity(alternatives.into_iter().collect())
    }

    fn rendered(alternatives: &[AmbiguousParse]) -> Vec<&str> {
        alternatives
            .iter()
            .map(|alternative| alternative.term.as_str())
            .collect()
    }

    #[test]
    fn reports_the_smallest_subterm_outside_which_every_reading_agrees() {
        let (grammar, node) = readings_fixture();
        // `wrapper(a)`, `wrapper(b)` and `outer` differ at the root, so the report is the root
        // with all three readings, not the inner ambiguity between `a` and `b`.
        let root = ambiguity([
            node(
                "wrapper",
                vec![ambiguity([node("a", vec![], 10), node("b", vec![], 10)])],
                0,
            ),
            node("outer", vec![], 0),
        ]);
        let ParseError::Ambiguous {
            parses,
            alternatives,
            span,
            places,
        } = grammar.resolve_ambiguities(root).unwrap_err()
        else {
            panic!("expected an ambiguity")
        };
        assert_eq!(parses, 3);
        assert_eq!(span.map(|span| span.start), Some(0));
        assert_eq!(
            rendered(&alternatives),
            ["outer(.KList)", "wrapper(a(.KList))", "wrapper(b(.KList))"]
        );
        assert!(places.is_empty());
    }

    #[test]
    fn two_packings_of_one_set_of_readings_report_alike() {
        let (grammar, node) = readings_fixture();
        let leaf = |name| node(name, vec![], 10);
        let packed = node("wrapper", vec![ambiguity([leaf("a"), leaf("b")])], 0);
        let flat = ambiguity([
            node("wrapper", vec![leaf("a")], 0),
            node("wrapper", vec![leaf("b")], 0),
        ]);
        let report = grammar.resolve_ambiguities(packed).unwrap_err();
        assert_eq!(grammar.resolve_ambiguities(flat).unwrap_err(), report);
        let ParseError::Ambiguous {
            parses,
            alternatives,
            span,
            ..
        } = report
        else {
            panic!("expected an ambiguity")
        };
        assert_eq!(parses, 2);
        assert_eq!(span.map(|span| span.start), Some(10));
        assert_eq!(rendered(&alternatives), ["a(.KList)", "b(.KList)"]);

        // Two independent choices, packed below `pair` or listed as four readings.
        let left = |name| node(name, vec![], 10);
        let right = |name| node(name, vec![], 20);
        let packed = node(
            "pair",
            vec![
                ambiguity([left("a"), left("b")]),
                ambiguity([right("c"), right("d")]),
            ],
            0,
        );
        let flat = ambiguity(
            [("a", "c"), ("a", "d"), ("b", "c"), ("b", "d")]
                .map(|(first, second)| node("pair", vec![left(first), right(second)], 0)),
        );
        let report = grammar.resolve_ambiguities(packed).unwrap_err();
        assert_eq!(grammar.resolve_ambiguities(flat).unwrap_err(), report);
        let ParseError::Ambiguous {
            parses,
            alternatives,
            span,
            places,
        } = &report
        else {
            panic!("expected an ambiguity")
        };
        assert_eq!(*parses, 4);
        assert_eq!(span.map(|span| span.start), Some(0));
        assert!(alternatives.is_empty());
        assert_eq!(
            places
                .iter()
                .map(|place| (
                    place.span.map(|span| span.start),
                    rendered(&place.alternatives)
                ))
                .collect::<Vec<_>>(),
            [
                (Some(10), vec!["a(.KList)", "b(.KList)"]),
                (Some(20), vec!["c(.KList)", "d(.KList)"]),
            ]
        );
        assert!(
            report.to_string().starts_with(
                "Parsing ambiguity: 4 readings, which differ independently in 2 subterms."
            ),
            "{report}"
        );
    }

    #[test]
    fn readings_that_differ_together_at_two_places_are_listed_at_their_common_subterm() {
        let (grammar, node) = readings_fixture();
        let left = |name| node(name, vec![], 10);
        let right = |name| node(name, vec![], 20);
        let root = ambiguity([
            node("pair", vec![left("a"), right("c")], 0),
            node("pair", vec![left("b"), right("d")], 0),
        ]);
        let ParseError::Ambiguous {
            parses,
            alternatives,
            span,
            places,
        } = grammar.resolve_ambiguities(root).unwrap_err()
        else {
            panic!("expected an ambiguity")
        };
        assert_eq!(parses, 2);
        assert_eq!(span.map(|span| span.start), Some(0));
        assert_eq!(
            rendered(&alternatives),
            ["pair(a(.KList),c(.KList))", "pair(b(.KList),d(.KList))"]
        );
        assert!(places.is_empty());
    }

    #[test]
    fn alternatives_that_lower_alike_are_one_reading() {
        let (grammar, node) = readings_fixture();
        // Two trees of one term (as two derivations through different unlabelled
        // productions would be) are one reading, and the ambiguity resolves to it.
        let root = node(
            "wrapper",
            vec![ambiguity([node("a", vec![], 10), node("a", vec![], 11)])],
            0,
        );
        assert_eq!(
            grammar.resolve_ambiguities(root).unwrap().to_string(),
            "wrapper(a(.KList))"
        );
    }

    #[test]
    fn applies_prefer_and_avoid_only_at_ambiguity_roots() {
        let mut grammar = Grammar::default();
        let preferred = add_production(&mut grammar, "Exp", &[], "preferred");
        let ordinary = add_production(&mut grammar, "Exp", &[], "ordinary");
        let avoided = add_production(&mut grammar, "Exp", &[], "avoided");
        let also_avoided = add_production(&mut grammar, "Exp", &[], "alsoAvoided");
        grammar.productions[preferred].prefer = true;
        grammar.productions[avoided].avoid = true;
        grammar.productions[also_avoided].avoid = true;

        let alternative = |production| ParsedTerm::Production {
            production,
            children: Vec::new(),
            metadata: Default::default(),
        };
        let selected =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                alternative(preferred),
                alternative(ordinary),
                alternative(avoided),
            ])));
        assert_eq!(selected, alternative(preferred));

        let without_prefer =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                alternative(ordinary),
                alternative(avoided),
            ])));
        assert_eq!(without_prefer, alternative(ordinary));

        let all_avoided =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                alternative(avoided),
                alternative(also_avoided),
            ])));
        assert!(matches!(all_avoided, ParsedTerm::Ambiguity(ref items) if items.len() == 2));

        let wrapper = add_production(&mut grammar, "Exp", &["Exp"], "wrapper");
        let nested =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                ParsedTerm::Production {
                    production: wrapper,
                    children: vec![alternative(preferred)],
                    metadata: Default::default(),
                },
                ParsedTerm::Production {
                    production: wrapper,
                    children: vec![alternative(ordinary)],
                    metadata: Default::default(),
                },
            ])));
        assert_eq!(
            nested,
            ParsedTerm::Production {
                production: wrapper,
                children: vec![alternative(preferred)],
                metadata: Default::default(),
            }
        );

        assert_eq!(render(&grammar, &selected), "preferred()");
        assert_eq!(render(&grammar, &without_prefer), "ordinary()");
        assert_eq!(
            render(&grammar, &all_avoided),
            "amb{avoided(), alsoAvoided()}"
        );
        assert_eq!(render(&grammar, &nested), "wrapper(preferred())");
    }

    /// A grammar for the frontier-step tests: `pair` has two children so that alternatives can
    /// share it and diverge below it at two positions.
    struct FrontierGrammar {
        grammar: Grammar,
        pair: usize,
        wrap: usize,
        preferred: usize,
        avoided: usize,
        also_avoided: usize,
    }

    impl FrontierGrammar {
        fn new() -> Self {
            let mut grammar = Grammar::default();
            let pair = add_production(&mut grammar, "Exp", &["Exp", "Exp"], "pair");
            let wrap = add_production(&mut grammar, "Exp", &["Exp"], "wrap");
            let preferred = add_production(&mut grammar, "Exp", &[], "preferred");
            let avoided = add_production(&mut grammar, "Exp", &[], "avoided");
            let also_avoided = add_production(&mut grammar, "Exp", &[], "alsoAvoided");
            grammar.productions[preferred].prefer = true;
            grammar.productions[avoided].avoid = true;
            grammar.productions[also_avoided].avoid = true;
            Self {
                grammar,
                pair,
                wrap,
                preferred,
                avoided,
                also_avoided,
            }
        }

        fn node(&self, production: usize, children: Vec<ParsedTerm>) -> ParsedTerm {
            ParsedTerm::Production {
                production,
                children,
                metadata: Default::default(),
            }
        }

        fn pair(&self, left: ParsedTerm, right: ParsedTerm) -> ParsedTerm {
            self.node(self.pair, vec![left, right])
        }

        fn leaf(&self, production: usize) -> ParsedTerm {
            self.node(production, Vec::new())
        }

        fn filter(&self, alternatives: impl IntoIterator<Item = ParsedTerm>) -> String {
            render(
                &self.grammar,
                &self
                    .grammar
                    .filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(
                        alternatives.into_iter().collect(),
                    )),
            )
        }
    }

    #[test]
    fn frontier_step_classifies_alternatives_that_diverge_at_two_positions() {
        let f = FrontierGrammar::new();
        // The alternatives share `pair` and differ in both children, so factoring cannot move
        // the ambiguity and the top-production step sees only `pair`.
        assert_eq!(
            f.filter([
                f.pair(f.leaf(f.avoided), variable("X")),
                f.pair(variable("V"), variable("Y")),
            ]),
            "pair(V, Y)"
        );
        assert_eq!(
            f.filter([
                f.pair(variable("X"), f.leaf(f.avoided)),
                f.pair(variable("V"), variable("Y")),
            ]),
            "pair(V, Y)"
        );
        assert_eq!(
            f.filter([
                f.pair(f.leaf(f.preferred), variable("X")),
                f.pair(variable("V"), variable("Y")),
            ]),
            "pair(preferred(), X)"
        );
        // An `avoid` production below a frontier node is not classified, as below a top
        // production.
        assert_eq!(
            f.filter([
                f.pair(f.node(f.wrap, vec![f.leaf(f.avoided)]), variable("X")),
                f.pair(variable("V"), variable("Y")),
            ]),
            "amb{pair(wrap(avoided()), X), pair(V, Y)}"
        );
    }

    #[test]
    fn frontier_step_prefers_before_it_avoids() {
        let f = FrontierGrammar::new();
        // The first alternative is both preferred and avoided at the frontier; `prefer` decides.
        assert_eq!(
            f.filter([
                f.pair(f.leaf(f.preferred), f.leaf(f.avoided)),
                f.pair(variable("V"), variable("Y")),
            ]),
            "pair(preferred(), avoided())"
        );
    }

    #[test]
    fn frontier_step_keeps_every_alternative_when_all_are_avoided() {
        let f = FrontierGrammar::new();
        assert_eq!(
            f.filter([
                f.pair(f.leaf(f.avoided), variable("X")),
                f.pair(variable("V"), f.leaf(f.also_avoided)),
            ]),
            "amb{pair(avoided(), X), pair(V, alsoAvoided())}"
        );
    }

    #[test]
    fn frontier_step_repeats_over_the_survivors_until_nothing_changes() {
        let f = FrontierGrammar::new();
        let first = f.pair(f.leaf(f.avoided), variable("X"));
        let second = f.pair(variable("V"), f.pair(f.leaf(f.avoided), variable("Y")));
        let third = f.pair(variable("V"), f.pair(variable("W"), variable("Z")));
        // Round 1: the frontier is both children of the root; only `first` is avoided there.
        // Round 2: `second` and `third` share the prefix `pair(V, pair(_, _))`, and the new
        // frontier below it shows `second`'s avoided node.
        let selected = f.grammar.select_at_frontier(BTreeSet::from([
            first.clone(),
            second.clone(),
            third.clone(),
        ]));
        assert_eq!(selected, BTreeSet::from([third.clone()]));
        assert_eq!(f.filter([first, second, third]), "pair(V, pair(W, Z))");
    }

    #[test]
    fn frontier_step_counts_an_ambiguity_node_as_neither_preferred_nor_avoided() {
        let f = FrontierGrammar::new();
        let nested =
            ParsedTerm::Ambiguity(BTreeSet::from([f.leaf(f.avoided), f.leaf(f.also_avoided)]));
        let with_ambiguity = f.pair(nested, variable("X"));
        let avoided = f.pair(f.leaf(f.avoided), variable("Y"));
        assert_eq!(
            f.grammar
                .select_at_frontier(BTreeSet::from([with_ambiguity.clone(), avoided.clone()])),
            BTreeSet::from([with_ambiguity.clone()])
        );
        assert_eq!(
            f.filter([with_ambiguity, avoided]),
            "pair(amb{avoided(), alsoAvoided()}, X)"
        );
        let nested = ParsedTerm::Ambiguity(BTreeSet::from([
            f.leaf(f.preferred),
            f.leaf(f.also_avoided),
        ]));
        assert_eq!(
            f.grammar.select_at_frontier(BTreeSet::from([
                f.pair(nested, variable("X")),
                f.pair(variable("V"), variable("Y")),
            ])),
            BTreeSet::from([
                f.pair(
                    ParsedTerm::Ambiguity(BTreeSet::from([
                        f.leaf(f.preferred),
                        f.leaf(f.also_avoided),
                    ])),
                    variable("X"),
                ),
                f.pair(variable("V"), variable("Y")),
            ])
        );
    }

    #[test]
    fn applies_prefer_and_avoid_to_token_production_metadata() {
        let mut grammar = Grammar::default();
        let preferred = grammar.productions.len();
        grammar
            .add(
                Sort::new("TokenA"),
                vec![ProductionItem::Terminal("x".into())],
                Some(Label::new("tokenA")),
                false,
                false,
            )
            .unwrap();
        let ordinary = grammar.productions.len();
        grammar
            .add(
                Sort::new("TokenB"),
                vec![ProductionItem::Terminal("x".into())],
                Some(Label::new("tokenB")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[preferred].source_production = Some(identity(10));
        grammar.productions[preferred].prefer = true;
        grammar.productions[ordinary].source_production = Some(identity(11));

        let token = |source, sort| {
            ParsedTerm::Term(
                Term::Token {
                    token: "x".into(),
                    sort: Sort::new(sort),
                }
                .with_metadata(crate::kast::TermMetadata {
                    production: Some(identity(source)),
                    ..Default::default()
                }),
            )
        };
        let selected =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                token(10, "TokenA"),
                token(11, "TokenB"),
            ])));
        assert_eq!(selected, token(10, "TokenA"));
    }

    #[test]
    fn removes_overloads_before_applying_prefer_and_avoid() {
        let mut grammar = Grammar::default();
        let specific = add_production(&mut grammar, "Small", &[], "pick");
        let general = add_production(&mut grammar, "Large", &[], "pick");
        grammar.productions[specific].source_production = Some(identity(0));
        grammar.productions[general].source_production = Some(identity(1));
        grammar.productions[general].prefer = true;
        grammar.overloads = PartialOrder::new([(identity(0), identity(1))]).unwrap();

        let alternative = |production| ParsedTerm::Production {
            production,
            children: Vec::new(),
            metadata: Default::default(),
        };
        let filtered =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                alternative(specific),
                alternative(general),
            ])));

        assert_eq!(filtered, alternative(specific));
        assert_eq!(render(&grammar, &filtered), "pick()");
    }

    #[test]
    fn resolves_overloaded_terminators_and_rejects_incomparable_minima() {
        let sentences = [
            terminal_production("Small", "small", "unit"),
            subsort("Large", "Small"),
            terminal_production("Large", "large", "unit"),
        ];
        let grammar = Grammar::from_sentences(&sentences).unwrap();
        let source = |result: &str| {
            grammar
                .productions
                .iter()
                .enumerate()
                .find_map(|(index, production)| {
                    (production.result.name == result
                        && production
                            .label
                            .as_ref()
                            .is_some_and(|label| label.name == "unit"))
                    .then_some(index)
                })
                .unwrap()
        };
        let resolved = grammar
            .resolve_overloaded_terminators(ParsedTerm::Production {
                production: source("Large"),
                children: Vec::new(),
                metadata: Default::default(),
            })
            .unwrap();
        assert_eq!(render(&grammar, &resolved), "unit()");
        let ParsedTerm::Production { production, .. } = resolved else {
            unreachable!()
        };
        assert_eq!(grammar.productions[production].result.name, "Small");

        let mut ambiguous = Grammar::default();
        let first = add_production(&mut ambiguous, "First", &[], "unit");
        let second = add_production(&mut ambiguous, "Second", &[], "unit");
        let general = add_production(&mut ambiguous, "General", &[], "unit");
        for (index, source) in [first, second, general].into_iter().enumerate() {
            ambiguous.productions[source].source_production = Some(identity(index));
        }
        ambiguous.overloads =
            PartialOrder::new([(identity(0), identity(2)), (identity(1), identity(2))]).unwrap();
        let error = ambiguous
            .resolve_overloaded_terminators(ParsedTerm::Production {
                production: general,
                children: Vec::new(),
                metadata: Default::default(),
            })
            .unwrap_err();

        assert_eq!(grammar.productions[production].result, Sort::new("Small"));
        assert_eq!(
            error,
            ParseError::OverloadedTerminator {
                possible_sorts: vec![Sort::new("First"), Sort::new("Second")],
            }
        );
    }
}

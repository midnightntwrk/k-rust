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
//! bound = "O(N) lowering (parser.lower.term) when every ambiguity has one reading; otherwise a node over children of several readings is kept unexpanded as the product of their readings when lower_term builds it from its children unchanged (a `~>` node: over its spliced items, when none may be a sequence), and an ambiguity node as pairwise disjoint parts, O(A^2) structural comparisons per ambiguity node with each pair of products decided once; a `~>` node whose items may be sequences is the union of such products, one per choice of one part of each of those items; only a #KToken join and the differing children of two overlapping products of one head enumerate their terms; the report then takes, at each subterm it narrows through or reports, one union of the parts' children and at most one of their contexts per child position, and builds one term per entry it lists"
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
use num_bigint::BigUint;
use num_traits::{One, Zero};
use rustc_hash::FxHasher;
use std::hash::{Hash, Hasher};

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
        let mut sets = ReadingSets::default();
        match self.resolve_ambiguities_node(term, &mut sets)? {
            Readings::One(term) => Ok(term),
            readings => Err(self.ambiguity_report(readings, &mut sets)?),
        }
    }

    /// The readings of one node of an inferred tree, as a set over the products in `sets`.
    ///
    /// A production node over children of one reading each is lowered as it stands. Over a
    /// child of several readings, its readings are the lowerings of every combination of its
    /// children's readings. Where `lower_term` builds the node from its children unchanged,
    /// distinct combinations are distinct terms and the set is kept unexpanded as a product
    /// (`Grammar::product_readings`); a `~>` node is such a product over its items when no
    /// item may itself be a sequence, since `Term::sequence` then splices nothing
    /// (`ReadingSets::sequence_items`), and otherwise the union of such products, one per
    /// choice of one part of each item that may be a sequence; a node that denotes its first
    /// child (a bracket, an unlabelled single child) has that child's readings. Only a node
    /// that joins its children's text (a `#KToken` of two strings) has its combinations
    /// enumerated. An ambiguity node's readings are the union of its alternatives', kept as
    /// pairwise disjoint parts (`Grammar::insert_readings`).
    ///
    /// ```toml algorithm-site
    /// id = "parser.diagnostic.ambiguity"
    /// role = "part"
    /// sites = ["Grammar::resolve_ambiguities_node", "Grammar::insert_readings", "Grammar::ambiguity_report", "Grammar::readings_place"]
    /// ```
    fn resolve_ambiguities_node(
        &self,
        term: ParsedTerm,
        sets: &mut ReadingSets,
    ) -> Result<Readings, ParseError> {
        crate::stack::guarded(|| match term.into_parts() {
            ParsedParts::Term(term) => Ok(Readings::One(term)),
            ParsedParts::Production {
                production,
                children,
                metadata,
            } => self.resolve_production_node(production, None, children, metadata, sets),
            ParsedParts::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => {
                self.resolve_production_node(production, Some(parameters), children, metadata, sets)
            }
            ParsedParts::Ambiguity(alternatives) => {
                let mut parts = Parts::default();
                for alternative in alternatives {
                    let alternative = self.resolve_ambiguities_node(alternative, sets)?;
                    self.insert_readings(&mut parts, alternative, sets)?;
                }
                Ok(parts.into_readings())
            }
        })
    }

    fn resolve_production_node(
        &self,
        production: usize,
        parameters: Option<Vec<Sort>>,
        children: Vec<ParsedTerm>,
        metadata: crate::kast::TermMetadata,
        sets: &mut ReadingSets,
    ) -> Result<Readings, ParseError> {
        let mut children = children
            .into_iter()
            .map(|child| self.resolve_ambiguities_node(child, sets))
            .collect::<Result<Vec<_>, _>>()?;
        if children
            .iter()
            .all(|child| matches!(child, Readings::One(_)))
        {
            return self.product_readings(production, parameters, metadata, children, sets);
        }
        let lowered = &self.productions[production];
        if lowered.transparent || lowered.label.is_none() && children.len() == 1 {
            // `lower_term` denotes the node by its first child.
            return Ok(children.swap_remove(0));
        }
        let label = lowered.label.as_ref();
        if label.is_some_and(|label| label.is(InternalLabel::KSequence)) {
            if let Some(items) = sets.sequence_items(&children) {
                return self.product_readings(production, parameters, metadata, items, sets);
            }
            // A child that may be a sequence is split into its parts. Each part is one term, a
            // `~>` product or a product of another head, so every choice of one part per such
            // child splices into items none of which is a sequence, and the node's readings
            // are the union of the products of those choices; no other child is enumerated.
            let mut choices = vec![Vec::with_capacity(children.len())];
            for child in &children {
                let options = if sets.may_be_sequence(child) {
                    child.parts().to_vec()
                } else {
                    vec![child.clone()]
                };
                choices = choices
                    .into_iter()
                    .flat_map(|prefix: Vec<Readings>| {
                        options.iter().map(move |option| {
                            let mut choice = prefix.clone();
                            choice.push(option.clone());
                            choice
                        })
                    })
                    .collect();
            }
            let mut parts = Parts::default();
            for choice in choices {
                let items = sets
                    .sequence_items(&choice)
                    .expect("no item of a chosen part is a sequence");
                let readings = self.product_readings(
                    production,
                    parameters.clone(),
                    metadata.clone(),
                    items,
                    sets,
                )?;
                self.insert_readings(&mut parts, readings, sets)?;
            }
            return Ok(parts.into_readings());
        } else if !label.is_some_and(|label| label.is(InternalLabel::KToken)) {
            return self.product_readings(production, parameters, metadata, children, sets);
        }
        let mut parts = Parts::default();
        for term in self.enumerate_combinations(
            production,
            parameters.as_deref(),
            &metadata,
            &children,
            sets,
        )? {
            self.insert_readings(&mut parts, Readings::One(term), sets)?;
        }
        Ok(parts.into_readings())
    }

    /// The readings of `production` over `children` when `lower_term` builds its node from its
    /// children unchanged: the one lowered term when every child has one reading, otherwise
    /// the product of the children's readings.
    fn product_readings(
        &self,
        production: usize,
        parameters: Option<Vec<Sort>>,
        metadata: crate::kast::TermMetadata,
        children: Vec<Readings>,
        sets: &mut ReadingSets,
    ) -> Result<Readings, ParseError> {
        if children
            .iter()
            .all(|child| matches!(child, Readings::One(_)))
        {
            let children = children
                .into_iter()
                .map(|child| match child {
                    Readings::One(term) => term,
                    Readings::Product(_) | Readings::Union(_) => {
                        unreachable!("every child has one reading")
                    }
                })
                .collect();
            return self
                .lower_production(production, parameters.as_deref(), children, metadata)
                .map(Readings::One);
        }
        // One node over one structure is one product, so a subtree the forest shared, which
        // unpacking copied, is compared with its copies by index.
        let hash = sets.product_hash(production, parameters.as_deref(), &metadata, &children);
        if let Some(index) = sets.consed.get(&hash).and_then(|candidates| {
            candidates.iter().copied().find(|index| {
                let node = &sets.products[*index];
                node.production == production
                    && node.parameters == parameters
                    && node.metadata == metadata
                    && node.children.len() == children.len()
                    && node
                        .children
                        .iter()
                        .zip(&children)
                        .all(|(own, child)| identical_readings(own, child))
            })
        }) {
            return Ok(Readings::Product(index));
        }
        let shape = self.lower_production(
            production,
            parameters.as_deref(),
            vec![hole(); children.len()],
            crate::kast::TermMetadata::default(),
        )?;
        let count = children
            .iter()
            .map(|child| sets.count(child))
            .fold(BigUint::one(), |count, child| count * child);
        sets.products.push(ProductNode {
            production,
            parameters,
            metadata,
            children,
            shape,
            count,
            hash,
        });
        let index = sets.products.len() - 1;
        sets.consed.entry(hash).or_default().push(index);
        Ok(Readings::Product(index))
    }

    /// The lowering of every combination of `children`'s readings, the first child's varying
    /// slowest. Only a node whose lowering may join distinct children, and a split of
    /// overlapping parts (`Grammar::overlap_parts`), enumerate.
    fn enumerate_combinations(
        &self,
        production: usize,
        parameters: Option<&[Sort]>,
        metadata: &crate::kast::TermMetadata,
        children: &[Readings],
        sets: &ReadingSets,
    ) -> Result<Vec<Term>, ParseError> {
        crate::stack::guarded(|| {
            let choices = children
                .iter()
                .map(|child| self.enumerate_readings(child, sets))
                .collect::<Result<Vec<_>, _>>()?;
            let mut terms = Vec::new();
            for combination in combinations(&choices) {
                terms.push(self.lower_production(
                    production,
                    parameters,
                    combination,
                    metadata.clone(),
                )?);
            }
            Ok(terms)
        })
    }

    /// Every term of `readings`.
    fn enumerate_readings(
        &self,
        readings: &Readings,
        sets: &ReadingSets,
    ) -> Result<Vec<Term>, ParseError> {
        crate::stack::guarded(|| match readings {
            Readings::One(term) => Ok(vec![term.clone()]),
            Readings::Product(index) => {
                let node = &sets.products[*index];
                self.enumerate_combinations(
                    node.production,
                    node.parameters.as_deref(),
                    &node.metadata,
                    &node.children,
                    sets,
                )
            }
            Readings::Union(parts) => {
                let mut terms = Vec::new();
                for part in parts {
                    terms.extend(self.enumerate_readings(part, sets)?);
                }
                Ok(terms)
            }
        })
    }

    /// Add the terms of `readings` to the pairwise disjoint `parts`.
    ///
    /// A part disjoint from every part is added as it is, and one inside another part is
    /// dropped. Two products that overlap without either containing the other have one head;
    /// they are replaced by parts of their union that are disjoint (`Grammar::overlap_parts`),
    /// added in turn. Disjointness and containment are decided on the parts' structure,
    /// never by listing their terms (`ReadingSets::disjoint`). The parts of a union are
    /// disjoint already, so each is compared only with the parts that were there before it,
    /// until one of them overlaps one of those.
    fn insert_readings(
        &self,
        parts: &mut Parts,
        readings: Readings,
        sets: &mut ReadingSets,
    ) -> Result<(), ParseError> {
        match readings {
            Readings::Union(added) => {
                let mut earlier = Some(parts.parts.len());
                for part in added {
                    let compared = earlier.unwrap_or(parts.parts.len());
                    earlier = self.insert_part(parts, part, compared, sets)?;
                }
                Ok(())
            }
            part => {
                let compared = parts.parts.len();
                self.insert_part(parts, part, compared, sets).map(|_| ())
            }
        }
    }

    /// Add one part (`One` or `Product`) to the pairwise disjoint `parts`, of which only the
    /// first `compared` can share a term with it. Returns how many of the parts it was
    /// compared with remain, unless it overlapped one of them, which replaced parts that
    /// later parts must be compared with too.
    fn insert_part(
        &self,
        parts: &mut Parts,
        part: Readings,
        mut compared: usize,
        sets: &mut ReadingSets,
    ) -> Result<Option<usize>, ParseError> {
        crate::stack::guarded(|| {
            let hash = sets.readings_hash(&part);
            let mut index = 0;
            while index < compared {
                // Two terms of different hashes differ.
                if matches!(
                    (&part, &parts.parts[index]),
                    (Readings::One(_), Readings::One(_))
                ) && hash != parts.hashes[index]
                    || sets.disjoint(&part, &parts.parts[index])
                {
                    index += 1;
                    continue;
                }
                if sets.subset(&part, &parts.parts[index]) {
                    return Ok(Some(compared));
                }
                compared -= 1;
                if sets.subset(&parts.parts[index], &part) {
                    parts.remove(index);
                    continue;
                }
                let other = parts.remove(index);
                for part in self.overlap_parts(part, other, sets)? {
                    self.insert_readings(parts, part, sets)?;
                }
                return Ok(None);
            }
            parts.parts.push(part);
            parts.hashes.push(hash);
            Ok(Some(compared))
        })
    }

    /// Parts whose union is that of two overlapping products of one head, neither inside the
    /// other.
    ///
    /// Outside the children at which the two differ in structure, their children are the same
    /// sets. When they differ at one child, their union is the product with the union of
    /// those children there. Otherwise the first is split at the differing children into the
    /// products of one combination of its terms there: such a part lies inside the second when
    /// each of its terms there is a term of the second's child, and is disjoint from it
    /// otherwise. Only the differing children are enumerated.
    fn overlap_parts(
        &self,
        part: Readings,
        other: Readings,
        sets: &mut ReadingSets,
    ) -> Result<Vec<Readings>, ParseError> {
        let (Readings::Product(first), Readings::Product(second)) = (&part, &other) else {
            unreachable!("a term in a set is inside it, so only two products overlap otherwise")
        };
        let first = &sets.products[*first];
        let second = &sets.products[*second];
        let differing = (0..first.children.len())
            .filter(|position| !sets.same(&first.children[*position], &second.children[*position]))
            .collect::<Vec<_>>();
        let (production, parameters, metadata) = (
            first.production,
            first.parameters.clone(),
            first.metadata.clone(),
        );
        let mut children = first.children.clone();
        if let [position] = differing[..] {
            let second_child = second.children[position].clone();
            let mut union = Parts::default();
            self.insert_readings(&mut union, children[position].clone(), sets)?;
            self.insert_readings(&mut union, second_child, sets)?;
            children[position] = union.into_readings();
            return Ok(vec![self.product_readings(
                production, parameters, metadata, children, sets,
            )?]);
        }
        let second_children = differing
            .iter()
            .map(|position| second.children[*position].clone())
            .collect::<Vec<_>>();
        let choices = differing
            .iter()
            .map(|position| self.enumerate_readings(&children[*position], sets))
            .collect::<Result<Vec<_>, _>>()?;
        let mut parts = vec![other];
        for combination in combinations(&choices) {
            if second_children
                .iter()
                .zip(&combination)
                .all(|(child, term)| sets.member(child, term))
            {
                continue;
            }
            for (position, term) in differing.iter().zip(combination) {
                children[*position] = Readings::One(term);
            }
            parts.push(self.product_readings(
                production,
                parameters.clone(),
                metadata.clone(),
                children.clone(),
                sets,
            )?);
        }
        Ok(parts)
    }

    /// The union of `readings`.
    fn union_readings(
        &self,
        readings: impl IntoIterator<Item = Readings>,
        sets: &mut ReadingSets,
    ) -> Result<Readings, ParseError> {
        let mut parts = Parts::default();
        for readings in readings {
            self.insert_readings(&mut parts, readings, sets)?;
        }
        Ok(parts.into_readings())
    }

    /// The readings of `parts` with each child at `positions` replaced by a hole: the
    /// contexts of the subterms at those positions.
    fn readings_contexts(
        &self,
        parts: &[Readings],
        positions: &[usize],
        sets: &mut ReadingSets,
    ) -> Result<Readings, ParseError> {
        let mut contexts = Vec::with_capacity(parts.len());
        for part in parts {
            contexts.push(match part {
                Readings::One(term) => {
                    Readings::One(positions.iter().fold(term.clone(), |term, position| {
                        with_argument(&term, *position, hole())
                    }))
                }
                Readings::Product(index) => {
                    let node = &sets.products[*index];
                    let mut children = node.children.clone();
                    for position in positions {
                        children[*position] = Readings::One(hole());
                    }
                    let (production, parameters, metadata) = (
                        node.production,
                        node.parameters.clone(),
                        node.metadata.clone(),
                    );
                    self.product_readings(production, parameters, metadata, children, sets)?
                }
                Readings::Union(_) => unreachable!("the parts of a set are not unions"),
            });
        }
        self.union_readings(contexts, sets)
    }

    /// The least term of `readings` in term order (`ReadingSets::least_view`).
    fn least_reading(&self, readings: &Readings, sets: &ReadingSets) -> Result<Term, ParseError> {
        self.least_term(sets.least_view(readings), sets)
    }

    fn least_term(&self, view: LeastView<'_>, sets: &ReadingSets) -> Result<Term, ParseError> {
        crate::stack::guarded(|| match view {
            LeastView::Term(term) => Ok(term.clone()),
            LeastView::Product(index) => {
                let node = &sets.products[index];
                let children = (0..node.children.len())
                    .map(|position| self.least_term(sets.least_child(index, position), sets))
                    .collect::<Result<Vec<_>, _>>()?;
                self.lower_production(
                    node.production,
                    node.parameters.as_deref(),
                    children,
                    node.metadata.clone(),
                )
            }
        })
    }

    /// The diagnostic of a tree with several readings (`Grammar::readings_place`).
    fn ambiguity_report(
        &self,
        readings: Readings,
        sets: &mut ReadingSets,
    ) -> Result<ParseError, ParseError> {
        let place = self.readings_place(readings, sets)?;
        let parses = saturating_count(&place.parses);
        Ok(match place.shape {
            PlaceShape::Listed(alternatives) => ParseError::Ambiguous {
                parses,
                alternatives,
                span: place.span,
                places: Vec::new(),
                independent: false,
            },
            PlaceShape::Independent(places) => ParseError::Ambiguous {
                parses,
                alternatives: Vec::new(),
                span: place.span,
                places: places.into_iter().map(ReportedPlace::into_place).collect(),
                independent: true,
            },
            PlaceShape::Jointly(places) => ParseError::Ambiguous {
                parses,
                alternatives: Vec::new(),
                span: place.span,
                places: places.into_iter().map(ReportedPlace::into_place).collect(),
                independent: false,
            },
        })
    }

    /// The report of a set of several readings: the smallest subterm outside which every
    /// reading agrees, its number of distinct readings, and how they differ there.
    ///
    /// Every quantity is a property of the set, computed from its parts without listing its
    /// terms. At a child position every reading has, the readings vary independently of the
    /// rest when the number of distinct subterms there times the number of distinct contexts
    /// (each reading with that subterm replaced by a hole) is the number of readings; the
    /// readings are then every combination of a context and the subterms at every such
    /// position. One such position with one context narrows the report to that subterm.
    /// Several, or one with several contexts, are reported as independent places: the
    /// contexts, when there are several, and the subterms at each position, each reported
    /// alike. Where no position varies independently (`Grammar::dependent_place`), readings
    /// with different root heads are listed one entry per head, and readings of one head are
    /// listed, or reported as the subterms at which they differ jointly, whichever takes fewer
    /// entries.
    fn readings_place(
        &self,
        mut set: Readings,
        sets: &mut ReadingSets,
    ) -> Result<ReportedPlace, ParseError> {
        crate::stack::guarded(|| {
            loop {
                let parses = sets.count(&set);
                let span = sets.span(&set);
                let parts = set.parts();
                let arity = parts
                    .iter()
                    .map(|part| sets.key(part).arity())
                    .min()
                    .unwrap_or(0);
                let mut heads = Vec::<(ReadingKey<'_>, BigUint)>::new();
                for part in parts {
                    let key = sets.key(part);
                    match heads.iter_mut().find(|(head, _)| *head == key) {
                        Some((_, count)) => *count += sets.count(part),
                        None => heads.push((key, sets.count(part))),
                    }
                }
                let heads = heads
                    .into_iter()
                    .map(|(_, count)| count)
                    .collect::<Vec<_>>();
                // Readings of different heads have different contexts, so readings that vary
                // independently at a position do so for each head apart: the distinct subterms
                // there divide every head's number of readings, and are at least as many as any
                // part has there. With several heads, a position that cannot meet both is not
                // looked at further, since only an independent one is reported.
                let divisor = heads.iter().fold(BigUint::zero(), |divisor, count| {
                    greatest_common_divisor(divisor, count.clone())
                });
                let mut independent = Vec::new();
                let mut jointly = Vec::new();
                for position in 0..arity {
                    if heads.len() > 1
                        && (divisor.is_one()
                            || parts
                                .iter()
                                .map(|part| sets.argument_count(part, position))
                                .any(|count| count > divisor))
                    {
                        continue;
                    }
                    let arguments = parts
                        .iter()
                        .map(|part| sets.argument(part, position))
                        .collect::<Vec<_>>();
                    let subterms = self.union_readings(arguments, sets)?;
                    let distinct = sets.count(&subterms);
                    if distinct.is_one() {
                        continue;
                    }
                    if !(&divisor % &distinct).is_zero() {
                        jointly.push(subterms);
                        continue;
                    }
                    let contexts = if let [Readings::Product(_)] = parts {
                        &parses / &distinct
                    } else {
                        let contexts = self.readings_contexts(parts, &[position], sets)?;
                        sets.count(&contexts)
                    };
                    if contexts * &distinct == parses {
                        independent.push((position, subterms, distinct));
                    } else {
                        jointly.push(subterms);
                    }
                }
                let contexts = independent
                    .iter()
                    .fold(parses.clone(), |contexts, (_, _, distinct)| {
                        contexts / distinct
                    });
                if independent.len() == 1 && contexts.is_one() {
                    let (_, subterms, _) = independent.pop().expect("one position");
                    set = subterms;
                    continue;
                }
                if independent.is_empty() {
                    return self.dependent_place(&set, parts, jointly, span, parses, sets);
                }
                let mut places = Vec::new();
                if !contexts.is_one() {
                    let positions = independent
                        .iter()
                        .map(|(position, _, _)| *position)
                        .collect::<Vec<_>>();
                    let contexts = self.readings_contexts(parts, &positions, sets)?;
                    self.readings_place(contexts, sets)?
                        .push_independent(&mut places);
                }
                for (_, subterms, _) in independent {
                    self.readings_place(subterms, sets)?
                        .push_independent(&mut places);
                }
                return Ok(ReportedPlace {
                    span,
                    parses,
                    shape: PlaceShape::Independent(places),
                });
            }
        })
    }

    /// The report of readings that vary independently at no child position (`set`, with
    /// `parts`; `jointly` holds the distinct subterms at each position at which they vary).
    ///
    /// Readings with different root heads are listed one entry per head: a head with one
    /// reading is that reading, and a head with several is its least reading and their
    /// number. Readings of one head differ at several positions, but not independently: they
    /// are reported as those positions' subterms, each reported alike, unless listing every
    /// reading takes no more entries.
    fn dependent_place(
        &self,
        set: &Readings,
        parts: &[Readings],
        jointly: Vec<Readings>,
        span: Option<TermSpan>,
        parses: BigUint,
        sets: &mut ReadingSets,
    ) -> Result<ReportedPlace, ParseError> {
        let mut heads = Vec::<(usize, Vec<&Readings>)>::new();
        for (index, part) in parts.iter().enumerate() {
            let key = sets.key(part);
            match heads
                .iter_mut()
                .find(|(first, _)| sets.key(&parts[*first]) == key)
            {
                Some((_, group)) => group.push(part),
                None => heads.push((index, vec![part])),
            }
        }
        if heads.len() > 1 {
            let mut entries = Vec::with_capacity(heads.len());
            for (_, group) in heads {
                let mut least = None::<Term>;
                let mut count = BigUint::zero();
                for part in group {
                    count += sets.count(part);
                    let term = self.least_reading(part, sets)?;
                    if least.as_ref().is_none_or(|least| term < *least) {
                        least = Some(term);
                    }
                }
                entries.push((least.expect("a head has parts"), count));
            }
            entries.sort_by(|(left, _), (right, _)| left.cmp(right));
            return Ok(ReportedPlace {
                span,
                parses,
                shape: PlaceShape::Listed(
                    entries
                        .into_iter()
                        .map(|(term, count)| self.ambiguous_parse(&term, &count))
                        .collect(),
                ),
            });
        }
        let mut places = Vec::new();
        for subterms in jointly {
            self.readings_place(subterms, sets)?
                .push_jointly(&mut places);
        }
        let entries = places
            .iter()
            .map(ReportedPlace::entries)
            .fold(BigUint::zero(), |entries, place| entries + place);
        if parses <= entries {
            let mut terms = self.enumerate_readings(set, sets)?;
            terms.sort();
            return Ok(ReportedPlace {
                span,
                parses,
                shape: PlaceShape::Listed(
                    terms
                        .iter()
                        .map(|term| self.ambiguous_parse(term, &BigUint::one()))
                        .collect(),
                ),
            });
        }
        Ok(ReportedPlace {
            span,
            parses,
            shape: PlaceShape::Jointly(places),
        })
    }

    /// The entry of a reported reading, standing for `count` readings with its root head.
    fn ambiguous_parse(&self, term: &Term, count: &BigUint) -> AmbiguousParse {
        AmbiguousParse {
            production: self.reading_production_text(term),
            term: term.to_string(),
            readings: saturating_count(count),
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
        #[cfg(test)]
        tests::LOWERINGS.with(|count| count.set(count.get() + 1));
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

/// The readings of one node of an inferred tree (`Grammar::resolve_ambiguities_node`): a
/// nonempty set of terms, compared without their metadata.
#[derive(Clone)]
enum Readings {
    One(Term),
    /// A `ProductNode` of `ReadingSets::products` by index: at least two terms.
    Product(usize),
    /// The union of at least two pairwise disjoint sets, each `One` or `Product`.
    Union(Vec<Readings>),
}

impl Readings {
    /// The set that pairwise disjoint, nonempty `parts` make together.
    fn of_parts(mut parts: Vec<Self>) -> Self {
        if parts.len() == 1 {
            parts.pop().expect("one part")
        } else {
            Self::Union(parts)
        }
    }

    /// The parts of this set, each `One` or `Product`.
    fn parts(&self) -> &[Self] {
        match self {
            Self::Union(parts) => parts,
            part => std::slice::from_ref(part),
        }
    }
}

/// The terms `lower_term` builds from `production` over every combination of `children`'s
/// readings, from the children unchanged: a combination is the vector of the term's
/// arguments, so distinct combinations are distinct terms.
struct ProductNode {
    production: usize,
    parameters: Option<Vec<Sort>>,
    metadata: crate::kast::TermMetadata,
    children: Vec<Readings>,
    /// The production lowered over holes, whose head and arity every term of the node has.
    shape: Term,
    /// The number of terms, the product of the children's.
    count: BigUint,
    /// The hash of the node's structure (`ReadingSets::product_hash`).
    hash: u64,
}

/// Pairwise disjoint sets being made into one (`Grammar::insert_readings`), each `One` or
/// `Product`, with the hash of each (`ReadingSets::readings_hash`).
#[derive(Default)]
struct Parts {
    parts: Vec<Readings>,
    hashes: Vec<u64>,
}

impl Parts {
    fn remove(&mut self, index: usize) -> Readings {
        self.hashes.remove(index);
        self.parts.remove(index)
    }

    /// The set the parts make together; there is at least one.
    fn into_readings(self) -> Readings {
        Readings::of_parts(self.parts)
    }
}

/// The products of one tree's readings, one per structure, what deciding their disjointness
/// keeps, and, for a child of a product that is a union, the part with the least term once it
/// was asked for.
#[derive(Default)]
struct ReadingSets {
    products: Vec<ProductNode>,
    /// The products by the hash of their structure.
    consed: HashMap<u64, Vec<usize>>,
    disjointness: DisjointnessMemo,
    least_parts: RefCell<HashMap<(usize, usize), usize>>,
}

impl ReadingSets {
    fn count(&self, readings: &Readings) -> BigUint {
        match readings {
            Readings::One(_) => BigUint::one(),
            Readings::Product(index) => self.products[*index].count.clone(),
            Readings::Union(parts) => parts.iter().map(|part| self.count(part)).sum(),
        }
    }

    /// The head and arity of every term of a part.
    fn key<'a>(&'a self, part: &'a Readings) -> ReadingKey<'a> {
        match part {
            Readings::One(term) => term_key(term),
            Readings::Product(index) => term_key(&self.products[*index].shape),
            Readings::Union(_) => unreachable!("a part is not a union"),
        }
    }

    /// The subterms at `position` of a part's terms.
    fn argument(&self, part: &Readings, position: usize) -> Readings {
        match part {
            Readings::One(term) => Readings::One(term_arguments(term)[position].clone()),
            Readings::Product(index) => self.products[*index].children[position].clone(),
            Readings::Union(_) => unreachable!("a part is not a union"),
        }
    }

    /// The number of subterms at `position` of a part's terms.
    fn argument_count(&self, part: &Readings, position: usize) -> BigUint {
        match part {
            Readings::One(_) => BigUint::one(),
            Readings::Product(index) => self.count(&self.products[*index].children[position]),
            Readings::Union(_) => unreachable!("a part is not a union"),
        }
    }

    /// The span the roots of `readings` cover together.
    fn span(&self, readings: &Readings) -> Option<TermSpan> {
        match readings {
            Readings::One(term) => term.metadata().and_then(|metadata| metadata.span),
            Readings::Product(index) => self.products[*index].metadata.span,
            Readings::Union(parts) => {
                parts
                    .iter()
                    .filter_map(|part| self.span(part))
                    .reduce(|covered, span| TermSpan {
                        source: covered.source,
                        start: covered.start.min(span.start),
                        end: covered.end.max(span.end),
                    })
            }
        }
    }

    /// The hash of a product's structure: its production, metadata span and children's
    /// structures. Terms hash without their metadata, as they compare.
    fn product_hash(
        &self,
        production: usize,
        parameters: Option<&[Sort]>,
        metadata: &crate::kast::TermMetadata,
        children: &[Readings],
    ) -> u64 {
        let mut state = FxHasher::default();
        production.hash(&mut state);
        if let Some(parameters) = parameters {
            parameters
                .iter()
                .for_each(|parameter| hash_sort(parameter, &mut state));
        }
        metadata.span.hash(&mut state);
        for child in children {
            state.write_u64(self.readings_hash(child));
        }
        state.finish()
    }

    fn readings_hash(&self, readings: &Readings) -> u64 {
        match readings {
            Readings::One(term) => {
                let mut state = FxHasher::default();
                hash_term(term, &mut state);
                state.finish()
            }
            Readings::Product(index) => self.products[*index].hash,
            Readings::Union(parts) => {
                let mut state = FxHasher::default();
                state.write_usize(parts.len());
                for part in parts {
                    state.write_u64(self.readings_hash(part));
                }
                state.finish()
            }
        }
    }

    /// Whether `term` is a term of `readings`.
    fn member(&self, readings: &Readings, term: &Term) -> bool {
        readings_member(&self.products, readings, term)
    }

    /// Whether two sets have no term in common (`readings_disjoint`).
    fn disjoint(&mut self, left: &Readings, right: &Readings) -> bool {
        readings_disjoint(&self.products, &mut self.disjointness, left, right)
    }

    /// Whether every term of `left` is a term of `right`, decided on their structure: `false`
    /// can also mean that the structure does not show it.
    fn subset(&self, left: &Readings, right: &Readings) -> bool {
        crate::stack::guarded(|| match (left, right) {
            (Readings::One(term), set) => self.member(set, term),
            (Readings::Union(parts), set) => parts.iter().all(|part| self.subset(part, set)),
            (Readings::Product(_), Readings::Union(parts)) => {
                parts.iter().any(|part| self.subset(left, part))
            }
            (Readings::Product(_), Readings::One(_)) => false,
            (Readings::Product(left), Readings::Product(right)) => {
                if left == right {
                    return true;
                }
                let (left, right) = (&self.products[*left], &self.products[*right]);
                term_key(&left.shape) == term_key(&right.shape)
                    && left
                        .children
                        .iter()
                        .zip(&right.children)
                        .all(|(left, right)| self.subset(left, right))
            }
        })
    }

    /// Whether two sets have one structure, which makes them one set.
    fn same(&self, left: &Readings, right: &Readings) -> bool {
        crate::stack::guarded(|| match (left, right) {
            (Readings::One(left), Readings::One(right)) => left == right,
            (Readings::Product(left), Readings::Product(right)) => {
                left == right || {
                    let (left, right) = (&self.products[*left], &self.products[*right]);
                    term_key(&left.shape) == term_key(&right.shape)
                        && left
                            .children
                            .iter()
                            .zip(&right.children)
                            .all(|(left, right)| self.same(left, right))
                }
            }
            (Readings::Union(left), Readings::Union(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(right)
                        .all(|(left, right)| self.same(left, right))
            }
            _ => false,
        })
    }

    /// The least term of `readings` in term order, without building it.
    ///
    /// Terms compare by kind, then label, then arguments in order, so the least term of a
    /// product is its production over its children's least terms, and that of a union is the
    /// least of its parts'. The parts' least terms are compared as they stand in the parts
    /// (`ReadingSets::compare_least`); only the reported term is built (`Grammar::least_term`).
    fn least_view<'a>(&'a self, readings: &'a Readings) -> LeastView<'a> {
        match readings {
            Readings::One(term) => LeastView::Term(term),
            Readings::Product(index) => LeastView::Product(*index),
            Readings::Union(parts) => self.least_view(&parts[self.least_part(parts)]),
        }
    }

    /// The least term of the child at `position` of the product `index`.
    fn least_child(&self, index: usize, position: usize) -> LeastView<'_> {
        let child = &self.products[index].children[position];
        let Readings::Union(parts) = child else {
            return self.least_view(child);
        };
        let known = self.least_parts.borrow().get(&(index, position)).copied();
        let least = known.unwrap_or_else(|| {
            let least = self.least_part(parts);
            self.least_parts
                .borrow_mut()
                .insert((index, position), least);
            least
        });
        self.least_view(&parts[least])
    }

    /// The index of the part of `parts` with the least term.
    fn least_part(&self, parts: &[Readings]) -> usize {
        (1..parts.len()).fold(0, |least, index| {
            match self.compare_least(
                self.least_view(&parts[index]),
                self.least_view(&parts[least]),
            ) {
                std::cmp::Ordering::Less => index,
                std::cmp::Ordering::Equal | std::cmp::Ordering::Greater => least,
            }
        })
    }

    /// The order of two least terms, as `Term::cmp` orders the terms they stand for.
    fn compare_least<'a>(
        &'a self,
        left: LeastView<'a>,
        right: LeastView<'a>,
    ) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        crate::stack::guarded(|| {
            if let (LeastView::Term(left), LeastView::Term(right)) = (left, right) {
                return left.cmp(right);
            }
            let head = |view: LeastView<'a>| -> &'a Term {
                match view {
                    LeastView::Term(term) => term.unannotated(),
                    LeastView::Product(index) => self.products[index].shape.unannotated(),
                }
            };
            let (left_head, right_head) = (head(left), head(right));
            match term_rank(left_head).cmp(&term_rank(right_head)) {
                Ordering::Equal => {}
                ordering => return ordering,
            }
            if let (
                Term::Apply {
                    label: left_label, ..
                },
                Term::Apply {
                    label: right_label, ..
                },
            ) = (left_head, right_head)
            {
                match left_label.cmp(right_label) {
                    Ordering::Equal => {}
                    ordering => return ordering,
                }
            }
            let arity = |view: LeastView<'_>| match view {
                LeastView::Term(term) => term_arguments(term).len(),
                LeastView::Product(index) => self.products[index].children.len(),
            };
            let argument = |view: LeastView<'a>, position: usize| -> LeastView<'a> {
                match view {
                    LeastView::Term(term) => LeastView::Term(term_arguments(term)[position]),
                    LeastView::Product(index) => self.least_child(index, position),
                }
            };
            let (left_arity, right_arity) = (arity(left), arity(right));
            for position in 0..left_arity.min(right_arity) {
                match self.compare_least(argument(left, position), argument(right, position)) {
                    Ordering::Equal => {}
                    ordering => return ordering,
                }
            }
            left_arity.cmp(&right_arity)
        })
    }

    /// The items of a `~>` node over `children` when its readings are the sequences of every
    /// combination of those items' readings, all distinct: when no item has a reading that is
    /// itself a sequence, which `Term::sequence` would splice. A child of one sequence reading
    /// and a `~>` product contribute their items.
    fn sequence_items(&self, children: &[Readings]) -> Option<Vec<Readings>> {
        let mut items = Vec::with_capacity(children.len());
        for child in children {
            match child {
                Readings::One(term) => match term.unannotated() {
                    Term::Sequence(nested) => {
                        items.extend(nested.iter().cloned().map(Readings::One));
                    }
                    _ => items.push(child.clone()),
                },
                Readings::Product(index)
                    if matches!(
                        term_key(&self.products[*index].shape),
                        ReadingKey::Sequence(_)
                    ) =>
                {
                    items.extend(self.products[*index].children.iter().cloned());
                }
                _ if self.may_be_sequence(child) => return None,
                _ => items.push(child.clone()),
            }
        }
        Some(items)
    }

    /// Whether some term of `readings` is a sequence.
    fn may_be_sequence(&self, readings: &Readings) -> bool {
        readings.parts().iter().any(|part| match part {
            Readings::One(term) => matches!(term.unannotated(), Term::Sequence(_)),
            Readings::Product(index) => matches!(
                term_key(&self.products[*index].shape),
                ReadingKey::Sequence(_)
            ),
            Readings::Union(_) => unreachable!("a part is not a union"),
        })
    }
}

fn readings_member(products: &[ProductNode], readings: &Readings, term: &Term) -> bool {
    crate::stack::guarded(|| match readings {
        Readings::One(own) => own == term,
        Readings::Product(index) => {
            let node = &products[*index];
            term_key(&node.shape) == term_key(term)
                && node
                    .children
                    .iter()
                    .zip(term_arguments(term))
                    .all(|(child, argument)| readings_member(products, child, argument))
        }
        Readings::Union(parts) => parts
            .iter()
            .any(|part| readings_member(products, part, term)),
    })
}

/// What `readings_disjoint` keeps between calls: the decided disjointness of pairs of
/// products, and for a child of a product that is a union, its parts of one term each, sorted.
#[derive(Default)]
struct DisjointnessMemo {
    products: HashMap<(usize, usize), bool>,
    sorted_terms: HashMap<(usize, usize), Rc<[usize]>>,
}

/// Whether two sets have no term in common: a term is outside a set it is not a member of,
/// products of different heads are disjoint, and products of one head are disjoint when their
/// children at some position are.
fn readings_disjoint(
    products: &[ProductNode],
    memo: &mut DisjointnessMemo,
    left: &Readings,
    right: &Readings,
) -> bool {
    crate::stack::guarded(|| match (left, right) {
        (Readings::Union(parts), other) | (other, Readings::Union(parts)) => parts
            .iter()
            .all(|part| readings_disjoint(products, memo, part, other)),
        (Readings::One(left), Readings::One(right)) => left != right,
        (Readings::One(term), set) | (set, Readings::One(term)) => {
            !readings_member(products, set, term)
        }
        (Readings::Product(left), Readings::Product(right)) => {
            if left == right {
                return false;
            }
            let pair = (*left.min(right), *left.max(right));
            if let Some(disjoint) = memo.products.get(&pair) {
                return *disjoint;
            }
            let (first, second) = (&products[*left], &products[*right]);
            let disjoint = term_key(&first.shape) != term_key(&second.shape) || {
                let pairs = || first.children.iter().zip(&second.children).enumerate();
                // Children of one term each are compared first: they decide most pairs.
                pairs().any(|(_, pair)| {
                    matches!(pair, (Readings::One(left), Readings::One(right)) if left != right)
                }) || pairs().any(|(position, pair)| match pair {
                    (Readings::One(_), Readings::One(_)) => false,
                    (Readings::Union(_), Readings::Union(_)) => children_disjoint(
                        products,
                        memo,
                        (*left, position),
                        (*right, position),
                    ),
                    (left, right) => readings_disjoint(products, memo, left, right),
                })
            };
            memo.products.insert(pair, disjoint);
            disjoint
        }
    })
}

/// Whether two children of products that are unions have no term in common: their parts of
/// one term each are compared in term order, and every other pair of parts in turn.
fn children_disjoint(
    products: &[ProductNode],
    memo: &mut DisjointnessMemo,
    left: (usize, usize),
    right: (usize, usize),
) -> bool {
    let parts = |(index, position): (usize, usize)| -> &[Readings] {
        products[index].children[position].parts()
    };
    let (left_parts, right_parts) = (parts(left), parts(right));
    fn term(part: &Readings) -> &Term {
        match part {
            Readings::One(term) => term,
            Readings::Product(_) | Readings::Union(_) => unreachable!("a part of one term"),
        }
    }
    fn several(parts: &[Readings]) -> Vec<&Readings> {
        parts
            .iter()
            .filter(|part| !matches!(part, Readings::One(_)))
            .collect()
    }
    let mut sorted = |child: (usize, usize)| -> Rc<[usize]> {
        Rc::clone(memo.sorted_terms.entry(child).or_insert_with(|| {
            let parts = parts(child);
            let mut terms = (0..parts.len())
                .filter(|index| matches!(parts[*index], Readings::One(_)))
                .collect::<Vec<_>>();
            terms.sort_by(|left, right| term(&parts[*left]).cmp(term(&parts[*right])));
            terms.into()
        }))
    };
    let (left_terms, right_terms) = (sorted(left), sorted(right));
    let (mut left_index, mut right_index) = (0, 0);
    while left_index < left_terms.len() && right_index < right_terms.len() {
        match term(&left_parts[left_terms[left_index]])
            .cmp(term(&right_parts[right_terms[right_index]]))
        {
            std::cmp::Ordering::Less => left_index += 1,
            std::cmp::Ordering::Greater => right_index += 1,
            std::cmp::Ordering::Equal => return false,
        }
    }
    let (left_several, right_several) = (several(left_parts), several(right_parts));
    left_terms.iter().all(|index| {
        let term = term(&left_parts[*index]);
        right_several
            .iter()
            .all(|part| !readings_member(products, part, term))
    }) && right_terms.iter().all(|index| {
        let term = term(&right_parts[*index]);
        left_several
            .iter()
            .all(|part| !readings_member(products, part, term))
    }) && left_several.iter().all(|left| {
        right_several
            .iter()
            .all(|right| readings_disjoint(products, memo, left, right))
    })
}

/// Whether two sets are built alike, metadata included, from products that are one product
/// when built alike.
fn identical_readings(left: &Readings, right: &Readings) -> bool {
    match (left, right) {
        (Readings::One(left), Readings::One(right)) => left.identical(right),
        (Readings::Product(left), Readings::Product(right)) => left == right,
        (Readings::Union(left), Readings::Union(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| identical_readings(left, right))
        }
        _ => false,
    }
}

/// Hash `term` without its metadata, consistently with `Term`'s equality.
fn hash_term(term: &Term, state: &mut FxHasher) {
    crate::stack::guarded(|| {
        let term = term.unannotated();
        state.write_u8(term_rank(term));
        match term {
            Term::InjectedLabel(label) => hash_label(label, state),
            Term::Rewrite { .. } | Term::As { .. } | Term::Sequence(_) | Term::Apply { .. } => {
                if let Term::Apply { label, .. } = term {
                    hash_label(label, state);
                }
                let arguments = term_arguments(term);
                state.write_usize(arguments.len());
                for argument in arguments {
                    hash_term(argument, state);
                }
            }
            Term::Variable { name, sort } => {
                name.hash(state);
                if let Some(sort) = sort {
                    hash_sort(sort, state);
                }
            }
            Term::Token { token, sort } => {
                token.hash(state);
                hash_sort(sort, state);
            }
            Term::Annotated { .. } => unreachable!("an unannotated term"),
        }
    });
}

fn hash_label(label: &crate::kast::Label, state: &mut FxHasher) {
    label.name.hash(state);
    state.write_usize(label.parameters.len());
    for parameter in &label.parameters {
        hash_sort(parameter, state);
    }
}

fn hash_sort(sort: &Sort, state: &mut FxHasher) {
    crate::stack::guarded(|| {
        sort.name.hash(state);
        state.write_usize(sort.parameters.len());
        for parameter in &sort.parameters {
            hash_sort(parameter, state);
        }
    });
}

/// The least term of a set of readings (`ReadingSets::least_view`): a term, or the least
/// term of a product.
#[derive(Clone, Copy)]
enum LeastView<'a> {
    Term(&'a Term),
    Product(usize),
}

/// The rank of a term's kind in `Term::cmp`, which orders terms by kind first.
fn term_rank(term: &Term) -> u8 {
    match term {
        Term::InjectedLabel(_) => 0,
        Term::Rewrite { .. } => 1,
        Term::As { .. } => 2,
        Term::Variable { .. } => 3,
        Term::Sequence(_) => 4,
        Term::Apply { .. } => 5,
        Term::Token { .. } => 6,
        Term::Annotated { .. } => unreachable!("an unannotated term"),
    }
}

/// The head and arity of a term, or the term itself when it has no arguments of its own: two
/// terms with one key differ only in their arguments.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum ReadingKey<'a> {
    Rewrite,
    As,
    Sequence(usize),
    Apply(&'a crate::kast::Label, usize),
    Leaf(&'a Term),
}

impl ReadingKey<'_> {
    fn arity(self) -> usize {
        match self {
            Self::Rewrite | Self::As => 2,
            Self::Sequence(arity) | Self::Apply(_, arity) => arity,
            Self::Leaf(_) => 0,
        }
    }
}

fn term_key(term: &Term) -> ReadingKey<'_> {
    match term.unannotated() {
        Term::Rewrite { .. } => ReadingKey::Rewrite,
        Term::As { .. } => ReadingKey::As,
        Term::Sequence(items) => ReadingKey::Sequence(items.len()),
        Term::Apply { label, arguments } => ReadingKey::Apply(label, arguments.len()),
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => {
            ReadingKey::Leaf(leaf)
        }
        Term::Annotated { .. } => unreachable!("an unannotated term"),
    }
}

/// The arguments of a term, in the order of its key's arity.
fn term_arguments(term: &Term) -> Vec<&Term> {
    match term.unannotated() {
        Term::Rewrite { left, right } => vec![&**left, &**right],
        Term::As { pattern, alias } => vec![&**pattern, &**alias],
        Term::Sequence(items) => items.iter().collect(),
        Term::Apply { arguments, .. } => arguments.iter().collect(),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => Vec::new(),
        Term::Annotated { .. } => unreachable!("an unannotated term"),
    }
}

/// `term` with its argument at `position` replaced by `argument`, keeping its metadata.
fn with_argument(term: &Term, position: usize, argument: Term) -> Term {
    let mut arguments = term_arguments(term)
        .into_iter()
        .cloned()
        .collect::<Vec<_>>();
    arguments[position] = argument;
    let rebuilt = match term.unannotated() {
        Term::Rewrite { .. } | Term::As { .. } => {
            let [first, second] = <[Term; 2]>::try_from(arguments)
                .unwrap_or_else(|_| unreachable!("a rewrite or alias has two arguments"));
            let (first, second) = (Box::new(first), Box::new(second));
            if matches!(term.unannotated(), Term::Rewrite { .. }) {
                Term::Rewrite {
                    left: first,
                    right: second,
                }
            } else {
                Term::As {
                    pattern: first,
                    alias: second,
                }
            }
        }
        Term::Sequence(_) => Term::Sequence(arguments),
        Term::Apply { label, .. } => Term::Apply {
            label: label.clone(),
            arguments,
        },
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {
            unreachable!("a term with arguments")
        }
        Term::Annotated { .. } => unreachable!("an unannotated term"),
    };
    match term.metadata() {
        Some(metadata) => rebuilt.with_metadata(metadata.clone()),
        None => rebuilt,
    }
}

/// The term that stands for a subterm left out of a context, or for an argument of a
/// production lowered for its shape.
fn hole() -> Term {
    Term::variable("□")
}

/// Every combination of one term of each of `choices`, the first varying slowest.
fn combinations(choices: &[Vec<Term>]) -> Vec<Vec<Term>> {
    let mut combinations = vec![Vec::with_capacity(choices.len())];
    for terms in choices {
        combinations = combinations
            .into_iter()
            .flat_map(|prefix| {
                terms.iter().map(move |term| {
                    let mut combination = prefix.clone();
                    combination.push(term.clone());
                    combination
                })
            })
            .collect();
    }
    combinations
}

fn greatest_common_divisor(mut left: BigUint, mut right: BigUint) -> BigUint {
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

/// A count of readings as a `usize`, `usize::MAX` for a larger one.
fn saturating_count(count: &BigUint) -> usize {
    usize::try_from(count).unwrap_or(usize::MAX)
}

/// The report of a set of readings (`Grammar::readings_place`).
struct ReportedPlace {
    span: Option<TermSpan>,
    parses: BigUint,
    shape: PlaceShape,
}

enum PlaceShape {
    /// The readings, or one entry per root head.
    Listed(Vec<AmbiguousParse>),
    /// Places whose readings combine freely: each listed or `Jointly`.
    Independent(Vec<ReportedPlace>),
    /// Listed places at which the readings differ, of whose readings' combinations only some
    /// are readings.
    Jointly(Vec<ReportedPlace>),
}

impl ReportedPlace {
    /// The entries the report lists.
    fn entries(&self) -> BigUint {
        match &self.shape {
            PlaceShape::Listed(entries) => BigUint::from(entries.len()),
            PlaceShape::Independent(places) | PlaceShape::Jointly(places) => {
                places.iter().map(Self::entries).sum()
            }
        }
    }

    /// Add this report to places that vary independently: the places of an independent report
    /// are themselves such places.
    fn push_independent(self, places: &mut Vec<Self>) {
        match self.shape {
            PlaceShape::Independent(inner) => places.extend(inner),
            PlaceShape::Listed(_) | PlaceShape::Jointly(_) => places.push(self),
        }
    }

    /// Add this report to places that vary jointly: every listed place below it is such a
    /// place.
    fn push_jointly(self, places: &mut Vec<Self>) {
        match self.shape {
            PlaceShape::Independent(inner) | PlaceShape::Jointly(inner) => {
                for place in inner {
                    place.push_jointly(places);
                }
            }
            PlaceShape::Listed(_) => places.push(self),
        }
    }

    fn into_place(self) -> AmbiguityPlace {
        let parses = saturating_count(&self.parses);
        match self.shape {
            PlaceShape::Listed(alternatives) => AmbiguityPlace {
                span: self.span,
                location: None,
                parses,
                alternatives,
                places: Vec::new(),
            },
            PlaceShape::Independent(places) | PlaceShape::Jointly(places) => AmbiguityPlace {
                span: self.span,
                location: None,
                parses,
                alternatives: Vec::new(),
                places: places.into_iter().map(Self::into_place).collect(),
            },
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
    use std::cell::Cell;
    use std::collections::BTreeMap;

    thread_local! {
        /// The calls of `Grammar::lower_production` on this thread.
        pub(super) static LOWERINGS: Cell<usize> = const { Cell::new(0) };
    }

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

    /// A grammar of `wrapper(Exp)`, `pair(Exp, Exp)`, `couple(Exp, Exp)`, a `~>` over two
    /// `Exp`, the empty sequence `#EmptyK`, and constants `a` to `d` and `outer`, and a builder
    /// of its production nodes over `start..start + 1`.
    fn readings_fixture() -> (Grammar, impl Fn(&str, Vec<ParsedTerm>, usize) -> ParsedTerm) {
        let mut grammar = Grammar::default();
        let mut productions = BTreeMap::new();
        productions.insert(
            "wrapper",
            add_production(&mut grammar, "Exp", &["Exp"], "wrapper"),
        );
        for name in ["pair", "couple"] {
            productions.insert(
                name,
                add_production(&mut grammar, "Exp", &["Exp", "Exp"], name),
            );
        }
        productions.insert(
            "~>",
            add_production(
                &mut grammar,
                "Exp",
                &["Exp", "Exp"],
                InternalLabel::KSequence.as_str(),
            ),
        );
        productions.insert(
            "#EmptyK",
            add_production(&mut grammar, "Exp", &[], InternalLabel::EmptyK.as_str()),
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

    /// `choices` nested `pair`s whose leaves each read `a` or `b`, the leaf `i` at `10 * (i +
    /// 1)`: packed as one ambiguity per leaf, or, `flat`, as one ambiguity over every tree.
    fn independent_choices(
        node: &impl Fn(&str, Vec<ParsedTerm>, usize) -> ParsedTerm,
        choices: usize,
        flat: bool,
    ) -> ParsedTerm {
        let leaf = |index: usize, name: &str| node(name, vec![], 10 * (index + 1));
        if flat {
            let trees = (0..1usize << choices).map(|combination| {
                (0..choices)
                    .rev()
                    .map(|index| {
                        let name = if combination >> (choices - 1 - index) & 1 == 0 {
                            "a"
                        } else {
                            "b"
                        };
                        leaf(index, name)
                    })
                    .reduce(|right, left| node("pair", vec![left, right], 0))
                    .expect("at least one choice")
            });
            return ambiguity(trees);
        }
        (0..choices)
            .rev()
            .map(|index| ambiguity([leaf(index, "a"), leaf(index, "b")]))
            .reduce(|right, left| node("pair", vec![left, right], 0))
            .expect("at least one choice")
    }

    #[test]
    fn reports_the_smallest_subterm_outside_which_every_reading_agrees() {
        let (grammar, node) = readings_fixture();
        // `wrapper(a)`, `wrapper(b)` and `outer` differ at the root, so the report is the root,
        // not the inner ambiguity between `a` and `b`; its readings are listed one entry per
        // root head, `wrapper(a)` standing for the two `wrapper` readings.
        let root = ambiguity([
            node(
                "wrapper",
                vec![ambiguity([node("a", vec![], 10), node("b", vec![], 10)])],
                0,
            ),
            node("outer", vec![], 0),
        ]);
        let report = grammar.resolve_ambiguities(root).unwrap_err();
        let ParseError::Ambiguous {
            parses,
            ref alternatives,
            span,
            ref places,
            ..
        } = report
        else {
            panic!("expected an ambiguity")
        };
        assert_eq!(parses, 3);
        assert_eq!(span.map(|span| span.start), Some(0));
        assert_eq!(
            rendered(alternatives),
            ["outer(.KList)", "wrapper(a(.KList))"]
        );
        assert_eq!(
            alternatives
                .iter()
                .map(|alternative| alternative.readings)
                .collect::<Vec<_>>(),
            [1, 2]
        );
        assert!(places.is_empty());
        assert!(
            report
                .to_string()
                .starts_with("Parsing ambiguity: 3 readings.")
                && report
                    .to_string()
                    .ends_with("wrapper(a(.KList))\n    and 1 more reading with the same root"),
            "{report}"
        );
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
            independent,
        } = &report
        else {
            panic!("expected an ambiguity")
        };
        assert_eq!(*parses, 4);
        assert!(*independent);
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
        let message = report.to_string();
        assert!(
            message.starts_with(
                "Parsing ambiguity: 4 readings, which differ independently in 2 subterms."
            ) && message.contains("\nSubterm 2 at bytes 20..21:\n1: "),
            "{message}"
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
        // Listing the two readings takes fewer entries than the two subterms' four.
        let ParseError::Ambiguous {
            parses,
            alternatives,
            span,
            places,
            ..
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
    fn readings_that_differ_jointly_are_reported_at_their_subterms_when_that_lists_less() {
        let (grammar, node) = readings_fixture();
        // `pair(T, c)` and `pair(wrapper(T), d)`, where `T` has 8 readings: 16 readings, which
        // differ at both children of `pair` but not independently. Reporting the two subterms
        // takes 4 entries: `T` and `wrapper(T)` one entry per head, then `c` and `d`.
        let root = |flat: bool| {
            ambiguity([
                node(
                    "pair",
                    vec![independent_choices(&node, 3, flat), node("c", vec![], 100)],
                    0,
                ),
                node(
                    "pair",
                    vec![
                        node("wrapper", vec![independent_choices(&node, 3, flat)], 5),
                        node("d", vec![], 100),
                    ],
                    0,
                ),
            ])
        };
        let report = grammar.resolve_ambiguities(root(false)).unwrap_err();
        assert_eq!(grammar.resolve_ambiguities(root(true)).unwrap_err(), report);
        let ParseError::Ambiguous {
            parses,
            ref alternatives,
            ref places,
            independent,
            ..
        } = report
        else {
            panic!("expected an ambiguity")
        };
        assert_eq!(parses, 16);
        assert!(!independent);
        assert!(alternatives.is_empty());
        assert_eq!(
            places
                .iter()
                .map(|place| (
                    place.parses,
                    place
                        .alternatives
                        .iter()
                        .map(|alternative| alternative.readings)
                        .collect::<Vec<_>>()
                ))
                .collect::<Vec<_>>(),
            [(16, vec![8, 8]), (2, vec![1, 1])]
        );
        assert!(
            report
                .to_string()
                .starts_with("Parsing ambiguity: 16 readings, which differ jointly in 2 subterms."),
            "{report}"
        );

        // Below a choice independent of it, the subterm is one place, reported by its own
        // subterms.
        let outer = node(
            "couple",
            vec![
                root(false),
                ambiguity([node("a", vec![], 200), node("b", vec![], 200)]),
            ],
            0,
        );
        let report = grammar.resolve_ambiguities(outer).unwrap_err();
        let ParseError::Ambiguous {
            parses,
            ref places,
            independent,
            ..
        } = report
        else {
            panic!("expected an ambiguity")
        };
        assert_eq!(parses, 32);
        assert!(independent);
        assert_eq!(
            places
                .iter()
                .map(|place| (place.parses, place.places.len()))
                .collect::<Vec<_>>(),
            [(16, 2), (2, 0)]
        );
        let message = report.to_string();
        assert!(
            message.starts_with(
                "Parsing ambiguity: 32 readings, which differ independently in 2 subterms.\n\
                 Subterm 1 at bytes 0..1: 16 readings, which differ jointly in 2 subterms.\n\
                 Subterm 1.1 at bytes 0..6:\n1: "
            ) && message.contains("\nSubterm 1.2 at bytes 100..101:\n1: ")
                && message.contains("\nSubterm 2 at bytes 200..201:\n1: "),
            "{message}"
        );
    }

    #[test]
    fn readings_with_two_heads_over_independent_choices_report_their_contexts_as_a_place() {
        let (grammar, node) = readings_fixture();
        // `pair(a, T)` and `couple(b, T)`, where `T` has 2^k readings, as `a(X, Y, t(...))` read
        // through two productions over `t(...)`: the two contexts of `T` and each of its `k`
        // choices are independent places, found without listing the 2 x 2^k readings.
        let root = |choices, flat| {
            ambiguity([
                node(
                    "pair",
                    vec![
                        node("a", vec![], 1),
                        independent_choices(&node, choices, flat),
                    ],
                    0,
                ),
                node(
                    "couple",
                    vec![
                        node("b", vec![], 1),
                        independent_choices(&node, choices, flat),
                    ],
                    0,
                ),
            ])
        };
        let report = grammar.resolve_ambiguities(root(4, false)).unwrap_err();
        assert_eq!(
            grammar.resolve_ambiguities(root(4, true)).unwrap_err(),
            report
        );
        let ParseError::Ambiguous {
            parses,
            ref places,
            independent,
            ..
        } = report
        else {
            panic!("expected an ambiguity")
        };
        assert_eq!(parses, 32);
        assert!(independent);
        assert_eq!(places.len(), 5);
        assert_eq!(
            rendered(&places[0].alternatives),
            ["couple(b(.KList),□)", "pair(a(.KList),□)"]
        );
        assert!(
            places[1..]
                .iter()
                .all(|place| { rendered(&place.alternatives) == ["a(.KList)", "b(.KList)"] })
        );

        let lowerings = |choices| {
            LOWERINGS.with(|count| count.set(0));
            let error = grammar
                .resolve_ambiguities(root(choices, false))
                .unwrap_err();
            assert!(
                matches!(error, ParseError::Ambiguous { parses, .. } if parses == 2 << choices),
                "{error:?}"
            );
            LOWERINGS.with(Cell::get)
        };
        // Each 4 more choices take as many more lowerings: the work is linear in their number.
        let counts = [lowerings(4), lowerings(8), lowerings(12)];
        assert_eq!(counts[2] - counts[1], counts[1] - counts[0], "{counts:?}");
    }

    #[test]
    fn overlapping_alternatives_count_their_common_readings_once() {
        let (grammar, node) = readings_fixture();
        let left = |name| node(name, vec![], 10);
        let right = |name| node(name, vec![], 20);
        // `pair(a | b, c)` and `pair(a, c | d)` share `pair(a, c)`.
        let packed = ambiguity([
            node(
                "pair",
                vec![ambiguity([left("a"), left("b")]), right("c")],
                0,
            ),
            node(
                "pair",
                vec![left("a"), ambiguity([right("c"), right("d")])],
                0,
            ),
        ]);
        let flat = ambiguity(
            [("a", "c"), ("a", "d"), ("b", "c")]
                .map(|(first, second)| node("pair", vec![left(first), right(second)], 0)),
        );
        let report = grammar.resolve_ambiguities(packed).unwrap_err();
        assert_eq!(grammar.resolve_ambiguities(flat).unwrap_err(), report);
        let ParseError::Ambiguous {
            parses,
            alternatives,
            ..
        } = report
        else {
            panic!("expected an ambiguity")
        };
        assert_eq!(parses, 3);
        assert_eq!(
            rendered(&alternatives),
            [
                "pair(a(.KList),c(.KList))",
                "pair(a(.KList),d(.KList))",
                "pair(b(.KList),c(.KList))"
            ]
        );
    }

    #[test]
    fn a_sequence_of_ambiguous_items_is_reported_in_work_linear_in_its_length() {
        let (grammar, node) = readings_fixture();
        // `x ~> x ~> ... ~> x`, each `x` reading `a` or `b`, nested as the parser builds a
        // binary `~>`: its readings are the sequences of every combination of the items'.
        let sequence = |items: usize| {
            (0..items)
                .map(|index| {
                    ambiguity([
                        node("a", vec![], 10 * (index + 1)),
                        node("b", vec![], 10 * (index + 1)),
                    ])
                })
                .reduce(|left, right| node("~>", vec![left, right], 0))
                .expect("at least one item")
        };
        let lowerings = |items| {
            LOWERINGS.with(|count| count.set(0));
            let error = grammar.resolve_ambiguities(sequence(items)).unwrap_err();
            let ParseError::Ambiguous {
                parses,
                places,
                independent,
                ..
            } = error
            else {
                panic!("expected an ambiguity")
            };
            assert_eq!(parses, 1 << items);
            assert!(independent);
            assert_eq!(places.len(), items);
            LOWERINGS.with(Cell::get)
        };
        // Each 4 more choices take as many more lowerings: the work is linear in their number.
        let counts = [lowerings(4), lowerings(8), lowerings(12)];
        assert_eq!(counts[2] - counts[1], counts[1] - counts[0], "{counts:?}");
    }

    #[test]
    fn a_sequence_whose_last_item_may_be_empty_is_reported_in_work_linear_in_its_length() {
        let (grammar, node) = readings_fixture();
        // `x ~> ... ~> x ~> y`, each `x` reading `a` or `b` and `y` reading `a` or the empty
        // sequence, nested as the parser builds a binary `~>`. The root's right child may be
        // a sequence, so its items are not known before a reading of `y` is chosen; the
        // readings are still the sequences of every combination, all distinct.
        let sequence = |items: usize| {
            (0..items)
                .map(|index| {
                    ambiguity([
                        node("a", vec![], 10 * (index + 1)),
                        node("b", vec![], 10 * (index + 1)),
                    ])
                })
                .chain([ambiguity([
                    node("a", vec![], 10 * (items + 1)),
                    node("#EmptyK", vec![], 10 * (items + 1)),
                ])])
                .reduce(|left, right| node("~>", vec![left, right], 0))
                .expect("at least one item")
        };
        let lowerings = |items| {
            LOWERINGS.with(|count| count.set(0));
            let error = grammar.resolve_ambiguities(sequence(items)).unwrap_err();
            let ParseError::Ambiguous { parses, .. } = error else {
                panic!("expected an ambiguity")
            };
            assert_eq!(parses, 2 << items);
            LOWERINGS.with(Cell::get)
        };
        // Each 4 more choices take as many more lowerings: the work is linear in their number.
        let counts = [lowerings(4), lowerings(8), lowerings(12)];
        assert_eq!(counts[2] - counts[1], counts[1] - counts[0], "{counts:?}");
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

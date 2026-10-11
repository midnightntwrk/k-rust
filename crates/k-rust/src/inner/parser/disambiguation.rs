//! ```toml algorithm
//! id = "parser.disambiguation.priority"
//! name = "priority and associativity filtering of packed terms"
//! sites = ["Grammar::filter_packed_priority", "Grammar::filter_completed_packed_priority"]
//! variable = "N = packed nodes per memo lifetime"
//! counters = ["ParserPackedPriorityComputations"]
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one parse forest"
//! bound = "O(N)"
//!
//! [[cost]]
//! mode = "one completion candidate (filter_completed_packed_priority)"
//! bound = "one memoized packed filter; a candidate that breaks any relation, a scope error included, is dropped"
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
//! bound = "O(N) lowering (parser.lower.term) when every ambiguity has one reading; otherwise each node's readings are an expression over its children's, built once per structure: a product, the union of an ambiguity node's alternatives (equal terms merged by hash, O(A) per node), or the concatenation a `~>` node splices, with only the string tokens of a #KToken node's two children paired; the report is polynomial in N and never lists or counts the readings: each question it asks a node (root keys, subterms at a position of the readings of one key, items at an index of the words of one length, least reading, least word of a length) is answered once per node and argument from its children's answers, an item of a concatenation in O(N^2) over its children and the lengths before them, and it builds one term per entry it lists"
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
//! 11. Factor and report remaining ambiguities (owned tree, O(nodes * alternatives); the report
//!     is polynomial in the nodes and never lists the readings).
//!
//! One node/child memo pair is shared through recognition and packed-forest preparation for each
//! parse attempt; child keys are `(identity, parent production, side)`.
//! `Counter::ParserPackedPriorityComputations` counts priority memo misses. Portable and Z3
//! inference paths remain independent oracles and must produce the same accepted tree.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use k_rust_kore::measure::{self, Algorithm, Counter};
use rustc_hash::FxHasher;
use std::hash::{Hash, Hasher};

use super::exclusion::{Exclusion, Side};
use super::{
    AmbiguityPlace, AmbiguousParse, Grammar, Item, PackedNode, PackedTerm, ParseError, ParsedParts,
    ParsedTerm, Production, StructuralOrder, cmp_packed_structurally, lower_term,
};
use crate::kast::{
    FrontendSort, InternalLabel, ProductionIdentity, Sort, Term, TermMetadata, TermSpan, string,
};

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

    /// Filter a node at its completion: a node that breaks a relation (scope, cast, priority or
    /// associativity) at one of its edges denotes nothing there, so it is dropped before any
    /// caller packs it. A rewrite, sequence or `#let` below an operator is such a violation like
    /// any other: the reading that holds it is not a term the rule could mean. The filter only
    /// excludes; the choice among the readings that survive it is made per tree, on the readings
    /// of the whole input ([`Self::prefer_structural_readings`]).
    pub(super) fn filter_completed_packed_priority(
        &self,
        term: Rc<PackedTerm>,
        memos: &RefCell<PackedPriorityMemos>,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let mut memos = memos.borrow_mut();
        let PackedPriorityMemos { nodes, children } = &mut *memos;
        self.filter_packed_priority_memo(term, nodes, children)
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
    pub(super) fn filter_completed_packed_priority_fresh(
        &self,
        term: Rc<PackedTerm>,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        self.filter_completed_packed_priority(term, &RefCell::new(PackedPriorityMemos::default()))
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
                        let mut retained = BTreeSet::new();
                        let mut errors = Vec::new();
                        for alternative in original_alternatives.iter().cloned() {
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
                        let child_count = children.len();
                        let results = children
                            .iter()
                            .enumerate()
                            .map(|(index, child)| {
                                self.filter_packed_priority_child(
                                    *production,
                                    Rc::clone(child),
                                    descriptor.shape().judged_side(index + 1, child_count),
                                    memo,
                                    child_memo,
                                )
                            })
                            .collect::<Vec<_>>();
                        // Every child is judged, so that a node failing at several children
                        // reports a scope error when one of them has it (`canonical_packed_error`).
                        let filtered_children = match results
                            .iter()
                            .filter_map(|result| result.as_ref().err())
                            .reduce(|first, error| {
                                if !first.is_scope() && error.is_scope() {
                                    error
                                } else {
                                    first
                                }
                            }) {
                            Some(error) => return Err(error.clone()),
                            None => results
                                .into_iter()
                                .collect::<Result<Vec<_>, _>>()
                                .expect("no child failed"),
                        };
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

    /// Among the readings of a forest, keep at every position those whose subtree there is
    /// rooted at a rewrite, else at a sequence, else at a `#let`, else every one.
    ///
    /// In a rule body these three constructs are the rule's own structure, not operators of the
    /// user's language: a subtree rooted at `=>` says that this part of the body is the rewrite
    /// its `=>` spells. When user syntax reuses one of their tokens (a match arm `A "=>" A`), a
    /// part of the body also has a reading through that syntax, and the rule's own construct is
    /// what the rule means there, at the body's root as in a cell, an argument or a bracket.
    ///
    /// The choice is defined on trees. A position of a tree is a node occurrence in it, standing
    /// at a child slot of its parent's production; the rank of the subtree there is read at its
    /// root seen through pass-through productions (as [`Self::packed_top_parse_label`] reads it):
    /// rewrite, sequence, `#let`, anything else, where a construct that cannot stand for a term
    /// of a sort below the one its place declares ranks as anything else ([`Self::may_stand`]):
    /// a sequence, of sort `K`, is no `KItem` argument, and a rewrite of a `Pat` to an `Exp` is
    /// no `Arm`, so neither is what the rule means there. A rewrite's own sort is chosen by
    /// inference, at most its place's, so its sides stand at that place. A tree is kept when, at
    /// each of its positions, its subtree has the least rank among the trees that agree with it
    /// everywhere outside that position. A position that some readings do not have is compared only among those that
    /// have it; there is one condition per position and no order between them, so choosing
    /// top-down, bottom-up or in any order keeps the same trees, and since every comparison
    /// includes the tree itself, the choice never leaves a forest empty.
    ///
    /// It needs no list of the places a construct may stand: a reading that puts one where the
    /// scope relation gives it no meaning denotes nothing and is gone before this runs, so the
    /// condition only chooses where the remaining readings offer the construct. The comparisons
    /// are of readings that each break no relation, so it runs after every relation and every
    /// application has been judged ([`Grammar::prepare_packed_forest`]).
    ///
    /// In the forest, the trees that agree outside a production node's child slot are the trees
    /// of that slot's child node, together with those of the same slot of every other
    /// alternative that applies the same production over the same split
    /// ([`Self::alternatives_at_one_position`]). So the choice restricts each child node to its
    /// alternatives of least rank (through pass-throughs) and recurses into the kept ones, once
    /// per node and place however many parents share them; it does not depend on where trees
    /// share subterms, on how alternatives of one node are packed, or on which sorts readings
    /// pass through.
    pub(super) fn prefer_structural_readings(&self, forest: Rc<PackedTerm>) -> Rc<PackedTerm> {
        self.prefer_structural_readings_memo(&forest, None, &mut HashMap::new())
    }

    /// The readings of `term`, every reading of a position at `place` (`None` at the parse's
    /// root), that [`Self::prefer_structural_readings`] keeps.
    fn prefer_structural_readings_memo(
        &self,
        term: &Rc<PackedTerm>,
        place: Option<StructuralPlace<'_>>,
        memo: &mut PreferenceMemo,
    ) -> Rc<PackedTerm> {
        crate::stack::guarded(|| {
            // Invariant: an entry maps a node, kept alive beside it, at a place of one declared
            // and one recognized sort to its kept readings.
            let key = (
                Rc::as_ptr(term),
                place.map(|place| (place.declared.clone(), place.recognized.clone())),
            );
            if let Some((_, preferred)) = memo.get(&key) {
                return Rc::clone(preferred);
            }
            let restricted = [
                InternalLabel::KRewrite,
                InternalLabel::KSequence,
                InternalLabel::Let,
            ]
            .into_iter()
            .find_map(|label| self.restrict_root_label(term, label.as_str(), place))
            .unwrap_or_else(|| Rc::clone(term));
            let preferred = self.prefer_structural_readings_below(&restricted, place, memo);
            memo.insert(key, (Rc::clone(term), Rc::clone(&preferred)));
            preferred
        })
    }

    /// The readings of `term` whose root has been chosen, with the choice made at every child
    /// slot below it ([`Self::prefer_structural_readings`]).
    fn prefer_structural_readings_below(
        &self,
        term: &Rc<PackedTerm>,
        place: Option<StructuralPlace<'_>>,
        memo: &mut PreferenceMemo,
    ) -> Rc<PackedTerm> {
        match &term.node {
            PackedNode::Ambiguity(alternatives) => {
                let mut retained = BTreeSet::new();
                let mut changed = false;
                for group in self.alternatives_at_one_position(alternatives) {
                    let kept = match group.as_slice() {
                        [alternative] => {
                            vec![self.prefer_structural_readings_below(alternative, place, memo)]
                        }
                        _ => {
                            let merged = merge_alternatives_at_one_position(&group);
                            let kept = self.prefer_structural_readings_below(&merged, place, memo);
                            if Rc::ptr_eq(&kept, &merged) {
                                group
                                    .iter()
                                    .map(|alternative| Rc::clone(alternative))
                                    .collect()
                            } else {
                                vec![kept]
                            }
                        }
                    };
                    changed |= kept.len() != group.len()
                        || kept
                            .iter()
                            .zip(&group)
                            .any(|(kept, alternative)| !Rc::ptr_eq(kept, alternative));
                    for kept in kept {
                        match &kept.node {
                            PackedNode::Ambiguity(nested) => {
                                retained.extend(nested.iter().cloned())
                            }
                            _ => {
                                retained.insert(kept);
                            }
                        }
                    }
                }
                if changed {
                    PackedTerm::ambiguity(retained)
                } else {
                    Rc::clone(term)
                }
            }
            PackedNode::Production {
                production,
                children,
                metadata,
            } => {
                let places = self.structural_places(*production, place);
                let preferred = children
                    .iter()
                    .enumerate()
                    .map(|(index, child)| {
                        self.prefer_structural_readings_memo(
                            child,
                            places.get(index).copied().flatten(),
                            memo,
                        )
                    })
                    .collect::<Vec<_>>();
                if preferred
                    .iter()
                    .zip(children)
                    .all(|(preferred, child)| Rc::ptr_eq(preferred, child))
                {
                    Rc::clone(term)
                } else {
                    PackedTerm::production(*production, preferred, metadata.clone())
                }
            }
            PackedNode::Term(_) | PackedNode::InstantiatedProduction { .. } => Rc::clone(term),
        }
    }

    /// The alternatives of an ambiguity grouped by the node they are at their root: one group per
    /// production applied over the same children's spans with the same metadata, and every other
    /// alternative alone ([`Self::prefer_structural_readings`]). A group's alternatives are trees
    /// of one production over one split of the text that the forest packs apart, each over part
    /// of a child's readings (`f(a => a)` can arrive as `f(rewrite | arrow)`, `f(rewrite)` and
    /// `f(arrow)`). The exclusions judge each edge by itself, so a child that may stand at a
    /// slot of the production may stand there beside any children of the other slots: every
    /// combination of the group's children is a reading, and each child slot of the group is
    /// one position whose readings are the union of the group's children there.
    fn alternatives_at_one_position<'a>(
        &self,
        alternatives: &'a BTreeSet<Rc<PackedTerm>>,
    ) -> Vec<Vec<&'a Rc<PackedTerm>>> {
        let mut groups: Vec<Vec<&'a Rc<PackedTerm>>> = Vec::new();
        let mut keys: Vec<Option<PositionKey<'a>>> = Vec::new();
        for alternative in alternatives {
            let key = position_key(alternative);
            match key
                .as_ref()
                .and_then(|key| keys.iter().position(|other| other.as_ref() == Some(key)))
            {
                Some(index) => groups[index].push(alternative),
                None => {
                    groups.push(vec![alternative]);
                    keys.push(key);
                }
            }
        }
        groups
    }

    /// The trees of a packed node, standing at `place` (`None` at the parse's root), whose root,
    /// seen through pass-through productions as [`Self::packed_top_parse_label`] sees it, is
    /// labelled `label` by a production whose node may stand where it stands
    /// ([`Self::structural_reading_fits`]).
    fn restrict_root_label(
        &self,
        term: &Rc<PackedTerm>,
        label: &str,
        place: Option<StructuralPlace<'_>>,
    ) -> Option<Rc<PackedTerm>> {
        crate::stack::guarded(|| match &term.node {
            PackedNode::Ambiguity(alternatives) => {
                self.restrict_alternatives(term, alternatives, |alternative| {
                    self.restrict_root_label(alternative, label, place)
                })
            }
            PackedNode::Production {
                production,
                children,
                metadata,
            } => {
                let descriptor = &self.productions[*production];
                match descriptor.parse_label.as_deref() {
                    Some(own) => {
                        (own == label && self.may_stand(term, place)).then(|| Rc::clone(term))
                    }
                    None if descriptor.syntactic_subsort || children.len() == 1 => {
                        let inner = self
                            .structural_places(*production, place)
                            .first()
                            .copied()
                            .flatten();
                        let child = self.restrict_root_label(children.first()?, label, inner)?;
                        if Rc::ptr_eq(&child, &children[0]) {
                            Some(Rc::clone(term))
                        } else {
                            let mut children = children.clone();
                            children[0] = child;
                            Some(PackedTerm::production(
                                *production,
                                children,
                                metadata.clone(),
                            ))
                        }
                    }
                    None => None,
                }
            }
            PackedNode::Term(_) | PackedNode::InstantiatedProduction { .. } => None,
        })
    }

    /// Whether a node standing for a term of sort `sort` can be well sorted at `place`: where
    /// the sort is not below the one the place declares, no reading puts the node there with a
    /// meaning, and the choice does not prefer a construct there
    /// ([`Self::prefer_structural_readings`]). A node of the scaffolding sort a widened place is
    /// recognized at stands for a term of the sort the place declares
    /// (`Grammar::admit_rewrites_in_argument_positions`): in the portable build a rewrite at a
    /// `KItem` argument is a node of `#RuleKItem`, a rewrite of sort `KItem`. A place of no sort
    /// (the parse's root) or of a sort outside the subsort order (a sort parameter) admits it.
    fn structural_reading_fits(&self, sort: &Sort, place: Option<StructuralPlace<'_>>) -> bool {
        let Some(place) = place else {
            return true;
        };
        if sort == place.recognized {
            return true;
        }
        let Ok(order) = self.subsort_relations.order() else {
            return true;
        };
        !order.contains(place.declared) || order.less_than_eq(sort, place.declared)
    }

    /// Whether some reading of `term` can be well sorted at `place` as far as the sorts written in
    /// it say: a node of a production stands for a term of the production's sort
    /// ([`Self::structural_reading_fits`]); a node of a parametric production whose sort is its
    /// result parameter (a rewrite, `#as`, `#let`) for a term of a sort that is at most the
    /// place's and at least each operand's at that parameter, so it can stand there exactly when
    /// each of those operands can; a pass-through for its child's term or one of its own sort; a
    /// token for a term of its sort; a variable for a term of any sort. A reading this rejects
    /// is rejected by inference too, so the choice does not prefer a construct where no term puts
    /// it ([`Self::prefer_structural_readings`]). It reads only the sorts written in the reading,
    /// not a variable's sort from its other occurrences, which only inference relates.
    fn may_stand(&self, term: &Rc<PackedTerm>, place: Option<StructuralPlace<'_>>) -> bool {
        if place.is_none() {
            return true;
        }
        match &term.node {
            PackedNode::Ambiguity(alternatives) => alternatives
                .iter()
                .any(|alternative| self.may_stand(alternative, place)),
            PackedNode::Production {
                production,
                children,
                ..
            } => {
                let descriptor = &self.productions[*production];
                if let Some(origin) = &descriptor.parametric_origin
                    && origin.result_is_parameter()
                {
                    return origin
                        .nonterminal_sorts()
                        .zip(children)
                        .filter(|(sort, _)| **sort == origin.result)
                        .all(|(_, child)| self.may_stand(child, place));
                }
                self.structural_reading_fits(&descriptor.result, place)
                    || ((descriptor.parse_label.is_none() || descriptor.syntactic_subsort)
                        && children.len() == 1
                        && self.may_stand(&children[0], place))
            }
            PackedNode::Term(term) => match term.unannotated() {
                Term::Token { sort, .. } => self.structural_reading_fits(sort, place),
                _ => true,
            },
            PackedNode::InstantiatedProduction { .. } => true,
        }
    }

    /// The place of each nonterminal child slot of `production`, in order, for a node standing
    /// at `own` (`None`: a place that admits every construct). An operand declared at the
    /// parametric production's result parameter stands at the node's own place, since the
    /// parameter is at most that place's sort; an operand of another parameter admits every
    /// construct; every other operand's place is the one the production declares there.
    fn structural_places<'a>(
        &'a self,
        production: usize,
        own: Option<StructuralPlace<'a>>,
    ) -> Vec<Option<StructuralPlace<'a>>> {
        let descriptor = &self.productions[production];
        let origin_sorts = descriptor
            .parametric_origin
            .as_ref()
            .map(|origin| (origin, origin.nonterminal_sorts().collect::<Vec<_>>()));
        descriptor
            .items
            .iter()
            .zip(&descriptor.item_sort_ids)
            .filter_map(|(item, sort_id)| match item {
                Item::NonTerminal(declared) => Some((declared, sort_id)),
                _ => None,
            })
            .enumerate()
            .map(|(slot, (declared, sort_id))| {
                if let Some((origin, sorts)) = &origin_sorts
                    && let Some(sort) = sorts.get(slot)
                {
                    if origin.result_is_parameter() && **sort == origin.result {
                        return own;
                    }
                    if mentions_parameter(sort, &origin.parameters) {
                        return None;
                    }
                }
                Some(StructuralPlace {
                    declared,
                    recognized: sort_id.map_or(declared, |id| &self.sorts[id]),
                })
            })
            .collect()
    }

    /// The alternatives of an ambiguity that `restrict` keeps, the ambiguity itself when it keeps
    /// every one unchanged, or `None` when it keeps none.
    fn restrict_alternatives(
        &self,
        term: &Rc<PackedTerm>,
        alternatives: &BTreeSet<Rc<PackedTerm>>,
        mut restrict: impl FnMut(&Rc<PackedTerm>) -> Option<Rc<PackedTerm>>,
    ) -> Option<Rc<PackedTerm>> {
        let mut retained = BTreeSet::new();
        for alternative in alternatives {
            if let Some(kept) = restrict(alternative) {
                match &kept.node {
                    PackedNode::Ambiguity(nested) => retained.extend(nested.iter().cloned()),
                    _ => {
                        retained.insert(kept);
                    }
                }
            }
        }
        if retained.is_empty() {
            None
        } else if packed_sets_share_nodes(&retained, alternatives) {
            Some(Rc::clone(term))
        } else {
            Some(PackedTerm::ambiguity(retained))
        }
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
                // A scope error below the edge is reported before another violation at it.
                if !error.is_scope()
                    && let Err(below) = self.filter_packed_priority_memo(child, memo, child_memo)
                    && below.is_scope()
                {
                    return Err(below);
                }
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
        crate::stack::guarded(|| match term.into_parts() {
            ParsedParts::Term(leaf) => Ok(ParsedTerm::Term(leaf)),
            ParsedParts::Ambiguity(alternatives) => {
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
                let child_count = children.len();
                let children = children
                    .into_iter()
                    .enumerate()
                    .map(|(index, child)| {
                        let side = descriptor.shape().judged_side(index + 1, child_count);
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
    /// [`Self::filter_packed_priority_memo`] makes at that edge
    /// ([`NodeShape::judged_side`]) finds a scope, cast, priority or associativity violation,
    /// so no reading the filter accepts has that edge. Both productions are those of the nodes.
    /// A production that passes its child through (`build_packed_term`) builds no node, so the
    /// node at the edge is one this question does not know, and a token production builds a
    /// leaf, which no relation judges: for either the answer is `false`. A record production's
    /// edges are checked only after its node is collapsed into another production's, so for
    /// one the answer is `false` too.
    pub(super) fn edge_rejects(&self, parent: usize, child: usize, position: usize) -> bool {
        let child = self.productions[child].shape();
        if !child.judged_as_child() {
            return false;
        }
        let parent = self.productions[parent].shape();
        parent
            .judged_side(position, parent.nonterminals)
            .is_some_and(|side| {
                self.relation_index()
                    .exclusions
                    .violation(&parent, &child, side)
                    .is_some()
            })
    }

    /// The violation the relations find at the edge between a node of `parent` and `child` on
    /// `side` ([`Exclusions::violation`](super::exclusion::Exclusions::violation)), named by
    /// the two nodes' labels. A leaf is in no relation.
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
        let exclusion =
            self.relation_index()
                .exclusions
                .violation(&parent.shape(), &child.shape(), side)?;
        let parent = parent.parse_label.clone()?;
        let child = child.parse_label.clone()?;
        Some(match exclusion {
            Exclusion::Scope => ParseError::Scope { parent, child },
            Exclusion::CastPriority => ParseError::CastPriority {
                cast: parent,
                child,
            },
            Exclusion::Priority => ParseError::Priority { parent, child },
            Exclusion::Associativity(side) => ParseError::Associativity {
                parent,
                child,
                side: if side == Side::Left { "left" } else { "right" },
            },
        })
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
            readings @ Readings::Several(_) => Err(self.ambiguity_report(readings, &mut sets)?),
        }
    }

    /// The readings of one node of an inferred tree: its one term, or a node of `sets` that
    /// stands for several without listing them.
    ///
    /// A production node over children of one reading each is lowered as it stands. Over a
    /// child of several readings, its readings are the lowerings of every combination of its
    /// children's readings, kept as an expression over the children's sets:
    /// - where `lower_term` builds the node from its children unchanged, a product
    ///   (`Grammar::product_readings`); distinct combinations are distinct terms;
    /// - a `~>` node, the concatenation of its children's readings read as words of items
    ///   (`SetNode::Concat`), or, when no child may be a sequence, the product of its items,
    ///   since `Term::sequence` then splices nothing (`ReadingSets::sequence_items`);
    /// - a `#KToken` node over two strings, which joins their text: one term per pair of the
    ///   string tokens its children may be, and products for the rest (`Grammar::token_readings`);
    /// - a node that denotes its first child (a bracket, an unlabelled single child), that
    ///   child's readings.
    ///
    /// An ambiguity node's readings are the union of its alternatives'. No set is ever split
    /// into its terms, and none is made disjoint from another: every question the report asks
    /// distributes over these expressions (`ReadingSets`).
    ///
    /// ```toml algorithm-site
    /// id = "parser.diagnostic.ambiguity"
    /// role = "part"
    /// sites = ["Grammar::resolve_ambiguities_node", "Grammar::ambiguity_report", "Grammar::collect_places", "Grammar::least_reading"]
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
                let mut readings = Vec::with_capacity(alternatives.len());
                for alternative in alternatives {
                    readings.push(self.resolve_ambiguities_node(alternative, sets)?);
                }
                Ok(sets.union(readings))
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
            // Children whose readings are one word each make one sequence, whichever reading
            // of each is spliced.
            if let Some(words) = children
                .iter()
                .map(|child| sets.one_word(child))
                .collect::<Option<Vec<_>>>()
            {
                return self
                    .lower_production(production, parameters.as_deref(), words, metadata)
                    .map(Readings::One);
            }
            if let Some(items) = sets.sequence_items(&children) {
                return self.product_readings(production, parameters, metadata, items, sets);
            }
            return Ok(sets.cons_concat(production, parameters, metadata, children));
        }
        if label.is_some_and(|label| label.is(InternalLabel::KToken)) && children.len() == 2 {
            return self.token_readings(production, parameters, metadata, children, sets);
        }
        self.product_readings(production, parameters, metadata, children, sets)
    }

    /// The readings of `production` over `children` when `lower_term` builds its node from its
    /// children unchanged: the one lowered term when every child has one reading, otherwise
    /// the product of the children's readings, of which there are then several.
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
                    Readings::Several(_) => unreachable!("every child has one reading"),
                })
                .collect();
            return self
                .lower_production(production, parameters.as_deref(), children, metadata)
                .map(Readings::One);
        }
        // One node over one structure is one product, so a subtree the forest shared, which
        // unpacking copied, is one node, and every question about it is answered once.
        let hash = sets.structure_hash(
            NodeTag::Product,
            Some((production, parameters.as_deref(), &metadata)),
            &children,
        );
        if let Some(index) =
            sets.consed_product(hash, production, &parameters, &metadata, &children)
        {
            return Ok(Readings::Several(index));
        }
        let shape = self.lower_production(
            production,
            parameters.as_deref(),
            vec![hole(); children.len()],
            crate::kast::TermMetadata::default(),
        )?;
        Ok(sets.push(
            hash,
            SetNode::Product {
                production,
                parameters,
                metadata,
                children,
                key: Key::of(&shape),
            },
        ))
    }

    /// The readings of a `#KToken` node over `value` and `sort` (`children`), of which one has
    /// several readings.
    ///
    /// `lower_term` joins two string tokens into the token they spell, and builds the node
    /// from its children unchanged otherwise. So the readings are those of every pair of the
    /// string tokens the children may be, each lowered, and the products over the rest: the
    /// values that are not string tokens with every sort, and the string-token values with
    /// the sorts that are not. Only the string tokens are paired, which are leaves of the
    /// tree.
    fn token_readings(
        &self,
        production: usize,
        parameters: Option<Vec<Sort>>,
        metadata: crate::kast::TermMetadata,
        children: Vec<Readings>,
        sets: &mut ReadingSets,
    ) -> Result<Readings, ParseError> {
        let [value, sort] = <[Readings; 2]>::try_from(children)
            .unwrap_or_else(|_| unreachable!("a #KToken node of two children"));
        let (value_tokens, value_rest) = sets.split_string_tokens(&value);
        let (sort_tokens, sort_rest) = sets.split_string_tokens(&sort);
        let mut readings = Vec::new();
        for value in &value_tokens {
            for sort in &sort_tokens {
                readings.push(Readings::One(self.lower_production(
                    production,
                    parameters.as_deref(),
                    vec![value.clone(), sort.clone()],
                    metadata.clone(),
                )?));
            }
        }
        if let Some(rest) = value_rest {
            readings.push(self.product_readings(
                production,
                parameters.clone(),
                metadata.clone(),
                vec![rest, sort],
                sets,
            )?);
        }
        if let Some(rest) = sort_rest
            && !value_tokens.is_empty()
        {
            let values = sets.union(value_tokens.into_iter().map(Readings::One));
            readings.push(self.product_readings(
                production,
                parameters,
                metadata,
                vec![values, rest],
                sets,
            )?);
        }
        Ok(sets.union(readings))
    }

    /// The diagnostic of a tree with several readings.
    ///
    /// The report is the smallest subterm outside which every reading agrees, found by
    /// descending from the root while the readings have one root key (head and arity) and
    /// exactly one child position at which they have several subterms. There the readings
    /// either have several root keys, and are listed one entry per key
    /// (`Grammar::reading_entries`), or differ at several positions, each of which is
    /// reported (`Grammar::collect_places`).
    ///
    /// Each step asks the expression of `readings` for its root keys and for the subterms at
    /// one position of its readings of one key, which distribute over products, unions and
    /// concatenations without listing a reading (`ReadingSets`); the number of readings is
    /// not computed, and neither is whether the places vary independently, since both are
    /// hard for some forests (`docs/compatibility.md`).
    fn ambiguity_report(
        &self,
        mut readings: Readings,
        sets: &mut ReadingSets,
    ) -> Result<ParseError, ParseError> {
        loop {
            let keys = sets.keys(&readings);
            if let [key] = &keys[..] {
                let mut varying = sets.varying_subterms(&readings, key);
                if varying.len() == 1 {
                    readings = varying.pop().expect("one position");
                    continue;
                }
                let mut places = Vec::new();
                for subterms in varying {
                    self.collect_places(subterms, sets, &mut places)?;
                }
                return Ok(ParseError::Ambiguous {
                    alternatives: Vec::new(),
                    span: sets.span(&readings),
                    places,
                });
            }
            return Ok(ParseError::Ambiguous {
                alternatives: self.reading_entries(&readings, &keys, sets)?,
                span: sets.span(&readings),
                places: Vec::new(),
            });
        }
    }

    /// Add to `places` the subterms of `readings`, a set of several readings at a position of
    /// the reported subterm, at which they differ: `readings` itself when its readings have
    /// several root keys, and otherwise those of each position at which its readings have
    /// several subterms.
    fn collect_places(
        &self,
        readings: Readings,
        sets: &mut ReadingSets,
        places: &mut Vec<AmbiguityPlace>,
    ) -> Result<(), ParseError> {
        crate::stack::guarded(|| {
            let keys = sets.keys(&readings);
            if let [key] = &keys[..] {
                for subterms in sets.varying_subterms(&readings, key) {
                    self.collect_places(subterms, sets, places)?;
                }
                return Ok(());
            }
            places.push(AmbiguityPlace {
                span: sets.span(&readings),
                location: None,
                alternatives: self.reading_entries(&readings, &keys, sets)?,
            });
            Ok(())
        })
    }

    /// One entry per root key of `readings` (`keys`): the least of its readings with that key
    /// in term order, and whether it has others, in the order of those least readings.
    fn reading_entries(
        &self,
        readings: &Readings,
        keys: &[Key],
        sets: &mut ReadingSets,
    ) -> Result<Vec<AmbiguousParse>, ParseError> {
        let mut entries = Vec::with_capacity(keys.len());
        for key in keys {
            let least = self.least_reading(readings, key, sets)?;
            let several = (0..key.arity()).any(|position| {
                matches!(sets.subterms(readings, key, position), Readings::Several(_))
            });
            entries.push((least, several));
        }
        entries.sort_by(|(left, _), (right, _)| left.cmp(right));
        Ok(entries
            .into_iter()
            .map(|(term, several)| AmbiguousParse {
                production: self.reading_production_text(&term),
                term: term.to_string(),
                more_with_same_root: several,
            })
            .collect())
    }

    /// The least reading of `readings` with root key `key` in term order
    /// (`ReadingSets::keyed_least`), the one term built for it.
    fn least_reading(
        &self,
        readings: &Readings,
        key: &Key,
        sets: &ReadingSets,
    ) -> Result<Term, ParseError> {
        let text = |production| {
            self.source_production_texts
                .get(&production)
                .map(|text| text.as_str())
        };
        self.build_least(sets.keyed_least(readings, key, &text), sets)
    }

    /// The term a least view stands for (`ReadingSets::resolve`), built from its root down:
    /// one lowering per node of the term.
    fn build_least(&self, view: LeastView<'_>, sets: &ReadingSets) -> Result<Term, ParseError> {
        crate::stack::guarded(|| match sets.resolve(view) {
            LeastView::Term(term) => Ok(term.clone()),
            LeastView::Node(index) => {
                let SetNode::Product {
                    production,
                    parameters,
                    metadata,
                    children,
                    ..
                } = &sets.nodes[index]
                else {
                    unreachable!("a resolved node is a product")
                };
                let mut arguments = Vec::with_capacity(children.len());
                for child in children {
                    arguments.push(self.build_least(sets.view(child), sets)?);
                }
                self.lower_production(
                    *production,
                    parameters.as_deref(),
                    arguments,
                    metadata.clone(),
                )
            }
            LeastView::Word(index, length) => {
                let SetNode::Concat {
                    production,
                    parameters,
                    metadata,
                    ..
                } = &sets.nodes[index]
                else {
                    unreachable!("a word is one of a concatenation")
                };
                let word = sets.least_word(&Readings::Several(index), length);
                let mut items = Vec::with_capacity(word.len());
                for item in word.iter() {
                    items.push(self.build_least(sets.view(item), sets)?);
                }
                self.lower_production(*production, parameters.as_deref(), items, metadata.clone())
            }
        })
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
    /// A node of `ReadingSets::nodes`, which has at least two readings.
    Several(usize),
}

/// An expression for a set of at least two readings over the readings of its children.
enum SetNode {
    /// The terms `lower_term` builds from `production` over every combination of one reading of
    /// each child, from the children unchanged, so that distinct combinations are distinct
    /// terms; at least one child has several readings. Every term has the root key `key`. A
    /// `~>` product's children are its items, none of which may be a sequence.
    Product {
        production: usize,
        parameters: Option<Vec<Sort>>,
        metadata: crate::kast::TermMetadata,
        children: Vec<Readings>,
        key: Key,
    },
    /// The sequences a `~>` node lowers to over every combination of one reading of each
    /// child: the concatenations of the children's words, a word being the items of a
    /// sequence or the one item of any other term (`word_items`). Some child has several words;
    /// with the other children's words fixed, distinct words of that child make distinct
    /// concatenations (a free monoid cancels), so the node has several readings.
    Concat {
        production: usize,
        parameters: Option<Vec<Sort>>,
        metadata: crate::kast::TermMetadata,
        children: Rc<[Readings]>,
    },
    /// The union of at least two alternatives: pairwise distinct terms, and nodes other than
    /// unions, so it has several readings.
    Union(Rc<[Readings]>),
}

#[derive(Clone, Copy)]
enum NodeTag {
    Product,
    Concat,
    Union,
}

/// The lengths of the words of the children before and after each child of a concatenation
/// (`ReadingSets::concat_bounds`).
struct ConcatBounds {
    /// `prefixes[t]`: the lengths of the words of the first `t` children.
    prefixes: Vec<BTreeSet<usize>>,
    /// `suffixes[t]`: the lengths of the words of the children from the `t`-th on.
    suffixes: Vec<BTreeSet<usize>>,
}

/// The nodes of one tree's readings, one per structure, and the answers to the questions the
/// report asks of them, each computed once per node (and length, position or key).
///
/// Every question distributes over the expressions: the root keys of a product are its own,
/// of a union its alternatives', and of a concatenation the sequences of each length its
/// children's lengths sum to; the subterms at a position of the readings of one key are a
/// product's child, the union of the alternatives' that have the key, or the items at that
/// index of a concatenation's words of that length (`ReadingSets::item`). No question lists
/// the readings of a node.
#[derive(Default)]
struct ReadingSets {
    nodes: Vec<SetNode>,
    /// The hash of each node's structure (`ReadingSets::structure_hash`; a union's is that of
    /// its alternatives, `ReadingSets::union`).
    hashes: Vec<u64>,
    /// The nodes by the hash of their structure.
    consed: HashMap<u64, Vec<usize>>,
    keys: RefCell<HashMap<usize, Rc<[Key]>>>,
    lengths: RefCell<HashMap<usize, Rc<[usize]>>>,
    bounds: RefCell<HashMap<usize, Rc<ConcatBounds>>>,
    subterms: BTreeMap<(usize, usize, Key), Readings>,
    items: HashMap<(usize, usize, usize), Readings>,
    /// The alternative of each union with the least reading (`ReadingSets::resolve`).
    least_alternatives: RefCell<HashMap<usize, usize>>,
    /// The length of the least reading of each concatenation.
    least_lengths: RefCell<HashMap<usize, usize>>,
    least_words: RefCell<HashMap<(usize, usize), Word>>,
    /// The order of the least readings of pairs of nodes compared.
    comparisons: RefCell<HashMap<(usize, usize), std::cmp::Ordering>>,
}

/// A word of a `~>` node's readings: its items, each standing for the least reading of its
/// set (`ReadingSets::least_word`).
type Word = Rc<[Rc<Readings>]>;

/// The least term of a set of readings, standing for it without building it
/// (`ReadingSets::compare`, `Grammar::build_least`).
#[derive(Clone, Copy)]
enum LeastView<'a> {
    Term(&'a Term),
    /// The least of every reading of a node.
    Node(usize),
    /// The least sequence of a length (the second field) a concatenation has.
    Word(usize, usize),
}

impl ReadingSets {
    /// Add `node`, of structure hash `hash`, which no node has.
    fn push(&mut self, hash: u64, node: SetNode) -> Readings {
        #[cfg(test)]
        tests::SET_NODES.with(|count| count.set(count.get() + 1));
        self.nodes.push(node);
        self.hashes.push(hash);
        let index = self.nodes.len() - 1;
        self.consed.entry(hash).or_default().push(index);
        Readings::Several(index)
    }

    /// The product of this structure, when there is one.
    fn consed_product(
        &self,
        hash: u64,
        production: usize,
        parameters: &Option<Vec<Sort>>,
        metadata: &crate::kast::TermMetadata,
        children: &[Readings],
    ) -> Option<usize> {
        self.consed.get(&hash)?.iter().copied().find(|index| {
            matches!(
                &self.nodes[*index],
                SetNode::Product {
                    production: own_production,
                    parameters: own_parameters,
                    metadata: own_metadata,
                    children: own_children,
                    ..
                } if *own_production == production
                    && own_parameters == parameters
                    && own_metadata == metadata
                    && identical_children(own_children, children)
            )
        })
    }

    /// The concatenation of this structure, added when there is none.
    fn cons_concat(
        &mut self,
        production: usize,
        parameters: Option<Vec<Sort>>,
        metadata: crate::kast::TermMetadata,
        children: Vec<Readings>,
    ) -> Readings {
        let hash = self.structure_hash(
            NodeTag::Concat,
            Some((production, parameters.as_deref(), &metadata)),
            &children,
        );
        let found = self.consed.get(&hash).and_then(|candidates| {
            candidates.iter().copied().find(|index| {
                matches!(
                    &self.nodes[*index],
                    SetNode::Concat {
                        production: own_production,
                        parameters: own_parameters,
                        metadata: own_metadata,
                        children: own_children,
                    } if *own_production == production
                        && *own_parameters == parameters
                        && *own_metadata == metadata
                        && identical_children(own_children, &children)
                )
            })
        });
        match found {
            Some(index) => Readings::Several(index),
            None => self.push(
                hash,
                SetNode::Concat {
                    production,
                    parameters,
                    metadata,
                    children: children.into(),
                },
            ),
        }
    }

    /// The hash of a node's structure: its kind, production, parameters and span, and its
    /// children's structures. Terms hash without their metadata, as they compare.
    fn structure_hash(
        &self,
        tag: NodeTag,
        production: Option<(usize, Option<&[Sort]>, &crate::kast::TermMetadata)>,
        children: &[Readings],
    ) -> u64 {
        let mut state = FxHasher::default();
        state.write_u8(tag as u8);
        if let Some((production, parameters, metadata)) = production {
            production.hash(&mut state);
            if let Some(parameters) = parameters {
                parameters
                    .iter()
                    .for_each(|parameter| hash_sort(parameter, &mut state));
            }
            metadata.span.hash(&mut state);
        }
        state.write_usize(children.len());
        for child in children {
            state.write_u64(self.readings_hash(child));
        }
        state.finish()
    }

    fn readings_hash(&self, readings: &Readings) -> u64 {
        match readings {
            Readings::One(term) => term_hash(term),
            Readings::Several(index) => self.hashes[*index],
        }
    }

    /// The union of `alternatives`: one of them when their readings are one term.
    fn union(&mut self, alternatives: impl IntoIterator<Item = Readings>) -> Readings {
        let mut flat = Vec::new();
        let mut hashes = Vec::new();
        let mut nodes = HashSet::new();
        let mut terms = HashMap::<u64, Vec<usize>>::new();
        let mut add = |reading: Readings, flat: &mut Vec<Readings>, hashes: &mut Vec<u64>| {
            match &reading {
                Readings::One(term) => {
                    let hash = term_hash(term);
                    let same = terms.entry(hash).or_default();
                    if let Some(kept) = same.iter().copied().find(|index| match &flat[*index] {
                        Readings::One(other) => other == term,
                        Readings::Several(_) => false,
                    }) {
                        if let Readings::One(kept) = &mut flat[kept] {
                            widen_spans(kept, term);
                        }
                        return;
                    }
                    same.push(flat.len());
                    hashes.push(hash);
                }
                Readings::Several(index) => {
                    if !nodes.insert(*index) {
                        return;
                    }
                    hashes.push(self.hashes[*index]);
                }
            }
            flat.push(reading);
        };
        for alternative in alternatives {
            if let Readings::Several(index) = alternative
                && let SetNode::Union(inner) = &self.nodes[index]
            {
                for reading in inner.iter() {
                    add(reading.clone(), &mut flat, &mut hashes);
                }
            } else {
                add(alternative, &mut flat, &mut hashes);
            }
        }
        if flat.len() == 1 {
            return flat.pop().expect("one alternative");
        }
        let mut state = FxHasher::default();
        state.write_u8(NodeTag::Union as u8);
        state.write_usize(hashes.len());
        for hash in &hashes {
            state.write_u64(*hash);
        }
        let hash = state.finish();
        let found = self.consed.get(&hash).and_then(|candidates| {
            candidates.iter().copied().find(|index| {
                matches!(&self.nodes[*index], SetNode::Union(own) if identical_children(own, &flat))
            })
        });
        match found {
            Some(index) => Readings::Several(index),
            None => self.push(hash, SetNode::Union(flat.into())),
        }
    }

    /// One term of `readings` when its readings are one word, so that every reading of it
    /// splices into a sequence alike.
    fn one_word(&self, readings: &Readings) -> Option<Term> {
        let index = match readings {
            Readings::One(term) => return Some(term.clone()),
            Readings::Several(index) => *index,
        };
        let SetNode::Union(alternatives) = &self.nodes[index] else {
            return None;
        };
        let mut terms = alternatives.iter().map(|alternative| match alternative {
            Readings::One(term) => Some(term),
            Readings::Several(_) => None,
        });
        let first = terms.next()??;
        for term in terms {
            if word_items(term?) != word_items(first) {
                return None;
            }
        }
        Some(first.clone())
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
                Readings::Several(index) => match &self.nodes[*index] {
                    SetNode::Product {
                        key: Key::Sequence(_),
                        children,
                        ..
                    } => items.extend(children.iter().cloned()),
                    _ if self.may_be_sequence(child) => return None,
                    _ => items.push(child.clone()),
                },
            }
        }
        Some(items)
    }

    /// Whether some term of `readings` is a sequence.
    fn may_be_sequence(&self, readings: &Readings) -> bool {
        match readings {
            Readings::One(term) => matches!(term.unannotated(), Term::Sequence(_)),
            Readings::Several(index) => match &self.nodes[*index] {
                SetNode::Product { key, .. } => matches!(key, Key::Sequence(_)),
                SetNode::Concat { .. } => true,
                SetNode::Union(alternatives) => alternatives
                    .iter()
                    .any(|alternative| self.may_be_sequence(alternative)),
            },
        }
    }

    /// The string tokens among the readings of `readings`, and the set of its other
    /// readings, when it has others.
    fn split_string_tokens(&mut self, readings: &Readings) -> (Vec<Term>, Option<Readings>) {
        let alternatives = match readings {
            Readings::Several(index) => match &self.nodes[*index] {
                SetNode::Union(alternatives) => alternatives.to_vec(),
                SetNode::Product { .. } | SetNode::Concat { .. } => vec![readings.clone()],
            },
            Readings::One(_) => vec![readings.clone()],
        };
        let mut tokens = Vec::new();
        let mut rest = Vec::new();
        for alternative in alternatives {
            match alternative {
                Readings::One(term) if super::kstring_token(&term).is_some() => tokens.push(term),
                other => rest.push(other),
            }
        }
        let rest = (!rest.is_empty()).then(|| self.union(rest));
        (tokens, rest)
    }

    /// The children of the product or concatenation `index`.
    fn node_children(&self, index: usize) -> &[Readings] {
        match &self.nodes[index] {
            SetNode::Product { children, .. } => children,
            SetNode::Concat { children, .. } => children,
            SetNode::Union(_) => unreachable!("a union has alternatives"),
        }
    }

    /// The root keys of the readings of `readings`, in key order.
    fn keys(&self, readings: &Readings) -> Rc<[Key]> {
        crate::stack::guarded(|| {
            let index = match readings {
                Readings::One(term) => return Rc::from([Key::of(term)]),
                Readings::Several(index) => *index,
            };
            if let Some(keys) = self.keys.borrow().get(&index) {
                return Rc::clone(keys);
            }
            let keys: Rc<[Key]> = match &self.nodes[index] {
                SetNode::Product { key, .. } => Rc::from([key.clone()]),
                SetNode::Concat { .. } => self
                    .lengths(readings)
                    .iter()
                    .map(|length| Key::Sequence(*length))
                    .collect(),
                SetNode::Union(alternatives) => {
                    let mut keys = BTreeSet::new();
                    for alternative in alternatives.iter() {
                        keys.extend(self.keys(alternative).iter().cloned());
                    }
                    keys.into_iter().collect()
                }
            };
            self.keys.borrow_mut().insert(index, Rc::clone(&keys));
            keys
        })
    }

    /// The lengths of the words of `readings` (`word_items`), in increasing order.
    fn lengths(&self, readings: &Readings) -> Rc<[usize]> {
        crate::stack::guarded(|| {
            let index = match readings {
                Readings::One(term) => return Rc::from([word_items(term).len()]),
                Readings::Several(index) => *index,
            };
            if let Some(lengths) = self.lengths.borrow().get(&index) {
                return Rc::clone(lengths);
            }
            let lengths: Rc<[usize]> = match &self.nodes[index] {
                SetNode::Product { key, children, .. } => match key {
                    Key::Sequence(_) => Rc::from([children.len()]),
                    _ => Rc::from([1]),
                },
                SetNode::Concat { .. } => {
                    let bounds = self.concat_bounds(index);
                    bounds.prefixes[bounds.prefixes.len() - 1]
                        .iter()
                        .copied()
                        .collect()
                }
                SetNode::Union(alternatives) => {
                    let mut lengths = BTreeSet::new();
                    for alternative in alternatives.iter() {
                        lengths.extend(self.lengths(alternative).iter().copied());
                    }
                    lengths.into_iter().collect()
                }
            };
            self.lengths.borrow_mut().insert(index, Rc::clone(&lengths));
            lengths
        })
    }

    /// The lengths of the words of every prefix and every suffix of the children of the
    /// concatenation `index`: sums of one length of each child.
    fn concat_bounds(&self, index: usize) -> Rc<ConcatBounds> {
        if let Some(bounds) = self.bounds.borrow().get(&index) {
            return Rc::clone(bounds);
        }
        let lengths = self
            .node_children(index)
            .iter()
            .map(|child| self.lengths(child))
            .collect::<Vec<_>>();
        let sums = |sums: &BTreeSet<usize>, lengths: &[usize]| -> BTreeSet<usize> {
            sums.iter()
                .flat_map(|sum| lengths.iter().map(move |length| sum + length))
                .collect()
        };
        let mut prefixes = vec![BTreeSet::from([0])];
        for lengths in &lengths {
            let next = sums(prefixes.last().expect("a prefix"), lengths);
            prefixes.push(next);
        }
        let mut suffixes = vec![BTreeSet::from([0])];
        for lengths in lengths.iter().rev() {
            let next = sums(suffixes.last().expect("a suffix"), lengths);
            suffixes.push(next);
        }
        suffixes.reverse();
        let bounds = Rc::new(ConcatBounds { prefixes, suffixes });
        self.bounds.borrow_mut().insert(index, Rc::clone(&bounds));
        bounds
    }

    /// The least view of every reading of `readings`.
    fn view<'a>(&self, readings: &'a Readings) -> LeastView<'a> {
        match readings {
            Readings::One(term) => LeastView::Term(term),
            Readings::Several(index) => LeastView::Node(*index),
        }
    }

    /// The least reading of `readings` with root key `key`, which some of them have: a
    /// product's least, a concatenation's least word of the key's length, or the least of the
    /// alternatives' with that key.
    ///
    /// Alternatives whose least readings are one term built by different productions of one
    /// label (overloads) are ordered by the text of their root's production (`text`, `None`
    /// for a production without one first), so that the production an entry names
    /// (`Grammar::reading_entries`) is that of the least text, not of the alternative the
    /// forest happens to list first.
    fn keyed_least<'a, 't>(
        &'a self,
        readings: &'a Readings,
        key: &Key,
        text: &dyn Fn(ProductionIdentity) -> Option<&'t str>,
    ) -> LeastView<'a> {
        let index = match readings {
            Readings::One(term) => return LeastView::Term(term),
            Readings::Several(index) => *index,
        };
        match &self.nodes[index] {
            SetNode::Product { .. } => LeastView::Node(index),
            SetNode::Concat { .. } => {
                let Key::Sequence(length) = key else {
                    unreachable!("the readings of a concatenation are sequences")
                };
                LeastView::Word(index, *length)
            }
            SetNode::Union(alternatives) => alternatives
                .iter()
                .filter(|alternative| self.keys(alternative).contains(key))
                .map(|alternative| self.keyed_least(alternative, key, text))
                .reduce(|least, view| {
                    let root_text = |view| self.root_production(view).and_then(text);
                    if self
                        .compare(view, least)
                        .then_with(|| root_text(view).cmp(&root_text(least)))
                        .is_lt()
                    {
                        view
                    } else {
                        least
                    }
                })
                .expect("an alternative has the key"),
        }
    }

    /// The production a view's root comes from, as its metadata names it.
    fn root_production(&self, view: LeastView<'_>) -> Option<ProductionIdentity> {
        match self.resolve(view) {
            LeastView::Term(term) => term.metadata().and_then(|metadata| metadata.production),
            LeastView::Node(index) | LeastView::Word(index, _) => match &self.nodes[index] {
                SetNode::Product { metadata, .. } | SetNode::Concat { metadata, .. } => {
                    metadata.production
                }
                SetNode::Union(_) => None,
            },
        }
    }

    /// `view` with a union replaced by its least alternative and a concatenation by its least
    /// word, until it is a term, a product or a word.
    fn resolve<'a>(&'a self, mut view: LeastView<'a>) -> LeastView<'a> {
        loop {
            let LeastView::Node(index) = view else {
                return view;
            };
            match &self.nodes[index] {
                SetNode::Product { .. } => return view,
                SetNode::Concat { .. } => {
                    return LeastView::Word(index, self.least_length(index));
                }
                SetNode::Union(alternatives) => {
                    view = self.view(&alternatives[self.least_alternative(index)]);
                }
            }
        }
    }

    /// The alternative of the union `index` with the least reading.
    fn least_alternative(&self, index: usize) -> usize {
        if let Some(least) = self.least_alternatives.borrow().get(&index) {
            return *least;
        }
        let SetNode::Union(alternatives) = &self.nodes[index] else {
            unreachable!("a union")
        };
        let least = (1..alternatives.len()).fold(0, |least, alternative| {
            if self
                .compare(
                    self.view(&alternatives[alternative]),
                    self.view(&alternatives[least]),
                )
                .is_lt()
            {
                alternative
            } else {
                least
            }
        });
        self.least_alternatives.borrow_mut().insert(index, least);
        least
    }

    /// The length of the least reading of the concatenation `index`.
    fn least_length(&self, index: usize) -> usize {
        if let Some(length) = self.least_lengths.borrow().get(&index) {
            return *length;
        }
        let readings = Readings::Several(index);
        let length = self
            .lengths(&readings)
            .iter()
            .copied()
            .reduce(|least, length| {
                let ordering = self.compare_words(
                    &self.least_word(&readings, length),
                    &self.least_word(&readings, least),
                );
                if ordering.is_lt() { length } else { least }
            })
            .expect("a concatenation has a length");
        self.least_lengths.borrow_mut().insert(index, length);
        length
    }

    /// The least word of length `length` of `readings`, which has one, each item standing for
    /// the least reading of its set.
    ///
    /// Words of one length compare at their first differing item, so the least word of words
    /// of fixed lengths put together is their least words put together. That of a
    /// concatenation is then the least, over the ways its length divides among its children,
    /// of such a word, computed for every length of every prefix of its children once per
    /// node.
    fn least_word(&self, readings: &Readings, length: usize) -> Word {
        crate::stack::guarded(|| {
            let index = match readings {
                Readings::One(term) => {
                    return word_items(term)
                        .iter()
                        .map(|item| Rc::new(Readings::One(item.clone())))
                        .collect();
                }
                Readings::Several(index) => *index,
            };
            if let Some(word) = self.least_words.borrow().get(&(index, length)) {
                return Rc::clone(word);
            }
            let word: Word = match &self.nodes[index] {
                SetNode::Product {
                    key: Key::Sequence(_),
                    children,
                    ..
                } => children.iter().cloned().map(Rc::new).collect(),
                SetNode::Product { .. } => Rc::from([Rc::new(readings.clone())]),
                SetNode::Union(alternatives) => alternatives
                    .iter()
                    .filter(|alternative| self.lengths(alternative).contains(&length))
                    .map(|alternative| self.least_word(alternative, length))
                    .reduce(|least, word| {
                        if self.compare_words(&word, &least).is_lt() {
                            word
                        } else {
                            least
                        }
                    })
                    .expect("an alternative has the length"),
                SetNode::Concat { children, .. } => {
                    let mut prefixes =
                        BTreeMap::<usize, Vec<Rc<Readings>>>::from([(0, Vec::new())]);
                    for child in children.iter() {
                        let words = self
                            .lengths(child)
                            .iter()
                            .map(|own| (*own, self.least_word(child, *own)))
                            .collect::<Vec<_>>();
                        let mut extended = BTreeMap::<usize, Vec<Rc<Readings>>>::new();
                        for (before, prefix) in &prefixes {
                            for (own, word) in &words {
                                let candidate = prefix
                                    .iter()
                                    .chain(word.iter())
                                    .cloned()
                                    .collect::<Vec<_>>();
                                match extended.entry(before + own) {
                                    std::collections::btree_map::Entry::Vacant(vacant) => {
                                        vacant.insert(candidate);
                                    }
                                    std::collections::btree_map::Entry::Occupied(mut least) => {
                                        if self.compare_words(&candidate, least.get()).is_lt() {
                                            least.insert(candidate);
                                        }
                                    }
                                }
                            }
                        }
                        prefixes = extended;
                    }
                    let mut least_words = self.least_words.borrow_mut();
                    for (own, word) in prefixes {
                        least_words.insert((index, own), word.into());
                    }
                    return Rc::clone(
                        least_words
                            .get(&(index, length))
                            .expect("the concatenation has the length"),
                    );
                }
            };
            self.least_words
                .borrow_mut()
                .insert((index, length), Rc::clone(&word));
            word
        })
    }

    /// The order of two words as `Term::cmp` orders sequences: item by item, then by length.
    fn compare_words(&self, left: &[Rc<Readings>], right: &[Rc<Readings>]) -> std::cmp::Ordering {
        left.iter()
            .zip(right)
            .map(|(left, right)| self.compare(self.view(left), self.view(right)))
            .find(|ordering| ordering.is_ne())
            .unwrap_or_else(|| left.len().cmp(&right.len()))
    }

    /// The order of the terms two least views stand for, as `Term::cmp` orders them, without
    /// building them: by kind, then label, then arguments in order, then arity. Two nodes are
    /// compared once.
    fn compare(&self, left: LeastView<'_>, right: LeastView<'_>) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        crate::stack::guarded(|| {
            let (left, right) = (self.resolve(left), self.resolve(right));
            match (left, right) {
                (LeastView::Term(left), LeastView::Term(right)) => return left.cmp(right),
                (LeastView::Node(left), LeastView::Node(right)) if left == right => {
                    return Ordering::Equal;
                }
                (LeastView::Word(left, left_length), LeastView::Word(right, right_length))
                    if left == right && left_length == right_length =>
                {
                    return Ordering::Equal;
                }
                _ => {}
            }
            let pair = match (left, right) {
                (LeastView::Node(left), LeastView::Node(right)) => Some((left, right)),
                _ => None,
            };
            if let Some(ordering) =
                pair.and_then(|pair| self.comparisons.borrow().get(&pair).copied())
            {
                return ordering;
            }
            let ordering = self.compare_resolved(left, right);
            if let Some(pair) = pair {
                self.comparisons.borrow_mut().insert(pair, ordering);
            }
            ordering
        })
    }

    /// `ReadingSets::compare` of two resolved views, not both terms.
    fn compare_resolved(&self, left: LeastView<'_>, right: LeastView<'_>) -> std::cmp::Ordering {
        let ordering = self.head(left).cmp(&self.head(right));
        if ordering.is_ne() {
            return ordering;
        }
        let word = |view: LeastView<'_>| match view {
            LeastView::Word(index, length) => {
                Some(self.least_word(&Readings::Several(index), length))
            }
            LeastView::Term(_) | LeastView::Node(_) => None,
        };
        let (left_word, right_word) = (word(left), word(right));
        let (left_arity, right_arity) = (
            self.arity(left, left_word.as_deref()),
            self.arity(right, right_word.as_deref()),
        );
        for position in 0..left_arity.min(right_arity) {
            let ordering = self.compare(
                self.argument(left, left_word.as_deref(), position),
                self.argument(right, right_word.as_deref(), position),
            );
            if ordering.is_ne() {
                return ordering;
            }
        }
        left_arity.cmp(&right_arity)
    }

    /// The kind of the term a resolved view stands for, as `Term::cmp` ranks it, and its label
    /// when it is an application.
    fn head<'a>(&'a self, view: LeastView<'a>) -> (u8, Option<&'a crate::kast::Label>) {
        match view {
            LeastView::Term(term) => match term.unannotated() {
                Term::Apply { label, .. } => (term_rank(term.unannotated()), Some(label)),
                other => (term_rank(other), None),
            },
            LeastView::Node(index) => match &self.nodes[index] {
                SetNode::Product { key, .. } => match key {
                    Key::Apply(label, _) => (key.rank(), Some(label)),
                    Key::Rewrite | Key::As | Key::Sequence(_) | Key::Leaf(_) => (key.rank(), None),
                },
                SetNode::Concat { .. } | SetNode::Union(_) => {
                    unreachable!("a resolved node is a product")
                }
            },
            LeastView::Word(_, length) => (Key::Sequence(length).rank(), None),
        }
    }

    /// The number of arguments of the term a resolved view stands for; `word` is the view's
    /// least word when it is one.
    fn arity(&self, view: LeastView<'_>, word: Option<&[Rc<Readings>]>) -> usize {
        match view {
            LeastView::Term(term) => term_arguments(term).len(),
            LeastView::Node(index) => self.node_children(index).len(),
            LeastView::Word(..) => word.expect("a word").len(),
        }
    }

    /// The least view of the argument at `position` of the term a resolved view stands for;
    /// `word` is the view's least word when it is one.
    fn argument<'a>(
        &'a self,
        view: LeastView<'a>,
        word: Option<&'a [Rc<Readings>]>,
        position: usize,
    ) -> LeastView<'a> {
        match view {
            LeastView::Term(term) => LeastView::Term(term_arguments(term)[position]),
            LeastView::Node(index) => self.view(&self.node_children(index)[position]),
            LeastView::Word(..) => self.view(&word.expect("a word")[position]),
        }
    }

    /// The subterms at `position` of the readings of `readings` with root key `key`, which
    /// some of its readings have.
    fn subterms(&mut self, readings: &Readings, key: &Key, position: usize) -> Readings {
        crate::stack::guarded(|| {
            let index = match readings {
                Readings::One(term) => {
                    return Readings::One(term_arguments(term)[position].clone());
                }
                Readings::Several(index) => *index,
            };
            let memo = (index, position, key.clone());
            if let Some(subterms) = self.subterms.get(&memo) {
                return subterms.clone();
            }
            let subterms = match &self.nodes[index] {
                SetNode::Product { children, .. } => children[position].clone(),
                SetNode::Concat { .. } => {
                    let Key::Sequence(length) = key else {
                        unreachable!("the readings of a concatenation are sequences")
                    };
                    self.item(readings, *length, position)
                }
                SetNode::Union(alternatives) => {
                    let alternatives = Rc::clone(alternatives);
                    let mut subterms = Vec::new();
                    for alternative in alternatives.iter() {
                        if self.keys(alternative).contains(key) {
                            subterms.push(self.subterms(alternative, key, position));
                        }
                    }
                    self.union(subterms)
                }
            };
            self.subterms.insert(memo, subterms.clone());
            subterms
        })
    }

    /// The subterms of the readings of `readings` with root key `key` at each position at
    /// which they have several: none when they are one reading.
    fn varying_subterms(&mut self, readings: &Readings, key: &Key) -> Vec<Readings> {
        (0..key.arity())
            .map(|position| self.subterms(readings, key, position))
            .filter(|subterms| matches!(subterms, Readings::Several(_)))
            .collect()
    }

    /// The items at `position` of the words of length `length` of `readings`, which has some.
    ///
    /// For a concatenation, a word of that length is one word of each child whose lengths sum
    /// to it; the item at `position` lies in the child whose word covers it, at an offset set
    /// by the lengths of the words before it, and every word of each child occurs with every
    /// choice of the others. So the items are the union, over each child and each length of
    /// the words before it and of its own that leave a length the children after it have, of
    /// the child's items at that offset.
    fn item(&mut self, readings: &Readings, length: usize, position: usize) -> Readings {
        crate::stack::guarded(|| {
            let index = match readings {
                Readings::One(term) => return Readings::One(word_items(term)[position].clone()),
                Readings::Several(index) => *index,
            };
            if let Some(items) = self.items.get(&(index, length, position)) {
                return items.clone();
            }
            let items = match &self.nodes[index] {
                SetNode::Product {
                    key: Key::Sequence(_),
                    children,
                    ..
                } => children[position].clone(),
                SetNode::Product { .. } => readings.clone(),
                SetNode::Union(alternatives) => {
                    let alternatives = Rc::clone(alternatives);
                    let mut items = Vec::new();
                    for alternative in alternatives.iter() {
                        if self.lengths(alternative).contains(&length) {
                            items.push(self.item(alternative, length, position));
                        }
                    }
                    self.union(items)
                }
                SetNode::Concat { children, .. } => {
                    let children = Rc::clone(children);
                    let bounds = self.concat_bounds(index);
                    let mut covering = Vec::new();
                    for (child_index, child) in children.iter().enumerate() {
                        let lengths = self.lengths(child);
                        for before in bounds.prefixes[child_index].range(..=position) {
                            for own in lengths.iter() {
                                let end = before + own;
                                if end <= position || end > length {
                                    continue;
                                }
                                if bounds.suffixes[child_index + 1].contains(&(length - end)) {
                                    covering.push((child_index, *own, position - before));
                                }
                            }
                        }
                    }
                    let mut items = Vec::with_capacity(covering.len());
                    for (child_index, own, offset) in covering {
                        items.push(self.item(&children[child_index], own, offset));
                    }
                    self.union(items)
                }
            };
            self.items.insert((index, length, position), items.clone());
            items
        })
    }

    /// The span the roots of `readings` cover together. A root without a span of its own (a
    /// cast inference added) covers the text of its arguments.
    fn span(&self, readings: &Readings) -> Option<TermSpan> {
        crate::stack::guarded(|| match readings {
            Readings::One(term) => term_span(term),
            Readings::Several(index) => match &self.nodes[*index] {
                SetNode::Product { metadata, .. } | SetNode::Concat { metadata, .. } => {
                    metadata.span.or_else(|| {
                        cover(
                            self.node_children(*index)
                                .iter()
                                .filter_map(|child| self.span(child)),
                        )
                    })
                }
                SetNode::Union(alternatives) => cover(
                    alternatives
                        .iter()
                        .filter_map(|alternative| self.span(alternative)),
                ),
            },
        })
    }
}

/// The span of `term`, or, when it has none, the one its arguments cover together.
fn term_span(term: &Term) -> Option<TermSpan> {
    crate::stack::guarded(|| {
        term.metadata()
            .and_then(|metadata| metadata.span)
            .or_else(|| cover(term_arguments(term).into_iter().filter_map(term_span)))
    })
}

/// Make `kept`, the copy of a reading a union keeps, cover the text of `copy`, an equal
/// reading the union drops, at its root and at each subterm. A place's span is the text its
/// readings cover there; equal readings parsed from different text are one reading that covers
/// the text of every copy, so whichever copy a union keeps, and however a forest packs the
/// copies (one union of them, or unions below a node of each), a place covers them all.
fn widen_spans(kept: &mut Term, copy: &Term) {
    crate::stack::guarded(|| {
        for (kept, copy) in term_arguments_mut(kept)
            .into_iter()
            .zip(term_arguments(copy))
        {
            widen_spans(kept, copy);
        }
        let Some(other) = term_span(copy) else {
            return;
        };
        let span = match term_span(kept) {
            None => other,
            Some(own)
                if own.source != other.source
                    || (own.start <= other.start && other.end <= own.end) =>
            {
                return;
            }
            Some(own) => TermSpan {
                source: own.source,
                start: own.start.min(other.start),
                end: own.end.max(other.end),
            },
        };
        let widened = std::mem::replace(kept, Term::Sequence(Vec::new())).with_metadata(
            crate::kast::TermMetadata {
                span: Some(span),
                ..Default::default()
            },
        );
        *kept = widened;
    })
}

/// The smallest span that covers every one of `spans`.
fn cover(spans: impl Iterator<Item = TermSpan>) -> Option<TermSpan> {
    spans.reduce(|covered, span| TermSpan {
        source: covered.source,
        start: covered.start.min(span.start),
        end: covered.end.max(span.end),
    })
}

/// Whether two vectors of sets are built alike, metadata included, from nodes that are one
/// node when built alike.
fn identical_children(left: &[Readings], right: &[Readings]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| match (left, right) {
                (Readings::One(left), Readings::One(right)) => left.identical(right),
                (Readings::Several(left), Readings::Several(right)) => left == right,
                _ => false,
            })
}

/// The hash of `term` without its metadata, consistent with `Term`'s equality.
fn term_hash(term: &Term) -> u64 {
    let mut state = FxHasher::default();
    hash_term(term, &mut state);
    state.finish()
}

/// The items `term` contributes to a `~>` sequence it is spliced into: its own items when it
/// is a sequence, and otherwise itself.
fn word_items(term: &Term) -> &[Term] {
    match term.unannotated() {
        Term::Sequence(items) => items,
        _ => std::slice::from_ref(term),
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

/// The root key of a term: its head and arity, or the term itself when it has no arguments of
/// its own. Two terms with one key differ only in their arguments.
#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
enum Key {
    Rewrite,
    As,
    Sequence(usize),
    Apply(crate::kast::Label, usize),
    Leaf(Term),
}

impl Key {
    fn of(term: &Term) -> Self {
        match term.unannotated() {
            Term::Rewrite { .. } => Self::Rewrite,
            Term::As { .. } => Self::As,
            Term::Sequence(items) => Self::Sequence(items.len()),
            Term::Apply { label, arguments } => Self::Apply(label.clone(), arguments.len()),
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => {
                Self::Leaf(leaf.clone())
            }
            Term::Annotated { .. } => unreachable!("an unannotated term"),
        }
    }

    /// The rank of the kind of a term of this key, as `Term::cmp` orders kinds (`term_rank`).
    fn rank(&self) -> u8 {
        match self {
            Self::Rewrite => 1,
            Self::As => 2,
            Self::Sequence(_) => 4,
            Self::Apply(..) => 5,
            Self::Leaf(term) => term_rank(term.unannotated()),
        }
    }

    /// The number of arguments of a term of this key.
    fn arity(&self) -> usize {
        match self {
            Self::Rewrite | Self::As => 2,
            Self::Sequence(arity) | Self::Apply(_, arity) => *arity,
            Self::Leaf(_) => 0,
        }
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

/// `term_arguments`, mutably.
fn term_arguments_mut(term: &mut Term) -> Vec<&mut Term> {
    let mut term = term;
    loop {
        match term {
            Term::Annotated { term: inner, .. } => term = inner,
            Term::Rewrite { left, right } => return vec![&mut **left, &mut **right],
            Term::As { pattern, alias } => return vec![&mut **pattern, &mut **alias],
            Term::Sequence(items) => return items.iter_mut().collect(),
            Term::Apply { arguments, .. } => return arguments.iter_mut().collect(),
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {
                return Vec::new();
            }
        }
    }
}

/// The term that stands for an argument of a production lowered for its shape.
fn hole() -> Term {
    Term::variable("□")
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

/// Whether `sort` is one of `parameters` or applies a sort constructor to one.
fn mentions_parameter(sort: &Sort, parameters: &[Sort]) -> bool {
    parameters.contains(sort)
        || sort
            .parameters
            .iter()
            .any(|inner| mentions_parameter(inner, parameters))
}

/// A child slot as [`Grammar::prefer_structural_readings`] sees it: the sort its production
/// declares there and the sort the recognizer predicts there, which differ only at a place
/// widened to a rule-scaffolding sort (`Grammar::admit_rewrites_in_argument_positions`).
#[derive(Clone, Copy, Debug)]
struct StructuralPlace<'a> {
    declared: &'a Sort,
    recognized: &'a Sort,
}

/// The readings [`Grammar::prefer_structural_readings`] kept of a node at a place, by the node's
/// identity and the place's declared and recognized sorts, with the node kept alive beside its
/// entry.
type PreferenceMemo =
    HashMap<(*const PackedTerm, Option<(Sort, Sort)>), (Rc<PackedTerm>, Rc<PackedTerm>)>;

/// What makes two alternatives of one ambiguity the same node over different packings of its
/// children: the production, the node's metadata (its span among it) and every child's span.
/// `None` for a node without a production or a child of unknown span, which is grouped with
/// nothing.
type PositionKey<'a> = (usize, &'a TermMetadata, Vec<TermSpan>);

fn position_key(term: &PackedTerm) -> Option<PositionKey<'_>> {
    let PackedNode::Production {
        production,
        children,
        metadata,
    } = &term.node
    else {
        return None;
    };
    let spans = children
        .iter()
        .map(|child| super::chart::packed_term_span(child))
        .collect::<Option<Vec<_>>>()?;
    Some((*production, metadata, spans))
}

/// One node for a group of [`Grammar::alternatives_at_one_position`]: the group's production
/// over, at each child slot, the union of the group's children there.
fn merge_alternatives_at_one_position(group: &[&Rc<PackedTerm>]) -> Rc<PackedTerm> {
    let PackedNode::Production {
        production,
        children,
        metadata,
    } = &group[0].node
    else {
        unreachable!("a group of several alternatives applies one production")
    };
    let merged = (0..children.len())
        .map(|slot| {
            let mut union = BTreeSet::new();
            for alternative in group {
                let PackedNode::Production { children, .. } = &alternative.node else {
                    unreachable!("a group of several alternatives applies one production")
                };
                match &children[slot].node {
                    PackedNode::Ambiguity(nested) => union.extend(nested.iter().cloned()),
                    _ => {
                        union.insert(Rc::clone(&children[slot]));
                    }
                }
            }
            if union.len() == 1 {
                union.pop_first().expect("one alternative")
            } else {
                PackedTerm::ambiguity(union)
            }
        })
        .collect();
    PackedTerm::production(*production, merged, metadata.clone())
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
        /// The nodes `ReadingSets::push` adds on this thread.
        pub(super) static SET_NODES: Cell<usize> = const { Cell::new(0) };
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
                let actual = grammar.filter_completed_packed_priority(Rc::clone(&root), &memos);
                let expected = grammar.filter_completed_packed_priority_fresh(root);
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
                    .filter_completed_packed_priority(Rc::clone(&root), &memos)
                    .unwrap();
            }
            let shared_work = snapshot().delta(&before).get(Counter::ParserPackedPriorityComputations);
            let before = snapshot();
            for _ in 0..repetitions {
                grammar
                    .filter_completed_packed_priority_fresh(Rc::clone(&root))
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

    /// Each entry's term and whether other readings share its root.
    fn entries(alternatives: &[AmbiguousParse]) -> Vec<(&str, bool)> {
        alternatives
            .iter()
            .map(|alternative| (alternative.term.as_str(), alternative.more_with_same_root))
            .collect()
    }

    /// Each reported place's span start and entries' terms.
    fn place_entries(places: &[AmbiguityPlace]) -> Vec<(Option<usize>, Vec<&str>)> {
        places
            .iter()
            .map(|place| {
                (
                    place.span.map(|span| span.start),
                    rendered(&place.alternatives),
                )
            })
            .collect()
    }

    /// The calls of `Grammar::lower_production` and the reading-set nodes `run` makes.
    fn work(run: impl FnOnce()) -> [usize; 2] {
        LOWERINGS.with(|count| count.set(0));
        SET_NODES.with(|count| count.set(0));
        run();
        [LOWERINGS.with(Cell::get), SET_NODES.with(Cell::get)]
    }

    /// Assert that a measure grows by equal increments over three sizes in arithmetic
    /// progression: the work is linear in the size.
    fn assert_linear(counts: [usize; 3], measure: &str) {
        assert_eq!(
            counts[2] - counts[1],
            counts[1] - counts[0],
            "{measure}: {counts:?}"
        );
    }

    fn ambiguous_parts(
        error: ParseError,
    ) -> (Vec<AmbiguousParse>, Option<TermSpan>, Vec<AmbiguityPlace>) {
        let ParseError::Ambiguous {
            alternatives,
            span,
            places,
        } = error
        else {
            panic!("expected an ambiguity, got {error:?}")
        };
        (alternatives, span, places)
    }

    #[test]
    fn reports_the_smallest_subterm_outside_which_every_reading_agrees() {
        let (grammar, node) = readings_fixture();
        // `wrapper(a)`, `wrapper(b)` and `outer` differ at the root, so the report is the root,
        // not the inner ambiguity between `a` and `b`; its readings are listed one entry per
        // root key, `wrapper(a)` standing for the two `wrapper` readings.
        let root = ambiguity([
            node(
                "wrapper",
                vec![ambiguity([node("a", vec![], 10), node("b", vec![], 10)])],
                0,
            ),
            node("outer", vec![], 0),
        ]);
        let report = grammar.resolve_ambiguities(root).unwrap_err();
        let message = report.to_string();
        let (alternatives, span, places) = ambiguous_parts(report);
        assert_eq!(span.map(|span| span.start), Some(0));
        assert_eq!(
            entries(&alternatives),
            [("outer(.KList)", false), ("wrapper(a(.KList))", true)]
        );
        assert!(places.is_empty());
        assert!(
            message.starts_with("Parsing ambiguity.\n1: ")
                && message
                    .ends_with("wrapper(a(.KList))\n    and other readings with the same root"),
            "{message}"
        );

        // Readings that agree outside one child are reported at that child, however deep.
        let root = node(
            "wrapper",
            vec![node(
                "wrapper",
                vec![ambiguity([
                    node("a", vec![], 10),
                    node("outer", vec![], 10),
                ])],
                5,
            )],
            0,
        );
        let (alternatives, span, places) =
            ambiguous_parts(grammar.resolve_ambiguities(root).unwrap_err());
        assert_eq!(span.map(|span| span.start), Some(10));
        assert_eq!(
            entries(&alternatives),
            [("a(.KList)", false), ("outer(.KList)", false)]
        );
        assert!(places.is_empty());
    }

    #[test]
    fn an_entry_is_the_least_reading_whatever_the_order_of_alternatives() {
        let (grammar, node) = readings_fixture();
        // An ambiguity keeps its alternatives as trees, where `wrapper(a)` comes before `outer`
        // (its production is declared first), but `outer` is the lesser term. The `pair` entry
        // is the least `pair` reading, `pair(c, outer)`, both when the choice is packed inside
        // `pair`, with `wrapper(a)` as the union's first alternative, and when it is flat.
        let c = || node("c", vec![], 1);
        let wrapped = || node("wrapper", vec![node("a", vec![], 3)], 2);
        let outer = || node("outer", vec![], 2);
        let couple = || node("couple", vec![c(), node("c", vec![], 2)], 0);
        let packed = ambiguity([
            node("pair", vec![c(), ambiguity([wrapped(), outer()])], 0),
            couple(),
        ]);
        let flat = ambiguity([
            node("pair", vec![c(), wrapped()], 0),
            node("pair", vec![c(), outer()], 0),
            couple(),
        ]);
        let report = grammar.resolve_ambiguities(packed).unwrap_err();
        assert_eq!(grammar.resolve_ambiguities(flat).unwrap_err(), report);
        let (alternatives, _, _) = ambiguous_parts(report);
        assert_eq!(
            entries(&alternatives),
            [
                ("couple(c(.KList),c(.KList))", false),
                ("pair(c(.KList),outer(.KList))", true),
            ]
        );
    }

    #[test]
    fn a_place_covers_every_copy_of_an_equal_reading_however_the_trees_are_packed() {
        let (grammar, node) = readings_fixture();
        // `pair(a, c)` is read from two texts, `a` at 5..6 and `c` at 20..21, or `a` at 7..8
        // and `c` at 22..23; `pair(b, d)` reads `b` at 6..7 and `d` at 21..22. The readings
        // differ at both subterms, and each place covers the text of every copy of its readings,
        // 5..8 and 20..23, whichever copy a union meets first: in one ambiguity over the three
        // trees, or with either copy grouped first with `pair(b, d)` in a nested ambiguity.
        let tree = |first: &str, at: usize, second: &str, second_at: usize| {
            node(
                "pair",
                vec![node(first, vec![], at), node(second, vec![], second_at)],
                0,
            )
        };
        let near = || tree("a", 5, "c", 20);
        let far = || tree("a", 7, "c", 22);
        let other = || tree("b", 6, "d", 21);
        let flat = ambiguity([near(), other(), far()]);
        let far_first = ambiguity([ambiguity([far(), other()]), near()]);
        let near_first = ambiguity([ambiguity([near(), other()]), far()]);
        let report = grammar.resolve_ambiguities(flat).unwrap_err();
        assert_eq!(grammar.resolve_ambiguities(far_first).unwrap_err(), report);
        assert_eq!(grammar.resolve_ambiguities(near_first).unwrap_err(), report);
        let (_, _, places) = ambiguous_parts(report);
        let spans: Vec<_> = places
            .iter()
            .map(|place| place.span.map(|span| (span.start, span.end)))
            .collect();
        assert_eq!(spans, [Some((5, 8)), Some((20, 23))]);
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
        let (alternatives, span, _) = ambiguous_parts(report);
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
        let message = report.to_string();
        let (alternatives, span, places) = ambiguous_parts(report);
        assert_eq!(span.map(|span| span.start), Some(0));
        assert!(alternatives.is_empty());
        assert_eq!(
            place_entries(&places),
            [
                (Some(10), vec!["a(.KList)", "b(.KList)"]),
                (Some(20), vec!["c(.KList)", "d(.KList)"]),
            ]
        );
        assert!(
            message.starts_with("Parsing ambiguity: the readings differ in 2 subterms.")
                && message.contains("\nSubterm 2 at bytes 20..21:\n1: "),
            "{message}"
        );
    }

    #[test]
    fn readings_that_differ_at_two_places_report_both_whichever_combinations_are_readings() {
        let (grammar, node) = readings_fixture();
        let left = |name| node(name, vec![], 10);
        let right = |name| node(name, vec![], 20);
        // `pair(a, c)` and `pair(b, d)` differ at both children, together. The report names
        // the two subterms and their readings, as for the four combinations: which
        // combinations are readings is not reported (`docs/compatibility.md`).
        let together = ambiguity([
            node("pair", vec![left("a"), right("c")], 0),
            node("pair", vec![left("b"), right("d")], 0),
        ]);
        let every = node(
            "pair",
            vec![
                ambiguity([left("a"), left("b")]),
                ambiguity([right("c"), right("d")]),
            ],
            0,
        );
        let report = grammar.resolve_ambiguities(together).unwrap_err();
        assert_eq!(grammar.resolve_ambiguities(every).unwrap_err(), report);
        let (alternatives, span, places) = ambiguous_parts(report);
        assert_eq!(span.map(|span| span.start), Some(0));
        assert!(alternatives.is_empty());
        assert_eq!(
            place_entries(&places),
            [
                (Some(10), vec!["a(.KList)", "b(.KList)"]),
                (Some(20), vec!["c(.KList)", "d(.KList)"]),
            ]
        );
    }

    #[test]
    fn places_are_found_below_every_position_whose_readings_have_one_root_key() {
        let (grammar, node) = readings_fixture();
        // `pair(T, c)` and `pair(wrapper(T), d)`, where `T` has 8 readings. Both children of
        // `pair` differ: the first between `T`, rooted at `pair`, and `wrapper(T)`, one entry
        // per root key, the second between `c` and `d`.
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
        let (alternatives, _, places) = ambiguous_parts(report);
        assert!(alternatives.is_empty());
        assert_eq!(
            places
                .iter()
                .map(|place| entries(&place.alternatives))
                .collect::<Vec<_>>(),
            [
                vec![
                    ("pair(a(.KList),pair(a(.KList),a(.KList)))", true),
                    ("wrapper(pair(a(.KList),pair(a(.KList),a(.KList))))", true),
                ],
                vec![("c(.KList)", false), ("d(.KList)", false)],
            ]
        );

        // Below a choice beside it, the places of the subterm are places of the whole.
        let outer = node(
            "couple",
            vec![
                root(false),
                ambiguity([node("a", vec![], 200), node("b", vec![], 200)]),
            ],
            0,
        );
        let report = grammar.resolve_ambiguities(outer).unwrap_err();
        let message = report.to_string();
        let (_, _, places) = ambiguous_parts(report);
        assert_eq!(
            places
                .iter()
                .map(|place| place.span.map(|span| (span.start, span.end)))
                .collect::<Vec<_>>(),
            [Some((0, 6)), Some((100, 101)), Some((200, 201))]
        );
        assert!(
            message.starts_with(
                "Parsing ambiguity: the readings differ in 3 subterms.\n\
                 Subterm 1 at bytes 0..6:\n1: "
            ) && message.contains("\nSubterm 3 at bytes 200..201:\n1: "),
            "{message}"
        );
    }

    #[test]
    fn readings_with_two_heads_over_independent_choices_are_listed_in_linear_work() {
        let (grammar, node) = readings_fixture();
        // `pair(a, T)` and `couple(b, T)`, where `T` has 2^k readings, as `a(X, Y, t(...))` read
        // through two productions over `t(...)`: the readings differ at the root, so they are
        // listed one entry per root key, each the least of its 2^k readings.
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
        let report = grammar.resolve_ambiguities(root(2, false)).unwrap_err();
        assert_eq!(
            grammar.resolve_ambiguities(root(2, true)).unwrap_err(),
            report
        );
        let (alternatives, _, places) = ambiguous_parts(report);
        assert!(places.is_empty());
        assert_eq!(
            entries(&alternatives),
            [
                ("couple(b(.KList),pair(a(.KList),a(.KList)))", true),
                ("pair(a(.KList),pair(a(.KList),a(.KList)))", true),
            ]
        );

        let measured = |choices| {
            work(|| {
                let (alternatives, _, _) = ambiguous_parts(
                    grammar
                        .resolve_ambiguities(root(choices, false))
                        .unwrap_err(),
                );
                assert_eq!(alternatives.len(), 2);
            })
        };
        // Each 4 more choices take as much more work: the work is linear in their number.
        let counts = [measured(4), measured(8), measured(12)];
        assert_linear(counts.map(|[lowerings, _]| lowerings), "lowerings");
        assert_linear(counts.map(|[_, nodes]| nodes), "set nodes");
    }

    #[test]
    fn overlapping_alternatives_report_as_their_union() {
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
        let (_, _, places) = ambiguous_parts(report);
        assert_eq!(
            place_entries(&places),
            [
                (Some(10), vec!["a(.KList)", "b(.KList)"]),
                (Some(20), vec!["c(.KList)", "d(.KList)"]),
            ]
        );
    }

    /// `f(x_1, ..., x_n) | f(y_1, ..., y_n)` over one `n`-ary `f`, where `x_i` reads `a` or
    /// `b` at odd `i` and `a` at even `i`, and `y_i` the other way round, so that the two
    /// alternatives share readings and each has 2^(n/2) of its own (the overlapping products
    /// of review R2-F2), and, with `lead`, a first child `c` in the first alternative and `d`
    /// in the second, which makes them disjoint. Each child `i` spans `10 * (i + 1)`.
    fn overlapping_products(arity: usize, lead: bool) -> (Grammar, ParsedTerm) {
        let mut grammar = Grammar::default();
        let f = add_production(&mut grammar, "Exp", &vec!["Exp"; arity + 1], "f");
        let mut leaves = BTreeMap::new();
        for name in ["a", "b", "c", "d"] {
            leaves.insert(name, add_production(&mut grammar, "Exp", &[], name));
        }
        let span = |start: usize| crate::kast::TermMetadata {
            span: Some(TermSpan {
                source: SourceId(0),
                start,
                end: start + 1,
            }),
            ..Default::default()
        };
        let leaf = |name: &str, position: usize| ParsedTerm::Production {
            production: leaves[name],
            children: Vec::new(),
            metadata: span(10 * (position + 1)),
        };
        let alternative = |first: &str, parity: usize| ParsedTerm::Production {
            production: f,
            children: std::iter::once(if lead {
                leaf(first, 0)
            } else {
                ambiguity([leaf("a", 0), leaf("b", 0)])
            })
            .chain((1..=arity).map(|position| {
                if position % 2 == parity {
                    ambiguity([leaf("a", position), leaf("b", position)])
                } else {
                    leaf("a", position)
                }
            }))
            .collect(),
            metadata: span(0),
        };
        let root = ambiguity([alternative("c", 1), alternative("d", 0)]);
        (grammar, root)
    }

    #[test]
    fn overlapping_products_are_reported_in_work_linear_in_their_arity() {
        for lead in [false, true] {
            let measured = |arity: usize| {
                let (grammar, root) = overlapping_products(arity, lead);
                work(|| {
                    let (alternatives, span, places) =
                        ambiguous_parts(grammar.resolve_ambiguities(root).unwrap_err());
                    assert!(alternatives.is_empty());
                    assert_eq!(span.map(|span| span.start), Some(0));
                    // Every child reads `a` or `b`, or, first with `lead`, `c` or `d`.
                    assert_eq!(places.len(), arity + 1);
                    assert!(places.iter().skip(1).all(|place| {
                        rendered(&place.alternatives) == ["a(.KList)", "b(.KList)"]
                    }));
                })
            };
            // Each 8 more children take as much more work: no choice inside either
            // alternative is listed, whether the alternatives overlap or not.
            let counts = [measured(8), measured(16), measured(24)];
            assert_linear(counts.map(|[lowerings, _]| lowerings), "lowerings");
            assert_linear(counts.map(|[_, nodes]| nodes), "set nodes");
        }
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
        let measured = |items| {
            work(|| {
                let (_, _, places) =
                    ambiguous_parts(grammar.resolve_ambiguities(sequence(items)).unwrap_err());
                assert_eq!(places.len(), items);
            })
        };
        // Each 4 more items take as much more work: the work is linear in their number.
        let counts = [measured(4), measured(8), measured(12)];
        assert_linear(counts.map(|[lowerings, _]| lowerings), "lowerings");
        assert_linear(counts.map(|[_, nodes]| nodes), "set nodes");
    }

    #[test]
    fn a_sequence_whose_last_item_may_be_empty_is_reported_in_work_linear_in_its_length() {
        let (grammar, node) = readings_fixture();
        // `x ~> ... ~> x ~> y`, each `x` reading `a` or `b` and `y` reading `a` or the empty
        // sequence, nested as the parser builds a binary `~>`. Its readings are sequences of
        // two lengths, one entry each.
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
        let measured = |items| {
            work(|| {
                let (alternatives, _, _) =
                    ambiguous_parts(grammar.resolve_ambiguities(sequence(items)).unwrap_err());
                assert_eq!(
                    alternatives
                        .iter()
                        .map(|alternative| alternative.more_with_same_root)
                        .collect::<Vec<_>>(),
                    [true, true]
                );
            })
        };
        // Each 4 more items take as much more work: the work is linear in their number.
        let counts = [measured(4), measured(8), measured(12)];
        assert_linear(counts.map(|[lowerings, _]| lowerings), "lowerings");
        assert_linear(counts.map(|[_, nodes]| nodes), "set nodes");
    }

    #[test]
    fn a_sequence_with_interleaved_empty_items_is_reported_in_work_linear_in_its_length() {
        let (grammar, node) = readings_fixture();
        // `a ~> y ~> a ~> y ~> ... ~> a` with `m` items `y`, each reading `b` or the empty
        // sequence, nested as the parser builds a binary `~>`: 2^m readings, the sequences of
        // `m + 1` to `2m + 1` items, one entry per length. Only the shortest (every `y` empty)
        // and the longest (every `y` a `b`) are one reading each.
        let sequence = |optional: usize| {
            (0..=2 * optional)
                .map(|index| {
                    let start = 10 * (index + 1);
                    if index % 2 == 0 {
                        node("a", vec![], start)
                    } else {
                        ambiguity([node("b", vec![], start), node("#EmptyK", vec![], start)])
                    }
                })
                .reduce(|left, right| node("~>", vec![left, right], 0))
                .expect("at least one item")
        };
        let (alternatives, _, _) =
            ambiguous_parts(grammar.resolve_ambiguities(sequence(2)).unwrap_err());
        assert_eq!(
            entries(&alternatives),
            [
                ("a(.KList)~>a(.KList)~>a(.KList)", false),
                ("a(.KList)~>a(.KList)~>b(.KList)~>a(.KList)", true),
                (
                    "a(.KList)~>b(.KList)~>a(.KList)~>b(.KList)~>a(.KList)",
                    false
                ),
            ]
        );
        let measured = |optional| {
            work(|| {
                let (alternatives, _, _) =
                    ambiguous_parts(grammar.resolve_ambiguities(sequence(optional)).unwrap_err());
                assert_eq!(alternatives.len(), optional + 1);
            })
        };
        // Each 4 more optional items take as many more lowerings: no reading is built beyond
        // one per entry.
        let counts = [measured(4), measured(8), measured(12)];
        assert_linear(counts.map(|[lowerings, _]| lowerings), "lowerings");
    }

    #[test]
    fn a_token_of_ambiguous_strings_pairs_only_its_string_tokens() {
        let (grammar, node) = readings_fixture();
        let mut grammar = grammar;
        let token = add_production(
            &mut grammar,
            "Exp",
            &["KString", "KString"],
            InternalLabel::KToken.as_str(),
        );
        let string = |text: &str| {
            ParsedTerm::Term(Term::Token {
                token: format!("\"{text}\""),
                sort: Sort::frontend(FrontendSort::KString),
            })
        };
        // `#token("1" | "2", "Int" | a)`: the two values joined with `"Int"` are tokens, and the
        // values with `a`, which is not a string, are applications of `#KToken`.
        let root = ParsedTerm::Production {
            production: token,
            children: vec![
                ambiguity([string("1"), string("2")]),
                ambiguity([string("Int"), node("a", vec![], 10)]),
            ],
            metadata: crate::kast::TermMetadata::default(),
        };
        let (alternatives, _, places) =
            ambiguous_parts(grammar.resolve_ambiguities(root).unwrap_err());
        assert!(places.is_empty());
        assert_eq!(entries(&alternatives).len(), 3, "{alternatives:#?}");
        assert_eq!(
            alternatives
                .iter()
                .filter(|alternative| alternative.more_with_same_root)
                .count(),
            1,
            "{alternatives:#?}"
        );
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
        // So are an item and the sequence of that one item, spliced into a sequence.
        let root = node(
            "~>",
            vec![
                ambiguity([
                    node("a", vec![], 10),
                    node(
                        "~>",
                        vec![node("a", vec![], 10), node("#EmptyK", vec![], 11)],
                        10,
                    ),
                ]),
                node("b", vec![], 20),
            ],
            0,
        );
        assert_eq!(
            grammar.resolve_ambiguities(root).unwrap().to_string(),
            "a(.KList)~>b(.KList)"
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

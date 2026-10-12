//! ```toml algorithm
//! id = "parser.inference.portable"
//! name = "portable sort inference by bound propagation"
//! sites = ["Grammar::infer_sorts_portable", "Grammar::infer_packed_sorts", "Grammar::infer_sorts", "Grammar::infer_ambiguous_sorts_portable", "Grammar::infer_ambiguous_sorts_portable_first"]
//! variable = "V = sort-bound vertices (of a forest: variables); E = bound edges; S = concrete sorts among the bounds (of a forest: sorts of the subsort order); I = instances of an ambiguous forest, a node with one context its ancestors give it; a = largest arity; W = distinct typings of the trees of one instance; M = maximal typings; P = nodes of the forest of a typing group whose trees instantiate formal parameters differently"
//! counters = ["ParserPortableInferences"]
//! falls_back_to = ["parser.inference.z3"]
//! consumes = [{ type = "k_rust::inner::parser::forest::PackedTerm", role = "packed forest" }]
//! produces = [{ type = "k_rust::inner::parser::forest::ParsedTerm", role = "sorted tree" }]
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one tree"
//! bound = "O(V x E)"
//!
//! [[cost]]
//! mode = "ambiguous monomorphic forest"
//! bound = "O(I x a x W^2 x V x S/64) for the typings of every instance, O(W^2 x V) for the maximal typings of the root, O(M x I) to build the kept trees, plus, for a typing group whose trees instantiate formal parameters differently, the lowering of each of its trees alone computed on its forest of P nodes (parser.disambiguation.resolve_ambiguity, mode each tree), polynomial in P and independent of its number of trees; W is at most the trees below an instance and 1 where its ambiguities choose sorts for variables that occur only below it; the sorts' numbering, and each sort's down and up sets (S/64 words each), are built once per grammar, the first time a decision reads them (SortTable)"
//!
//! [[cost]]
//! mode = "variable realization"
//! bound = "O((V + E) x S) for the concrete bounds every variable reaches (one strongly-connected-component pass per direction), plus one PartialOrder::new over the subsort relations the first time a grammar needs its order"
//! ```
//!
//! Portable bound-propagation sort inference for monomorphic trees and forests.
//!
//! Constraint propagation saturates a finite sort-bound graph, worst-case O(V * E).
//! An ambiguous monomorphic forest is decided by keeping the trees whose typing no other tree's
//! typing strictly exceeds (`Grammar::infer_ambiguous_sorts_portable`), computed on the forest
//! from the distinct typings of each node's trees (`Grammar::decide_forest`), never by listing
//! its trees. Parametric forests, trees without a greatest typing and trees of one typing that
//! instantiate formal parameters differently and do not all lower to one term dispatch to Z3.
//! Deciding whether a packed forest has a well-sorted tree is NP-complete (a forest of clauses
//! over two incomparable sorts encodes satisfiability), so the decision's cost is polynomial in
//! the forest times the number of distinct typings its nodes exhibit, which no bound on the
//! forest alone gives. In the z3 build the
//! portable decision is asked first and Z3 decides what it refuses or rejects
//! (`Grammar::infer_ambiguous_sorts_portable_first`); checked mode runs both engines as oracles,
//! comparing inferred trees on unambiguous forests and lowered terms on ambiguous ones. `Counter::ParserPortableInferences` counts portable inference attempts, one per unambiguous tree
//! and one per ambiguous forest.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::definition::{PartialOrder, ProductionItem};
use crate::kast::{FrontendSort, GeneratedLabel, InternalLabel, Label, Sort, Term, TermSpan};

mod forest_decision;

pub(super) use forest_decision::SortTable;

#[cfg(test)]
use super::cmp_packed_structurally;
use super::{
    Grammar, Item, LoweringSession, PackedNode, PackedTerm, ParseError, ParsedParts, ParsedTerm,
    Production, inferred_variable_name,
};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum SortRef {
    Concrete(Sort),
    Variable(usize),
}

#[derive(Clone, Debug, Default)]
struct Bounds {
    lower: BTreeSet<SortRef>,
    upper: BTreeSet<SortRef>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum VariableId {
    Named(String),
    Anonymous(usize),
}

/// Why the portable engine did not type one tree.
enum PortableError {
    /// The tree's sort constraints have no solution: the tree is ill-sorted.
    Unsatisfiable(ParseError),
    /// The constraints have solutions but no greatest one, so the engine does not choose.
    Incomparable(ParseError),
    /// The tree or the grammar is not a well-formed inference problem.
    Malformed(ParseError),
}

impl PortableError {
    fn into_parse_error(self) -> ParseError {
        match self {
            Self::Unsatisfiable(error) | Self::Incomparable(error) | Self::Malformed(error) => {
                error
            }
        }
    }
}

/// A variable of a rule as it is identified across the alternative trees of one forest: a named
/// variable by its name, an anonymous one by its source occurrence, the span it stands at and
/// its name. A written anonymous variable is the only variable at its span; the variables a
/// record pattern stands in for its omitted fields share the pattern's span and are told apart
/// by their names, one per field (`omitted_field_variable` in `record.rs`).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum TypingVariable {
    Named(String),
    Anonymous(TermSpan, String),
}

/// One tree typed by the portable engine, with the sorts it realized for the tree's variables,
/// which the per-tree decision of a forest compares (`Grammar::maximal_typing_groups`).
struct TypedTree {
    term: ParsedTerm,
    #[cfg(test)]
    typing: BTreeMap<TypingVariable, Sort>,
    /// An anonymous variable without a source span has no identity across trees.
    #[cfg(test)]
    unidentified_variable: bool,
}

#[cfg(test)]
/// The kept trees of one maximal typing, factored into one term.
struct TypingGroup {
    term: Rc<PackedTerm>,
    /// The group's trees when two of them instantiate the formal sort parameters of their
    /// productions differently (`parameter_instantiations`); `None` when all instantiate them
    /// alike.
    parameter_split: Option<BTreeSet<ParsedTerm>>,
}

/// A lowered parse result whose equality with another decides, when the trees of a forest are
/// lowered one at a time (`lower_each_tree_by_listing`), whether a choice among them changes
/// the parse (`Grammar::infer_ambiguous_sorts_portable`).
#[cfg(test)]
pub(super) trait LoweredTerm {
    /// Equal as parse results, compiler metadata included.
    fn same_lowering(&self, other: &Self) -> bool;
}

#[cfg(test)]
impl LoweredTerm for Term {
    fn same_lowering(&self, other: &Self) -> bool {
        self.identical(other)
    }
}

#[cfg(test)]
impl LoweredTerm for ParsedTerm {
    fn same_lowering(&self, other: &Self) -> bool {
        self == other
    }
}

/// Two inferred forests are the same result when they stand for the same owned tree, which
/// their structural order decides without unpacking them.
#[cfg(test)]
impl LoweredTerm for Rc<PackedTerm> {
    fn same_lowering(&self, other: &Self) -> bool {
        cmp_packed_structurally(self, other).is_eq()
    }
}

/// How a caller turns the sort-inferred trees of a forest into its result.
pub(super) trait Lowering<T> {
    /// The result for the inferred trees, packed as one owned tree.
    fn lower(&self, inferred: ParsedTerm) -> Result<T, ParseError>;

    /// The result for an inferred packed forest: one the Z3 engine inferred as a whole, or the
    /// join of the inferred forests of two parts of a structural choice
    /// (`Grammar::infer_without_structural_preference`). By default, the result for its trees
    /// as one owned tree, which can have exponentially more nodes than the forest; the parse's
    /// lowering and [`InferredForest`] override it to keep to the forest.
    fn lower_forest(&self, inferred: &Rc<PackedTerm>) -> Result<T, ParseError> {
        self.lower(inferred.unpack())
    }

    /// The one result every tree of an inferred packed forest has when lowered alone, `None`
    /// when two trees' results differ (`Term::identical` for a term) or a tree's lowering fails.
    /// Each lowering computes it on the forest, in time polynomial in the forest's nodes: the
    /// parse's lowering runs forms of its passes that read, at an ambiguity, the alternative each
    /// tree takes (`Grammar::lower_each_inferred_tree`), and [`InferredForest`]'s result is the
    /// forest, so its trees have one result only when there is one tree.
    fn lower_each_tree(&self, inferred: &Rc<PackedTerm>) -> Result<Option<T>, ParseError>;
}

/// The one result every tree of an inferred packed forest has when lowered alone by `lower`,
/// each tree built and lowered on its own up to the first that differs or fails, `None` then or
/// when `usize` cannot count the trees: the definition `Lowering::lower_each_tree` computes on
/// the forest, which the tests check it against.
#[cfg(test)]
pub(super) fn lower_each_tree_by_listing<T: LoweredTerm>(
    lower: &impl Lowering<T>,
    inferred: &Rc<PackedTerm>,
) -> Option<T> {
    let mut lowered = packed_trees(inferred)?.map(|tree| lower.lower(tree));
    let Some(Ok(first)) = lowered.next() else {
        return None;
    };
    lowered
        .all(|other| other.is_ok_and(|other| other.same_lowering(&first)))
        .then_some(first)
}

/// A closure lowers each tree alone by listing the trees, for the tests' lowerings.
#[cfg(test)]
impl<T: LoweredTerm, F: Fn(ParsedTerm) -> Result<T, ParseError>> Lowering<T> for F {
    fn lower(&self, inferred: ParsedTerm) -> Result<T, ParseError> {
        self(inferred)
    }

    fn lower_each_tree(&self, inferred: &Rc<PackedTerm>) -> Result<Option<T>, ParseError> {
        Ok(lower_each_tree_by_listing(self, inferred))
    }
}

/// The inferred trees themselves, as a packed forest that stands for exactly the owned tree an
/// engine hands its lowering: a forest the Z3 engine inferred is kept as it is, and the owned
/// tree of the portable engine is packed as written ([`LoweringSession::intern_parsed`]). Like
/// `Ok` on the owned tree, it never fails.
struct InferredForest;

impl Lowering<Rc<PackedTerm>> for InferredForest {
    fn lower(&self, inferred: ParsedTerm) -> Result<Rc<PackedTerm>, ParseError> {
        Ok(LoweringSession::default().intern_parsed(&inferred))
    }

    fn lower_forest(&self, inferred: &Rc<PackedTerm>) -> Result<Rc<PackedTerm>, ParseError> {
        Ok(Rc::clone(inferred))
    }

    /// Two trees are two results here, so the trees have one result only when there is one.
    fn lower_each_tree(
        &self,
        inferred: &Rc<PackedTerm>,
    ) -> Result<Option<Rc<PackedTerm>>, ParseError> {
        Ok((packed_tree_count(inferred) == 1).then(|| Rc::clone(inferred)))
    }
}

struct Solver<'a> {
    order: &'a PartialOrder<Sort>,
    bounds: Vec<Bounds>,
    variables: BTreeMap<VariableId, usize>,
    typing_variables: BTreeMap<VariableId, Option<TypingVariable>>,
    /// The sort parameter slots of each parametric production of the tree, in pre-order:
    /// `Grammar::insert_inferred_casts` walks the tree in the same order and reads them back by
    /// position, so a node is identified without a path, which would be as long as its depth.
    parameters: Vec<Vec<usize>>,
    /// Every slot of `parameters`.
    parameter_slots: HashSet<usize>,
    constraint_cache: BTreeSet<(SortRef, SortRef)>,
    next_anonymous: usize,
}

/// The concrete sorts each variable reaches along its bounds of one direction.
type ConcreteBounds = Vec<Rc<BTreeSet<Sort>>>;

/// The sort of every variable, and of every parameter slot of each parametric production.
type Realization = (BTreeMap<VariableId, Sort>, Vec<Vec<Sort>>);

impl Grammar {
    /// Infer the sorts of a packed forest and lower the result with `lower`.
    ///
    /// The portable decision of an ambiguous forest depends on how its kept trees lower
    /// (`Grammar::infer_ambiguous_sorts_portable`), so inference and lowering are one step here.
    pub(super) fn infer_packed_sorts<T>(
        &self,
        term: Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
        lower: &impl Lowering<T>,
    ) -> Result<T, ParseError> {
        if !self.packed_sort_inference_supported(&term) {
            #[cfg(feature = "z3-inference")]
            return self.infer_ambiguous_sorts_portable_first(
                term,
                top_sort,
                explicitly_anywhere,
                lower,
            );
            #[cfg(not(feature = "z3-inference"))]
            return self.infer_ambiguous_sorts_portable(
                &term,
                top_sort,
                explicitly_anywhere,
                lower,
            );
        }
        let unpacked = term.unpack();
        lower.lower(self.infer_sorts(unpacked, top_sort, explicitly_anywhere)?)
    }

    /// Decide a parse none of whose preferred readings is well sorted by the sorts of every
    /// reading the relations admit, `admitted`; `preferred_error` is the preferred readings'
    /// rejection.
    ///
    /// The preference (`Grammar::prefer_structural_readings`) chooses before inference, from the
    /// sorts written in a reading, so it can keep only readings that inference rejects and drop
    /// the one it would accept: under `f(Foo)` with a user `Foo ::= Bar "=>" Bar`,
    /// `<k> f(X => Y) ... </k> <c> g(X) => .K ... </c>` with `g(Bar)` prefers the rewrite at
    /// `f`'s argument, which needs `X` both a `Foo` and a `Bar`. The rule the preference stands
    /// for is the per-position choice among the well-sorted readings: a reading is kept when no
    /// well-sorted reading that agrees with it outside a position ranks lower there. That set
    /// is not a product of choices per position (a variable's sort ties distant positions), so
    /// a forest pass cannot compute it; this decides the parses it can from inference alone.
    ///
    /// The readings are those of `admitted` without a rewrite inside a side of another or in a
    /// side condition where the position has another reading (`Grammar::prefer_no_rewrite_inside_a_term`): such a
    /// reading is no rule whatever its sorts, so dropping it drops no candidate. When no
    /// reading is well sorted, the preferred readings' rejection is the error, as without this
    /// step. Otherwise every position at which the readings differ in rank
    /// (`Grammar::structural_choices`) is asked, part by part, whether some well-sorted reading
    /// has that part there. When the well-sorted readings have parts of two ranks at one
    /// position, the per-position choice would separate them and this does not: the parse is
    /// reported ambiguous between a well-sorted reading of each part. When they have one rank
    /// at every such position, no well-sorted reading ranks lower than another where they
    /// first differ, so the per-position choice keeps every well-sorted reading, and inference
    /// over the readings decides exactly as it decides among the kept ones: its result is the
    /// parse.
    ///
    /// So a parse this returns is the one the per-position choice among well-sorted readings
    /// gives, and where that choice would separate readings by rank this reports an ambiguity
    /// rather than choose. It runs only after the preferred readings failed inference, so a
    /// parse whose preferred readings are well sorted pays nothing for it.
    ///
    /// Each part's inferred trees are kept as their packed forest ([`InferredForest`]), and the
    /// ambiguity between two parts is the packed node over both parts' readings, which stands for
    /// the owned ambiguity over their trees and is lowered as a forest
    /// ([`Lowering::lower_forest`]). A part's trees can be exponentially more than its forest's
    /// nodes, so deciding and joining the parts costs what their forests do, never their trees.
    pub(super) fn infer_without_structural_preference<T>(
        &self,
        admitted: &Rc<PackedTerm>,
        preferred_error: ParseError,
        top_sort: &Sort,
        explicitly_anywhere: bool,
        lower: &impl Lowering<T>,
    ) -> Result<T, ParseError> {
        let readings = self.prefer_no_rewrite_inside_a_term(Rc::clone(admitted));
        let merged = self.merge_alternatives_at_every_position(&readings);
        let choices = self.structural_choices(&merged);
        if choices.is_empty() {
            return Err(preferred_error);
        }
        let decided = self.infer_packed_sorts(
            self.finish_pre_inference_packed_forest(readings),
            top_sort,
            explicitly_anywhere,
            lower,
        );
        match decided {
            Err(ParseError::SortInference { .. }) => return Err(preferred_error),
            Err(error @ ParseError::Ambiguous { .. }) => return Err(error),
            _ => {}
        }
        for choice in &choices {
            let mut well_sorted: Option<Result<Rc<PackedTerm>, ParseError>> = None;
            for part in &choice.parts {
                let Some(through) = self.readings_through(&merged, choice, part) else {
                    continue;
                };
                let inferred = self.infer_packed_sorts(
                    self.finish_pre_inference_packed_forest(through),
                    top_sort,
                    explicitly_anywhere,
                    &InferredForest,
                );
                if matches!(inferred, Err(ParseError::SortInference { .. })) {
                    continue;
                }
                let Some(first) = well_sorted.take() else {
                    well_sorted = Some(inferred);
                    continue;
                };
                return match (first, inferred) {
                    (Ok(first), Ok(second)) => {
                        // A part's readings are the alternatives of its root ambiguity, or the
                        // part itself, and the join is an ambiguity even over one reading.
                        let mut readings = BTreeSet::new();
                        for inferred in [first, second] {
                            match &inferred.node {
                                PackedNode::Ambiguity(nested) => {
                                    readings.extend(nested.iter().cloned())
                                }
                                _ => {
                                    readings.insert(inferred);
                                }
                            }
                        }
                        lower.lower_forest(&PackedTerm::alternatives(readings))
                    }
                    (Err(error), _) | (_, Err(error)) => Err(error),
                };
            }
        }
        decided
    }

    /// Decide an ambiguous or parametric forest in the z3 build: the portable decision when it
    /// decides, otherwise Z3.
    ///
    /// Both engines decide which trees of the forest are the parse: the well-sorted trees whose
    /// typing no other tree's typing strictly exceeds. The portable decision
    /// (`Grammar::infer_ambiguous_sorts_portable`) keeps exactly those trees whenever it
    /// returns a term, and returns `ParseError::Z3InferenceRequired` instead of deciding
    /// wherever its premises fail: a parametric forest, an anonymous variable without a span
    /// when more than one tree is well-sorted, incomparable typings, a parameter slot its context
    /// does not determine (`Grammar::decide_forest`), or a parameter split that does not lower to
    /// one term. Both engines pack the kept trees as the pre-inference forest was
    /// (`Grammar::factor_pre_inference_packed_ambiguities`) before the same post-inference
    /// passes (`lower`), so a term the portable decision returns is the term Z3's decision
    /// lowers to; checked mode compares the two on every forest the portable decision decides
    /// (`Grammar::checked_ambiguous_parse`). Every portable rejection, a refusal or not, is
    /// handed to Z3, so a rejected forest gets Z3's diagnostic and the order of the engines
    /// never shows in a rejection. Both engines work on the forest with its subtrees shared, so
    /// the order costs one portable decision on a forest Z3 still decides and saves the solver
    /// on every other.
    #[cfg(feature = "z3-inference")]
    fn infer_ambiguous_sorts_portable_first<T>(
        &self,
        term: Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
        lower: &impl Lowering<T>,
    ) -> Result<T, ParseError> {
        if let Ok(decided) =
            self.infer_ambiguous_sorts_portable(&term, top_sort, explicitly_anywhere, lower)
        {
            return Ok(decided);
        }
        let inferred = self.infer_packed_forest_z3(term, top_sort, explicitly_anywhere)?;
        lower.lower_forest(&inferred)
    }

    /// Checked mode on an ambiguous forest in the z3 build: `None` when the forest is on the
    /// unambiguous portable path, whose inference checks itself. Otherwise the portable decision
    /// runs once; when it decides, both engines' results are lowered by `lower` and compared,
    /// and when it refuses (`ParseError::Z3InferenceRequired`) there is nothing to compare and
    /// Z3's lowered result is returned, as `Grammar::infer_ambiguous_sorts_portable_first` would
    /// return it after the same refusal. Returning it here, rather than `None`, keeps the caller
    /// from running the portable decision a second time. The
    /// caller runs it only under `KRUST_TYPE_INFERENCE_MODE=checked`
    /// (`checked_inference_requested`).
    ///
    /// Two inferred trees that differ only in a bracket production or in the instantiation of a
    /// formal sort parameter lower to one term, and the lowered term is what the rule means, so
    /// the comparison is on lowered terms, including their compiler metadata
    /// (`Term::identical`), or on both being errors. Z3's lowered result is returned, so
    /// checked mode does not change the z3 build's output.
    #[cfg(feature = "z3-inference")]
    pub(super) fn checked_ambiguous_parse(
        &self,
        term: &Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
        lower: &impl Lowering<Term>,
    ) -> Option<Result<Term, ParseError>> {
        if self.packed_sort_inference_supported(term) {
            return None;
        }
        let portable =
            self.infer_ambiguous_sorts_portable(term, top_sort, explicitly_anywhere, lower);
        let z3 = self
            .infer_packed_forest_z3(Rc::clone(term), top_sort, explicitly_anywhere)
            .and_then(|inferred| lower.lower_forest(&inferred));
        if matches!(portable, Err(ParseError::Z3InferenceRequired { .. })) {
            return Some(z3);
        }
        Some(checked_lowered_result(portable, z3))
    }

    /// Decide an ambiguous monomorphic forest without Z3 and lower the decision with `lower`.
    ///
    /// Each alternative `A` is a complete tree with a set `Sat(A)` of well-sorted variable
    /// typings. The forest's candidates are the pairs `(A, M)` with `M` maximal in the union of
    /// all `Sat(A)` and `M` in `Sat(A)`. The portable engine returns for one tree the greatest
    /// element `T_A` of `Sat(A)`, and it rejects a tree only when `Sat(A)` is empty; when
    /// `Sat(A)` has no greatest element it reports incomparable candidates instead of choosing.
    /// Since the sort order is finite, every element of `Sat(A)` is at most `T_A`, so every
    /// maximal `M` is some `T_A`, and `T_A` is maximal exactly when no `T_B` strictly exceeds
    /// it. If `T_A` is also in `Sat(C)`, then `T_A <= T_C`, and maximality forces `T_A = T_C`.
    /// The candidates are therefore exactly the well-sorted trees whose typing no other
    /// tree's typing strictly exceeds, each with its own typing. A variable that does not occur
    /// in a tree is unconstrained there, so it takes the top sort `K` that the engine gives
    /// every unconstrained variable. Both the kept trees and a unique tree then go through the
    /// same post-inference passes as any other inference result.
    ///
    /// The argument fixes the candidate set over variable typings; a tree's solution also
    /// includes the sorts at which its parametric productions instantiate their formal
    /// parameters, and maximality does not order those. Trees that share one maximal typing
    /// and one set of parameter instantiations have the same solution, so nothing in their sort
    /// constraints separates them: when the post-inference passes (`lower`) leave them
    /// ambiguous, the rule itself is ambiguous and `ParseError::Ambiguous` is the answer. When
    /// the trees of one typing instantiate parameters differently, choosing among them needs a
    /// preference over parameter instantiations that this decision does not model. The choice
    /// is immaterial only when every tree of the group lowers, on its own, to one and the same
    /// term: then any non-empty subset of the group lowers to that term. Otherwise a preference
    /// that keeps a subset of the group can change the parse, including when the
    /// post-inference passes would resolve the whole group (a `prefer` on a production whose
    /// trees the preference removes), so the forest is left to Z3 with
    /// `ParseError::Z3InferenceRequired`. An ambiguity between different maximal typings stays
    /// `ParseError::Ambiguous`.
    ///
    /// The decision is exact only under those premises, so it also returns
    /// `ParseError::Z3InferenceRequired` instead of deciding when a tree is parametric, when a
    /// tree's typing has incomparable candidates, and when an anonymous variable has no source
    /// span to identify it across trees. When no tree is well-sorted, the first tree's
    /// rejection is returned.
    ///
    /// The decision is computed on the forest (`Grammar::decide_forest`): a tree's typings are
    /// the product of one interval per variable, each the meet of what its occurrences' contexts
    /// allow, so the distinct typings of a node's trees are computed once per node and context.
    /// Where it differs from typing each tree alone, it decides more: a tree with a variable of
    /// no sort is ill-sorted even when another of its variables has incomparable candidates.
    /// Of the instances of a bracket over one text, it keeps the one at the sort its position
    /// gives, the reading without the brackets (`docs/compatibility.md`, "Formal parameter
    /// preference"); the other instances would bound the parameters of what they enclose by a
    /// sort no text states.
    pub(super) fn infer_ambiguous_sorts_portable<T>(
        &self,
        term: &Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
        lower: &impl Lowering<T>,
    ) -> Result<T, ParseError> {
        let (ambiguity, parametric_sorts) = self.packed_z3_reasons(term);
        let required = || ParseError::Z3InferenceRequired {
            ambiguity,
            parametric_sorts,
        };
        if parametric_sorts {
            return Err(required());
        }
        let _span = measure::algorithm_span(Algorithm::ParserInferencePortable);
        measure::bump(Counter::ParserPortableInferences);
        let groups = self.decide_forest(term, top_sort, explicitly_anywhere, &required);
        #[cfg(test)]
        self.check_forest_decision(term, top_sort, explicitly_anywhere, &groups, required);
        let groups = groups?;
        for group in groups.iter().filter(|group| group.parameter_split) {
            if !matches!(lower.lower_each_tree(&group.term), Ok(Some(_))) {
                return Err(required());
            }
        }
        let joined = self.factor_pre_inference_packed_ambiguities(PackedTerm::ambiguity(
            groups.into_iter().map(|group| group.term).collect(),
        ));
        lower.lower_forest(&joined)
    }

    /// The decision of `Grammar::infer_ambiguous_sorts_portable` computed tree by tree: every
    /// tree of the forest typed alone, the maximal typings' trees factored per typing, and a
    /// parameter split lowered tree by tree. The tests compare the forest decision with it.
    #[cfg(test)]
    pub(super) fn infer_ambiguous_sorts_per_tree<T: LoweredTerm>(
        &self,
        term: &Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
        lower: &impl Lowering<T>,
    ) -> Result<T, ParseError> {
        let (ambiguity, parametric_sorts) = self.packed_z3_reasons(term);
        let required = || ParseError::Z3InferenceRequired {
            ambiguity,
            parametric_sorts,
        };
        if parametric_sorts {
            return Err(required());
        }
        let groups = self.maximal_typing_groups(term, top_sort, explicitly_anywhere, required)?;
        let joined = |groups: Vec<Rc<PackedTerm>>| {
            self.factor_pre_inference_packed_ambiguities(PackedTerm::ambiguity(
                groups.into_iter().collect(),
            ))
            .unpack()
        };
        for trees in groups
            .iter()
            .filter_map(|group| group.parameter_split.as_ref())
        {
            let mut lowered = trees
                .iter()
                .map(|tree| lower.lower(joined(vec![PackedTerm::from_parsed(tree)])));
            let Some(Ok(first)) = lowered.next() else {
                return Err(required());
            };
            if !lowered.all(|other| other.is_ok_and(|other| other.same_lowering(&first))) {
                return Err(required());
            }
        }
        lower.lower(joined(groups.into_iter().map(|group| group.term).collect()))
    }

    /// Check the forest decision of `term` against the per-tree decision wherever the forest's
    /// trees can be listed: the same trees per maximal typing and the same parameter splits, or
    /// the same rejection. Where the per-tree decision refuses, the forest decision may decide:
    /// a tree with a variable of no sort is ill-sorted even when another of its variables has
    /// incomparable candidates, which the per-tree decision can meet first.
    #[cfg(test)]
    fn check_forest_decision(
        &self,
        term: &Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
        decided: &Result<Vec<forest_decision::DecidedGroup>, ParseError>,
        required: impl Fn() -> ParseError,
    ) {
        if packed_tree_count(term) > 1 << 12 {
            return;
        }
        let per_tree = self.maximal_typing_groups(term, top_sort, explicitly_anywhere, required);
        let trees = |term: &Rc<PackedTerm>| {
            expand_packed_trees(term)
                .into_iter()
                .map(|tree| self.erase_bracket_instances(tree))
                .collect::<BTreeSet<_>>()
        };
        let readings = |trees: &BTreeSet<ParsedTerm>| {
            trees
                .iter()
                .map(|tree| erase_instances(tree.clone()))
                .collect::<BTreeSet<_>>()
        };
        match (decided, per_tree) {
            (Ok(groups), Ok(per_tree)) => {
                // Up to the instances of brackets, each forest group keeps a nonempty subset of
                // one per-tree group, and every per-tree group has one: the forest decision
                // expects a bracket's child where the bracket stands, so it keeps, of the trees
                // the per-tree decision keeps, those whose parameters the brackets do not bound
                // below their position (`ForestDecision::eval`).
                let per_tree = per_tree
                    .iter()
                    .map(|group| (trees(&group.term), group.parameter_split.is_some()))
                    .collect::<Vec<_>>();
                let mut matched = BTreeSet::new();
                for group in groups {
                    let kept = trees(&group.term);
                    // Trees that differ only in metadata compare equal, so two groups can hold
                    // equal trees; each forest group takes an unmatched per-tree group.
                    let owner = (0..per_tree.len())
                        .find(|owner| {
                            !matched.contains(owner)
                                && !kept.is_empty()
                                && kept.is_subset(&per_tree[*owner].0)
                        })
                        .unwrap_or_else(|| panic!("the decisions of {term:?} differ"));
                    matched.insert(owner);
                    assert!(
                        !group.parameter_split || per_tree[owner].1,
                        "the parameter splits of {term:?} differ"
                    );
                    // Every reading the per-tree group keeps is kept, at some instance of its
                    // brackets and parameters: shadowing a bracket instance drops an instance,
                    // never a reading.
                    assert_eq!(
                        readings(&kept),
                        readings(&per_tree[owner].0),
                        "the readings of {term:?} differ"
                    );
                }
                assert_eq!(
                    matched.len(),
                    per_tree.len(),
                    "the decisions of {term:?} differ"
                );
            }
            (Err(forest), Err(per_tree)) => {
                assert_eq!(forest, &per_tree, "the rejections of {term:?} differ");
            }
            (_, Err(ParseError::Z3InferenceRequired { .. })) => {}
            (forest, per_tree) => panic!(
                "the decisions of {term:?} differ: forest {:?}, per tree {:?}",
                forest.as_ref().map(|groups| groups.len()),
                per_tree.map(|groups| groups.len())
            ),
        }
    }

    /// `tree` with every node of a bracket replaced by its child: the trees that differ only in
    /// the instance of a bracket they read are one reading.
    #[cfg(test)]
    pub(super) fn erase_bracket_instances(&self, tree: ParsedTerm) -> ParsedTerm {
        crate::stack::guarded(|| match tree.into_parts() {
            ParsedParts::Production {
                production,
                mut children,
                metadata,
            } => {
                let descriptor = &self.productions[production];
                if descriptor.bracket && children.len() == 1 {
                    return self.erase_bracket_instances(children.swap_remove(0));
                }
                ParsedTerm::Production {
                    production,
                    children: children
                        .into_iter()
                        .map(|child| self.erase_bracket_instances(child))
                        .collect(),
                    metadata,
                }
            }
            ParsedParts::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children: children
                    .into_iter()
                    .map(|child| self.erase_bracket_instances(child))
                    .collect(),
                metadata,
            },
            ParsedParts::Term(leaf) => ParsedTerm::Term(leaf),
            ParsedParts::Ambiguity(alternatives) => ParsedTerm::Ambiguity(
                alternatives
                    .into_iter()
                    .map(|alternative| self.erase_bracket_instances(alternative))
                    .collect(),
            ),
        })
    }

    /// The well-sorted trees of an ambiguous monomorphic forest that no other tree's typing
    /// strictly exceeds, one factored group per maximal typing
    /// (`Grammar::infer_ambiguous_sorts_portable` gives the argument).
    #[cfg(test)]
    fn maximal_typing_groups(
        &self,
        term: &Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
        required: impl Fn() -> ParseError,
    ) -> Result<Vec<TypingGroup>, ParseError> {
        let mut typed = Vec::new();
        let mut first_rejection = None;
        for tree in expand_packed_trees(term) {
            match self.infer_typed_sorts_portable(tree, top_sort, explicitly_anywhere) {
                Ok(tree) => typed.push(tree),
                Err(PortableError::Unsatisfiable(error)) => {
                    first_rejection.get_or_insert(error);
                }
                Err(PortableError::Incomparable(_)) => return Err(required()),
                Err(PortableError::Malformed(error)) => return Err(error),
            }
        }
        if typed.is_empty() {
            return Err(first_rejection.expect("an ambiguous forest has at least one tree"));
        }
        if typed.len() > 1 && typed.iter().any(|tree| tree.unidentified_variable) {
            return Err(required());
        }
        let order = self.sort_order().map_err(PortableError::into_parse_error)?;
        let top = Sort::new("K");
        let kept = typed
            .iter()
            .filter(|tree| {
                !typed
                    .iter()
                    .any(|other| strictly_exceeds(order, &top, &other.typing, &tree.typing))
            })
            .collect::<Vec<_>>();
        // A kept tree's typing, with every variable it lacks at the top sort, is the one maximal
        // typing the tree is well-sorted under, so the kept trees fall into one group per
        // maximal typing. Within a group the trees differ only where the forest had ambiguity
        // nodes, and they are factored back into that shape: the post-inference passes resolve
        // overloads, terminators and `prefer`/`avoid` per ambiguity node, so the same trees
        // listed as one flat ambiguity can lower differently. The groups are then alternatives
        // of one ambiguity, factored as the pre-inference forest was.
        let variables = kept
            .iter()
            .flat_map(|tree| tree.typing.keys())
            .collect::<BTreeSet<_>>();
        let mut groups = BTreeMap::<Vec<&Sort>, BTreeSet<ParsedTerm>>::new();
        for tree in kept {
            let typing = variables
                .iter()
                .map(|variable| tree.typing.get(*variable).unwrap_or(&top))
                .collect();
            groups.entry(typing).or_default().insert(tree.term.clone());
        }
        Ok(groups
            .into_values()
            .map(|trees| {
                let parameters_differ = trees
                    .iter()
                    .map(parameter_instantiations)
                    .collect::<BTreeSet<_>>()
                    .len()
                    > 1;
                let parameter_split = parameters_differ.then(|| trees.clone());
                TypingGroup {
                    term: PackedTerm::from_parsed(&factor_trees(trees)),
                    parameter_split,
                }
            })
            .collect())
    }

    fn packed_sort_inference_supported(&self, term: &Rc<PackedTerm>) -> bool {
        // Invariant: accepted recursion has seen only a monomorphic, unambiguous subtree and every
        // call strictly descends.
        fn supported(
            grammar: &Grammar,
            term: &Rc<PackedTerm>,
            visited: &mut HashSet<*const PackedTerm>,
        ) -> bool {
            crate::stack::guarded(|| {
                if !visited.insert(Rc::as_ptr(term)) {
                    return true;
                }
                match &term.node {
                    PackedNode::Ambiguity(_) => false,
                    PackedNode::Term(term) => match term.unannotated() {
                        Term::Token { sort, .. } => sort.parameters.is_empty(),
                        _ => true,
                    },
                    PackedNode::Production {
                        production,
                        children,
                        ..
                    } => {
                        let production = &grammar.productions[*production];
                        signature_is_monomorphic(production)
                            && children
                                .iter()
                                .all(|child| supported(grammar, child, visited))
                    }
                    PackedNode::InstantiatedProduction { .. } => {
                        unreachable!("sort support is checked before inference")
                    }
                }
            })
        }

        supported(self, term, &mut HashSet::new())
    }

    fn packed_z3_reasons(&self, term: &Rc<PackedTerm>) -> (bool, bool) {
        fn reasons(
            grammar: &Grammar,
            term: &Rc<PackedTerm>,
            visited: &mut HashSet<*const PackedTerm>,
        ) -> (bool, bool) {
            crate::stack::guarded(|| {
                if !visited.insert(Rc::as_ptr(term)) {
                    return (false, false);
                }
                match &term.node {
                    PackedNode::Ambiguity(alternatives) => alternatives.iter().fold(
                        (true, false),
                        |(ambiguity, parametric), alternative| {
                            let (child_ambiguity, child_parametric) =
                                reasons(grammar, alternative, visited);
                            (ambiguity || child_ambiguity, parametric || child_parametric)
                        },
                    ),
                    PackedNode::Production {
                        production,
                        children,
                        ..
                    } => {
                        let descriptor = &grammar.productions[*production];
                        let local = !signature_is_monomorphic(descriptor);
                        children
                            .iter()
                            .fold((false, local), |(ambiguity, parametric), child| {
                                let (child_ambiguity, child_parametric) =
                                    reasons(grammar, child, visited);
                                (ambiguity || child_ambiguity, parametric || child_parametric)
                            })
                    }
                    PackedNode::Term(term) => match term.unannotated() {
                        Term::Token { sort, .. } => (false, !sort.parameters.is_empty()),
                        _ => (false, false),
                    },
                    PackedNode::InstantiatedProduction { .. } => {
                        unreachable!("Z3 reasons are computed before inference")
                    }
                }
            })
        }

        reasons(self, term, &mut HashSet::new())
    }

    pub(super) fn infer_sorts(
        &self,
        term: ParsedTerm,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<ParsedTerm, ParseError> {
        #[cfg(all(test, feature = "z3-inference"))]
        super::z3_inference::record_inference_problem(self, &term, top_sort, explicitly_anywhere);
        if !self.sort_inference_supported(&term) {
            #[cfg(feature = "z3-inference")]
            return self.infer_sorts_z3(term, top_sort, explicitly_anywhere);
            #[cfg(not(feature = "z3-inference"))]
            {
                let (ambiguity, parametric_sorts) = self.z3_reasons(&term);
                return Err(ParseError::Z3InferenceRequired {
                    ambiguity,
                    parametric_sorts,
                });
            }
        }
        #[cfg(feature = "z3-inference")]
        if checked_inference_requested() {
            let portable = self.infer_sorts_portable(term.clone(), top_sort, explicitly_anywhere);
            let z3 = self.infer_sorts_z3(term, top_sort, explicitly_anywhere);
            return checked_inference_result(portable, z3);
        }
        self.infer_sorts_portable(term, top_sort, explicitly_anywhere)
    }

    fn infer_sorts_portable(
        &self,
        term: ParsedTerm,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<ParsedTerm, ParseError> {
        self.infer_typed_sorts_portable(term, top_sort, explicitly_anywhere)
            .map(|typed| typed.term)
            .map_err(PortableError::into_parse_error)
    }

    /// Infer the sorts of one unambiguous tree and also return the variable typing the solver
    /// realized for it.
    fn infer_typed_sorts_portable(
        &self,
        term: ParsedTerm,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<TypedTree, PortableError> {
        let _span = measure::algorithm_span(Algorithm::ParserInferencePortable);
        measure::bump(Counter::ParserPortableInferences);
        let order = self.sort_order()?;
        let anywhere = explicitly_anywhere || self.lhs_is_function_or_macro(&term);
        let anywhere_top = anywhere
            .then(|| self.top_rewrite_node(&term))
            .flatten()
            .map(std::ptr::from_ref);
        let mut solver = Solver::new(order);
        let inferred = solver.infer(self, &term, anywhere_top)?;
        // Synthetic rule-grammar result sorts describe parser context, not bounds on a
        // rewrite's formal result parameter. Concrete caller sorts remain real constraints.
        if top_sort.in_inference_domain() || !solver.is_parameter_ref(&inferred) {
            solver.constrain(inferred, SortRef::Concrete(top_sort.clone()))?;
        }
        let (variable_sorts, parameter_sorts) = solver.realize()?;
        #[cfg(test)]
        let mut typing = BTreeMap::new();
        #[cfg(test)]
        let mut unidentified_variable = false;
        #[cfg(test)]
        for (id, sort) in &variable_sorts {
            match &solver.typing_variables[id] {
                Some(variable) => {
                    typing.insert(variable.clone(), sort.clone());
                }
                None => unidentified_variable = true,
            }
        }
        let mut next_anonymous = 0;
        let mut next_parametric = 0;
        let term = self
            .insert_inferred_casts(
                term,
                &variable_sorts,
                &parameter_sorts,
                None,
                &mut next_anonymous,
                &mut next_parametric,
            )
            .map_err(PortableError::Malformed)?;
        Ok(TypedTree {
            term,
            #[cfg(test)]
            typing,
            #[cfg(test)]
            unidentified_variable,
        })
    }

    fn sort_order(&self) -> Result<&PartialOrder<Sort>, PortableError> {
        self.subsort_relations.order().map_err(|cycle| {
            PortableError::Malformed(inference_error(format!(
                "cannot infer sorts with a circular subsort relation: {}",
                cycle
                    .path
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" < ")
            )))
        })
    }

    fn sort_inference_supported(&self, term: &ParsedTerm) -> bool {
        crate::stack::guarded(|| match term {
            ParsedTerm::Ambiguity(_) => false,
            ParsedTerm::Term(term) => match term.unannotated() {
                Term::Token { sort, .. } => sort.parameters.is_empty(),
                _ => true,
            },
            ParsedTerm::Production {
                production,
                children,
                ..
            } => {
                let production = &self.productions[*production];
                signature_is_monomorphic(production)
                    && children
                        .iter()
                        .all(|child| self.sort_inference_supported(child))
            }
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("sort support is checked before inference")
            }
        })
    }

    #[cfg(not(feature = "z3-inference"))]
    fn z3_reasons(&self, term: &ParsedTerm) -> (bool, bool) {
        crate::stack::guarded(|| match term {
            ParsedTerm::Ambiguity(alternatives) => {
                alternatives
                    .iter()
                    .fold((true, false), |(ambiguity, parametric), alternative| {
                        let (_, child_parametric) = self.z3_reasons(alternative);
                        (ambiguity, parametric || child_parametric)
                    })
            }
            ParsedTerm::Production {
                production,
                children,
                ..
            } => {
                let descriptor = &self.productions[*production];
                let local = !signature_is_monomorphic(descriptor);
                children
                    .iter()
                    .fold((false, local), |(ambiguity, parametric), child| {
                        let (child_ambiguity, child_parametric) = self.z3_reasons(child);
                        (ambiguity || child_ambiguity, parametric || child_parametric)
                    })
            }
            ParsedTerm::Term(term) => match term.unannotated() {
                Term::Token { sort, .. } => (false, !sort.parameters.is_empty()),
                _ => (false, false),
            },
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("Z3 inference reasons are computed before inference")
            }
        })
    }

    pub(super) fn lhs_is_function_or_macro(&self, term: &ParsedTerm) -> bool {
        self.function_lhs(term).is_some()
    }

    pub(super) fn function_lhs<'a>(&self, term: &'a ParsedTerm) -> Option<&'a ParsedTerm> {
        let rewrite = self.top_rewrite(term)?;
        let lhs = strip_brackets(self, rewrite.0);
        let ParsedTerm::Production { production, .. } = lhs else {
            return None;
        };
        let production = &self.productions[*production];
        (production.function || production.macro_like).then_some(lhs)
    }

    fn top_rewrite<'a>(&self, term: &'a ParsedTerm) -> Option<(&'a ParsedTerm, &'a ParsedTerm)> {
        let term = self.top_rewrite_node(term)?;
        let ParsedTerm::Production { children, .. } = term else {
            unreachable!("top_rewrite_node returns a production")
        };
        Some((&children[0], &children[1]))
    }

    fn top_rewrite_node<'a>(&self, term: &'a ParsedTerm) -> Option<&'a ParsedTerm> {
        let mut term = strip_brackets(self, term);
        loop {
            let ParsedTerm::Production {
                production,
                children,
                ..
            } = term
            else {
                return None;
            };
            let production = &self.productions[*production];
            if production.result.is_frontend(FrontendSort::RuleContent) {
                term = strip_brackets(self, children.first()?);
                continue;
            }
            if production.result.is_frontend(FrontendSort::RuleBody)
                && production
                    .label
                    .as_ref()
                    .is_some_and(|label| label.is(InternalLabel::WithConfig))
            {
                term = strip_brackets(self, children.first()?);
                continue;
            }
            return (production
                .label
                .as_ref()
                .is_some_and(|label| label.is(InternalLabel::KRewrite))
                && children.len() == 2)
                .then_some(term);
        }
    }

    fn insert_inferred_casts(
        &self,
        term: ParsedTerm,
        variable_sorts: &BTreeMap<VariableId, Sort>,
        parameter_sorts: &[Vec<Sort>],
        enclosing_cast: Option<&Sort>,
        next_anonymous: &mut usize,
        next_parametric: &mut usize,
    ) -> Result<ParsedTerm, ParseError> {
        crate::stack::guarded(|| {
            match term.into_parts() {
                ParsedParts::Term(leaf) if inferred_variable_name(&leaf).is_some() => {
                    let term = ParsedTerm::Term(leaf);
                    let ParsedTerm::Term(leaf) = &term else {
                        unreachable!("built above")
                    };
                    let Some(name) = inferred_variable_name(leaf) else {
                        unreachable!()
                    };
                    let id = variable_id(name, next_anonymous);
                    let sort = variable_sorts.get(&id).ok_or_else(|| {
                        inference_error(format!(
                            "no inferred sort was produced for variable {name}"
                        ))
                    })?;
                    // A semantic cast bounds the variable from above; it records the variable's sort
                    // only when inference chose the bound itself. Otherwise the variable carries the
                    // inferred sort under the cast, so every occurrence agrees on it.
                    if let Some(bound) = enclosing_cast {
                        if bound == sort {
                            return Ok(term);
                        }
                        if let Some(variable) = super::variable_with_inferred_sort(leaf, sort) {
                            return Ok(ParsedTerm::Term(variable));
                        }
                    }
                    let label = Label::semantic_cast(sort).name;
                    let production = self
                    .productions
                    .iter()
                    .enumerate()
                    .find_map(|(index, production)| {
                        (production.label.as_ref().is_some_and(|candidate| candidate.name == label)
                            && production_arity(production) == 1)
                            .then_some(index)
                    })
                    .ok_or_else(|| {
                        inference_error(format!(
                            "cannot record inferred sort {sort} for variable {name}: missing semantic-cast production"
                        ))
                    })?;
                    Ok(ParsedTerm::Production {
                        production,
                        children: vec![term],
                        metadata: super::TermMetadata::default(),
                    })
                }
                ParsedParts::Term(leaf) => Ok(ParsedTerm::Term(leaf)),
                ParsedParts::Ambiguity(_) => Err(inference_error(
                    "portable sort inference received an ambiguous parse forest",
                )),
                ParsedParts::Production {
                    production,
                    children,
                    metadata,
                } => {
                    let descriptor = &self.productions[production];
                    let cast_sort = descriptor
                        .label
                        .as_ref()
                        .is_some_and(|label| {
                            matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. }))
                        })
                        .then_some(&descriptor.result);
                    // The parametric productions are numbered in pre-order, as `Solver::infer`
                    // records their parameters.
                    let parameters = descriptor
                    .parametric_origin
                    .is_some()
                    .then(|| {
                        let index = *next_parametric;
                        *next_parametric += 1;
                        parameter_sorts.get(index).cloned().ok_or_else(|| {
                            inference_error(format!(
                                "no inferred parameters were produced for parametric production {index}"
                            ))
                        })
                    })
                    .transpose()?;
                    let children = children
                        .into_iter()
                        .map(|child| {
                            self.insert_inferred_casts(
                                child,
                                variable_sorts,
                                parameter_sorts,
                                cast_sort,
                                next_anonymous,
                                next_parametric,
                            )
                        })
                        .collect::<Result<_, _>>()?;
                    if let Some(parameters) = parameters {
                        Ok(ParsedTerm::InstantiatedProduction {
                            production,
                            parameters,
                            children,
                            metadata,
                        })
                    } else {
                        Ok(ParsedTerm::Production {
                            production,
                            children,
                            metadata,
                        })
                    }
                }
                ParsedParts::InstantiatedProduction { .. } => {
                    unreachable!("portable inference cannot create instantiated productions")
                }
            }
        })
    }
}

impl<'a> Solver<'a> {
    fn new(order: &'a PartialOrder<Sort>) -> Self {
        Self {
            order,
            bounds: Vec::new(),
            variables: BTreeMap::new(),
            typing_variables: BTreeMap::new(),
            parameters: Vec::new(),
            parameter_slots: HashSet::new(),
            constraint_cache: BTreeSet::new(),
            next_anonymous: 0,
        }
    }

    fn infer(
        &mut self,
        grammar: &Grammar,
        term: &ParsedTerm,
        anywhere_top: Option<*const ParsedTerm>,
    ) -> Result<SortRef, PortableError> {
        crate::stack::guarded(|| {
            match term {
                ParsedTerm::Ambiguity(_) => Err(PortableError::Malformed(inference_error(
                    "portable sort inference does not support ambiguous parse forests",
                ))),
                ParsedTerm::Term(term) => {
                    match (inferred_variable_name(term), term.unannotated()) {
                        (Some(name), _) => self.variable(name, term),
                        (None, Term::Token { sort, .. }) => Ok(SortRef::Concrete(sort.clone())),
                        (None, _) => Err(PortableError::Malformed(inference_error(
                            "unexpected lowered KAST node in the concrete parse forest",
                        ))),
                    }
                }
                ParsedTerm::Production {
                    production,
                    children,
                    ..
                } => {
                    let production = &grammar.productions[*production];
                    let parameter_slots = production.parametric_origin.as_ref().map(|origin| {
                        origin
                            .parameters
                            .iter()
                            .map(|_| self.fresh_slot())
                            .collect::<Vec<_>>()
                    });
                    if let Some(slots) = &parameter_slots {
                        self.parameters.push(slots.clone());
                        self.parameter_slots.extend(slots.iter().copied());
                    }
                    let parameter_substitution = production
                        .parametric_origin
                        .as_ref()
                        .zip(parameter_slots.as_ref())
                        .map(|(origin, slots)| {
                            origin
                                .parameters
                                .iter()
                                .cloned()
                                .zip(slots.iter().copied().map(SortRef::Variable))
                                .collect::<BTreeMap<_, _>>()
                        })
                        .unwrap_or_default();
                    let child_sorts = children
                        .iter()
                        .map(|child| self.infer(grammar, child, anywhere_top))
                        .collect::<Result<Vec<_>, _>>()?;
                    let (expected, actual) = if let Some(origin) = &production.parametric_origin {
                        (
                            origin
                                .items
                                .iter()
                                .filter_map(|item| match item {
                                    ProductionItem::NonTerminal { sort, .. } => {
                                        Some(substitute_sort_ref(sort, &parameter_substitution))
                                    }
                                    ProductionItem::Terminal(_)
                                    | ProductionItem::RegexTerminal { .. } => None,
                                })
                                .collect::<Vec<_>>(),
                            substitute_sort_ref(&origin.result, &parameter_substitution),
                        )
                    } else {
                        (
                            production
                                .items
                                .iter()
                                .filter_map(|item| match item {
                                    Item::NonTerminal(sort) => {
                                        Some(SortRef::Concrete(sort.clone()))
                                    }
                                    Item::Terminal(_) | Item::Regex { .. } => None,
                                })
                                .collect::<Vec<_>>(),
                            SortRef::Concrete(production.result.clone()),
                        )
                    };
                    // A position the grammar widened to a `#Rule` scaffolding sort accepts a rewrite
                    // or `#as` node of that sort; such a node stands for a term of the declared sort
                    // and its own children carry that bound. Any other child keeps the declared sort.
                    let widened = production
                        .items
                        .iter()
                        .zip(&production.item_sort_ids)
                        .filter_map(|(item, sort_id)| match item {
                            Item::NonTerminal(sort) => {
                                let parse =
                                    &grammar.sorts[sort_id.expect("nonterminal has a sort id")];
                                Some((parse != sort).then(|| SortRef::Concrete(parse.clone())))
                            }
                            Item::Terminal(_) | Item::Regex { .. } => None,
                        })
                        .collect::<Vec<_>>();
                    if expected.len() != child_sorts.len() {
                        return Err(PortableError::Malformed(inference_error(format!(
                            "production {:?} has {} nonterminals but its parse node has {} children",
                            production.parse_label,
                            expected.len(),
                            child_sorts.len()
                        ))));
                    }
                    let anywhere_lhs_sort = (anywhere_top
                        .is_some_and(|top| std::ptr::eq(term, top))
                        && production
                            .label
                            .as_ref()
                            .is_some_and(|label| label.is(InternalLabel::KRewrite))
                        && children.len() == 2)
                        .then(|| {
                            if matches!(
                                strip_brackets(grammar, &children[0]),
                                ParsedTerm::Term(term)
                                    if matches!(term.unannotated(), Term::Variable { .. })
                            ) {
                                SortRef::Concrete(Sort::new("K"))
                            } else {
                                child_sorts[0].clone()
                            }
                        });
                    for (index, ((term, child), expected)) in children
                        .iter()
                        .zip(child_sorts.iter().cloned())
                        .zip(expected.iter().cloned())
                        .enumerate()
                    {
                        let expected = if index == 1
                            && let Some(lhs_sort) = &anywhere_lhs_sort
                        {
                            lhs_sort.clone()
                        } else if let Some(Some(parse)) = widened.get(index)
                            && &child == parse
                        {
                            parse.clone()
                        } else {
                            expected
                        };
                        if is_anonymous_leaf(term) {
                            // An anonymous occurrence occurs once, so nothing but its context
                            // constrains it: it has exactly the sort its context requires, the most
                            // general sort it can have there.  A mere upper bound is insufficient
                            // for parser sorts such as KItem, whose synthetic hierarchy is not always
                            // represented by an ordinary subsort production.
                            self.constrain(child.clone(), expected.clone())?;
                            self.constrain(expected, child)?;
                        } else if !(self.is_parameter_ref(&child)
                            && matches!(
                                &expected,
                                SortRef::Concrete(sort) if !sort.in_inference_domain()
                            ))
                        {
                            // Rule-grammar scaffolding sorts carry parser context, not semantic sort
                            // bounds for a formal production parameter. The Z3 engine and reference
                            // SimpleSub path likewise keep that parameter independent of the wrapper.
                            self.constrain(child, expected)?;
                        }
                    }
                    if let Some(lhs_sort) = anywhere_lhs_sort
                        && !matches!(&actual, SortRef::Concrete(sort) if !sort.in_inference_domain())
                    {
                        // A monomorphic #KRewrite may return #RuleK, which is parser scaffolding.
                        // Only semantic results (including formal parameters) inherit the LHS bound.
                        self.constrain(actual.clone(), lhs_sort)?;
                    }
                    if production.label.as_ref().is_some_and(|label| {
                        [
                            InternalLabel::SyntacticCast,
                            InternalLabel::SyntacticCastBraced,
                        ]
                        .iter()
                        .any(|cast| label.is(*cast))
                    }) && let (Some(child), Some(inner)) =
                        (expected.first(), child_sorts.first())
                    {
                        self.constrain(actual.clone(), child.clone())?;
                        self.constrain(child.clone(), actual.clone())?;
                        // A strict cast fixes the sort of its inner term without a runtime check,
                        // so that term's sort is exactly the cast sort. The loop above already bounds
                        // the inner sort by the declared one; bounding it from below too makes the
                        // two equal. Without it a cast would only restate what the enclosing
                        // position already requires and could not select an overload by sort.
                        // A synthetic parser sort such as the bottom sort of `#token(_,_)` or
                        // `#klabel(_)` says nothing about the term's sort: there the cast is the only
                        // statement of that sort, so it cannot be required to equal the cast sort.
                        if !matches!(inner, SortRef::Concrete(sort) if !sort.in_inference_domain())
                        {
                            self.constrain(child.clone(), inner.clone())?;
                        }
                    }
                    Ok(actual)
                }
                ParsedTerm::InstantiatedProduction { .. } => {
                    unreachable!("instantiated productions are created after constraint solving")
                }
            }
        })
    }

    fn variable(&mut self, name: &str, term: &Term) -> Result<SortRef, PortableError> {
        let id = variable_id(name, &mut self.next_anonymous);
        let variable = if let Some(variable) = self.variables.get(&id) {
            *variable
        } else {
            let variable = self.bounds.len();
            self.bounds.push(Bounds::default());
            let typing_variable = match &id {
                VariableId::Named(name) => Some(TypingVariable::Named(name.clone())),
                VariableId::Anonymous(_) => term
                    .metadata()
                    .and_then(|metadata| metadata.span)
                    .map(|span| TypingVariable::Anonymous(span, name.to_owned())),
            };
            self.typing_variables.insert(id.clone(), typing_variable);
            self.variables.insert(id, variable);
            self.constrain(
                SortRef::Variable(variable),
                SortRef::Concrete(Sort::new("K")),
            )?;
            variable
        };
        Ok(SortRef::Variable(variable))
    }

    fn fresh_slot(&mut self) -> usize {
        let variable = self.bounds.len();
        self.bounds.push(Bounds::default());
        variable
    }

    fn is_parameter_ref(&self, sort: &SortRef) -> bool {
        let SortRef::Variable(variable) = sort else {
            return false;
        };
        self.parameter_slots.contains(variable)
    }

    fn constrain(&mut self, lesser: SortRef, greater: SortRef) -> Result<(), PortableError> {
        crate::stack::guarded(|| {
            // Invariant: `constraint_cache` contains every propagated bound; recursive propagation
            // only adds finite lower or upper bounds.
            if lesser == greater
                || !self
                    .constraint_cache
                    .insert((lesser.clone(), greater.clone()))
            {
                return Ok(());
            }
            match (lesser, greater) {
                (SortRef::Variable(variable), greater) => {
                    self.bounds[variable].upper.insert(greater.clone());
                    let lower = self.bounds[variable]
                        .lower
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>();
                    for lesser in lower {
                        self.constrain(lesser, greater.clone())?;
                    }
                    Ok(())
                }
                (lesser, SortRef::Variable(variable)) => {
                    self.bounds[variable].lower.insert(lesser.clone());
                    let upper = self.bounds[variable]
                        .upper
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>();
                    for greater in upper {
                        self.constrain(lesser.clone(), greater)?;
                    }
                    Ok(())
                }
                (SortRef::Concrete(lesser), SortRef::Concrete(greater)) => {
                    if self.order.less_than_eq(&lesser, &greater) {
                        Ok(())
                    } else {
                        Err(PortableError::Unsatisfiable(inference_error(format!(
                            "unexpected sort {lesser}; expected a subsort of {greater}"
                        ))))
                    }
                }
            }
        })
    }

    /// The sort of every variable, and of every parameter slot of each parametric production
    /// in pre-order, chosen from the concrete bounds each reaches ([`Self::concrete_bounds`]).
    fn realize(&self) -> Result<Realization, PortableError> {
        let upper = self.concrete_bounds(true);
        let lower = self.concrete_bounds(false);
        let variables = self
            .variables
            .iter()
            .map(|(id, variable)| {
                self.realize_variable(*variable, &upper, &lower)
                    .map(|sort| (id.clone(), sort))
            })
            .collect::<Result<_, _>>()?;
        let parameters = self
            .parameters
            .iter()
            .map(|slots| {
                slots
                    .iter()
                    .map(|slot| self.realize_variable(*slot, &upper, &lower))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<_, _>>()?;
        Ok((variables, parameters))
    }

    fn realize_variable(
        &self,
        variable: usize,
        upper: &ConcreteBounds,
        lower: &ConcreteBounds,
    ) -> Result<Sort, PortableError> {
        if self.bounds[variable].lower.is_empty() && self.bounds[variable].upper.is_empty() {
            return Ok(Sort::new("K"));
        }
        let (upper, lower) = (&*upper[variable], &*lower[variable]);
        if upper.is_empty() && lower.is_empty() {
            return Ok(Sort::new("K"));
        }
        let k = Sort::new("K");
        if upper.is_empty() && lower.iter().all(|bound| self.order.less_than_eq(bound, &k)) {
            return Ok(k);
        }
        let candidates = if upper.len() == 1 {
            upper.clone()
        } else {
            let bounds = self.order.lower_bounds(upper.iter());
            self.order.maximal(bounds.iter())
        }
        .into_iter()
        .filter(|sort| {
            !self
                .order
                .less_than_eq(sort, &Sort::frontend(FrontendSort::KBott))
        })
        .filter(|candidate| {
            lower
                .iter()
                .all(|bound| self.order.less_than_eq(bound, candidate))
        })
        .collect::<BTreeSet<_>>();
        if candidates.len() == 1 {
            Ok(candidates.into_iter().next().expect("one candidate"))
        } else if candidates.is_empty() {
            Err(PortableError::Unsatisfiable(inference_error(format!(
                "variable has incompatible sort bounds: lower {lower:?}, upper {upper:?}"
            ))))
        } else {
            Err(PortableError::Incomparable(inference_error(format!(
                "variable sort has incomparable candidates {candidates:?} from bounds {upper:?}"
            ))))
        }
    }

    /// For each variable, the concrete sorts it reaches along its upper (`upper`) or lower
    /// bounds: its own concrete bounds and, through each variable bound, that variable's.
    ///
    /// Propagation (`constrain`) closes the bounds over concrete sorts in one direction only, so
    /// a chain of parameter slots `v_n <= ... <= v_1 <= Nat` (a nesting of a parametric
    /// production) leaves `Nat` to be found at the end of the chain from every slot. A sort is
    /// reachable along some path exactly when it is reachable along a simple one, so the sets
    /// are computed once for all variables over the strongly connected components of the bound
    /// graph (Tarjan's algorithm with an explicit stack; components are completed after every
    /// component they reach): a component's set joins its members' concrete bounds with the
    /// sets of the components they reach, and a component with no concrete bound of its own
    /// that reaches one set shares it. O((V + E) x S) for S concrete sorts.
    fn concrete_bounds(&self, upper: bool) -> ConcreteBounds {
        let edges = |variable: usize| {
            if upper {
                &self.bounds[variable].upper
            } else {
                &self.bounds[variable].lower
            }
        };
        let successors = |variable: usize| {
            edges(variable)
                .iter()
                .filter_map(|bound| match bound {
                    SortRef::Variable(next) => Some(*next),
                    SortRef::Concrete(_) => None,
                })
                .collect::<Vec<_>>()
        };
        let count = self.bounds.len();
        let empty = Rc::new(BTreeSet::new());
        let mut sets: Vec<Option<Rc<BTreeSet<Sort>>>> = vec![None; count];
        let mut index = vec![usize::MAX; count];
        let mut low_link = vec![0; count];
        let mut on_stack = vec![false; count];
        let mut component_stack = Vec::new();
        let mut next_index = 0;
        for root in 0..count {
            if index[root] != usize::MAX {
                continue;
            }
            // Invariant: `frames` is the depth-first path from `root`; each frame holds a
            // variable, its successors, and how many of them it has examined.
            let mut frames = vec![(root, successors(root), 0usize)];
            index[root] = next_index;
            low_link[root] = next_index;
            next_index += 1;
            component_stack.push(root);
            on_stack[root] = true;
            while let Some((variable, next, examined)) = frames.last_mut() {
                let variable = *variable;
                if let Some(&successor) = next.get(*examined) {
                    *examined += 1;
                    if index[successor] == usize::MAX {
                        index[successor] = next_index;
                        low_link[successor] = next_index;
                        next_index += 1;
                        component_stack.push(successor);
                        on_stack[successor] = true;
                        frames.push((successor, successors(successor), 0));
                    } else if on_stack[successor] {
                        low_link[variable] = low_link[variable].min(index[successor]);
                    }
                    continue;
                }
                frames.pop();
                if let Some((parent, _, _)) = frames.last() {
                    low_link[*parent] = low_link[*parent].min(low_link[variable]);
                }
                if low_link[variable] != index[variable] {
                    continue;
                }
                let mut members = Vec::new();
                loop {
                    let member = component_stack
                        .pop()
                        .expect("the component's root is stacked");
                    on_stack[member] = false;
                    members.push(member);
                    if member == variable {
                        break;
                    }
                }
                let mut own = BTreeSet::new();
                let mut reached: Vec<&Rc<BTreeSet<Sort>>> = Vec::new();
                for member in &members {
                    for bound in edges(*member) {
                        match bound {
                            SortRef::Concrete(sort) => {
                                own.insert(sort.clone());
                            }
                            SortRef::Variable(next) => {
                                if let Some(set) = &sets[*next]
                                    && !reached.iter().any(|known| Rc::ptr_eq(known, set))
                                {
                                    reached.push(set);
                                }
                            }
                        }
                    }
                }
                let set = match reached.as_slice() {
                    [] if own.is_empty() => Rc::clone(&empty),
                    [only] if own.is_empty() => Rc::clone(only),
                    _ => {
                        for set in reached {
                            own.extend(set.iter().cloned());
                        }
                        Rc::new(own)
                    }
                };
                for member in members {
                    sets[member] = Some(Rc::clone(&set));
                }
            }
        }
        sets.into_iter()
            .map(|set| set.expect("every variable belongs to a component"))
            .collect()
    }
}

fn strip_brackets<'a>(grammar: &Grammar, mut term: &'a ParsedTerm) -> &'a ParsedTerm {
    while let ParsedTerm::Production {
        production,
        children,
        ..
    } = term
    {
        if !grammar.productions[*production].bracket || children.len() != 1 {
            break;
        }
        term = &children[0];
    }
    term
}

fn is_anonymous_leaf(term: &ParsedTerm) -> bool {
    matches!(
        term,
        ParsedTerm::Term(term)
            if matches!(term.unannotated(), Term::Variable { name, .. } if is_anonymous(name))
    )
}

fn signature_is_monomorphic(production: &Production) -> bool {
    if let Some(origin) = &production.parametric_origin {
        let bare = |sort: &Sort| origin.parameters.contains(sort) || sort.parameters.is_empty();
        bare(&origin.result)
            && origin.items.iter().all(|item| {
                !matches!(
                    item,
                    ProductionItem::NonTerminal { sort, .. } if !bare(sort)
                )
            })
    } else {
        production.result.parameters.is_empty()
            && production
                .items
                .iter()
                .all(|item| !matches!(item, Item::NonTerminal(sort) if !sort.parameters.is_empty()))
    }
}

fn substitute_sort_ref(sort: &Sort, substitution: &BTreeMap<Sort, SortRef>) -> SortRef {
    substitution
        .get(sort)
        .cloned()
        .unwrap_or_else(|| SortRef::Concrete(sort.clone()))
}

#[cfg(feature = "z3-inference")]
pub(super) fn checked_inference_requested() -> bool {
    std::env::var("KRUST_TYPE_INFERENCE_MODE").as_deref() == Ok("checked")
}

#[cfg(feature = "z3-inference")]
fn checked_inference_result(
    portable: Result<ParsedTerm, ParseError>,
    z3: Result<ParsedTerm, ParseError>,
) -> Result<ParsedTerm, ParseError> {
    match (portable, z3) {
        (Ok(portable), Ok(z3)) if portable == z3 => Ok(portable),
        (Err(portable), Err(_)) => Err(portable),
        (portable, z3) => Err(engine_disagreement(portable, z3, false)),
    }
}

/// The lowered-term comparison of `Grammar::checked_ambiguous_parse`; returns Z3's result.
///
/// Two rejections agree unless one of them is an ambiguity that the other is not: an
/// ambiguity is reported from the readings the decision kept, so two engines that keep the
/// same trees report it alike, while an ill-sorted forest is explained by each engine in its
/// own terms.
#[cfg(feature = "z3-inference")]
fn checked_lowered_result(
    portable: Result<Term, ParseError>,
    z3: Result<Term, ParseError>,
) -> Result<Term, ParseError> {
    match (portable, z3) {
        (Ok(portable), Ok(z3)) if portable.identical(&z3) => Ok(z3),
        (Err(portable), Err(z3)) if rejections_agree(&portable, &z3) => Err(z3),
        (portable, z3) => Err(engine_disagreement(portable, z3, true)),
    }
}

/// Whether two engines' rejections of one forest are one rejection (`checked_lowered_result`).
#[cfg(feature = "z3-inference")]
fn rejections_agree(portable: &ParseError, z3: &ParseError) -> bool {
    let ambiguity = |error: &ParseError| matches!(error, ParseError::Ambiguous { .. });
    if ambiguity(portable) || ambiguity(z3) {
        return portable == z3;
    }
    true
}

/// The outcome of checked inference when the engines differ: at least one accepted, or both
/// rejected and at least one reported an ambiguity the other did not, so the term is neither
/// inferred nor rejected.
#[cfg(feature = "z3-inference")]
fn engine_disagreement<T: std::fmt::Debug>(
    portable: Result<T, ParseError>,
    z3: Result<T, ParseError>,
    ambiguous_parse: bool,
) -> ParseError {
    let render = |outcome: Result<T, ParseError>| {
        outcome
            .map(|term| format!("{term:?}"))
            .map_err(|error| error.to_string())
    };
    ParseError::InferenceEngineDisagreement {
        portable: render(portable),
        z3: render(z3),
        ambiguous_parse,
    }
}

/// The number of complete trees of a packed forest, saturating at `usize::MAX`. Shared nodes
/// are counted once each, so the count costs time linear in the forest's distinct nodes.
pub(super) fn packed_tree_count(term: &Rc<PackedTerm>) -> usize {
    tree_counts(term, &mut HashMap::new())
}

/// The tree count of `term` and of every node below it, recorded in `memo`, saturating at
/// `usize::MAX`.
fn tree_counts(term: &Rc<PackedTerm>, memo: &mut HashMap<*const PackedTerm, usize>) -> usize {
    crate::stack::guarded(|| {
        if let Some(count) = memo.get(&Rc::as_ptr(term)) {
            return *count;
        }
        let result = match &term.node {
            PackedNode::Term(_) => 1,
            PackedNode::Ambiguity(alternatives) => {
                alternatives.iter().fold(0usize, |total, alternative| {
                    total.saturating_add(tree_counts(alternative, memo))
                })
            }
            PackedNode::Production { children, .. }
            | PackedNode::InstantiatedProduction { children, .. } => {
                children.iter().fold(1usize, |total, child| {
                    total.saturating_mul(tree_counts(child, memo))
                })
            }
        };
        memo.insert(Rc::as_ptr(term), result);
        result
    })
}

/// The complete trees of a packed forest in the order of `expand_packed_trees`, each built only
/// when it is read, so a caller that stops at a tree pays for no later one and holds one tree at
/// a time; `None` when `usize` cannot count them. Tree `index` is read off the tree counts of
/// the nodes: an ambiguity's trees are its alternatives' in turn, and a production's are the
/// combinations of its children's trees with the last child varying fastest.
#[cfg(test)]
pub(super) fn packed_trees(term: &Rc<PackedTerm>) -> Option<impl Iterator<Item = ParsedTerm>> {
    fn nth(
        term: &Rc<PackedTerm>,
        mut index: usize,
        counts: &HashMap<*const PackedTerm, usize>,
    ) -> ParsedTerm {
        crate::stack::guarded(|| {
            let count = |term: &Rc<PackedTerm>| counts[&Rc::as_ptr(term)];
            let children_at = |children: &[Rc<PackedTerm>], mut index: usize| {
                let mut indexes = vec![0; children.len()];
                for (slot, child) in indexes.iter_mut().zip(children).rev() {
                    *slot = index % count(child);
                    index /= count(child);
                }
                children
                    .iter()
                    .zip(indexes)
                    .map(|(child, index)| nth(child, index, counts))
                    .collect()
            };
            match &term.node {
                PackedNode::Term(leaf) => ParsedTerm::Term(leaf.clone()),
                PackedNode::Ambiguity(alternatives) => {
                    for alternative in alternatives {
                        if index < count(alternative) {
                            return nth(alternative, index, counts);
                        }
                        index -= count(alternative);
                    }
                    unreachable!("a tree index is below its forest's tree count")
                }
                PackedNode::Production {
                    production,
                    children,
                    metadata,
                } => ParsedTerm::Production {
                    production: *production,
                    children: children_at(children, index),
                    metadata: metadata.clone(),
                },
                PackedNode::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                    metadata,
                } => ParsedTerm::InstantiatedProduction {
                    production: *production,
                    parameters: parameters.clone(),
                    children: children_at(children, index),
                    metadata: metadata.clone(),
                },
            }
        })
    }
    let mut counts = HashMap::new();
    let total = tree_counts(term, &mut counts);
    // A saturated count is no count; below a root with trees, every count is at most the root's.
    let term = Rc::clone(term);
    (total < usize::MAX).then(move || (0..total).map(move |index| nth(&term, index, &counts)))
}

/// The complete trees of a packed forest. The caller bounds their number with
/// `packed_tree_count`.
#[cfg(test)]
pub(super) fn expand_packed_trees(term: &Rc<PackedTerm>) -> Vec<ParsedTerm> {
    fn expand(
        term: &Rc<PackedTerm>,
        memo: &mut HashMap<*const PackedTerm, Rc<Vec<ParsedTerm>>>,
    ) -> Rc<Vec<ParsedTerm>> {
        crate::stack::guarded(|| {
            if let Some(trees) = memo.get(&Rc::as_ptr(term)) {
                return Rc::clone(trees);
            }
            let trees = match &term.node {
                PackedNode::Term(leaf) => vec![ParsedTerm::Term(leaf.clone())],
                PackedNode::Ambiguity(alternatives) => alternatives
                    .iter()
                    .flat_map(|alternative| expand(alternative, memo).as_ref().clone())
                    .collect(),
                PackedNode::Production {
                    production,
                    children,
                    metadata,
                } => child_combinations(children.iter().map(|child| expand(child, memo)).collect())
                    .into_iter()
                    .map(|children| ParsedTerm::Production {
                        production: *production,
                        children,
                        metadata: metadata.clone(),
                    })
                    .collect(),
                PackedNode::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                    metadata,
                } => child_combinations(children.iter().map(|child| expand(child, memo)).collect())
                    .into_iter()
                    .map(|children| ParsedTerm::InstantiatedProduction {
                        production: *production,
                        parameters: parameters.clone(),
                        children,
                        metadata: metadata.clone(),
                    })
                    .collect(),
            };
            let trees = Rc::new(trees);
            memo.insert(Rc::as_ptr(term), Rc::clone(&trees));
            trees
        })
    }
    expand(term, &mut HashMap::new()).as_ref().clone()
}

/// `tree` (with its brackets erased) with every instantiated production read as its production:
/// the reading a tree is, whatever sorts its parameters were instantiated at.
#[cfg(test)]
fn erase_instances(tree: ParsedTerm) -> ParsedTerm {
    crate::stack::guarded(|| match tree.into_parts() {
        ParsedParts::Production {
            production,
            children,
            metadata,
        }
        | ParsedParts::InstantiatedProduction {
            production,
            children,
            metadata,
            ..
        } => ParsedTerm::Production {
            production,
            children: children.into_iter().map(erase_instances).collect(),
            metadata,
        },
        ParsedParts::Term(leaf) => ParsedTerm::Term(leaf),
        ParsedParts::Ambiguity(alternatives) => {
            ParsedTerm::Ambiguity(alternatives.into_iter().map(erase_instances).collect())
        }
    })
}

#[cfg(test)]
/// The formal-parameter instantiations of one inferred tree: each parametric production it
/// uses with the sorts its parameters were instantiated at, in a canonical order.
fn parameter_instantiations(term: &ParsedTerm) -> Vec<(usize, &[Sort])> {
    fn collect<'t>(term: &'t ParsedTerm, into: &mut Vec<(usize, &'t [Sort])>) {
        crate::stack::guarded(|| match term {
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
                ..
            } => {
                into.push((*production, parameters));
                children.iter().for_each(|child| collect(child, into));
            }
            ParsedTerm::Production { children, .. } => {
                children.iter().for_each(|child| collect(child, into));
            }
            ParsedTerm::Ambiguity(alternatives) => {
                alternatives.iter().for_each(|child| collect(child, into));
            }
            ParsedTerm::Term(_) => {}
        })
    }
    let mut instantiations = Vec::new();
    collect(term, &mut instantiations);
    instantiations.sort_unstable();
    instantiations
}

#[cfg(test)]
/// One term whose complete trees are exactly `trees`, with each ambiguity as deep as the trees
/// allow: trees that share a node differ below it only in its children, and when they are
/// every combination of the children's variants the node is kept once over factored children.
fn factor_trees(trees: BTreeSet<ParsedTerm>) -> ParsedTerm {
    /// A node without its children: two trees with equal headers differ only in children.
    #[derive(Eq, Ord, PartialEq, PartialOrd)]
    enum Header<'t> {
        Leaf(&'t ParsedTerm),
        Node {
            production: usize,
            parameters: Option<&'t [Sort]>,
            metadata: &'t super::TermMetadata,
            arity: usize,
        },
    }
    fn header(term: &ParsedTerm) -> Header<'_> {
        match term {
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } => Header::Node {
                production: *production,
                parameters: None,
                metadata,
                arity: children.len(),
            },
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => Header::Node {
                production: *production,
                parameters: Some(parameters),
                metadata,
                arity: children.len(),
            },
            ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => Header::Leaf(term),
        }
    }
    fn children(term: &ParsedTerm) -> &[ParsedTerm] {
        match term {
            ParsedTerm::Production { children, .. }
            | ParsedTerm::InstantiatedProduction { children, .. } => children,
            ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => &[],
        }
    }

    if trees.len() == 1 {
        return trees.into_iter().next().expect("length was one");
    }
    let mut by_header = BTreeMap::<Header<'_>, Vec<&ParsedTerm>>::new();
    for tree in &trees {
        by_header.entry(header(tree)).or_default().push(tree);
    }
    let mut alternatives = BTreeSet::new();
    for (header, group) in by_header {
        let Header::Node { arity, .. } = header else {
            alternatives.extend(group.into_iter().cloned());
            continue;
        };
        let variants = (0..arity)
            .map(|index| {
                group
                    .iter()
                    .map(|tree| children(tree)[index].clone())
                    .collect::<BTreeSet<_>>()
            })
            .collect::<Vec<_>>();
        let combinations = variants
            .iter()
            .try_fold(1usize, |total, variants| total.checked_mul(variants.len()));
        if group.len() == 1 || combinations != Some(group.len()) {
            alternatives.extend(group.into_iter().cloned());
            continue;
        }
        let factored = variants.into_iter().map(factor_trees).collect();
        alternatives.insert(match group[0].clone().into_parts() {
            ParsedParts::Production {
                production,
                metadata,
                ..
            } => ParsedTerm::Production {
                production,
                children: factored,
                metadata,
            },
            ParsedParts::InstantiatedProduction {
                production,
                parameters,
                metadata,
                ..
            } => ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children: factored,
                metadata,
            },
            ParsedParts::Term(_) | ParsedParts::Ambiguity(_) => {
                unreachable!("only production headers have children")
            }
        });
    }
    if alternatives.len() == 1 {
        alternatives.pop_first().expect("length was one")
    } else {
        ParsedTerm::Ambiguity(alternatives)
    }
}

/// Every choice of one tree per child position, in order.
#[cfg(test)]
fn child_combinations(children: Vec<Rc<Vec<ParsedTerm>>>) -> Vec<Vec<ParsedTerm>> {
    let mut combinations = vec![Vec::with_capacity(children.len())];
    for options in children {
        combinations = combinations
            .into_iter()
            .flat_map(|prefix| {
                options.iter().map(move |option| {
                    let mut combination = prefix.clone();
                    combination.push(option.clone());
                    combination
                })
            })
            .collect();
    }
    combinations
}

#[cfg(test)]
/// Whether the typing `greater` strictly exceeds `lesser`: every variable of either typing has a
/// sort in `lesser` at most its sort in `greater`, and some variable's sorts differ. A variable
/// absent from a typing does not occur in that tree, so it is unconstrained there and takes the
/// top sort `top`.
fn strictly_exceeds(
    order: &PartialOrder<Sort>,
    top: &Sort,
    greater: &BTreeMap<TypingVariable, Sort>,
    lesser: &BTreeMap<TypingVariable, Sort>,
) -> bool {
    let sort = |typing: &'_ BTreeMap<TypingVariable, Sort>, variable| {
        typing.get(variable).unwrap_or(top).clone()
    };
    let variables = greater.keys().chain(lesser.keys()).collect::<BTreeSet<_>>();
    let mut distinct = false;
    for variable in variables {
        let (lesser, greater) = (sort(lesser, variable), sort(greater, variable));
        if lesser != greater {
            if !order.less_than_eq(&lesser, &greater) {
                return false;
            }
            distinct = true;
        }
    }
    distinct
}

fn production_arity(production: &Production) -> usize {
    production
        .items
        .iter()
        .filter(|item| matches!(item, Item::NonTerminal(_)))
        .count()
}

fn variable_id(name: &str, next_anonymous: &mut usize) -> VariableId {
    if is_anonymous(name) {
        let id = VariableId::Anonymous(*next_anonymous);
        *next_anonymous += 1;
        id
    } else {
        VariableId::Named(name.to_owned())
    }
}

fn is_anonymous(name: &str) -> bool {
    name.starts_with('_')
        || name.starts_with("?_")
        || name.starts_with("!_")
        || name.starts_with("@_")
}

fn inference_error(message: impl Into<String>) -> ParseError {
    ParseError::SortInference {
        message: message.into(),
    }
}

/// The parse the per-position choice among well-sorted readings gives, computed on trees, for
/// testing the choice made before inference and its fallback
/// (`Grammar::infer_without_structural_preference`).
#[cfg(test)]
pub(crate) struct ExactStructuralChoice {
    /// The distinct terms of the admitted readings that are well sorted and put no rewrite
    /// inside a side of another or in a side condition, each lowered with its own typing.
    pub(crate) well_sorted: usize,
    /// The distinct terms of the well-sorted readings the per-position choice keeps, each
    /// lowered with its own typing: a reading is kept when no well-sorted reading that agrees
    /// with it everywhere outside one position ranks lower at that position.
    pub(crate) kept: Vec<Term>,
}

#[cfg(test)]
impl Grammar {
    /// [`ExactStructuralChoice`] for `input` parsed at `start`, by expanding every reading the
    /// relations admit, typing each alone and comparing every pair.
    pub(crate) fn exact_structural_choice(
        &self,
        start: &Sort,
        input: &str,
    ) -> ExactStructuralChoice {
        use super::{ParseProvenance, PredictionMode, PriorityFilter};
        let start_id = self
            .sort_id(start)
            .expect("the start sort is in the grammar");
        let mut scanner_cache = vec![None; input.len() + 1];
        let start_position = self.canonical_position(input, 0, &mut scanner_cache);
        let memos = std::cell::RefCell::new(super::disambiguation::PackedPriorityMemos::default());
        let recognition = self
            .recognize(
                start_id,
                start_position,
                input,
                ParseProvenance {
                    source: crate::provenance::SourceId(0),
                    base_offset: 0,
                },
                PredictionMode::Unfiltered,
                PriorityFilter::Enforced,
                None,
                false,
                &mut false,
                &mut super::WorkMeter::unlimited(),
                &mut scanner_cache,
                &memos,
            )
            .expect("the input is recognized");
        let Ok(admitted) =
            self.check_packed_forest(PackedTerm::ambiguity(recognition.parses), &memos)
        else {
            return ExactStructuralChoice {
                well_sorted: 0,
                kept: Vec::new(),
            };
        };
        let mut candidates = Vec::new();
        for tree in expand_packed_trees(&admitted) {
            let mut ranks = HashMap::new();
            let mut nested = false;
            self.exact_ranks(&tree, None, false, &mut Vec::new(), &mut ranks, &mut nested);
            if nested {
                continue;
            }
            if let Ok(inferred) =
                self.infer_packed_sorts(PackedTerm::from_parsed(&tree), start, false, &Ok)
            {
                candidates.push((tree, ranks, inferred));
            }
        }
        let distinct = |terms: &mut dyn Iterator<Item = &ParsedTerm>| {
            let mut distinct: Vec<Term> = Vec::new();
            for inferred in terms {
                let lowered = self
                    .lower_inferred(inferred.clone(), start)
                    .expect("a well-sorted reading lowers");
                if !distinct.iter().any(|term| term.identical(&lowered)) {
                    distinct.push(lowered);
                }
            }
            distinct
        };
        let well_sorted = distinct(&mut candidates.iter().map(|(_, _, inferred)| inferred)).len();
        let kept = distinct(
            &mut candidates
                .iter()
                .filter(|(tree, ranks, _)| {
                    !candidates.iter().any(|(other, other_ranks, _)| {
                        let mut frontier = Vec::new();
                        exact_frontier(tree, other, &mut Vec::new(), &mut frontier);
                        matches!(&frontier[..], [position] if other_ranks[position] < ranks[position])
                    })
                })
                .map(|(_, _, inferred)| inferred),
        );
        ExactStructuralChoice { well_sorted, kept }
    }

    /// The rank of every position of `tree` standing at `place`, by its path, and whether a
    /// rewrite stands in a term no rule changes (a side of another, a side condition).
    fn exact_ranks(
        &self,
        tree: &ParsedTerm,
        place: Option<super::disambiguation::StructuralPlace<'_>>,
        in_term: bool,
        path: &mut Vec<usize>,
        ranks: &mut HashMap<Vec<usize>, u8>,
        nested: &mut bool,
    ) {
        let parts = self.structural_rank_parts(&PackedTerm::from_parsed(tree), place, in_term);
        let [rank] = parts.keys().copied().collect::<Vec<_>>()[..] else {
            panic!("a tree has one rank at a position");
        };
        *nested |= rank == 4;
        ranks.insert(path.clone(), rank);
        if let ParsedTerm::Production {
            production,
            children,
            ..
        } = tree
        {
            let context = self.structural_child_context(*production, place, in_term);
            for (index, child) in children.iter().enumerate() {
                let (place, in_term) = context.get(index).copied().unwrap_or((None, in_term));
                path.push(index);
                self.exact_ranks(child, place, in_term, path, ranks, nested);
                path.pop();
            }
        }
    }
}

/// The topmost positions at which two trees differ: a node of one production with equal
/// metadata in both is compared child by child, any other difference is a position.
#[cfg(test)]
fn exact_frontier(
    left: &ParsedTerm,
    right: &ParsedTerm,
    path: &mut Vec<usize>,
    frontier: &mut Vec<Vec<usize>>,
) {
    if left == right {
        return;
    }
    match (left, right) {
        (
            ParsedTerm::Production {
                production,
                children,
                metadata,
            },
            ParsedTerm::Production {
                production: other_production,
                children: other_children,
                metadata: other_metadata,
            },
        ) if production == other_production
            && metadata == other_metadata
            && children.len() == other_children.len() =>
        {
            for (index, (child, other)) in children.iter().zip(other_children).enumerate() {
                path.push(index);
                exact_frontier(child, other, path, frontier);
                path.pop();
            }
        }
        _ => frontier.push(path.clone()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::Attributes;
    use crate::kast::{Label, TermMetadata};

    use super::super::ParametricOrigin;

    fn nonterminal(sort: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(sort),
            name: None,
        }
    }

    /// The tests' split check by listing (`lower_each_tree_by_listing`, which a closure's
    /// lowering uses) builds and lowers the trees of a group one at a time and stops at the
    /// first that lowers differently from the first tree, so a refusal pays for no later tree:
    /// here the forest has 2^32 trees, and its first two differ in their last leaf.
    #[test]
    fn the_split_check_stops_at_the_first_tree_that_lowers_differently() {
        let leaves = |names: &[&str]| {
            PackedTerm::ambiguity(
                names
                    .iter()
                    .map(|name| PackedTerm::leaf(Term::variable(*name)))
                    .collect(),
            )
        };
        let mut forest = leaves(&["X", "Y"]);
        for _ in 0..5 {
            forest = PackedTerm::production(
                0,
                vec![Rc::clone(&forest), Rc::clone(&forest)],
                TermMetadata::default(),
            );
        }
        assert_eq!(packed_tree_count(&forest), 1 << 32);
        let lowered = std::cell::Cell::new(0);
        let lower = |tree: ParsedTerm| {
            lowered.set(lowered.get() + 1);
            Ok::<_, ParseError>(tree)
        };
        assert_eq!(lower.lower_each_tree(&forest), Ok(None));
        assert_eq!(lowered.get(), 2);
        lowered.set(0);
        let forest = leaves(&["X", "Y", "Z"]);
        let same = |_: ParsedTerm| {
            lowered.set(lowered.get() + 1);
            Ok::<_, ParseError>(ParsedTerm::Term(Term::variable("X")))
        };
        assert!(matches!(same.lower_each_tree(&forest), Ok(Some(_))));
        assert_eq!(lowered.get(), 3);
    }

    fn parametric_rewrite_grammar() -> (Grammar, usize, usize, usize, usize) {
        let mut grammar = Grammar::default();
        let constant = |grammar: &mut Grammar, sort: &str, label: &str| {
            let index = grammar.productions.len();
            grammar
                .add(
                    Sort::new(sort),
                    vec![ProductionItem::Terminal(label.into())],
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
            index
        };
        let a = constant(&mut grammar, "A", "a");
        let b = constant(&mut grammar, "B", "b");
        let foo = grammar.productions.len();
        grammar
            .add(
                Sort::new("Foo"),
                vec![nonterminal("Base")],
                Some(Label::new("foo")),
                false,
                false,
            )
            .unwrap();
        let rewrite = grammar.productions.len();
        grammar
            .add(
                Sort::new("Base"),
                vec![nonterminal("Base"), nonterminal("Base")],
                Some(Label::new("#KRewrite")),
                false,
                false,
            )
            .unwrap();
        let parameter = Sort::new("S");
        grammar.productions[rewrite].parametric_origin = Some(ParametricOrigin {
            label: Some(Label::new("#KRewrite")),
            parameters: vec![parameter.clone()],
            result: parameter.clone(),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal("=>".into()),
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
            ],
            attributes: Attributes::default(),
            substitution: BTreeMap::from([(parameter, Sort::new("Base"))]),
        });
        grammar.subsort_relations.extend([
            (Sort::new("A"), Sort::new("Base")),
            (Sort::new("B"), Sort::new("Base")),
            (Sort::new("Base"), Sort::new("K")),
            (Sort::new("Foo"), Sort::new("K")),
        ]);
        (grammar, a, b, foo, rewrite)
    }

    fn production(production: usize, children: Vec<ParsedTerm>) -> ParsedTerm {
        ParsedTerm::Production {
            production,
            children,
            metadata: TermMetadata::default(),
        }
    }

    fn packed_production(production: usize, children: Vec<Rc<PackedTerm>>) -> Rc<PackedTerm> {
        PackedTerm::production(production, children, TermMetadata::default())
    }

    #[test]
    fn rewrite_rules_without_ambiguity_take_the_portable_path() {
        let (grammar, a, b, _, rewrite) = parametric_rewrite_grammar();
        let forest = packed_production(
            rewrite,
            vec![packed_production(a, vec![]), packed_production(b, vec![])],
        );

        assert!(grammar.packed_sort_inference_supported(&forest));
        assert!(grammar.sort_inference_supported(&forest.unpack()));
        assert!(
            !grammar.packed_sort_inference_supported(&PackedTerm::ambiguity(BTreeSet::from([
                forest,
                packed_production(a, vec![])
            ]),))
        );
        assert!(
            !grammar.packed_sort_inference_supported(&PackedTerm::leaf(Term::Token {
                token: "1p6".into(),
                sort: Sort::with_parameters("MInt", vec![Sort::new("6")]),
            },))
        );
    }

    #[test]
    fn portable_anywhere_bound_applies_to_the_top_rewrite_only() {
        let (grammar, a, b, foo, rewrite) = parametric_rewrite_grammar();
        let leaf = |index| production(index, vec![]);
        let nested = production(rewrite, vec![leaf(a), leaf(b)]);
        let lhs = production(foo, vec![nested]);
        let rhs = production(foo, vec![leaf(b)]);
        let body = production(rewrite, vec![lhs, rhs]);

        grammar
            .infer_sorts_portable(body, &Sort::new("K"), true)
            .expect("the nested rewrite gets only its ordinary parameter bounds");

        let widening = production(rewrite, vec![leaf(a), leaf(b)]);
        grammar
            .infer_sorts_portable(widening, &Sort::new("K"), true)
            .expect_err("the top rewrite RHS cannot widen beyond its declared LHS sort");
    }

    #[test]
    fn portable_function_bound_uses_the_inferred_parametric_lhs_sort() {
        let mut grammar = Grammar::default();
        let false_token = grammar.productions.len();
        grammar
            .add(
                Sort::new("Bool"),
                vec![ProductionItem::Terminal("false".into())],
                Some(Label::new("false")),
                false,
                false,
            )
            .unwrap();
        let k_value = grammar.productions.len();
        grammar
            .add(
                Sort::new("K"),
                vec![ProductionItem::Terminal("k".into())],
                Some(Label::new("k")),
                false,
                false,
            )
            .unwrap();
        let equals = grammar.productions.len();
        grammar
            .add(
                Sort::new("Bag"),
                vec![nonterminal("K"), nonterminal("K")],
                Some(Label::new("#Equals")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[equals].function = true;
        let operand = Sort::new("S");
        let result = Sort::new("R");
        grammar.productions[equals].parametric_origin = Some(ParametricOrigin {
            label: Some(Label::new("#Equals")),
            parameters: vec![operand.clone(), result.clone()],
            result: result.clone(),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: operand.clone(),
                    name: None,
                },
                ProductionItem::NonTerminal {
                    sort: operand.clone(),
                    name: None,
                },
            ],
            attributes: Attributes::default(),
            substitution: BTreeMap::from([(operand, Sort::new("K")), (result, Sort::new("Bag"))]),
        });
        let rewrite = grammar.productions.len();
        grammar
            .add(
                Sort::new("K"),
                vec![nonterminal("K"), nonterminal("K")],
                Some(Label::new("#KRewrite")),
                false,
                false,
            )
            .unwrap();
        let parameter = Sort::new("P");
        grammar.productions[rewrite].parametric_origin = Some(ParametricOrigin {
            label: Some(Label::new("#KRewrite")),
            parameters: vec![parameter.clone()],
            result: parameter.clone(),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
            ],
            attributes: Attributes::default(),
            substitution: BTreeMap::from([(parameter, Sort::new("K"))]),
        });
        grammar.subsort_relations.extend([
            (Sort::new("Bool"), Sort::new("K")),
            (Sort::new("K"), Sort::new("Bag")),
        ]);
        let lhs = production(
            equals,
            vec![
                production(false_token, vec![]),
                production(false_token, vec![]),
            ],
        );
        let body = production(rewrite, vec![lhs, production(k_value, vec![])]);

        let inferred = grammar
            .infer_sorts_portable(body, &Sort::new("#RuleBody"), false)
            .unwrap();
        let ParsedParts::InstantiatedProduction {
            parameters,
            children,
            ..
        } = inferred.into_parts()
        else {
            panic!("the rewrite should retain its inferred parameter")
        };
        assert_eq!(parameters, [Sort::new("K")]);
        assert!(matches!(
            &children[0],
            ParsedTerm::InstantiatedProduction { parameters, .. }
                if parameters == &[Sort::new("K"), Sort::new("K")]
        ));
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn checked_mode_requires_exact_cross_engine_agreement() {
        let x = ParsedTerm::Term(Term::variable("X"));
        let y = ParsedTerm::Term(Term::variable("Y"));

        assert_eq!(
            checked_inference_result(Ok(x.clone()), Ok(x.clone())),
            Ok(x.clone())
        );
        assert!(matches!(
            checked_inference_result(
                Err(inference_error("portable rejection")),
                Err(inference_error("Z3 rejection")),
            ),
            Err(ParseError::SortInference { ref message }) if message == "portable rejection"
        ));
        assert_eq!(
            checked_inference_result(Ok(x.clone()), Ok(y.clone())),
            Err(ParseError::InferenceEngineDisagreement {
                portable: Ok(format!("{x:?}")),
                z3: Ok(format!("{y:?}")),
                ambiguous_parse: false,
            })
        );
        assert_eq!(
            checked_inference_result(Ok(x.clone()), Err(inference_error("Z3 rejection"))),
            Err(ParseError::InferenceEngineDisagreement {
                portable: Ok(format!("{x:?}")),
                z3: Err("Z3 rejection".to_owned()),
                ambiguous_parse: false,
            })
        );
        assert_eq!(
            checked_inference_result(Err(inference_error("portable rejection")), Ok(y.clone())),
            Err(ParseError::InferenceEngineDisagreement {
                portable: Err("portable rejection".to_owned()),
                z3: Ok(format!("{y:?}")),
                ambiguous_parse: false,
            })
        );
    }

    /// A disagreement is its own outcome, not a sort-inference rejection: a caller that expects
    /// `ParseError::SortInference` must not accept a term that one engine accepted, or that the
    /// engines inferred differently. The message text of each disagreement is unchanged.
    #[cfg(feature = "z3-inference")]
    #[test]
    fn checked_mode_reports_a_disagreement_apart_from_a_sort_inference_rejection() {
        let x = ParsedTerm::Term(Term::variable("X"));
        let y = ParsedTerm::Term(Term::variable("Y"));
        let s = || Term::apply("s", Vec::new());
        let t = || Term::apply("t", Vec::new());
        let rejection = |engine: &str| inference_error(format!("{engine} rejection"));

        let outcomes: [(Result<(), ParseError>, String); 6] = [
            (
                checked_inference_result(Ok(x.clone()), Ok(y.clone())).map(drop),
                format!(
                    "portable and Z3 sort inference produced different terms: portable {x:?}; \
                     Z3 {y:?}"
                ),
            ),
            (
                checked_inference_result(Ok(x.clone()), Err(rejection("Z3"))).map(drop),
                format!(
                    "portable and Z3 sort inference disagree: portable accepted {x:?}; Z3 \
                     rejected with Z3 rejection"
                ),
            ),
            (
                checked_inference_result(Err(rejection("portable")), Ok(y.clone())).map(drop),
                format!(
                    "portable and Z3 sort inference disagree: portable rejected with portable \
                     rejection; Z3 accepted {y:?}"
                ),
            ),
            (
                checked_lowered_result(Ok(s()), Ok(t())).map(drop),
                format!(
                    "portable and Z3 sort inference lowered an ambiguous parse to different \
                     terms: portable {:?}; Z3 {:?}",
                    s(),
                    t()
                ),
            ),
            (
                checked_lowered_result(Ok(s()), Err(rejection("Z3"))).map(drop),
                format!(
                    "portable and Z3 sort inference disagree on an ambiguous parse: portable \
                     lowered to {:?}; Z3 rejected with Z3 rejection",
                    s()
                ),
            ),
            (
                checked_lowered_result(Err(rejection("portable")), Ok(t())).map(drop),
                format!(
                    "portable and Z3 sort inference disagree on an ambiguous parse: portable \
                     rejected with portable rejection; Z3 lowered to {:?}",
                    t()
                ),
            ),
        ];
        for (outcome, text) in outcomes {
            assert!(
                !matches!(outcome, Ok(()) | Err(ParseError::SortInference { .. })),
                "{outcome:?}"
            );
            assert_eq!(outcome.unwrap_err().to_string(), text);
        }
    }

    /// `Item ::= Big` (`big`) and `Item ::= Small` (`small`) with `Small < Big`,
    /// `Good ::= Item ... Item` with `arity` items, and the semantic casts that record an
    /// inferred variable sort.
    fn independent_ambiguity_grammar(arity: usize) -> (Grammar, usize, usize, usize) {
        let mut grammar = Grammar::default();
        let add = |grammar: &mut Grammar, result: &str, items, label: &str| {
            let index = grammar.productions.len();
            grammar
                .add(
                    Sort::new(result),
                    items,
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
            index
        };
        let big = add(&mut grammar, "Item", vec![nonterminal("Big")], "big");
        let small = add(&mut grammar, "Item", vec![nonterminal("Small")], "small");
        let sequence = add(
            &mut grammar,
            "Good",
            (0..arity).map(|_| nonterminal("Item")).collect(),
            "sequence",
        );
        for sort in ["Big", "Small"] {
            add(
                &mut grammar,
                sort,
                vec![nonterminal("K")],
                &format!("#SemanticCastTo{sort}"),
            );
        }
        grammar.subsort_relations.extend([
            (Sort::new("Small"), Sort::new("Big")),
            (Sort::new("Big"), Sort::new("K")),
            (Sort::new("Item"), Sort::new("K")),
            (Sort::new("Good"), Sort::new("K")),
        ]);
        (grammar, big, small, sequence)
    }

    /// A forest of `arity` independent binary ambiguities, `2^arity` complete trees: item `i`
    /// is `big(Yi)` or `small(Yi)`.
    fn independent_ambiguities(arity: usize) -> (Grammar, Rc<PackedTerm>) {
        let (grammar, big, small, sequence) = independent_ambiguity_grammar(arity);
        let items = (0..arity)
            .map(|index| {
                let variable = || PackedTerm::leaf(Term::variable(format!("Y{index}")));
                PackedTerm::ambiguity(BTreeSet::from([
                    packed_production(big, vec![variable()]),
                    packed_production(small, vec![variable()]),
                ]))
            })
            .collect();
        (grammar, packed_production(sequence, items))
    }

    /// The complete trees of a decision's result, as a set: the forest decision and the
    /// per-tree decision pack the same trees differently.
    fn decided_trees(
        grammar: &Grammar,
        decided: &Result<ParsedTerm, ParseError>,
    ) -> Result<BTreeSet<ParsedTerm>, ParseError> {
        decided
            .as_ref()
            .map(|term| {
                expand_packed_trees(&PackedTerm::from_parsed(term))
                    .into_iter()
                    .map(|tree| grammar.erase_bracket_instances(tree))
                    .collect()
            })
            .map_err(Clone::clone)
    }

    /// The forest decision and the per-tree decision keep the same trees of `forest`, or reject
    /// it alike; where the per-tree decision refuses because a tree's typing has incomparable
    /// candidates while another of its variables has no sort, the forest decision may decide.
    pub(super) fn assert_forest_decision_agrees(
        grammar: &Grammar,
        forest: &Rc<PackedTerm>,
        top: &Sort,
        anywhere: bool,
    ) {
        let forest_decision = decided_trees(
            grammar,
            &grammar.infer_ambiguous_sorts_portable(forest, top, anywhere, &Ok),
        );
        let per_tree = decided_trees(
            grammar,
            &grammar.infer_ambiguous_sorts_per_tree(forest, top, anywhere, &Ok),
        );
        // Up to the instances of brackets, the forest decision keeps a subset of the trees the
        // per-tree decision keeps (`Grammar::check_forest_decision`).
        match (&forest_decision, &per_tree) {
            (_, Err(ParseError::Z3InferenceRequired { .. })) => {}
            (Ok(forest_trees), Ok(per_tree_trees)) => {
                assert!(
                    !forest_trees.is_empty() && forest_trees.is_subset(per_tree_trees),
                    "{forest:?}"
                );
                let readings = |trees: &BTreeSet<ParsedTerm>| {
                    trees
                        .iter()
                        .map(|tree| super::erase_instances(tree.clone()))
                        .collect::<BTreeSet<_>>()
                };
                assert_eq!(
                    readings(forest_trees),
                    readings(per_tree_trees),
                    "{forest:?}"
                );
            }
            _ => assert_eq!(forest_decision, per_tree, "{forest:?}"),
        }
    }

    #[test]
    fn independent_ambiguities_are_decided_on_the_forest() {
        // Each item's ambiguity chooses its own variable's sort, so the forest has `2^arity`
        // trees but one maximal typing at each item: the forest decision keeps the all-`big`
        // tree in time linear in the forest.
        let top = Sort::new("Good");
        for arity in [1, 2, 5] {
            let (grammar, forest) = independent_ambiguities(arity);
            assert_forest_decision_agrees(&grammar, &forest, &top, false);
        }
        let (grammar, forest) = independent_ambiguities(64);
        assert!(!grammar.packed_sort_inference_supported(&forest));
        let decided = grammar
            .infer_ambiguous_sorts_portable(&forest, &top, false, &Ok)
            .expect("the all-`big` tree's typing strictly exceeds every other tree's");
        assert_eq!(
            Grammar::ambiguity_count(&decided),
            1,
            "one tree survives: {decided:?}"
        );
    }

    /// A grammar in which a parametric rewrite `{S} S ::= S "=>" S` stands inside brackets at
    /// two unrelated sorts `B` and `C` above `A`, below a `g(D)` with `B, C < D`, and a forest
    /// of `positions` such items, `g(( a => a ))` each, read through either bracket: `2^positions`
    /// trees of one typing (there is no variable), whose rewrites instantiate at `B` or `C` as
    /// the bracket around them does. The brackets are no family (`#bracket:B`, `#bracket:C`),
    /// so neither instance shadows the other, and every tree lowers to the same term: a
    /// rewrite's term records no sort, and a bracket denotes its child.
    fn bracketed_rewrites(positions: usize) -> (Grammar, Rc<PackedTerm>) {
        let mut grammar = Grammar::default();
        let add = |grammar: &mut Grammar, result: &str, items, label: Option<&str>| {
            let index = grammar.productions.len();
            grammar
                .add(
                    Sort::new(result),
                    items,
                    label.map(Label::new),
                    false,
                    false,
                )
                .unwrap();
            index
        };
        let terminal = |text: &str| ProductionItem::Terminal(text.into());
        let a = add(&mut grammar, "A", vec![terminal("a")], Some("a"));
        let mut brackets = Vec::new();
        for sort in ["B", "C"] {
            brackets.push(grammar.productions.len());
            grammar
                .add_bracket(
                    Sort::new(sort),
                    vec![terminal("("), nonterminal(sort), terminal(")")],
                    None,
                )
                .unwrap();
        }
        let rewrite = add(
            &mut grammar,
            "D",
            vec![nonterminal("D"), terminal("=>"), nonterminal("D")],
            Some("#KRewrite"),
        );
        let parameter = Sort::new("S");
        grammar.productions[rewrite].parametric_origin = Some(ParametricOrigin {
            label: Some(Label::new("#KRewrite")),
            parameters: vec![parameter.clone()],
            result: parameter.clone(),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal("=>".into()),
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
            ],
            attributes: Attributes::default(),
            substitution: BTreeMap::from([(parameter, Sort::new("D"))]),
        });
        let g = add(
            &mut grammar,
            "Item",
            vec![
                terminal("g"),
                terminal("("),
                nonterminal("D"),
                terminal(")"),
            ],
            Some("g"),
        );
        let sequence = add(
            &mut grammar,
            "Good",
            (0..positions).map(|_| nonterminal("Item")).collect(),
            Some("sequence"),
        );
        grammar.subsort_relations.extend([
            (Sort::new("A"), Sort::new("B")),
            (Sort::new("A"), Sort::new("C")),
            (Sort::new("B"), Sort::new("D")),
            (Sort::new("C"), Sort::new("D")),
            (Sort::new("D"), Sort::new("K")),
            (Sort::new("Item"), Sort::new("K")),
            (Sort::new("Good"), Sort::new("K")),
        ]);
        let leaf = packed_production(a, Vec::new());
        let rewritten = packed_production(rewrite, vec![Rc::clone(&leaf), leaf]);
        let item = packed_production(
            g,
            vec![PackedTerm::ambiguity(
                brackets
                    .iter()
                    .map(|bracket| packed_production(*bracket, vec![Rc::clone(&rewritten)]))
                    .collect(),
            )],
        );
        let forest = packed_production(sequence, vec![item; positions]);
        (grammar, forest)
    }

    /// The trees of a typing group whose rewrites instantiate at different sorts are lowered
    /// each alone on the forest: at 64 positions (2^64 trees, more than `usize` counts) the
    /// group is decided, without unpacking a node, and each further position costs the same
    /// number of node lowerings, so the cost is linear in the forest. At three positions the
    /// test build checks the forest's per-tree lowering against lowering each tree alone
    /// (`InferredLowering`), and the z3 build checks the decision against Z3's.
    #[test]
    fn a_parameter_split_group_is_lowered_tree_by_tree_on_the_forest() {
        let top = Sort::new("Good");
        let expected = |positions: usize| {
            let item = "g(a(.KList)=>a(.KList))";
            format!("sequence({})", vec![item; positions].join(","))
        };
        let mut lowerings = Vec::new();
        for positions in [3, 16, 32, 64] {
            let (grammar, forest) = bracketed_rewrites(positions);
            let lower = super::super::InferredLowering {
                grammar: &grammar,
                start: &top,
            };
            let groups = grammar
                .decide_forest(&forest, &top, false, &|| ParseError::Z3InferenceRequired {
                    ambiguity: true,
                    parametric_sorts: false,
                })
                .expect("the forest has one typing");
            assert!(
                groups.iter().any(|group| group.parameter_split),
                "the trees of the typing instantiate the rewrite at `B` and at `C`"
            );
            super::super::forest::reset_unpacked_nodes();
            super::super::disambiguation::tests::LOWERINGS.with(|count| count.set(0));

            let decided = grammar.infer_ambiguous_sorts_portable(&forest, &top, false, &lower);

            let decided = decided.expect("every tree lowers to one term");
            assert_eq!(decided.to_string(), expected(positions));
            if positions > 3 {
                assert_eq!(super::super::forest::unpacked_nodes(), 0);
            }
            lowerings
                .push(super::super::disambiguation::tests::LOWERINGS.with(std::cell::Cell::get));
            #[cfg(feature = "z3-inference")]
            if positions == 3 {
                let z3 = grammar
                    .infer_packed_forest_z3(Rc::clone(&forest), &top, false)
                    .and_then(|inferred| lower.lower_forest(&inferred))
                    .expect("Z3 decides the forest");
                assert!(z3.identical(&decided), "Z3: {z3}, portable: {decided}");
            }
        }
        // 16, 32 and 64 positions: the cost of 16 positions, then of 32 more, is the same per
        // position.
        assert_eq!(
            lowerings[3] - lowerings[2],
            2 * (lowerings[2] - lowerings[1])
        );
    }

    #[test]
    fn forest_decisions_over_one_grammar_share_its_sort_table() {
        // The sorts' numbering and their down and up sets are functions of the subsort order:
        // the first decision fills the grammar's table, a second decision of the same forest
        // computes no set again, and a change to the relation discards the table with the order.
        let top = Sort::new("Good");
        let (mut grammar, forest) = independent_ambiguities(2);
        let decide = |grammar: &Grammar| {
            grammar
                .infer_ambiguous_sorts_portable(&forest, &top, false, &Ok)
                .expect("the all-`big` tree is kept")
        };
        let first = decide(&grammar);
        let table = grammar
            .subsort_relations
            .sort_table
            .get()
            .expect("the decision built the grammar's table");
        let computed = table.computed_sets();
        assert!(computed > 0, "the decision read no sort's bounds");
        let table: *const SortTable = table;
        assert_eq!(decide(&grammar), first);
        let shared = grammar
            .subsort_relations
            .sort_table
            .get()
            .expect("the table is kept");
        assert!(
            std::ptr::eq(table, shared),
            "the second decision built another table"
        );
        assert_eq!(shared.computed_sets(), computed);
        grammar
            .subsort_relations
            .insert((Sort::new("Fresh"), Sort::new("Good")));
        assert!(grammar.subsort_relations.sort_table.get().is_none());
    }

    /// Two well-sorted trees, `big(Y)` and `small(Y)` beside `big(_)`, whose anonymous variable
    /// has no span to identify it across trees, so the portable decision refuses the forest.
    fn unidentified_anonymous_forest() -> (Grammar, Rc<PackedTerm>) {
        let (grammar, big, small, sequence) = independent_ambiguity_grammar(2);
        let variable = || PackedTerm::leaf(Term::variable("Y"));
        let item = PackedTerm::ambiguity(BTreeSet::from([
            packed_production(big, vec![variable()]),
            packed_production(small, vec![variable()]),
        ]));
        let anonymous = packed_production(big, vec![PackedTerm::leaf(Term::variable("_"))]);
        (grammar, packed_production(sequence, vec![item, anonymous]))
    }

    #[test]
    fn an_anonymous_variable_without_a_span_is_refused_beside_two_well_sorted_trees() {
        let (grammar, forest) = unidentified_anonymous_forest();
        let top = Sort::new("Good");
        assert_eq!(
            grammar.infer_ambiguous_sorts_portable(&forest, &top, false, &Ok),
            Err(ParseError::Z3InferenceRequired {
                ambiguity: true,
                parametric_sorts: false,
            })
        );
        assert_forest_decision_agrees(&grammar, &forest, &top, false);
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn checked_mode_accepts_trees_that_differ_only_in_a_bracket() {
        // `(s)` read through the `Big` bracket or through the `Small` bracket: two well-sorted
        // trees with one (empty) typing that lower to the one term `s`.
        let mut grammar = Grammar::default();
        let add = |grammar: &mut Grammar, result: &str, items, label: &str| {
            let index = grammar.productions.len();
            grammar
                .add(
                    Sort::new(result),
                    items,
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
            index
        };
        let constant = add(
            &mut grammar,
            "Small",
            vec![ProductionItem::Terminal("s".into())],
            "s",
        );
        let bracket = |sort: &str| {
            vec![
                ProductionItem::Terminal("(".into()),
                nonterminal(sort),
                ProductionItem::Terminal(")".into()),
            ]
        };
        let big_bracket = add(&mut grammar, "Big", bracket("Big"), "bracketBig");
        let small_bracket = add(&mut grammar, "Small", bracket("Small"), "bracketSmall");
        grammar.productions[big_bracket].bracket = true;
        grammar.productions[small_bracket].bracket = true;
        grammar.subsort_relations.extend([
            (Sort::new("Small"), Sort::new("Big")),
            (Sort::new("Big"), Sort::new("K")),
        ]);
        let forest = PackedTerm::ambiguity(BTreeSet::from([
            packed_production(big_bracket, vec![packed_production(constant, vec![])]),
            packed_production(small_bracket, vec![packed_production(constant, vec![])]),
        ]));
        let top = Sort::new("Big");

        let portable = grammar
            .infer_ambiguous_sorts_portable(&forest, &top, false, &Ok)
            .expect("both bracket readings are well-sorted");
        assert_eq!(Grammar::ambiguity_count(&portable), 2, "{portable:?}");
        let checked = grammar
            .checked_ambiguous_parse(&forest, &top, false, &|tree| {
                grammar.lower_inferred(tree, &top)
            })
            .expect("the portable engine decides the forest");
        assert_eq!(checked, Ok(Term::apply("s", Vec::new())));
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn checked_mode_returns_z3s_result_on_a_forest_the_portable_decision_refuses() {
        // An anonymous variable without a span beside two well-sorted trees: the portable
        // decision refuses the forest, so checked mode has nothing to compare and returns what
        // the default path returns, which is Z3's decision. Returning nothing instead would make
        // the caller run the portable decision again on the default path before reaching Z3.
        let (grammar, forest) = unidentified_anonymous_forest();
        let top = Sort::new("Good");
        let lower = |tree| grammar.lower_inferred(tree, &top);
        assert!(matches!(
            grammar.infer_ambiguous_sorts_portable(&forest, &top, false, &lower),
            Err(ParseError::Z3InferenceRequired { .. })
        ));
        let checked = grammar
            .checked_ambiguous_parse(&forest, &top, false, &lower)
            .expect("checked mode decides every forest outside the unambiguous path");
        let default = grammar.infer_packed_sorts(Rc::clone(&forest), &top, false, &lower);
        assert!(default.is_ok(), "{default:?}");
        match (checked, default) {
            (Ok(checked), Ok(default)) => assert!(checked.identical(&default), "{checked:?}"),
            other => panic!("{other:?}"),
        }
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn checked_mode_on_ambiguous_forests_compares_lowered_terms_and_returns_z3s() {
        let s = || Term::apply("s", Vec::new());
        let annotated = || {
            s().with_metadata(TermMetadata {
                sort: Some(Sort::new("Small")),
                ..TermMetadata::default()
            })
        };

        assert_eq!(checked_lowered_result(Ok(s()), Ok(s())), Ok(s()));
        assert!(matches!(
            checked_lowered_result(
                Err(inference_error("portable rejection")),
                Err(inference_error("Z3 rejection")),
            ),
            Err(ParseError::SortInference { ref message }) if message == "Z3 rejection"
        ));
        let ambiguity = |entries: usize| ParseError::Ambiguous {
            alternatives: (0..entries)
                .map(|entry| super::super::AmbiguousParse {
                    production: None,
                    term: entry.to_string(),
                    more_with_same_root: false,
                })
                .collect(),
            span: None,
            places: Vec::new(),
        };
        assert_eq!(
            checked_lowered_result(Err(ambiguity(2)), Err(ambiguity(2))),
            Err(ambiguity(2))
        );
        assert_eq!(
            checked_lowered_result(Err(ambiguity(14)), Err(ambiguity(2))),
            Err(ParseError::InferenceEngineDisagreement {
                portable: Err(ambiguity(14).to_string()),
                z3: Err(ambiguity(2).to_string()),
                ambiguous_parse: true,
            })
        );
        assert!(matches!(
            checked_lowered_result(Err(ambiguity(2)), Err(inference_error("Z3 rejection"))),
            Err(ParseError::InferenceEngineDisagreement { .. })
        ));
        assert_eq!(
            checked_lowered_result(Ok(s()), Ok(annotated())),
            Err(ParseError::InferenceEngineDisagreement {
                portable: Ok(format!("{:?}", s())),
                z3: Ok(format!("{:?}", annotated())),
                ambiguous_parse: true,
            })
        );
        assert_eq!(
            checked_lowered_result(Ok(s()), Err(inference_error("Z3 rejection"))),
            Err(ParseError::InferenceEngineDisagreement {
                portable: Ok(format!("{:?}", s())),
                z3: Err("Z3 rejection".to_owned()),
                ambiguous_parse: true,
            })
        );
        assert_eq!(
            checked_lowered_result(Err(inference_error("portable rejection")), Ok(s())),
            Err(ParseError::InferenceEngineDisagreement {
                portable: Err("portable rejection".to_owned()),
                z3: Ok(format!("{:?}", s())),
                ambiguous_parse: true,
            })
        );
    }
}

//! ```toml algorithm
//! id = "parser.inference.portable"
//! name = "portable sort inference by bound propagation"
//! sites = ["Grammar::infer_sorts_portable", "Grammar::infer_packed_sorts", "Grammar::infer_sorts", "Grammar::infer_ambiguous_sorts_portable"]
//! variable = "V = sort-bound vertices; E = bound edges; q = simple bound-edge paths from one variable, exponential in V in the worst case; T = complete trees of an ambiguous forest, at most PORTABLE_AMBIGUITY_TREE_LIMIT"
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
//! bound = "O(T x V x E) for the per-tree inferences plus O(T^2 x V) order checks for the maximality filter"
//!
//! [[cost]]
//! mode = "variable realization"
//! bound = "O(V x q) concrete_bounds calls, plus one PartialOrder::new over the subsort relations per inference"
//! ```
//!
//! Portable bound-propagation sort inference for monomorphic trees and forests.
//!
//! Constraint propagation saturates a finite sort-bound graph, worst-case O(V * E).
//! An ambiguous monomorphic forest with at most `PORTABLE_AMBIGUITY_TREE_LIMIT` complete trees
//! is decided by typing each tree and keeping the trees whose typing no other tree's typing
//! strictly exceeds (`Grammar::infer_ambiguous_sorts_portable`). Parametric forests, larger
//! forests, trees without a greatest typing and trees of one typing that instantiate formal
//! parameters differently and stay ambiguous after lowering dispatch to Z3; checked mode runs both engines as
//! oracles, comparing inferred trees on unambiguous forests and lowered terms on ambiguous
//! ones. `Counter::ParserPortableInferences` counts portable inference attempts, one per tree.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::definition::{PartialOrder, ProductionItem};
use crate::kast::{FrontendSort, GeneratedLabel, InternalLabel, Label, Sort, Term, TermSpan};
use crate::names::BuiltinSort;

use super::{
    Grammar, Item, PackedNode, PackedTerm, ParseError, ParsedTerm, Production,
    inferred_variable_name,
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

/// The largest number of complete trees for which the portable engine decides an ambiguous
/// monomorphic forest (`Grammar::infer_ambiguous_sorts_portable`).
///
/// The count is the product of the alternative counts along the forest, so it grows
/// exponentially in the number of independent ambiguity nodes, and the decision costs one
/// portable inference per tree. Z3 encodes the same forest once with its subtrees shared, so a
/// larger forest stays at the `ParseError::Z3InferenceRequired` boundary instead of making the
/// portable build pay an exponential expansion. 64 trees are six independent binary
/// ambiguities, ten times the six trees of the largest ambiguous forest in the embedded prelude.
const PORTABLE_AMBIGUITY_TREE_LIMIT: usize = 64;

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
/// variable by its name, an anonymous one by its source occurrence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum TypingVariable {
    Named(String),
    Anonymous(TermSpan),
}

/// One tree typed by the portable engine, with the sorts it realized for the tree's variables.
struct TypedTree {
    term: ParsedTerm,
    typing: BTreeMap<TypingVariable, Sort>,
    /// An anonymous variable without a source span has no identity across trees.
    unidentified_variable: bool,
}

/// The kept trees of one maximal typing, factored into one term.
struct TypingGroup {
    term: Rc<PackedTerm>,
    /// Two of the trees instantiate the formal sort parameters of their productions
    /// differently (`parameter_instantiations`).
    parameters_differ: bool,
}

struct Solver<'a> {
    order: &'a PartialOrder<Sort>,
    bounds: Vec<Bounds>,
    variables: BTreeMap<VariableId, usize>,
    typing_variables: BTreeMap<VariableId, Option<TypingVariable>>,
    parameters: Vec<(String, Vec<usize>)>,
    constraint_cache: BTreeSet<(SortRef, SortRef)>,
    next_anonymous: usize,
}

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
        lower: impl Fn(ParsedTerm) -> Result<T, ParseError>,
    ) -> Result<T, ParseError> {
        if !self.packed_sort_inference_supported(&term) {
            // Z3 stays the engine for ambiguous forests in the z3 build; checked mode compares
            // the portable decision with it on lowered terms (`Grammar::checked_ambiguous_parse`).
            #[cfg(feature = "z3-inference")]
            return lower(self.infer_packed_sorts_z3(term, top_sort, explicitly_anywhere)?);
            #[cfg(not(feature = "z3-inference"))]
            return self.infer_ambiguous_sorts_portable(
                &term,
                top_sort,
                explicitly_anywhere,
                lower,
            );
        }
        let unpacked = term.unpack();
        lower(self.infer_sorts(unpacked, top_sort, explicitly_anywhere)?)
    }

    /// Checked mode on an ambiguous forest in the z3 build: `None` unless the forest is outside
    /// the unambiguous portable path and the portable decision decides it; otherwise both
    /// engines' results are lowered by `lower` and compared. The caller runs it only under
    /// `KRUST_TYPE_INFERENCE_MODE=checked` (`checked_inference_requested`).
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
        lower: impl Fn(ParsedTerm) -> Result<Term, ParseError>,
    ) -> Option<Result<Term, ParseError>> {
        if self.packed_sort_inference_supported(term) {
            return None;
        }
        let portable =
            self.infer_ambiguous_sorts_portable(term, top_sort, explicitly_anywhere, &lower);
        if matches!(portable, Err(ParseError::Z3InferenceRequired { .. })) {
            return None;
        }
        let z3 = self.infer_packed_sorts_z3(Rc::clone(term), top_sort, explicitly_anywhere);
        Some(checked_lowered_result(portable, z3.and_then(&lower)))
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
    /// preference over parameter instantiations that this decision does not model, so if that
    /// group alone does not lower to one term the forest is left to Z3 with
    /// `ParseError::Z3InferenceRequired`. An ambiguity between different maximal typings stays
    /// `ParseError::Ambiguous`.
    ///
    /// The decision is exact only under those premises, so it also returns
    /// `ParseError::Z3InferenceRequired` instead of deciding when a tree is parametric, when a
    /// tree's typing has incomparable candidates, when an anonymous variable has no source span
    /// to identify it across trees, and when the forest has more than
    /// `PORTABLE_AMBIGUITY_TREE_LIMIT` complete trees. When no tree is well-sorted, the first
    /// tree's rejection is returned.
    pub(super) fn infer_ambiguous_sorts_portable<T>(
        &self,
        term: &Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
        lower: impl Fn(ParsedTerm) -> Result<T, ParseError>,
    ) -> Result<T, ParseError> {
        let (ambiguity, parametric_sorts) = self.packed_z3_reasons(term);
        let required = || ParseError::Z3InferenceRequired {
            ambiguity,
            parametric_sorts,
        };
        if parametric_sorts || packed_tree_count(term) > PORTABLE_AMBIGUITY_TREE_LIMIT {
            return Err(required());
        }
        let groups = self.maximal_typing_groups(term, top_sort, explicitly_anywhere, required)?;
        let joined = |groups: Vec<Rc<PackedTerm>>| {
            self.factor_pre_inference_packed_ambiguities(PackedTerm::ambiguity(
                groups.into_iter().collect(),
            ))
            .unpack()
        };
        let undecided =
            |result: &Result<T, ParseError>| matches!(result, Err(ParseError::Ambiguous { .. }));
        if let [group] = groups.as_slice() {
            let result = lower(joined(vec![Rc::clone(&group.term)]));
            return if group.parameters_differ && undecided(&result) {
                Err(required())
            } else {
                result
            };
        }
        for group in groups.iter().filter(|group| group.parameters_differ) {
            if undecided(&lower(joined(vec![Rc::clone(&group.term)]))) {
                return Err(required());
            }
        }
        lower(joined(groups.into_iter().map(|group| group.term).collect()))
    }

    /// The well-sorted trees of an ambiguous monomorphic forest that no other tree's typing
    /// strictly exceeds, one factored group per maximal typing
    /// (`Grammar::infer_ambiguous_sorts_portable` gives the argument).
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
                    .any(|other| strictly_exceeds(&order, &top, &other.typing, &tree.typing))
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
                let instantiations = trees
                    .iter()
                    .map(parameter_instantiations)
                    .collect::<BTreeSet<_>>();
                TypingGroup {
                    parameters_differ: instantiations.len() > 1,
                    term: PackedTerm::from_parsed(&factor_trees(trees)),
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
        }

        supported(self, term, &mut HashSet::new())
    }

    fn packed_z3_reasons(&self, term: &Rc<PackedTerm>) -> (bool, bool) {
        fn reasons(
            grammar: &Grammar,
            term: &Rc<PackedTerm>,
            visited: &mut HashSet<*const PackedTerm>,
        ) -> (bool, bool) {
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
        }

        reasons(self, term, &mut HashSet::new())
    }

    pub(super) fn infer_sorts(
        &self,
        term: ParsedTerm,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<ParsedTerm, ParseError> {
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
        let mut solver = Solver::new(&order);
        let inferred = solver.infer(self, &term, anywhere_top, "root")?;
        // Synthetic rule-grammar result sorts describe parser context, not bounds on a
        // rewrite's formal result parameter. Concrete caller sorts remain real constraints.
        if is_real_ground_sort(top_sort) || !solver.is_parameter_ref(&inferred) {
            solver.constrain(inferred, SortRef::Concrete(top_sort.clone()))?;
        }
        let variable_sorts = solver.realize_variables()?;
        let parameter_sorts = solver.realize_parameters()?;
        let mut typing = BTreeMap::new();
        let mut unidentified_variable = false;
        for (id, sort) in &variable_sorts {
            match &solver.typing_variables[id] {
                Some(variable) => {
                    typing.insert(variable.clone(), sort.clone());
                }
                None => unidentified_variable = true,
            }
        }
        let mut next_anonymous = 0;
        let term = self
            .insert_inferred_casts(
                term,
                &variable_sorts,
                &parameter_sorts,
                None,
                &mut next_anonymous,
                "root",
            )
            .map_err(PortableError::Malformed)?;
        Ok(TypedTree {
            term,
            typing,
            unidentified_variable,
        })
    }

    fn sort_order(&self) -> Result<PartialOrder<Sort>, PortableError> {
        PartialOrder::new(self.subsort_relations.iter().cloned()).map_err(|cycle| {
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
        match term {
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
        }
    }

    #[cfg(not(feature = "z3-inference"))]
    fn z3_reasons(&self, term: &ParsedTerm) -> (bool, bool) {
        match term {
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
        }
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
        parameter_sorts: &BTreeMap<String, Vec<Sort>>,
        enclosing_cast: Option<&Sort>,
        next_anonymous: &mut usize,
        path: &str,
    ) -> Result<ParsedTerm, ParseError> {
        match term {
            ParsedTerm::Term(ref leaf) if inferred_variable_name(leaf).is_some() => {
                let Some(name) = inferred_variable_name(leaf) else {
                    unreachable!()
                };
                let id = variable_id(name, next_anonymous);
                let sort = variable_sorts.get(&id).ok_or_else(|| {
                    inference_error(format!("no inferred sort was produced for variable {name}"))
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
            ParsedTerm::Term(_) => Ok(term),
            ParsedTerm::Ambiguity(_) => Err(inference_error(
                "portable sort inference received an ambiguous parse forest",
            )),
            ParsedTerm::Production {
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
                let children = children
                    .into_iter()
                    .enumerate()
                    .map(|(index, child)| {
                        self.insert_inferred_casts(
                            child,
                            variable_sorts,
                            parameter_sorts,
                            cast_sort,
                            next_anonymous,
                            &format!("{path}_c{index}"),
                        )
                    })
                    .collect::<Result<_, _>>()?;
                if descriptor.parametric_origin.is_some() {
                    let parameters = parameter_sorts.get(path).cloned().ok_or_else(|| {
                        inference_error(format!(
                            "no inferred parameters were produced for production at {path}"
                        ))
                    })?;
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
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("portable inference cannot create instantiated productions")
            }
        }
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
            constraint_cache: BTreeSet::new(),
            next_anonymous: 0,
        }
    }

    fn infer(
        &mut self,
        grammar: &Grammar,
        term: &ParsedTerm,
        anywhere_top: Option<*const ParsedTerm>,
        path: &str,
    ) -> Result<SortRef, PortableError> {
        match term {
            ParsedTerm::Ambiguity(_) => Err(PortableError::Malformed(inference_error(
                "portable sort inference does not support ambiguous parse forests",
            ))),
            ParsedTerm::Term(term) => match (inferred_variable_name(term), term.unannotated()) {
                (Some(name), _) => self.variable(name, term),
                (None, Term::Token { sort, .. }) => Ok(SortRef::Concrete(sort.clone())),
                (None, _) => Err(PortableError::Malformed(inference_error(
                    "unexpected lowered KAST node in the concrete parse forest",
                ))),
            },
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
                    self.parameters.push((path.to_owned(), slots.clone()));
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
                    .enumerate()
                    .map(|(index, child)| {
                        self.infer(grammar, child, anywhere_top, &format!("{path}_c{index}"))
                    })
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
                                Item::NonTerminal(sort) => Some(SortRef::Concrete(sort.clone())),
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
                            let parse = &grammar.sorts[sort_id.expect("nonterminal has a sort id")];
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
                let anywhere_lhs_sort = (anywhere_top.is_some_and(|top| std::ptr::eq(term, top))
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
                        // Scala's inferencer treats every anonymous occurrence as having exactly
                        // the sort required by its context.  A mere upper bound is insufficient
                        // for parser sorts such as KItem, whose synthetic hierarchy is not always
                        // represented by an ordinary subsort production.
                        self.constrain(child.clone(), expected.clone())?;
                        self.constrain(expected, child)?;
                    } else if !(self.is_parameter_ref(&child)
                        && matches!(
                            &expected,
                            SortRef::Concrete(sort) if !is_real_ground_sort(sort)
                        ))
                    {
                        // Rule-grammar scaffolding sorts carry parser context, not semantic sort
                        // bounds for a formal production parameter. The Z3 engine and reference
                        // SimpleSub path likewise keep that parameter independent of the wrapper.
                        self.constrain(child, expected)?;
                    }
                }
                if let Some(lhs_sort) = anywhere_lhs_sort
                    && !matches!(&actual, SortRef::Concrete(sort) if !is_real_ground_sort(sort))
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
                }) && let (Some(child), Some(inner)) = (expected.first(), child_sorts.first())
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
                    if !matches!(inner, SortRef::Concrete(sort) if !is_real_ground_sort(sort)) {
                        self.constrain(child.clone(), inner.clone())?;
                    }
                }
                Ok(actual)
            }
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("instantiated productions are created after constraint solving")
            }
        }
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
                    .map(TypingVariable::Anonymous),
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
        self.parameters
            .iter()
            .any(|(_, slots)| slots.contains(variable))
    }

    fn constrain(&mut self, lesser: SortRef, greater: SortRef) -> Result<(), PortableError> {
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
    }

    fn realize_variables(&self) -> Result<BTreeMap<VariableId, Sort>, PortableError> {
        self.variables
            .iter()
            .map(|(id, variable)| {
                self.realize_variable(*variable)
                    .map(|sort| (id.clone(), sort))
            })
            .collect()
    }

    fn realize_parameters(&self) -> Result<BTreeMap<String, Vec<Sort>>, PortableError> {
        self.parameters
            .iter()
            .map(|(path, slots)| {
                slots
                    .iter()
                    .map(|slot| self.realize_variable(*slot))
                    .collect::<Result<Vec<_>, _>>()
                    .map(|sorts| (path.clone(), sorts))
            })
            .collect()
    }

    fn realize_variable(&self, variable: usize) -> Result<Sort, PortableError> {
        if self.bounds[variable].lower.is_empty() && self.bounds[variable].upper.is_empty() {
            return Ok(Sort::new("K"));
        }
        let upper = self.concrete_bounds(variable, true, &mut BTreeSet::new());
        let lower = self.concrete_bounds(variable, false, &mut BTreeSet::new());
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

    fn concrete_bounds(
        &self,
        variable: usize,
        upper: bool,
        visited: &mut BTreeSet<usize>,
    ) -> BTreeSet<Sort> {
        // Invariant: `visited` is the current DFS path; recursion follows one bound edge and
        // returns only reachable concrete sorts.
        if !visited.insert(variable) {
            return BTreeSet::new();
        }
        let bounds = if upper {
            &self.bounds[variable].upper
        } else {
            &self.bounds[variable].lower
        };
        bounds
            .iter()
            .flat_map(|bound| match bound {
                SortRef::Concrete(sort) => BTreeSet::from([sort.clone()]),
                SortRef::Variable(variable) => {
                    self.concrete_bounds(*variable, upper, &mut visited.clone())
                }
            })
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

fn is_real_ground_sort(sort: &Sort) -> bool {
    !sort.parameters.is_empty()
        || !super::is_parser_sort(sort)
        || sort.name == BuiltinSort::K.k_name()
        || sort.name == BuiltinSort::KItem.k_name()
        || sort.is_frontend(FrontendSort::KLabel)
        || sort.name.parse::<u64>().is_ok()
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
        (Ok(portable), Ok(z3)) => Err(inference_error(format!(
            "portable and Z3 sort inference produced different terms: portable {portable:?}; Z3 {z3:?}"
        ))),
        (Ok(portable), Err(z3)) => Err(inference_error(format!(
            "portable and Z3 sort inference disagree: portable accepted {portable:?}; Z3 rejected with {z3}"
        ))),
        (Err(portable), Ok(z3)) => Err(inference_error(format!(
            "portable and Z3 sort inference disagree: portable rejected with {portable}; Z3 accepted {z3:?}"
        ))),
    }
}

/// The lowered-term comparison of `Grammar::checked_ambiguous_parse`; returns Z3's result.
#[cfg(feature = "z3-inference")]
fn checked_lowered_result(
    portable: Result<Term, ParseError>,
    z3: Result<Term, ParseError>,
) -> Result<Term, ParseError> {
    match (portable, z3) {
        (Ok(portable), Ok(z3)) if portable.identical(&z3) => Ok(z3),
        (Err(_), Err(z3)) => Err(z3),
        (Ok(portable), Ok(z3)) => Err(inference_error(format!(
            "portable and Z3 sort inference lowered an ambiguous parse to different terms: \
             portable {portable:?}; Z3 {z3:?}"
        ))),
        (Ok(portable), Err(z3)) => Err(inference_error(format!(
            "portable and Z3 sort inference disagree on an ambiguous parse: portable lowered to \
             {portable:?}; Z3 rejected with {z3}"
        ))),
        (Err(portable), Ok(z3)) => Err(inference_error(format!(
            "portable and Z3 sort inference disagree on an ambiguous parse: portable rejected \
             with {portable}; Z3 lowered to {z3:?}"
        ))),
    }
}

/// The number of complete trees of a packed forest, saturating at `usize::MAX`. Shared nodes
/// are counted once each, so the count costs time linear in the forest's distinct nodes.
fn packed_tree_count(term: &Rc<PackedTerm>) -> usize {
    fn count(term: &Rc<PackedTerm>, memo: &mut HashMap<*const PackedTerm, usize>) -> usize {
        if let Some(count) = memo.get(&Rc::as_ptr(term)) {
            return *count;
        }
        let result = match &term.node {
            PackedNode::Term(_) => 1,
            PackedNode::Ambiguity(alternatives) => {
                alternatives.iter().fold(0usize, |total, alternative| {
                    total.saturating_add(count(alternative, memo))
                })
            }
            PackedNode::Production { children, .. }
            | PackedNode::InstantiatedProduction { children, .. } => {
                children.iter().fold(1usize, |total, child| {
                    total.saturating_mul(count(child, memo))
                })
            }
        };
        memo.insert(Rc::as_ptr(term), result);
        result
    }
    count(term, &mut HashMap::new())
}

/// The complete trees of a packed forest. The caller bounds their number with
/// `packed_tree_count`.
fn expand_packed_trees(term: &Rc<PackedTerm>) -> Vec<ParsedTerm> {
    fn expand(
        term: &Rc<PackedTerm>,
        memo: &mut HashMap<*const PackedTerm, Rc<Vec<ParsedTerm>>>,
    ) -> Rc<Vec<ParsedTerm>> {
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
    }
    expand(term, &mut HashMap::new()).as_ref().clone()
}

/// The formal-parameter instantiations of one inferred tree: each parametric production it
/// uses with the sorts its parameters were instantiated at, in a canonical order.
fn parameter_instantiations(term: &ParsedTerm) -> Vec<(usize, &[Sort])> {
    fn collect<'t>(term: &'t ParsedTerm, into: &mut Vec<(usize, &'t [Sort])>) {
        match term {
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
        }
    }
    let mut instantiations = Vec::new();
    collect(term, &mut instantiations);
    instantiations.sort_unstable();
    instantiations
}

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
        alternatives.insert(match group[0].clone() {
            ParsedTerm::Production {
                production,
                metadata,
                ..
            } => ParsedTerm::Production {
                production,
                children: factored,
                metadata,
            },
            ParsedTerm::InstantiatedProduction {
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
            ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => {
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
        let ParsedTerm::InstantiatedProduction {
            parameters,
            children,
            ..
        } = inferred
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
        assert!(matches!(
            checked_inference_result(Ok(x.clone()), Ok(y)),
            Err(ParseError::SortInference { ref message })
                if message.contains("produced different terms")
        ));
        assert!(matches!(
            checked_inference_result(Ok(x), Err(inference_error("Z3 rejection"))),
            Err(ParseError::SortInference { ref message })
                if message.contains("portable accepted") && message.contains("Z3 rejected")
        ));
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

    #[test]
    fn independent_ambiguities_are_decided_up_to_the_tree_limit_and_deferred_above_it() {
        // The largest family within the limit has `PORTABLE_AMBIGUITY_TREE_LIMIT.ilog2()`
        // independent binary ambiguities; one more doubles the tree count past it.
        let within = PORTABLE_AMBIGUITY_TREE_LIMIT.ilog2() as usize;
        let top = Sort::new("Good");

        let (grammar, forest) = independent_ambiguities(within);
        assert!(!grammar.packed_sort_inference_supported(&forest));
        let decided = grammar
            .infer_ambiguous_sorts_portable(&forest, &top, false, Ok)
            .expect("the all-`big` tree's typing strictly exceeds every other tree's");
        assert_eq!(
            Grammar::ambiguity_count(&decided),
            1,
            "one tree survives: {decided:?}"
        );

        let (grammar, forest) = independent_ambiguities(within + 1);
        assert_eq!(
            grammar.infer_ambiguous_sorts_portable(&forest, &top, false, Ok),
            Err(ParseError::Z3InferenceRequired {
                ambiguity: true,
                parametric_sorts: false,
            })
        );
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
            .infer_ambiguous_sorts_portable(&forest, &top, false, Ok)
            .expect("both bracket readings are well-sorted");
        assert_eq!(Grammar::ambiguity_count(&portable), 2, "{portable:?}");
        let checked = grammar
            .checked_ambiguous_parse(&forest, &top, false, |tree| {
                grammar.lower_inferred(tree, &top)
            })
            .expect("the portable engine decides the forest");
        assert_eq!(checked, Ok(Term::apply("s", Vec::new())));
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
        assert!(matches!(
            checked_lowered_result(Ok(s()), Ok(annotated())),
            Err(ParseError::SortInference { ref message })
                if message.contains("lowered an ambiguous parse to different terms")
        ));
        assert!(matches!(
            checked_lowered_result(Ok(s()), Err(inference_error("Z3 rejection"))),
            Err(ParseError::SortInference { ref message })
                if message.contains("portable lowered") && message.contains("Z3 rejected")
        ));
        assert!(matches!(
            checked_lowered_result(Err(inference_error("portable rejection")), Ok(s())),
            Err(ParseError::SortInference { ref message })
                if message.contains("portable rejected") && message.contains("Z3 lowered")
        ));
    }
}

//! ```toml algorithm
//! id = "backend.definedness.discharge"
//! name = "structural definedness constraint generation and discharge"
//! sites = ["rule_is_defined", "ceil_term", "ceil_predicate", "deduplicate", "ceil_term_walk", "ceil_term_without_attribute", "ceil_term_node", "KeyGroups", "elements_are_apart", "terms_apart", "condition_definedness", "condition_atom_term", "hoist_condition_definedness", "nested_condition_definedness"]
//! variable = "t = term size, not counting subterms whose stored ceil_free attribute is true; m = entries of one map or elements of one set; k = nodes of the keys (elements) of one map (set); g = groups of those keys by apartness skeleton; v = variables of one term; y = symbols in the definition; q = ceil equations under one partial function head; R = rewrite rules in the definition; l = definedness predicates of one rule"
//! counters = []
//! no_counter = "definedness has no dedicated counter; MatchingProblems, MatchingPairs and SimplifyInvocations count the matching and predicate simplification it calls"
//! span = "per call"
//! consumes = [{ type = "k_rust_backend::matching::MatchResult", role = "match result" }]
//! lean = ["KRust.TermAttributes.ceilFree_sound", "KRust.TermAttributes.walk_eq_ceilTerm", "KRust.TermAttributes.apart_of_sameSkeleton", "KRust.TermAttributes.normDistinct_of_sameSkeleton"]
//!
//! [[cost]]
//! mode = "one term (ceil_term)"
//! bound = "O(1) when the term's stored ceil_free attribute is true (term.rs ceil_free); otherwise O(t) visits of one loop over a work list of at most O(t) entries, on a native stack that does not grow with the term, a visit of a ceil_free subterm returning at once, and one deduplication clone per obligation emitted, plus, per map or set of at least four keys, O(k) to group its keys by apartness skeleton (term.rs rigid_apart_skeleton_hash, and same_apart_skeleton against each group of the same hash) and O(g log m) per key to list the later keys of other groups; then one apartness check per pair of keys that are not both rigid with one skeleton and per pair of equal keys (at most m^2 / 2, none for distinct keys of one skeleton), each a walk of the two elements' shared fixed-root spine that stops at the first open root, by recursion for eight levels and on a work list below them, with up to two matching problems for a pair of certified ground normal forms, plus O(y) per entry beside a rest and, when the definition declares no membership function at the entry's sorts, one absence atom (rule.rs Absence::new): a single-entry collection built over that rest and, for a map, a binder named apart from the O(v) variables of the key and the rest, plus q matches and one predicate simplification per partial application, and, for an application of a value-production symbol that no ceil equation decides and the simplifier has not certified, one instance-normality scan of it (instance_normal.rs)"
//!
//! [[cost]]
//! mode = "one rule or equation condition (condition_definedness)"
//! bound = "one ceil_term call per Boolean atom and per atom side tested for provable definedness, each bounded as above, plus O(c + k) hashing of the c conditions and k known predicates when an obligation is hoisted"
//!
//! [[cost]]
//! mode = "one definition (BackendDefinition::discharge_rewrite_definedness)"
//! bound = "R rule_is_defined calls, each two ceil_term calls, one ceil_predicate over the requires clause, and O(l^2) Vec::contains comparisons"
//! ```
//!
//! Structural definedness (ceil) constraint generation and rewrite-rule definedness discharge, one
//! pass over the term, a loop over an explicit work list that skips subterms whose
//! construction-time `ceil_free` attribute is true, plus apartness checks over the pairs of map
//! keys and set elements that grouping them by apartness skeleton does not decide, with one
//! `FxHashSet` deduplication of the whole list; no counter.

use std::{borrow::Cow, collections::HashSet};

use k_rust_kore::measure::{self, Algorithm};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    definition::BackendDefinition,
    matching::{
        InjectionEquality, MatchMode, MatchResult, SortGraph, match_injection_equality,
        match_terms_in_definition,
    },
    rewrite::{Pattern, Truth, predicates_truth, substitute_predicates},
    rule::{
        Absence, KeyedCollection, Predicate, RewriteRule, RuleRhs, TermIndex, rename_apart,
        term_index,
    },
    simplify::{SimplificationOptions, simplify_predicates_with_solver, term_is_provably_defined},
    smt::{NoSolver, SmtSolver},
    stop::Stoppable,
    term::{
        FunctionType, InjectionComparison, SymbolType, Term, TermKind, Variable, VariableKind,
        head::{Apart, certified_ground_normal_form},
        rigid_apart_skeleton_hash, same_apart_skeleton,
    },
};

pub(crate) fn rule_is_defined(definition: &BackendDefinition, rule: &RewriteRule) -> bool {
    if rule.computed_attributes.undefined_symbols.is_empty() {
        return true;
    }
    let RuleRhs::Term(rhs) = &rule.rhs else {
        return false;
    };
    let lhs = ceil_term(definition, &rule.lhs);
    let requires = rule
        .requires
        .iter()
        .flat_map(|predicate| ceil_predicate(definition, predicate))
        .collect::<Vec<_>>();
    let mut rhs = ceil_term(definition, rhs);
    rhs.retain(|predicate| !lhs.contains(predicate) && !requires.contains(predicate));
    requires.is_empty() && rhs.is_empty()
}

/// The definedness obligations of `term`, deduplicated: the ceil of every partial application
/// (or the instance of its ceil equation), the ceil of every set variable, and the disequalities
/// and not-in atoms of every map and set, in the order [`ceil_term_walk`] gives.
pub fn ceil_term(definition: &BackendDefinition, term: &Term) -> Vec<Predicate> {
    let _span = measure::algorithm_span(Algorithm::BackendDefinedness);
    ceil_term_walk(definition, term, AtCeilFree::Skip)
}

/// The definedness walk without the `ceil_free` shortcut at any depth: the reference the
/// shortcut is checked against (`tests::definedness`).
#[cfg(test)]
pub(crate) fn ceil_term_without_attribute(
    definition: &BackendDefinition,
    term: &Term,
) -> Vec<Predicate> {
    ceil_term_walk(definition, term, AtCeilFree::Descend)
}

/// What [`ceil_term_walk`] does at a subterm whose stored `ceil_free` attribute is true.
#[derive(Clone, Copy, Eq, PartialEq)]
enum AtCeilFree {
    /// Skip it: it has no obligation.
    Skip,
    /// Walk it as any other subterm.
    #[cfg(test)]
    Descend,
}

/// An entry of the work list of [`ceil_term_walk`].
enum Pending<'a> {
    /// A subterm whose obligations come next.
    Term(&'a Term),
    /// Obligations of a node that follow those of its children: the collection obligations of a
    /// map or set.
    Obligations(Vec<Predicate>),
}

/// The definedness obligations of `term`, computed by one loop over a work list.
///
/// The list is that of every node in pre-order: first the node's own obligations (the ceil of a
/// partial application or the instance of its ceil equation, the ceil of a set variable), then
/// its children's, left to right, then its collection obligations; it is deduplicated once at
/// the end, keeping the first occurrence of each member. A list deduplicated at every node gives
/// the same result, since keeping first occurrences absorbs a deduplication of a part of the list
/// (a member removed inside the part has an earlier copy in it): `walk_eq_ceilTerm` of
/// `lean/KRust/TermAttributes.lean` proves it for the model of this walk (`walk`), from that
/// absorption law, which `tests::deduplicate_absorbs_a_deduplicated_part` checks.
///
/// The pending subterms and obligations are kept on the heap, so the walk takes the same native
/// stack whatever the height of the term. It runs on instantiated right-hand sides and bound
/// values of any height, including from the simplifier close to its stack red zone
/// (`stop::STACK_RED_ZONE`), which a recursion over the term would overrun.
///
/// With [`AtCeilFree::Skip`] a subterm whose `ceil_free` attribute is true is skipped. Sound
/// because `ceil_free` (term.rs) is true only when the walk finds no obligation in the subterm
/// under every definition: `lean/KRust/TermAttributes.lean` proves it (`ceilFree_sound`) for the
/// model of the walk and of the attribute, from the constructor invariants that
/// `tests/backend/term_order.rs` checks. The attribute depends only on the term, never on the
/// definition, so one stored bit serves every definition a process holds. In debug builds
/// [`check_ceil_free`] verifies every skipped subterm.
fn ceil_term_walk(
    definition: &BackendDefinition,
    term: &Term,
    at_ceil_free: AtCeilFree,
) -> Vec<Predicate> {
    let mut predicates = Vec::new();
    let mut children = Vec::new();
    let mut work = vec![Pending::Term(term)];
    while let Some(pending) = work.pop() {
        let term = match pending {
            Pending::Term(term) => term,
            Pending::Obligations(obligations) => {
                predicates.extend(obligations);
                continue;
            }
        };
        if at_ceil_free == AtCeilFree::Skip && term.attributes().ceil_free() {
            #[cfg(debug_assertions)]
            check_ceil_free(definition, term);
            continue;
        }
        let after = ceil_term_node(definition, term, &mut predicates, &mut children);
        if !after.is_empty() {
            work.push(Pending::Obligations(after));
        }
        // Reversed, so that the first child is the next entry taken.
        work.extend(children.drain(..).rev().map(Pending::Term));
    }
    deduplicate(&mut predicates);
    predicates
}

/// Debug builds: verify the `ceil_free` shortcut on `term`, a subterm [`ceil_term_walk`] skips.
///
/// The walk without the shortcut returns nothing for `term` exactly when no node of `term` has
/// an obligation of its own, since its result is the deduplicated list of all of them. So this
/// asserts that of every node, and once all of them passed marks them
/// (`Term::mark_ceil_free_checked`). A marked node and every node below it passed already, so the
/// check does not walk it again: each node is walked by the check once, and a descent that skips
/// the same subterm at every level (a list a recursive equation consumes) stays linear. A node is
/// not checked again under another definition: the attribute is a function of the term, and
/// `ceilFree_sound` holds for every definition.
#[cfg(debug_assertions)]
fn check_ceil_free(definition: &BackendDefinition, term: &Term) {
    if term.ceil_free_checked() {
        return;
    }
    let mut obligations = Vec::new();
    let mut children = Vec::new();
    let mut unchecked = vec![term];
    let mut passed = Vec::new();
    while let Some(node) = unchecked.pop() {
        if node.ceil_free_checked() {
            continue;
        }
        let after = ceil_term_node(definition, node, &mut obligations, &mut children);
        assert!(
            obligations.is_empty() && after.is_empty(),
            "a ceil_free term has definedness obligations: {term:?}"
        );
        unchecked.append(&mut children);
        passed.push(node);
    }
    for node in passed {
        node.mark_ceil_free_checked();
    }
}

/// One node of the definedness walk: appends the node's own obligations to `before` and its
/// children, left to right, to `children`, and returns the obligations that follow the
/// children's.
fn ceil_term_node<'a>(
    definition: &BackendDefinition,
    term: &'a Term,
    before: &mut Vec<Predicate>,
    children: &mut Vec<&'a Term>,
) -> Vec<Predicate> {
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial) {
                before.extend(
                    apply_ceil_equation(definition, term)
                        .unwrap_or_else(|| vec![Predicate::Ceil(term.clone())]),
                );
            }
            // Applications are strict in their arguments. Keep this knowledge explicit
            // even when the parent's ceil is opaque to predicate simplification and SMT.
            children.extend(arguments);
            Vec::new()
        }
        TermKind::And(left, right) => {
            children.extend([left, right]);
            Vec::new()
        }
        TermKind::Injection { term, .. } => {
            children.push(term);
            Vec::new()
        }
        TermKind::Map {
            definition: map,
            entries,
            rest,
        } => {
            children.extend(entries.iter().flat_map(|(key, value)| [key, value]));
            children.extend(rest);
            let keys = entries.iter().map(|(key, _)| key).collect::<Vec<_>>();
            let groups = KeyGroups::new(&keys);
            let mut after = Vec::new();
            for (position, left) in keys.iter().enumerate() {
                groups.push_disequalities(definition, position, &mut after);
                if let Some(rest) = rest {
                    after.push(not_in_collection(
                        definition,
                        "MAP.in_keys",
                        KeyedCollection::Map(map.clone()),
                        left,
                        rest,
                    ));
                }
            }
            after
        }
        TermKind::List { heads, rest, .. } => {
            children.extend(heads);
            if let Some((middle, tails)) = rest {
                children.push(middle);
                children.extend(tails);
            }
            Vec::new()
        }
        TermKind::Set {
            definition: set,
            elements,
            rest,
        } => {
            children.extend(elements);
            children.extend(rest);
            let keys = elements.iter().collect::<Vec<_>>();
            let groups = KeyGroups::new(&keys);
            let mut after = Vec::new();
            for (position, left) in keys.iter().enumerate() {
                groups.push_disequalities(definition, position, &mut after);
                if let Some(rest) = rest {
                    after.push(not_in_collection(
                        definition,
                        "SET.in",
                        KeyedCollection::Set(set.clone()),
                        left,
                        rest,
                    ));
                }
            }
            after
        }
        TermKind::DomainValue { .. } => Vec::new(),
        // KORE element variables range over elements and are therefore defined. Set variables
        // range over arbitrary patterns, so their definedness remains an explicit obligation.
        TermKind::Variable(variable) if variable.kind == VariableKind::Element => Vec::new(),
        TermKind::Variable(_) => {
            before.push(Predicate::Ceil(term.clone()));
            Vec::new()
        }
    }
}

/// Fewest keys of one map or set for which [`KeyGroups`] computes skeletons: below it the keys
/// make at most three pairs, which the pairwise checks decide in no more work than the walks.
const GROUPED_KEYS: usize = 4;

/// The keys (or elements) of one map (or set) grouped by apartness skeleton, which decides most
/// of the pairs whose disequality the definedness walk states.
///
/// R-def: the walk states `\not(k_i = k_j)` for every pair `i < j` that [`elements_are_apart`]
/// does not separate. Two rigid keys with one skeleton are apart exactly when they differ
/// (`term::rigid_apart_skeleton_hash`; `apart_of_sameSkeleton` of the Lean model), and then
/// `elements_are_apart` holds through its first disjunct, so such a pair needs no call. Only the
/// pairs with a key in another group or a key that is not rigid, and the pairs of equal keys,
/// are decided by `elements_are_apart`, in increasing `j`: the list is the one the walk states
/// pair by pair.
struct KeyGroups<'a, 't> {
    keys: &'a [&'t Term],
    /// The group of each key; `None` for a key that is not rigid, or for every key of a
    /// collection with fewer than [`GROUPED_KEYS`] keys.
    group: Vec<Option<usize>>,
    /// The indices of each group's keys, increasing.
    members: Vec<Vec<usize>>,
    /// The indices of the keys without a group, increasing.
    loose: Vec<usize>,
    /// The next key equal to each grouped key, which has its group.
    next_equal: Vec<Option<usize>>,
}

impl<'a, 't> KeyGroups<'a, 't> {
    fn new(keys: &'a [&'t Term]) -> Self {
        let mut groups = Self {
            keys,
            group: vec![None; keys.len()],
            members: Vec::new(),
            loose: Vec::new(),
            next_equal: vec![None; keys.len()],
        };
        if keys.len() < GROUPED_KEYS {
            groups.loose = (0..keys.len()).collect();
            return groups;
        }
        let mut pending = Vec::new();
        // The groups of each skeleton hash, by the index of their first key.
        let mut by_hash = FxHashMap::<u64, Vec<usize>>::default();
        let mut last_of_key = FxHashMap::<&Term, usize>::default();
        for (index, key) in keys.iter().enumerate() {
            let Some(hash) = rigid_apart_skeleton_hash(key, &mut pending) else {
                groups.loose.push(index);
                continue;
            };
            let candidates = by_hash.entry(hash).or_default();
            let group = match candidates
                .iter()
                .copied()
                .find(|&group| same_apart_skeleton(keys[groups.members[group][0]], key))
            {
                Some(group) => group,
                None => {
                    groups.members.push(Vec::new());
                    candidates.push(groups.members.len() - 1);
                    groups.members.len() - 1
                }
            };
            groups.members[group].push(index);
            groups.group[index] = Some(group);
            // Equal keys have one skeleton, so they share this group.
            if let Some(previous) = last_of_key.insert(key, index) {
                groups.next_equal[previous] = Some(index);
            }
        }
        groups
    }

    /// Append to `after` the disequality of the key at `position` with every later key that
    /// [`elements_are_apart`] does not separate, in the order of the later keys.
    fn push_disequalities(
        &self,
        definition: &BackendDefinition,
        position: usize,
        after: &mut Vec<Predicate>,
    ) {
        let left = self.keys[position];
        let later = |indices: &[usize]| {
            let start = indices.partition_point(|&index| index <= position);
            indices[start..].to_vec()
        };
        let undecided = match self.group[position] {
            None => (position + 1..self.keys.len()).collect::<Vec<_>>(),
            Some(own) => {
                let mut undecided = later(&self.loose);
                for (group, members) in self.members.iter().enumerate() {
                    if group != own {
                        undecided.extend(later(members));
                    }
                }
                let mut equal = self.next_equal[position];
                while let Some(index) = equal {
                    undecided.push(index);
                    equal = self.next_equal[index];
                }
                undecided.sort_unstable();
                undecided
            }
        };
        for index in undecided {
            let right = self.keys[index];
            // R-def: this list states both elements' definedness obligations, so an apart
            // pair's disequality is implied wherever the list holds.
            if !elements_are_apart(definition, left, right) {
                after.push(Predicate::Not(Box::new(Predicate::Equals(
                    left.clone(),
                    right.clone(),
                ))));
            }
        }
    }
}

#[cfg(test)]
thread_local! {
    /// Test builds: the `elements_are_apart` calls this thread has made.
    pub(crate) static APARTNESS_CHECKS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The disequalities the definedness walk states for the keys (or elements) `keys` of one map
/// (or set), in order: through [`KeyGroups`] when `grouped`, otherwise by calling
/// [`elements_are_apart`] on every pair, the reference the grouping is checked against
/// (`tests::definedness`).
#[cfg(test)]
pub(crate) fn collection_disequalities(
    definition: &BackendDefinition,
    keys: &[&Term],
    grouped: bool,
) -> Vec<Predicate> {
    let mut after = Vec::new();
    if grouped {
        let groups = KeyGroups::new(keys);
        for position in 0..keys.len() {
            groups.push_disequalities(definition, position, &mut after);
        }
    } else {
        for (position, left) in keys.iter().enumerate() {
            for right in &keys[position + 1..] {
                if !elements_are_apart(definition, left, right) {
                    after.push(Predicate::Not(Box::new(Predicate::Equals(
                        (*left).clone(),
                        (*right).clone(),
                    ))));
                }
            }
        }
    }
    after
}

/// Apartness (A): no value of one term is a value of the other on any valuation.
/// `Term::apart_with` supplies the fixed-root decision; the optional sort graph separates
/// injections whose source sorts share no value, without requiring a normal-form certificate.
/// Without a sort graph the callback retains only injection facts that need no subsort lookup.
pub(crate) fn terms_apart(sorts: Option<&SortGraph>, left: &Term, right: &Term) -> Option<Apart> {
    left.apart_with(
        right,
        &|left, right| match match_injection_equality(sorts, left, right) {
            Some(InjectionEquality::Distinct) => InjectionComparison::Distinct,
            Some(
                InjectionEquality::Direct(left, right) | InjectionEquality::Split(left, right),
            ) => InjectionComparison::Compare(left, right),
            Some(InjectionEquality::Unknown) | None => InjectionComparison::Undecided,
        },
    )
}

/// R-def: whether two collection keys or elements need no disequality when both are defined.
///
/// The keys reach here from any term `ceil_term` walks, including instantiated right-hand sides
/// no simplification has seen, so nothing here assumes they are normal forms.
/// Apartness first separates any terms with disjoint denotations. Rewrite matching
/// additionally compares overloads and widening injections, which occur in generated cells; it
/// treats `anywhere` heads as rigid, so its failure separates two terms only when both are
/// normal forms. It is consulted only for ground terms whose every subterm is certified normal
/// by the `evaluated` bit (a constructor or injection over certified arguments, a domain value,
/// or an `anywhere` application the simplifier cached as a fixed point). Requiring failure in
/// both directions keeps the decision independent of matching orientation.
fn elements_are_apart(definition: &BackendDefinition, left: &Term, right: &Term) -> bool {
    #[cfg(test)]
    APARTNESS_CHECKS.set(APARTNESS_CHECKS.get() + 1);
    if terms_apart(Some(definition.sort_graph()), left, right).is_some() {
        return true;
    }
    certified_ground_normal_form(left)
        && certified_ground_normal_form(right)
        && matches!(
            match_terms_in_definition(MatchMode::Rewrite, definition, left, right),
            MatchResult::Failed(_)
        )
        && matches!(
            match_terms_in_definition(MatchMode::Rewrite, definition, right, left),
            MatchResult::Failed(_)
        )
}

/// The instantiated right-hand side `predicates` of a ceil equation, simplified.
///
/// Simplifying the right-hand side only refines it: the unsimplified predicates are the same
/// condition, so a failure keeps them.
///
/// Not inlined: `ceil_term_node` recurses once per level of the term, and the temporaries of this
/// nested simplification would otherwise be part of every one of those frames.
#[inline(never)]
fn simplified_ceil_condition(
    definition: &BackendDefinition,
    predicates: Vec<Predicate>,
) -> Vec<Predicate> {
    match simplify_predicates_with_solver(
        definition,
        &predicates,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    ) {
        Ok(Ok(simplified)) => simplified,
        Ok(Err(_failure)) => predicates,
        Err(stop) => {
            // The stop interrupted only that refinement. The ceil keeps its condition, the
            // instantiated right-hand side `predicates`, unsimplified, which is sound without the
            // simplified form; a stop of the request or of the solver stays raised, so its
            // owner's next poll mints it again.
            stop.forgo_refinement();
            predicates
        }
    }
}

/// The definedness of the partial application `term` beyond that of its arguments, which
/// `ceil_term_node` adds: the condition of the first unconditional ceil equation that matches it,
/// or, for an application of a `value-production` symbol that no equation reduces on any
/// instance, nothing, since that marker makes such an application a value
/// (`BackendDefinition::irreducible_application_is_defined`). `None` keeps the opaque `\ceil`.
fn apply_ceil_equation(definition: &BackendDefinition, term: &Term) -> Option<Vec<Predicate>> {
    ceil_theory_condition(definition, term).or_else(|| {
        definition
            .irreducible_application_is_defined(term)
            .then(Vec::new)
    })
}

fn ceil_theory_condition(definition: &BackendDefinition, term: &Term) -> Option<Vec<Predicate>> {
    let indexes = [term_index(term), TermIndex::Variable];
    for index in indexes {
        let Some(groups) = definition.ceil_theory().get(&index) else {
            continue;
        };
        for rules in groups.values() {
            for rule in rules {
                // This analysis has no path condition with which to discharge a conditional
                // ceil equation. Applying it here would incorrectly treat the equation as
                // unconditional; runtime predicate simplification handles conditional rules.
                // An equation whose result has a variable its left-hand side does not bind has
                // no instance to use (`simplify::evaluate_equation_condition`).
                if !rule.requires.is_empty()
                    || !rule.computed_attributes.unbound_result_variables.is_empty()
                {
                    continue;
                }
                let renamed = rename_apart(rule, &term.attributes().variables, &[]);
                let rule = renamed.as_ref().map_or(&**rule, |(renamed, _)| renamed);
                let MatchResult::Success(substitution) =
                    match_terms_in_definition(MatchMode::Evaluate, definition, &rule.lhs, term)
                else {
                    continue;
                };
                let RuleRhs::Predicates(predicates) = &rule.rhs else {
                    continue;
                };
                #[expect(
                    clippy::disallowed_methods,
                    reason = "the right-hand side of an unconditional ceil equation; ceil_term_node collects the definedness of the arguments, which contain every bound term"
                )]
                let predicates = simplified_ceil_condition(
                    definition,
                    substitute_predicates(predicates, &substitution),
                );
                return Some(
                    predicates
                        .into_iter()
                        .filter(|predicate| predicate != &Predicate::True)
                        .collect(),
                );
            }
        }
    }
    None
}

/// A rule or equation condition with the definedness of its Boolean terms made explicit.
///
/// A condition is a predicate over the instance, and a term in it denotes `\bottom` on an
/// instance where it is undefined. For a term `v` that is defined on every instance, the
/// equality `\equals(b, v)` is false wherever `b` is `\bottom` (the empty pattern equals no
/// element), so `\equals(b, v) = \ceil(b) /\ \equals(b, v)`, and a Boolean term `b` used as a
/// predicate means `\equals(b, true)`. The equivalence holds in every predicate context, so it is
/// applied to every such atom: `\ceil(b)`, as the `ceil_term` obligations of `b`, becomes sibling
/// conjuncts of an atom that is itself a conjunct of the condition, and is conjoined in place to an
/// atom under a negation, a disjunction, an implication, a quantifier or a `\floor`. An equality
/// with no side provably defined is left alone: `\equals(\bottom, \bottom)` is `\top`, so neither
/// side's definedness is implied there.
///
/// The result is equivalent to `conditions`. Stating it before a condition is simplified or
/// decided keeps both from answering on the instances where its terms are undefined: the
/// simplifier can reduce `b` to a value that no longer shows the partial subterm, and a solver
/// that maps a partial function to a total operation gives it a value there.
///
/// A hoisted obligation already in `known` or among the conditions is not restated. A
/// condition whose terms are all `ceil_free` is returned as it is after one read of the stored
/// attribute per term, and one whose partial subterms are defined by an unconditional ceil
/// equation gains only what that equation leaves undecided.
pub(crate) fn condition_definedness(
    definition: &BackendDefinition,
    conditions: Vec<Predicate>,
    known: &[Predicate],
) -> Vec<Predicate> {
    if predicates_are_ceil_free(&conditions) {
        return conditions;
    }
    let _span = measure::algorithm_span(Algorithm::BackendDefinedness);
    let mut obligations = Vec::new();
    let mut rewritten = Vec::with_capacity(conditions.len());
    for condition in &conditions {
        rewritten.push(hoist_condition_definedness(
            definition,
            condition,
            known,
            &mut obligations,
        ));
    }
    if obligations.is_empty() {
        return rewritten;
    }
    let mut seen = FxHashSet::with_capacity_and_hasher(
        known.len() + rewritten.len() + obligations.len(),
        Default::default(),
    );
    seen.extend(known.iter().cloned());
    seen.extend(rewritten.iter().cloned());
    let mut result = Vec::with_capacity(obligations.len() + rewritten.len());
    for obligation in obligations {
        if seen.insert(obligation.clone()) {
            result.push(obligation);
        }
    }
    result.extend(rewritten);
    result
}

/// Whether every term of `predicates` has its stored `ceil_free` attribute, one read per term:
/// then no atom of them has a definedness obligation to state.
fn predicates_are_ceil_free(predicates: &[Predicate]) -> bool {
    predicates.iter().all(|predicate| {
        let mut free = true;
        predicate.visit_terms(&mut |term| free &= term.attributes().ceil_free());
        free
    })
}

/// The facts every instance of a pattern `t ∧ φ` satisfies (I7): `condition_definedness(φ)`
/// followed by the members of `ceil_term(t)` it lacks.
///
/// A pattern denotes `⌈t⌉ ∧ t ∧ φ`, since a term is `\bottom` where it is undefined and
/// `\bottom ∧ φ` is `\bottom`, so `⌈t⌉` holds on each of its instances. And `φ` equals
/// `condition_definedness(φ)`, so the obligations that call states are consequences of `φ` there.
/// A decision whose answer is relative to the pattern's instances (a claim applied to a proof
/// state, a condition reported together with its state) takes these as known: a stated `⌈s⌉`
/// they contain is a fact, not an open condition, and a solver that reads `⌈s⌉` as an opaque atom
/// would otherwise find a model where it fails. On an empty pattern every such answer is right.
///
/// A verdict that an instance exists (a match reported) decides them first (I7'): a member that
/// simplifies to `\bottom` means the pattern has no instance, and an assumed false fact would both
/// hide that and let the simplifier answer anything about the rest. Such a verdict takes the
/// members not among the constraints through [`knowledge_facts`] and [`UndecidedFacts::decide`],
/// and assumes only the decided residual.
///
/// The result is equivalent to `pattern.constraints` on the pattern's instances. It is the
/// constraints themselves, borrowed, when the term and every constraint term are `ceil_free`, after
/// one read of the stored attribute per term.
pub(crate) fn pattern_knowledge<'a>(
    definition: &BackendDefinition,
    pattern: &'a Pattern,
) -> Cow<'a, [Predicate]> {
    if pattern.term.attributes().ceil_free() && predicates_are_ceil_free(&pattern.constraints) {
        return Cow::Borrowed(&pattern.constraints);
    }
    let mut knowledge = condition_definedness(definition, pattern.constraints.clone(), &[]);
    let mut known = knowledge.iter().cloned().collect::<FxHashSet<_>>();
    for predicate in ceil_term(definition, &pattern.term) {
        if known.insert(predicate.clone()) {
            knowledge.push(predicate);
        }
    }
    Cow::Owned(knowledge)
}

/// The members of `knowledge` (a pattern's [`pattern_knowledge`]) that are not among its
/// `constraints`.
pub(crate) fn knowledge_facts(
    knowledge: Cow<'_, [Predicate]>,
    constraints: &[Predicate],
) -> Vec<Predicate> {
    match knowledge {
        // The knowledge of a `ceil_free` pattern is its constraints themselves.
        Cow::Borrowed(_) => Vec::new(),
        Cow::Owned(knowledge) => {
            let constraints = constraints.iter().collect::<HashSet<_>>();
            knowledge
                .into_iter()
                .filter(|fact| !constraints.contains(fact))
                .collect()
        }
    }
}

/// Facts every instance of a pattern satisfies (I7), not yet decided.
///
/// There is no view of the facts: they are taken as known only through the [`DecidedFacts`] that
/// [`Self::decide`] returns when none of them is refuted, so a verdict that an instance exists
/// cannot assume a false fact (I7').
#[must_use]
pub(crate) struct UndecidedFacts(Vec<Predicate>);

impl UndecidedFacts {
    pub(crate) fn new(facts: Vec<Predicate>) -> Self {
        Self(facts)
    }

    /// The facts of `pattern` itself: the members of its [`pattern_knowledge`] that are not
    /// among its constraints. A `ceil_free` pattern has none, found without a simplification.
    pub(crate) fn of_pattern(definition: &BackendDefinition, pattern: &Pattern) -> Self {
        Self(knowledge_facts(
            pattern_knowledge(definition, pattern),
            &pattern.constraints,
        ))
    }

    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Simplify the facts with nothing assumed.
    ///
    /// A member simplified to `\bottom` is a false fact about every instance, so the pattern has
    /// no instance: [`FactsVerdict::Refuted`]. Otherwise the simplified facts without their
    /// `\top` members are the residual a decision may take as known, since they are equivalent to
    /// the facts. The decision only refutes: an undecided member stays in the residual, a fact
    /// about the pattern rather than a condition to discharge. A failed simplification leaves the
    /// facts undecided and returns them unsimplified, which is sound for the same reason. Empty
    /// facts return at once, without calling the simplifier.
    pub(crate) fn decide(
        self,
        definition: &BackendDefinition,
        options: SimplificationOptions,
        solver: &dyn SmtSolver,
    ) -> Stoppable<FactsVerdict> {
        let Self(facts) = self;
        if facts.is_empty() {
            return Ok(FactsVerdict::NotRefuted(DecidedFacts(facts)));
        }
        Ok(
            match simplify_predicates_with_solver(definition, &facts, &[], options, solver)? {
                Ok(simplified) if predicates_truth(&simplified) == Truth::False => {
                    FactsVerdict::Refuted
                }
                Ok(simplified) => FactsVerdict::NotRefuted(DecidedFacts(
                    simplified
                        .into_iter()
                        .filter(|fact| fact != &Predicate::True)
                        .collect(),
                )),
                Err(_failure) => FactsVerdict::NotRefuted(DecidedFacts(facts)),
            },
        )
    }
}

/// The outcome of [`UndecidedFacts::decide`].
#[must_use]
pub(crate) enum FactsVerdict {
    /// A fact is false: the pattern has no instance.
    Refuted,
    /// No fact is refuted; the residual may be taken as known.
    NotRefuted(DecidedFacts),
}

/// Facts of a pattern that [`UndecidedFacts::decide`] did not refute, equivalent to them on the
/// pattern's instances.
pub(crate) struct DecidedFacts(Vec<Predicate>);

impl DecidedFacts {
    /// The facts, to be taken as known by a decision on the pattern's instances.
    pub(crate) fn as_known(&self) -> &[Predicate] {
        &self.0
    }
}

/// The Boolean term an atom asserts to equal a defined value, if any.
fn condition_atom_term<'a>(
    definition: &BackendDefinition,
    predicate: &'a Predicate,
    known: &[Predicate],
) -> Option<&'a Term> {
    let defined = |term: &Term| {
        term_is_provably_defined(definition, term, |obligation| known.contains(obligation))
    };
    match predicate {
        Predicate::Term(term) => Some(term),
        Predicate::Equals(left, right) if defined(right) => Some(left),
        Predicate::Equals(left, right) if defined(left) => Some(right),
        _ => None,
    }
}

/// A conjunct of the condition: an atom keeps its shape and its obligations are hoisted.
fn hoist_condition_definedness(
    definition: &BackendDefinition,
    predicate: &Predicate,
    known: &[Predicate],
    obligations: &mut Vec<Predicate>,
) -> Predicate {
    if let Predicate::And(conjuncts) = predicate {
        return Predicate::And(
            conjuncts
                .iter()
                .map(|conjunct| {
                    hoist_condition_definedness(definition, conjunct, known, obligations)
                })
                .collect(),
        );
    }
    if let Some(term) = condition_atom_term(definition, predicate, known) {
        obligations.extend(ceil_term_walk(definition, term, AtCeilFree::Skip));
        return predicate.clone();
    }
    nested_condition_definedness(definition, predicate, known)
}

/// A predicate below a connective other than a top-level conjunction: an atom becomes
/// `\ceil(b) /\ atom` in place.
fn nested_condition_definedness(
    definition: &BackendDefinition,
    predicate: &Predicate,
    known: &[Predicate],
) -> Predicate {
    let nested =
        |inner: &Predicate| Box::new(nested_condition_definedness(definition, inner, known));
    match predicate {
        Predicate::True
        | Predicate::False
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Absent(_) => predicate.clone(),
        Predicate::Term(_) | Predicate::Equals(..) => {
            let Some(term) = condition_atom_term(definition, predicate, known) else {
                return predicate.clone();
            };
            let mut conjuncts = ceil_term_walk(definition, term, AtCeilFree::Skip);
            conjuncts.retain(|obligation| !known.contains(obligation));
            if conjuncts.is_empty() {
                return predicate.clone();
            }
            conjuncts.push(predicate.clone());
            Predicate::And(conjuncts)
        }
        Predicate::Not(inner) => Predicate::Not(nested(inner)),
        Predicate::Exists(variable, inner) => Predicate::Exists(
            variable.clone(),
            Box::new(under_binder(definition, variable, inner, known)),
        ),
        Predicate::Forall(variable, inner) => Predicate::Forall(
            variable.clone(),
            Box::new(under_binder(definition, variable, inner, known)),
        ),
        Predicate::And(inner) => Predicate::And(
            inner
                .iter()
                .map(|inner| nested_condition_definedness(definition, inner, known))
                .collect(),
        ),
        Predicate::Or(inner) => Predicate::Or(
            inner
                .iter()
                .map(|inner| nested_condition_definedness(definition, inner, known))
                .collect(),
        ),
        Predicate::Implies(left, right) => Predicate::Implies(nested(left), nested(right)),
        Predicate::Iff(left, right) => Predicate::Iff(nested(left), nested(right)),
    }
}

/// [`nested_condition_definedness`] of `inner`, the body of a quantifier over `variable`.
///
/// A known fact that mentions `variable` free is about the variable of that name outside the
/// quantifier, not about the one it binds, so it is set aside under the binder: an obligation
/// about the bound variable is stated even when a fact of the same text is known outside.
fn under_binder(
    definition: &BackendDefinition,
    variable: &Variable,
    inner: &Predicate,
    known: &[Predicate],
) -> Predicate {
    let holds = |fact: &Predicate| !crate::rule::mentions_free(fact, variable);
    if known.iter().all(holds) {
        return nested_condition_definedness(definition, inner, known);
    }
    let unshadowed = known
        .iter()
        .filter(|fact| holds(fact))
        .cloned()
        .collect::<Vec<_>>();
    nested_condition_definedness(definition, inner, &unshadowed)
}

fn ceil_predicate(definition: &BackendDefinition, predicate: &Predicate) -> Vec<Predicate> {
    match predicate {
        Predicate::True | Predicate::False => Vec::new(),
        Predicate::Term(term) | Predicate::Ceil(term) | Predicate::Floor(term) => {
            ceil_term(definition, term)
        }
        Predicate::Equals(left, right) | Predicate::In(left, right) => ceil_term(definition, left)
            .into_iter()
            .chain(ceil_term(definition, right))
            .collect(),
        // An absence is the `\ceil` of its joined collection, whose value is a variable.
        Predicate::Absent(absence) => ceil_term(definition, absence.joined()),
        Predicate::Not(inner) | Predicate::Exists(_, inner) | Predicate::Forall(_, inner) => {
            ceil_predicate(definition, inner)
        }
        Predicate::And(inner) | Predicate::Or(inner) => inner
            .iter()
            .flat_map(|predicate| ceil_predicate(definition, predicate))
            .collect(),
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            ceil_predicate(definition, left)
                .into_iter()
                .chain(ceil_predicate(definition, right))
                .collect()
        }
    }
}

/// The definedness obligation that `element` is not a key (`MAP.in_keys`) or an element
/// (`SET.in`) of `rest`, the rest of a map or set of `collection` that also binds `element`.
///
/// A function the definition hooks to `hook` at exactly these argument sorts states it as
/// `\not(hook(element, rest) = true)`. Without one, the obligation is the atom
/// [`Absence`]: the definedness of `element` joined to `rest`, whatever value a map entry
/// binds to it. It is a fact about `element` and `rest` alone, so a rule that only changes the
/// value bound to a key restates the obligation its left-hand side or its path already holds.
/// KORE's `\in{S1,S2}(P1:S1, P2:S1)` is no substitute: it relates two patterns of one sort,
/// while a key or element and the collection have different sorts.
fn not_in_collection(
    definition: &BackendDefinition,
    hook: &str,
    collection: KeyedCollection,
    element: &Term,
    rest: &Term,
) -> Predicate {
    let application = definition.symbols().values().find_map(|symbol| {
        (symbol.attributes.hook.as_deref() == Some(hook)
            && symbol.argument_sorts.as_slice() == [element.sort(), rest.sort()])
        .then(|| {
            Term::application(
                symbol.clone(),
                Vec::new(),
                vec![element.clone(), rest.clone()],
            )
        })
    });
    application.map_or_else(
        || Absence::predicate(collection, element.clone(), rest.clone()),
        |application| Predicate::Not(Box::new(Predicate::Term(application))),
    )
}

fn deduplicate(predicates: &mut Vec<Predicate>) {
    let mut seen = FxHashSet::with_capacity_and_hasher(predicates.len(), Default::default());
    predicates.retain(|predicate| seen.insert(predicate.clone()));
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::rewrite::{Pattern, RewriteResult, rewrite_step};
    use crate::term::Sort;

    #[test]
    fn definedness_deduplication_preserves_first_occurrence_order() {
        let sort = Sort::simple("SortS");
        let x = Term::variable(crate::term::Variable::new("X", sort.clone()));
        let y = Term::variable(crate::term::Variable::new("Y", sort));
        let first = Predicate::Ceil(x);
        let second = Predicate::Ceil(y);
        let mut predicates = vec![first.clone(), second.clone(), first.clone(), second.clone()];

        deduplicate(&mut predicates);

        assert_eq!(predicates, vec![first, second]);
    }

    /// The hypothesis `Oracles.dedup_nil` of lean/KRust/TermAttributes.lean: `deduplicate`
    /// leaves an empty vector empty, so an arm of the model `ceilTerm` whose parts are all empty,
    /// and `ceil_term_walk` when it emits no obligation, return the empty vector.
    #[test]
    fn deduplicate_keeps_an_empty_vector_empty() {
        let mut predicates = Vec::new();

        deduplicate(&mut predicates);

        assert_eq!(predicates, Vec::<Predicate>::new());
    }

    /// The hypothesis `DedupAbsorbs` of `walk_eq_ceilTerm` (lean/KRust/TermAttributes.lean):
    /// deduplicating a part of a list first changes nothing, for every split of every list of up
    /// to six members over three predicates.
    #[test]
    fn deduplicate_absorbs_a_deduplicated_part() {
        let sort = Sort::simple("SortS");
        let alphabet = ["X", "Y", "Z"].map(|name| {
            Predicate::Ceil(Term::variable(crate::term::Variable::new(
                name,
                sort.clone(),
            )))
        });
        let alphabet = &alphabet;
        let lists = |length: usize| {
            (0..alphabet.len().pow(length as u32)).map(move |mut code| {
                (0..length)
                    .map(|_| {
                        let member = alphabet[code % alphabet.len()].clone();
                        code /= alphabet.len();
                        member
                    })
                    .collect::<Vec<_>>()
            })
        };
        let deduplicated = |mut predicates: Vec<Predicate>| {
            deduplicate(&mut predicates);
            predicates
        };
        let mut cases = 0;
        for length in 0..=6 {
            for list in lists(length) {
                for start in 0..=length {
                    for end in start..=length {
                        let (before, rest) = list.split_at(start);
                        let (part, after) = rest.split_at(end - start);
                        let absorbed = [before, &deduplicated(part.to_vec()), after].concat();
                        assert_eq!(
                            deduplicated(absorbed),
                            deduplicated(list.clone()),
                            "{before:?} {part:?} {after:?}"
                        );
                        cases += 1;
                    }
                }
            }
        }
        assert!(cases > 10_000, "{cases}");
    }

    /// The definedness walk keeps its pending subterms on the heap, so it finds the obligations
    /// of a term of any height on a small stack: here chains of 20,000 applications on a
    /// 256 KiB thread, where a recursion per level overflowed in every build. `partial` emits
    /// its ceil at every level, in pre-order; `wrap` is total, so its chain is `ceil_free`, which
    /// `ceil_term` skips (in debug builds after `check_ceil_free` walked it) and the walk without
    /// the shortcut walks to the end. The chains are built and dropped on a larger thread, since
    /// dropping a term recurses over it.
    #[test]
    fn deep_terms_have_their_obligations_found_on_a_small_stack() {
        const LEVELS: usize = 20_000;
        const SMALL_STACK: usize = 256 * 1024;
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(|| {
                let definition = definition("");
                let symbol = |name: &str| {
                    let application = definition
                        .internalize_term(
                            &parse_pattern(&format!("{name}{{}}(X:SortS{{}})")).unwrap(),
                            &[],
                        )
                        .unwrap();
                    let TermKind::Application { symbol, .. } = application.kind() else {
                        panic!("{name} should be an application");
                    };
                    symbol.clone()
                };
                let leaf = definition
                    .internalize_term(&parse_pattern(r#"\dv{SortS{}}("v")"#).unwrap(), &[])
                    .unwrap();
                let chain = |name: &str| {
                    let symbol = symbol(name);
                    (0..LEVELS).fold(leaf.clone(), |term, _| {
                        Term::application(symbol.clone(), Vec::new(), vec![term])
                    })
                };
                let partial = chain("partial");
                let wrap = chain("wrap");
                assert!(!partial.attributes().ceil_free());
                assert!(wrap.attributes().ceil_free());
                let mut expected = Vec::with_capacity(LEVELS);
                let mut level = &partial;
                while let TermKind::Application { arguments, .. } = level.kind() {
                    expected.push(Predicate::Ceil(level.clone()));
                    level = &arguments[0];
                }
                let found = std::thread::scope(|scope| {
                    std::thread::Builder::new()
                        .stack_size(SMALL_STACK)
                        .spawn_scoped(scope, || {
                            [
                                ceil_term(&definition, &partial),
                                ceil_term_without_attribute(&definition, &partial),
                                ceil_term(&definition, &wrap),
                                ceil_term_without_attribute(&definition, &wrap),
                            ]
                        })
                        .unwrap()
                        .join()
                        .unwrap()
                });
                assert_eq!(found[0], expected);
                assert_eq!(found[1], expected);
                assert_eq!(found[2], Vec::new());
                assert_eq!(found[3], Vec::new());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Debug builds: the check of a skipped `ceil_free` subterm marks every node it walked, so a
    /// later skip of any of them, such as the tail of a list a recursive equation consumes one
    /// level at a time, does not walk it again; a term built over a checked one is checked only
    /// down to it.
    #[cfg(debug_assertions)]
    #[test]
    fn the_ceil_free_check_walks_each_node_once() {
        let definition = definition("");
        let wrap = |term: Term| {
            definition
                .internalize_term(&parse_pattern("wrap{}(X:SortS{})").unwrap(), &[])
                .map(|application| {
                    let TermKind::Application { symbol, .. } = application.kind() else {
                        panic!("wrap should be an application");
                    };
                    Term::application(symbol.clone(), Vec::new(), vec![term])
                })
                .unwrap()
        };
        let leaf = definition
            .internalize_term(&parse_pattern(r#"\dv{SortS{}}("v")"#).unwrap(), &[])
            .unwrap();
        let inner = wrap(wrap(leaf.clone()));
        let outer = wrap(inner.clone());
        assert!(!inner.ceil_free_checked() && !leaf.ceil_free_checked());
        assert_eq!(ceil_term(&definition, &inner), Vec::new());
        assert!(inner.ceil_free_checked() && leaf.ceil_free_checked());
        assert!(!outer.ceil_free_checked());
        assert_eq!(ceil_term(&definition, &outer), Vec::new());
        assert!(outer.ceil_free_checked());
    }

    fn definition(extra_axioms: &str) -> BackendDefinition {
        let source = r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol partial{}(SortS{}) : SortS{} [function{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                    partial{}(X:SortS{})
                ) [label{}("uses-partial")]
                $EXTRA
            endmodule []"#
            .replace("$EXTRA", extra_axioms);
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// An unconditional ceil equation whose result has a variable its left-hand side does not
    /// bind states `\ceil(partial(X)) = \equals(X, Z)` for every `Z`; matching fixes no value
    /// for `Z`, so the static analysis does not use it and keeps the opaque obligation, as with
    /// no equation. A bound equation of the same shape is used, the control.
    #[test]
    fn an_unbound_ceil_equation_is_not_used_by_the_static_analysis() {
        let ceil = |result: &str| {
            let definition = definition(&format!(
                r#"axiom{{R, Q}} \implies{{R}}(\top{{R}}(),
                    \equals{{Q, R}}(\ceil{{SortS{{}}, Q}}(partial{{}}(X:SortS{{}})),
                        \and{{Q}}({result}, \top{{Q}}())))
                    [simplification{{}}(), label{{}}("ceil-partial")]"#
            ));
            let subject = definition
                .internalize_term(
                    &parse_pattern(r#"partial{}(\dv{SortS{}}("v"))"#).unwrap(),
                    &[],
                )
                .unwrap();
            (ceil_term(&definition, &subject), subject)
        };
        let (unbound, subject) = ceil(r#"\equals{SortS{}, Q}(X:SortS{}, Z:SortS{})"#);
        assert_eq!(unbound, vec![Predicate::Ceil(subject)]);
        let (bound, _) = ceil(r#"\equals{SortS{}, Q}(X:SortS{}, X:SortS{})"#);
        assert!(
            !bound
                .iter()
                .any(|predicate| matches!(predicate, Predicate::Ceil(_))),
            "{bound:?}"
        );
    }

    fn rewrite_rule(definition: &BackendDefinition) -> &Arc<RewriteRule> {
        definition
            .rewrite_theory()
            .values()
            .flat_map(|groups| groups.values())
            .flatten()
            .next()
            .map(|stored| &stored.rule)
            .expect("rewrite rule should be indexed")
    }

    /// `condition_definedness` over `partial{}(X)`, which has no ceil equation, so its
    /// obligation is `\ceil(partial{}(X))`.
    #[test]
    fn condition_definedness_states_the_ceil_of_each_boolean_atom() {
        let definition = definition("");
        let parse = |source| {
            definition
                .internalize_term(&parse_pattern(source).unwrap(), &[])
                .unwrap()
        };
        let partial_x = parse("partial{}(X:SortS{})");
        let partial_y = parse("partial{}(Y:SortS{})");
        let value = parse(r#"\dv{SortS{}}("v")"#);
        let x = parse("X:SortS{}");
        let ceil_x = Predicate::Ceil(partial_x.clone());
        let ceil_y = Predicate::Ceil(partial_y.clone());
        let equals_x = Predicate::Equals(partial_x.clone(), value.clone());
        let equals_y = Predicate::Equals(value.clone(), partial_y.clone());

        // A top-level atom: its obligation is hoisted as a sibling conjunct, before the
        // conditions, with either side of the equality as the defined one.
        assert_eq!(
            condition_definedness(&definition, vec![equals_x.clone(), equals_y.clone()], &[]),
            vec![
                ceil_x.clone(),
                ceil_y.clone(),
                equals_x.clone(),
                equals_y.clone()
            ]
        );
        // A conjunction at the top is still a conjunction of the condition.
        assert_eq!(
            condition_definedness(
                &definition,
                vec![Predicate::And(vec![equals_x.clone()])],
                &[]
            ),
            vec![ceil_x.clone(), Predicate::And(vec![equals_x.clone()])]
        );
        // A known obligation, or one the condition already states, is not restated.
        assert_eq!(
            condition_definedness(
                &definition,
                vec![equals_x.clone()],
                std::slice::from_ref(&ceil_x)
            ),
            vec![equals_x.clone()]
        );
        assert_eq!(
            condition_definedness(&definition, vec![ceil_x.clone(), equals_x.clone()], &[]),
            vec![ceil_x.clone(), equals_x.clone()]
        );
        // Under a negation or a disjunction the obligation is conjoined in place: hoisting it
        // would change the meaning, since `\not \equals(\bottom, v)` holds.
        let negated = Predicate::Not(Box::new(equals_x.clone()));
        assert_eq!(
            condition_definedness(&definition, vec![negated], &[]),
            vec![Predicate::Not(Box::new(Predicate::And(vec![
                ceil_x.clone(),
                equals_x.clone()
            ])))]
        );
        let disjunction = Predicate::Or(vec![equals_x.clone(), equals_y.clone()]);
        assert_eq!(
            condition_definedness(&definition, vec![disjunction], &[]),
            vec![Predicate::Or(vec![
                Predicate::And(vec![ceil_x.clone(), equals_x.clone()]),
                Predicate::And(vec![ceil_y.clone(), equals_y.clone()]),
            ])]
        );
        // A known fact about `X` is about the free `X`, not about the `X` a quantifier binds:
        // under `\exists X` the obligation is stated although the same text is known outside.
        let binder = crate::term::Variable::new("X", Sort::simple("SortS"));
        let body = Box::new(equals_x.clone());
        let stated = Box::new(Predicate::And(vec![ceil_x.clone(), equals_x.clone()]));
        for (quantified, expected) in [
            (
                Predicate::Exists(binder.clone(), body.clone()),
                Predicate::Exists(binder.clone(), stated.clone()),
            ),
            (
                Predicate::Forall(binder.clone(), body),
                Predicate::Forall(binder.clone(), stated),
            ),
        ] {
            assert_eq!(
                condition_definedness(&definition, vec![quantified], std::slice::from_ref(&ceil_x)),
                vec![expected]
            );
        }
        // An equality with no provably defined side implies neither side's definedness
        // (`\equals(\bottom, \bottom)` is `\top`), and a condition over defined terms has none
        // to state.
        let undecided = Predicate::Equals(partial_x.clone(), partial_y.clone());
        let defined = Predicate::Equals(x, value);
        for condition in [undecided, defined, ceil_x.clone()] {
            assert_eq!(
                condition_definedness(&definition, vec![condition.clone()], &[]),
                vec![condition]
            );
        }
    }

    /// A map and a set over an opaque rest, with a partial function on keys; `membership`
    /// declares further symbols.
    fn collection_definition(membership: &str) -> BackendDefinition {
        let source = r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortKey{} [hasDomainValues{}()]
                sort SortValue{} [hasDomainValues{}()]
                sort SortState{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                hooked-symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                hooked-sort SortSet{}
                    [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
                hooked-symbol setUnit{}() : SortSet{}
                    [function{}(), total{}(), hook{}("SET.unit")]
                hooked-symbol setItem{}(SortKey{}) : SortSet{}
                    [function{}(), total{}(), hook{}("SET.element")]
                hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{}
                    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}()]
                symbol pick{}(SortKey{}) : SortKey{} [function{}()]
                symbol state{}(SortMap{}, SortSet{}) : SortState{} [constructor{}()]
                $MEMBERSHIP
            endmodule []"#
            .replace("$MEMBERSHIP", membership);
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// `ceil_term` of the state holding `map` and `set`, after the definedness of `pick(K)`.
    fn collection_obligations(
        definition: &BackendDefinition,
        map: &str,
        set: &str,
    ) -> (Vec<Predicate>, Predicate) {
        let state = format!("state{{}}({map}, {set})");
        let term = definition
            .internalize_term(&parse_pattern(&state).unwrap(), &[])
            .unwrap();
        let pick = definition
            .internalize_term(&parse_pattern("pick{}(K:SortKey{})").unwrap(), &[])
            .unwrap();
        (ceil_term(definition, &term), Predicate::Ceil(pick))
    }

    fn internal(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(source).unwrap(), &[])
            .unwrap()
    }

    /// The map and the set collections of [`collection_definition`].
    fn keyed_collections(definition: &BackendDefinition) -> (KeyedCollection, KeyedCollection) {
        let map = internal(
            definition,
            "mapConcat{}(mapItem{}(K:SortKey{}, V:SortValue{}), M:SortMap{})",
        );
        let set = internal(
            definition,
            "setConcat{}(setItem{}(K:SortKey{}), S:SortSet{})",
        );
        let (
            TermKind::Map {
                definition: map, ..
            },
            TermKind::Set {
                definition: set, ..
            },
        ) = (map.kind(), set.kind())
        else {
            panic!("a map and a set");
        };
        (
            KeyedCollection::Map(map.clone()),
            KeyedCollection::Set(set.clone()),
        )
    }

    fn absence(
        definition: &BackendDefinition,
        collection: &KeyedCollection,
        key: &str,
        rest: &str,
    ) -> Predicate {
        Absence::predicate(
            collection.clone(),
            internal(definition, key),
            internal(definition, rest),
        )
    }

    /// Without a membership function, a key's absence from the rest of its map, and an
    /// element's absence from the rest of its set, is one atom about the key and the rest: the
    /// entry's value does not occur in it, and it is a fixed point of predicate simplification.
    #[test]
    fn absence_from_an_opaque_rest_is_one_atom_whatever_the_value() {
        let definition = collection_definition("");
        let (map, set) = keyed_collections(&definition);
        let set_source = "setConcat{}(setItem{}(pick{}(K:SortKey{})), S:SortSet{})";
        let (obligations, pick) = collection_obligations(
            &definition,
            "mapConcat{}(mapItem{}(pick{}(K:SortKey{}), V:SortValue{}), M:SortMap{})",
            set_source,
        );
        let expected = vec![
            pick,
            absence(&definition, &map, "pick{}(K:SortKey{})", "M:SortMap{}"),
            absence(&definition, &set, "pick{}(K:SortKey{})", "S:SortSet{}"),
        ];
        assert_eq!(obligations, expected);
        assert!(
            expected[1..]
                .iter()
                .all(|atom| matches!(atom, Predicate::Absent(_)))
        );
        let (other_value, _) = collection_obligations(
            &definition,
            r#"mapConcat{}(mapItem{}(pick{}(K:SortKey{}), \dv{SortValue{}}("1")), M:SortMap{})"#,
            set_source,
        );
        assert_eq!(other_value, expected);

        let simplified = simplify_predicates_with_solver(
            &definition,
            &obligations,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap()
        .unwrap();
        assert_eq!(simplified, obligations);
    }

    /// Two entries over one rest: one absence per entry, each from the rest alone, beside the
    /// keys' disequality.
    #[test]
    fn each_entry_beside_an_opaque_rest_has_its_own_absence_obligation() {
        let definition = collection_definition("");
        let (map, _) = keyed_collections(&definition);
        let source = r#"mapConcat{}(mapConcat{}(mapItem{}(A:SortKey{}, V:SortValue{}),
            mapItem{}(B:SortKey{}, W:SortValue{})), M:SortMap{})"#;
        let (obligations, _) =
            collection_obligations(&definition, source, "setItem{}(A:SortKey{})");
        assert_eq!(
            obligations,
            vec![
                Predicate::Not(Box::new(Predicate::Equals(
                    internal(&definition, "A:SortKey{}"),
                    internal(&definition, "B:SortKey{}")
                ))),
                absence(&definition, &map, "A:SortKey{}", "M:SortMap{}"),
                absence(&definition, &map, "B:SortKey{}", "M:SortMap{}"),
            ]
        );
    }

    /// A membership function at exactly the key (or element) and collection sorts states the
    /// absence as its negation.
    #[test]
    fn a_membership_function_states_absence_from_an_opaque_rest() {
        let definition = collection_definition(
            r#"hooked-symbol inKeys{}(SortKey{}, SortMap{}) : SortBool{}
                    [function{}(), total{}(), hook{}("MAP.in_keys")]
                hooked-symbol inSet{}(SortKey{}, SortSet{}) : SortBool{}
                    [function{}(), total{}(), hook{}("SET.in")]"#,
        );
        let (obligations, _) = collection_obligations(
            &definition,
            "mapConcat{}(mapItem{}(K:SortKey{}, V:SortValue{}), M:SortMap{})",
            "setConcat{}(setItem{}(K:SortKey{}), S:SortSet{})",
        );
        let not_member = |source: &str| {
            Predicate::Not(Box::new(Predicate::Term(
                definition
                    .internalize_term(&parse_pattern(source).unwrap(), &[])
                    .unwrap(),
            )))
        };
        assert_eq!(
            obligations,
            vec![
                not_member("inKeys{}(K:SortKey{}, M:SortMap{})"),
                not_member("inSet{}(K:SortKey{}, S:SortSet{})"),
            ]
        );
    }

    /// Once its rest is a collection with entries, an absence is decided through them: false
    /// when they bind the key, the absences of the key and of theirs from their own rest when
    /// they do not, and no obligation over a unit.
    #[test]
    fn an_absence_is_decided_through_the_entries_of_its_rest() {
        let definition = collection_definition("");
        let (map, set) = keyed_collections(&definition);
        let simplified = |predicate: Predicate| {
            simplify_predicates_with_solver(
                &definition,
                &[predicate],
                &[],
                SimplificationOptions::default(),
                &NoSolver,
            )
            .unwrap()
            .unwrap()
        };
        let a = r#"\dv{SortKey{}}("a")"#;
        let b = r#"\dv{SortKey{}}("b")"#;
        let map_rest = |key: &str| {
            format!("mapConcat{{}}(mapItem{{}}({key}, W:SortValue{{}}), N:SortMap{{}})")
        };
        let set_rest = |key: &str| format!("setConcat{{}}(setItem{{}}({key}), T:SortSet{{}})");

        assert_eq!(
            simplified(absence(&definition, &map, a, &map_rest(a))),
            vec![Predicate::False]
        );
        assert_eq!(
            simplified(absence(&definition, &map, a, &map_rest(b))),
            vec![
                absence(&definition, &map, a, "N:SortMap{}"),
                absence(&definition, &map, b, "N:SortMap{}"),
            ]
        );
        assert_eq!(
            simplified(absence(&definition, &map, a, "mapUnit{}()")),
            Vec::<Predicate>::new()
        );

        assert_eq!(
            simplified(absence(&definition, &set, a, &set_rest(a))),
            vec![Predicate::False]
        );
        assert_eq!(
            simplified(absence(&definition, &set, a, &set_rest(b))),
            vec![
                absence(&definition, &set, a, "T:SortSet{}"),
                absence(&definition, &set, b, "T:SortSet{}"),
            ]
        );
        assert_eq!(
            simplified(absence(&definition, &set, a, "setUnit{}()")),
            Vec::<Predicate>::new()
        );
    }

    /// An absence prints as a pattern the standalone verifier accepts, `\exists V. \ceil(K |->
    /// V R)` for a map and `\ceil(SetItem(K) R)` for a set, and that pattern reads back as the
    /// same atom. A map's binder is named apart from the variables of the key and the rest, and
    /// a rest with entries of its own is kept apart from the key's entry. A set whose rest has
    /// elements of its own is stated as the plain `\ceil` of the joined set, which reads back
    /// as itself.
    #[test]
    fn an_absence_prints_as_a_verified_pattern_that_reads_back_as_itself() {
        let definition = collection_definition("");
        let (map, set) = keyed_collections(&definition);
        let state = Sort::simple("SortState");
        let atoms = [
            absence(&definition, &map, "pick{}(K:SortKey{})", "M:SortMap{}"),
            absence(
                &definition,
                &map,
                "K:SortKey{}",
                "mapConcat{}(mapItem{}(J:SortKey{}, Value-bbinder0:SortValue{}), M:SortMap{})",
            ),
            absence(&definition, &map, "K:SortKey{}", "mapUnit{}()"),
            absence(&definition, &set, "pick{}(K:SortKey{})", "S:SortSet{}"),
        ];
        let Predicate::Absent(spelled_apart) = &atoms[1] else {
            panic!("a map absence is an atom");
        };
        assert_eq!(
            spelled_apart.binder().map(|binder| binder.name.to_string()),
            Some("Value!binder1".to_owned())
        );
        let set_over_elements = absence(
            &definition,
            &set,
            "K:SortKey{}",
            "setConcat{}(setItem{}(J:SortKey{}), S:SortSet{})",
        );
        assert!(matches!(set_over_elements, Predicate::Ceil(_)));
        for predicate in atoms.iter().chain([&set_over_elements]) {
            let printed = crate::externalize::predicate_pattern(predicate, &state);
            let read = definition
                .verify_standalone_pattern(&printed, &[])
                .unwrap_or_else(|error| panic!("{printed:?} does not verify: {error}"))
                .internalize_predicate()
                .unwrap_or_else(|error| panic!("{printed:?} does not internalize: {error}"))
                .0;
            assert_eq!(&read, predicate, "{printed:?}");
        }
    }

    #[test]
    fn nested_partial_definedness_exposes_child_obligations_to_simplification() {
        let definition = definition("");
        let parse = |source| {
            definition
                .internalize_term(&parse_pattern(source).unwrap(), &[])
                .unwrap()
        };
        let child = parse("partial{}(X:SortS{})");
        let parent = parse("partial{}(partial{}(X:SortS{}))");
        let parent_ceil = Predicate::Ceil(parent);
        let child_ceil = Predicate::Ceil(child);

        // Applications are strict in each argument. A defined outer application and an
        // undefined inner application describe no state, even without an SMT solver.
        let contradictory = simplify_predicates_with_solver(
            &definition,
            &[
                parent_ceil.clone(),
                Predicate::Not(Box::new(child_ceil.clone())),
            ],
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        );
        assert_eq!(contradictory, Ok(Ok(vec![Predicate::False])));

        let consistent = simplify_predicates_with_solver(
            &definition,
            &[parent_ceil, child_ceil],
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap()
        .unwrap();
        assert!(!consistent.contains(&Predicate::False));
        assert!(!consistent.is_empty());
    }

    #[test]
    fn ceil_equations_discharge_partial_rhs_obligations() {
        let definition = definition(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{R, R}(
                    \ceil{SortS{}, R}(partial{}(X:SortS{})),
                    \top{R}()
                )
            ) [label{}("partial-defined")]
            "#,
        );
        let rule = rewrite_rule(&definition);

        assert!(rule.attributes.preserves_definedness);
        assert!(rule.computed_attributes.undefined_symbols.is_empty());
    }

    #[test]
    fn unresolved_partial_rhs_becomes_a_definedness_constraint() {
        let definition = definition("");
        let subject = definition
            .internalize_term(
                &parse_pattern(r#"wrap{}(\dv{SortS{}}("value"))"#).unwrap(),
                &[],
            )
            .unwrap();
        let mut fresh = crate::fresh::FreshCounter::default();

        let RewriteResult::Branch {
            branches,
            remainder: None,
            trivial,
            ..
        } = rewrite_step(
            &definition,
            &Pattern {
                term: subject,
                constraints: Vec::new(),
            },
            &mut fresh,
        )
        .expect("no stop is armed")
        else {
            panic!("the symbolic definedness branch should be retained");
        };
        let [applied] = branches.as_slice() else {
            panic!("one candidate: {branches:?}");
        };
        assert_eq!(applied.unique_id, "uses-partial");
        let [ceil @ Predicate::Ceil(term)] = applied.pattern.constraints.as_slice() else {
            panic!("the candidate carries the obligation: {applied:?}");
        };
        assert!(
            matches!(term.kind(), TermKind::Application { symbol, .. } if symbol.name.as_ref() == "partial")
        );
        // The instances where the obligation fails are the carried entry's.
        let [entry] = trivial.as_slice() else {
            panic!("one carried entry: {trivial:?}");
        };
        assert_eq!(entry.kind, crate::rewrite::TrivialKind::Carried);
        assert_eq!(entry.undefined, Predicate::Not(Box::new(ceil.clone())));
    }

    #[test]
    fn simplifies_an_instantiated_rhs_before_checking_definedness() {
        let definition = definition(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    partial{}(X:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("evaluate-partial"), simplification{}()]
            "#,
        );
        let subject = definition
            .internalize_term(
                &parse_pattern(r#"wrap{}(\dv{SortS{}}("value"))"#).unwrap(),
                &[],
            )
            .unwrap();
        let mut fresh = crate::fresh::FreshCounter::default();

        let RewriteResult::Finished(applied) = rewrite_step(
            &definition,
            &Pattern {
                term: subject,
                constraints: Vec::new(),
            },
            &mut fresh,
        )
        .expect("no stop is armed") else {
            panic!("evaluated RHS should be defined");
        };
        assert_eq!(
            applied.pattern.term,
            Term::domain_value(Sort::simple("SortS"), "value")
        );
    }

    #[test]
    fn lhs_definedness_assumptions_cancel_identical_rhs_obligations() {
        let source = r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol partial{}(SortS{}) : SortS{} [function{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(partial{}(X:SortS{}), \top{SortS{}}()),
                    partial{}(X:SortS{})
                ) [label{}("preserved")]
            endmodule []"#;
        let syntax = parse_definition(source).unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();

        assert!(
            rewrite_rule(&definition)
                .computed_attributes
                .undefined_symbols
                .is_empty()
        );
    }
}

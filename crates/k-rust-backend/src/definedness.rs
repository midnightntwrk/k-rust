//! ```toml algorithm
//! id = "backend.definedness.discharge"
//! name = "structural definedness constraint generation and discharge"
//! sites = ["rule_is_defined", "ceil_term", "ceil_predicate", "deduplicate", "ceil_term_recursive", "ceil_term_without_attribute", "ceil_term_node", "elements_are_apart", "terms_apart", "condition_definedness", "condition_atom_term", "hoist_condition_definedness", "nested_condition_definedness"]
//! variable = "t = term size, not counting subterms whose stored ceil_free attribute is true; m = entries of one map or elements of one set; y = symbols in the definition; q = ceil equations under one partial function head; R = rewrite rules in the definition; l = definedness predicates of one rule"
//! counters = []
//! no_counter = "definedness has no dedicated counter; MatchingProblems, MatchingPairs and SimplifyInvocations count the matching and predicate simplification it calls"
//! span = "per call"
//! consumes = [{ type = "k_rust_backend::matching::MatchResult", role = "match result" }]
//! lean = ["KRust.TermAttributes.ceilFree_sound"]
//!
//! [[cost]]
//! mode = "one term (ceil_term)"
//! bound = "O(1) when the term's stored ceil_free attribute is true (term.rs ceil_free); otherwise O(t) visits with one deduplication clone each, a visit of a ceil_free subterm returning at once, plus m^2 / 2 apartness checks per map or set, each a walk of the two elements' shared fixed-root spine that stops at the first open root, with up to two matching problems for a pair of certified ground normal forms, plus O(y) per entry beside a rest, plus q matches and one predicate simplification per partial application"
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
//! pass over the term, which stops at subterms whose construction-time `ceil_free` attribute is
//! true, plus pairwise apartness checks over map keys and set elements, with `FxHashSet`
//! deduplication; no counter, no worklist loop.

use std::{borrow::Cow, collections::HashSet};

use k_rust_kore::measure::{self, Algorithm};
use rustc_hash::FxHashSet;

use crate::{
    definition::BackendDefinition,
    matching::{
        InjectionEquality, MatchMode, MatchResult, SortGraph, match_injection_equality,
        match_terms_in_definition,
    },
    rewrite::{Pattern, Truth, predicates_truth, substitute_predicates},
    rule::{Predicate, RewriteRule, RuleRhs, TermIndex, rename_apart, term_index},
    simplify::{SimplificationOptions, simplify_predicates_with_solver, term_is_provably_defined},
    smt::{NoSolver, SmtSolver},
    stop::Stoppable,
    term::{
        FunctionType, InjectionComparison, SymbolType, Term, TermKind, Variable, VariableKind,
        head::{Apart, certified_ground_normal_form},
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

pub fn ceil_term(definition: &BackendDefinition, term: &Term) -> Vec<Predicate> {
    let _span = measure::algorithm_span(Algorithm::BackendDefinedness);
    ceil_term_recursive(definition, term)
}

/// `ceil_term` below the span: returns at once on a `ceil_free` term.
///
/// Sound because `ceil_free` (term.rs) is true only when `ceil_term_node` would return no
/// predicate for the term under every definition: `lean/KRust/TermAttributes.lean` proves it
/// (`ceilFree_sound`) for the model of `ceil_term_node` and of the attribute, from the constructor
/// invariants that `tests/backend/term_order.rs` checks. The attribute depends only on the term,
/// never on the definition, so one stored bit serves every definition a process holds. In debug
/// builds the walk that never reads the attribute is recomputed wherever the shortcut is taken.
fn ceil_term_recursive(definition: &BackendDefinition, term: &Term) -> Vec<Predicate> {
    if term.attributes().ceil_free() {
        debug_assert!(
            ceil_term_without_attribute(definition, term).is_empty(),
            "a ceil_free term has definedness obligations: {term:?}"
        );
        return Vec::new();
    }
    ceil_term_node(definition, term, ceil_term_recursive)
}

/// The definedness walk without the `ceil_free` shortcut at any depth: the reference the
/// shortcut is checked against (the `debug_assert!` above and `tests::definedness`).
pub(crate) fn ceil_term_without_attribute(
    definition: &BackendDefinition,
    term: &Term,
) -> Vec<Predicate> {
    ceil_term_node(definition, term, ceil_term_without_attribute)
}

/// One node of the definedness walk; `recurse` computes the children's predicates.
fn ceil_term_node(
    definition: &BackendDefinition,
    term: &Term,
    recurse: fn(&BackendDefinition, &Term) -> Vec<Predicate>,
) -> Vec<Predicate> {
    let mut predicates = match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial) => {
            let mut predicates = apply_ceil_equation(definition, term)
                .unwrap_or_else(|| vec![Predicate::Ceil(term.clone())]);
            // Applications are strict in their arguments. Keep this knowledge explicit
            // even when the parent's ceil is opaque to predicate simplification and SMT.
            for argument in arguments {
                predicates.extend(recurse(definition, argument));
            }
            predicates
        }
        TermKind::Application { arguments, .. } => arguments
            .iter()
            .flat_map(|argument| recurse(definition, argument))
            .collect(),
        TermKind::And(left, right) => {
            let mut predicates = recurse(definition, left);
            predicates.extend(recurse(definition, right));
            predicates
        }
        TermKind::Injection { term, .. } => recurse(definition, term),
        TermKind::Map { entries, rest, .. } => {
            let mut predicates = entries
                .iter()
                .flat_map(|(key, value)| {
                    recurse(definition, key)
                        .into_iter()
                        .chain(recurse(definition, value))
                })
                .collect::<Vec<_>>();
            if let Some(rest) = rest {
                predicates.extend(recurse(definition, rest));
            }
            for (position, (left, _)) in entries.iter().enumerate() {
                for (right, _) in &entries[position + 1..] {
                    // R-def: this list states both elements' definedness obligations, so
                    // an apart pair's disequality is implied wherever the list holds.
                    if !elements_are_apart(definition, left, right) {
                        predicates.push(Predicate::Not(Box::new(Predicate::Equals(
                            left.clone(),
                            right.clone(),
                        ))));
                    }
                }
                if let Some(rest) = rest {
                    predicates.push(not_in_collection(definition, "MAP.in_keys", left, rest));
                }
            }
            predicates
        }
        TermKind::List { heads, rest, .. } => heads
            .iter()
            .chain(
                rest.iter()
                    .flat_map(|(middle, tails)| std::iter::once(middle).chain(tails)),
            )
            .flat_map(|term| recurse(definition, term))
            .collect(),
        TermKind::Set { elements, rest, .. } => {
            let mut predicates = elements
                .iter()
                .flat_map(|element| recurse(definition, element))
                .collect::<Vec<_>>();
            if let Some(rest) = rest {
                predicates.extend(recurse(definition, rest));
            }
            for (position, left) in elements.iter().enumerate() {
                for right in &elements[position + 1..] {
                    // R-def: this list states both elements' definedness obligations, so
                    // an apart pair's disequality is implied wherever the list holds.
                    if !elements_are_apart(definition, left, right) {
                        predicates.push(Predicate::Not(Box::new(Predicate::Equals(
                            left.clone(),
                            right.clone(),
                        ))));
                    }
                }
                if let Some(rest) = rest {
                    predicates.push(not_in_collection(definition, "SET.in", left, rest));
                }
            }
            predicates
        }
        TermKind::DomainValue { .. } => Vec::new(),
        // KORE element variables range over elements and are therefore defined. Set variables
        // range over arbitrary patterns, so their definedness remains an explicit obligation.
        TermKind::Variable(variable) if variable.kind == VariableKind::Element => Vec::new(),
        TermKind::Variable(_) => vec![Predicate::Ceil(term.clone())],
    };
    deduplicate(&mut predicates);
    predicates
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

fn apply_ceil_equation(definition: &BackendDefinition, term: &Term) -> Option<Vec<Predicate>> {
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
    for predicate in ceil_term(definition, &pattern.term) {
        if !knowledge.contains(&predicate) {
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
        obligations.extend(ceil_term_recursive(definition, term));
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
        | Predicate::In(..) => predicate.clone(),
        Predicate::Term(_) | Predicate::Equals(..) => {
            let Some(term) = condition_atom_term(definition, predicate, known) else {
                return predicate.clone();
            };
            let mut conjuncts = ceil_term_recursive(definition, term);
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

fn not_in_collection(
    definition: &BackendDefinition,
    hook: &str,
    element: &Term,
    collection: &Term,
) -> Predicate {
    let application = definition.symbols().values().find_map(|symbol| {
        (symbol.attributes.hook.as_deref() == Some(hook)
            && symbol.argument_sorts.as_slice() == [element.sort(), collection.sort()])
        .then(|| {
            Term::application(
                symbol.clone(),
                Vec::new(),
                vec![element.clone(), collection.clone()],
            )
        })
    });
    application.map_or_else(
        || Predicate::Not(Box::new(Predicate::In(element.clone(), collection.clone()))),
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
    /// leaves an empty vector empty, so an arm of `ceil_term_recursive` whose parts are all empty
    /// returns the empty vector.
    #[test]
    fn deduplicate_keeps_an_empty_vector_empty() {
        let mut predicates = Vec::new();

        deduplicate(&mut predicates);

        assert_eq!(predicates, Vec::<Predicate>::new());
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

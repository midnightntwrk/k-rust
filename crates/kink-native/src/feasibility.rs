//! Feasibility of execution leaves and backend-decided payload relations.
//!
//! Both are decided by k-rust's own definition, unifier and solver, never by host term
//! comparison.
//!
//! **Leaf feasibility.** A leaf state is [`LeafFeasibility::Syntactic`] when it internalizes to a
//! term with no predicate conjunct that contains only free constructors, sort injections, domain
//! values and element variables of inhabited sorts. Free constructors are total and injective,
//! so every valuation of the variables over their inhabited sorts gives a value: the state has
//! an instance. With a solver present, a constrained state over such a term is
//! [`LeafFeasibility::Solver`] when the solver answers `Sat` for exactly its predicate
//! conjuncts and they translate without approximation (`smt::translation_exactness`: no term
//! abstracted to a fresh constant, no uninterpreted `smtlib` function, no partial function
//! made total, and only `Int`/`Bool` variables and quantifiers; otherwise a `Sat` is not
//! evidence), and [`LeafFeasibility::Unsat`] when the solver answers `Unsat` under the
//! definedness premise of k-rust `smt.rs:176-183,736-744`: every partial term relied on by
//! the predicate has its definedness explicit in it. This is trust-base item T-UNSAT
//! (variable-identity README 16.4, D-B), pinned by TB-01. A feasible state has an instance, and that instance
//! follows the leaf's path, because k-rust keeps every rule condition it relied on (`requires`
//! with the definedness of its partial terms, narrowing conditions, remainders, and the
//! definedness of partial terms in right-hand sides and simplified states) in the leaf
//! predicate.
//!
//! **Stuckness.** A `Stuck` halt says that no instance of the leaf state under its constraints
//! has a rewrite successor, in both profiles: k-rust offers every rule to a subject whose top
//! is not rigid, refutes a rule only at a head that is the same on every instance, and ends an
//! undecided step `Indeterminate`. The halt does not say that the state has an instance.
//! k-rust gives an undefined rewrite step a `Trivial` leaf with its pre-step state and the
//! condition under which no defined successor exists. The leaves of an unbounded execution
//! therefore cover the initial state under strategy `all`.
//!
//! **Relations.** [`BackendRelations`] answers `relate` by jointly unifying the assumptions made
//! so far with the new pair through `unify_term_pairs`, and `feasible` by jointly unifying the
//! assumptions. Unification preserves the solutions of the equation set, so a proved clash means
//! no instance satisfies them, and a solved form without residual constraints is equivalent to
//! them. Only clashes that hold in K's constructor algebra count (distinct free constructors, a
//! free constructor against an injection, distinct domain values with an injective codec, and a
//! variable occurring under free constructors); anything else, including a residual function
//! equation, is undecided. Two distinct ground terms are not assumed unequal. Terms that the
//! unifier would decompose on a non-`anywhere` `injective` declaration or a non-free
//! `constructor` declaration are undecided unless identical (see `decomposes_freely`).
//!
//! `feasible` decides the *relation query* of a real-prefix path: its path predicate, the
//! residual constraints of the assumptions' joint unification, and the unifier's substitution.
//! A binding `x = t` whose value `t` is a constructor term over inhabited sorts and whose
//! variable `x` occurs in neither the path predicate nor a residual constraint is *eliminated*:
//! any valuation of the other variables extends to one satisfying it (define `x` as the value of
//! `t`; the substitution is idempotent). The remaining conjuncts are the solver query. `Sat` needs
//! either an empty query (no solver is asked, in both profiles), or a solver `Sat` for exactly
//! that query with all of it translating without approximation and every variable of it an
//! initial-state variable: the model then values the query's `Int`/`Bool` variables, every other
//! variable takes any value of its inhabited sort, and the eliminated ones follow. A solver
//! `Unsat` counts under the same explicit definedness premise (T-UNSAT), because the query
//! is implied by the path predicate and the assumptions. Such an instance follows the path: without a solver every valuation does
//! (k-rust turns every binding of a subject variable into a match condition and needs the
//! solver to accept one, `rewrite/apply.rs` phases P7 and P10); with Z3, every rule condition
//! k-rust relied on stays in the leaf predicate (the evidence behind [`LeafFeasibility::Solver`]),
//! so every model of the path predicate does.
//!
//! **Variable identity (T-VI).** Names are read verbatim (`definition.rs:1046-1066`).
//! Printing is injective with capture-avoiding binder renaming (`term/names.rs:33-61`,
//! `externalize.rs:791-880`): a printed response read back is a bijective renaming of the
//! internal response that fixes the request's names. One growing counter per request skips
//! every request spelling (`fresh.rs:1082-1099`), so no free mint is reused or prints like a
//! request variable. Within a request one name, kind and sort identifies one variable.
//! Across requests only the test's initial variables are shared ([`InitialVariables`]).
//! An equation instance with unbound result variables is unused and carries an
//! UndecidedCondition diagnostic (`docs/compatibility.md:792-815`); the bridge maps a
//! diagnosed leaf to BackendLimit, never a complete path.

use std::collections::BTreeSet;

use k_rust::kore::ast::{Pattern, Sort as KoreSort, Variable as KoreVariable};
use k_rust::names::BuiltinSort;
use k_rust_backend::definition::BackendDefinition;
use k_rust_backend::externalize;
use k_rust_backend::rule::Predicate;
use k_rust_backend::smt::{Exactness, Satisfiability, SmtSolver, translation_exactness};
use k_rust_backend::substitution::{Substitution, substitute};
use k_rust_backend::term::{
    HeadRole, Sort, Symbol, SymbolType, Term, TermKind, Variable, VariableKind,
};
use k_rust_backend::unification::{
    Unification, UnificationFailure, UnificationResult, unify_term_pairs,
};
use kink_pattern::{Feasibility, PathInput, RelationDecider, RelationDecision, TermRelation};

/// k-rust's variable-identity contract, version 3 (T-VI; module documentation): verbatim
/// reading, injective printing with binder renaming, and unique free mints from one growing
/// counter per request that skips every request spelling. These premises justify leaf Unsat
/// and discard, relation Equal/Unequal/Unsat, step identity, and certificate generalization.
/// Unbound-result equation instances are unused and diagnosed, hence incomplete in the bridge.
/// A contract mismatch fails compilation instead of silently removing a premise.
const _: () = assert!(k_rust_backend::term::names::VARIABLE_IDENTITY == 3);

/// Whether a leaf state is shown to have an instance, or shown to have none.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum LeafFeasibility {
    /// A predicate-free term of free constructors, injections, domain values and element
    /// variables of inhabited sorts: every valuation is an instance.
    Syntactic,
    /// Such a term under predicate conjuncts that translate exactly to SMT and that the solver
    /// answered `Sat`: the solver's model, extended by any values of the other variables, is an
    /// instance.
    Solver,
    /// The solver answered `Unsat` for the predicate conjuncts: the state has no instance.
    Unsat,
    /// Neither shown.
    Unknown,
}

/// The sorts of a backend definition that have a value: a sort with domain values, a hooked
/// map, list or set sort (the empty collection), the result sort of a free constructor whose
/// argument sorts have values, or a supersort of such a sort. Only sorts without parameters are
/// considered; anything else is conservatively not shown inhabited.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Inhabitation {
    sorts: BTreeSet<Sort>,
}

impl Inhabitation {
    /// The least fixpoint over `definition`.
    pub(crate) fn of(definition: &BackendDefinition) -> Self {
        let simple = definition
            .sorts()
            .iter()
            .filter(|(_, info)| info.parameters.is_empty())
            .map(|(name, info)| {
                let values = info.has_domain_values
                    || matches!(
                        info.hook.as_deref(),
                        Some("MAP.Map" | "LIST.List" | "SET.Set")
                    );
                (Sort::simple(name.clone()), values)
            })
            .collect::<Vec<_>>();
        let mut sorts = simple
            .iter()
            .filter(|(_, values)| *values)
            .map(|(sort, _)| sort.clone())
            .collect::<BTreeSet<_>>();
        loop {
            let before = sorts.len();
            for symbol in definition.symbols().values() {
                if free_constructor(symbol)
                    && symbol
                        .argument_sorts
                        .iter()
                        .all(|sort| sorts.contains(sort))
                {
                    sorts.insert(symbol.result_sort.clone());
                }
            }
            for (sort, _) in &simple {
                if !sorts.contains(sort)
                    && sorts.iter().any(|sub| {
                        definition
                            .sort_graph()
                            .check_subsort(sub, sort)
                            .unwrap_or(false)
                    })
                {
                    sorts.insert(sort.clone());
                }
            }
            if sorts.len() == before {
                return Self { sorts };
            }
        }
    }

    pub(crate) fn contains(&self, sort: &Sort) -> bool {
        self.sorts.contains(sort)
    }
}

/// The test's initial state, as the stable-name source of the cross-request rule
/// ([`InitialVariables`]; variable-identity README VI-R7).
///
/// It is the only input that [`BackendRelations::shared`],
/// [`crate::step_events::ObservationDecider::new`] and
/// [`crate::execution_difference::certify_difference`] accept for the variables they link
/// between requests. The pattern must be the one every k-rust request that kink combines for
/// one test receives as its input: the initial configuration of the test, run on the baseline
/// and on the mutant, stepped and event-free. A leaf state, an observed payload or any other
/// state of a request is not one: its minted names belong to that request alone, and wrapping
/// it here would make them stable across requests. In production the only construction is the
/// campaign runner's, from `TestCase::initial_state`, the same pattern it executes.
#[derive(Clone, Copy, Debug)]
pub struct TestInitialState<'a>(&'a Pattern);

impl<'a> TestInitialState<'a> {
    /// The initial state of a test, which every request whose payloads are combined received.
    #[must_use]
    pub const fn of_test(initial_state: &'a Pattern) -> Self {
        Self(initial_state)
    }

    /// The pattern.
    #[must_use]
    pub const fn pattern(self) -> &'a Pattern {
        self.0
    }
}

/// The variables that kink links across requests: the free element variables of the **test's**
/// initial state, when every free variable of it internalizes to an element variable of an
/// inhabited sort, and none otherwise.
///
/// **Cross-request rule.** kink combines the payloads of several k-rust requests: the baseline
/// run and the mutant run of a test, and the stepped run of each. Under the variable-identity
/// contract the only names such requests share are their request names, and every one of these
/// requests has the test's initial state as its input. So an initial variable means the same
/// variable in every state of every path of each of them (no mint re-binds a request name), and
/// it is the only kind of variable that may be identified between them: a minted name of one
/// request says nothing about a minted name of another (exploration order and rule-variable
/// names choose them). The spelling of an initial name does not matter (`X1`, `ExVarI0` and
/// `Ex-hX-b0` are stable like `X`). The only input is a [`TestInitialState`].
pub(crate) struct InitialVariables;

impl InitialVariables {
    /// The test's initial variables per the type documentation; `None` when some free variable
    /// of `initial` is not an element variable of a sort `inhabitation` shows inhabited.
    pub(crate) fn of(
        definition: &BackendDefinition,
        inhabitation: &Inhabitation,
        initial: TestInitialState<'_>,
    ) -> Option<BTreeSet<Variable>> {
        initial
            .pattern()
            .free_variables()
            .into_iter()
            .map(|variable| {
                match definition
                    .admit_unverified(&Pattern::Variable(variable), &[])
                    .internalize_term()
                    .as_ref()
                    .map(Term::kind)
                {
                    Ok(TermKind::Variable(internal))
                        if internal.kind == VariableKind::Element
                            && inhabitation.contains(&internal.sort) =>
                    {
                        Some(internal.clone())
                    }
                    _ => None,
                }
            })
            .collect()
    }
}

/// A constructor of K's free term algebra: total, injective, and distinct from every other
/// constructor and injection. Freeness is trust-base item T-FREE (D-A, variable-identity
/// README 16.4): Constructor plus HeadRole::FreeConstructor (`term.rs:283-289,520-552`),
/// with no sort variables, hook, collection, binder, macro or alias. Load refuses
/// constructor-headed function equations (`verify.rs:823-867`); kompile never emits both
/// constructor and function (`kompile/module_to_kore/roles.rs:361-380`). A hand-written
/// constructor+function declaration is free under that contract, as decided by D-A.
pub(crate) fn free_constructor(symbol: &Symbol) -> bool {
    let attributes = &symbol.attributes;
    attributes.symbol_type == SymbolType::Constructor
        && attributes.head_role() == HeadRole::FreeConstructor
        && symbol.sort_variables.is_empty()
        && attributes.hook.is_none()
        && attributes.collection.is_none()
        && !attributes.binder
        && !attributes.macro_or_alias
}

/// The solver's answer to `query`, or `None` when it has none. A stop withholds only a
/// refinement: every caller's outcome without an answer (`Unknown`, not proved) is sound, so
/// the stop is dismissed and its owner observes it again.
pub(crate) fn solver_answer(solver: &dyn SmtSolver, query: &[Predicate]) -> Option<Satisfiability> {
    match solver.is_sat(query, &Substitution::new()) {
        Ok(answer) => answer.ok(),
        Err(stop) => {
            stop.forgo_refinement();
            None
        }
    }
}

/// Whether the SMT translation of `query` is exact (`smt::translation_exactness`).
pub(crate) fn translates_exactly(query: &[Predicate]) -> bool {
    translation_exactness(query) == Exactness::Exact
}

/// Whether `term` is built only from free constructors, injections, domain values and element
/// variables of inhabited sorts, so that it has a value under every valuation.
fn constructor_term(term: &Term, inhabitation: &Inhabitation) -> bool {
    match term.kind() {
        TermKind::Variable(variable) => {
            variable.kind == VariableKind::Element && inhabitation.contains(&variable.sort)
        }
        TermKind::DomainValue { .. } => true,
        TermKind::Injection { term, .. } => constructor_term(term, inhabitation),
        TermKind::Application {
            symbol, arguments, ..
        } => {
            free_constructor(symbol)
                && arguments
                    .iter()
                    .all(|argument| constructor_term(argument, inhabitation))
        }
        TermKind::And(..) | TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. } => {
            false
        }
    }
}

/// The feasibility of a leaf state (KORE JSON) per the module documentation. Only the solver's
/// `Sat` and `Unsat` are used, and `Sat` only when the query translates exactly; `NoSolver`
/// contributes nothing.
pub(crate) fn leaf_feasibility(
    definition: &BackendDefinition,
    solver: &dyn SmtSolver,
    inhabitation: &Inhabitation,
    state: &serde_json::Value,
) -> LeafFeasibility {
    let Ok(pattern) = k_rust::kore::codec::from_value(state) else {
        return LeafFeasibility::Unknown;
    };
    let Ok(internal) = definition
        .admit_unverified(&pattern, &[])
        .internalize_pattern()
    else {
        return LeafFeasibility::Unknown;
    };
    let instances = constructor_term(&internal.term, inhabitation);
    if internal.constraints.is_empty() {
        return if instances {
            LeafFeasibility::Syntactic
        } else {
            LeafFeasibility::Unknown
        };
    }
    match solver_answer(solver, &internal.constraints) {
        Some(Satisfiability::Unsat) => LeafFeasibility::Unsat,
        Some(Satisfiability::Sat) if instances && translates_exactly(&internal.constraints) => {
            LeafFeasibility::Solver
        }
        Some(Satisfiability::Sat | Satisfiability::Unknown(_)) | None => LeafFeasibility::Unknown,
    }
}

/// Leaf feasibility under the observation decider's definition-independent query policy.
/// The baseline definition and solver are shared by both sides of a mutant pair.
pub(crate) fn shared_leaf_feasibility(
    definition: &BackendDefinition,
    solver: &dyn SmtSolver,
    inhabitation: &Inhabitation,
    state: &serde_json::Value,
) -> LeafFeasibility {
    let Ok(pattern) = k_rust::kore::codec::from_value(state) else {
        return LeafFeasibility::Unknown;
    };
    if contains_non_strict_injection(definition, &pattern)
        || contains_untrusted_domain_value(definition, &pattern)
    {
        return LeafFeasibility::Unknown;
    }
    let Ok(internal) = definition
        .admit_unverified(&pattern, &[])
        .internalize_pattern()
    else {
        return LeafFeasibility::Unknown;
    };
    let instances = constructor_term(&internal.term, inhabitation);
    if internal.constraints.is_empty() {
        return if instances {
            LeafFeasibility::Syntactic
        } else {
            LeafFeasibility::Unknown
        };
    }
    if !internal
        .constraints
        .iter()
        .all(|predicate| shared_predicate_interpreted(definition, predicate))
    {
        return LeafFeasibility::Unknown;
    }
    match solver_answer(solver, &internal.constraints) {
        Some(Satisfiability::Unsat) => LeafFeasibility::Unsat,
        Some(Satisfiability::Sat) if instances && translates_exactly(&internal.constraints) => {
            LeafFeasibility::Solver
        }
        Some(Satisfiability::Sat | Satisfiability::Unknown(_)) | None => LeafFeasibility::Unknown,
    }
}

/// Only a proper subsort injection has the free decomposition used by step observations.
pub(crate) fn strict_injection_sorts(
    definition: &BackendDefinition,
    source: &KoreSort,
    target: &KoreSort,
) -> bool {
    let simple = |sort: &KoreSort| match sort {
        KoreSort::Application { name, arguments } if arguments.is_empty() => {
            Some(Sort::simple(name.as_str()))
        }
        _ => None,
    };
    let (Some(source), Some(target)) = (simple(source), simple(target)) else {
        return false;
    };
    source != target
        && definition
            .sort_graph()
            .check_subsort(&source, &target)
            .unwrap_or(false)
}

pub(crate) fn non_strict_injection_node(definition: &BackendDefinition, pattern: &Pattern) -> bool {
    let Pattern::Application { symbol, arguments } = pattern else {
        return false;
    };
    if symbol.name != "inj" {
        return false;
    }
    let [source, target] = symbol.sort_parameters.as_slice() else {
        return true;
    };
    arguments.len() != 1 || !strict_injection_sorts(definition, source, target)
}

pub(crate) fn contains_non_strict_injection(
    definition: &BackendDefinition,
    pattern: &Pattern,
) -> bool {
    let mut found = false;
    k_rust::kore::walk::for_each_post_order(pattern, |node| {
        found |= non_strict_injection_node(definition, node);
    });
    found
}

/// Only these decoded domain values have a proven injective codec at the current k-rust pin.
pub(crate) fn domain_value_identity_safe(
    definition: &BackendDefinition,
    sort: &KoreSort,
    bytes: &[u8],
) -> bool {
    let KoreSort::Application { name, arguments } = sort else {
        return false;
    };
    if !arguments.is_empty() {
        return false;
    }
    domain_bytes_identity_safe(definition, name, bytes)
}

fn domain_bytes_identity_safe(definition: &BackendDefinition, name: &str, bytes: &[u8]) -> bool {
    let Some(info) = definition.sorts().get(name) else {
        return false;
    };
    if !info.has_domain_values {
        return false;
    }
    match info.hook.as_deref() {
        Some("INT.Int") => {
            let digits = bytes.strip_prefix(b"-").unwrap_or(bytes);
            !digits.is_empty()
                && digits.iter().all(u8::is_ascii_digit)
                && (digits == b"0" || !digits.starts_with(b"0"))
                && bytes != b"-0"
        }
        Some("BOOL.Bool") => bytes == b"true" || bytes == b"false",
        Some("STRING.String") | None => bytes.is_ascii(),
        _ => false,
    }
}

fn internal_domain_value_identity_safe(
    definition: &BackendDefinition,
    sort: &Sort,
    bytes: &[u8],
) -> bool {
    match sort {
        Sort::Application { name, arguments } if arguments.is_empty() => {
            domain_bytes_identity_safe(definition, name, bytes)
        }
        _ => false,
    }
}

/// An untrusted domain codec blocks decoded-term identity and shared proofs.
pub(crate) fn contains_untrusted_domain_value(
    definition: &BackendDefinition,
    pattern: &Pattern,
) -> bool {
    let mut found = false;
    k_rust::kore::walk::for_each_post_order(pattern, |node| {
        if let Pattern::DomainValue { sort, value } = node {
            found |= !domain_value_identity_safe(definition, sort, value.as_bytes());
        }
    });
    found
}

/// Every term of `predicate` is built from hooked symbols, free constructors, injections,
/// canonical domain values and variables only (no collection and no conjunction term).
pub(crate) fn interpreted_predicate(predicate: &Predicate) -> bool {
    fn interpreted(term: &Term) -> bool {
        match term.kind() {
            TermKind::Variable(_) => true,
            TermKind::DomainValue { sort, value } => {
                !sort.is_builtin(BuiltinSort::String) || value.as_bytes().is_ascii()
            }
            TermKind::Injection { term, .. } => interpreted(term),
            TermKind::Application {
                symbol, arguments, ..
            } => {
                (symbol.attributes.hook.is_some() || free_constructor(symbol))
                    && arguments.iter().all(interpreted)
            }
            TermKind::And(..)
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. } => false,
        }
    }
    let mut all = true;
    predicate.visit_terms(&mut |term| all &= interpreted(term));
    all
}

fn shared_predicate_interpreted(definition: &BackendDefinition, predicate: &Predicate) -> bool {
    let mut safe = interpreted_predicate(predicate);
    predicate.visit_terms(&mut |term| {
        if let TermKind::DomainValue { sort, value } = term.kind() {
            safe &= internal_domain_value_identity_safe(definition, sort, value.as_bytes());
        }
    });
    safe
}

/// The first free element variable of `state` whose sort is not shown inhabited, or the
/// internalization error of a variable.
pub(crate) fn uninhabited_variable(
    definition: &BackendDefinition,
    inhabitation: &Inhabitation,
    state: &Pattern,
) -> Result<Option<KoreVariable>, String> {
    for variable in state.free_variables() {
        let term = definition
            .admit_unverified(&Pattern::Variable(variable.clone()), &[])
            .internalize_term()
            .map_err(|error| format!("{error:?}"))?;
        if let TermKind::Variable(internal) = term.kind()
            && internal.kind == VariableKind::Element
            && !inhabitation.contains(&internal.sort)
        {
            return Ok(Some(variable));
        }
    }
    Ok(None)
}

/// Whether a failed unification proves that its equations have no common instance in K's
/// constructor algebra (see the module documentation).
pub(crate) fn proves_clash(failure: &UnificationFailure) -> bool {
    match failure {
        UnificationFailure::DifferentSymbols(clash) => {
            let (left, right) = (clash.left(), clash.right());
            let free = |term: &Term| {
                matches!(term.kind(), TermKind::Application { symbol, .. }
                    if free_constructor(symbol))
            };
            let injection = |term: &Term| matches!(term.kind(), TermKind::Injection { .. });
            (free(left) && free(right))
                || (free(left) && injection(right))
                || (injection(left) && free(right))
        }
        UnificationFailure::DifferentValues(left, right) => {
            let canonical = |term: &Term| {
                matches!(term.kind(), TermKind::DomainValue { sort, value }
                    if sort.is_builtin(BuiltinSort::Int)
                        || sort.is_builtin(BuiltinSort::Bool)
                        || (sort.is_builtin(BuiltinSort::String) && value.as_bytes().is_ascii()))
            };
            canonical(left) && canonical(right)
        }
        UnificationFailure::VariableRecursion(cycle) => {
            occurs_under_free_constructors(cycle.variable(), cycle.term())
        }
        // Raised for disjoint injections and ill-sorted pairs alike; not claimed.
        UnificationFailure::DifferentSorts(..) => false,
        // An argument-length mismatch is ill-formed, not constructor-algebra evidence.
        UnificationFailure::ArgumentLengthsDiffer(..) => false,
    }
}

fn proves_shared_clash(definition: &BackendDefinition, failure: &UnificationFailure) -> bool {
    match failure {
        UnificationFailure::DifferentValues(left, right) => {
            let safe = |term: &Term| {
                matches!(term.kind(), TermKind::DomainValue { sort, value }
                    if internal_domain_value_identity_safe(definition, sort, value.as_bytes()))
            };
            safe(left) && safe(right)
        }
        _ => proves_clash(failure),
    }
}

/// `variable` occurs in `term` strictly below free constructors and injections only.
fn occurs_under_free_constructors(variable: &Variable, term: &Term) -> bool {
    fn below(variable: &Variable, term: &Term) -> bool {
        match term.kind() {
            TermKind::Variable(found) => found == variable,
            TermKind::Injection { term, .. } => below(variable, term),
            TermKind::Application {
                symbol, arguments, ..
            } if free_constructor(symbol) => {
                arguments.iter().any(|argument| below(variable, argument))
            }
            _ => false,
        }
    }
    !matches!(term.kind(), TermKind::Variable(_)) && below(variable, term)
}

/// Whether every application in `term` that the unifier may decompose on a declared
/// `injective` or `constructor` attribute is a free constructor.
///
/// Decomposing `f(a) = f(b)` into `a = b` is an equivalence only when equal applications of `f`
/// have equal arguments. As documented by `unify_term_pairs`, k-rust decomposes an `anywhere`
/// application only when both sides are normal on every instance under the definition's
/// equations; it does not read `injective` for such a symbol. A non-`anywhere` `injective`
/// symbol instead decomposes on the declared axiom, which k-rust does not check against those
/// equations. The declaration can come from kompile, hand-written KORE, or a mutant, so this
/// decider refuses it unless the symbol satisfies T-FREE (see [`free_constructor`]).
/// EquationHead (anywhere) decomposition is left to k-rust: both applications must be normal
/// on every instance (`unification.rs:154-160`). This is the freeness trust base of README 16.4.
/// Collections are unsupported by the unifier and conservatively excluded.
fn decomposes_freely(term: &Term) -> bool {
    match term.kind() {
        TermKind::Variable(_) | TermKind::DomainValue { .. } => true,
        TermKind::Injection { term, .. } => decomposes_freely(term),
        TermKind::Application {
            symbol, arguments, ..
        } => {
            // A non-anywhere injective head is decomposed on its declaration; it must be free.
            // EquationHead is left to k-rust's normal-on-every-instance decomposition.
            let decomposed = matches!(
                symbol.attributes.head_role(),
                HeadRole::FreeConstructor
                    | HeadRole::Function {
                        injective: true,
                        ..
                    }
            ) || symbol.attributes.symbol_type == SymbolType::Constructor;
            (!decomposed || free_constructor(symbol)) && arguments.iter().all(decomposes_freely)
        }
        TermKind::And(left, right) => decomposes_freely(left) && decomposes_freely(right),
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. } => false,
    }
}

/// Every side of every pair decomposes freely (see [`decomposes_freely`]).
fn pairs_decompose_freely<'t>(pairs: impl IntoIterator<Item = &'t (Term, Term)>) -> bool {
    pairs
        .into_iter()
        .all(|(left, right)| decomposes_freely(left) && decomposes_freely(right))
}

/// `feasible` and `relate` for pattern observations on both sides of a mutant pair, decided by
/// the baseline definition's unifier and solver (see the module documentation).
///
/// The paths must come from [`crate::bridge::paths_from_steps`] over executions of
/// `initial_state` whose signatures match the baseline. Only terms whose variables are the test's
/// initial variables ([`InitialVariables`]) are compared: the paths of both sides come from
/// different requests, and those are the only variables the requests share. Under the
/// variable-identity contract each of them means one value along every path, whatever rules
/// the definitions have, because no variable a request mints has a request variable's name.
pub struct BackendRelations<'a> {
    definition: &'a BackendDefinition,
    solver: &'a dyn SmtSolver,
    inhabitation: Inhabitation,
    /// The test's initial variables, when all of them are inhabited element variables.
    variables: Option<BTreeSet<Variable>>,
}

impl<'a> BackendRelations<'a> {
    /// Relations for pattern observations on both sides of a mutant pair, over the test's
    /// initial state; only interpreted predicates may reach the solver.
    #[must_use]
    pub fn shared(
        definition: &'a BackendDefinition,
        solver: &'a dyn SmtSolver,
        initial_state: TestInitialState<'_>,
    ) -> Self {
        let inhabitation = Inhabitation::of(definition);
        let variables = InitialVariables::of(definition, &inhabitation, initial_state);
        Self {
            definition,
            solver,
            inhabitation,
            variables,
        }
    }

    /// The internalized term, when every variable in it is a stable initial-state variable.
    fn term(&self, pattern: &Pattern) -> Option<Term> {
        let term = self
            .definition
            .admit_unverified(pattern, &[])
            .internalize_term()
            .ok()?;
        let variables = &term.attributes().variables;
        let stable = match &self.variables {
            Some(stable) => variables.is_subset(stable),
            None => variables.is_empty(),
        };
        stable.then_some(term)
    }

    /// The internalized pairs of `relations`, each of one sort.
    fn pairs(&self, relations: &[TermRelation]) -> Option<Vec<(Term, Term)>> {
        relations
            .iter()
            .map(|relation| {
                let left = self.term(&relation.left)?;
                let right = self.term(&relation.right)?;
                (left.sort() == right.sort()).then_some((left, right))
            })
            .collect()
    }

    /// `substitution` as relations with the variable on the left, when each side externalizes
    /// to KORE that internalizes back to the same term.
    fn relations(&self, substitution: &Substitution) -> Option<Vec<TermRelation>> {
        substitution
            .iter()
            .map(|(variable, value)| {
                let variable = Term::variable(variable.clone());
                let left = externalize::term(&variable);
                let right = externalize::term(value);
                (self.term(&left)? == variable && self.term(&right)? == *value)
                    .then_some(TermRelation { left, right })
            })
            .collect()
    }

    /// The solver query of the relation query of `path` under the solved form `solved` (see
    /// the module documentation): the path predicate unless it is `\top`, the residual
    /// constraints, and `x = t` for every binding that is not eliminated. `None` when the path
    /// predicate does not internalize.
    fn relation_query(&self, path: &PathInput, solved: Unification) -> Option<Vec<Predicate>> {
        let mut query = match &path.path_predicate {
            Pattern::Top { .. } => Vec::new(),
            predicate => vec![
                self.definition
                    .admit_unverified(predicate, &[])
                    .internalize_predicate()
                    .ok()?
                    .0,
            ],
        };
        query.extend(solved.constraints);
        let constrained = query
            .iter()
            .flat_map(Predicate::free_variables)
            .collect::<BTreeSet<_>>();
        for (variable, value) in solved.substitution {
            let eliminated =
                !constrained.contains(&variable) && constructor_term(&value, &self.inhabitation);
            if !eliminated {
                query.push(Predicate::Equals(Term::variable(variable), value));
            }
        }
        Some(query)
    }

    /// Decides the relation query of `path` under `solved` (see the module documentation).
    fn decide(&self, path: &PathInput, solved: Unification) -> Feasibility {
        // The eliminated bindings are defined from the other variables only if no bound
        // variable occurs in a value; `unify_term_pairs` promises that, and it is checked.
        let bound = solved.substitution.keys().cloned().collect::<BTreeSet<_>>();
        let idempotent = solved
            .substitution
            .values()
            .all(|value| value.attributes().variables.is_disjoint(&bound));
        let Some(query) = self.relation_query(path, solved) else {
            return Feasibility::Unknown;
        };
        if query.is_empty() {
            return if idempotent {
                Feasibility::Sat
            } else {
                Feasibility::Unknown
            };
        }
        if !query
            .iter()
            .all(|predicate| shared_predicate_interpreted(self.definition, predicate))
        {
            return Feasibility::Unknown;
        }
        // Every variable of an exact `Sat` must be one of the test's initial variables: the
        // model then values variables that both sides' requests share, each one value along the
        // whole path (`InitialVariables`).
        let stable = self.variables.as_ref().is_some_and(|stable| {
            query
                .iter()
                .all(|predicate| predicate.free_variables().is_subset(stable))
        });
        match solver_answer(self.solver, &query) {
            Some(Satisfiability::Unsat) => Feasibility::Unsat,
            Some(Satisfiability::Sat) if idempotent && stable && translates_exactly(&query) => {
                Feasibility::Sat
            }
            Some(Satisfiability::Sat | Satisfiability::Unknown(_)) | None => Feasibility::Unknown,
        }
    }
}

impl RelationDecider for BackendRelations<'_> {
    /// `Equal` for identical terms. For terms that decompose freely: `Unequal` when `assumed`
    /// together with `left = right` has a proved clash, `Equal` when
    /// the solved form of `assumed` already unifies them, `EqualIf` with the solved-form
    /// relations the pair adds (variable on the left), and otherwise `Indeterminate`.
    fn relate(
        &self,
        path: &PathInput,
        assumed: &[TermRelation],
        left: &Pattern,
        right: &Pattern,
    ) -> RelationDecision {
        if contains_non_strict_injection(self.definition, left)
            || contains_non_strict_injection(self.definition, right)
            || contains_non_strict_injection(self.definition, &path.path_predicate)
            || contains_untrusted_domain_value(self.definition, left)
            || contains_untrusted_domain_value(self.definition, right)
            || contains_untrusted_domain_value(self.definition, &path.path_predicate)
            || assumed.iter().any(|relation| {
                contains_non_strict_injection(self.definition, &relation.left)
                    || contains_non_strict_injection(self.definition, &relation.right)
                    || contains_untrusted_domain_value(self.definition, &relation.left)
                    || contains_untrusted_domain_value(self.definition, &relation.right)
            })
        {
            return RelationDecision::Indeterminate;
        }
        let (Some(mut pairs), Some(left), Some(right)) =
            (self.pairs(assumed), self.term(left), self.term(right))
        else {
            return RelationDecision::Indeterminate;
        };
        if left.sort() != right.sort() {
            return RelationDecision::Indeterminate;
        }
        if left == right {
            return RelationDecision::Equal;
        }
        if !decomposes_freely(&left)
            || !decomposes_freely(&right)
            || !pairs_decompose_freely(&pairs)
        {
            return RelationDecision::Indeterminate;
        }
        let UnificationResult::Unified(before) =
            unify_term_pairs(self.definition, Substitution::new(), pairs.clone())
        else {
            return RelationDecision::Indeterminate;
        };
        if !before.constraints.is_empty() {
            return RelationDecision::Indeterminate;
        }
        if substitute(&left, &before.substitution) == substitute(&right, &before.substitution) {
            return RelationDecision::Equal;
        }
        pairs.push((left, right));
        match unify_term_pairs(self.definition, Substitution::new(), pairs) {
            UnificationResult::Bottom(failure)
                if proves_shared_clash(self.definition, &failure) =>
            {
                RelationDecision::Unequal
            }
            UnificationResult::Unified(joint) if joint.constraints.is_empty() => {
                match self.relations(&joint.substitution) {
                    Some(relations) => {
                        let extra = relations
                            .into_iter()
                            .filter(|relation| !assumed.contains(relation))
                            .collect::<Vec<_>>();
                        if extra.is_empty() {
                            RelationDecision::Equal
                        } else {
                            RelationDecision::EqualIf(extra)
                        }
                    }
                    None => RelationDecision::Indeterminate,
                }
            }
            UnificationResult::Bottom(_)
            | UnificationResult::Unified(_)
            | UnificationResult::Unsupported { .. } => RelationDecision::Indeterminate,
        }
    }

    /// On a real-prefix path, for assumptions that decompose freely: `Unsat` on a proved
    /// clash; otherwise the decision of the relation query of the path under their solved form
    /// (see the module documentation): `Sat` for an empty query or an exact solver `Sat`,
    /// `Unsat` for a solver `Unsat`, else `Unknown`.
    fn feasible(&self, path: &PathInput, assumptions: &[TermRelation]) -> Feasibility {
        if contains_non_strict_injection(self.definition, &path.path_predicate)
            || contains_untrusted_domain_value(self.definition, &path.path_predicate)
            || assumptions.iter().any(|relation| {
                contains_non_strict_injection(self.definition, &relation.left)
                    || contains_non_strict_injection(self.definition, &relation.right)
                    || contains_untrusted_domain_value(self.definition, &relation.left)
                    || contains_untrusted_domain_value(self.definition, &relation.right)
            })
        {
            return Feasibility::Unknown;
        }
        if !path.stop.has_real_prefix() {
            return Feasibility::Unknown;
        }
        if assumptions.is_empty() {
            return Feasibility::Sat;
        }
        let Some(pairs) = self.pairs(assumptions) else {
            return Feasibility::Unknown;
        };
        if !pairs_decompose_freely(&pairs) {
            return Feasibility::Unknown;
        }
        match unify_term_pairs(self.definition, Substitution::new(), pairs) {
            UnificationResult::Bottom(failure)
                if proves_shared_clash(self.definition, &failure) =>
            {
                Feasibility::Unsat
            }
            UnificationResult::Unified(solved) => self.decide(path, solved),
            UnificationResult::Bottom(_) | UnificationResult::Unsupported { .. } => {
                Feasibility::Unknown
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::backend::{Backend, BackendError, BackendOptions};
    use k_rust::kompile::CompileOptions;
    use k_rust::kore::{codec, parser::parse_definition};
    use k_rust_backend::smt::{SmtError, Validity};
    use k_rust_backend::stop::Stoppable;
    use kink_pattern::{ExecutionStop, PathStop};

    use crate::{NativeValidator, support};

    use Feasibility::{Sat, Unknown, Unsat};
    use RelationDecision::{Equal, EqualIf, Indeterminate, Unequal};

    fn backend(name: &str, module: &str) -> Backend {
        let validator = NativeValidator::bind(support::load(name), CompileOptions::default());
        let side = validator.compile_baseline().expect("fixture compiles");
        Backend::new(
            &side.artifacts().definition_kore,
            module,
            BackendOptions::default(),
        )
        .expect("backend")
    }

    #[test]
    fn non_ascii_strings_are_not_clashes_or_interpreted_predicates() {
        let value =
            |bytes: &[u8]| Term::domain_value(Sort::builtin(BuiltinSort::String), bytes.to_vec());
        let non_ascii = value("é".as_bytes());
        let other = value("Ã©".as_bytes());
        assert!(!proves_clash(&UnificationFailure::DifferentValues(
            non_ascii.clone(),
            other.clone()
        )));
        assert!(!interpreted_predicate(&Predicate::Equals(non_ascii, other)));
        assert!(proves_clash(&UnificationFailure::DifferentValues(
            value(b"a"),
            value(b"b")
        )));
        assert!(interpreted_predicate(&Predicate::Equals(
            value(b"a"),
            value(b"b")
        )));
    }

    #[test]
    fn shared_relations_refuse_noncanonical_integer_identity() {
        let mut backend = backend("symmem.k", "SYMMEM");
        let state = symmem_state();
        let real = path(PathStop::DepthLimit, top());
        backend
            .with_solver(None, |definition, solver| {
                let relations =
                    BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
                for (bytes, canonical) in [
                    (b"01".as_slice(), b"1".as_slice()),
                    (b"+1", b"1"),
                    (b"-0", b"0"),
                ] {
                    let value = Pattern::DomainValue {
                        sort: k_rust::kompile::initial_configuration::kore_sort("SortInt"),
                        value: bytes.to_vec().into(),
                    };
                    let internal = definition
                        .admit_unverified(&value, &[])
                        .internalize_term()
                        .expect("Int accepts this decimal form");
                    assert_eq!(
                        externalize::term(&internal),
                        Pattern::DomainValue {
                            sort: k_rust::kompile::initial_configuration::kore_sort("SortInt"),
                            value: canonical.to_vec().into(),
                        }
                    );
                    assert_eq!(relations.relate(&real, &[], &value, &value), Indeterminate);
                    assert_eq!(
                        relations.feasible(&real, &[relation(value.clone(), value)]),
                        Unknown
                    );
                }
                Ok::<_, BackendError>(())
            })
            .expect("shared decider");
    }

    fn nat(name: &str) -> Pattern {
        support::var(name, "SortNat")
    }
    fn z() -> Pattern {
        support::app("Lblz", vec![])
    }
    fn s(value: Pattern) -> Pattern {
        support::app("Lbls", vec![value])
    }
    fn addr(value: Pattern) -> Pattern {
        support::app("Lbladdr", vec![value])
    }
    fn relation(left: Pattern, right: Pattern) -> TermRelation {
        TermRelation { left, right }
    }

    /// `seq(write(addr(X), V), seq(load(addr(Y), W), halt))`: every variable the rows use.
    fn symmem_state() -> Pattern {
        let op = |symbol: &str, address: Pattern, value: Pattern| {
            support::app(symbol, vec![addr(address), value])
        };
        support::initial_state(
            support::app(
                "Lblseq",
                vec![
                    op("Lblwrite", nat("X"), nat("V")),
                    support::app(
                        "Lblseq",
                        vec![
                            op("Lblload", nat("Y"), nat("W")),
                            support::app("Lblhalt", vec![]),
                        ],
                    ),
                ],
            ),
            "SortProg",
        )
    }

    fn path(stop: PathStop, predicate: Pattern) -> PathInput {
        PathInput {
            test_id: "t".into(),
            path_ordinal: 0,
            path_key: None,
            complete: false,
            stop,
            execution_stop: ExecutionStop::DepthLimit,
            execution_terminal: None,
            events: Vec::new(),
            path_predicate: predicate,
            equivalences: Vec::new(),
            inequalities: Vec::new(),
        }
    }

    fn top() -> Pattern {
        top_of("SortGeneratedTopCell")
    }

    fn top_of(sort: &str) -> Pattern {
        Pattern::Top {
            sort: k_rust::kompile::initial_configuration::kore_sort(sort),
        }
    }

    #[test]
    fn leaf_feasibility_is_syntactic_only_for_predicate_free_constructor_terms() {
        let mut symmem = backend("symmem.k", "SYMMEM");
        let state = symmem_state();
        let constrained = Pattern::And {
            sort: k_rust::kompile::initial_configuration::kore_sort("SortGeneratedTopCell"),
            arguments: vec![
                state.clone(),
                Pattern::Equals {
                    operand_sort: Box::new(k_rust::kompile::initial_configuration::kore_sort(
                        "SortNat",
                    )),
                    result_sort: k_rust::kompile::initial_configuration::kore_sort(
                        "SortGeneratedTopCell",
                    ),
                    left: Box::new(nat("X")),
                    right: Box::new(z()),
                },
            ],
        };
        let rows = symmem
            .with_solver(None, |definition, solver| {
                let inhabitation = Inhabitation::of(definition);
                let feasibility = |pattern: &Pattern| {
                    leaf_feasibility(
                        definition,
                        solver,
                        &inhabitation,
                        &codec::to_value(pattern).expect("state JSON"),
                    )
                };
                Ok::<_, BackendError>((
                    feasibility(&state),
                    feasibility(&support::initial_state(
                        support::app("Lblhalt", vec![]),
                        "SortProg",
                    )),
                    feasibility(&constrained),
                    uninhabited_variable(definition, &inhabitation, &state),
                ))
            })
            .expect("definition");
        assert_eq!(
            rows.0,
            LeafFeasibility::Syntactic,
            "symbolic constructor state"
        );
        assert_eq!(
            rows.1,
            LeafFeasibility::Syntactic,
            "ground constructor state"
        );
        assert_eq!(rows.2, LeafFeasibility::Unknown, "nonempty predicate");
        assert_eq!(rows.3, Ok(None));

        // `X +Int 1` in address position: a function symbol.
        let mut guarded = backend("guardedmem.k", "GUARDEDMEM");
        let function = guarded
            .with_solver(None, |definition, solver| {
                let plus = definition
                    .symbols()
                    .values()
                    .find(|symbol| symbol.attributes.hook.as_deref() == Some("INT.add"))
                    .expect("+Int")
                    .name
                    .to_string();
                let sum = support::app(&plus, vec![support::var("X", "SortInt"), support::int(1)]);
                let state = support::initial_state(
                    support::app(
                        "Lblseq",
                        vec![
                            support::app("Lblwrite", vec![addr(sum), support::var("V", "SortInt")]),
                            support::app("Lblhalt", vec![]),
                        ],
                    ),
                    "SortProg",
                );
                Ok::<_, BackendError>(leaf_feasibility(
                    definition,
                    solver,
                    &Inhabitation::of(definition),
                    &codec::to_value(&state).expect("state JSON"),
                ))
            })
            .expect("definition");
        assert_eq!(function, LeafFeasibility::Unknown, "function symbol");
    }

    const EMPTY: &str = r"[]
        module MAIN
            sort SortS{} []
            sort SortEmpty{} []
            sort SortWrapped{} []
            symbol Lbla{}() : SortS{} [constructor{}()]
            symbol Lblwrap{}(SortEmpty{}) : SortWrapped{} [constructor{}()]
            symbol Lblpair{}(SortS{}, SortWrapped{}) : SortS{} [constructor{}()]
        endmodule []";

    #[test]
    fn uninhabited_variable_sorts_are_found_by_fixpoint() {
        let definition =
            BackendDefinition::internalize(&parse_definition(EMPTY).expect("KORE"), "MAIN")
                .expect("definition");
        let inhabitation = Inhabitation::of(&definition);
        assert!(inhabitation.contains(&Sort::simple("SortS")));
        assert!(!inhabitation.contains(&Sort::simple("SortEmpty")));
        assert!(!inhabitation.contains(&Sort::simple("SortWrapped")));
        let empty = support::var("VarE", "SortEmpty");
        let state = support::app(
            "Lblpair",
            vec![
                support::app("Lbla", vec![]),
                support::app("Lblwrap", vec![empty.clone()]),
            ],
        );
        let Pattern::Variable(variable) = &empty else {
            unreachable!()
        };
        assert_eq!(
            uninhabited_variable(&definition, &inhabitation, &state),
            Ok(Some(variable.clone()))
        );
        assert_eq!(
            leaf_feasibility(
                &definition,
                &k_rust_backend::smt::NoSolver,
                &inhabitation,
                &codec::to_value(&state).expect("state JSON")
            ),
            LeafFeasibility::Unknown
        );
    }

    #[test]
    fn backend_relations_decide_symmem_payloads_by_unification() {
        let mut symmem = backend("symmem.k", "SYMMEM");
        let real = path(PathStop::DepthLimit, top());
        let (x, y) = (nat("X"), nat("Y"));
        let x_is_y = relation(x.clone(), y.clone());
        // (id, assumed, left, right, expected)
        let rows = [
            (
                "same-address",
                vec![],
                addr(x.clone()),
                addr(x.clone()),
                Equal,
            ),
            (
                "distinct-addresses",
                vec![],
                addr(x.clone()),
                addr(y.clone()),
                EqualIf(vec![x_is_y.clone()]),
            ),
            (
                "reversed-distinct-addresses",
                vec![],
                addr(y.clone()),
                addr(x.clone()),
                EqualIf(vec![x_is_y.clone()]),
            ),
            (
                "already-assumed",
                vec![x_is_y.clone()],
                addr(y.clone()),
                addr(x.clone()),
                Equal,
            ),
            (
                "constructor-clash",
                vec![],
                addr(z()),
                addr(s(y.clone())),
                Unequal,
            ),
            ("occurs-check", vec![], x.clone(), s(x.clone()), Unequal),
            (
                "clash-under-assumption",
                vec![x_is_y.clone()],
                x.clone(),
                s(y.clone()),
                Unequal,
            ),
            ("ground-distinct-constructors", vec![], z(), s(z()), Unequal),
            (
                "instantiation",
                vec![],
                addr(x.clone()),
                addr(s(z())),
                EqualIf(vec![relation(x.clone(), s(z()))]),
            ),
            // A variable that is not an initial-state variable may be renamed or reused.
            ("foreign-variable", vec![], nat("Q"), z(), Indeterminate),
            (
                "different-sorts",
                vec![],
                addr(x.clone()),
                x.clone(),
                Indeterminate,
            ),
        ];
        let state = symmem_state();
        let answers = symmem
            .with_solver(None, |definition, solver| {
                let relations =
                    BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
                Ok::<_, BackendError>(
                    rows.iter()
                        .map(|(id, assumed, left, right, _)| {
                            (*id, relations.relate(&real, assumed, left, right))
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .expect("relations");
        for ((id, answer), (.., expected)) in answers.into_iter().zip(&rows) {
            assert_eq!(&answer, expected, "{id}");
        }
    }

    #[test]
    fn backend_relations_decide_assumption_feasibility_without_a_solver() {
        let mut symmem = backend("symmem.k", "SYMMEM");
        let (x, y) = (nat("X"), nat("Y"));
        let constrained = Pattern::Equals {
            operand_sort: Box::new(k_rust::kompile::initial_configuration::kore_sort("SortNat")),
            result_sort: k_rust::kompile::initial_configuration::kore_sort("SortGeneratedTopCell"),
            left: Box::new(y.clone()),
            right: Box::new(z()),
        };
        // On a `\top` path, bindings of variables to constructor terms are eliminated and the
        // relation query is empty: `Sat` without asking a solver, in both profiles (SYM-3B-03).
        // (id, path, assumptions, expected)
        let rows = [
            (
                "empty-on-real-prefix",
                path(PathStop::DepthLimit, top()),
                vec![],
                Sat,
            ),
            (
                "variable-identification",
                path(PathStop::DepthLimit, top()),
                vec![relation(x.clone(), y.clone())],
                Sat,
            ),
            (
                "constructor-instantiation",
                path(PathStop::Terminal, top()),
                vec![relation(x.clone(), s(y.clone()))],
                Sat,
            ),
            (
                "joint-clash",
                path(PathStop::DepthLimit, top()),
                vec![relation(x.clone(), z()), relation(x.clone(), s(y.clone()))],
                Unsat,
            ),
            (
                "no-real-prefix",
                path(PathStop::SolverUnknown, top()),
                vec![relation(x.clone(), y.clone())],
                Unknown,
            ),
            (
                "path-condition-needs-a-solver",
                path(PathStop::DepthLimit, constrained),
                vec![relation(x.clone(), y.clone())],
                Unknown,
            ),
            (
                "foreign-variable",
                path(PathStop::DepthLimit, top()),
                vec![relation(nat("Q"), y.clone())],
                Unknown,
            ),
        ];
        let state = symmem_state();
        let answers = symmem
            .with_solver(None, |definition, solver| {
                let relations =
                    BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
                Ok::<_, BackendError>(
                    rows.iter()
                        .map(|(id, path, assumptions, _)| {
                            (*id, relations.feasible(path, assumptions))
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .expect("relations");
        for ((id, answer), (.., expected)) in answers.into_iter().zip(&rows) {
            assert_eq!(answer, *expected, "{id}");
        }
    }

    #[test]
    fn ground_function_pairs_are_indeterminate() {
        let mut guarded = backend("guardedmem.k", "GUARDEDMEM");
        let state = support::initial_state(support::app("Lblhalt", vec![]), "SortProg");
        let answers = guarded
            .with_solver(None, |definition, solver| {
                let plus = definition
                    .symbols()
                    .values()
                    .find(|symbol| symbol.attributes.hook.as_deref() == Some("INT.add"))
                    .expect("+Int")
                    .name
                    .to_string();
                let one_plus_one = support::app(&plus, vec![support::int(1), support::int(1)]);
                let relations =
                    BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
                let real = path(PathStop::Terminal, top());
                Ok::<_, BackendError>([
                    relations.relate(&real, &[], &one_plus_one, &support::int(2)),
                    relations.relate(&real, &[], &one_plus_one, &support::int(3)),
                    relations.relate(&real, &[], &support::int(1), &support::int(2)),
                    relations.relate(&real, &[], &support::int(2), &support::int(2)),
                ])
            })
            .expect("relations");
        assert_eq!(answers, [Indeterminate, Indeterminate, Unequal, Equal]);
    }

    /// A solver that answers every satisfiability query with one scripted result.
    struct Scripted(Result<Satisfiability, SmtError>);

    impl SmtSolver for Scripted {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            Ok(self.0.clone())
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(Err(SmtError::Unavailable))
        }
    }

    /// A solver that answers every satisfiability query with one scripted result and records
    /// each query it is asked.
    struct Recording {
        answer: Result<Satisfiability, SmtError>,
        queries: std::cell::RefCell<Vec<Vec<Predicate>>>,
    }

    impl SmtSolver for Recording {
        fn is_sat(
            &self,
            predicates: &[Predicate],
            substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            assert!(substitution.is_empty(), "bindings are sent as predicates");
            self.queries.borrow_mut().push(predicates.to_vec());
            Ok(self.answer.clone())
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(Err(SmtError::Unavailable))
        }
    }

    /// The scripted solver answers of [`solver_sat_counts_only_for_the_exact_relation_query`].
    const ANSWERS: usize = 4;

    fn scripted_answers() -> [Result<Satisfiability, SmtError>; ANSWERS] {
        [
            Ok(Satisfiability::Sat),
            Ok(Satisfiability::Unsat),
            Ok(Satisfiability::Unknown("scripted".into())),
            Err(SmtError::Unavailable),
        ]
    }

    /// One row: id, path, assumptions, the `feasible` answer under each scripted solver answer
    /// (`Sat`, `Unsat`, `Unknown`, `Unavailable`), and the query the solver must be asked
    /// (`None`: no solver call).
    type QueryRow = (
        &'static str,
        PathInput,
        Vec<TermRelation>,
        [Feasibility; ANSWERS],
        Option<Vec<Predicate>>,
    );

    fn check_query_rows(
        definition: &BackendDefinition,
        state: &Pattern,
        rows: &[QueryRow],
    ) -> Vec<String> {
        let mut failures = Vec::new();
        for (id, path, assumptions, expected, query) in rows {
            for (answer, expected) in scripted_answers().into_iter().zip(expected) {
                let solver = Recording {
                    answer: answer.clone(),
                    queries: std::cell::RefCell::default(),
                };
                let feasible =
                    BackendRelations::shared(definition, &solver, TestInitialState::of_test(state))
                        .feasible(path, assumptions);
                let asked = solver.queries.into_inner();
                let expected_queries = query.iter().cloned().collect::<Vec<_>>();
                if feasible != *expected || asked != expected_queries {
                    failures.push(format!(
                        "{id} under {answer:?}: expected {expected:?} asking {expected_queries:?}, \
                         got {feasible:?} asking {asked:?}"
                    ));
                }
            }
        }
        failures
    }

    /// SYM-3B-03: `feasible` sends exactly the relation query (path predicate, residual
    /// constraints, bindings that are not eliminated) as predicates, counts a solver `Sat` only
    /// when that whole query translates exactly and mentions initial-state variables only, and
    /// counts every `Unsat`. Attacks: user-sort terms Z3 abstracts, `Int` payloads under
    /// constructors and injections, assumptions whose variables do not occur in the predicate,
    /// partial functions, foreign variables. Relations never depend on the solver.
    #[test]
    fn solver_sat_counts_only_for_the_exact_relation_query() {
        use Feasibility::{Sat as S, Unknown as U, Unsat as N};
        let exact = [S, N, U, U];
        let inexact = [U, N, U, U];
        let mut guarded = backend("guardedmem.k", "GUARDEDMEM");
        let int = |name: &str| support::var(name, "SortInt");
        let (x, y, v, w) = (int("X"), int("Y"), int("V"), int("W"));
        let state = support::initial_state(
            support::app(
                "Lblseq",
                vec![
                    support::app("Lblwrite", vec![addr(x.clone()), v.clone()]),
                    support::app(
                        "Lblseq",
                        vec![
                            support::app("Lblload", vec![addr(y.clone()), w.clone()]),
                            support::app("Lblhalt", vec![]),
                        ],
                    ),
                ],
            ),
            "SortProg",
        );
        let failures = guarded
            .with_solver(None, |definition, _| {
                let term = |pattern: &Pattern| {
                    definition
                        .admit_unverified(pattern, &[])
                        .internalize_term()
                        .expect("term internalizes")
                };
                let predicate = |pattern: &Pattern| {
                    definition
                        .admit_unverified(pattern, &[])
                        .internalize_predicate()
                        .expect("predicate internalizes")
                        .0
                };
                let binds =
                    |left: &Pattern, right: &Pattern| Predicate::Equals(term(left), term(right));
                let at_least_zero = |value: &Pattern| {
                    equals(
                        "SortBool",
                        Pattern::DomainValue {
                            sort: k_rust::kompile::initial_configuration::kore_sort("SortBool"),
                            value: "true".into(),
                        },
                        support::app(
                            &hooked(definition, "INT.ge"),
                            vec![value.clone(), support::int(0)],
                        ),
                    )
                };
                let plus_one = |value: &Pattern| {
                    support::app(
                        &hooked(definition, "INT.add"),
                        vec![value.clone(), support::int(1)],
                    )
                };
                let divided =
                    support::app(&hooked(definition, "INT.tdiv"), vec![y.clone(), v.clone()]);
                let inj = |value: &Pattern| {
                    k_rust::kompile::initial_configuration::kore_application(
                        "inj",
                        vec![
                            k_rust::kompile::initial_configuration::kore_sort("SortInt"),
                            k_rust::kompile::initial_configuration::kore_sort("SortKItem"),
                        ],
                        vec![value.clone()],
                    )
                };
                let x_ge = at_least_zero(&x);
                let y_ge = at_least_zero(&y);
                // `X &Int 1 ==Int 2`: no instance, but `&Int` is uninterpreted in SMT (R19).
                let uninterpreted = equals(
                    "SortInt",
                    support::app(
                        &hooked(definition, "INT.and"),
                        vec![x.clone(), support::int(1)],
                    ),
                    support::int(2),
                );
                let foreign_ge = at_least_zero(&int("Q"));
                // A predicate over `Address`, which Z3 abstracts.
                let abstracted = equals("SortAddress", addr(x.clone()), addr(v.clone()));
                let x_is_y = relation(x.clone(), y.clone());
                let rows: Vec<QueryRow> = vec![
                    (
                        "int-identification-under-a-guard",
                        path(PathStop::Terminal, x_ge.clone()),
                        vec![x_is_y.clone()],
                        exact,
                        Some(vec![predicate(&x_ge), binds(&x, &y)]),
                    ),
                    (
                        // `X` occurs only in the binding `X = Y`: eliminated.
                        "binding-outside-the-predicate",
                        path(PathStop::Terminal, y_ge.clone()),
                        vec![x_is_y.clone()],
                        exact,
                        Some(vec![predicate(&y_ge)]),
                    ),
                    (
                        "int-payload-under-a-constructor",
                        path(PathStop::DepthLimit, x_ge.clone()),
                        vec![relation(addr(x.clone()), addr(y.clone()))],
                        exact,
                        Some(vec![predicate(&x_ge), binds(&x, &y)]),
                    ),
                    (
                        "int-payload-under-an-injection",
                        path(PathStop::Terminal, x_ge.clone()),
                        vec![relation(inj(&x), inj(&y))],
                        exact,
                        Some(vec![predicate(&x_ge), binds(&x, &y)]),
                    ),
                    (
                        // Every binding eliminated, no predicate: no solver is asked.
                        "empty-query",
                        path(PathStop::Terminal, top()),
                        vec![x_is_y.clone()],
                        [S, S, S, S],
                        None,
                    ),
                    (
                        "total-function-value",
                        path(PathStop::Terminal, top()),
                        vec![relation(x.clone(), plus_one(&y))],
                        exact,
                        Some(vec![binds(&x, &plus_one(&y))]),
                    ),
                    (
                        "residual-function-equation",
                        path(PathStop::Terminal, top()),
                        vec![relation(plus_one(&x), plus_one(&y))],
                        exact,
                        Some(vec![binds(&plus_one(&x), &plus_one(&y))]),
                    ),
                    (
                        "partial-function-value",
                        path(PathStop::Terminal, top()),
                        vec![relation(x.clone(), divided.clone())],
                        inexact,
                        Some(vec![binds(&x, &divided)]),
                    ),
                    (
                        "abstracted-user-sort-predicate",
                        path(PathStop::Terminal, abstracted.clone()),
                        vec![x_is_y.clone()],
                        inexact,
                        Some(vec![predicate(&abstracted), binds(&x, &y)]),
                    ),
                    (
                        "uninterpreted-smtlib-function",
                        path(PathStop::Terminal, uninterpreted.clone()),
                        vec![x_is_y.clone()],
                        inexact,
                        Some(vec![predicate(&uninterpreted), binds(&x, &y)]),
                    ),
                    (
                        "foreign-predicate-variable",
                        path(PathStop::Terminal, foreign_ge.clone()),
                        vec![x_is_y.clone()],
                        inexact,
                        Some(vec![predicate(&foreign_ge)]),
                    ),
                    (
                        "no-real-prefix",
                        path(PathStop::SolverUnknown, x_ge.clone()),
                        vec![x_is_y.clone()],
                        [U, U, U, U],
                        None,
                    ),
                    (
                        "proved-clash",
                        path(PathStop::Terminal, x_ge),
                        vec![
                            relation(x.clone(), support::int(1)),
                            relation(x, support::int(2)),
                        ],
                        [N, N, N, N],
                        None,
                    ),
                ];
                Ok::<_, BackendError>(check_query_rows(definition, &state, &rows))
            })
            .expect("definition");
        assert!(failures.is_empty(), "{failures:#?}");

        // `Nat` variables: the eliminated `X = Y` leaves no query on `\top`; a `Nat` predicate
        // or a `Nat` binding the predicate constrains is abstracted by Z3.
        let mut symmem = backend("symmem.k", "SYMMEM");
        let (x, y) = (nat("X"), nat("Y"));
        let failures = symmem
            .with_solver(None, |definition, _| {
                let term = |pattern: &Pattern| {
                    definition
                        .admit_unverified(pattern, &[])
                        .internalize_term()
                        .expect("term internalizes")
                };
                let predicate = |pattern: &Pattern| {
                    definition
                        .admit_unverified(pattern, &[])
                        .internalize_predicate()
                        .expect("predicate internalizes")
                        .0
                };
                let y_is_z = equals("SortNat", y.clone(), z());
                let x_is_z = equals("SortNat", x.clone(), z());
                let rows: Vec<QueryRow> = vec![
                    (
                        "nat-identification",
                        path(PathStop::Terminal, top()),
                        vec![relation(addr(x.clone()), addr(y.clone()))],
                        [S, S, S, S],
                        None,
                    ),
                    (
                        "nat-predicate",
                        path(PathStop::Terminal, y_is_z.clone()),
                        vec![relation(x.clone(), y.clone())],
                        inexact,
                        Some(vec![predicate(&y_is_z)]),
                    ),
                    (
                        "constrained-nat-binding",
                        path(PathStop::Terminal, x_is_z.clone()),
                        vec![relation(x.clone(), s(y.clone()))],
                        inexact,
                        Some(vec![
                            predicate(&x_is_z),
                            Predicate::Equals(term(&x), term(&s(y.clone()))),
                        ]),
                    ),
                ];
                Ok::<_, BackendError>(check_query_rows(definition, &symmem_state(), &rows))
            })
            .expect("definition");
        assert!(failures.is_empty(), "{failures:#?}");

        // `relate` never asks the solver.
        let relate = symmem
            .with_solver(None, |definition, _| {
                let solver = Recording {
                    answer: Ok(Satisfiability::Unsat),
                    queries: std::cell::RefCell::default(),
                };
                let answer = BackendRelations::shared(
                    definition,
                    &solver,
                    TestInitialState::of_test(&symmem_state()),
                )
                .relate(
                    &path(PathStop::Terminal, top()),
                    &[],
                    &addr(x.clone()),
                    &addr(y.clone()),
                );
                Ok::<_, BackendError>((answer, solver.queries.into_inner().len()))
            })
            .expect("definition");
        assert_eq!(relate, (EqualIf(vec![relation(x, y)]), 0));
    }

    fn top_sort() -> k_rust::kore::ast::Sort {
        k_rust::kompile::initial_configuration::kore_sort("SortGeneratedTopCell")
    }

    /// `state` under the predicate conjunct `predicate`.
    fn constrained(state: Pattern, predicate: Pattern) -> Pattern {
        Pattern::And {
            sort: top_sort(),
            arguments: vec![state, predicate],
        }
    }

    /// `\equals{Sort, Top}(left, right)`.
    fn equals(sort: &str, left: Pattern, right: Pattern) -> Pattern {
        Pattern::Equals {
            operand_sort: Box::new(k_rust::kompile::initial_configuration::kore_sort(sort)),
            result_sort: top_sort(),
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// The guardedmem symbol named by `hook`.
    fn hooked(definition: &BackendDefinition, hook: &str) -> String {
        definition
            .symbols()
            .values()
            .find(|symbol| symbol.attributes.hook.as_deref() == Some(hook))
            .unwrap_or_else(|| panic!("{hook}"))
            .name
            .to_string()
    }

    /// `seq(write(addr(address), V), halt)` of guardedmem.
    fn guarded_state(address: Pattern) -> Pattern {
        guarded_write(address, support::var("V", "SortInt"))
    }

    /// `seq(write(addr(address), value), halt)` of guardedmem.
    fn guarded_write(address: Pattern, value: Pattern) -> Pattern {
        support::initial_state(
            support::app(
                "Lblseq",
                vec![
                    support::app("Lblwrite", vec![addr(address), value]),
                    support::app("Lblhalt", vec![]),
                ],
            ),
            "SortProg",
        )
    }

    /// VI preserves the free ExW0 in W = 1 and exists Ex#W!0. W = 2 (Unsat).
    /// The pre-VI binder spelling ExW0 captures W in the second equality (Solver).
    /// Without Z3 both constrained states have Unknown feasibility.
    #[test]
    fn decoded_binders_do_not_capture() {
        let mut guarded = backend("guardedmem.k", "GUARDEDMEM");
        let rows = guarded
            .with_solver(None, |definition, solver| {
                let inhabitation = Inhabitation::of(definition);
                let w = support::var("ExW0", "SortInt");
                let binder = externalize::external_variable_name("Ex#W!0");
                let mut rows = Vec::new();
                for name in [&binder, "ExW0"] {
                    let Pattern::Variable(variable) = &support::var(name, "SortInt") else {
                        unreachable!()
                    };
                    let state = constrained(
                        constrained(
                            guarded_state(w.clone()),
                            equals("SortInt", w.clone(), support::int(1)),
                        ),
                        Pattern::Exists {
                            sort: top_sort(),
                            variable: Box::new(variable.clone()),
                            body: Box::new(equals("SortInt", w.clone(), support::int(2))),
                        },
                    );
                    rows.push(leaf_feasibility(
                        definition,
                        solver,
                        &inhabitation,
                        &codec::to_value(&state).expect("decoded state encodes"),
                    ));
                }
                Ok::<_, BackendError>(rows)
            })
            .expect("binder rows");
        let expected = if cfg!(feature = "z3") {
            vec![LeafFeasibility::Unsat, LeafFeasibility::Solver]
        } else {
            vec![LeafFeasibility::Unknown; 2]
        };
        assert_eq!(rows, expected);
    }

    /// VI-06 attack VI-AT7, the row `decoded_binders_do_not_capture` cannot build from KORE:
    /// an internal binder `Ex#W!0` (a mint, never a read name) printed next to a free
    /// variable that a test spelled `Ex-hW-b0`, the binder's own printed spelling. k-rust's
    /// printer renames the binder apart (`apart_binders`: `Ex#W!0!binder0`, printed
    /// `Ex-hW-b0-bbinder0`), so the read-back state keeps the real `w = 1 and exists v. w = 2`:
    /// Unsat under Z3, not the captured, satisfiable `w = 1 and exists w. w = 2`. Without Z3
    /// the state is Unknown.
    #[test]
    fn audit_vi_at7_initial_name_spelled_like_a_printed_binder_is_not_captured() {
        let mut guarded = backend("guardedmem.k", "GUARDEDMEM");
        let (binder, row) = guarded
            .with_solver(None, |definition, solver| {
                let inhabitation = Inhabitation::of(definition);
                let w = support::var("Ex-hW-b0", "SortInt");
                let Pattern::Variable(read_binder) = &support::var("B", "SortInt") else {
                    unreachable!()
                };
                let read = constrained(
                    constrained(
                        guarded_state(w.clone()),
                        equals("SortInt", w.clone(), support::int(1)),
                    ),
                    Pattern::Exists {
                        sort: top_sort(),
                        variable: Box::new(read_binder.clone()),
                        body: Box::new(equals("SortInt", w.clone(), support::int(2))),
                    },
                );
                let mut internal = definition
                    .admit_unverified(&read, &[])
                    .internalize_pattern()
                    .expect("state internalizes");
                let mut minted = 0;
                for predicate in &mut internal.constraints {
                    if let k_rust_backend::rule::Predicate::Exists(variable, _) = predicate {
                        *variable = variable.with_name("Ex#W!0");
                        minted += 1;
                    }
                }
                assert_eq!(minted, 1, "one binder: {:?}", internal.constraints);
                let printed = externalize::constrained_pattern(&internal);
                let mut binders = Vec::new();
                k_rust::kore::walk::for_each_post_order(&printed, |node| {
                    if let Pattern::Exists { variable, .. } = node {
                        binders.push(variable.name.clone());
                    }
                });
                assert_eq!(
                    printed
                        .free_variables()
                        .into_iter()
                        .map(|variable| variable.name)
                        .collect::<Vec<_>>(),
                    ["Ex-hW-b0", "V"]
                );
                let row = leaf_feasibility(
                    definition,
                    solver,
                    &inhabitation,
                    &codec::to_value(&printed).expect("printed state encodes"),
                );
                Ok::<_, BackendError>((binders, row))
            })
            .expect("binder row");
        assert_eq!(binder, ["Ex-hW-b0-bbinder0"]);
        let expected = if cfg!(feature = "z3") {
            LeafFeasibility::Unsat
        } else {
            LeafFeasibility::Unknown
        };
        assert_eq!(row, expected);
    }

    /// Under the documented explicit-definedness premise, leaf feasibility uses the solver's
    /// `Unsat`, and uses its `Sat` only for an exactly
    /// translated predicate over a constructor term; `NoSolver` adds nothing.
    #[test]
    fn solver_feasibility_needs_exact_sat_and_counts_every_unsat() {
        let mut guarded = backend("guardedmem.k", "GUARDEDMEM");
        let answers = guarded
            .with_solver(None, |definition, _| {
                let inhabitation = Inhabitation::of(definition);
                let x = support::var("X", "SortInt");
                let guard = equals(
                    "SortBool",
                    Pattern::DomainValue {
                        sort: k_rust::kompile::initial_configuration::kore_sort("SortBool"),
                        value: "true".into(),
                    },
                    support::app(
                        &hooked(definition, "INT.ge"),
                        vec![x.clone(), support::int(0)],
                    ),
                );
                let plus = support::app(
                    &hooked(definition, "INT.add"),
                    vec![x.clone(), support::int(1)],
                );
                // A predicate over the `Address` sort, which Z3 abstracts.
                let abstracted = equals(
                    "SortAddress",
                    addr(x.clone()),
                    addr(support::var("Y", "SortInt")),
                );
                // `X &Int 1 ==Int 2`: `&Int` is `smtlib(andInt)`, an uninterpreted SMT function
                // (SYM-3B-05, README R19).
                let uninterpreted = equals(
                    "SortInt",
                    support::app(
                        &hooked(definition, "INT.and"),
                        vec![x.clone(), support::int(1)],
                    ),
                    support::int(2),
                );
                let states = [
                    (
                        "exact",
                        constrained(guarded_state(x.clone()), guard.clone()),
                    ),
                    (
                        "uninterpreted",
                        constrained(guarded_state(x.clone()), uninterpreted),
                    ),
                    (
                        "abstracted",
                        constrained(guarded_state(x.clone()), abstracted),
                    ),
                    ("function-term", constrained(guarded_state(plus), guard)),
                    ("predicate-free", guarded_state(x)),
                ];
                let rows = [
                    Ok(Satisfiability::Sat),
                    Ok(Satisfiability::Unsat),
                    Ok(Satisfiability::Unknown("scripted".into())),
                    Err(SmtError::Unavailable),
                ]
                .into_iter()
                .flat_map(|answer| {
                    let solver = Scripted(answer.clone());
                    states
                        .iter()
                        .map(|(id, state)| {
                            (
                                format!("{answer:?} {id}"),
                                leaf_feasibility(
                                    definition,
                                    &solver,
                                    &inhabitation,
                                    &codec::to_value(state).expect("state JSON"),
                                ),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
                Ok::<_, BackendError>(rows)
            })
            .expect("definition");
        use LeafFeasibility::{Solver, Syntactic, Unknown as U, Unsat as N};
        let expected = [
            // Sat
            Solver, U, U, U, Syntactic, //
            // Unsat
            N, N, N, N, Syntactic, //
            // Unknown
            U, U, U, U, Syntactic, //
            // NoSolver
            U, U, U, U, Syntactic,
        ];
        assert_eq!(answers.len(), expected.len());
        for ((id, answer), expected) in answers.into_iter().zip(expected) {
            assert_eq!(answer, expected, "{id}");
        }
    }

    const WRAP: &str = r#"[]
        module MAIN
            sort SortNat{} []
            symbol Lblz{}() : SortNat{} [constructor{}(), functional{}()]
            symbol Lbls{}(SortNat{}) : SortNat{} [constructor{}(), functional{}()]
            symbol Lblpair{}(SortNat{}, SortNat{}) : SortNat{} [constructor{}(), functional{}()]
            symbol Lblwrap{}(SortNat{}) : SortNat{} [functional{}(), injective{}(), anywhere{}()]
            symbol Lbltag{}(SortNat{}) : SortNat{} [functional{}(), injective{}(), anywhere{}()]
            symbol Lblperm{}(SortNat{}) : SortNat{} [function{}(), injective{}()]
            symbol Lblboth{}(SortNat{}) : SortNat{} [constructor{}(), function{}()]
            axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(\in{SortNat{}, R}(X0:SortNat{}, Lbls{}(Lblz{}())), \top{R}())
                ),
                \equals{SortNat{}, R}(
                    Lblwrap{}(X0:SortNat{}),
                    \and{SortNat{}}(Lblwrap{}(Lblz{}()), \top{SortNat{}}())
                )
            ) [label{}("collapse-wrap"), anywhere{}()]
            axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(\in{SortNat{}, R}(X0:SortNat{}, Lbls{}(Lblz{}())), \top{R}())
                ),
                \equals{SortNat{}, R}(
                    Lbltag{}(X0:SortNat{}),
                    \and{SortNat{}}(Lbltag{}(Lblz{}()), \top{SortNat{}}())
                )
            ) [label{}("collapse-tag"), anywhere{}()]
        endmodule []"#;

    /// The wrap equation can identify distinct arguments, while the tag equation cannot reach
    /// `tag(s(s(X)))`. A non-anywhere injective function remains untrusted.
    /// Trust-base change (VI-03F, D-A): row 6 is Unequal in both profiles because
    /// constructor+function is HeadRole::FreeConstructor under k-rust's freeness contract.
    #[test]
    fn non_free_injective_symbols_leave_relations_undecided() {
        let definition =
            BackendDefinition::internalize(&parse_definition(WRAP).expect("KORE"), "MAIN")
                .expect("definition");
        let (x, y) = (nat("X"), nat("Y"));
        let wrap = |value: Pattern| support::app("Lblwrap", vec![value]);
        let tag = |value: Pattern| support::app("Lbltag", vec![value]);
        let perm = |value: Pattern| support::app("Lblperm", vec![value]);
        let both = |value: Pattern| support::app("Lblboth", vec![value]);
        let state = support::app("Lblpair", vec![x.clone(), y.clone()]);
        let solver = Scripted(Err(SmtError::Unavailable));
        let relations =
            BackendRelations::shared(&definition, &solver, TestInitialState::of_test(&state));
        let real = path(PathStop::Terminal, top_of("SortNat"));
        assert_eq!(
            [
                relations.relate(&real, &[], &wrap(s(x.clone())), &wrap(z())),
                relations.relate(&real, &[], &wrap(x.clone()), &wrap(y.clone())),
                relations.relate(&real, &[], &wrap(x.clone()), &wrap(x.clone())),
                relations.relate(&real, &[], &s(x.clone()), &z()),
                relations.relate(&real, &[], &x, &y),
                relations.relate(&real, &[], &both(z()), &both(s(z()))),
                relations.relate(&real, &[], &tag(s(s(x.clone()))), &tag(z())),
                relations.relate(&real, &[], &tag(s(s(x.clone()))), &tag(s(s(y.clone())))),
                relations.relate(&real, &[], &perm(x.clone()), &perm(y.clone())),
            ],
            [
                Indeterminate,
                Indeterminate,
                Equal,
                Unequal,
                EqualIf(vec![relation(x.clone(), y.clone())]),
                Unequal,
                Unequal,
                EqualIf(vec![relation(x.clone(), y.clone())]),
                Indeterminate,
            ]
        );
        assert_eq!(
            [
                relations.feasible(&real, &[relation(wrap(x.clone()), wrap(s(y.clone())))]),
                relations.feasible(&real, &[relation(x.clone(), z()), relation(x, s(y))]),
            ],
            [Unknown, Unsat]
        );
    }

    /// VI-03F review attack AT13 over a non-confluent `anywhere` head: `tag(s(z))` rewrites to
    /// `tag(z)` and to `tag(s(s(z)))`; `f` is a partial function without equations and `g` a
    /// total function with one.
    const TAG: &str = r#"[]
        module MAIN
            sort SortNat{} []
            symbol Lblz{}() : SortNat{} [constructor{}(), functional{}()]
            symbol Lbls{}(SortNat{}) : SortNat{} [constructor{}(), functional{}()]
            symbol Lblpair{}(SortNat{}, SortNat{}) : SortNat{} [constructor{}(), functional{}()]
            symbol Lbltag{}(SortNat{}) : SortNat{} [functional{}(), injective{}(), anywhere{}()]
            symbol Lblf{}(SortNat{}) : SortNat{} [function{}()]
            symbol Lblg{}(SortNat{}) : SortNat{} [function{}(), functional{}()]
            axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(\in{SortNat{}, R}(X0:SortNat{}, Lbls{}(Lblz{}())), \top{R}())
                ),
                \equals{SortNat{}, R}(
                    Lbltag{}(X0:SortNat{}),
                    \and{SortNat{}}(Lbltag{}(Lblz{}()), \top{SortNat{}}())
                )
            ) [label{}("t1"), anywhere{}()]
            axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(\in{SortNat{}, R}(X0:SortNat{}, Lbls{}(Lblz{}())), \top{R}())
                ),
                \equals{SortNat{}, R}(
                    Lbltag{}(X0:SortNat{}),
                    \and{SortNat{}}(Lbltag{}(Lbls{}(Lbls{}(Lblz{}()))), \top{SortNat{}}())
                )
            ) [label{}("t2"), anywhere{}()]
            axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(\in{SortNat{}, R}(X0:SortNat{}, Lblz{}()), \top{R}())
                ),
                \equals{SortNat{}, R}(
                    Lblg{}(X0:SortNat{}),
                    \and{SortNat{}}(Lblz{}(), \top{SortNat{}}())
                )
            ) [label{}("g-z")]
        endmodule []"#;

    /// VI-06 re-run of VI-03F review attack AT13 (T-FREE, README 16.4): an `anywhere` head
    /// (`HeadRole::EquationHead`) is decomposed only by k-rust, and only where both
    /// applications are normal on every instance. Every relation that an equation could
    /// decide another way is Indeterminate and every such query Unknown; only `tag(z)` against
    /// `tag(s(s(z)))`, both normal on every instance, is Unequal. Same values in both profiles,
    /// with the build's solver. No unjustified Equal, Unequal or Clash.
    #[test]
    fn audit_vi_at13_anywhere_heads_are_decomposed_only_where_normal() {
        let mut backend = Backend::new(TAG, "MAIN", BackendOptions::default()).expect("backend");
        let (x, y) = (nat("X"), nat("Y"));
        let tag = |value: Pattern| support::app("Lbltag", vec![value]);
        let f = |value: Pattern| support::app("Lblf", vec![value]);
        let g = |value: Pattern| support::app("Lblg", vec![value]);
        let state = support::app("Lblpair", vec![x.clone(), y.clone()]);
        let real = path(PathStop::Terminal, top_of("SortNat"));
        let (answers, queries) = backend
            .with_solver(None, |definition, solver| {
                let relations =
                    BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
                let answers = [
                    (tag(s(z())), tag(z())),
                    (tag(f(x.clone())), tag(z())),
                    (tag(g(x.clone())), tag(z())),
                    (tag(g(x.clone())), tag(s(s(z())))),
                    (tag(x.clone()), tag(z())),
                    (tag(x.clone()), tag(s(s(y.clone())))),
                    (tag(s(x.clone())), tag(s(s(z())))),
                    (f(x.clone()), f(y.clone())),
                    (g(x.clone()), g(y.clone())),
                    (s(tag(s(x.clone()))), s(tag(z()))),
                    (tag(z()), tag(s(s(z())))),
                ]
                .map(|(left, right)| relations.relate(&real, &[], &left, &right));
                let queries = [
                    relations.feasible(&real, &[relation(tag(x.clone()), tag(z()))]),
                    relations.feasible(&real, &[relation(tag(s(x.clone())), tag(s(s(z()))))]),
                ];
                Ok::<_, BackendError>((answers, queries))
            })
            .expect("relations");
        let mut expected = [const { Indeterminate }; 11];
        expected[10] = Unequal;
        assert_eq!(answers, expected);
        assert_eq!(queries, [Unknown, Unknown]);
    }

    /// Before variable identity, a definition whose rewrite rules introduce existential
    /// variables could reuse a variable name for two values on one path, so every comparison
    /// involving a variable was undecided (`[Indeterminate, Indeterminate, Unequal]`). Under the
    /// contract no mint re-binds an initial name, so the initial variables stay comparable.
    #[test]
    fn existential_rules_keep_initial_variable_comparisons() {
        let mut symmem = backend(
            "symmem_existential.k",
            &k_rust::kast::identifier::encode("SYMMEM_EXISTENTIAL"),
        );
        let state = symmem_state();
        let (x, y) = (nat("X"), nat("Y"));
        let real = path(PathStop::DepthLimit, top());
        let answers = symmem
            .with_solver(None, |definition, solver| {
                // Construction change (VI-03F): immutable BackendDefinition is supplied
                // by a fixture with an existential rewrite rule instead of an in-memory edit.
                assert!(
                    definition
                        .rewrite_theory()
                        .values()
                        .flat_map(|priorities| priorities.values())
                        .flatten()
                        .any(|rule| !rule.rule.existentials.is_empty()),
                    "fixture must introduce an existential"
                );
                let relations =
                    BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
                Ok::<_, BackendError>([
                    relations.relate(&real, &[], &addr(x.clone()), &addr(x.clone())),
                    relations.relate(&real, &[], &addr(x.clone()), &addr(y.clone())),
                    relations.relate(&real, &[], &z(), &s(z())),
                ])
            })
            .expect("relations");
        assert_eq!(
            answers,
            [Equal, EqualIf(vec![relation(nat("X"), nat("Y"))]), Unequal]
        );
    }

    /// The test's initial variables are linked whatever their spelling: a digit suffix, an old
    /// mint spelling (`ExVarI0`, `RuleX`) and a printed mint spelling (`Ex-hX-b0`) all
    /// name request variables. Rename-only change (VI-03F): v3 reads Ex-hX-b0 verbatim. All or nothing: one variable
    /// of an uninhabited sort leaves no initial variable.
    #[test]
    fn initial_variables_are_every_inhabited_initial_variable() {
        let mut symmem = backend("symmem.k", "SYMMEM");
        let (a, b, c, d) = (nat("X1"), nat("ExVarI0"), nat("RuleX"), nat("Ex-hX-b0"));
        let state = support::initial_state(
            support::app(
                "Lblseq",
                vec![
                    support::app("Lblwrite", vec![addr(a.clone()), b.clone()]),
                    support::app(
                        "Lblseq",
                        vec![
                            support::app("Lblload", vec![addr(c.clone()), d.clone()]),
                            support::app("Lblhalt", vec![]),
                        ],
                    ),
                ],
            ),
            "SortProg",
        );
        let real = path(PathStop::DepthLimit, top());
        let (variables, answers) = symmem
            .with_solver(None, |definition, solver| {
                let relations =
                    BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
                Ok::<_, BackendError>((
                    relations.variables.clone(),
                    [
                        relations.relate(&real, &[], &addr(a.clone()), &addr(a.clone())),
                        relations.relate(&real, &[], &addr(a.clone()), &addr(c.clone())),
                        relations.relate(&real, &[], &b, &d),
                    ],
                ))
            })
            .expect("relations");
        assert_eq!(
            variables,
            Some(
                ["X1", "ExVarI0", "RuleX", "Ex-hX-b0"]
                    .into_iter()
                    .map(|name| Variable::new(name, Sort::simple("SortNat")))
                    .collect()
            )
        );
        assert_eq!(
            answers,
            [
                Equal,
                EqualIf(vec![relation(c.clone(), a.clone())]),
                EqualIf(vec![relation(d.clone(), b.clone())]),
            ]
        );
        let definition =
            BackendDefinition::internalize(&parse_definition(EMPTY).expect("KORE"), "MAIN")
                .expect("definition");
        let solver = k_rust_backend::smt::NoSolver;
        let inhabited = support::var("VarS", "SortS");
        let empty = support::var("VarE", "SortEmpty");
        assert_eq!(
            BackendRelations::shared(&definition, &solver, TestInitialState::of_test(&inhabited))
                .variables,
            Some(BTreeSet::from([Variable::new(
                "VarS",
                Sort::simple("SortS")
            )]))
        );
        let pair = support::app(
            "Lblpair",
            vec![inhabited, support::app("Lblwrap", vec![empty])],
        );
        assert_eq!(
            BackendRelations::shared(&definition, &solver, TestInitialState::of_test(&pair))
                .variables,
            None
        );
    }

    #[test]
    fn shared_relations_refuse_identity_injections() {
        let mut backend = backend("subsort_steps.k", "SUBSORT'Unds'STEPS");
        let y = support::var("Y", "SortLarge");
        let state = support::initial_state(support::app("Lblstep", vec![y.clone()]), "SortProg");
        let identity = k_rust::kompile::initial_configuration::kore_application(
            "inj",
            vec![
                k_rust::kompile::initial_configuration::kore_sort("SortLarge"),
                k_rust::kompile::initial_configuration::kore_sort("SortLarge"),
            ],
            vec![y.clone()],
        );
        let real = path(PathStop::DepthLimit, top());
        backend
            .with_solver(None, |definition, solver| {
                let shared =
                    BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
                assert_eq!(
                    shared.relate(&real, &[], &identity, &y),
                    RelationDecision::Indeterminate
                );
                assert_eq!(
                    shared.feasible(&real, &[relation(identity.clone(), y.clone())]),
                    Feasibility::Unknown
                );
                assert_eq!(
                    shared.relate(&real, &[relation(identity.clone(), y.clone())], &y, &y),
                    RelationDecision::Indeterminate
                );
                let invalid_state = support::initial_state(
                    support::app("Lblstep", vec![identity.clone()]),
                    "SortProg",
                );
                assert_eq!(
                    shared_leaf_feasibility(
                        definition,
                        solver,
                        &Inhabitation::of(definition),
                        &codec::to_value(&invalid_state).expect("state JSON"),
                    ),
                    LeafFeasibility::Unknown
                );
                Ok::<_, BackendError>(())
            })
            .expect("relations");
    }

    /// state-observations SO-03 review R1-D3/R2-D2 (probe `r6`), the printed-name exposure the
    /// EI certificate backstopped: `go(B)` narrows `B:Box` to `c(I)` with a fresh `I`, and the
    /// test's own variable is named `ExVarI0`, the spelling k-rust printed that mint in before
    /// the variable-identity contract. Then the decoded state 1 read
    /// `seq(check2(ExVarI0), seq(check2(ExVarI0), done))`, so the declaration
    /// `seq(check2(J), seq(check2(J), P))` was Certain at step 1 by name identity, and
    /// shared leaf feasibility proved the real `fail` leaf (mint `> 0`, user `<= 0`) Unsat over
    /// the merged names and discarded it. Under the contract the mint is its own variable: no
    /// Certain event and no Unsat leaf, in either profile.
    #[test]
    fn minted_and_initial_variables_are_never_identified() {
        use crate::bridge::{BridgeContext, paths_from_steps};
        use crate::execution::{ExecutionAdapter, ExecutionBudget, SolverProfile};
        use crate::step_events::{ObservationDecider, StepEventSpec, StepObservation};
        use kink_pattern::{EventPresence, ExecutionTerminalKind, SymbolSorts};

        const SOURCE: &str = "module CONFLATETERM-SYNTAX\n  imports INT-SYNTAX\n  syntax Box ::= c(Int) [symbol(c)]\n  syntax Op ::= check2(Int) [symbol(check2)] | go(Box) [symbol(go)]\n  syntax Prog ::= \"done\" [symbol(done)] | \"fail\" [symbol(fail)] | seq(Op, Prog) [symbol(seq)]\nendmodule\n\nmodule CONFLATETERM\n  imports CONFLATETERM-SYNTAX\n  imports BASIC-K\n  imports INT\n  configuration <k> .K </k>\n  rule [check2]:     seq(check2(J), P) => P requires J >Int 0\n  rule [check2Fail]: seq(check2(J), _) => fail requires J <=Int 0\n  rule [goPos]: seq(go(c(I)), P) => seq(check2(I), P) requires I >Int 0\n  rule [goNeg]: seq(go(c(I)), P) => P requires I <=Int 0\nendmodule\n";
        let directory = std::env::temp_dir().join(format!(
            "vi04-conflateterm-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock")
                .as_nanos()
        ));
        std::fs::create_dir(&directory).expect("temporary definition directory");
        let source = directory.join("conflateterm.k");
        std::fs::write(&source, SOURCE).expect("definition source");
        let side = NativeValidator::bind(
            support::load_path(&source, "CONFLATETERM"),
            CompileOptions::default(),
        )
        .compile_baseline()
        .expect("conflateterm compiles");
        std::fs::remove_dir_all(&directory).expect("remove temporary definition");
        let kore = &side.artifacts().definition_kore;
        let mut backend =
            Backend::new(kore, "CONFLATETERM", BackendOptions::default()).expect("backend");
        let seq = |head, tail| support::app("Lblseq", vec![head, tail]);
        let check2 = |value| support::app("Lblcheck2", vec![value]);
        let state = support::initial_state(
            seq(
                support::app("Lblgo", vec![support::var("B", "SortBox")]),
                seq(
                    check2(support::var("ExVarI0", "SortInt")),
                    support::app("Lbldone", vec![]),
                ),
            ),
            "SortProg",
        );
        let j = support::var("J", "SortInt");
        let spec = StepEventSpec {
            constructor: "same".into(),
            pre: support::k_config(
                seq(
                    check2(j.clone()),
                    seq(check2(j), support::var("P", "SortProg")),
                ),
                "SortProg",
                "R",
                "C",
            ),
            post: None,
            payload: vec!["J".into()],
        };
        let observation = StepObservation::new(&mut backend, vec![spec]).expect("declaration");
        let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
            .execute_steps(
                &mut backend,
                &state,
                ExecutionBudget {
                    time: std::time::Duration::from_secs(30),
                    max_simplification_iterations: 1000,
                    max_depth: None,
                    max_breadth: None,
                },
            )
            .expect("execution")
            .expect("stepped run");
        let sorts = SymbolSorts::from_definition(&parse_definition(kore).expect("KORE"));
        let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
        let (feasibility, events) = backend
            .with_solver(None, |definition, solver| {
                let decider =
                    ObservationDecider::new(definition, solver, TestInitialState::of_test(&state));
                let feasibility = execution
                    .adapted
                    .leaves()
                    .iter()
                    .map(|leaf| decider.shared_leaf_feasibility(&leaf.branch.state))
                    .collect::<Vec<_>>();
                let paths = paths_from_steps(
                    &BridgeContext {
                        test_id: "r6",
                        classify: &normal,
                        sorts: &sorts,
                    },
                    &execution,
                    &observation,
                    &decider,
                )
                .expect("bridge")
                .paths;
                let events = paths
                    .iter()
                    .map(|path| {
                        path.events
                            .iter()
                            .map(|event| (event.step, event.presence.clone()))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                Ok::<_, BackendError>((feasibility, events))
            })
            .expect("shared decider");
        assert!(
            !feasibility.contains(&LeafFeasibility::Unsat),
            "{feasibility:?}"
        );
        assert!(
            events
                .iter()
                .flatten()
                .all(|(_, presence)| *presence != EventPresence::Certain),
            "{events:?}"
        );
        // Z3: five leaves, none shared-Unsat, so every leaf is bridged; the two paths through
        // `seq(check2(mint), seq(check2(ExVarI0), done))` leave the step-1 event Undecided (the
        // mint is no initial variable, so `relate` does not compare it). No-Z3: the narrowing
        // step is Indeterminate at the initial state.
        if cfg!(feature = "z3") {
            assert_eq!(feasibility, vec![LeafFeasibility::Unknown; 5]);
            assert_eq!(
                events,
                vec![
                    vec![],
                    vec![],
                    vec![],
                    vec![(1, EventPresence::Undecided)],
                    vec![(1, EventPresence::Undecided)],
                ]
            );
        } else {
            assert_eq!(feasibility, vec![LeafFeasibility::Syntactic]);
            assert_eq!(events, vec![Vec::new()]);
        }
    }
}

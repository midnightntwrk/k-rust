//! Solver-free feasibility of execution leaves and backend-decided payload relations.
//!
//! Both are decided by k-rust's own definition and unifier, never by host term comparison.
//!
//! **Leaf feasibility.** A leaf state is [`LeafFeasibility::Syntactic`] when it internalizes to a
//! term with no predicate conjunct that contains only free constructors, sort injections, domain
//! values and element variables of inhabited sorts. Free constructors are total and injective,
//! so every valuation of the variables over their inhabited sorts gives a value: the state has
//! an instance. The bridge uses this only to keep a depth or breadth cut a real prefix; it never
//! makes a symbolic stuck leaf complete, because a symbolic `Stuck` is not a completeness claim.
//!
//! **Relations.** [`BackendRelations`] answers `relate` by jointly unifying the assumptions made
//! so far with the new pair through `unify_term_pairs`, and `feasible` by jointly unifying the
//! assumptions. Unification preserves the solutions of the equation set, so a proved clash means
//! no instance satisfies them, and a solved form without residual constraints is equivalent to
//! them. Only clashes that hold in K's constructor algebra count (distinct free constructors, a
//! free constructor against an injection, distinct canonical `Int`/`Bool`/`String` values, and a
//! variable occurring under free constructors); anything else, including a residual function
//! equation, is undecided. Two distinct ground terms are not assumed unequal. Terms that the
//! unifier would decompose through a symbol other than a free constructor (an `anywhere` or
//! overloaded production is `injective` without being free) are undecided unless identical.
//!
//! `feasible` answers `Sat` without a solver only for a real-prefix path whose predicate is
//! `\top` and whose solved form maps variables to constructor terms over inhabited sorts. That
//! argument needs every valuation of the initial-state variables to follow the path, which holds
//! without a solver: k-rust turns every binding of a subject variable into a match condition and
//! needs the solver to accept one (`rewrite/apply.rs`, phases P7 and P10), so a clean no-Z3 step
//! only instantiates rules. With a solver present that is no longer true, and `feasible` answers
//! only `Unsat` or `Unknown` until the Z3 profile establishes the stronger argument.

use std::collections::BTreeSet;

use k_rust::backend::{Backend, BackendError};
use k_rust::kore::ast::{Pattern, Variable as KoreVariable};
use k_rust::names::BuiltinSort;
use k_rust_backend::definition::BackendDefinition;
use k_rust_backend::externalize;
use k_rust_backend::smt::{Satisfiability, SmtSolver};
use k_rust_backend::substitution::{Substitution, substitute};
use k_rust_backend::term::{Sort, Symbol, SymbolType, Term, TermKind, Variable, VariableKind};
use k_rust_backend::unification::{UnificationFailure, UnificationResult, unify_term_pairs};
use kink_pattern::{Feasibility, PathInput, RelationDecider, RelationDecision, TermRelation};

/// Whether a leaf state is shown to have an instance.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum LeafFeasibility {
    /// A predicate-free term of free constructors, injections, domain values and element
    /// variables of inhabited sorts.
    Syntactic,
    /// Not shown feasible without a solver.
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
            .sorts
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
            for symbol in definition.symbols.values() {
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
                            .sort_graph
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

/// A constructor of K's free term algebra: total, injective, and distinct from every other
/// constructor and from every injection. Hooked, associative, idempotent, binder, collection,
/// `anywhere`, macro and sort-parametric symbols are excluded, because they are not free, and
/// so is a symbol that also carries the KORE `function` attribute (k-rust types it as a
/// constructor; k-rust's kompile never emits both, hand-written KORE may).
fn free_constructor(symbol: &Symbol) -> bool {
    let attributes = &symbol.attributes;
    attributes.symbol_type == SymbolType::Constructor
        && !attributes.declared_function
        && symbol.sort_variables.is_empty()
        && attributes.hook.is_none()
        && attributes.collection.is_none()
        && !attributes.anywhere
        && !attributes.associative
        && !attributes.idempotent
        && !attributes.binder
        && !attributes.macro_or_alias
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

/// The feasibility of a leaf state (KORE JSON) per the module documentation.
pub(crate) fn leaf_feasibility(
    definition: &BackendDefinition,
    inhabitation: &Inhabitation,
    state: &serde_json::Value,
) -> LeafFeasibility {
    let Ok(pattern) = k_rust::kore::codec::from_value(state) else {
        return LeafFeasibility::Unknown;
    };
    match definition.internalize_pattern(&pattern, &[]) {
        Ok(internal)
            if internal.constraints.is_empty()
                && constructor_term(&internal.term, inhabitation) =>
        {
            LeafFeasibility::Syntactic
        }
        _ => LeafFeasibility::Unknown,
    }
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
            .internalize_term(&Pattern::Variable(variable.clone()), &[])
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
fn proves_clash(failure: &UnificationFailure) -> bool {
    match failure {
        UnificationFailure::DifferentSymbols(left, right) => {
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
                matches!(term.kind(), TermKind::DomainValue { sort, .. }
                    if [BuiltinSort::Int, BuiltinSort::Bool, BuiltinSort::String]
                        .into_iter()
                        .any(|builtin| sort.is_builtin(builtin)))
            };
            canonical(left) && canonical(right)
        }
        UnificationFailure::VariableRecursion(variable, term) => {
            occurs_under_free_constructors(variable, term)
        }
        // Raised for disjoint injections and ill-sorted pairs alike; not claimed.
        UnificationFailure::DifferentSorts(..) => false,
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

/// Whether the unifier decomposes `term` only through free constructors and injections: every
/// application it may decompose (a constructor or an `injective` symbol) is a free constructor.
/// Decomposing any other symbol is not an equivalence. k-rust's kompile marks an `anywhere` or
/// overloaded production `injective` although its equations identify distinct applications
/// (`wrap(s(z)) => wrap(z) [anywhere]`), so a clash or solved form found below it proves
/// nothing. Collections are unsupported by the unifier and conservatively excluded.
fn decomposes_freely(term: &Term) -> bool {
    match term.kind() {
        TermKind::Variable(_) | TermKind::DomainValue { .. } => true,
        TermKind::Injection { term, .. } => decomposes_freely(term),
        TermKind::Application {
            symbol, arguments, ..
        } => {
            let decomposed = symbol.attributes.injective
                || symbol.attributes.symbol_type == SymbolType::Constructor;
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

/// `feasible` and `relate` for payloads of one execution, decided by the backend definition's
/// unifier and solver (see the module documentation).
///
/// The paths must come from [`crate::bridge::paths_from_execution`] over an execution of
/// `initial_state` on the same definition. Only terms whose variables are element variables of
/// `initial_state` are compared: those names mean one value along the whole path. A variable
/// introduced during execution is not, because k-rust renames a rule's existential variables
/// apart only from the current state, so one name can stand for two values on one path; a
/// definition whose rewrite rules have existential variables therefore leaves every comparison
/// involving a variable undecided.
pub struct BackendRelations<'a> {
    definition: &'a BackendDefinition,
    solver: &'a dyn SmtSolver,
    inhabitation: Inhabitation,
    /// The initial-state element variables, when they are stable and all inhabited.
    variables: Option<BTreeSet<Variable>>,
    /// Whether `solver` answers at all; `NoSolver` never does.
    solver_present: bool,
}

impl<'a> BackendRelations<'a> {
    #[must_use]
    pub fn new(
        definition: &'a BackendDefinition,
        solver: &'a dyn SmtSolver,
        initial_state: &Pattern,
    ) -> Self {
        let inhabitation = Inhabitation::of(definition);
        let existentials = definition
            .rewrite_theory
            .values()
            .flat_map(|priorities| priorities.values())
            .flatten()
            .any(|rule| !rule.existentials.is_empty());
        let variables = initial_state
            .free_variables()
            .into_iter()
            .map(|variable| {
                match definition
                    .internalize_term(&Pattern::Variable(variable), &[])
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
            .collect::<Option<BTreeSet<_>>>()
            .filter(|_| !existentials);
        Self {
            definition,
            solver,
            inhabitation,
            variables,
            solver_present: solver.is_sat(&[], &Substitution::new()).is_ok(),
        }
    }

    /// The internalized term, when every variable in it is a stable initial-state variable.
    fn term(&self, pattern: &Pattern) -> Option<Term> {
        let term = self.definition.internalize_term(pattern, &[]).ok()?;
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

    /// Asks the solver about the path predicate, the residual `constraints` and
    /// `substitution`. Only `Unsat` is used: a `Sat` needs the argument the Z3 profile owns.
    fn solver_check(
        &self,
        path: &PathInput,
        constraints: Vec<k_rust_backend::rule::Predicate>,
        substitution: &Substitution,
    ) -> Feasibility {
        let mut predicates = constraints;
        if !matches!(path.path_predicate, Pattern::Top { .. }) {
            let Ok((predicate, _)) = self
                .definition
                .internalize_predicate(&path.path_predicate, &[])
            else {
                return Feasibility::Unknown;
            };
            predicates.push(predicate);
        }
        match self.solver.is_sat(&predicates, substitution) {
            Ok(Satisfiability::Unsat) => Feasibility::Unsat,
            Ok(Satisfiability::Sat | Satisfiability::Unknown(_)) | Err(_) => Feasibility::Unknown,
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
        _path: &PathInput,
        assumed: &[TermRelation],
        left: &Pattern,
        right: &Pattern,
    ) -> RelationDecision {
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
            UnificationResult::Bottom(failure) if proves_clash(&failure) => {
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

    /// For assumptions that decompose freely: `Unsat` on a proved clash; without a solver, `Sat` on a real-prefix
    /// path with predicate `\top` when their solved form maps variables to constructor terms
    /// over inhabited sorts; otherwise the solver's `Unsat`, or `Unknown`.
    fn feasible(&self, path: &PathInput, assumptions: &[TermRelation]) -> Feasibility {
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
            UnificationResult::Bottom(failure) if proves_clash(&failure) => Feasibility::Unsat,
            UnificationResult::Unified(solved) => {
                if !self.solver_present
                    && solved.constraints.is_empty()
                    && matches!(path.path_predicate, Pattern::Top { .. })
                    && solved
                        .substitution
                        .values()
                        .all(|value| constructor_term(value, &self.inhabitation))
                {
                    Feasibility::Sat
                } else {
                    self.solver_check(path, solved.constraints, &solved.substitution)
                }
            }
            UnificationResult::Bottom(_) | UnificationResult::Unsupported { .. } => {
                Feasibility::Unknown
            }
        }
    }
}

/// Runs `operation` with the [`BackendRelations`] of `backend`'s default module and solver for
/// executions of `initial_state`.
pub fn with_backend_relations<T>(
    backend: &mut Backend,
    initial_state: &Pattern,
    operation: impl FnOnce(&BackendRelations<'_>) -> T,
) -> Result<T, BackendError> {
    backend.with_solver(None, |definition, solver| {
        Ok(operation(&BackendRelations::new(
            definition,
            solver,
            initial_state,
        )))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::backend::BackendOptions;
    use k_rust::kompile::CompileOptions;
    use k_rust::kore::{codec, parser::parse_definition};
    use k_rust_backend::rule::Predicate;
    use k_rust_backend::smt::{SmtError, Validity};
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
                    operand_sort: k_rust::kompile::initial_configuration::kore_sort("SortNat"),
                    result_sort: k_rust::kompile::initial_configuration::kore_sort(
                        "SortGeneratedTopCell",
                    ),
                    left: Box::new(nat("X")),
                    right: Box::new(z()),
                },
            ],
        };
        let rows = symmem
            .with_solver(None, |definition, _| {
                let inhabitation = Inhabitation::of(definition);
                let feasibility = |pattern: &Pattern| {
                    leaf_feasibility(
                        definition,
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
            .with_solver(None, |definition, _| {
                let plus = definition
                    .symbols
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
        let answers = with_backend_relations(&mut symmem, &state, |relations| {
            rows.iter()
                .map(|(id, assumed, left, right, _)| {
                    (*id, relations.relate(&real, assumed, left, right))
                })
                .collect::<Vec<_>>()
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
            operand_sort: k_rust::kompile::initial_configuration::kore_sort("SortNat"),
            result_sort: k_rust::kompile::initial_configuration::kore_sort("SortGeneratedTopCell"),
            left: Box::new(y.clone()),
            right: Box::new(z()),
        };
        // A present solver withholds the solver-free `Sat` (README 4.2, R9): the Z3 column is
        // what the current code produces and is provisional until SYM-3B-03 decides when a
        // solver `Sat` counts.
        let sat_without_solver = if cfg!(feature = "z3") { Unknown } else { Sat };
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
                sat_without_solver,
            ),
            (
                "constructor-instantiation",
                path(PathStop::Terminal, top()),
                vec![relation(x.clone(), s(y.clone()))],
                sat_without_solver,
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
        let answers = with_backend_relations(&mut symmem, &state, |relations| {
            rows.iter()
                .map(|(id, path, assumptions, _)| (*id, relations.feasible(path, assumptions)))
                .collect::<Vec<_>>()
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
                    .symbols
                    .values()
                    .find(|symbol| symbol.attributes.hook.as_deref() == Some("INT.add"))
                    .expect("+Int")
                    .name
                    .to_string();
                let one_plus_one = support::app(&plus, vec![support::int(1), support::int(1)]);
                let relations = BackendRelations::new(definition, solver, &state);
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
        ) -> Result<Satisfiability, SmtError> {
            self.0.clone()
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Result<Validity, SmtError> {
            Err(SmtError::Unavailable)
        }
    }

    /// With a solver present, a solver-free `Sat` is withheld and a solver `Sat` is not
    /// trusted; only `Unsat` is used. Relations do not depend on the solver.
    #[test]
    fn a_present_solver_contributes_only_unsat() {
        let mut symmem = backend("symmem.k", "SYMMEM");
        let state = symmem_state();
        let (x, y) = (nat("X"), nat("Y"));
        let assumptions = [relation(x.clone(), y.clone())];
        let real = path(PathStop::DepthLimit, top());
        let answers = symmem
            .with_solver(None, |definition, _| {
                let answer = |solver: Scripted| {
                    let relations = BackendRelations::new(definition, &solver, &state);
                    (
                        relations.feasible(&real, &assumptions),
                        relations.relate(&real, &[], &addr(x.clone()), &addr(y.clone())),
                    )
                };
                Ok::<_, BackendError>([
                    answer(Scripted(Ok(Satisfiability::Sat))),
                    answer(Scripted(Ok(Satisfiability::Unsat))),
                    answer(Scripted(Ok(Satisfiability::Unknown("scripted".into())))),
                ])
            })
            .expect("relations");
        let equal_if = EqualIf(assumptions.to_vec());
        assert_eq!(
            answers,
            [
                (Unknown, equal_if.clone()),
                (Unsat, equal_if.clone()),
                (Unknown, equal_if),
            ]
        );
    }

    const WRAP: &str = r"[]
        module MAIN
            sort SortNat{} []
            symbol Lblz{}() : SortNat{} [constructor{}(), functional{}()]
            symbol Lbls{}(SortNat{}) : SortNat{} [constructor{}(), functional{}()]
            symbol Lblpair{}(SortNat{}, SortNat{}) : SortNat{} [constructor{}(), functional{}()]
            symbol Lblwrap{}(SortNat{}) : SortNat{} [functional{}(), injective{}(), anywhere{}()]
            symbol Lblboth{}(SortNat{}) : SortNat{} [constructor{}(), function{}()]
        endmodule []";

    /// Audit (SYM-3A-09): k-rust's kompile marks an `anywhere` production `injective`, and the
    /// unifier decomposes it, but its equations can identify `wrap(s(z))` with `wrap(z)`. A
    /// clash or solved form below it is therefore not evidence; identical terms still are. The
    /// same holds for a symbol that k-rust types as a constructor although it is a `function`.
    #[test]
    fn non_free_injective_symbols_leave_relations_undecided() {
        let definition =
            BackendDefinition::internalize(&parse_definition(WRAP).expect("KORE"), "MAIN")
                .expect("definition");
        let (x, y) = (nat("X"), nat("Y"));
        let wrap = |value: Pattern| support::app("Lblwrap", vec![value]);
        let both = |value: Pattern| support::app("Lblboth", vec![value]);
        let state = support::app("Lblpair", vec![x.clone(), y.clone()]);
        let solver = Scripted(Err(SmtError::Unavailable));
        let relations = BackendRelations::new(&definition, &solver, &state);
        let real = path(PathStop::Terminal, top_of("SortNat"));
        assert_eq!(
            [
                relations.relate(&real, &[], &wrap(s(x.clone())), &wrap(z())),
                relations.relate(&real, &[], &wrap(x.clone()), &wrap(y.clone())),
                relations.relate(&real, &[], &wrap(x.clone()), &wrap(x.clone())),
                relations.relate(&real, &[], &s(x.clone()), &z()),
                relations.relate(&real, &[], &x, &y),
                relations.relate(&real, &[], &both(z()), &both(s(z()))),
            ],
            [
                Indeterminate,
                Indeterminate,
                Equal,
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

    /// A definition whose rewrite rules introduce existential variables can reuse a variable
    /// name for two values on one path, so no comparison involving a variable is decided.
    #[test]
    fn existential_rules_leave_variable_comparisons_undecided() {
        let mut symmem = backend("symmem.k", "SYMMEM");
        let state = symmem_state();
        let (x, y) = (nat("X"), nat("Y"));
        let real = path(PathStop::DepthLimit, top());
        let answers = symmem
            .with_solver(None, |definition, solver| {
                let mut definition = definition.clone();
                let rule = definition
                    .rewrite_theory
                    .values_mut()
                    .flat_map(|priorities| priorities.values_mut())
                    .flatten()
                    .next()
                    .expect("a rewrite rule");
                let mut changed = (*rule.rule).clone();
                changed
                    .existentials
                    .insert(Variable::new("Ex#Fresh", Sort::simple("SortNat")));
                rule.rule = std::sync::Arc::new(changed);
                let relations = BackendRelations::new(&definition, solver, &state);
                Ok::<_, BackendError>([
                    relations.relate(&real, &[], &addr(x.clone()), &addr(x.clone())),
                    relations.relate(&real, &[], &addr(x.clone()), &addr(y.clone())),
                    relations.relate(&real, &[], &z(), &s(z())),
                ])
            })
            .expect("relations");
        assert_eq!(answers, [Indeterminate, Indeterminate, Unequal]);
    }
}

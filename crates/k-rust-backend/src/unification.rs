//! ```toml algorithm
//! id = "backend.unification.syntactic"
//! name = "syntactic first-order unification with eager substitution composition"
//! sites = ["unify_term_pairs", "Unifier::run", "Unifier::unify_one"]
//! variable = "n = pairs; s = bindings; t = term size"
//! counters = ["UnificationProblems"]
//! span = "per problem"
//! produces = [{ type = "k_rust_backend::unification::UnificationResult", role = "unification result" }]
//!
//! [[cost]]
//! mode = "symbolic KORE terms"
//! bound = "O(n x s x t)"
//! ```
//!
//! Syntactic first-order unification (Robinson / Martelli-Montanari work queue with eager
//! composition) for symbolic KORE terms: O(n x s x t) for n pairs, s bindings, and term size t,
//! since each pop re-substitutes both sides and each bind composes the whole substitution; a
//! variable cycle through free constructors and injections only is bottom, and any other cycle
//! stays an equation; `Counter::UnificationProblems`.
//!
//! Collection and hook-specific theories remain separate because they may produce more than one
//! solution. This procedure handles the common syntactic theory, saturates bindings in both
//! orientations, and retains irreducible functional equations as predicates.
//!
//! Both sides of an equation are read as the values they denote (`term::head::classify_value`,
//! with the instance-normal scan as the evidence for an equation-head root). An equal-name
//! application pair is decomposed into its argument pairs only when equal applications of the
//! symbol have equal arguments on every instance: two fixed roots of one symbol (a free
//! constructor, or an equation head whose two applications are both instance-normal), or a
//! function declared injective without the `anywhere` attribute. An equation head's equations
//! may identify applications with different arguments (`wrap(s(z)) = wrap(z)` makes
//! `wrap(s(X)) = wrap(z)` true for `X = z`), so decomposing such a pair could turn a
//! satisfiable equation into a false clash; it stays a residual equation instead. The
//! conservative test also keeps an overload-greater `f(X) = f(Y)` as an equation rather than
//! `X = Y`, which costs completeness, not soundness. Only two fixed roots that differ, neither of
//! them an equation head's, clash (a [`HeadClash`]).

use std::collections::VecDeque;

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::{
    condition::MatchSolution,
    definition::BackendDefinition,
    matching::{InjectionEquality, match_injection_equality},
    rule::Predicate,
    substitution::{Substitution, compose, substitute},
    term::{
        Term, TermKind, Variable,
        head::{
            FixedRoot, Head, HeadClash, NoEvidence, Open, ReleasedRoots, RigidCycle,
            RootComparison, SameApplication, Scanned, classify_value, compare_roots,
            rigid_occurrence,
        },
    },
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Unification {
    pub substitution: Substitution,
    /// The equations the unifier kept because their roots decide nothing, with `substitution` applied.
    /// They hold exactly where the input pairs do, together with the bindings of `substitution`; a
    /// caller that drops a binding of an element variable to a term states that term's definedness.
    pub constraints: Vec<Predicate>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnificationResult {
    Unified(Unification),
    Bottom(UnificationFailure),
    Unsupported {
        substitution: Substitution,
        /// The equations the unifier kept because their roots decide nothing, with `substitution` applied.
        /// They hold exactly where the input pairs do, together with the bindings of `substitution`; a
        /// caller that drops a binding of an element variable to a term states that term's definedness.
        constraints: Vec<Predicate>,
        remainder: Vec<(Term, Term)>,
    },
}

/// Unification of a match, keeping its conditions under the resulting bindings.
pub(crate) enum MatchUnification {
    Unified(MatchSolution),
    Bottom(UnificationFailure),
    Unsupported {
        solution: MatchSolution,
        remainder: Vec<(Term, Term)>,
    },
}

/// Unify `pairs` from `initial`. Its conditions and the equations the unifier keeps leave
/// under the unifier's final substitution, including bindings found after an equation was kept.
pub(crate) fn unify_from(
    definition: &BackendDefinition,
    initial: MatchSolution,
    pairs: impl IntoIterator<Item = (Term, Term)>,
) -> MatchUnification {
    let (substitution, conditions) = initial.into_parts();
    match unify_term_pairs(definition, substitution, pairs) {
        UnificationResult::Unified(unified) => {
            let mut solution = MatchSolution::from_parts(unified.substitution, conditions);
            solution.conjoin(unified.constraints);
            MatchUnification::Unified(solution)
        }
        UnificationResult::Bottom(failure) => MatchUnification::Bottom(failure),
        UnificationResult::Unsupported {
            substitution,
            constraints,
            remainder,
        } => {
            let mut solution = MatchSolution::from_parts(substitution, conditions);
            solution.conjoin(constraints);
            MatchUnification::Unsupported {
                solution,
                remainder,
            }
        }
    }
}

/// Why two terms have no common instance.
///
/// A clash of roots carries a [`HeadClash`], and a variable that would be bound to a term built
/// around itself a [`RigidCycle`]. The backend builds both only from roots that are the roots of
/// every value their terms denote, so neither can be stated about a bare variable and term:
///
/// ```compile_fail
/// use k_rust_backend::{term::{Term, Variable}, unification::UnificationFailure};
/// fn refute(x: Variable, t: Term) -> UnificationFailure {
///     UnificationFailure::VariableRecursion(x, t)
/// }
/// ```
///
/// ```
/// use k_rust_backend::{term::{Term, Variable}, unification::UnificationFailure};
/// fn refute(x: Variable, t: Term) -> UnificationFailure {
///     UnificationFailure::DifferentValues(t.clone(), t)
/// }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnificationFailure {
    DifferentSorts(Term, Term),
    DifferentValues(Term, Term),
    /// Two roots that no one value has.
    DifferentSymbols(HeadClash),
    /// A variable that would be bound to a term built around it by free constructors and
    /// injections.
    VariableRecursion(RigidCycle),
    /// Two applications of one symbol with equal sort arguments and different numbers of
    /// arguments: an ill-formed pair.
    ArgumentLengthsDiffer(Term, Term),
}

/// Unify all `pairs` under an existing partial substitution.
///
/// Bindings are symmetric: variables from either side may be solved. An equal-name application
/// pair is replaced by its argument pairs when its head is a free constructor (a declared
/// axiom), an equation head whose two applications are normal on every instance (derived from
/// the definition's equations), or a function declared `injective` (a declared axiom that is not
/// checked against those equations). This includes a non-`anywhere` `function` symbol with a
/// user-written `injective` attribute. The `injective` attribute is ignored on `anywhere`
/// symbols. Sort injections are also decomposed. Only distinct free-constructor, domain-value
/// and injection roots clash; other equations are retained as constraints. AC collections are
/// returned as unsupported so their dedicated multi-solution solvers can run.
pub fn unify_term_pairs(
    definition: &BackendDefinition,
    initial: Substitution,
    pairs: impl IntoIterator<Item = (Term, Term)>,
) -> UnificationResult {
    let _span = measure::algorithm_span(Algorithm::BackendUnificationSyntactic);
    let mut unifier = Unifier {
        definition,
        substitution: initial,
        pending: pairs.into_iter().collect(),
        equations: Vec::new(),
        unsupported: Vec::new(),
    };
    measure::bump(Counter::UnificationProblems);
    if let Err(failure) = unifier.run() {
        return UnificationResult::Bottom(failure);
    }
    // A residual equation recorded before a later binding mentions the bound variable; under the
    // final substitution it states the same equation on the unifier's solutions.
    let constraints = unifier
        .equations
        .into_iter()
        .map(|(left, right)| {
            Predicate::Equals(
                substitute(&left, &unifier.substitution),
                substitute(&right, &unifier.substitution),
            )
        })
        .collect();
    if unifier.unsupported.is_empty() {
        UnificationResult::Unified(Unification {
            substitution: unifier.substitution,
            constraints,
        })
    } else {
        UnificationResult::Unsupported {
            substitution: unifier.substitution.clone(),
            constraints,
            remainder: unifier
                .unsupported
                .into_iter()
                .map(|(left, right)| {
                    (
                        substitute(&left, &unifier.substitution),
                        substitute(&right, &unifier.substitution),
                    )
                })
                .collect(),
        }
    }
}

struct Unifier<'a> {
    definition: &'a BackendDefinition,
    substitution: Substitution,
    pending: VecDeque<(Term, Term)>,
    /// The equations whose roots decide nothing, as `(left, right)`. Only equations are kept, so
    /// the one substitution they undergo is the one of their two sides.
    equations: Vec<(Term, Term)>,
    unsupported: Vec<(Term, Term)>,
}

impl Unifier<'_> {
    fn run(&mut self) -> Result<(), UnificationFailure> {
        // Binds strictly reduce the free variables of the pending multiset and decompositions
        // strictly reduce its size, so the loop terminates; a popped pair is re-substituted first;
        // opaque equations are deferred to `constraints`, AC pairs to `unsupported`.
        // Invariant: `substitution` is idempotent and unifies every pair popped so far.
        while let Some((left, right)) = self.pending.pop_front() {
            let left = substitute(&left, &self.substitution);
            let right = substitute(&right, &self.substitution);
            self.unify_one(left, right)?;
        }
        Ok(())
    }

    fn unify_one(&mut self, left: Term, right: Term) -> Result<(), UnificationFailure> {
        if left == right {
            return Ok(());
        }
        if left.sort() != right.sort() {
            return Err(UnificationFailure::DifferentSorts(left, right));
        }
        if let TermKind::And(first, second) = left.kind() {
            self.pending.push_back((first.clone(), right.clone()));
            self.pending.push_back((second.clone(), right));
            return Ok(());
        }
        if let TermKind::And(first, second) = right.kind() {
            self.pending.push_back((left.clone(), first.clone()));
            self.pending.push_back((left, second.clone()));
            return Ok(());
        }
        if let (TermKind::Variable(left_variable), TermKind::Variable(right_variable)) =
            (left.kind(), right.kind())
        {
            let (variable, term) = if left_variable <= right_variable {
                (left_variable.clone(), right)
            } else {
                (right_variable.clone(), left)
            };
            return self.bind(variable, term);
        }
        if let TermKind::Variable(variable) = left.kind() {
            return self.bind(variable.clone(), right);
        }
        if let TermKind::Variable(variable) = right.kind() {
            return self.bind(variable.clone(), left);
        }

        match (left.kind(), right.kind()) {
            (
                TermKind::DomainValue {
                    sort: left_sort,
                    value: left_value,
                },
                TermKind::DomainValue {
                    sort: right_sort,
                    value: right_value,
                },
            ) => {
                if left_sort == right_sort && left_value == right_value {
                    Ok(())
                } else {
                    Err(UnificationFailure::DifferentValues(left, right))
                }
            }
            (TermKind::Injection { .. }, TermKind::Injection { .. }) => {
                match match_injection_equality(Some(self.definition.sort_graph()), &left, &right) {
                    Some(InjectionEquality::Direct(left, right))
                    | Some(InjectionEquality::Split(left, right)) => {
                        self.pending.push_back((left, right));
                        Ok(())
                    }
                    Some(InjectionEquality::Distinct) | None => {
                        Err(UnificationFailure::DifferentSorts(left, right))
                    }
                    Some(InjectionEquality::Unknown) => {
                        self.equations.push((left, right));
                        Ok(())
                    }
                }
            }
            _ => {
                let arguments = one_symbol(&left, &right);
                let (left_head, right_head) = self.classify(&left, &right, arguments.is_some());
                match unification_root_policy(left_head, right_head, arguments) {
                    UnifierStep::Decompose(decomposition) => {
                        self.decompose(decomposition);
                        Ok(())
                    }
                    UnifierStep::ArgumentLengthsDiffer => {
                        Err(UnificationFailure::ArgumentLengthsDiffer(left, right))
                    }
                    UnifierStep::Refute(witness) => Err(UnificationFailure::DifferentSymbols(
                        HeadClash::new(witness, left, right),
                    )),
                    UnifierStep::Unsupported => {
                        self.unsupported.push((left, right));
                        Ok(())
                    }
                    UnifierStep::Keep => {
                        self.equations.push((left, right));
                        Ok(())
                    }
                }
            }
        }
    }

    /// Classify both sides as the values they denote, with the instance-normal scan as the
    /// oracle for an equation-head root (`Scanned`). The scan runs equation matchers, so it is
    /// asked only where its answer changes the step: for two applications of one symbol with
    /// equal sort arguments (`one_symbol`), which decompose when both roots are fixed, and for
    /// the right one only when the left one is fixed. Every other equation-head root keeps its
    /// equation whether it is fixed or not, since the unifier refutes no equation-head root
    /// (open question Q4 of the classifier's design), so it is classified without evidence.
    fn classify<'t>(
        &self,
        left: &'t Term,
        right: &'t Term,
        one_symbol: bool,
    ) -> (Head<'t>, Head<'t>) {
        if !one_symbol {
            return (
                classify_value(left, &mut NoEvidence),
                classify_value(right, &mut NoEvidence),
            );
        }
        let mut scanned = Scanned(self.definition);
        let left_head = classify_value(left, &mut scanned);
        let right_head = match left_head {
            Head::Fixed(_) => classify_value(right, &mut scanned),
            Head::Open(_) | Head::Residual => classify_value(right, &mut NoEvidence),
        };
        (left_head, right_head)
    }

    /// Replace an equation between two applications of one symbol by the equations between their
    /// arguments, in argument order: the one place the unifier decomposes an application pair.
    fn decompose(&mut self, decomposition: Decomposition<'_>) {
        match decomposition {
            Decomposition::SameApplication(same) => self.pending.extend(
                same.pairs()
                    .map(|(left, right)| (left.clone(), right.clone())),
            ),
            Decomposition::InjectiveFunction(left, right) => self
                .pending
                .extend(left.iter().cloned().zip(right.iter().cloned())),
        }
    }

    fn bind(&mut self, variable: Variable, term: Term) -> Result<(), UnificationFailure> {
        let term = substitute(&term, &self.substitution);
        if term.attributes().variables.contains(&variable) {
            // A free constructor or an injection builds a value strictly larger than each of its
            // arguments, so no finite value equals one built around itself through such roots
            // only. Below any other root (a function, an equation head, a collection) the
            // occurrence may vanish when that root is evaluated (`X = incPos(X -Int 1)` holds
            // for every `X`), so the equation is kept for evaluation to decide: it is neither a
            // binding nor a contradiction.
            if let Some(cycle) = rigid_occurrence(&variable, &term) {
                return Err(UnificationFailure::VariableRecursion(cycle));
            }
            self.equations.push((Term::variable(variable), term));
            return Ok(());
        }
        let binding = Substitution::from([(variable, term)]);
        self.substitution = compose(&binding, &self.substitution);
        Ok(())
    }
}

/// The argument slices of two applications of one symbol name with equal sort arguments, or
/// `None`.
fn one_symbol<'t>(left: &'t Term, right: &'t Term) -> Option<(&'t [Term], &'t [Term])> {
    match (left.kind(), right.kind()) {
        (
            TermKind::Application {
                symbol: left_symbol,
                sort_arguments: left_sorts,
                arguments: left_arguments,
            },
            TermKind::Application {
                symbol: right_symbol,
                sort_arguments: right_sorts,
                arguments: right_arguments,
            },
        ) if left_symbol.name == right_symbol.name && left_sorts == right_sorts => {
            Some((left_arguments, right_arguments))
        }
        _ => None,
    }
}

/// What the roots of the two sides of an equation decide in unification
/// ([`unification_root_policy`]).
#[derive(Clone, Copy, Debug)]
enum UnifierStep<'t> {
    /// Replace the equation by the equations between the arguments.
    Decompose(Decomposition<'t>),
    /// Two applications of one symbol with different numbers of arguments.
    ArgumentLengthsDiffer,
    /// The roots differ: no value has both.
    Refute(ReleasedRoots),
    /// A collection, left to the collection solvers.
    Unsupported,
    /// The roots decide nothing: the equation is kept as a constraint.
    Keep,
}

/// Why an equation between two applications of one symbol may be replaced by the equations
/// between their arguments ([`Unifier::decompose`]).
#[derive(Clone, Copy, Debug)]
enum Decomposition<'t> {
    /// Two fixed roots of one free symbol (`compare_roots`): the values are equal exactly when
    /// the arguments are.
    SameApplication(SameApplication<'t>),
    /// Two applications of one function declared injective without `anywhere`, a declared axiom
    /// the backend does not check against the function's equations (open question Q5).
    InjectiveFunction(&'t [Term], &'t [Term]),
}

/// The unifier's root policy: what the roots of two terms, each classified as the value it
/// denotes, decide. `arguments` are the argument slices when both terms are applications of one
/// symbol with equal sort arguments (`one_symbol`). Pure.
///
/// Two fixed roots that differ refute the equation, unless one of them is an equation head's
/// (open question Q4: an instance-normal equation head against another root stays an
/// equation). Two fixed roots of one symbol, and two applications of one function declared
/// injective, decompose; with different numbers of arguments they are an ill-formed pair. A
/// collection is left to the collection solvers, and every other pair, among them a macro or
/// alias root, keeps its equation.
#[must_use]
#[deny(clippy::wildcard_enum_match_arm)]
fn unification_root_policy<'t>(
    left: Head<'t>,
    right: Head<'t>,
    arguments: Option<(&'t [Term], &'t [Term])>,
) -> UnifierStep<'t> {
    if matches!(left, Head::Open(Open::Uninterpreted))
        || matches!(right, Head::Open(Open::Uninterpreted))
    {
        return UnifierStep::Keep;
    }
    if is_collection_root(left) || is_collection_root(right) {
        return UnifierStep::Unsupported;
    }
    match left {
        Head::Fixed(left_root) => match right {
            Head::Fixed(right_root) => match compare_roots(left_root, right_root) {
                RootComparison::Distinct(witness) => {
                    if is_equation_head(left) || is_equation_head(right) {
                        UnifierStep::Keep
                    } else {
                        UnifierStep::Refute(witness.release())
                    }
                }
                RootComparison::SameApplication(same) => {
                    UnifierStep::Decompose(Decomposition::SameApplication(same))
                }
                RootComparison::ArityMismatch => UnifierStep::ArgumentLengthsDiffer,
                // Compared by their own arms in `Unifier::unify_one` before any classification.
                RootComparison::DomainValues | RootComparison::Injections => UnifierStep::Keep,
                RootComparison::Collections(_) => UnifierStep::Unsupported,
            },
            Head::Open(_) | Head::Residual => UnifierStep::Keep,
        },
        Head::Open(Open::Function {
            injective: true, ..
        }) => match (right, arguments) {
            (
                Head::Open(Open::Function {
                    injective: true, ..
                }),
                Some((left, right)),
            ) => {
                if left.len() == right.len() {
                    UnifierStep::Decompose(Decomposition::InjectiveFunction(left, right))
                } else {
                    UnifierStep::ArgumentLengthsDiffer
                }
            }
            (Head::Open(_) | Head::Fixed(_) | Head::Residual, _) => UnifierStep::Keep,
        },
        Head::Open(
            Open::Function {
                injective: false, ..
            }
            | Open::Variable
            | Open::And
            | Open::EquationHead
            | Open::Uninterpreted,
        )
        | Head::Residual => UnifierStep::Keep,
    }
}

/// A collection root.
#[deny(clippy::wildcard_enum_match_arm)]
fn is_collection_root(head: Head<'_>) -> bool {
    match head {
        Head::Fixed(fixed) => match fixed.root() {
            FixedRoot::Collection(_) => true,
            FixedRoot::DomainValue
            | FixedRoot::Injection
            | FixedRoot::FreeConstructor
            | FixedRoot::EquationHead(_) => false,
        },
        Head::Open(_) | Head::Residual => false,
    }
}

/// An equation-head root.
#[deny(clippy::wildcard_enum_match_arm)]
fn is_equation_head(head: Head<'_>) -> bool {
    match head {
        Head::Fixed(fixed) => match fixed.root() {
            FixedRoot::EquationHead(_) => true,
            FixedRoot::DomainValue
            | FixedRoot::Injection
            | FixedRoot::Collection(_)
            | FixedRoot::FreeConstructor => false,
        },
        Head::Open(open) => match open {
            Open::EquationHead => true,
            Open::Variable | Open::And | Open::Function { .. } | Open::Uninterpreted => false,
        },
        Head::Residual => false,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use k_rust_kore::kore::parser::parse_definition;

    use crate::term::{FunctionType, HeadRole, Sort, Symbol, SymbolType};

    use super::*;

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} []
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn sort() -> Sort {
        Sort::simple("SortS")
    }

    fn variable(name: &str) -> Variable {
        Variable::new(name, sort())
    }

    fn var(name: &str) -> Term {
        Term::variable(variable(name))
    }

    fn constructor(name: &str, arguments: Vec<Term>) -> Term {
        let sorts = vec![sort(); arguments.len()];
        Term::application(
            Arc::new(Symbol::constructor(name, sorts, sort())),
            Vec::new(),
            arguments,
        )
    }

    fn function(name: &str, arguments: Vec<Term>) -> Term {
        let sorts = vec![sort(); arguments.len()];
        let mut symbol = Symbol::constructor(name, sorts, sort());
        symbol.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
        symbol.attributes.has_evaluators = true;
        Term::application(Arc::new(symbol), Vec::new(), arguments)
    }

    #[test]
    fn saturates_non_linear_first_order_bindings() {
        let a = constructor("a", Vec::new());
        let left = constructor("f", vec![constructor("g", vec![var("X")]), var("X")]);
        let right = constructor("f", vec![var("Y"), a.clone()]);

        let UnificationResult::Unified(result) =
            unify_term_pairs(&definition(), Substitution::new(), [(left, right)])
        else {
            panic!("first-order terms should unify");
        };

        assert_eq!(result.substitution[&variable("X")], a.clone());
        assert_eq!(
            result.substitution[&variable("Y")],
            constructor("g", vec![a])
        );
        assert!(result.constraints.is_empty());
    }

    #[test]
    fn rejects_occurs_check_cycles() {
        let result = unify_term_pairs(
            &definition(),
            Substitution::new(),
            [(var("X"), constructor("g", vec![var("X")]))],
        );

        assert!(matches!(
            result,
            UnificationResult::Bottom(UnificationFailure::VariableRecursion(cycle))
                if cycle.variable().name.as_ref() == "X"
        ));
    }

    /// regression-new spec-rule-application def62: after `Y2 := X2 -Int 1` the deferred pair
    /// `incPos(Y2) ~ X2` becomes `X2 ~ incPos(X2 -Int 1)`, a cycle through a function symbol.
    /// Kore's substitution normalization keeps such a "simplifiable" cycle as a denormalized
    /// predicate (Kore/Unification/SubstitutionNormalization.hs simplifiableCycle) that
    /// evaluation later discharges (`incPos(X2 -Int 1)` is `X2`); only a cycle through
    /// constructors is bottom (mixedCtorCycle).
    #[test]
    fn retains_a_function_cycle_as_an_equality() {
        let cycle = function("f", vec![var("X")]);
        let result = unify_term_pairs(
            &definition(),
            Substitution::new(),
            [(var("X"), cycle.clone())],
        );

        let UnificationResult::Unified(result) = result else {
            panic!("a cycle through a function symbol is a predicate, not bottom: {result:?}");
        };
        assert!(result.substitution.is_empty(), "{result:?}");
        assert_eq!(result.constraints, [Predicate::Equals(var("X"), cycle)]);
    }

    /// An equation kept before a later pair binds one of its variables comes out under the final
    /// substitution: `f(X) = a` is kept, `X = b` then binds `X`, and the result states `f(b) = a`.
    #[test]
    fn states_kept_equations_under_the_final_substitution() {
        let a = constructor("a", Vec::new());
        let b = constructor("b", Vec::new());
        let result = unify_term_pairs(
            &definition(),
            Substitution::new(),
            [
                (function("f", vec![var("X")]), a.clone()),
                (var("X"), b.clone()),
            ],
        );
        let UnificationResult::Unified(result) = result else {
            panic!("an opaque function equation and a binding should unify: {result:?}");
        };
        assert_eq!(result.substitution[&variable("X")], b);
        assert_eq!(
            result.constraints,
            [Predicate::Equals(function("f", vec![b]), a)]
        );
    }

    #[test]
    fn decomposes_conjunctions_before_binding_variables() {
        let a = constructor("a", Vec::new());
        let result = unify_term_pairs(
            &definition(),
            Substitution::new(),
            [(var("X"), Term::and(a.clone(), a.clone()))],
        );

        let UnificationResult::Unified(result) = result else {
            panic!("identical conjunction operands should unify");
        };
        assert_eq!(result.substitution[&variable("X")], a);

        assert!(matches!(
            unify_term_pairs(
                &definition(),
                Substitution::new(),
                [(
                    var("X"),
                    Term::and(constructor("a", Vec::new()), constructor("b", Vec::new()),),
                )],
            ),
            UnificationResult::Bottom(UnificationFailure::DifferentSymbols(_))
        ));
    }

    #[test]
    fn retains_opaque_function_equalities_as_constraints() {
        let left = function("left", vec![var("X")]);
        let right = function("right", vec![var("Y")]);

        let UnificationResult::Unified(result) = unify_term_pairs(
            &definition(),
            Substitution::new(),
            [(left.clone(), right.clone())],
        ) else {
            panic!("opaque functions should produce a constraint");
        };

        assert!(result.substitution.is_empty());
        assert_eq!(result.constraints, [Predicate::Equals(left, right)]);
    }

    #[test]
    fn decomposes_a_declared_injective_function_on_the_attribute() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} []
                symbol f{}(SortS{}) : SortS{}
                    [function{}(), total{}(), injective{}()]
            endmodule []"#,
        )
        .expect("injective function definition should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("injective function definition should internalize");
        let left = anywhere_term(&definition, "f{}(X:SortS{})");
        let right = anywhere_term(&definition, "f{}(Y:SortS{})");
        let TermKind::Application { symbol, .. } = left.kind() else {
            panic!("f should be an application");
        };
        assert!(matches!(
            symbol.attributes.symbol_type,
            SymbolType::Function(_)
        ));
        assert_eq!(
            symbol.attributes.head_role(),
            HeadRole::Function {
                declared: true,
                injective: true,
                refutable_arguments: true
            }
        );

        let UnificationResult::Unified(result) =
            unify_term_pairs(&definition, Substitution::new(), [(left, right)])
        else {
            panic!("declared injectivity should decompose f(X) = f(Y)");
        };
        assert_eq!(
            result.substitution,
            Substitution::from([(variable("X"), var("Y"))])
        );
        assert!(result.constraints.is_empty());
    }

    #[test]
    fn binds_a_supersort_variable_to_the_injected_subsort_term() {
        let sub = Sort::simple("SortSub");
        let sup = Sort::simple("SortSup");
        let variable = Variable::new("Y", sup.clone());
        let injected = Term::injection(sub.clone(), sup, Term::variable(Variable::new("X", sub)));
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} []
                sort SortSub{} []
                sort SortSup{} []
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                axiom{R} \exists{R}(Value:SortSup{},
                    \equals{SortSup{}, R}(Value:SortSup{}, inj{SortSub{}, SortSup{}}(From:SortSub{})))
                    [subsort{SortSub{}, SortSup{}}()]
            endmodule []"#,
        )
        .expect("subsort definition should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("subsort definition should internalize");

        let UnificationResult::Unified(result) = unify_term_pairs(
            &definition,
            Substitution::new(),
            [(injected.clone(), Term::variable(variable.clone()))],
        ) else {
            panic!("a sort-aligned injection and supersort variable should unify");
        };

        assert_eq!(
            result.substitution,
            Substitution::from([(variable, injected)])
        );
        assert!(result.constraints.is_empty());
    }

    #[test]
    fn preserves_overlapping_incomparable_injections_as_an_equality() {
        let item = Sort::simple("SortItem");
        let left_sort = Sort::simple("SortLeft");
        let right_sort = Sort::simple("SortRight");
        let disjoint_sort = Sort::simple("SortDisjoint");
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} []
                sort SortItem{} []
                sort SortLeft{} []
                sort SortRight{} []
                sort SortCommon{} []
                sort SortDisjoint{} []
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                axiom{R} \exists{R}(Value:SortItem{},
                    \equals{SortItem{}, R}(Value:SortItem{}, inj{SortLeft{}, SortItem{}}(From:SortLeft{})))
                    [subsort{SortLeft{}, SortItem{}}()]
                axiom{R} \exists{R}(Value:SortItem{},
                    \equals{SortItem{}, R}(Value:SortItem{}, inj{SortRight{}, SortItem{}}(From:SortRight{})))
                    [subsort{SortRight{}, SortItem{}}()]
                axiom{R} \exists{R}(Value:SortItem{},
                    \equals{SortItem{}, R}(Value:SortItem{}, inj{SortDisjoint{}, SortItem{}}(From:SortDisjoint{})))
                    [subsort{SortDisjoint{}, SortItem{}}()]
                axiom{R} \exists{R}(Value:SortLeft{},
                    \equals{SortLeft{}, R}(Value:SortLeft{}, inj{SortCommon{}, SortLeft{}}(From:SortCommon{})))
                    [subsort{SortCommon{}, SortLeft{}}()]
                axiom{R} \exists{R}(Value:SortRight{},
                    \equals{SortRight{}, R}(Value:SortRight{}, inj{SortCommon{}, SortRight{}}(From:SortCommon{})))
                    [subsort{SortCommon{}, SortRight{}}()]
            endmodule []"#,
        )
        .expect("overlapping subsort definition should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("overlapping subsort definition should internalize");

        let left = Term::injection(
            left_sort.clone(),
            item.clone(),
            Term::variable(Variable::new("LEFT", left_sort)),
        );
        let right = Term::injection(
            right_sort.clone(),
            item.clone(),
            Term::variable(Variable::new("RIGHT", right_sort)),
        );
        let separate = Term::injection(
            disjoint_sort.clone(),
            item,
            Term::variable(Variable::new("DISJOINT", disjoint_sort)),
        );

        let UnificationResult::Unified(result) = unify_term_pairs(
            &definition,
            Substitution::new(),
            [(left.clone(), right.clone())],
        ) else {
            panic!("overlapping injection sources should remain symbolic");
        };
        assert!(result.substitution.is_empty());
        assert_eq!(result.constraints, [Predicate::Equals(left.clone(), right)]);

        assert!(matches!(
            unify_term_pairs(&definition, Substitution::new(), [(left, separate)]),
            UnificationResult::Bottom(UnificationFailure::DifferentSorts(_, _))
        ));
    }

    /// `wrap` is an `anywhere` production (injective as kompile emits it today) with the
    /// equation `wrap(s(z)) = wrap(z)`, bound through `\in` as kompile emits it; `pair` is an
    /// `anywhere` production without equations; `f` is a declared function.
    fn anywhere_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortNat{} []
                sort SortAddress{} []
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol f{}(SortNat{}) : SortNat{} [function{}(), total{}(), no-evaluators{}()]
                symbol wrap{}(SortNat{}) : SortAddress{}
                    [anywhere{}(), functional{}(), injective{}()]
                symbol pair{}(SortNat{}, SortNat{}) : SortAddress{}
                    [anywhere{}(), functional{}(), injective{}(), no-evaluators{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(z{}())), \top{R}())
                    ),
                    \equals{SortAddress{}, R}(
                        wrap{}(X0:SortNat{}),
                        \and{SortAddress{}}(wrap{}(z{}()), \top{SortAddress{}}())
                    )
                ) [label{}("collapse"), anywhere{}()]
            endmodule []"#,
        )
        .expect("anywhere definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn anywhere_term(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(
                &k_rust_kore::kore::parser::parse_pattern(source).expect("term should parse"),
                &[],
            )
            .expect("term should internalize")
    }

    fn unify_anywhere(left: &str, right: &str) -> UnificationResult {
        let definition = anywhere_definition();
        let left = anywhere_term(&definition, left);
        let right = anywhere_term(&definition, right);
        unify_term_pairs(&definition, Substitution::new(), [(left, right)])
    }

    /// `X = z` makes `wrap(s(X))` equal to `wrap(z)` through the equation, so the pair must stay
    /// an equation rather than clash `s(X)` with `z`.
    #[test]
    fn keeps_an_anywhere_pair_an_equation_may_identify() {
        let left = "wrap{}(s{}(X:SortNat{}))";
        let right = "wrap{}(z{}())";
        let UnificationResult::Unified(result) = unify_anywhere(left, right) else {
            panic!(
                "an instance of wrap(s(X)) equals wrap(z): {:?}",
                unify_anywhere(left, right)
            );
        };
        let definition = anywhere_definition();
        assert!(result.substitution.is_empty(), "{result:?}");
        assert_eq!(
            result.constraints,
            [Predicate::Equals(
                anywhere_term(&definition, left),
                anywhere_term(&definition, right)
            )]
        );
    }

    /// No instance of `wrap(s(s(X)))` matches the equation `wrap(s(z))`, so every instance is a
    /// normal form distinct from `wrap(z)`.
    #[test]
    fn refutes_an_anywhere_pair_no_equation_reaches() {
        assert!(matches!(
            unify_anywhere("wrap{}(s{}(s{}(X:SortNat{})))", "wrap{}(z{}())"),
            UnificationResult::Bottom(UnificationFailure::DifferentSymbols(_))
        ));
    }

    /// A ground application no equation reaches is refuted by the scan.
    #[test]
    fn refutes_ground_anywhere_applications_no_equation_reaches() {
        assert!(matches!(
            unify_anywhere("wrap{}(s{}(s{}(z{}())))", "wrap{}(z{}())"),
            UnificationResult::Bottom(UnificationFailure::DifferentSymbols(_))
        ));
    }

    /// The ground `wrap(s(z))` is concrete after normalization but is the equation's redex, and
    /// equals `wrap(z)`: unification must not refute it, whether it arrives ground or is built
    /// by the unifier's own substitution (`X := s(z)` into `wrap(X)`).
    #[test]
    fn keeps_a_ground_anywhere_redex_an_equation() {
        let result = unify_anywhere("wrap{}(s{}(z{}()))", "wrap{}(z{}())");
        let UnificationResult::Unified(unified) = &result else {
            panic!("wrap(s(z)) equals wrap(z): {result:?}");
        };
        assert_eq!(unified.constraints.len(), 1, "{result:?}");

        let definition = anywhere_definition();
        let pairs = [
            (
                anywhere_term(&definition, "X:SortNat{}"),
                anywhere_term(&definition, "s{}(z{}())"),
            ),
            (
                anywhere_term(&definition, "wrap{}(X:SortNat{})"),
                anywhere_term(&definition, "wrap{}(z{}())"),
            ),
        ];
        let result = unify_term_pairs(&definition, Substitution::new(), pairs);
        let UnificationResult::Unified(unified) = &result else {
            panic!("X = s(z) and wrap(X) = wrap(z) are satisfiable: {result:?}");
        };
        assert_eq!(unified.constraints.len(), 1, "{result:?}");
    }

    /// Instance-normal applications of an equal `anywhere` head decompose into their arguments.
    #[test]
    fn decomposes_instance_normal_anywhere_applications() {
        let UnificationResult::Unified(result) = unify_anywhere(
            "pair{}(X:SortNat{}, s{}(s{}(Y:SortNat{})))",
            "pair{}(z{}(), s{}(s{}(z{}())))",
        ) else {
            panic!("pair has no equations and should decompose");
        };
        let definition = anywhere_definition();
        assert!(result.constraints.is_empty(), "{result:?}");
        assert_eq!(
            result.substitution[&Variable::new("X", Sort::simple("SortNat"))],
            anywhere_term(&definition, "z{}()")
        );
        assert_eq!(
            result.substitution[&Variable::new("Y", Sort::simple("SortNat"))],
            anywhere_term(&definition, "z{}()")
        );
        assert!(matches!(
            unify_anywhere(
                "pair{}(X:SortNat{}, z{}())",
                "pair{}(Y:SortNat{}, s{}(Y:SortNat{}))"
            ),
            UnificationResult::Bottom(UnificationFailure::DifferentSymbols(_))
        ));
    }

    /// A function argument is not instance-normal: `f(X)` may evaluate to `s(z)`, so neither
    /// `wrap(f(X))` nor `pair(f(X), z)` exposes its arguments to a clash.
    #[test]
    fn keeps_anywhere_pairs_over_function_arguments_as_equations() {
        for (left, right) in [
            ("wrap{}(f{}(X:SortNat{}))", "wrap{}(z{}())"),
            (
                "pair{}(f{}(X:SortNat{}), z{}())",
                "pair{}(z{}(), s{}(z{}()))",
            ),
        ] {
            let result = unify_anywhere(left, right);
            let UnificationResult::Unified(result) = &result else {
                panic!("{left} = {right} should stay an equation: {result:?}");
            };
            assert_eq!(result.constraints.len(), 1, "{result:?}");
        }
    }

    /// The declared `injective` on `wrap` is ignored: its equation matches the instance
    /// `X = s(z)`, so `wrap(X) = wrap(Y)` remains a constraint rather than `X = Y`.
    #[test]
    fn ignores_injective_on_an_anywhere_symbol() {
        let definition = anywhere_definition();
        let left = anywhere_term(&definition, "wrap{}(X:SortNat{})");
        let right = anywhere_term(&definition, "wrap{}(Y:SortNat{})");
        let UnificationResult::Unified(result) = unify_term_pairs(
            &definition,
            Substitution::new(),
            [(left.clone(), right.clone())],
        ) else {
            panic!("wrap(X) = wrap(Y) should stay an equation");
        };
        assert!(result.substitution.is_empty(), "{result:?}");
        assert_eq!(result.constraints, [Predicate::Equals(left, right)]);
    }

    #[test]
    fn keeps_constructor_pairs_unchanged_beside_anywhere_symbols() {
        assert!(matches!(
            unify_anywhere("s{}(X:SortNat{})", "z{}()"),
            UnificationResult::Bottom(UnificationFailure::DifferentSymbols(_))
        ));
        let UnificationResult::Unified(result) = unify_anywhere("s{}(X:SortNat{})", "s{}(z{}())")
        else {
            panic!("s(X) = s(z) should unify");
        };
        assert!(result.constraints.is_empty(), "{result:?}");
        assert_eq!(result.substitution.len(), 1, "{result:?}");
    }

    #[test]
    fn rejects_distinct_constructors() {
        let left = constructor("left", Vec::new());
        let right = constructor("right", Vec::new());

        let result = unify_term_pairs(
            &definition(),
            Substitution::new(),
            [(left.clone(), right.clone())],
        );
        let UnificationResult::Bottom(UnificationFailure::DifferentSymbols(clash)) = result else {
            panic!("two free constructors with different names clash: {result:?}");
        };
        assert_eq!(clash.into_terms(), (left, right));
    }

    /// Two applications of one symbol with different numbers of arguments are an ill-formed
    /// pair, not a clash of roots, for a free constructor and a function declared injective
    /// alike; the function has no root a clash could be built from.
    #[test]
    fn reports_an_arity_mismatch_of_one_symbol() {
        let injective = {
            let mut symbol = Symbol::constructor("inj", vec![sort()], sort());
            symbol.attributes = symbol
                .attributes
                .clone()
                .with_declared_function(true)
                .with_injective(true);
            symbol.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
            Arc::new(symbol)
        };
        let injective_application =
            |arguments| Term::application(injective.clone(), Vec::new(), arguments);
        for (left, right) in [
            (
                constructor("f", vec![var("X")]),
                constructor("f", vec![var("Y"), var("Z")]),
            ),
            (
                injective_application(vec![var("X")]),
                injective_application(vec![var("Y"), var("Z")]),
            ),
        ] {
            assert_eq!(
                unify_term_pairs(
                    &definition(),
                    Substitution::new(),
                    [(left.clone(), right.clone())]
                ),
                UnificationResult::Bottom(UnificationFailure::ArgumentLengthsDiffer(left, right))
            );
        }
    }

    /// `tag` is declared `constructor` and `anywhere`, `label` `constructor` and `macro`. An
    /// equation makes `tag(s(z))` equal `tag(z)` (a simplification, since an equation headed by
    /// a symbol declared constructor is otherwise rejected), and a macro application denotes a
    /// value the definition does not describe; neither symbol is free.
    fn unfree_constructor_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortNat{} []
                sort SortAddress{} []
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol tag{}(SortNat{}) : SortAddress{}
                    [constructor{}(), anywhere{}(), functional{}(), injective{}()]
                symbol label{}(SortNat{}) : SortAddress{}
                    [constructor{}(), functional{}(), injective{}(), macro{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(z{}())), \top{R}())
                    ),
                    \equals{SortAddress{}, R}(
                        tag{}(X0:SortNat{}),
                        \and{SortAddress{}}(tag{}(z{}()), \top{SortAddress{}}())
                    )
                ) [label{}("collapse"), anywhere{}(), simplification{}()]
            endmodule []"#,
        )
        .expect("unfree constructor definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn unify_unfree(left: &str, right: &str) -> UnificationResult {
        let definition = unfree_constructor_definition();
        let left = anywhere_term(&definition, left);
        let right = anywhere_term(&definition, right);
        unify_term_pairs(&definition, Substitution::new(), [(left, right)])
    }

    /// B1: a `constructor` symbol that also carries `anywhere` is an equation head, so
    /// `tag(s(z)) = tag(z)`, which its equation makes true, stays an equation instead of being
    /// decomposed into the clash `s(z) = z`.
    #[test]
    fn keeps_an_anywhere_constructor_pair_an_equation() {
        let result = unify_unfree("tag{}(s{}(z{}()))", "tag{}(z{}())");
        let UnificationResult::Unified(unified) = &result else {
            panic!("tag(s(z)) equals tag(z) by the anywhere equation: {result:?}");
        };
        assert!(unified.substitution.is_empty(), "{result:?}");
        assert_eq!(unified.constraints.len(), 1, "{result:?}");
    }

    /// B2: a constructor-typed macro is residual, so `label(s(z)) = label(z)` stays an equation
    /// instead of being decomposed into the clash `s(z) = z`.
    #[test]
    fn keeps_a_constructor_macro_pair_an_equation() {
        let result = unify_unfree("label{}(s{}(z{}()))", "label{}(z{}())");
        let UnificationResult::Unified(unified) = &result else {
            panic!("label is not free, so its applications are not refuted: {result:?}");
        };
        assert!(unified.substitution.is_empty(), "{result:?}");
        assert_eq!(unified.constraints.len(), 1, "{result:?}");
    }

    fn uninterpreted_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} []
                symbol a{}() : SortS{} [constructor{}(), functional{}(), injective{}()]
                symbol b{}() : SortS{} [constructor{}(), functional{}(), injective{}()]
                symbol c{}() : SortS{} [constructor{}(), functional{}(), injective{}()]
                symbol g{}(SortS{}, SortS{}) : SortS{} [functional{}()]
                axiom{R} \equals{SortS{}, R}(
                    g{}(X:SortS{}, Y:SortS{}), g{}(Y:SortS{}, X:SortS{})
                ) [comm{}()]
            endmodule []"#,
        )
        .expect("uninterpreted definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// Without injectivity, an equation between `g` applications does not imply an equation
    /// between their arguments, even when one argument pair consists of distinct constructors.
    #[test]
    fn keeps_an_uninterpreted_pair_without_an_argument_clash() {
        let definition = uninterpreted_definition();
        let left = anywhere_term(&definition, "g{}(a{}(), X:SortS{})");
        let right = anywhere_term(&definition, "g{}(g{}(a{}(), b{}()), c{}())");
        let result = unify_term_pairs(
            &definition,
            Substitution::new(),
            [(left.clone(), right.clone())],
        );
        let UnificationResult::Unified(unified) = result else {
            panic!("an uninterpreted root cannot justify an argument clash: {result:?}");
        };
        assert!(unified.substitution.is_empty());
        assert_eq!(unified.constraints, vec![Predicate::Equals(left, right)]);
    }

    #[test]
    fn an_identical_uninterpreted_pair_needs_no_constraint() {
        let definition = uninterpreted_definition();
        let term = anywhere_term(&definition, "g{}(a{}(), X:SortS{})");
        assert_eq!(
            unify_term_pairs(&definition, Substitution::new(), [(term.clone(), term)]),
            UnificationResult::Unified(Unification {
                substitution: Substitution::new(),
                constraints: Vec::new(),
            })
        );
    }

    /// An uninterpreted application may identify its argument with the whole application,
    /// so a variable occurrence through that root cannot certify a rigid cycle.
    #[test]
    fn keeps_an_uninterpreted_cycle_as_an_equation() {
        let definition = uninterpreted_definition();
        let left = anywhere_term(&definition, "X:SortS{}");
        let right = anywhere_term(&definition, "g{}(X:SortS{}, a{}())");
        let result = unify_term_pairs(
            &definition,
            Substitution::new(),
            [(left.clone(), right.clone())],
        );
        let UnificationResult::Unified(unified) = result else {
            panic!("an uninterpreted occurrence is not a rigid cycle: {result:?}");
        };
        assert!(unified.substitution.is_empty());
        assert_eq!(unified.constraints, vec![Predicate::Equals(left, right)]);
    }

    /// The step `Unifier::unify_one` took, after its variable and conjunction arms, at the
    /// integration base (`c11e4adb`): each arm as written there, with its `decomposable` and
    /// `rigid`, over the roles.
    fn transcribed_step(definition: &BackendDefinition, left: &Term, right: &Term) -> &'static str {
        let decomposable = |symbol: &Symbol| match symbol.attributes.head_role() {
            HeadRole::FreeConstructor => true,
            HeadRole::EquationHead => {
                definition.instance_normal(left).is_some()
                    && definition.instance_normal(right).is_some()
            }
            HeadRole::Function { injective, .. } => injective,
            HeadRole::Uninterpreted | HeadRole::Residual => false,
        };
        let rigid = |kind: &TermKind| match kind {
            TermKind::DomainValue { .. } | TermKind::Injection { .. } => true,
            TermKind::Application { symbol, .. } => {
                symbol.attributes.head_role() == HeadRole::FreeConstructor
            }
            _ => false,
        };
        let is_collection = |kind: &TermKind| {
            matches!(
                kind,
                TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. }
            )
        };
        match (left.kind(), right.kind()) {
            (TermKind::DomainValue { .. }, TermKind::DomainValue { .. }) => "domain values",
            (
                TermKind::Application {
                    symbol: left_symbol,
                    sort_arguments: left_sorts,
                    arguments: left_arguments,
                },
                TermKind::Application {
                    symbol: right_symbol,
                    sort_arguments: right_sorts,
                    arguments: right_arguments,
                },
            ) if left_symbol.name == right_symbol.name
                && left_sorts == right_sorts
                && decomposable(left_symbol) =>
            {
                // `DifferentSymbols` at the base; `ArgumentLengthsDiffer` since CBC-02-T4.
                if left_arguments.len() != right_arguments.len() {
                    "argument lengths differ"
                } else {
                    "decompose"
                }
            }
            (
                TermKind::Application {
                    symbol: left_symbol,
                    ..
                },
                TermKind::Application {
                    symbol: right_symbol,
                    ..
                },
            ) if left_symbol.attributes.head_role() == HeadRole::FreeConstructor
                && right_symbol.attributes.head_role() == HeadRole::FreeConstructor =>
            {
                "clash"
            }
            (TermKind::Injection { .. }, TermKind::Injection { .. }) => "injections",
            (left_kind, right_kind) if is_collection(left_kind) || is_collection(right_kind) => {
                "unsupported"
            }
            (left_kind, right_kind) if rigid(left_kind) && rigid(right_kind) => "clash",
            _ => "keep",
        }
    }

    /// The step the unifier takes now, by the same labels.
    fn policy_step(unifier: &Unifier<'_>, left: &Term, right: &Term) -> &'static str {
        match (left.kind(), right.kind()) {
            (TermKind::DomainValue { .. }, TermKind::DomainValue { .. }) => "domain values",
            (TermKind::Injection { .. }, TermKind::Injection { .. }) => "injections",
            _ => {
                let arguments = one_symbol(left, right);
                let (left_head, right_head) = unifier.classify(left, right, arguments.is_some());
                match unification_root_policy(left_head, right_head, arguments) {
                    UnifierStep::Decompose(_) => "decompose",
                    UnifierStep::ArgumentLengthsDiffer => "argument lengths differ",
                    UnifierStep::Refute(witness) => {
                        let clash = HeadClash::new(witness, left.clone(), right.clone());
                        assert_eq!(clash.into_terms(), (left.clone(), right.clone()));
                        "clash"
                    }
                    UnifierStep::Unsupported => "unsupported",
                    UnifierStep::Keep => "keep",
                }
            }
        }
    }

    /// Over the terms of the Lean bridge generators, the unifier's root policy takes the step
    /// the integration base took for every pair that reaches it, the arity mismatch of one
    /// symbol now reported as such. The generated symbols are not declared by the definition,
    /// so an equation-head application is instance-normal exactly when its arguments are.
    /// B4 exempts an uninterpreted root from the transcription and requires its equation to stay.
    #[test]
    fn the_root_policy_takes_the_steps_of_the_arms_it_replaced() {
        use std::{cell::RefCell, collections::BTreeMap};

        use proptest::{
            prelude::*,
            test_runner::{Config, TestRunner},
        };

        use crate::tests::lean_bridge::generators;

        let definition = anywhere_definition();
        let unifier = Unifier {
            definition: &definition,
            substitution: Substitution::new(),
            pending: VecDeque::new(),
            equations: Vec::new(),
            unsupported: Vec::new(),
        };
        let counts = RefCell::new(BTreeMap::<&'static str, usize>::new());
        let mut runner = TestRunner::new(Config {
            cases: 4096,
            ..Config::default()
        });
        runner
            .run(
                &(generators::term(), generators::term(), any::<bool>()),
                |(left, right, share)| {
                    // One symbol per name, as in a definition, and frequent pairs of one symbol.
                    let right = match (left.kind(), right.kind()) {
                        (
                            TermKind::Application { symbol, .. },
                            TermKind::Application {
                                symbol: other,
                                sort_arguments,
                                arguments,
                            },
                        ) if share || symbol.name == other.name => Term::application(
                            symbol.clone(),
                            sort_arguments.clone(),
                            arguments.clone(),
                        ),
                        _ => right,
                    };
                    // Pairs decided before the roots: equal or of different sorts, a
                    // conjunction or a variable on either side.
                    let before = |term: &Term| {
                        matches!(term.kind(), TermKind::Variable(_) | TermKind::And(..))
                    };
                    if left == right
                        || left.sort() != right.sort()
                        || before(&left)
                        || before(&right)
                    {
                        return Ok(());
                    }
                    let step = policy_step(&unifier, &left, &right);
                    let uninterpreted = |term: &Term| {
                        matches!(
                            term.kind(),
                            TermKind::Application { symbol, .. }
                                if symbol.attributes.head_role() == HeadRole::Uninterpreted
                        )
                    };
                    if uninterpreted(&left) || uninterpreted(&right) {
                        // B4: no axiom individuates an uninterpreted root, so it cannot
                        // justify decomposition or a clash against any other root.
                        prop_assert_eq!(step, "keep");
                    } else {
                        prop_assert_eq!(step, transcribed_step(&definition, &left, &right));
                    }
                    *counts.borrow_mut().entry(step).or_default() += 1;
                    Ok(())
                },
            )
            .unwrap();
        let counts = counts.into_inner();
        for step in [
            "decompose",
            "argument lengths differ",
            "clash",
            "unsupported",
            "keep",
        ] {
            assert!(counts.contains_key(step), "no case took {step}: {counts:?}");
        }
    }
}

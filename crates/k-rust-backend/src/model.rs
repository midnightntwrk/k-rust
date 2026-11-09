//! Model queries: a valuation of a predicate's free variables that satisfies it.
//!
//! The solver interprets the definition's defined symbols without the definition's equations
//! and without the freeness of its constructors, so a predicate those decide has an answer the
//! solver cannot see: `start = done` over two distinct constructors is false by the
//! definition, while the solver, reading both as uninterpreted constants, finds them equal in
//! some model of its approximate translation. A model query therefore decides the predicate with
//! the definition
//! first and asks the solver only for a valuation of the residual the simplifier left undecided.
//! [`model_of`] is that query, and [`ModelQuery`], the only argument
//! [`SmtSolver::get_model`] takes, is built by nothing else.

use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    simplify::{
        SimplificationError, SimplificationOptions, simplify_and_decide_predicate_with_solver,
    },
    smt::{ModelResult, SmtError, SmtSolver},
    stop::Stoppable,
    substitution::Substitution,
};

/// The residual of a model query: predicates the definition's simplifier left undecided, under
/// a substitution. Only [`model_of`] builds one, so a solver is asked for a model only after
/// the definition has decided what it can. Asking the solver directly does not compile:
///
/// ```compile_fail,E0061
/// # use k_rust_backend::{rule::Predicate, smt::SmtSolver, substitution::Substitution};
/// # fn ask(solver: &dyn SmtSolver, predicate: Predicate) {
/// let _ = solver.get_model(&[predicate], &Substitution::new());
/// # }
/// ```
///
/// and neither does building a query outside this module, whose fields are private:
///
/// ```compile_fail,E0451
/// # use k_rust_backend::{model::ModelQuery, rule::Predicate, smt::SmtSolver,
/// # substitution::Substitution};
/// # fn ask(solver: &dyn SmtSolver, predicate: Predicate) {
/// let _ = solver.get_model(&ModelQuery { predicates: &[predicate], substitution:
/// &Substitution::new() });
/// # }
/// ```
///
/// nor through the constructor solver tests use, which exists only in this crate's Z3 test build:
///
/// ```compile_fail,E0599
/// # use k_rust_backend::{model::ModelQuery, rule::Predicate, smt::SmtSolver,
/// # substitution::Substitution};
/// # fn ask(solver: &dyn SmtSolver, predicate: Predicate) {
/// let _ = solver.get_model(&ModelQuery::for_solver_tests(&[predicate], &Substitution::new()));
/// # }
/// ```
///
/// The query goes through [`model_of`], which decides the predicate with the definition first:
///
/// ```
/// # use k_rust_backend::{definition::BackendDefinition, model::model_of, rule::Predicate,
/// # smt::SmtSolver};
/// # fn ask(definition: &BackendDefinition, solver: &dyn SmtSolver, predicate: Predicate) {
/// let _ = model_of(definition, &predicate, solver);
/// # }
/// ```
#[derive(Clone, Copy, Debug)]
pub struct ModelQuery<'a> {
    predicates: &'a [Predicate],
    substitution: &'a Substitution,
}

impl<'a> ModelQuery<'a> {
    /// The undecided predicates a model must satisfy.
    #[must_use]
    pub const fn predicates(&self) -> &'a [Predicate] {
        self.predicates
    }

    /// The bindings a model must agree with.
    #[must_use]
    pub const fn substitution(&self) -> &'a Substitution {
        self.substitution
    }

    /// A query on solver inputs chosen by a test, to exercise a solver implementation directly.
    /// The Z3 solver's tests are its only callers.
    #[cfg(all(test, feature = "z3"))]
    pub(crate) const fn for_solver_tests(
        predicates: &'a [Predicate],
        substitution: &'a Substitution,
    ) -> Self {
        Self {
            predicates,
            substitution,
        }
    }
}

/// The failure of a model query. A stop is not a failure: [`model_of`] returns it on its outer
/// layer, as the simplifier and the solver do.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ModelError {
    /// The definition could not simplify the predicate.
    Simplification(SimplificationError),
    /// The solver could not answer the residual query.
    Solver(SmtError),
}

/// Answer a model query from the predicate's meaning: decide `predicate` with `definition`, and
/// ask `solver` only for a valuation of the residual the simplifier left undecided.
///
/// A predicate the definition decides false has no model. A predicate it decides true needs no
/// bindings, since every valuation satisfies it. Any other residual goes to the solver complete,
/// including the open `\ceil` obligations simplification introduced, since a model must also
/// make those terms defined.
///
/// The result has two layers: the outer `Err` is a [`Stop`](crate::stop::Stop), for which no
/// answer exists; the inner result is the answer or the query's failure.
pub fn model_of(
    definition: &BackendDefinition,
    predicate: &Predicate,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<ModelResult, ModelError>> {
    let simplified = match simplify_and_decide_predicate_with_solver(
        definition,
        predicate,
        &[],
        SimplificationOptions::unbounded(),
        solver,
    )? {
        Ok(simplified) => simplified,
        Err(error) => return Ok(Err(ModelError::Simplification(error))),
    };
    match simplified {
        Predicate::False => Ok(Ok(ModelResult::Unsat)),
        Predicate::True => Ok(Ok(ModelResult::Sat(Substitution::new()))),
        residual => {
            let predicates = [residual];
            let substitution = Substitution::new();
            let query = ModelQuery {
                predicates: &predicates,
                substitution: &substitution,
            };
            Ok(solver.get_model(&query)?.map_err(ModelError::Solver))
        }
    }
}

#[cfg(all(test, feature = "z3"))]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::{smt::Z3Solver, stop::Stop};

    const MODEL_DEFINITION: &str = r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            sort SortState{} []
            symbol start{}() : SortState{} [constructor{}()]
            symbol done{}() : SortState{} [constructor{}()]
            symbol bitwise{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), smtlib{}("bitwise")]
            symbol partial{}(SortInt{}) : SortInt{} [function{}()]
        endmodule []"#;

    fn model(source: &str) -> ModelResult {
        let syntax = parse_definition(MODEL_DEFINITION).expect("model definition should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("model definition should internalize");
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let pattern = parse_pattern(source).expect("model predicate should parse");
        let (predicate, _) = definition
            .verify_standalone_pattern(&pattern, &[])
            .expect("model predicate should verify")
            .internalize_model_predicate()
            .expect("model predicate should internalize")
            .expect("model predicate should have a predicate");
        model_of(&definition, &predicate, &solver)
            .map_err(Stop::into_cause)
            .expect("model query should not stop")
            .expect("model query should succeed")
    }

    #[test]
    fn reflexive_configuration_has_an_empty_sat_model() {
        assert_eq!(
            model(r"\equals{SortState{}, SortBool{}}(start{}(), start{}())"),
            ModelResult::Sat(Substitution::new())
        );
    }

    #[test]
    fn distinct_constructor_configurations_have_no_model() {
        assert_eq!(
            model(r"\equals{SortState{}, SortBool{}}(start{}(), done{}())"),
            ModelResult::Unsat
        );
    }

    #[test]
    fn uninterpreted_residual_has_no_certified_model() {
        assert!(matches!(
            model(
                r#"\equals{SortInt{}, SortBool{}}(
                    bitwise{}(X:SortInt{}, \dv{SortInt{}}("1")),
                    \dv{SortInt{}}("2"))"#
            ),
            ModelResult::Unknown(_)
        ));
    }

    #[test]
    fn an_open_definedness_obligation_remains_in_the_model_query() {
        assert!(matches!(
            model(
                r"\and{SortBool{}}(
                    \equals{SortState{}, SortBool{}}(start{}(), start{}()),
                    \ceil{SortInt{}, SortBool{}}(partial{}(X:SortInt{})))"
            ),
            ModelResult::Unknown(_)
        ));
    }
}

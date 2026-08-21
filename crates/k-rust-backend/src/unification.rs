//! Symmetric first-order unification for symbolic KORE terms.
//!
//! Collection and hook-specific theories remain separate because they may produce more than one
//! solution. This procedure handles the common syntactic theory, saturates bindings in both
//! orientations, and retains irreducible functional equations as predicates.

use std::collections::VecDeque;

use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    substitution::{Substitution, compose, substitute},
    term::{SymbolType, Term, TermKind, Variable},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Unification {
    pub substitution: Substitution,
    pub constraints: Vec<Predicate>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnificationResult {
    Unified(Unification),
    Bottom(UnificationFailure),
    Unsupported {
        substitution: Substitution,
        constraints: Vec<Predicate>,
        remainder: Vec<(Term, Term)>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnificationFailure {
    DifferentSorts(Term, Term),
    DifferentValues(Term, Term),
    DifferentSymbols(Term, Term),
    VariableRecursion(Variable, Term),
}

/// Unify all `pairs` under an existing partial substitution.
///
/// Bindings are symmetric: variables from either side may be solved. Rigid constructors and sort
/// injections are decomposed, while opaque function equations are retained as constraints. AC
/// collections are returned as unsupported so their dedicated multi-solution solvers can run.
pub fn unify_term_pairs(
    definition: &BackendDefinition,
    initial: Substitution,
    pairs: impl IntoIterator<Item = (Term, Term)>,
) -> UnificationResult {
    let mut unifier = Unifier {
        definition,
        substitution: initial,
        pending: pairs.into_iter().collect(),
        constraints: Vec::new(),
        unsupported: Vec::new(),
    };
    if let Err(failure) = unifier.run() {
        return UnificationResult::Bottom(failure);
    }
    let constraints = unifier
        .constraints
        .into_iter()
        .map(|predicate| substitute_predicate(predicate, &unifier.substitution))
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
    constraints: Vec<Predicate>,
    unsupported: Vec<(Term, Term)>,
}

impl Unifier<'_> {
    fn run(&mut self) -> Result<(), UnificationFailure> {
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
                && (left_symbol.attributes.injective
                    || left_symbol.attributes.symbol_type == SymbolType::Constructor) =>
            {
                if left_arguments.len() != right_arguments.len() {
                    return Err(UnificationFailure::DifferentSymbols(left, right));
                }
                self.pending.extend(
                    left_arguments
                        .iter()
                        .cloned()
                        .zip(right_arguments.iter().cloned()),
                );
                Ok(())
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
            ) if left_symbol.attributes.symbol_type == SymbolType::Constructor
                && right_symbol.attributes.symbol_type == SymbolType::Constructor =>
            {
                Err(UnificationFailure::DifferentSymbols(left, right))
            }
            (
                TermKind::Injection {
                    source: left_source,
                    target: left_target,
                    term: left_term,
                },
                TermKind::Injection {
                    source: right_source,
                    target: right_target,
                    term: right_term,
                },
            ) => {
                if left_target != right_target {
                    return Err(UnificationFailure::DifferentSorts(left, right));
                }
                if left_source == right_source {
                    self.pending
                        .push_back((left_term.clone(), right_term.clone()));
                    return Ok(());
                }
                if self
                    .definition
                    .sort_graph
                    .check_subsort(left_source, right_source)
                    .unwrap_or(false)
                {
                    self.pending.push_back((
                        Term::injection(
                            left_source.clone(),
                            right_source.clone(),
                            left_term.clone(),
                        ),
                        right_term.clone(),
                    ));
                    return Ok(());
                }
                if self
                    .definition
                    .sort_graph
                    .check_subsort(right_source, left_source)
                    .unwrap_or(false)
                {
                    self.pending.push_back((
                        left_term.clone(),
                        Term::injection(
                            right_source.clone(),
                            left_source.clone(),
                            right_term.clone(),
                        ),
                    ));
                    return Ok(());
                }
                Err(UnificationFailure::DifferentSorts(left, right))
            }
            (left_kind, right_kind) if is_collection(left_kind) || is_collection(right_kind) => {
                self.unsupported.push((left, right));
                Ok(())
            }
            (left_kind, right_kind) if rigid(left_kind) && rigid(right_kind) => {
                Err(UnificationFailure::DifferentSymbols(left, right))
            }
            _ => {
                self.constraints.push(Predicate::Equals(left, right));
                Ok(())
            }
        }
    }

    fn bind(&mut self, variable: Variable, term: Term) -> Result<(), UnificationFailure> {
        let term = substitute(&term, &self.substitution);
        if term.attributes().variables.contains(&variable) {
            return Err(UnificationFailure::VariableRecursion(variable, term));
        }
        let binding = Substitution::from([(variable, term)]);
        self.substitution = compose(&binding, &self.substitution);
        Ok(())
    }
}

fn is_collection(kind: &TermKind) -> bool {
    matches!(
        kind,
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. }
    )
}

fn rigid(kind: &TermKind) -> bool {
    match kind {
        TermKind::DomainValue { .. } | TermKind::Injection { .. } => true,
        TermKind::Application { symbol, .. } => {
            symbol.attributes.symbol_type == SymbolType::Constructor
        }
        TermKind::And(..)
        | TermKind::Variable(_)
        | TermKind::Map { .. }
        | TermKind::List { .. }
        | TermKind::Set { .. } => false,
    }
}

fn substitute_predicate(predicate: Predicate, substitution: &Substitution) -> Predicate {
    match predicate {
        Predicate::Equals(left, right) => Predicate::Equals(
            substitute(&left, substitution),
            substitute(&right, substitution),
        ),
        predicate => predicate,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use k_rust_kore::kore::parser::parse_definition;

    use crate::term::{FunctionType, Sort, Symbol};

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
            UnificationResult::Bottom(UnificationFailure::VariableRecursion(variable, _))
                if variable.name.as_ref() == "X"
        ));
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
            UnificationResult::Bottom(UnificationFailure::DifferentSymbols(_, _))
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
    fn rejects_distinct_constructors() {
        let left = constructor("left", Vec::new());
        let right = constructor("right", Vec::new());

        assert!(matches!(
            unify_term_pairs(&definition(), Substitution::new(), [(left, right)]),
            UnificationResult::Bottom(UnificationFailure::DifferentSymbols(_, _))
        ));
    }
}

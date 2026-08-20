//! Saturating substitutions over immutable backend terms.

use std::collections::BTreeMap;

use crate::term::{Term, TermKind, Variable};

pub type Substitution = BTreeMap<Variable, Term>;

pub fn substitute(term: &Term, substitution: &Substitution) -> Term {
    if term
        .attributes()
        .variables
        .iter()
        .all(|variable| !substitution.contains_key(variable))
    {
        return term.clone();
    }

    match term.kind() {
        TermKind::And(left, right) => Term::and(
            substitute(left, substitution),
            substitute(right, substitution),
        ),
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => Term::application(
            symbol.clone(),
            sort_arguments.clone(),
            arguments
                .iter()
                .map(|argument| substitute(argument, substitution))
                .collect(),
        ),
        TermKind::DomainValue { .. } => term.clone(),
        TermKind::Variable(variable) => substitution
            .get(variable)
            .cloned()
            .unwrap_or_else(|| term.clone()),
        TermKind::Injection {
            source,
            target,
            term,
        } => Term::injection(
            source.clone(),
            target.clone(),
            substitute(term, substitution),
        ),
        TermKind::Map {
            definition,
            entries,
            rest,
        } => Term::map(
            definition.clone(),
            entries
                .iter()
                .map(|(key, value)| {
                    (
                        substitute(key, substitution),
                        substitute(value, substitution),
                    )
                })
                .collect(),
            rest.as_ref().map(|term| substitute(term, substitution)),
        ),
        TermKind::List {
            definition,
            heads,
            rest,
        } => Term::list(
            definition.clone(),
            heads
                .iter()
                .map(|term| substitute(term, substitution))
                .collect(),
            rest.as_ref().map(|(middle, tails)| {
                (
                    substitute(middle, substitution),
                    tails
                        .iter()
                        .map(|term| substitute(term, substitution))
                        .collect(),
                )
            }),
        ),
        TermKind::Set {
            definition,
            elements,
            rest,
        } => Term::set(
            definition.clone(),
            elements
                .iter()
                .map(|term| substitute(term, substitution))
                .collect(),
            rest.as_ref().map(|term| substitute(term, substitution)),
        ),
    }
}

/// Compose substitutions so new bindings take priority and saturate old values.
pub fn compose(new: &Substitution, old: &Substitution) -> Substitution {
    let mut result = old
        .iter()
        .map(|(variable, term)| (variable.clone(), substitute(term, new)))
        .collect::<Substitution>();
    result.extend(new.clone());
    result
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::term::{Sort, Symbol};

    use super::*;

    fn sort() -> Sort {
        Sort::simple("SomeSort")
    }

    fn variable(name: &str) -> Variable {
        Variable::new(name, sort())
    }

    fn var(name: &str) -> Term {
        Term::variable(variable(name))
    }

    fn con1(argument: Term) -> Term {
        Term::application(
            Arc::new(Symbol::constructor("con1", vec![sort()], sort())),
            Vec::new(),
            vec![argument],
        )
    }

    #[test]
    fn substitutes_through_applications_and_conjunctions() {
        let substitution = Substitution::from([(variable("X"), con1(var("Y")))]);
        assert_eq!(
            substitute(&con1(var("X")), &substitution),
            con1(con1(var("Y")))
        );
        assert_eq!(
            substitute(&Term::and(con1(var("X")), con1(var("Y"))), &substitution),
            Term::and(con1(con1(var("Y"))), con1(var("Y")))
        );
    }

    #[test]
    fn composition_is_idempotent() {
        let substitution = Substitution::from([(variable("X"), con1(var("Y")))]);
        assert_eq!(compose(&substitution, &substitution), substitution);
    }

    #[test]
    fn composition_is_transitive_and_saturating() {
        let new = Substitution::from([(variable("X"), var("Z"))]);
        let old = Substitution::from([(variable("Y"), var("X"))]);
        assert_eq!(
            compose(&new, &old),
            Substitution::from([(variable("X"), var("Z")), (variable("Y"), var("Z")),])
        );
    }
}

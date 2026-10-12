//! The reads of a term's `variables` attribute that a dependent crate makes through the public
//! API, written as that crate writes them: a test against an owned set of variables by
//! `is_subset` and `is_disjoint`, emptiness, and iteration by reference. They compile against
//! [`Variables`](k_rust_backend::term::Variables) without naming it, so a change of the
//! attribute's type that breaks one of them breaks this file first.

use std::collections::BTreeSet;

use k_rust_backend::{
    substitution::Substitution,
    term::{Sort, Term, Variable, VariableKind},
};

fn sort(name: &str) -> Sort {
    Sort::Application {
        name: name.into(),
        arguments: Vec::new(),
    }
}

fn variable(name: &str) -> Variable {
    Variable::new(name, sort("SortInt"))
}

/// `X /\ Y`: a term with the variables `X` and `Y`.
fn two_variables() -> Term {
    Term::and(Term::variable(variable("X")), Term::variable(variable("Y")))
}

/// Whether every variable of `term` is in `stable`, or, with no `stable` set, whether `term` is
/// ground.
fn within(term: &Term, stable: Option<&BTreeSet<Variable>>) -> bool {
    let variables = &term.attributes().variables;
    match stable {
        Some(stable) => variables.is_subset(stable),
        None => variables.is_empty(),
    }
}

#[test]
fn a_term_s_variables_are_tested_against_an_owned_set() {
    let term = two_variables();
    let ground = Term::domain_value(sort("SortInt"), "1");

    let both = BTreeSet::from([variable("X"), variable("Y"), variable("Z")]);
    let one = BTreeSet::from([variable("X")]);
    assert!(within(&term, Some(&both)));
    assert!(!within(&term, Some(&one)));
    assert!(!within(&term, None));
    assert!(within(&ground, None));
    assert!(within(&ground, Some(&BTreeSet::new())));

    let bound = BTreeSet::from([variable("Z")]);
    assert!(term.attributes().variables.is_disjoint(&bound));
    assert!(!term.attributes().variables.is_disjoint(&one));
    // The larger operand on either side.
    assert!(!term.attributes().variables.is_disjoint(&both));
}

#[test]
fn a_term_s_variables_are_iterated_by_reference_in_order() {
    let term = two_variables();

    let names = term
        .attributes()
        .variables
        .iter()
        .cloned()
        .chain([variable("Z")])
        .map(|variable| variable.name.to_string())
        .collect::<Vec<_>>();
    assert_eq!(names, ["X", "Y", "Z"]);

    let identities = term
        .attributes()
        .variables
        .iter()
        .map(|variable| (variable.name.to_string(), variable.kind))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        identities,
        BTreeSet::from([
            ("X".to_owned(), VariableKind::Element),
            ("Y".to_owned(), VariableKind::Element),
        ])
    );
}

#[test]
fn a_term_s_variables_are_tested_against_another_term_s_and_a_substitution_s_domain() {
    let term = two_variables();
    let x = Term::variable(variable("X"));
    let z = Term::variable(variable("Z"));
    let variables = &term.attributes().variables;

    assert!(x.attributes().variables.is_subset(variables));
    assert!(!variables.is_subset(&x.attributes().variables));
    assert!(z.attributes().variables.is_disjoint(variables));
    assert!(variables.contains(&variable("Y")));
    assert_eq!(variables.len(), 2);
    assert_eq!(
        variables.union(&z.attributes().variables).to_btree_set(),
        BTreeSet::from([variable("X"), variable("Y"), variable("Z")])
    );

    let substitution = Substitution::from([(variable("Z"), x.clone())]);
    assert!(variables.is_disjoint(&substitution));
    assert!(!z.attributes().variables.is_disjoint(&substitution));
    assert!(z.attributes().variables.is_subset(&substitution));
}

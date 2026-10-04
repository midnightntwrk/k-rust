//! Capture avoidance at binders.
//!
//! A binder shadows its name only for its own body: a value substituted under it, or a fact
//! about the free variable of the same name, must not be read as a statement about the bound
//! one. These tests use ordinary spellings: the defects they pin are independent of naming.

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::BackendDefinition,
    implication::{ImplicationStatus, check_implication_with_existentials_complete},
    rewrite::{Pattern, substitute_predicates},
    rule::Predicate,
    simplify::{SimplificationOptions, simplify_predicates_with_solver},
    smt::{NoSolver, SmtSolver},
    substitution::Substitution,
    term::{Sort, Term, TermKind, Variable},
};

fn two_values() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
        module MAIN
            sort SortK{} []
            symbol a{}() : SortK{} [constructor{}(), functional{}()]
            symbol b{}() : SortK{} [constructor{}(), functional{}()]
            axiom{} \or{SortK{}}(a{}(), b{}(), \bottom{SortK{}}()) [constructor{}()]
        endmodule []"#,
    )
    .expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn k(name: &str) -> Variable {
    Variable::new(name, Sort::simple("SortK"))
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).unwrap(), &[])
        .expect("term should internalize")
}

/// `\exists W. W = a /\ \not(W = X)` with the binder named `binder`.
fn other_than(definition: &BackendDefinition, binder: &str, free: &str) -> Predicate {
    let bound = k(binder);
    Predicate::Exists(
        bound.clone(),
        Box::new(Predicate::And(vec![
            Predicate::Equals(Term::variable(bound.clone()), term(definition, "a{}()")),
            Predicate::Not(Box::new(Predicate::Equals(
                Term::variable(bound),
                Term::variable(k(free)),
            ))),
        ])),
    )
}

/// Substituting `X := W` into `\exists W. ... X ...` renames the binder: the substituted `W`
/// stays free, and the result is alpha-equivalent to substituting under a binder named `V`.
#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "the test exercises substitution itself, with values that are variables or constructors"
)]
fn substitution_renames_a_binder_that_would_capture_the_value() {
    let definition = two_values();
    let predicate = other_than(&definition, "W", "X");
    let substitution = Substitution::from([(k("X"), Term::variable(k("W")))]);
    let [substituted] = substitute_predicates(std::slice::from_ref(&predicate), &substitution)
        .try_into()
        .expect("one predicate");
    assert!(
        substituted.free_variables().contains(&k("W")),
        "the substituted W was captured: {substituted:?}"
    );
    let Predicate::Exists(binder, _) = &substituted else {
        panic!("the quantifier stays: {substituted:?}");
    };
    assert_ne!(binder, &k("W"));
    // Without a clash the binder keeps its name.
    let untouched = substitute_predicates(
        std::slice::from_ref(&predicate),
        &Substitution::from([(k("X"), term(&definition, "b{}()"))]),
    );
    let Predicate::Exists(binder, _) = &untouched[0] else {
        panic!("the quantifier stays: {untouched:?}");
    };
    assert_eq!(binder, &k("W"));
}

/// A fact about the free `X` is not a fact about a bound `X`: `X = a` does not make
/// `\exists X. \not(X = a)` (true over `{a, b}`) false.
#[test]
fn a_known_fact_is_not_used_under_a_binder_of_its_variable() {
    let definition = two_values();
    let a = term(&definition, "a{}()");
    let known = Predicate::Equals(Term::variable(k("X")), a.clone());
    let shadowing = Predicate::Exists(
        k("X"),
        Box::new(Predicate::Not(Box::new(Predicate::Equals(
            Term::variable(k("X")),
            a.clone(),
        )))),
    );
    let simplified = simplify_predicates_with_solver(
        &definition,
        std::slice::from_ref(&shadowing),
        std::slice::from_ref(&known),
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("no stop")
    .expect("the predicate should simplify");
    assert_ne!(simplified, vec![Predicate::False], "{simplified:?}");
    // The same fact about a free variable of another name is still used.
    let other = Predicate::Exists(
        k("Y"),
        Box::new(Predicate::Equals(Term::variable(k("X")), a)),
    );
    let simplified = simplify_predicates_with_solver(
        &definition,
        std::slice::from_ref(&other),
        std::slice::from_ref(&known),
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("no stop")
    .expect("the predicate should simplify");
    assert!(
        simplified
            .iter()
            .all(|predicate| *predicate == Predicate::True),
        "{simplified:?}"
    );
}

/// Only the facts that mention the shadowed variable are set aside under its binder: with the
/// facts `X = a` and `Z = b`, `\exists X. Z = b` is still `\top`.
#[test]
fn a_shadowing_binder_keeps_the_facts_about_other_variables() {
    let definition = two_values();
    let known = [
        Predicate::Equals(Term::variable(k("X")), term(&definition, "a{}()")),
        Predicate::Equals(Term::variable(k("Z")), term(&definition, "b{}()")),
    ];
    let shadowing = Predicate::Exists(
        k("X"),
        Box::new(Predicate::Equals(
            Term::variable(k("Z")),
            term(&definition, "b{}()"),
        )),
    );
    let simplified = simplify_predicates_with_solver(
        &definition,
        std::slice::from_ref(&shadowing),
        &known,
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("no stop")
    .expect("the predicate should simplify");
    assert!(
        simplified
            .iter()
            .all(|predicate| *predicate == Predicate::True),
        "{simplified:?}"
    );
}

/// Implication instance: `W => \exists X. X /\ \not(\exists W. W = a /\ \not(W = X))`
/// is `W => X = a`, false for `W = b`. The match binds `X := W`, and substituting it under the
/// consequent's `\exists W` must not capture it. Every binder spelling answers as `V`.
#[test]
fn an_implication_binder_named_like_an_antecedent_variable_captures_nothing() {
    fn status(
        binder: &str,
        solver: &dyn SmtSolver,
        definition: &BackendDefinition,
    ) -> ImplicationStatus {
        let consequent = format!(
            r#"\exists{{SortK{{}}}}(X:SortK{{}}, \and{{SortK{{}}}}(X:SortK{{}},
                \not{{SortK{{}}}}(\exists{{SortK{{}}}}({binder}:SortK{{}},
                    \and{{SortK{{}}}}(\equals{{SortK{{}}, SortK{{}}}}({binder}:SortK{{}}, a{{}}()),
                        \not{{SortK{{}}}}(\equals{{SortK{{}}, SortK{{}}}}({binder}:SortK{{}}, X:SortK{{}})))))))"#
        );
        let (antecedent, antecedent_existentials) = definition
            .internalize_implication_pattern(&parse_pattern("W:SortK{}").unwrap(), &[])
            .unwrap();
        let (consequent, consequent_existentials) = definition
            .internalize_implication_pattern(&parse_pattern(&consequent).unwrap(), &[])
            .unwrap();
        check_implication_with_existentials_complete(
            definition,
            &antecedent,
            &antecedent_existentials,
            &consequent,
            &consequent_existentials,
            solver,
        )
        .expect("no stop")
        .expect("the implication should be checked")
        .status()
    }
    let definition = two_values();
    let control = status("V", &NoSolver, &definition);
    assert_ne!(control, ImplicationStatus::Valid);
    assert_eq!(status("W", &NoSolver, &definition), control);
    #[cfg(feature = "z3")]
    {
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");
        let control = status("V", &solver, &definition);
        assert_ne!(control, ImplicationStatus::Valid);
        assert_eq!(status("W", &solver, &definition), control);
    }
}

/// The substitution a proof applies to a claim renames a binder of the claim that would
/// capture a subject variable (the claim-level form of
/// `substitution_renames_a_binder_that_would_capture_the_value`).
#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "the test exercises substitution itself, with values that are variables or constructors"
)]
fn a_pattern_substitution_keeps_the_subject_variable_free() {
    let definition = two_values();
    let pattern = Pattern {
        term: term(&definition, "X:SortK{}"),
        constraints: vec![Predicate::Not(Box::new(other_than(&definition, "X", "Y")))],
    };
    let substitution = Substitution::from([(k("Y"), Term::variable(k("X")))]);
    let constraints = substitute_predicates(&pattern.constraints, &substitution);
    let free = constraints
        .iter()
        .flat_map(Predicate::free_variables)
        .collect::<Vec<_>>();
    assert!(
        free.contains(&k("X")),
        "the subject's X was captured: {constraints:?}"
    );
    let Predicate::Not(inner) = &constraints[0] else {
        panic!("{constraints:?}");
    };
    let Predicate::Exists(binder, _) = inner.as_ref() else {
        panic!("{constraints:?}");
    };
    assert!(
        matches!(Term::variable(binder.clone()).kind(), TermKind::Variable(v) if v.name.as_ref() != "X"),
        "{constraints:?}"
    );
}

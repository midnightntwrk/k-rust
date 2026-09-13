//! Crate-internal contracts of `crate::rewrite` (`pub(crate)` entry points).

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::BackendDefinition,
    rewrite::*,
    rule::Predicate,
    simplify::SimplificationOptions,
    smt::NoSolver,
    term::{Sort, Term, Variable},
};

fn existential_equality(bound: &str, free: &str) -> Predicate {
    let sort = Sort::simple("SortS");
    let bound = Variable::new(bound, sort.clone());
    Predicate::Exists(
        bound.clone(),
        Box::new(Predicate::Equals(
            Term::variable(bound),
            Term::variable(Variable::new(free, sort)),
        )),
    )
}

#[test]
fn recognizes_alpha_equivalent_applicability_exclusions() {
    let excluded = Predicate::Not(Box::new(existential_equality("Fresh!0", "State")));
    let retried = Predicate::Not(Box::new(existential_equality("Fresh!1", "State")));
    let different_free_variable =
        Predicate::Not(Box::new(existential_equality("Fresh!1", "Other")));

    assert!(conjunctively_contains_alpha_equivalent(
        &[Predicate::And(vec![Predicate::True, excluded])],
        &retried,
    ));
    assert!(!conjunctively_contains_alpha_equivalent(
        &[different_free_variable],
        &retried,
    ));
}

fn definition(axioms: &str) -> BackendDefinition {
    let source = format!(
        r#"[]
            module MAIN
                sort SortS{{}} [hasDomainValues{{}}()]
                symbol wrap{{}}(SortS{{}}) : SortS{{}}
                    [function{{}}(), total{{}}(), injective{{}}(), no-evaluators{{}}()]
                symbol injectiveFunction{{}}(SortS{{}}) : SortS{{}}
                    [function{{}}(), total{{}}(), injective{{}}()]
                {axioms}
            endmodule []"#
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

#[test]
fn rejects_exclusions_covering_a_finite_constructor_sort() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortS{} []
                symbol a{}() : SortS{} [constructor{}()]
                symbol b{}() : SortS{} [constructor{}()]
                symbol c{}() : SortS{} [constructor{}()]
                axiom{} \or{SortS{}}(
                    a{}(),
                    \or{SortS{}}(b{}(), c{}(), \bottom{SortS{}}())
                ) [constructor{}()]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let variable = Term::variable(Variable::new("X", Sort::simple("SortS")));
    let excluded = ["a", "b", "c"]
        .into_iter()
        .map(|name| {
            let constructor = definition
                .internalize_term(&parse_pattern(&format!("{name}{{}}()")).unwrap(), &[])
                .unwrap();
            Predicate::Not(Box::new(Predicate::Equals(variable.clone(), constructor)))
        })
        .collect::<Vec<_>>();

    assert!(!violates_finite_constructor_domain(
        &definition,
        &excluded[..2]
    ));
    assert!(violates_finite_constructor_domain(&definition, &excluded));
}

#[test]
fn rejects_exclusions_covering_parameterized_constructor_families() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortElement{} []
                sort SortList{} []
                symbol nil{}() : SortList{} [constructor{}()]
                symbol cons{}(SortElement{}, SortList{}) : SortList{} [constructor{}()]
                symbol unknown{}() : SortList{} [function{}(), total{}()]
                axiom{} \or{SortList{}}(
                    nil{}(),
                    \exists{SortList{}}(
                        E:SortElement{},
                        \exists{SortList{}}(
                            T:SortList{},
                            cons{}(E:SortElement{}, T:SortList{})
                        )
                    ),
                    \bottom{SortList{}}()
                ) [constructor{}()]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let list = Term::variable(Variable::new("L", Sort::simple("SortList")));
    let nil = internal_term(&definition, "nil{}()");
    let element = Variable::new("E0", Sort::simple("SortElement"));
    let tail = Variable::new("T1", Sort::simple("SortList"));
    let cons = internal_term(&definition, "cons{}(E0:SortElement{}, T1:SortList{})");
    let excludes_nil = Predicate::Not(Box::new(Predicate::Equals(list.clone(), nil)));
    let excludes_every_cons = Predicate::Not(Box::new(Predicate::Exists(
        element,
        Box::new(Predicate::Exists(
            tail,
            Box::new(Predicate::Equals(list.clone(), cons.clone())),
        )),
    )));
    let excludes_one_cons = Predicate::Not(Box::new(Predicate::Equals(list, cons)));

    assert!(!violates_finite_constructor_domain(
        &definition,
        &[excludes_nil.clone(), excludes_one_cons],
    ));
    assert!(violates_finite_constructor_domain(
        &definition,
        &[excludes_nil, excludes_every_cons],
    ));

    let unknown = internal_term(&definition, "unknown{}()");
    let nil = internal_term(&definition, "nil{}()");
    let element = Variable::new("E2", Sort::simple("SortElement"));
    let tail = Variable::new("T3", Sort::simple("SortList"));
    let cons = internal_term(&definition, "cons{}(E2:SortElement{}, T3:SortList{})");
    assert!(violates_finite_constructor_domain(
        &definition,
        &[
            Predicate::Not(Box::new(Predicate::Equals(unknown.clone(), nil))),
            Predicate::Not(Box::new(Predicate::Exists(
                element,
                Box::new(Predicate::Exists(
                    tail,
                    Box::new(Predicate::Equals(unknown, cons)),
                )),
            ))),
        ],
    ));
}

fn internal_term(definition: &BackendDefinition, source: &str) -> Term {
    let syntax = parse_pattern(source).expect("term should parse");
    definition
        .internalize_term(&syntax, &[])
        .expect("term should internalize")
}

#[test]
fn rhs_disjunction_branches_in_all_and_any_modes() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(\dv{SortS{}}("start")),
                    \top{SortS{}}()
                ),
                \or{SortS{}}(
                    wrap{}(\dv{SortS{}}("left")),
                    wrap{}(\dv{SortS{}}("right"))
                )
            ) [label{}("split-rhs")]
            "#,
    );
    let subject = Pattern {
        term: internal_term(&definition, r#"wrap{}(\dv{SortS{}}("start"))"#),
        constraints: Vec::new(),
    };

    for mode in [ExecutionMode::All, ExecutionMode::Any] {
        let mut fresh = 0;
        let result = rewrite_step_with_mode(
            &definition,
            &subject,
            &mut fresh,
            SimplificationOptions::default(),
            &NoSolver,
            mode,
            false,
        );
        let RewriteResult::Branch { branches, .. } = result else {
            panic!("RHS disjunction should branch in {mode:?}: {result:?}");
        };
        assert_eq!(branches.len(), 2);
        let rendered = branches
            .iter()
            .map(|branch| crate::externalize::constrained_pattern(&branch.pattern).to_string())
            .collect::<Vec<_>>();
        assert!(rendered.iter().any(|pattern| pattern.contains("left")));
        assert!(rendered.iter().any(|pattern| pattern.contains("right")));
    }
}

#[cfg(feature = "z3")]
#[test]
fn requires_definedness_unless_the_configuration_is_assumed_defined() {
    let definition = definition(
        r#"
            symbol partial{}(SortS{}) : SortS{} [function{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("variable-match")]
            "#,
    );
    let function = internal_term(&definition, r#"partial{}(\dv{SortS{}}("value"))"#);
    let subject = Pattern {
        term: internal_term(&definition, r#"wrap{}(partial{}(\dv{SortS{}}("value")))"#),
        constraints: Vec::new(),
    };
    let solver = crate::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("partial-function binding should retain applied and undefined branches");
    };
    let [branch] = branches.as_slice() else {
        panic!("expected one conditionally defined match, found {branches:?}");
    };
    assert_eq!(
        branch.pattern.term,
        internal_term(&definition, r#"\dv{SortS{}}("done")"#)
    );
    assert_eq!(
        branch.pattern.constraints,
        [Predicate::Ceil(function.clone())]
    );
    assert_eq!(
        remainder.pattern.constraints,
        [Predicate::Not(Box::new(Predicate::Ceil(function.clone())))]
    );
    assert_eq!(
        branch.substitution.values().collect::<Vec<_>>(),
        [&function]
    );

    let mut fresh = 0;
    let RewriteResult::Finished(assumed_defined) = rewrite_step_with_mode(
        &definition,
        &subject,
        &mut fresh,
        SimplificationOptions::default(),
        &solver,
        ExecutionMode::All,
        true,
    ) else {
        panic!("the defined configuration should rewrite without a side branch");
    };
    assert_eq!(
        assumed_defined.pattern.term,
        internal_term(&definition, r#"\dv{SortS{}}("done")"#)
    );
    assert!(assumed_defined.pattern.constraints.is_empty());
}

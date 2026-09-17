//! Public contracts of `k_rust_backend::simplify`.

use k_rust_backend::{
    builtin::BuiltinEffect,
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic},
    rule::Predicate,
    simplify::*,
    smt::{NoSolver, SmtError, SmtSolver, Validity},
    substitution::Substitution,
    term::{Sort, Term, TermKind, Variable},
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

fn definition(axioms: &str) -> BackendDefinition {
    let source = format!(
        r#"[]
            module MAIN
                sort SortS{{}} [hasDomainValues{{}}()]
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                symbol wrap{{}}(SortS{{}}) : SortS{{}}
                    [function{{}}(), total{{}}(), injective{{}}(), no-evaluators{{}}()]
                symbol budgetPair{{}}(SortS{{}}, SortS{{}}) : SortS{{}}
                    [function{{}}(), total{{}}(), injective{{}}(), no-evaluators{{}}()]
                symbol f{{}}(SortS{{}}) : SortS{{}} [function{{}}()]
                hooked-symbol missingHook{{}}(SortS{{}}) : SortS{{}}
                    [function{{}}(), hook{{}}("TEST.missing")]
                {axioms}
            endmodule []"#
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    let syntax = parse_pattern(source).expect("term should parse");
    definition
        .internalize_term(&syntax, &[])
        .expect("term should internalize")
}

struct FixedValiditySolver(Validity);

impl SmtSolver for FixedValiditySolver {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Result<k_rust_backend::smt::Satisfiability, SmtError> {
        unreachable!()
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        _checked: &[Predicate],
    ) -> Result<Validity, SmtError> {
        Ok(self.0.clone())
    }
}

#[test]
fn unimplemented_hook_on_constructor_like_arguments_is_an_error() {
    let definition = definition("");
    let input = term(&definition, r#"missingHook{}(\dv{SortS{}}("value"))"#);

    let error = simplify(&definition, &input, SimplificationOptions::default())
        .expect_err("a concrete unimplemented hook must halt simplification");

    let message = format!("{error:?}");
    assert!(message.contains("UnsupportedHook"), "{message}");
    assert!(message.contains("TEST.missing"), "{message}");
}

#[test]
fn unimplemented_hook_on_symbolic_arguments_stays_unevaluated() {
    let definition = definition("");
    let input = term(&definition, "missingHook{}(X:SortS{})");

    let (result, diagnostics) =
        diagnostic::collect(|| simplify(&definition, &input, SimplificationOptions::default()));

    assert_eq!(
        result.expect("symbolic hook should remain valid").term,
        input
    );
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    let message = format!("{:?}", diagnostics[0]);
    assert!(message.contains("UnsupportedHookUnevaluated"), "{message}");
    assert!(message.contains("TEST.missing"), "{message}");
}

#[test]
fn unimplemented_hook_with_equations_uses_the_equations() {
    let definition = definition(
        r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    missingHook{}(X:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("missing-equation"), simplification{}()]
            "#,
    );
    let input = term(&definition, r#"missingHook{}(\dv{SortS{}}("value"))"#);

    let result = simplify(&definition, &input, SimplificationOptions::default())
        .expect("the definition equation should handle the hook");

    assert_eq!(result.term, term(&definition, r#"\dv{SortS{}}("value")"#));
}

#[test]
fn hooked_symbol_whose_equations_do_not_apply_stays_unevaluated() {
    let definition = definition(
        r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    missingHook{}(\dv{SortS{}}("other")),
                    \and{SortS{}}(
                        \dv{SortS{}}("result"),
                        \top{SortS{}}()
                    )
                )
            ) [label{}("missing-equation"), simplification{}()]
            "#,
    );
    let input = term(&definition, r#"missingHook{}(\dv{SortS{}}("value"))"#);

    let result = simplify(&definition, &input, SimplificationOptions::default())
        .expect("an equation-backed hook may remain unevaluated");

    assert_eq!(result.term, input);
}

fn conditional_nullary_function() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol f{}() : SortS{} [function{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \equals{SortS{}, R}(X:SortS{}, \dv{SortS{}}("zero")),
                        \top{R}()
                    ),
                    \equals{SortS{}, R}(
                        f{}(),
                        \and{SortS{}}(\dv{SortS{}}("result"), \top{SortS{}}())
                    )
                ) [label{}("conditional")]
            endmodule []"#,
    )
    .expect("conditional function definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("conditional function definition should internalize")
}

#[test]
fn equation_rhs_disjunction_with_two_live_alternatives_is_an_explicit_error() {
    let definition = definition(
        r#"
            symbol a{}() : SortS{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(
                        \or{SortS{}}(X:SortS{}, a{}()),
                        \top{SortS{}}()
                    )
                )
            ) [label{}("or-equation"), simplification{}()]
            "#,
    );
    let input = term(&definition, r#"f{}(\dv{SortS{}}("value"))"#);

    let error = simplify(&definition, &input, SimplificationOptions::default())
        .expect_err("an equation must not silently choose between live RHS alternatives");
    assert!(
        format!("{error:?}").contains("DisjunctiveResult"),
        "{error:?}"
    );
}

const TOP_RHS_EQUATION: &str = r#"
        axiom{R} \implies{R}(
            \top{R}(),
            \equals{SortS{}, R}(
                f{}(X:SortS{}),
                \and{SortS{}}(\top{SortS{}}(), \top{SortS{}}())
            )
        ) [label{}("erase-f"), simplification{}()]
    "#;

#[test]
fn drops_conjunction_operands_rewritten_to_top() {
    let definition = definition(TOP_RHS_EQUATION);
    let retained = term(&definition, r#"\dv{SortS{}}("retained")"#);
    let input = Term::and(
        retained.clone(),
        term(&definition, r#"f{}(\dv{SortS{}}("removed"))"#),
    );

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(result.term, retained);
    assert!(result.applied_rules.iter().any(|rule| rule == "erase-f"));
}

#[test]
fn top_equation_outside_a_conjunction_is_an_explicit_error() {
    let definition = definition(TOP_RHS_EQUATION);
    let input = term(&definition, r#"f{}(\dv{SortS{}}("removed"))"#);

    assert!(matches!(
        simplify(&definition, &input, SimplificationOptions::default()),
        Err(SimplificationError::TopEquationOutsideConjunction { rule_id })
            if rule_id == "erase-f"
    ));
}

const IDENTITY: &str = r#"
        axiom{R} \implies{R}(
            \top{R}(),
            \equals{SortS{}, R}(
                f{}(X:SortS{}),
                \and{SortS{}}(X:SortS{}, \top{SortS{}}())
            )
        ) [label{}("identity"), simplification{}()]
    "#;

#[test]
fn equations_carry_open_element_binding_definedness_as_constraints() {
    let definition = definition(
        r#"
            symbol discard{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(\top{R}(), \equals{SortS{}, R}(
                discard{}(X:SortS{}), \and{SortS{}}(\dv{SortS{}}("done"), \top{SortS{}}())
            )) [label{}("discard"), simplification{}()]
            axiom{R} \implies{R}(\top{R}(), \equals{R, R}(
                \ceil{SortS{}, R}(f{}(\dv{SortS{}}("undefined"))), \and{R}(\bottom{R}(), \top{R}())
            )) [simplification{}()]
            axiom{R} \implies{R}(\top{R}(), \equals{R, R}(
                \ceil{SortS{}, R}(f{}(\dv{SortS{}}("defined"))), \and{R}(\top{R}(), \top{R}())
            )) [simplification{}()]
            "#,
    );
    let done = term(&definition, r#"\dv{SortS{}}("done")"#);
    // A binding whose definedness is decided applies or refuses the equation outright; a
    // refuted obligation retains the subject, which is already empty. An open obligation
    // applies the equation and carries `\ceil` of the discarded operand as a constraint.
    let open = term(&definition, "f{}(X:SortS{})");
    for (operand, expected) in [
        (r#"\dv{SortS{}}("value")"#, Some(Vec::new())),
        (r#"f{}(\dv{SortS{}}("defined"))"#, Some(Vec::new())),
        (r#"f{}(\dv{SortS{}}("undefined"))"#, None),
        (
            r#"f{}(X:SortS{})"#,
            Some(vec![Predicate::Ceil(open.clone())]),
        ),
    ] {
        let input = term(&definition, &format!("discard{{}}({operand})"));
        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();
        match expected {
            Some(constraints) => {
                assert_eq!(result.term, done, "{operand}");
                assert_eq!(result.constraints, constraints, "{operand}");
            }
            None => {
                assert_eq!(result.term, input, "{operand}");
                assert!(result.constraints.is_empty(), "{operand}");
            }
        }
    }

    let operand = term(&definition, "f{}(X:SortS{})");
    let input = term(&definition, "discard{}(f{}(X:SortS{}))");
    let result = simplify_with_solver(
        &definition,
        &input,
        &[Predicate::Ceil(operand)],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();
    assert_eq!(result.term, done);
    assert!(result.constraints.is_empty());
}

#[test]
fn equation_set_variable_bindings_do_not_require_definedness() {
    let definition = definition(
        r#"
            symbol discard{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(\top{R}(), \equals{SortS{}, R}(
                discard{}(@X:SortS{}), \and{SortS{}}(\dv{SortS{}}("done"), \top{SortS{}}())
            )) [simplification{}()]
            "#,
    );
    let input = term(&definition, "discard{}(f{}(X:SortS{}))");
    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();
    assert_eq!(result.term, term(&definition, r#"\dv{SortS{}}("done")"#));
    assert!(result.constraints.is_empty());
}

#[test]
fn evaluates_overload_axioms_before_the_overloaded_function() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortGas{} []
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                hooked-symbol intAdd{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add")]
                symbol gasAdd{}(SortGas{}, SortGas{}) : SortGas{}
                    [function{}(), total{}()]
                axiom{}
                    \equals{SortGas{}, SortGas{}}(
                        gasAdd{}(
                            inj{SortInt{}, SortGas{}}(K0:SortInt{}),
                            inj{SortInt{}, SortGas{}}(K1:SortInt{})
                        ),
                        inj{SortInt{}, SortGas{}}(intAdd{}(K0:SortInt{}, K1:SortInt{}))
                    )
                    [symbol-overload{}(gasAdd{}(), intAdd{}())]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let frontend_term = |source: &str| {
        let syntax = parse_pattern(source).expect("term should parse");
        definition
            .internalize_frontend_term(&syntax, &[])
            .expect("frontend term should internalize")
    };
    let input = frontend_term(
        r#"gasAdd{}(
                inj{SortInt{}, SortGas{}}(\dv{SortInt{}}("2")),
                inj{SortInt{}, SortGas{}}(\dv{SortInt{}}("3"))
            )"#,
    );
    let expected = frontend_term(r#"inj{SortInt{}, SortGas{}}(\dv{SortInt{}}("5"))"#);

    let result = simplify(&definition, &input, SimplificationOptions::default())
        .expect("overloaded function should simplify");

    assert_eq!(result.term, expected);
    assert_eq!(result.applied_rules, ["UNKNOWN", "builtin:INT.add"]);
}

#[test]
fn simplifies_children_before_their_parent_to_a_fixed_point() {
    let definition = definition(IDENTITY);
    let input = term(&definition, r#"wrap{}(f{}(f{}(\dv{SortS{}}("value"))))"#);
    let expected = term(&definition, r#"wrap{}(\dv{SortS{}}("value"))"#);

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();
    assert_eq!(result.term, expected);
    assert_eq!(result.applied_rules, vec!["identity", "identity"]);
    assert!(result.constraints.is_empty());
}

#[test]
fn does_not_apply_equations_to_evaluated_terms() {
    let definition = definition(
        r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    X:SortS{},
                    \and{SortS{}}(f{}(X:SortS{}), \top{SortS{}}())
                )
            ) [label{}("expand-anything"), simplification{}()]
            "#,
    );
    let input = term(&definition, r#"\dv{SortS{}}("value")"#);

    let result = simplify(
        &definition,
        &input,
        SimplificationOptions {
            max_iterations: 1,
            ..SimplificationOptions::default()
        },
    )
    .expect("evaluated terms should already be at a fixed point");

    assert_eq!(result.term, input);
    assert!(result.applied_rules.is_empty());
}

#[test]
fn accepts_an_evaluated_result_at_the_iteration_boundary() {
    let definition = definition(
        r#"
            symbol next{}(SortS{}) : SortS{} [function{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(next{}(X:SortS{}), \top{SortS{}}())
                )
            ) [label{}("first"), simplification{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    next{}(X:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("second"), simplification{}()]
            "#,
    );
    let input = term(&definition, r#"f{}(\dv{SortS{}}("value"))"#);
    let expected = term(&definition, r#"\dv{SortS{}}("value")"#);

    let result = simplify(
        &definition,
        &input,
        SimplificationOptions {
            max_iterations: 1,
            ..SimplificationOptions::default()
        },
    )
    .expect("an evaluated boundary result should not require another iteration");

    assert_eq!(result.term, expected);
    assert_eq!(result.applied_rules, ["first", "second"]);
}

#[test]
fn propagates_symbolic_path_equalities_into_terms() {
    let definition = definition("");
    let x = term(&definition, "X:SortS{}");
    let y = term(&definition, "Y:SortS{}");
    let value = term(&definition, r#"\dv{SortS{}}("value")"#);
    let input = term(&definition, "wrap{}(X:SortS{})");
    let known = [Predicate::And(vec![
        Predicate::Equals(x, y.clone()),
        Predicate::Equals(y, value.clone()),
    ])];

    let result = simplify_with_solver(
        &definition,
        &input,
        &known,
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(
        result.term,
        term(&definition, r#"wrap{}(\dv{SortS{}}("value"))"#)
    );
}

#[test]
fn simplifies_conjuncts_under_sibling_assumptions() {
    let definition = definition("");
    let x = term(&definition, "X:SortS{}");
    let y = term(&definition, "Y:SortS{}");
    let wrap_x = term(&definition, "wrap{}(X:SortS{})");
    let wrap_y = term(&definition, "wrap{}(Y:SortS{})");
    let predicate = Predicate::And(vec![
        Predicate::Iff(Box::new(Predicate::True), Box::new(Predicate::Equals(x, y))),
        Predicate::Not(Box::new(Predicate::Equals(wrap_x, wrap_y))),
    ]);

    let result = simplify_predicate_with_solver(
        &definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(result, Predicate::False);
}

#[test]
fn deduplicates_conjuncts_without_discharging_them() {
    let definition = definition("");
    let disequality = Predicate::Not(Box::new(Predicate::Equals(
        term(&definition, "X:SortS{}"),
        term(&definition, "Y:SortS{}"),
    )));
    let predicate = Predicate::And(vec![disequality.clone(), disequality.clone()]);

    let result = simplify_predicate_with_solver(
        &definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(result, disequality);
}

#[test]
fn flattens_overlapping_conjunctions_before_using_sibling_assumptions() {
    let definition = definition("");
    let x = term(&definition, "X:SortS{}");
    let y = term(&definition, "Y:SortS{}");
    let value = term(&definition, r#"\dv{SortS{}}("value")"#);
    let defined = Predicate::Ceil(term(&definition, "f{}(X:SortS{})"));
    let first = Predicate::Not(Box::new(Predicate::Equals(x.clone(), y)));
    let second = Predicate::Not(Box::new(Predicate::Equals(x, value)));

    let result = simplify_predicates_with_solver(
        &definition,
        &[
            Predicate::And(vec![defined.clone(), first.clone()]),
            Predicate::And(vec![defined.clone(), second.clone()]),
        ],
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(result, [defined, first, second]);
}

#[test]
fn applies_simplification_rules_to_ml_predicates() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-symbol add{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add")]
                axiom{R, Q} \implies{R}(
                    \not{R}(\equals{SortInt{}, R}(J:SortInt{}, K:SortInt{})),
                    \equals{Q, R}(
                        \equals{SortInt{}, Q}(
                            add{}(I:SortInt{}, J:SortInt{}),
                            add{}(I:SortInt{}, K:SortInt{})
                        ),
                        \and{Q}(\bottom{Q}(), \top{Q}())
                    )
                ) [label{}("different-offsets"), simplification{}()]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let predicate = Predicate::Equals(
        term(&definition, r#"add{}(X:SortInt{}, \dv{SortInt{}}("5"))"#),
        term(&definition, r#"add{}(X:SortInt{}, \dv{SortInt{}}("7"))"#),
    );

    let result = simplify_predicate_with_solver(
        &definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(result, Predicate::False);
    assert_eq!(definition.predicate_simplification_theory.len(), 1);
}

#[test]
fn applies_conditional_ceil_equations_under_known_predicates() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol isFun{}(SortInt{}) : SortBool{} [function{}(), total{}()]
                symbol fun{}(SortInt{}) : SortInt{} [function{}()]
                axiom{R, Q} \implies{R}(
                    \equals{SortBool{}, R}(
                        isFun{}(X:SortInt{}),
                        \dv{SortBool{}}("true")
                    ),
                    \equals{Q, R}(
                        \ceil{SortInt{}, Q}(fun{}(X:SortInt{})),
                        \and{Q}(\top{Q}(), \top{Q}())
                    )
                ) [label{}("ceil-fun"), simplification{}()]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let is_fun = term(&definition, "isFun{}(X:SortInt{})");
    let truth = term(&definition, r#"\dv{SortBool{}}("true")"#);
    let predicate = Predicate::Ceil(term(&definition, "fun{}(X:SortInt{})"));
    let known = [Predicate::Equals(is_fun, truth)];

    assert_eq!(
        simplify_predicate_with_solver(
            &definition,
            &predicate,
            &known,
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap(),
        Predicate::True,
    );
    assert_eq!(
        simplify_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap(),
        predicate,
    );
    let ceil_rule = definition
        .ceil_theory
        .values()
        .flat_map(|groups| groups.values())
        .flatten()
        .next()
        .expect("ceil equation should be indexed");
    assert_eq!(ceil_rule.requires.len(), 1);
}

#[test]
fn constructor_ceil_distinguishes_element_and_set_variables() {
    let definition = definition("");
    let fresh_constructor = Term::application(
        definition.symbols["wrap"].clone(),
        Vec::new(),
        vec![Term::variable(Variable::new("Ex#X", Sort::simple("SortS")))],
    );
    let ordinary_constructor = term(&definition, "wrap{}(X:SortS{})");
    let set_variable = Term::variable(Variable::set("X", Sort::simple("SortS")));
    let set_constructor = Term::application(
        definition.symbols["wrap"].clone(),
        Vec::new(),
        vec![set_variable.clone()],
    );

    assert_eq!(
        simplify_predicate_with_solver(
            &definition,
            &Predicate::Ceil(fresh_constructor),
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap(),
        Predicate::True,
    );
    assert_eq!(
        simplify_predicate_with_solver(
            &definition,
            &Predicate::Ceil(ordinary_constructor),
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap(),
        Predicate::True,
    );
    assert_eq!(
        simplify_predicate_with_solver(
            &definition,
            &Predicate::Ceil(set_constructor),
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap(),
        Predicate::Ceil(set_variable),
    );
}

#[test]
fn keeps_unknown_ensures_as_result_constraints() {
    let definition = definition(
        r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(
                        X:SortS{},
                        \equals{SortS{}, SortS{}}(X:SortS{}, Y:SortS{})
                    )
                )
            ) [label{}("constrained"), simplification{}()]
            "#,
    );
    let input = term(&definition, r#"f{}(\dv{SortS{}}("value"))"#);

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();
    assert_eq!(result.constraints.len(), 1);
    assert!(matches!(result.constraints[0], Predicate::Equals(..)));
}

#[test]
fn refuted_ensures_make_the_equation_result_bottom() {
    let definition = definition(
        r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(
                        X:SortS{},
                        \equals{SortBool{}, SortS{}}(
                            \dv{SortBool{}}("true"),
                            \dv{SortBool{}}("false")
                        )
                    )
                )
            ) [label{}("contradictory-result"), simplification{}()]
            "#,
    );
    let value = term(&definition, r#"\dv{SortS{}}("value")"#);
    let input = term(&definition, r#"f{}(\dv{SortS{}}("value"))"#);

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(result.term, value);
    assert_eq!(result.constraints, [Predicate::False]);
    assert_eq!(result.applied_rules, ["contradictory-result"]);
}

#[test]
fn predicate_term_simplification_preserves_result_constraints() {
    let definition = definition(
        r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(
                        X:SortS{},
                        \equals{SortS{}, SortS{}}(X:SortS{}, Y:SortS{})
                    )
                )
            ) [label{}("constrained"), simplification{}()]
            "#,
    );
    let value = term(&definition, r#"\dv{SortS{}}("value")"#);
    let input = term(&definition, r#"f{}(\dv{SortS{}}("value"))"#);
    let term_result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    let predicate_result = simplify_predicate_with_solver(
        &definition,
        &Predicate::Equals(input, value),
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(term_result.constraints.len(), 1);
    assert_eq!(predicate_result, term_result.constraints[0]);
}

#[test]
fn evaluates_hooked_functions_bottom_up() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortInt{} [hasDomainValues{}()]
                hooked-symbol add{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add")]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let input = term(
        &definition,
        r#"add{}(add{}(\dv{SortInt{}}("20"), \dv{SortInt{}}("21")), \dv{SortInt{}}("1"))"#,
    );
    let expected = term(&definition, r#"\dv{SortInt{}}("42")"#);

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(result.term, expected);
    assert_eq!(
        result.applied_rules,
        vec!["builtin:INT.add", "builtin:INT.add"]
    );
}

#[test]
fn evaluates_function_equations_with_symbolic_map_selection() {
    let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} [hasDomainValues{}()]
                sort SortValue{} [hasDomainValues{}()]
                sort SortBool{} [hasDomainValues{}()]
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                hooked-symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol nonEmpty{}(SortMap{}) : SortBool{} [function{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortBool{}, R}(
                        nonEmpty{}(
                            mapConcat{}(
                                mapItem{}(KEY:SortKey{}, VALUE:SortValue{}),
                                REST:SortMap{}
                            )
                        ),
                        \and{SortBool{}}(
                            \dv{SortBool{}}("true"),
                            \top{SortBool{}}()
                        )
                    )
                ) [label{}("non-empty-map"), simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let input = term(
        &definition,
        r#"nonEmpty{}(
                mapConcat{}(
                    mapItem{}(\dv{SortKey{}}("a"), \dv{SortValue{}}("1")),
                    mapItem{}(\dv{SortKey{}}("b"), \dv{SortValue{}}("2"))
                )
            )"#,
    );

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(result.term, term(&definition, r#"\dv{SortBool{}}("true")"#));
    assert_eq!(result.applied_rules, ["non-empty-map"]);
}

#[test]
fn keeps_ambiguous_open_map_equations_indeterminate() {
    let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} []
                sort SortValue{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                sort SortResult{} []
                hooked-symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol select{}(SortMap{}, SortKey{}) : SortResult{} [function{}()]
                symbol exact{}() : SortResult{} [constructor{}()]
                symbol different{}() : SortResult{} [constructor{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortResult{}, R}(
                        select{}(
                            mapConcat{}(
                                mapItem{}(KEY:SortKey{}, VALUE:SortValue{}),
                                REST:SortMap{}
                            ),
                            KEY:SortKey{}
                        ),
                        \and{SortResult{}}(exact{}(), \top{SortResult{}}())
                    )
                ) [label{}("exact"), simplification{}()]
                axiom{R} \implies{R}(
                    \not{R}(\equals{SortKey{}, R}(ENTRY:SortKey{}, REQUESTED:SortKey{})),
                    \equals{SortResult{}, R}(
                        select{}(
                            mapConcat{}(
                                mapItem{}(ENTRY:SortKey{}, VALUE:SortValue{}),
                                REST:SortMap{}
                            ),
                            REQUESTED:SortKey{}
                        ),
                        \and{SortResult{}}(different{}(), \top{SortResult{}}())
                    )
                ) [label{}("different"), simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let entry = term(&definition, "ENTRY:SortKey{}");
    let requested = term(&definition, "REQUESTED:SortKey{}");
    let known = Predicate::Not(Box::new(Predicate::Equals(entry, requested)));
    let input = term(
        &definition,
        "select{}(mapConcat{}(mapItem{}(ENTRY:SortKey{}, VALUE:SortValue{}), MAP:SortMap{}), REQUESTED:SortKey{})",
    );

    let result = simplify_with_solver(
        &definition,
        &input,
        std::slice::from_ref(&known),
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(result.term, input);
    assert!(result.applied_rules.is_empty());
}

#[test]
fn simplification_equations_continue_past_indeterminate_higher_priority_matches() {
    let definition = definition(
        r#"
            symbol a{}() : SortS{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(a{}()),
                    \and{SortS{}}(\dv{SortS{}}("specific"), \top{SortS{}}())
                )
            ) [label{}("specific"), simplification{}("10")]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("fallback"), \top{SortS{}}())
                )
            ) [label{}("fallback"), simplification{}("50")]
            "#,
    );
    let input = term(&definition, "f{}(Y:SortS{})");

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(
        result.term,
        term(&definition, r#"\dv{SortS{}}("fallback")"#)
    );
    assert_eq!(result.applied_rules, ["fallback"]);
}

#[test]
fn skips_equations_with_violated_concreteness_constraints() {
    let definition = definition(
        r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("concrete"), \top{SortS{}}())
                )
            ) [label{}("concrete-only"), concrete{}(X:SortS{}), simplification{}("10")]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("fallback"), \top{SortS{}}())
                )
            ) [label{}("fallback"), simplification{}("50")]
            "#,
    );
    let input = term(&definition, "f{}(Y:SortS{})");

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(
        result.term,
        term(&definition, r#"\dv{SortS{}}("fallback")"#)
    );
    assert_eq!(result.applied_rules, ["fallback"]);
}

#[test]
fn applies_concrete_symbolic_canonicalization_equations() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortInt{} [hasDomainValues{}()]
                hooked-symbol add{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), functional{}(), hook{}("INT.add")]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        add{}(I:SortInt{}, B:SortInt{}),
                        \and{SortInt{}}(add{}(B:SortInt{}, I:SortInt{}), \top{SortInt{}}())
                    )
                ) [
                    label{}("concrete-left"),
                    concrete{}(I:SortInt{}),
                    symbolic{}(B:SortInt{}),
                    simplification{}("51")
                ]
            endmodule []"#,
    )
    .unwrap();
    let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
    let input = term(&definition, r#"add{}(\dv{SortInt{}}("1"), X:SortInt{})"#);
    let expected = term(&definition, r#"add{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(result.term, expected);
    assert_eq!(result.applied_rules, ["concrete-left"]);
}

#[test]
fn applies_a_same_priority_result_despite_indeterminate_sibling_heads() {
    let definition = definition(
        r#"
            symbol g{}(SortS{}) : SortS{} [function{}()]
            symbol h{}(SortS{}) : SortS{} [function{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(g{}(X:SortS{})),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("through-g"), simplification{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(h{}(X:SortS{})),
                    \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}())
                )
            ) [label{}("through-h"), simplification{}()]
            "#,
    );
    let input = term(&definition, "f{}(g{}(Y:SortS{}))");

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(result.term, term(&definition, "Y:SortS{}"));
    assert_eq!(result.applied_rules, ["through-g"]);
}

fn same_priority_term_equations(attribute: &str) -> BackendDefinition {
    definition(&format!(
        r#"
            axiom{{R}} \implies{{R}}(
                \top{{R}}(),
                \equals{{SortS{{}}, R}}(
                    f{{}}(X:SortS{{}}),
                    \and{{SortS{{}}}}(\dv{{SortS{{}}}}("first"), \top{{SortS{{}}}}())
                )
            ) [label{{}}("z-first"){attribute}]
            axiom{{R}} \implies{{R}}(
                \top{{R}}(),
                \equals{{SortS{{}}, R}}(
                    f{{}}(X:SortS{{}}),
                    \and{{SortS{{}}}}(\dv{{SortS{{}}}}("second"), \top{{SortS{{}}}}())
                )
            ) [label{{}}("a-second"){attribute}]
            "#
    ))
}

#[test]
fn applies_the_first_declared_same_priority_simplification_equation() {
    let definition = same_priority_term_equations(", simplification{}()");
    let input = term(&definition, r#"f{}(\dv{SortS{}}("value"))"#);

    let result = simplify(&definition, &input, SimplificationOptions::default())
        .expect("the first applicable simplification equation should win");

    assert_eq!(result.term, term(&definition, r#"\dv{SortS{}}("first")"#));
    assert_eq!(result.applied_rules, ["z-first"]);
}

#[test]
fn applies_the_first_declared_same_priority_function_equation() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol f{}() : SortS{} [function{}()]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \top{R}()),
                    \equals{SortS{}, R}(
                        f{}(),
                        \and{SortS{}}(\dv{SortS{}}("first"), \top{SortS{}}())
                    )
                ) [label{}("function-first")]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \top{R}()),
                    \equals{SortS{}, R}(
                        f{}(),
                        \and{SortS{}}(\dv{SortS{}}("second"), \top{SortS{}}())
                    )
                ) [label{}("function-second")]
            endmodule []"#,
    )
    .expect("function definition should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("function definition should internalize");
    let input = term(&definition, "f{}()");

    let result = simplify(&definition, &input, SimplificationOptions::default())
        .expect("the first applicable function equation should win");

    assert_eq!(result.term, term(&definition, r#"\dv{SortS{}}("first")"#));
    assert_eq!(result.applied_rules, ["function-first"]);
}

#[test]
fn applies_the_canonically_first_same_priority_predicate_equation() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol f{}(SortS{}) : SortS{} [function{}()]
                axiom{R, Q} \implies{R}(
                    \top{R}(),
                    \equals{Q, R}(
                        \equals{SortS{}, Q}(f{}(X:SortS{}), X:SortS{}),
                        \and{Q}(\top{Q}(), \top{Q}())
                    )
                ) [label{}("predicate-first"), simplification{}()]
                axiom{R, Q} \implies{R}(
                    \top{R}(),
                    \equals{Q, R}(
                        \equals{SortS{}, Q}(f{}(X:SortS{}), X:SortS{}),
                        \and{Q}(\bottom{Q}(), \top{Q}())
                    )
                ) [label{}("predicate-second"), simplification{}()]
            endmodule []"#,
    )
    .expect("predicate definition should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("predicate definition should internalize");
    let value = term(&definition, r#"\dv{SortS{}}("value")"#);
    let predicate = Predicate::Equals(term(&definition, r#"f{}(\dv{SortS{}}("value"))"#), value);

    let result = simplify_predicate_with_solver(
        &definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("the first applicable predicate equation should win");

    assert_eq!(result, Predicate::True);
}

#[test]
fn function_group_with_an_indeterminate_sibling_still_blocks_owise() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol f{}() : SortS{} [function{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \equals{SortS{}, R}(X:SortS{}, \dv{SortS{}}("zero")),
                        \top{R}()
                    ),
                    \equals{SortS{}, R}(
                        f{}(),
                        \and{SortS{}}(\dv{SortS{}}("conditional"), \top{SortS{}}())
                    )
                ) [label{}("conditional")]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \top{R}()),
                    \equals{SortS{}, R}(
                        f{}(),
                        \and{SortS{}}(\dv{SortS{}}("owise"), \top{SortS{}}())
                    )
                ) [label{}("owise"), priority{}("200")]
            endmodule []"#,
    )
    .expect("function definition should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("function definition should internalize");
    let input = term(&definition, "f{}()");

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(result.term, input);
    assert!(result.applied_rules.is_empty());
}

#[test]
fn sort_membership_stays_symbolic_for_sorts_with_common_values() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortValue{} []
                sort SortExpression{} []
                sort SortResult{} []
                sort SortOther{} []
                sort SortKItem{} []
                sort SortK{} []
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                symbol dotk{}() : SortK{} [constructor{}()]
                symbol kseq{}(SortKItem{}, SortK{}) : SortK{}
                    [constructor{}(), injective{}()]
                symbol isResult{}(SortK{}) : SortBool{} [function{}(), total{}()]
                axiom{R} \exists{R}(
                    Value:SortExpression{},
                    \equals{SortExpression{}, R}(
                        Value:SortExpression{},
                        inj{SortValue{}, SortExpression{}}(From:SortValue{})
                    )
                ) [subsort{SortValue{}, SortExpression{}}()]
                axiom{R} \exists{R}(
                    Value:SortResult{},
                    \equals{SortResult{}, R}(
                        Value:SortResult{},
                        inj{SortValue{}, SortResult{}}(From:SortValue{})
                    )
                ) [subsort{SortValue{}, SortResult{}}()]
                axiom{R} \exists{R}(
                    Value:SortKItem{},
                    \equals{SortKItem{}, R}(
                        Value:SortKItem{},
                        inj{SortExpression{}, SortKItem{}}(From:SortExpression{})
                    )
                ) [subsort{SortExpression{}, SortKItem{}}()]
                axiom{R} \exists{R}(
                    Value:SortKItem{},
                    \equals{SortKItem{}, R}(
                        Value:SortKItem{},
                        inj{SortResult{}, SortKItem{}}(From:SortResult{})
                    )
                ) [subsort{SortResult{}, SortKItem{}}()]
                axiom{R} \exists{R}(
                    Value:SortKItem{},
                    \equals{SortKItem{}, R}(
                        Value:SortKItem{},
                        inj{SortOther{}, SortKItem{}}(From:SortOther{})
                    )
                ) [subsort{SortOther{}, SortKItem{}}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortK{}, R}(
                                X:SortK{},
                                kseq{}(
                                    inj{SortResult{}, SortKItem{}}(RESULT:SortResult{}),
                                    dotk{}()
                                )
                            ),
                            \top{R}()
                        )
                    ),
                    \equals{SortBool{}, R}(
                        isResult{}(X:SortK{}),
                        \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}())
                    )
                ) [label{}("result")]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortK{}, R}(X:SortK{}, ANY:SortK{}), \top{R}())
                    ),
                    \equals{SortBool{}, R}(
                        isResult{}(X:SortK{}),
                        \and{SortBool{}}(\dv{SortBool{}}("false"), \top{SortBool{}}())
                    )
                ) [label{}("owise"), priority{}("200")]
            endmodule []"#,
    )
    .expect("sort-membership definition should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("sort-membership definition should internalize");
    let true_term = term(&definition, r#"\dv{SortBool{}}("true")"#);
    let false_term = term(&definition, r#"\dv{SortBool{}}("false")"#);
    let cases = [
        ("SortExpression", None),
        ("SortValue", Some(&true_term)),
        ("SortResult", Some(&true_term)),
        ("SortOther", Some(&false_term)),
    ];

    for (source, expected) in cases {
        let input = term(
            &definition,
            &format!(
                "isResult{{}}(kseq{{}}(inj{{{source}{{}}, SortKItem{{}}}}(INPUT:{source}{{}}), dotk{{}}()))"
            ),
        );
        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();
        assert_eq!(result.term, expected.unwrap_or(&input).clone(), "{source}");
    }
}

#[test]
fn normalizes_boolean_k_disequality_conditions_to_native_predicates() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortBool{} [hasDomainValues{}()]
                sort SortElement{} []
                sort SortKItem{} []
                sort SortK{} []
                symbol dotk{}() : SortK{} [constructor{}()]
                symbol kseq{}(SortKItem{}, SortK{}) : SortK{}
                    [constructor{}(), injective{}()]
                hooked-symbol andBool{}(SortBool{}, SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.and")]
                hooked-symbol notEqual{}(SortK{}, SortK{}) : SortBool{}
                    [function{}(), total{}(), hook{}("KEQUAL.ne")]
                symbol g{}(SortElement{}) : SortElement{} [function{}(), total{}()]
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                axiom{R} \exists{R}(
                    Value:SortKItem{},
                    \equals{SortKItem{}, R}(
                        Value:SortKItem{},
                        inj{SortElement{}, SortKItem{}}(From:SortElement{})
                    )
                ) [subsort{SortElement{}, SortKItem{}}()]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let x = term(&definition, "X:SortElement{}");
    let y = term(&definition, "Y:SortElement{}");
    let gx = term(&definition, "g{}(X:SortElement{})");
    let gy = term(&definition, "g{}(Y:SortElement{})");
    let condition = term(
        &definition,
        r#"andBool{}(
                notEqual{}(
                    kseq{}(inj{SortElement{}, SortKItem{}}(X:SortElement{}), dotk{}()),
                    kseq{}(inj{SortElement{}, SortKItem{}}(Y:SortElement{}), dotk{}())
                ),
                notEqual{}(
                    kseq{}(inj{SortElement{}, SortKItem{}}(g{}(X:SortElement{})), dotk{}()),
                    kseq{}(inj{SortElement{}, SortKItem{}}(g{}(Y:SortElement{})), dotk{}())
                )
            )"#,
    );
    let predicate = Predicate::Equals(
        condition,
        Term::domain_value(Sort::simple("SortBool"), "true"),
    );

    let result = simplify_predicate_with_solver(
        &definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(
        result,
        Predicate::And(vec![
            Predicate::Not(Box::new(Predicate::Equals(x.clone(), y.clone()))),
            Predicate::Not(Box::new(Predicate::Equals(gx, gy))),
        ])
    );
}

#[test]
fn aligns_singleton_k_equality_operands_at_their_declared_supersort() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortBool{} [hasDomainValues{}()]
                sort SortSubElement{} []
                sort SortElement{} []
                sort SortKItem{} []
                sort SortK{} []
                symbol sub{}() : SortSubElement{} [constructor{}()]
                symbol dotk{}() : SortK{} [constructor{}()]
                symbol kseq{}(SortKItem{}, SortK{}) : SortK{}
                    [constructor{}(), injective{}()]
                hooked-symbol notEqual{}(SortK{}, SortK{}) : SortBool{}
                    [function{}(), total{}(), hook{}("KEQUAL.ne")]
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                axiom{R} \exists{R}(
                    Value:SortElement{},
                    \equals{SortElement{}, R}(
                        Value:SortElement{},
                        inj{SortSubElement{}, SortElement{}}(From:SortSubElement{})
                    )
                ) [subsort{SortSubElement{}, SortElement{}}()]
                axiom{R} \exists{R}(
                    Value:SortKItem{},
                    \equals{SortKItem{}, R}(
                        Value:SortKItem{},
                        inj{SortElement{}, SortKItem{}}(From:SortElement{})
                    )
                ) [subsort{SortElement{}, SortKItem{}}()]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let element = term(&definition, "X:SortElement{}");
    let sub_element = term(&definition, "sub{}()");
    let condition = term(
        &definition,
        r#"notEqual{}(
                kseq{}(inj{SortElement{}, SortKItem{}}(X:SortElement{}), dotk{}()),
                kseq{}(inj{SortSubElement{}, SortKItem{}}(sub{}()), dotk{}())
            )"#,
    );

    let result = simplify_predicate_with_solver(
        &definition,
        &Predicate::Equals(
            condition,
            Term::domain_value(Sort::simple("SortBool"), "true"),
        ),
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(
        result,
        Predicate::Not(Box::new(Predicate::Equals(
            element,
            Term::injection(
                Sort::simple("SortSubElement"),
                Sort::simple("SortElement"),
                sub_element,
            ),
        )))
    );
}

#[test]
fn normalizes_nested_boolean_term_negation_to_an_equality() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-symbol notBool{}(SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.not")]
                hooked-symbol equalsInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq")]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let variable = term(&definition, "X:SortInt{}");
    let zero = term(&definition, r#"\dv{SortInt{}}("0")"#);
    let condition = term(
        &definition,
        r#"notBool{}(notBool{}(equalsInt{}(X:SortInt{}, \dv{SortInt{}}("0"))))"#,
    );

    let result = simplify_predicate_with_solver(
        &definition,
        &Predicate::Term(condition),
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(result, Predicate::Equals(variable, zero));
}

#[test]
fn boolean_equalities_with_literals_normalize_to_term_predicates() {
    let definition = definition("");
    let condition = term(&definition, "B:SortBool{}");
    let true_value = Term::domain_value(Sort::simple("SortBool"), "true");
    let false_value = Term::domain_value(Sort::simple("SortBool"), "false");

    for (predicate, expected) in [
        (
            Predicate::Equals(condition.clone(), false_value.clone()),
            Predicate::Not(Box::new(Predicate::Term(condition.clone()))),
        ),
        (
            Predicate::Equals(false_value, condition.clone()),
            Predicate::Not(Box::new(Predicate::Term(condition.clone()))),
        ),
        (
            Predicate::Equals(condition.clone(), true_value.clone()),
            Predicate::Term(condition.clone()),
        ),
        (
            Predicate::Equals(true_value, condition.clone()),
            Predicate::Term(condition.clone()),
        ),
    ] {
        let result = simplify_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("Boolean literal equality should simplify");

        assert_eq!(result, expected, "input: {predicate:#?}");
    }
}

#[test]
fn normalizes_symbolic_integer_equality_and_keeps_operand_definedness() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortBool{} [hasDomainValues{}()]
                sort SortInt{} [hasDomainValues{}()]
                hooked-symbol eq{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq")]
                hooked-symbol pow{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.pow")]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let variable = term(&definition, "X:SortInt{}");
    let power = term(&definition, r#"pow{}(X:SortInt{}, \dv{SortInt{}}("256"))"#);
    let predicate = Predicate::Equals(
        Term::domain_value(Sort::simple("SortBool"), "true"),
        term(
            &definition,
            r#"eq{}(X:SortInt{}, pow{}(X:SortInt{}, \dv{SortInt{}}("256")))"#,
        ),
    );

    let result = simplify_predicate_with_solver(
        &definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(
        result,
        Predicate::And(vec![
            Predicate::Ceil(power.clone()),
            Predicate::Equals(variable, power),
        ])
    );
}

#[test]
fn preserves_symbolic_equalities_between_matching_injective_symbols() {
    let definition = definition(
        r#"
            symbol pair{}(SortS{}, SortS{}) : SortS{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            "#,
    );
    let one = term(&definition, r#"\dv{SortS{}}("1")"#);
    let left = term(&definition, r#"pair{}(X:SortS{}, \dv{SortS{}}("1"))"#);
    let right = term(&definition, r#"pair{}(Y:SortS{}, \dv{SortS{}}("1"))"#);
    let predicate = Predicate::Equals(left, right);

    let result = simplify_predicate_with_solver(
        &definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(result, predicate);
    assert_eq!(
        simplify_predicate_with_solver(
            &definition,
            &Predicate::Equals(one.clone(), one),
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap(),
        Predicate::True,
    );
}

fn injection_equality_definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortInt{} [hasDomainValues{}()]
                sort SortBool{} [hasDomainValues{}()]
                sort SortExp{} []
                sort SortKItem{} []
                sort SortA{} []
                sort SortB{} []
                sort SortC{} []
                sort SortD{} []
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                axiom{R} \exists{R}(E:SortExp{}, \equals{SortExp{}, R}(
                    E:SortExp{}, inj{SortInt{}, SortExp{}}(I:SortInt{})
                )) [subsort{SortInt{}, SortExp{}}()]
                axiom{R} \exists{R}(K:SortKItem{}, \equals{SortKItem{}, R}(
                    K:SortKItem{}, inj{SortExp{}, SortKItem{}}(E:SortExp{})
                )) [subsort{SortExp{}, SortKItem{}}()]
                axiom{R} \exists{R}(K:SortKItem{}, \equals{SortKItem{}, R}(
                    K:SortKItem{}, inj{SortBool{}, SortKItem{}}(B:SortBool{})
                )) [subsort{SortBool{}, SortKItem{}}()]
                axiom{R} \exists{R}(K:SortKItem{}, \equals{SortKItem{}, R}(
                    K:SortKItem{}, inj{SortA{}, SortKItem{}}(A:SortA{})
                )) [subsort{SortA{}, SortKItem{}}()]
                axiom{R} \exists{R}(K:SortKItem{}, \equals{SortKItem{}, R}(
                    K:SortKItem{}, inj{SortB{}, SortKItem{}}(B:SortB{})
                )) [subsort{SortB{}, SortKItem{}}()]
                axiom{R} \exists{R}(K:SortKItem{}, \equals{SortKItem{}, R}(
                    K:SortKItem{}, inj{SortC{}, SortKItem{}}(C:SortC{})
                )) [subsort{SortC{}, SortKItem{}}()]
                axiom{R} \exists{R}(A:SortA{}, \equals{SortA{}, R}(
                    A:SortA{}, inj{SortD{}, SortA{}}(D:SortD{})
                )) [subsort{SortD{}, SortA{}}()]
                axiom{R} \exists{R}(C:SortC{}, \equals{SortC{}, R}(
                    C:SortC{}, inj{SortD{}, SortC{}}(D:SortD{})
                )) [subsort{SortD{}, SortC{}}()]
            endmodule []"#,
    )
    .expect("injection equality definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("injection equality definition should internalize")
}

fn simplify_injection_equality(
    definition: &BackendDefinition,
    left: &str,
    right: &str,
) -> Predicate {
    simplify_predicate_with_solver(
        definition,
        &Predicate::Equals(term(definition, left), term(definition, right)),
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("injection equality should simplify")
}

#[test]
fn injection_equality_with_equal_sorts_reduces_to_the_children() {
    let definition = injection_equality_definition();

    assert_eq!(
        simplify_injection_equality(
            &definition,
            "inj{SortInt{}, SortKItem{}}(I:SortInt{})",
            r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("5"))"#,
        ),
        Predicate::Equals(
            term(&definition, "I:SortInt{}"),
            term(&definition, r#"\dv{SortInt{}}("5")"#),
        )
    );
}

#[test]
fn injection_equality_with_a_subsort_relation_reinjects_the_smaller_side() {
    let definition = injection_equality_definition();

    assert_eq!(
        simplify_injection_equality(
            &definition,
            "inj{SortInt{}, SortKItem{}}(I:SortInt{})",
            "inj{SortExp{}, SortKItem{}}(E:SortExp{})",
        ),
        Predicate::Equals(
            term(&definition, "inj{SortInt{}, SortExp{}}(I:SortInt{})"),
            term(&definition, "E:SortExp{}"),
        )
    );
}

#[test]
fn externalized_injection_equalities_verify_after_sort_narrowing() {
    let definition = injection_equality_definition();
    for (left, right) in [
        (
            "inj{SortInt{}, SortKItem{}}(I:SortInt{})",
            "inj{SortExp{}, SortKItem{}}(E:SortExp{})",
        ),
        (
            "inj{SortA{}, SortKItem{}}(A:SortA{})",
            "inj{SortC{}, SortKItem{}}(C:SortC{})",
        ),
    ] {
        for (left, right) in [(left, right), (right, left)] {
            let result = simplify_injection_equality(&definition, left, right);
            let Predicate::Equals(lhs, rhs) = &result else {
                panic!("symbolic equality must remain a constraint: {result:?}");
            };
            assert_eq!(lhs.sort(), rhs.sort());
            let external =
                k_rust_backend::externalize::predicate_pattern(&result, &Sort::simple("SortKItem"));
            definition.verify_standalone_pattern(&external).unwrap();
            let (roundtrip, _) = definition.internalize_predicate(&external, &[]).unwrap();
            assert_eq!(roundtrip, result);
        }
    }

    // The verifier must reject a missing injection, so this audit cannot silently
    // accept a producer that chooses the left operand's sort for unequal operands.
    let malformed = Predicate::Equals(
        term(&definition, "I:SortInt{}"),
        term(&definition, "E:SortExp{}"),
    );
    let external =
        k_rust_backend::externalize::predicate_pattern(&malformed, &Sort::simple("SortKItem"));
    assert!(definition.verify_standalone_pattern(&external).is_err());
}

#[test]
fn injection_equality_with_a_constructor_head_is_bottom() {
    let definition = injection_equality_definition();

    assert_eq!(
        simplify_injection_equality(
            &definition,
            "inj{SortInt{}, SortKItem{}}(I:SortInt{})",
            r#"inj{SortBool{}, SortKItem{}}(\dv{SortBool{}}("true"))"#,
        ),
        Predicate::False,
    );
}

#[test]
fn injection_equality_uses_common_subsorts_to_distinguish_unknown_from_disjoint() {
    let definition = injection_equality_definition();
    let disjoint = simplify_injection_equality(
        &definition,
        "inj{SortA{}, SortKItem{}}(A:SortA{})",
        "inj{SortB{}, SortKItem{}}(B:SortB{})",
    );
    let common = simplify_injection_equality(
        &definition,
        "inj{SortA{}, SortKItem{}}(A:SortA{})",
        "inj{SortC{}, SortKItem{}}(C:SortC{})",
    );

    assert_eq!(disjoint, Predicate::False);
    assert_eq!(
        common,
        Predicate::Equals(
            term(&definition, "inj{SortA{}, SortKItem{}}(A:SortA{})"),
            term(&definition, "inj{SortC{}, SortKItem{}}(C:SortC{})"),
        )
    );
}

#[test]
fn preserves_a_symbolic_equality_between_singleton_k_sequences() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortState{} []
                sort SortKItem{} []
                sort SortK{} []
                symbol peng{}() : SortState{} [constructor{}()]
                symbol dotk{}() : SortK{} [constructor{}()]
                symbol kseq{}(SortKItem{}, SortK{}) : SortK{}
                    [constructor{}(), injective{}()]
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                axiom{R} \exists{R}(
                    Value:SortKItem{},
                    \equals{SortKItem{}, R}(
                        Value:SortKItem{},
                        inj{SortState{}, SortKItem{}}(From:SortState{})
                    )
                ) [subsort{SortState{}, SortKItem{}}()]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let syntax = parse_pattern(
        r#"\not{SortK{}}(
                \equals{SortK{}, SortK{}}(
                    kseq{}(inj{SortState{}, SortKItem{}}(STATE:SortState{}), dotk{}()),
                    kseq{}(inj{SortState{}, SortKItem{}}(peng{}()), dotk{}())
                )
            )"#,
    )
    .expect("predicate should parse");
    let (predicate, _) = definition
        .internalize_predicate(&syntax, &[])
        .expect("predicate should internalize");

    let result = simplify_predicate_with_solver(
        &definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(result, predicate);
}

#[test]
fn returns_user_logs_as_effects_and_the_reference_unit_term() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortString{} [hasDomainValues{}()]
                sort SortK{} []
                sort SortUnit{} []
                symbol dotk{}() : SortK{} [constructor{}()]
                hooked-symbol log{}(SortString{}) : SortUnit{}
                    [function{}(), total{}(), hook{}("IO.logString")]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let input = term(&definition, r#"log{}(\dv{SortString{}}("hello from K"))"#);

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert!(matches!(
        result.term.kind(),
        TermKind::Application { symbol, arguments, .. }
            if symbol.name.as_ref() == "dotk"
                && symbol.result_sort == Sort::simple("SortUnit")
                && arguments.is_empty()
    ));
    assert_eq!(
        result.effects,
        [BuiltinEffect::UserLog("hello from K".into())]
    );
    assert_eq!(result.applied_rules, ["builtin:IO.logString"]);
}

#[test]
fn represents_undefined_partial_builtins_as_bottom_constraints() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortInt{} [hasDomainValues{}()]
                hooked-symbol tdiv{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.tdiv")]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let input = term(
        &definition,
        r#"tdiv{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0"))"#,
    );

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(result.term, input);
    assert_eq!(result.constraints, [Predicate::False]);
    assert_eq!(result.applied_rules, ["builtin:INT.tdiv"]);
}

#[cfg(feature = "z3")]
#[test]
fn z3_disambiguates_symbolic_equation_requires() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                symbol f{}(SortInt{}) : SortInt{} [function{}()]
                axiom{R} \implies{R}(
                    \equals{SortBool{}, R}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("10")),
                        \dv{SortBool{}}("true")
                    ),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(X:SortInt{}, \top{SortInt{}}())
                    )
                ) [label{}("conditional-f"), simplification{}()]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let input = term(&definition, "f{}(Y:SortInt{})");
    let variable = Term::variable(k_rust_backend::term::Variable::new(
        "Y",
        k_rust_backend::term::Sort::simple("SortInt"),
    ));
    let run = |value: &str| {
        simplify_with_solver(
            &definition,
            &input,
            &[Predicate::Equals(
                variable.clone(),
                Term::domain_value(k_rust_backend::term::Sort::simple("SortInt"), value),
            )],
            SimplificationOptions::default(),
            &solver,
        )
        .unwrap()
    };

    assert_eq!(
        run("5").term,
        Term::domain_value(k_rust_backend::term::Sort::simple("SortInt"), "5")
    );
    assert_eq!(
        run("15").term,
        term(&definition, r#"f{}(\dv{SortInt{}}("15"))"#)
    );
}

#[test]
fn simplification_equations_continue_past_unknown_conditions() {
    let definition = definition(
        r#"
            axiom{R} \implies{R}(
                \equals{SortS{}, R}(X:SortS{}, \dv{SortS{}}("zero")),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("conditional"), \top{SortS{}}())
                )
            ) [label{}("conditional"), simplification{}("10")]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("fallback"), \top{SortS{}}())
                )
            ) [label{}("fallback"), simplification{}("50")]
            "#,
    );
    let input = term(&definition, "f{}(Y:SortS{})");

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(
        result.term,
        term(&definition, r#"\dv{SortS{}}("fallback")"#)
    );
    assert_eq!(result.applied_rules, ["fallback"]);
}

#[test]
fn preserves_functions_with_complementary_unknown_equation_conditions() {
    let definition = definition(
        r#"
            axiom{R} \implies{R}(
                \equals{SortS{}, R}(X:SortS{}, \dv{SortS{}}("zero")),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("yes"), \top{SortS{}}())
                )
            ) [label{}("yes"), simplification{}()]
            axiom{R} \implies{R}(
                \not{R}(\equals{SortS{}, R}(X:SortS{}, \dv{SortS{}}("zero"))),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("no"), \top{SortS{}}())
                )
            ) [label{}("no"), simplification{}()]
            "#,
    );
    let input = term(&definition, "f{}(Y:SortS{})");

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(result.term, input);
    assert!(result.applied_rules.is_empty());
}

#[test]
fn recursive_side_condition_simplification_preserves_the_application() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol loop{}(SortBool{}) : SortBool{} [function{}()]
                axiom{R} \implies{R}(
                    \equals{SortBool{}, R}(
                        loop{}(X:SortBool{}),
                        \dv{SortBool{}}("true")
                    ),
                    \equals{SortBool{}, R}(
                        loop{}(X:SortBool{}),
                        \and{SortBool{}}(
                            \dv{SortBool{}}("true"),
                            \top{SortBool{}}()
                        )
                    )
                ) [label{}("recursive-condition"), simplification{}()]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let input = term(&definition, r#"loop{}(\dv{SortBool{}}("true"))"#);

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(result.term, input);
    assert!(result.applied_rules.is_empty());
}

#[test]
fn detects_non_terminating_equation_sets_at_the_bound() {
    let definition = definition(
        r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(f{}(f{}(X:SortS{})), \top{SortS{}}())
                )
            ) [label{}("expand"), simplification{}()]
            "#,
    );
    let input = term(&definition, r#"f{}(\dv{SortS{}}("value"))"#);

    assert!(matches!(
        simplify(
            &definition,
            &input,
            SimplificationOptions {
                max_iterations: 3,
                ..SimplificationOptions::default()
            },
        ),
        Err(SimplificationError::IterationLimit { limit: 3, .. })
    ));
}

fn long_fixed_point_chain() -> (BackendDefinition, Term, Term) {
    let mut theory = String::new();
    for index in 0..=128 {
        theory.push_str(&format!(
            "symbol chain{index}{{}}() : SortS{{}} [function{{}}()]\n"
        ));
    }
    for index in 0..128 {
        let next = index + 1;
        theory.push_str(&format!(
            r#"
                axiom{{R}} \implies{{R}}(
                    \top{{R}}(),
                    \equals{{SortS{{}}, R}}(
                        chain{index}{{}}(),
                        \and{{SortS{{}}}}(chain{next}{{}}(), \top{{SortS{{}}}}())
                    )
                ) [label{{}}("chain-{index}"), simplification{{}}()]
                "#
        ));
    }
    theory.push_str(
        r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    chain128{}(),
                    \and{SortS{}}(\dv{SortS{}}("done"), \top{SortS{}}())
                )
            ) [label{}("chain-done"), simplification{}()]
            "#,
    );
    let definition = definition(&theory);
    let input = term(&definition, "chain0{}()");
    let expected = term(&definition, r#"\dv{SortS{}}("done")"#);

    (definition, input, expected)
}

#[test]
fn keep_partial_returns_the_reached_term_with_the_exhaustion_flag() {
    let (definition, input, _) = long_fixed_point_chain();
    let partial = match simplify(
        &definition,
        &input,
        SimplificationOptions {
            max_iterations: 3,
            budget: BudgetPolicy::Fail,
        },
    ) {
        Err(SimplificationError::IterationLimit { term, .. }) => term,
        result => {
            panic!("expected the fail policy to expose its partial term, found {result:?}")
        }
    };

    let result = simplify(
        &definition,
        &input,
        SimplificationOptions {
            max_iterations: 3,
            budget: BudgetPolicy::KeepPartial,
        },
    )
    .expect("the keep-partial policy should preserve the reached term");

    assert_eq!(result.term, partial);
    assert_eq!(
        result.exhausted,
        Some(BudgetExhaustion {
            limit: 3,
            subject: BudgetSubject::Term,
        })
    );
}

#[test]
fn keep_partial_keeps_unsimplified_constraints_at_the_predicate_bound() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol p0{}(SortS{}) : SortS{} [function{}()]
                symbol p1{}(SortS{}) : SortS{} [function{}()]
                symbol p2{}(SortS{}) : SortS{} [function{}()]
                symbol p3{}(SortS{}) : SortS{} [function{}()]
                axiom{R, Q} \implies{R}(
                    \top{R}(),
                    \equals{Q, R}(
                        \equals{SortS{}, Q}(p0{}(X:SortS{}), X:SortS{}),
                        \and{Q}(\equals{SortS{}, Q}(p1{}(X:SortS{}), X:SortS{}), \top{Q}())
                    )
                ) [label{}("predicate-0"), simplification{}()]
                axiom{R, Q} \implies{R}(
                    \top{R}(),
                    \equals{Q, R}(
                        \equals{SortS{}, Q}(p1{}(X:SortS{}), X:SortS{}),
                        \and{Q}(\equals{SortS{}, Q}(p2{}(X:SortS{}), X:SortS{}), \top{Q}())
                    )
                ) [label{}("predicate-1"), simplification{}()]
                axiom{R, Q} \implies{R}(
                    \top{R}(),
                    \equals{Q, R}(
                        \equals{SortS{}, Q}(p2{}(X:SortS{}), X:SortS{}),
                        \and{Q}(\equals{SortS{}, Q}(p3{}(X:SortS{}), X:SortS{}), \top{Q}())
                    )
                ) [label{}("predicate-2"), simplification{}()]
            endmodule []"#,
    )
    .expect("predicate-chain definition should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("predicate-chain definition should internalize");
    let value = term(&definition, r#"\dv{SortS{}}("value")"#);
    let input = vec![Predicate::Equals(
        term(&definition, r#"p0{}(\dv{SortS{}}("value"))"#),
        value,
    )];

    let (result, diagnostics) = diagnostic::collect(|| {
        simplify_predicates_with_solver(
            &definition,
            &input,
            &[],
            SimplificationOptions {
                max_iterations: 1,
                budget: BudgetPolicy::KeepPartial,
            },
            &NoSolver,
        )
    });

    assert_eq!(result.unwrap(), input);
    assert_eq!(
        diagnostics,
        [BackendDiagnostic::SimplificationBudgetExhausted {
            limit: 1,
            subject: BudgetSubject::Predicates,
        }]
    );
}

#[test]
fn default_budget_halts_a_long_chain_with_a_typed_error() {
    let (definition, input, _) = long_fixed_point_chain();

    assert!(matches!(
        simplify(&definition, &input, SimplificationOptions::default()),
        Err(SimplificationError::IterationLimit {
            limit: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            ..
        })
    ));
}

#[test]
fn unbounded_simplification_completes_a_long_fixed_point_chain() {
    let (definition, input, expected) = long_fixed_point_chain();

    let result = simplify(&definition, &input, SimplificationOptions::unbounded())
        .expect("the complete Kore-style pass should finish finite computations");

    assert_eq!(result.term, expected);
    assert_eq!(result.applied_rules.len(), 129);
}

#[test]
fn iteration_limit_is_local_to_each_fixed_point_chain() {
    // Distilled from the pinned backend's function-evaluation-demo/NatList.demo: that finite
    // computation performs well over 100 reductions across independent constructor branches.
    let definition = definition(IDENTITY);
    let mut inputs = vec![r#"f{}(\dv{SortS{}}("value"))"#.to_owned(); 128];
    let mut expected = vec![r#"\dv{SortS{}}("value")"#.to_owned(); 128];
    while inputs.len() > 1 {
        inputs = inputs
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| format!("budgetPair{{}}({}, {})", pair[0], pair[1]))
            .collect();
        expected = expected
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| format!("budgetPair{{}}({}, {})", pair[0], pair[1]))
            .collect();
    }
    let input = term(&definition, &inputs[0]);
    let expected = term(&definition, &expected[0]);

    let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

    assert_eq!(result.term, expected);
    assert_eq!(result.applied_rules.len(), 128);
}

#[test]
fn predicate_iteration_limit_is_local_to_each_branch() {
    let definition = definition(IDENTITY);
    let value = term(&definition, r#"\dv{SortS{}}("value")"#);
    let predicates = (0..128)
        .map(|_| {
            Predicate::Equals(
                term(&definition, r#"f{}(\dv{SortS{}}("value"))"#),
                value.clone(),
            )
        })
        .collect();

    let result = simplify_predicate_with_solver(
        &definition,
        &Predicate::Or(predicates),
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .unwrap();

    assert_eq!(result, Predicate::True);
}

#[cfg(feature = "z3")]
#[test]
fn standalone_predicate_simplification_uses_smt_for_the_residual() {
    use k_rust_backend::smt::Z3Solver;

    let syntax = parse_definition(
        r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortList{} []
                hooked-symbol size{}(SortList{}) : SortInt{}
                    [function{}(), total{}(), hook{}("LIST.size")]
                hooked-symbol add{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
                hooked-symbol gt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
            endmodule []"#,
    )
    .unwrap();
    let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
    let predicate = Predicate::Term(term(
        &definition,
        r#"gt{}(add{}(size{}(L:SortList{}), \dv{SortInt{}}("2")), \dv{SortInt{}}("0"))"#,
    ));

    let result = simplify_and_decide_predicate_with_solver(
        &definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &Z3Solver::new(&definition).unwrap(),
    )
    .unwrap();

    assert_eq!(result, Predicate::True);
}

#[test]
fn standalone_predicate_simplification_keeps_the_residual_on_smt_unknown() {
    let definition = definition("");
    let predicate = Predicate::Term(term(&definition, "X:SortS{}"));
    let (result, diagnostics) = diagnostic::collect(|| {
        simplify_and_decide_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &FixedValiditySolver(Validity::Unknown("incomplete arithmetic".into())),
        )
    });
    let result = result.expect("SMT unknown should preserve the residual predicate");

    assert_eq!(result, predicate);
    assert_eq!(
        diagnostics,
        [BackendDiagnostic::UndecidedPredicate {
            predicate,
            reason: ConditionIndeterminacy::SmtUnknown("incomplete arithmetic".into()),
        }]
    );
}

#[test]
fn unknown_function_condition_leaves_the_application_unevaluated() {
    let definition = conditional_nullary_function();
    let input = term(&definition, "f{}()");

    let (result, diagnostics) = diagnostic::collect(|| {
        simplify_with_solver(
            &definition,
            &input,
            &[],
            SimplificationOptions::default(),
            &FixedValiditySolver(Validity::Unknown("timeout".into())),
        )
    });
    let result = result.expect("SMT unknown should not be a simplification error");

    assert_eq!(result.term, input);
    assert!(result.applied_rules.is_empty());
    assert!(matches!(
        diagnostics.as_slice(),
        [BackendDiagnostic::UndecidedCondition {
            rule_id,
            reason: ConditionIndeterminacy::SmtUnknown(reason),
            predicates,
        }] if rule_id == "conditional" && reason == "timeout" && predicates.len() == 1
    ));
}

#[test]
fn unknown_simplification_condition_tries_the_next_equation() {
    let definition = definition(
        r#"
            axiom{R} \implies{R}(
                \equals{SortS{}, R}(X:SortS{}, \dv{SortS{}}("zero")),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("conditional"), \top{SortS{}}())
                )
            ) [label{}("conditional"), simplification{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("fallback"), \top{SortS{}}())
                )
            ) [label{}("fallback"), simplification{}()]
            "#,
    );
    let input = term(&definition, "f{}(Y:SortS{})");

    let result = simplify_with_solver(
        &definition,
        &input,
        &[],
        SimplificationOptions::default(),
        &FixedValiditySolver(Validity::Unknown("timeout".into())),
    )
    .expect("an unknown simplification condition should be skipped");

    assert_eq!(
        result.term,
        term(&definition, r#"\dv{SortS{}}("fallback")"#)
    );
    assert_eq!(result.applied_rules, ["fallback"]);
}

#[test]
fn inconsistent_path_condition_is_indeterminate_not_an_error() {
    let definition = conditional_nullary_function();
    let input = term(&definition, "f{}()");

    let (result, diagnostics) = diagnostic::collect(|| {
        simplify_with_solver(
            &definition,
            &input,
            &[],
            SimplificationOptions::default(),
            &FixedValiditySolver(Validity::InconsistentGroundTruth),
        )
    });
    let result = result.expect("an inconsistent path condition should not be an error");

    assert_eq!(result.term, input);
    assert!(result.applied_rules.is_empty());
    assert!(matches!(
        diagnostics.as_slice(),
        [BackendDiagnostic::UndecidedCondition {
            rule_id,
            reason: ConditionIndeterminacy::InconsistentPathCondition,
            predicates,
        }] if rule_id == "conditional" && predicates.len() == 1
    ));
}

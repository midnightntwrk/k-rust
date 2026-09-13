//! Public contracts of `k_rust_backend::rewrite`.

#[cfg(feature = "z3")]
use k_rust_backend::term::{Sort, Term, Variable};
use k_rust_backend::{
    definition::BackendDefinition,
    rewrite::*,
    rule::Predicate,
    simplify::SimplificationOptions,
    smt::{NoSolver, Satisfiability, SmtError, SmtSolver, Validity},
    substitution::Substitution,
    term::TermKind,
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::support::internal_term;

#[derive(Clone, Debug)]
struct FixedSolver {
    satisfiability: Result<Satisfiability, SmtError>,
    validity: Result<Validity, SmtError>,
}

impl SmtSolver for FixedSolver {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Result<Satisfiability, SmtError> {
        self.satisfiability.clone()
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        _checked: &[Predicate],
    ) -> Result<Validity, SmtError> {
        self.validity.clone()
    }
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
fn list_update_patterns_rewrite_only_when_the_selected_element_agrees() {
    let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortList{}
                    [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
                sort SortState{} []
                hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
                hooked-symbol listItem{}(SortInt{}) : SortList{} [function{}(), total{}(), hook{}("LIST.element")]
                hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
                    [function{}(), hook{}("LIST.concat"), assoc{}()]
                hooked-symbol update{}(SortList{}, SortInt{}, SortInt{}) : SortList{}
                    [function{}(), hook{}("LIST.update")]
                symbol state{}(SortInt{}, SortInt{}, SortList{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(I:SortInt{}, V:SortInt{}, update{}(L:SortList{}, I:SortInt{}, V:SortInt{})),
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("list-update-pattern")]
            endmodule []"#,
        ).unwrap();
    let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
    let list = r#"listConcat{}(listItem{}(\dv{SortInt{}}("0")), listConcat{}(listItem{}(\dv{SortInt{}}("1")), listItem{}(\dv{SortInt{}}("2"))))"#;

    // The update is a pattern, not a mutation: the three agreeing values match;
    // a different value or an invalid index leaves the original state stuck.
    for (index, value, applies) in [
        (0, 0, true),
        (1, 1, true),
        (2, 2, true),
        (0, 1, false),
        (-1, 2, false),
        (3, 3, false),
    ] {
        let subject = Pattern {
            term: internal_term(
                &definition,
                &format!(
                    r#"state{{}}(\dv{{SortInt{{}}}}("{index}"), \dv{{SortInt{{}}}}("{value}"), {list})"#
                ),
            ),
            constraints: Vec::new(),
        };
        let result = rewrite_step(&definition, &subject, &mut 0);
        if applies {
            let RewriteResult::Finished(applied) = result else {
                panic!("({index}, {value}) should rewrite: {result:?}");
            };
            assert_eq!(applied.pattern.term, internal_term(&definition, "done{}()"));
            assert!(applied.pattern.constraints.is_empty());
        } else {
            assert_eq!(result, RewriteResult::Stuck(subject), "({index}, {value})");
        }
    }
}

fn rewrite_coverage_definition() -> BackendDefinition {
    let syntax = parse_definition(include_str!("../fixtures/rewrite-coverage.kore"))
        .expect("coverage fixture should parse");
    BackendDefinition::internalize(&syntax, "REWRITE-COVERAGE")
        .expect("coverage fixture should internalize")
}

#[test]
fn concrete_anywhere_match_requires_lhs_substitution_coverage() {
    let definition = rewrite_coverage_definition();
    let subject = Pattern {
        term: internal_term(&definition, "state{}(id{}())"),
        constraints: Vec::new(),
    };
    assert!(subject.term.attributes().constructor_like);
    let solver = FixedSolver {
        satisfiability: Ok(Satisfiability::Sat),
        validity: Ok(Validity::Indeterminate),
    };
    let mut fresh = 0;
    let result = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver);
    let RewriteResult::Indeterminate {
        reason: IndeterminateReason::Instantiation {
            missing_variables, ..
        },
        ..
    } = result
    else {
        panic!("a concrete subject must not acquire existential rule arguments: {result:?}");
    };
    assert_eq!(missing_variables.len(), 1);
    assert!(missing_variables.iter().next().unwrap().name.ends_with("E"));
    assert_eq!(
        fresh, 0,
        "a failed concrete instantiation must not freshen LHS variables"
    );
}

#[test]
fn concrete_instantiation_coverage_is_checked_after_requires() {
    for (requires, binds) in [
        (r"\bottom{SortS{}}()", false),
        (r"\equals{SortS{},SortS{}}(id{}(), value{}())", false),
        (r"\equals{SortS{},SortS{}}(E:SortS{}, id{}())", true),
    ] {
        let source = include_str!("../fixtures/rewrite-coverage.kore").replace(
            r"state{}(box{}(E:SortS{})), \top{SortS{}}()",
            &format!("state{{}}(box{{}}(E:SortS{{}})), {requires}"),
        );
        let definition =
            BackendDefinition::internalize(&parse_definition(&source).unwrap(), "REWRITE-COVERAGE")
                .unwrap();
        let subject = Pattern {
            term: internal_term(&definition, "state{}(id{}())"),
            constraints: Vec::new(),
        };
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Indeterminate),
        };
        let mut fresh = 0;
        let result = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver);
        if binds {
            let RewriteResult::Branch { branches, .. } = result else {
                panic!("requires must complete the substitution: {result:?}");
            };
            assert_eq!(
                branches[0].pattern.term,
                internal_term(&definition, "heated{}(id{}())")
            );
            assert_eq!(
                branches[0].pattern.constraints,
                vec![Predicate::Equals(
                    internal_term(&definition, "box{}(id{}())"),
                    internal_term(&definition, "id{}()"),
                )],
                "binding E must preserve the unresolved function equality",
            );
        } else {
            let RewriteResult::Finished(applied) = result else {
                panic!("a false requires must reject before coverage: {result:?}");
            };
            assert_eq!(applied.pattern.term, internal_term(&definition, "done{}()"));
        }
        assert_eq!(fresh, 0);
    }
}

#[test]
fn anywhere_normalization_and_covered_matching_remain_available() {
    let definition = rewrite_coverage_definition();
    let term = internal_term(&definition, "state{}(box{}(value{}()))");
    let normalized =
        k_rust_backend::simplify::simplify(&definition, &term, SimplificationOptions::default())
            .unwrap();
    assert_eq!(
        normalized.term,
        internal_term(&definition, "state{}(value{}())")
    );
    let subject = Pattern {
        term: internal_term(&definition, "state{}(box{}(id{}()))"),
        constraints: Vec::new(),
    };
    assert!(!subject.term.attributes().constructor_like);
    assert!(subject.term.attributes().variables.is_empty());
    let mut fresh = 0;
    let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh) else {
        panic!("a covered anywhere match must still apply");
    };
    assert_eq!(
        applied.pattern.term,
        internal_term(&definition, "heated{}(id{}())")
    );
    assert_eq!(fresh, 0);
}

#[test]
fn symbolic_anywhere_matching_retains_fresh_arguments_and_complement() {
    let definition = rewrite_coverage_definition();
    let subject = Pattern {
        term: internal_term(&definition, "state{}(SUBJECT:SortS{})"),
        constraints: Vec::new(),
    };
    let solver = FixedSolver {
        satisfiability: Ok(Satisfiability::Sat),
        validity: Ok(Validity::Indeterminate),
    };
    let mut fresh = 0;
    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("symbolic anywhere matching must narrow");
    };
    assert_eq!(branches[0].unique_id, "heat");
    assert_eq!(fresh, 1);
    assert!(
        matches!(remainder.pattern.constraints.as_slice(), [Predicate::Not(inner)]
            if matches!(inner.as_ref(), Predicate::Exists(..)))
    );
}

#[cfg(feature = "z3")]
#[test]
fn concrete_disequality_does_not_invent_an_operand() {
    let definition = kequal_rewrite_definition("state{}(equal{}(VALUE:SortValue{}, chosen{}()))");
    let subject = Pattern {
        term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("false"))"#),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;
    assert!(matches!(
        rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver),
        RewriteResult::Indeterminate {
            reason: IndeterminateReason::Instantiation { .. },
            ..
        }
    ));
    assert_eq!(fresh, 0);
}

fn unresolved_function_rewrite_definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol wrap{}(SortBool{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol not{}(SortBool{}) : SortBool{}
                    [function{}(), total{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        wrap{}(not{}(X:SortBool{})),
                        \top{SortS{}}()
                    ),
                    \dv{SortS{}}("done")
                ) [label{}("negated")]
            endmodule []"#,
    )
    .expect("function rewrite definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("function rewrite definition should internalize")
}

fn rigid_no_evaluators_rewrite_definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                symbol opaque{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol state{}(SortInt{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(\dv{SortInt{}}("0")),
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("zero")]
            endmodule []"#,
    )
    .expect("rigid function rewrite definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("rigid function rewrite definition should internalize")
}

fn non_evaluable_function_rewrite_definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol foo{}(SortS{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol f{}(SortS{}) : SortS{}
                    [function{}(), total{}(), no-evaluators{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        wrap{}(foo{}(X:SortS{})),
                        \top{SortS{}}()
                    ),
                    wrap{}(f{}(X:SortS{}))
                ) [label{}("to-non-evaluable")]
            endmodule []"#,
    )
    .expect("non-evaluable function definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("non-evaluable function definition should internalize")
}

#[test]
fn reports_smt_indeterminacy_after_rewriting_to_a_concrete_function_without_evaluators() {
    let definition = non_evaluable_function_rewrite_definition();
    let initial = Pattern {
        term: internal_term(&definition, r#"wrap{}(foo{}(\dv{SortS{}}("12")))"#),
        constraints: Vec::new(),
    };

    let execution = execute(
        &definition,
        initial,
        ExecutionOptions {
            max_depth: 2,
            ..ExecutionOptions::default()
        },
    );

    assert!(matches!(
        execution.leaves.as_slice(),
        [ExecutionLeaf {
            pattern: Pattern { term, constraints },
            depth: 1,
            halt_reason: HaltReason::Indeterminate(IndeterminateReason::Smt {
                rule_id,
                error: SmtError::Unavailable,
                ..
            }),
            ..
        }] if term == &internal_term(
            &definition,
            r#"wrap{}(f{}(\dv{SortS{}}("12")))"#,
        ) && constraints.is_empty() && rule_id == "to-non-evaluable"
    ));
}

fn kequal_rewrite_definition(lhs: &str) -> BackendDefinition {
    let source = r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortValue{} []
                sort SortState{} []
                hooked-symbol equal{}(SortValue{}, SortValue{}) : SortBool{}
                    [function{}(), total{}(), hook{}("KEQUAL.eq")]
                symbol chosen{}() : SortValue{} [constructor{}()]
                symbol rejected{}() : SortValue{} [constructor{}()]
                symbol state{}(SortBool{}) : SortState{} [constructor{}()]
                symbol stateWithContext{}(SortBool{}, SortValue{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        $LHS,
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("equality")]
            endmodule []"#
        .replace("$LHS", lhs);
    let syntax = parse_definition(&source).expect("K equality definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("K equality definition should internalize")
}

fn subject(definition: &BackendDefinition, value: &str) -> Pattern {
    let syntax = parse_pattern(&format!(r#"wrap{{}}(\dv{{SortS{{}}}}("{value}"))"#))
        .expect("subject should parse");
    Pattern {
        term: definition
            .internalize_term(&syntax, &[])
            .expect("subject should internalize"),
        constraints: Vec::new(),
    }
}

fn assert_constrained_rewrite_applies(attribute: &str, subject: &str) {
    let definition = definition(&format!(
        r#"
            axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}(wrap{{}}(X:SortS{{}}), \top{{SortS{{}}}}()),
                \dv{{SortS{{}}}}("done")
            ) [{attribute}, label{{}}("constrained-rewrite")]
            "#,
    ));
    let subject = Pattern {
        term: internal_term(&definition, subject),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh) else {
        panic!("concreteness attributes must not block rewrite rules");
    };
    assert_eq!(
        applied.pattern.term,
        internal_term(&definition, r#"\dv{SortS{}}("done")"#)
    );
}

#[test]
fn concrete_rewrite_rules_apply_to_symbolic_configurations() {
    assert_constrained_rewrite_applies("concrete{}()", "wrap{}(Y:SortS{})");
}

#[test]
fn symbolic_rewrite_rules_apply_to_concrete_configurations() {
    assert_constrained_rewrite_applies("symbolic{}()", r#"wrap{}(\dv{SortS{}}("value"))"#);
}

#[test]
fn named_concreteness_lists_are_ignored_on_rewrite_rules() {
    assert_constrained_rewrite_applies("concrete{}(X:SortS{})", "wrap{}(Y:SortS{})");
}

#[test]
fn treats_an_undefined_matched_subterm_as_trivial() {
    let definition = definition(
        r#"
            symbol partial{}() : SortS{} [function{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("done"))
            ) [label{}("unwrap")]
            "#,
    );
    let partial = internal_term(&definition, "partial{}()");
    let subject = Pattern {
        term: internal_term(&definition, "wrap{}(partial{}())"),
        constraints: vec![Predicate::Not(Box::new(Predicate::Ceil(partial)))],
    };
    let mut fresh = 0;

    let result = rewrite_step(&definition, &subject, &mut fresh);

    assert_eq!(result, RewriteResult::Trivial(subject));
}

#[test]
fn rejects_a_symbolic_occurs_check_during_rewriting() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortS{} []
                symbol pair{}(SortS{}, SortS{}) : SortS{} [constructor{}()]
                symbol nested{}(SortS{}) : SortS{} [constructor{}()]
                symbol done{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        pair{}(X:SortS{}, nested{}(X:SortS{})),
                        \top{SortS{}}()
                    ),
                    done{}()
                ) [label{}("cyclic")]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let subject = Pattern {
        term: internal_term(&definition, "pair{}(Y:SortS{}, Y:SortS{})"),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    assert_eq!(
        rewrite_step(&definition, &subject, &mut fresh),
        RewriteResult::Stuck(subject)
    );
}

#[test]
fn internalizes_a_nested_bottom_rewrite_rhs_as_trivial() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(\dv{SortS{}}("start")),
                    \top{SortS{}}()
                ),
                wrap{}(\bottom{SortS{}}())
            ) [label{}("bottom")]
            "#,
    );
    let subject = Pattern {
        term: internal_term(&definition, r#"wrap{}(\dv{SortS{}}("start"))"#),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let result = rewrite_step(&definition, &subject, &mut fresh);

    assert_eq!(result, RewriteResult::Trivial(subject.clone()));
    let (execution, initial_status) =
        execute_disjunction_with_solver_and_observer_with_initial_status(
            &definition,
            vec![subject],
            ExecutionOptions::default(),
            &NoSolver,
            |_| {},
        );
    assert!(!initial_status.simplified_to_bottom());
    assert!(matches!(
        execution.leaves.as_slice(),
        [ExecutionLeaf {
            depth: 0,
            halt_reason: HaltReason::Trivial,
            ..
        }]
    ));
}

#[test]
fn initial_bottom_metadata_requires_completed_bottom_simplification_for_every_input() {
    let definition = definition("");
    let live = subject(&definition, "live");
    let mut bottom = subject(&definition, "bottom");
    bottom.constraints.push(Predicate::False);

    let (_, all_bottom) = execute_disjunction_with_solver_and_observer_with_initial_status(
        &definition,
        vec![bottom.clone(), bottom.clone()],
        ExecutionOptions::default(),
        &NoSolver,
        |_| {},
    );
    assert!(all_bottom.simplified_to_bottom());

    let (_, mixed) = execute_disjunction_with_solver_and_observer_with_initial_status(
        &definition,
        vec![bottom.clone(), live],
        ExecutionOptions {
            max_depth: 0,
            ..ExecutionOptions::default()
        },
        &NoSolver,
        |_| {},
    );
    assert!(!mixed.simplified_to_bottom());

    let (_, not_started) = execute_disjunction_with_solver_and_observer_with_initial_status(
        &definition,
        vec![bottom],
        ExecutionOptions {
            max_breadth: Some(0),
            ..ExecutionOptions::default()
        },
        &NoSolver,
        |_| {},
    );
    assert!(!not_started.simplified_to_bottom());
}

#[test]
fn a_trivial_rule_shadows_lower_priority_rules() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \and{SortS{}}(\dv{SortS{}}("discarded"), \bottom{SortS{}}())
            ) [label{}("trivial"), priority{}("50")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("fallback")
            ) [label{}("fallback"), owise{}()]
            "#,
    );
    let initial = subject(&definition, "value");
    let mut fresh = 0;

    assert_eq!(
        rewrite_step(&definition, &initial, &mut fresh),
        RewriteResult::Trivial(initial.clone())
    );
    assert!(matches!(
        execute(&definition, initial.clone(), ExecutionOptions::default())
            .leaves
            .as_slice(),
        [ExecutionLeaf {
            depth: 0,
            halt_reason: HaltReason::Trivial,
            ..
        }]
    ));
    let search = k_rust_backend::search::search_graph(
        &definition,
        initial,
        k_rust_backend::search::SearchOptions {
            search_type: k_rust_backend::search::SearchType::Final,
            ..k_rust_backend::search::SearchOptions::default()
        },
    );
    assert!(search.states.is_empty(), "{search:#?}");
}

fn symbolic_trivial_definition(include_fallback: bool) -> BackendDefinition {
    let fallback = if include_fallback {
        r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
                \dv{SortInt{}}("20")
            ) [label{}("fallback"), priority{}("50")]
            "#
    } else {
        ""
    };
    symbolic_remainder_definition(&format!(
        r#"
            axiom{{}} \rewrites{{SortInt{{}}}}(
                \and{{SortInt{{}}}}(
                    wrap{{}}(X:SortInt{{}}),
                    \equals{{SortBool{{}}, SortInt{{}}}}(
                        lt{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
                        \dv{{SortBool{{}}}}("true")
                    )
                ),
                \and{{SortInt{{}}}}(
                    \dv{{SortInt{{}}}}("discarded"),
                    \bottom{{SortInt{{}}}}()
                )
            ) [label{{}}("trivial"), priority{{}}("10")]
            {fallback}
            "#,
    ))
}

fn indeterminate_sat_solver() -> FixedSolver {
    FixedSolver {
        satisfiability: Ok(Satisfiability::Sat),
        validity: Ok(Validity::Indeterminate),
    }
}

#[test]
fn a_trivial_rule_joins_the_group_remainder_symbolically() {
    let definition = symbolic_trivial_definition(true);
    let initial = symbolic_subject(&definition);
    let solver = indeterminate_sat_solver();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        trivial,
        ..
    } = rewrite_step_with_solver(&definition, &initial, &mut fresh, &solver)
    else {
        panic!("a conditional bottom result should leave its complement");
    };
    assert!(branches.is_empty());
    let [trivial] = trivial.as_slice() else {
        panic!("expected one visible trivial sub-case");
    };
    assert_eq!(trivial.rule_id, "trivial");
    assert_eq!(trivial.label.as_deref(), Some("trivial"));
    assert_ne!(trivial.applicability, Predicate::True);
    assert_eq!(
        trivial.remainder,
        Predicate::Not(Box::new(trivial.applicability.clone()))
    );
    assert_eq!(remainder.rule_ids, ["trivial"]);
    assert!(remainder.pattern.constraints.contains(&trivial.remainder));

    let execution = execute_with_solver(&definition, initial, ExecutionOptions::default(), &solver);
    let [leaf] = execution.leaves.as_slice() else {
        panic!("the complement should reach the fallback exactly once");
    };
    assert!(matches!(leaf.halt_reason, HaltReason::Stuck));
    assert!(matches!(
        leaf.pattern.term.kind(),
        TermKind::DomainValue { value, .. } if value.as_ref() == "20"
    ));
    assert!(
        leaf.pattern
            .constraints
            .iter()
            .any(|predicate| matches!(predicate, Predicate::Not(_)))
    );
}

#[test]
fn a_mixed_group_keeps_its_trivial_sub_case_visible() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \and{SortS{}}(\dv{SortS{}}("discarded"), \bottom{SortS{}}())
            ) [label{}("trivial")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("survivor")
            ) [label{}("survivor")]
            "#,
    );
    let initial = subject(&definition, "value");
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: None,
        trivial,
        ..
    } = rewrite_step(&definition, &initial, &mut fresh)
    else {
        panic!("a mixed group must retain its bottom sub-case");
    };
    assert_eq!(branches.len(), 1);
    assert_eq!(trivial.len(), 1);
    assert_eq!(trivial[0].rule_id, "trivial");
    assert_eq!(trivial[0].applicability, Predicate::True);
    assert_eq!(trivial[0].remainder, Predicate::False);

    let execution = execute(&definition, initial, ExecutionOptions::default());
    let [leaf] = execution.leaves.as_slice() else {
        panic!("execution must drop only the trivial sub-case");
    };
    assert!(matches!(
        leaf.pattern.term.kind(),
        TermKind::DomainValue { value, .. } if value.as_ref() == "survivor"
    ));
}

#[test]
fn sequential_mode_narrows_by_trivial_rules() {
    let definition = symbolic_trivial_definition(true);
    let initial = symbolic_subject(&definition);
    let solver = indeterminate_sat_solver();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: None,
        trivial,
        ..
    } = rewrite_step_sequential_with_solver(&definition, &initial, &mut fresh, &solver)
    else {
        panic!("sequential rewriting must expose and exclude the trivial sub-case");
    };
    assert_eq!(trivial.len(), 1);
    let [branch] = branches.as_slice() else {
        panic!("the fallback should cover only the trivial rule's complement");
    };
    assert!(matches!(
        branch.pattern.term.kind(),
        TermKind::DomainValue { value, .. } if value.as_ref() == "20"
    ));
    assert!(branch.pattern.constraints.contains(&trivial[0].remainder));
}

#[test]
fn trivial_only_sequence_with_a_satisfiable_remainder_is_not_bottom() {
    let definition = symbolic_trivial_definition(false);
    let initial = symbolic_subject(&definition);
    let solver = indeterminate_sat_solver();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        trivial,
        ..
    } = rewrite_step_sequential_with_solver(&definition, &initial, &mut fresh, &solver)
    else {
        panic!("the uncovered symbolic remainder must remain live");
    };
    assert!(branches.is_empty());
    assert_eq!(trivial.len(), 1);
    assert!(
        remainder
            .pattern
            .constraints
            .contains(&trivial[0].remainder)
    );
}

#[test]
fn reports_vacuous_execution_paths() {
    let definition = definition("");
    let subject = Pattern {
        term: internal_term(&definition, r#"wrap{}(\dv{SortS{}}("start"))"#),
        constraints: vec![Predicate::False],
    };
    let mut fresh = 0;

    assert_eq!(
        rewrite_step(&definition, &subject, &mut fresh),
        RewriteResult::Vacuous(subject.clone())
    );
    let execution = execute(&definition, subject, ExecutionOptions::default());
    assert!(matches!(
        execution.leaves.as_slice(),
        [ExecutionLeaf {
            depth: 0,
            halt_reason: HaltReason::Vacuous,
            ..
        }]
    ));
}

#[test]
fn input_substitution_contradictions_are_checked_after_the_first_rewrite_attempt() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                symbol b{}() : SortState{} [constructor{}()]
                symbol d{}() : SortState{} [constructor{}()]
                hooked-symbol intEq{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq")]
                hooked-symbol intNe{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.ne")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(b{}(), \top{SortState{}}()),
                    d{}()
                ) [label{}("step")]
            endmodule []"#,
    )
    .unwrap();
    let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
    let pattern = |state: &str| {
        let syntax = parse_pattern(&format!(
            r#"\and{{SortState{{}}}}(
                    {state}{{}}(),
                    \and{{SortState{{}}}}(
                        \equals{{SortBool{{}}, SortState{{}}}}(
                            intEq{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
                            \dv{{SortBool{{}}}}("true")
                        ),
                        \equals{{SortBool{{}}, SortState{{}}}}(
                            intNe{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
                            \dv{{SortBool{{}}}}("true")
                        )
                    )
                )"#
        ))
        .unwrap();
        definition.internalize_pattern(&syntax, &[]).unwrap()
    };

    let rewritten = execute(&definition, pattern("b"), ExecutionOptions::default());
    let stuck = execute(&definition, pattern("d"), ExecutionOptions::default());

    assert!(matches!(
        rewritten.leaves.as_slice(),
        [ExecutionLeaf {
            pattern: Pattern { term, constraints },
            depth: 1,
            halt_reason: HaltReason::Vacuous,
            ..
        }] if term == &internal_term(&definition, "d{}()")
            && constraints.iter().any(|predicate| matches!(predicate, Predicate::False))
    ));
    assert!(matches!(
        stuck.leaves.as_slice(),
        [ExecutionLeaf {
            depth: 0,
            halt_reason: HaltReason::Vacuous,
            ..
        }]
    ));
}

fn symbolic_remainder_definition(rules: &str) -> BackendDefinition {
    let source = r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol wrap{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol pair{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol partial{}(SortInt{}) : SortInt{} [function{}()]
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                $RULES
            endmodule []"#
        .replace("$RULES", rules);
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn symbolic_subject(definition: &BackendDefinition) -> Pattern {
    Pattern {
        term: definition
            .internalize_term(&parse_pattern("wrap{}(X:SortInt{})").unwrap(), &[])
            .unwrap(),
        constraints: Vec::new(),
    }
}

fn rewritten_value(result: RewriteResult) -> String {
    let RewriteResult::Finished(applied) = result else {
        panic!("expected finished rewrite, found {result:?}");
    };
    let TermKind::DomainValue { value, .. } = applied.pattern.term.kind() else {
        panic!("expected domain value, found {:?}", applied.pattern.term);
    };
    value.to_string()
}

#[test]
fn tries_priority_groups_in_ascending_numeric_order() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("zero")), \top{SortS{}}()),
                \dv{SortS{}}("high")
            ) [label{}("high"), priority{}("10")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("low")
            ) [label{}("low"), priority{}("50")]
            "#,
    );
    let mut fresh = 0;

    assert_eq!(
        rewritten_value(rewrite_step(
            &definition,
            &subject(&definition, "zero"),
            &mut fresh,
        )),
        "high"
    );
    assert_eq!(
        rewritten_value(rewrite_step(
            &definition,
            &subject(&definition, "one"),
            &mut fresh,
        )),
        "low"
    );
}

#[test]
fn applies_rules_with_top_level_alias_binders() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortS{}), Whole:SortS{}),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("aliased")]
            "#,
    );
    let mut fresh = 0;

    assert_eq!(
        rewritten_value(rewrite_step(
            &definition,
            &subject(&definition, "value"),
            &mut fresh,
        )),
        "done"
    );
}

#[test]
fn retries_function_pattern_remainders_after_simplification() {
    let definition = definition(
        r#"
            symbol identity{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    identity{}(X:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("identity"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(identity{}(X:SortS{})),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("function-pattern")]
            "#,
    );
    let mut fresh = 0;

    assert_eq!(
        rewritten_value(rewrite_step(
            &definition,
            &subject(&definition, "value"),
            &mut fresh,
        )),
        "done"
    );
}

#[test]
fn simplifies_configuration_functions_after_partial_matching() {
    let definition = definition(
        r#"
            symbol pair{}(SortS{}, SortS{}) : SortS{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            symbol identity{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    identity{}(X:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("identity"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    pair{}(X:SortS{}, X:SortS{}),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("repeated-variable")]
            "#,
    );
    let value = r#"\dv{SortS{}}("value")"#;
    let pattern = Pattern {
        term: internal_term(
            &definition,
            &format!("pair{{}}({value}, identity{{}}({value}))"),
        ),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    assert_eq!(
        rewritten_value(rewrite_step(&definition, &pattern, &mut fresh)),
        "done"
    );
}

#[cfg(feature = "z3")]
#[test]
fn narrows_configuration_variables_from_repeated_rule_variables() {
    let definition = definition(
        r#"
            sort SortTerm{} []
            symbol pair{}(SortTerm{}, SortTerm{}) : SortTerm{} [constructor{}()]
            symbol arrow{}(SortTerm{}, SortTerm{}) : SortTerm{} [constructor{}()]
            symbol done{}() : SortTerm{} [constructor{}()]
            axiom{} \rewrites{SortTerm{}}(
                \and{SortTerm{}}(
                    pair{}(T:SortTerm{}, T:SortTerm{}),
                    \top{SortTerm{}}()
                ),
                done{}()
            ) [label{}("repeated-variable")]
            "#,
    );
    let configuration = Pattern {
        term: internal_term(
            &definition,
            "pair{}(X:SortTerm{}, arrow{}(Y:SortTerm{}, Z:SortTerm{}))",
        ),
        constraints: Vec::new(),
    };
    let expected_variable = internal_term(&definition, "X:SortTerm{}");
    let expected_value = internal_term(&definition, "arrow{}(Y:SortTerm{}, Z:SortTerm{})");
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch { branches, .. } =
        rewrite_step_with_solver(&definition, &configuration, &mut fresh, &solver)
    else {
        panic!("repeated-variable unification should narrow the configuration");
    };
    let [applied] = branches.as_slice() else {
        panic!("expected one narrowed application, found {branches:?}");
    };
    assert!(matches!(
        applied.pattern.term.kind(),
        TermKind::Application { symbol, .. } if symbol.name.as_ref() == "done"
    ));
    assert!(
        applied
            .pattern
            .constraints
            .contains(&Predicate::Equals(expected_variable, expected_value,))
    );
}

#[cfg(feature = "z3")]
#[test]
fn retains_conditions_from_configuration_function_simplification() {
    let definition = definition(
        r#"
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            sort SortPair{} []
            symbol pair{}(SortS{}, SortS{}) : SortPair{} [constructor{}()]
            symbol done{}() : SortPair{} [constructor{}()]
            symbol constrained{}(SortS{}) : SortS{} [function{}(), total{}()]
            symbol predicate{}(SortS{}) : SortBool{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    constrained{}(X:SortS{}),
                    \and{SortS{}}(
                        X:SortS{},
                        \equals{SortBool{}, SortS{}}(
                            predicate{}(X:SortS{}),
                            \dv{SortBool{}}("true")
                        )
                    )
                )
            ) [label{}("constrained"), simplification{}()]
            axiom{} \rewrites{SortPair{}}(
                \and{SortPair{}}(
                    pair{}(X:SortS{}, X:SortS{}),
                    \top{SortPair{}}()
                ),
                done{}()
            ) [label{}("repeated-variable")]
            "#,
    );
    let value = r#"\dv{SortS{}}("value")"#;
    let pattern = Pattern {
        term: internal_term(
            &definition,
            &format!("pair{{}}({value}, constrained{{}}({value}))"),
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(_),
        ..
    } = rewrite_step_with_solver(&definition, &pattern, &mut fresh, &solver)
    else {
        panic!("a constrained simplification should retain applied and remainder branches");
    };
    let [branch] = branches.as_slice() else {
        panic!("expected one constrained rewrite branch, found {branches:?}");
    };
    assert_eq!(branch.pattern.term, internal_term(&definition, "done{}()"));
    assert!(matches!(
        branch.pattern.constraints.as_slice(),
        [Predicate::Term(..)]
    ));
}

#[test]
fn unresolved_function_equality_requires_an_smt_solver() {
    let definition = unresolved_function_rewrite_definition();
    let term = definition
        .internalize_term(
            &parse_pattern(r#"wrap{}(\dv{SortBool{}}("true"))"#).unwrap(),
            &[],
        )
        .unwrap();
    let mut fresh = 0;

    assert!(matches!(
        rewrite_step(
            &definition,
            &Pattern {
                term,
                constraints: Vec::new(),
            },
            &mut fresh,
        ),
        RewriteResult::Indeterminate {
            reason: IndeterminateReason::Smt {
                error: SmtError::Unavailable,
                ..
            },
            ..
        }
    ));
}

#[test]
fn rigid_no_evaluators_equality_reports_smt_indeterminacy_without_a_solver() {
    let definition = rigid_no_evaluators_rewrite_definition();
    let pattern = Pattern {
        term: internal_term(&definition, "state{}(opaque{}(N:SortInt{}))"),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    assert!(matches!(
        rewrite_step(&definition, &pattern, &mut fresh),
        RewriteResult::Indeterminate {
            reason: IndeterminateReason::Smt {
                error: SmtError::Unavailable,
                ..
            },
            ..
        }
    ));
}

#[test]
fn rigid_no_evaluators_equality_is_an_applied_and_complementary_condition() {
    let definition = rigid_no_evaluators_rewrite_definition();
    let pattern = Pattern {
        term: internal_term(&definition, "state{}(opaque{}(N:SortInt{}))"),
        constraints: Vec::new(),
    };
    let solver = FixedSolver {
        satisfiability: Ok(Satisfiability::Sat),
        validity: Ok(Validity::Indeterminate),
    };
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &pattern, &mut fresh, &solver)
    else {
        panic!("the rigid/function pair should narrow into a branch and remainder");
    };
    let [applied] = branches.as_slice() else {
        panic!("expected one conditional application, found {branches:?}");
    };
    assert_eq!(applied.pattern.term, internal_term(&definition, "done{}()"));
    let [condition @ Predicate::Equals(left, right)] = applied.pattern.constraints.as_slice()
    else {
        panic!("expected the function equality on the applied branch");
    };
    assert_eq!(left, &internal_term(&definition, r#"\dv{SortInt{}}("0")"#));
    assert_eq!(right, &internal_term(&definition, "opaque{}(N:SortInt{})"));
    assert_eq!(
        remainder.pattern.constraints,
        vec![Predicate::Not(Box::new(condition.clone()))]
    );

    let mut fresh = 0;
    assert!(matches!(
        rewrite_step_with_solver(&definition, &remainder.pattern, &mut fresh, &solver),
        RewriteResult::Stuck(_)
    ));
}

#[test]
fn solver_refutes_a_rigid_no_evaluators_function_equality() {
    let definition = rigid_no_evaluators_rewrite_definition();
    let pattern = Pattern {
        term: internal_term(&definition, "state{}(opaque{}(N:SortInt{}))"),
        constraints: Vec::new(),
    };
    let solver = FixedSolver {
        satisfiability: Ok(Satisfiability::Unsat),
        validity: Ok(Validity::Indeterminate),
    };
    let mut fresh = 0;

    assert!(matches!(
        rewrite_step_with_solver(&definition, &pattern, &mut fresh, &solver),
        RewriteResult::Stuck(_)
    ));
}

#[cfg(feature = "z3")]
#[test]
fn retains_unresolved_function_equality_as_a_branch_condition() {
    let definition = unresolved_function_rewrite_definition();
    let term = internal_term(&definition, r#"wrap{}(\dv{SortBool{}}("true"))"#);
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(
        &definition,
        &Pattern {
            term,
            constraints: Vec::new(),
        },
        &mut fresh,
        &solver,
    )
    else {
        panic!("functional equality should produce applied and complementary branches");
    };
    let [branch] = branches.as_slice() else {
        panic!("expected one conditional function match, found {branches:?}");
    };
    let [condition @ Predicate::Term(term)] = branch.pattern.constraints.as_slice() else {
        panic!("expected one functional Boolean condition");
    };
    assert!(matches!(
        term.kind(),
        TermKind::Application { symbol, .. } if symbol.name.as_ref() == "not"
    ));
    let fresh_variables = condition.free_variables();
    let mut fresh_variables = fresh_variables.iter();
    let fresh_variable = fresh_variables
        .next()
        .expect("the unbound rule argument should be freshened");
    assert!(fresh_variables.next().is_none());
    assert!(fresh_variable.name.starts_with("Ex#X"));
    assert!(matches!(
        remainder.pattern.constraints.as_slice(),
        [Predicate::Not(inner)]
            if matches!(inner.as_ref(), Predicate::Exists(variable, quantified)
                if variable == fresh_variable && quantified.as_ref() == condition)
    ));
}

#[test]
fn simplifies_rule_conditions_with_backend_equations_before_rewriting() {
    let definition = definition(
        r#"
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            symbol isZero{}(SortS{}) : SortBool{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortBool{}, R}(
                    isZero{}(\dv{SortS{}}("zero")),
                    \and{SortBool{}}(
                        \dv{SortBool{}}("true"),
                        \top{SortBool{}}()
                    )
                )
            ) [label{}("zero-is-zero"), simplification{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortBool{}, R}(
                    isZero{}(\dv{SortS{}}("one")),
                    \and{SortBool{}}(
                        \dv{SortBool{}}("false"),
                        \top{SortBool{}}()
                    )
                )
            ) [label{}("one-is-not-zero"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \equals{SortBool{}, SortS{}}(
                        isZero{}(X:SortS{}),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortS{}}("high")
            ) [label{}("conditional"), priority{}("10")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("fallback")
            ) [label{}("fallback"), priority{}("50")]
            "#,
    );
    let mut fresh = 0;

    assert_eq!(
        rewritten_value(rewrite_step(
            &definition,
            &subject(&definition, "zero"),
            &mut fresh,
        )),
        "high"
    );
    assert_eq!(
        rewritten_value(rewrite_step(
            &definition,
            &subject(&definition, "one"),
            &mut fresh,
        )),
        "fallback"
    );
}

#[test]
fn aborts_before_lower_priorities_when_requires_are_unknown() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \equals{SortS{}, SortS{}}(X:SortS{}, \dv{SortS{}}("zero"))
                ),
                \dv{SortS{}}("conditional")
            ) [label{}("conditional"), priority{}("10")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("fallback")
            ) [label{}("fallback"), priority{}("50")]
            "#,
    );
    let syntax = parse_pattern("wrap{}(Y:SortS{})").unwrap();
    let pattern = Pattern {
        term: definition.internalize_term(&syntax, &[]).unwrap(),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    assert!(matches!(
        rewrite_step(&definition, &pattern, &mut fresh),
        RewriteResult::Indeterminate {
            reason: IndeterminateReason::Requires { rule_id, .. },
            ..
        } if rule_id == "conditional"
    ));
}

#[test]
fn false_requires_prune_a_rule_even_when_matching_is_indeterminate() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \bottom{SortS{}}()
                ),
                \dv{SortS{}}("unreachable")
            ) [label{}("false-requires")]
            "#,
    );
    let rule = definition
        .rewrite_theory
        .values()
        .flat_map(|groups| groups.values())
        .flatten()
        .next()
        .expect("rewrite rule should be indexed");
    let pattern = Pattern {
        term: rule.lhs.clone(),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    assert!(matches!(
        rewrite_step(&definition, &pattern, &mut fresh),
        RewriteResult::Stuck(_)
    ));
}

#[cfg(feature = "z3")]
#[test]
fn z3_proves_or_refutes_symbolic_requires_before_priority_fallback() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol wrap{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                axiom{} \rewrites{SortInt{}}(
                    \and{SortInt{}}(
                        wrap{}(X:SortInt{}),
                        \equals{SortBool{}, SortInt{}}(
                            lt{}(X:SortInt{}, \dv{SortInt{}}("10")),
                            \dv{SortBool{}}("true")
                        )
                    ),
                    \dv{SortInt{}}("10")
                ) [label{}("high"), priority{}("10")]
                axiom{} \rewrites{SortInt{}}(
                    \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
                    \dv{SortInt{}}("20")
                ) [label{}("fallback"), priority{}("50")]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let variable = Variable::new("Y", Sort::simple("SortInt"));
    let subject = definition
        .internalize_term(&parse_pattern("wrap{}(Y:SortInt{})").unwrap(), &[])
        .unwrap();
    let integer = |value: &str| Term::domain_value(Sort::simple("SortInt"), value);
    let run = |value: &str| {
        let pattern = Pattern {
            term: subject.clone(),
            constraints: vec![Predicate::Equals(
                Term::variable(variable.clone()),
                integer(value),
            )],
        };
        let mut fresh = 0;
        rewritten_value(rewrite_step_with_solver(
            &definition,
            &pattern,
            &mut fresh,
            &solver,
        ))
    };

    assert_eq!(run("5"), "10");
    assert_eq!(run("15"), "20");
}

#[cfg(feature = "z3")]
#[test]
fn preserves_a_satisfiable_remainder_from_one_symbolic_rule() {
    let definition = symbolic_remainder_definition(
        r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("-1")
            ) [label{}("negative")]
            "#,
    );
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(
        &definition,
        &symbolic_subject(&definition),
        &mut fresh,
        &solver,
    )
    else {
        panic!("a partial symbolic rule should retain its remainder branch");
    };
    assert_eq!(branches.len(), 1);
    assert_eq!(remainder.rule_ids, ["negative"]);
    assert_eq!(remainder.pattern.term, symbolic_subject(&definition).term);
    assert!(matches!(
        remainder.pattern.constraints.as_slice(),
        [Predicate::Not(_)]
    ));
}

#[cfg(feature = "z3")]
#[test]
fn stopping_at_a_symbolic_branch_preserves_its_remainder() {
    let definition = symbolic_remainder_definition(
        r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("-1")
            ) [label{}("negative")]
            "#,
    );
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();

    let result = execute_with_solver(
        &definition,
        symbolic_subject(&definition),
        ExecutionOptions {
            branch_mode: ExecutionBranchMode::StopAtBranch,
            ..ExecutionOptions::default()
        },
        &solver,
    );

    let [
        ExecutionLeaf {
            halt_reason:
                HaltReason::Branch {
                    branches,
                    remainder: Some(remainder),
                },
            ..
        },
    ] = result.leaves.as_slice()
    else {
        panic!("expected an applied branch and its symbolic remainder");
    };
    assert_eq!(branches.len(), 1);
    assert_eq!(remainder.rule_ids, ["negative"]);
    assert!(matches!(
        remainder.pattern.constraints.as_slice(),
        [Predicate::Not(_)]
    ));
}

#[cfg(feature = "z3")]
#[test]
fn stopping_at_a_branch_expands_remainders_through_lower_priorities() {
    let definition = symbolic_remainder_definition(
        r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("-1")
            ) [label{}("negative"), priority{}("10")]
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(\dv{SortInt{}}("0"), X:SortInt{}),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("1")
            ) [label{}("positive"), priority{}("10")]
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
                \dv{SortInt{}}("2")
            ) [label{}("zero-a"), priority{}("50")]
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
                \dv{SortInt{}}("3")
            ) [label{}("zero-b"), priority{}("50")]
            "#,
    );
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();

    let result = execute_with_solver(
        &definition,
        symbolic_subject(&definition),
        ExecutionOptions {
            branch_mode: ExecutionBranchMode::StopAtBranch,
            ..ExecutionOptions::default()
        },
        &solver,
    );

    let [
        ExecutionLeaf {
            halt_reason:
                HaltReason::Branch {
                    branches,
                    remainder: None,
                },
            ..
        },
    ] = result.leaves.as_slice()
    else {
        panic!("expected every priority branch and no uncovered remainder");
    };
    let mut labels = branches
        .iter()
        .map(|branch| branch.label.as_deref().unwrap())
        .collect::<Vec<_>>();
    labels.sort_unstable();
    assert_eq!(labels, ["negative", "positive", "zero-a", "zero-b"]);
}

#[cfg(feature = "z3")]
#[test]
fn carries_a_symbolic_remainder_to_lower_priority_rules() {
    let definition = symbolic_remainder_definition(
        r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("-1")
            ) [label{}("negative"), priority{}("10")]
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
                \dv{SortInt{}}("20")
            ) [label{}("fallback"), priority{}("50")]
            "#,
    );
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();

    let result = execute_with_solver(
        &definition,
        symbolic_subject(&definition),
        ExecutionOptions {
            max_depth: 1,
            ..ExecutionOptions::default()
        },
        &solver,
    );

    let mut values = result
        .leaves
        .iter()
        .map(|leaf| {
            let TermKind::DomainValue { value, .. } = leaf.pattern.term.kind() else {
                panic!(
                    "expected rewritten domain value, found {:?}",
                    leaf.pattern.term
                );
            };
            value.to_string()
        })
        .collect::<Vec<_>>();
    values.sort();
    assert_eq!(values, ["-1", "20"]);
    assert!(result.leaves.iter().any(|leaf| {
        leaf.trace
            .iter()
            .any(|entry| entry.kind == TraceKind::Remainder)
    }));
}

#[cfg(feature = "z3")]
#[test]
fn narrows_a_ground_rule_fragment_over_a_symbolic_configuration() {
    let definition = symbolic_remainder_definition(
        r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(\dv{SortInt{}}("0")),
                    \top{SortInt{}}()
                ),
                \dv{SortInt{}}("0")
            ) [label{}("zero")]
            "#,
    );
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let subject = symbolic_subject(&definition);
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("ground narrowing should produce an applied and a remaining branch");
    };

    assert_eq!(branches.len(), 1);
    assert!(matches!(
        branches[0].pattern.constraints.as_slice(),
        [Predicate::Equals(left, right)]
            if matches!(left.kind(), TermKind::Variable(_))
                && matches!(right.kind(), TermKind::DomainValue { value, .. } if value.as_ref() == "0")
    ));
    assert!(matches!(
        remainder.pattern.constraints.as_slice(),
        [Predicate::Not(inner)]
            if matches!(inner.as_ref(), Predicate::Equals(_, _))
    ));
}

#[cfg(feature = "z3")]
#[test]
fn narrows_a_constructor_pattern_with_fresh_rule_variables() {
    let definition = symbolic_remainder_definition(
        r#"
            sort SortNarrow{} []
            symbol narrowZero{}() : SortNarrow{} [constructor{}()]
            symbol narrowPair{}(SortNarrow{}, SortNarrow{}) : SortNarrow{} [constructor{}()]
            symbol narrowWrap{}(SortNarrow{}) : SortNarrow{} [constructor{}()]
            axiom{} \rewrites{SortNarrow{}}(
                \and{SortNarrow{}}(
                    narrowWrap{}(
                        narrowPair{}(
                            X:SortNarrow{},
                            narrowZero{}()
                        )
                    ),
                    \top{SortNarrow{}}()
                ),
                X:SortNarrow{}
            ) [label{}("destructure")]
            "#,
    );
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let subject = Pattern {
        term: internal_term(&definition, "narrowWrap{}(X:SortNarrow{})"),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("constructor narrowing should produce applied and complementary branches");
    };

    let [branch] = branches.as_slice() else {
        panic!("expected one applied branch, found {branches:?}");
    };
    let TermKind::Variable(result_variable) = branch.pattern.term.kind() else {
        panic!(
            "expected the fresh component variable, found {:?}",
            branch.pattern.term
        );
    };
    let [Predicate::Equals(configuration, constructor)] = branch.pattern.constraints.as_slice()
    else {
        panic!(
            "expected one narrowing equality, found {:?}",
            branch.pattern.constraints
        );
    };
    assert!(
        matches!(configuration.kind(), TermKind::Variable(variable) if variable.name.as_ref() == "X")
    );
    let TermKind::Application {
        symbol, arguments, ..
    } = constructor.kind()
    else {
        panic!("expected constructor pattern, found {constructor:?}");
    };
    assert_eq!(symbol.name.as_ref(), "narrowPair");
    assert!(
        matches!(arguments[0].kind(), TermKind::Variable(variable) if variable == result_variable)
    );
    assert!(
        matches!(arguments[1].kind(), TermKind::Application { symbol, .. }
                if symbol.name.as_ref() == "narrowZero")
    );
    assert_ne!(result_variable.name.as_ref(), "Rule#X");
    let first_name = result_variable.name.clone();
    assert_eq!(fresh, 1);
    let [Predicate::Not(remainder_condition)] = remainder.pattern.constraints.as_slice() else {
        panic!(
            "expected a negated remainder, found {:?}",
            remainder.pattern.constraints
        );
    };
    let Predicate::Exists(remainder_variable, remainder_condition) = remainder_condition.as_ref()
    else {
        panic!("fresh narrowing variables must be existential in the remainder");
    };
    assert_eq!(remainder_variable, result_variable);
    assert_eq!(
        remainder_condition.as_ref(),
        &Predicate::Equals(configuration.clone(), constructor.clone())
    );

    let RewriteResult::Branch {
        branches: second, ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("repeated constructor narrowing should still apply");
    };
    assert!(matches!(
        second[0].pattern.term.kind(),
        TermKind::Variable(variable) if variable.name != first_name
    ));
    assert_eq!(fresh, 2);
}

#[cfg(feature = "z3")]
#[test]
fn narrows_a_function_pattern_with_a_definedness_condition() {
    let definition = symbolic_remainder_definition(
        r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(partial{}(X:SortInt{})),
                    \top{SortInt{}}()
                ),
                X:SortInt{}
            ) [label{}("partial-destructure")]
            "#,
    );
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let subject = symbolic_subject(&definition);
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("functional narrowing should produce applied and complementary branches");
    };

    let [branch] = branches.as_slice() else {
        panic!("expected one applied branch, found {branches:?}");
    };
    let TermKind::Variable(result_variable) = branch.pattern.term.kind() else {
        panic!(
            "expected a fresh function argument, found {:?}",
            branch.pattern.term
        );
    };
    assert!(result_variable.name.starts_with("Ex#"));
    let [
        Predicate::Equals(configuration, function),
        Predicate::Ceil(defined),
    ] = branch.pattern.constraints.as_slice()
    else {
        panic!(
            "expected equality and definedness, found {:?}",
            branch.pattern.constraints
        );
    };
    assert_eq!(function, defined);
    assert!(
        matches!(configuration.kind(), TermKind::Variable(variable) if variable.name.as_ref() == "X")
    );
    assert!(matches!(
        function.kind(),
        TermKind::Application { symbol, arguments, .. }
            if symbol.name.as_ref() == "partial"
                && matches!(arguments[0].kind(), TermKind::Variable(variable) if variable == result_variable)
    ));

    let [Predicate::Not(remainder_condition)] = remainder.pattern.constraints.as_slice() else {
        panic!("expected a negated complementary condition");
    };
    assert!(matches!(
        remainder_condition.as_ref(),
        Predicate::Exists(variable, body)
            if variable == result_variable
                && matches!(body.as_ref(), Predicate::And(predicates) if predicates == branch.pattern.constraints.as_slice())
    ));
}

#[cfg(feature = "z3")]
#[test]
fn branches_only_after_complementary_rules_make_the_remainder_unsatisfiable() {
    let definition = symbolic_remainder_definition(
        r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("-1")
            ) [label{}("negative")]
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("false")
                    )
                ),
                \dv{SortInt{}}("1")
            ) [label{}("nonnegative")]
            "#,
    );
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch { branches, .. } = rewrite_step_with_solver(
        &definition,
        &symbolic_subject(&definition),
        &mut fresh,
        &solver,
    ) else {
        panic!("complementary rules should form a complete branch");
    };
    assert_eq!(
        branches
            .iter()
            .map(|branch| branch.label.as_deref().unwrap())
            .collect::<Vec<_>>(),
        ["negative", "nonnegative"]
    );
    assert!(
        branches
            .iter()
            .all(|branch| branch.pattern.constraints.len() == 1)
    );
}

#[test]
fn branches_when_multiple_rules_in_one_priority_apply() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("left")
            ) [label{}("left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("right")
            ) [label{}("right")]
            "#,
    );
    let mut fresh = 0;

    let RewriteResult::Branch { branches, .. } =
        rewrite_step(&definition, &subject(&definition, "value"), &mut fresh)
    else {
        panic!("both rules should branch");
    };
    assert_eq!(
        branches
            .iter()
            .map(|branch| branch.label.as_deref().unwrap())
            .collect::<Vec<_>>(),
        vec!["left", "right"]
    );
}

#[test]
fn any_mode_uses_declaration_order_within_a_priority() {
    let heat = r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(injectiveFunction{}(X:SortS{})),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("heat")
            ) [label{}("heat")]
        "#;
    let lookup = r#"
             axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(\dv{SortS{}}("value")),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("lookup")
            ) [label{}("lookup")]
        "#;

    // Equal priority: rules are tried in declaration order. Declared first, lookup consumes
    // the whole subject and heat is never tried; declared second, it only reaches the
    // remainder of heat's indeterminate application.
    let solver = FixedSolver {
        satisfiability: Ok(Satisfiability::Sat),
        validity: Ok(Validity::Indeterminate),
    };

    let lookup_first = definition(&format!("{lookup}{heat}"));
    let mut fresh = 0;
    let result = rewrite_step_sequential_with_solver(
        &lookup_first,
        &subject(&lookup_first, "value"),
        &mut fresh,
        &solver,
    );
    let RewriteResult::Finished(application) = result else {
        panic!("lookup should consume the whole subject before heat: {result:?}");
    };
    assert_eq!(application.label.as_deref(), Some("lookup"));
    assert!(application.pattern.constraints.is_empty());
    assert_eq!(
        application.pattern.term,
        internal_term(&lookup_first, r#"\dv{SortS{}}("lookup")"#)
    );

    let heat_first = definition(&format!("{heat}{lookup}"));
    let mut fresh = 0;
    let result = rewrite_step_sequential_with_solver(
        &heat_first,
        &subject(&heat_first, "value"),
        &mut fresh,
        &solver,
    );
    let RewriteResult::Branch { branches, .. } = &result else {
        panic!("heat is tried first and its indeterminate application branches: {result:?}");
    };
    assert_eq!(
        branches
            .iter()
            .map(|branch| branch.label.as_deref().unwrap())
            .collect::<Vec<_>>(),
        ["heat", "lookup"]
    );
}

#[test]
fn explicit_rewrite_order_precedes_a_trivial_fallback() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortValue{} []
                sort SortState{} []
                symbol target{}() : SortValue{} [constructor{}()]
                symbol state{}(SortValue{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]

                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(X:SortValue{}),
                        \top{SortState{}}()
                    ),
                    \bottom{SortState{}}()
                ) [label{}("late-generic"), UNIQUE'Unds'ID{}("late-generic")]

                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(target{}()),
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("early-specific"), UNIQUE'Unds'ID{}("early-specific")]
            endmodule []"#,
    )
    .expect("definition should parse");
    let definition = BackendDefinition::internalize_for_source_execution(
        &syntax,
        "MAIN",
        &["early-specific", "late-generic"],
    )
    .expect("definition should internalize");
    let initial = Pattern {
        term: internal_term(&definition, "state{}(target{}())"),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let result = rewrite_step_sequential_with_solver(&definition, &initial, &mut fresh, &NoSolver);

    let RewriteResult::Finished(applied) = result else {
        panic!("the explicit earlier rewrite must precede the trivial fallback: {result:?}");
    };
    assert_eq!(applied.unique_id, "early-specific");
    assert_eq!(applied.label.as_deref(), Some("early-specific"));
    assert_eq!(applied.pattern.term, internal_term(&definition, "done{}()"));
}

#[test]
fn freshens_existentials_against_the_current_pattern() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \exists{SortS{}}(Y:SortS{}, wrap{}(Y:SortS{}))
            ) [label{}("fresh")]
            "#,
    );
    let pattern = subject(&definition, "value");
    let mut fresh = 0;
    let first = rewrite_step(&definition, &pattern, &mut fresh);
    let first_name = match &first {
        RewriteResult::Finished(applied) => applied
            .pattern
            .term
            .attributes()
            .variables
            .iter()
            .next()
            .unwrap()
            .name
            .clone(),
        _ => panic!("rule should apply"),
    };
    assert_eq!(first_name.as_ref(), "Y");

    let RewriteResult::Finished(first) = first else {
        unreachable!();
    };
    let second = rewrite_step(&definition, &first.pattern, &mut fresh);
    let second_name = match second {
        RewriteResult::Finished(applied) => {
            let variables = &applied.pattern.term.attributes().variables;
            assert_eq!(variables.len(), 1);
            variables.iter().next().unwrap().name.clone()
        }
        _ => panic!("rule should apply again"),
    };
    assert_eq!(second_name.as_ref(), "Y0");

    let repeated = rewrite_step(&definition, &pattern, &mut fresh);
    let repeated_name = match repeated {
        RewriteResult::Finished(applied) => {
            let variables = &applied.pattern.term.attributes().variables;
            assert_eq!(variables.len(), 1);
            variables.iter().next().unwrap().name.clone()
        }
        _ => panic!("rule should apply to the original pattern again"),
    };
    assert_eq!(repeated_name, first_name);
}

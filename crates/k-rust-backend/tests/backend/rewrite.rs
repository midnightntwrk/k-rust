//! Public contracts of `k_rust_backend::rewrite`.

use std::{collections::BTreeSet, time::Duration};

use k_rust_backend::{
    builtin::BuiltinEffect,
    cancellation::CancellationToken,
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic},
    rewrite::*,
    rule::Predicate,
    simplify::{
        BudgetSubject, DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError,
        SimplificationOptions,
    },
    smt::{NoSolver, Satisfiability, SmtError, SmtSolver, Validity},
    substitution::Substitution,
    term::{Sort, Term, TermKind},
    timeout::StepTimeoutMode,
    transition::{
        ObservationEvent, ObservationFilterError, ObservationOptions, PatternDigest,
        TransitionClass, UncommittedReason,
    },
};
#[cfg(feature = "z3")]
use k_rust_backend::{substitution::substitute, term::Variable};
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

fn set_selection_definition() -> BackendDefinition {
    let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortElement{} [hasDomainValues{}()]
                hooked-sort SortSet{}
                    [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
                sort SortState{} []
                hooked-symbol setUnit{}() : SortSet{}
                    [function{}(), total{}(), hook{}("SET.unit")]
                hooked-symbol setItem{}(SortElement{}) : SortSet{}
                    [function{}(), total{}(), hook{}("SET.element")]
                hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{}
                    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
                symbol state{}(SortSet{}) : SortState{} [constructor{}()]
                symbol picked{}(SortElement{}, SortSet{}) : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(setConcat{}(setItem{}(ELEMENT:SortElement{}), REST:SortSet{})),
                        \top{SortState{}}()
                    ),
                    picked{}(ELEMENT:SortElement{}, REST:SortSet{})
                ) [label{}("select")]
            endmodule []"#,
        )
        .expect("set definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("set definition should internalize")
}

#[cfg(feature = "z3")]
fn closed_collection_frame_definition() -> BackendDefinition {
    let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortElement{} [hasDomainValues{}()]
                hooked-sort SortList{}
                    [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
                hooked-sort SortSet{}
                    [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
                sort SortListState{} []
                sort SortSetState{} []
                hooked-symbol listUnit{}() : SortList{}
                    [function{}(), total{}(), hook{}("LIST.unit")]
                hooked-symbol listItem{}(SortElement{}) : SortList{}
                    [function{}(), total{}(), hook{}("LIST.element")]
                hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
                    [function{}(), hook{}("LIST.concat"), assoc{}()]
                hooked-symbol setUnit{}() : SortSet{}
                    [function{}(), total{}(), hook{}("SET.unit")]
                hooked-symbol setItem{}(SortElement{}) : SortSet{}
                    [function{}(), total{}(), hook{}("SET.element")]
                hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{}
                    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
                symbol listState{}(SortList{}) : SortListState{} [constructor{}()]
                symbol listDone{}() : SortListState{} [constructor{}()]
                symbol setState{}(SortSet{}) : SortSetState{} [constructor{}()]
                symbol setDone{}() : SortSetState{} [constructor{}()]
                axiom{} \rewrites{SortListState{}}(
                    \and{SortListState{}}(
                        listState{}(
                            listItem{}(\dv{SortElement{}}("first"))
                        ),
                        \top{SortListState{}}()
                    ),
                    listDone{}()
                ) [label{}("closed-list")]
                axiom{} \rewrites{SortSetState{}}(
                    \and{SortSetState{}}(
                        setState{}(
                            setItem{}(\dv{SortElement{}}("first"))
                        ),
                        \top{SortSetState{}}()
                    ),
                    setDone{}()
                ) [label{}("closed-set")]
            endmodule []"#,
        )
        .expect("closed collection definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("closed collection definition should internalize")
}

fn opaque_set_narrowing_definition() -> BackendDefinition {
    let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortElement{} [hasDomainValues{}()]
                hooked-sort SortSet{}
                    [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
                sort SortState{} []
                hooked-symbol setUnit{}() : SortSet{}
                    [function{}(), total{}(), hook{}("SET.unit")]
                hooked-symbol setItem{}(SortElement{}) : SortSet{}
                    [function{}(), total{}(), hook{}("SET.element")]
                hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{}
                    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
                symbol opaqueA{}() : SortSet{} [function{}(), total{}()]
                symbol opaqueB{}() : SortSet{} [function{}(), total{}()]
                symbol state{}(SortSet{}) : SortState{} [constructor{}()]
                symbol selected{}(SortElement{}) : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(
                            setConcat{}(
                                setItem{}(RULE:SortElement{}),
                                setConcat{}(
                                    opaqueA{}(),
                                    setConcat{}(opaqueB{}(), opaqueB{}())
                                )
                            )
                        ),
                        \top{SortState{}}()
                    ),
                    selected{}(RULE:SortElement{})
                ) [label{}("opaque-set")]
            endmodule []"#,
        )
        .expect("opaque Set definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("opaque Set definition should internalize")
}

fn map_selection_definition() -> BackendDefinition {
    let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} [hasDomainValues{}()]
                sort SortValue{} [hasDomainValues{}()]
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                sort SortState{} []
                hooked-symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol mapState{}(SortMap{}) : SortState{} [constructor{}()]
                symbol mapPicked{}(SortKey{}, SortValue{}, SortMap{}) : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        mapState{}(
                            mapConcat{}(
                                mapItem{}(KEY:SortKey{}, VALUE:SortValue{}),
                                REST:SortMap{}
                            )
                        ),
                        \top{SortState{}}()
                    ),
                    mapPicked{}(KEY:SortKey{}, VALUE:SortValue{}, REST:SortMap{})
                ) [label{}("map-select")]
            endmodule []"#,
        )
        .expect("map definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("map definition should internalize")
}

fn closed_map_narrowing_definition() -> BackendDefinition {
    let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} [hasDomainValues{}()]
                sort SortValue{} [hasDomainValues{}()]
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                sort SortState{} []
                hooked-symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol mapState{}(SortMap{}) : SortState{} [constructor{}()]
                symbol mixedState{}(SortValue{}, SortMap{}) : SortState{} [constructor{}()]
                symbol select{}(SortValue{}) : SortValue{} [function{}(), total{}()]
                symbol done{}() : SortState{} [constructor{}()]
                symbol selected{}(SortValue{}) : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        mapState{}(
                            mapConcat{}(
                                mapItem{}(
                                    \dv{SortKey{}}("first"),
                                    \dv{SortValue{}}("first-value")
                                ),
                                mapItem{}(
                                    \dv{SortKey{}}("second"),
                                    \dv{SortValue{}}("second-value")
                                )
                            )
                        ),
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("closed-map")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        mixedState{}(
                            select{}(RULE:SortValue{}),
                            mapConcat{}(
                                mapItem{}(
                                    \dv{SortKey{}}("first"),
                                    \dv{SortValue{}}("first-value")
                                ),
                                mapItem{}(
                                    \dv{SortKey{}}("second"),
                                    \dv{SortValue{}}("second-value")
                                )
                            )
                        ),
                        \top{SortState{}}()
                    ),
                    selected{}(RULE:SortValue{})
                ) [label{}("mixed-unification")]
            endmodule []"#,
        )
        .expect("closed map definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("closed map definition should internalize")
}

fn symbolic_map_key_definition() -> BackendDefinition {
    let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} [hasDomainValues{}()]
                sort SortValue{} [hasDomainValues{}()]
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                sort SortState{} []
                hooked-symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol mapState{}(SortMap{}) : SortState{} [constructor{}()]
                symbol mapPicked{}(SortValue{}, SortMap{}) : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        mapState{}(
                            mapConcat{}(
                                mapItem{}(\dv{SortKey{}}("wanted"), VALUE:SortValue{}),
                                REST:SortMap{}
                            )
                        ),
                        \top{SortState{}}()
                    ),
                    mapPicked{}(VALUE:SortValue{}, REST:SortMap{})
                ) [label{}("select-wanted")]
            endmodule []"#,
        )
        .expect("symbolic map-key definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("symbolic map-key definition should internalize")
}

fn shared_symbolic_map_key_definition() -> BackendDefinition {
    let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} []
                sort SortValue{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                sort SortState{} []
                hooked-symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol request{}(SortMap{}, SortKey{}) : SortState{} [constructor{}()]
                symbol exact{}() : SortState{} [constructor{}()]
                symbol different{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        request{}(
                            mapConcat{}(
                                mapItem{}(KEY:SortKey{}, VALUE:SortValue{}),
                                REST:SortMap{}
                            ),
                            KEY:SortKey{}
                        ),
                        \top{SortState{}}()
                    ),
                    exact{}()
                ) [label{}("exact")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        request{}(
                            mapConcat{}(
                                mapItem{}(ENTRY:SortKey{}, VALUE:SortValue{}),
                                REST:SortMap{}
                            ),
                            REQUESTED:SortKey{}
                        ),
                        \not{SortState{}}(
                            \equals{SortKey{}, SortState{}}(
                                ENTRY:SortKey{},
                                REQUESTED:SortKey{}
                            )
                        )
                    ),
                    different{}()
                ) [label{}("different")]
            endmodule []"#,
        )
        .expect("shared symbolic map-key definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("shared symbolic map-key definition should internalize")
}

#[cfg(feature = "z3")]
fn map_not_in_keys_rewrite_definition() -> BackendDefinition {
    let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortKey{} []
                sort SortValue{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                sort SortState{} []
                hooked-symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                hooked-symbol inKeys{}(SortKey{}, SortMap{}) : SortBool{}
                    [function{}(), total{}(), hook{}("MAP.in_keys")]
                symbol state{}(SortBool{}, SortKey{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(
                            inKeys{}(
                                KEY:SortKey{},
                                mapConcat{}(
                                    mapItem{}(ENTRY:SortKey{}, VALUE:SortValue{}),
                                    REST:SortMap{}
                                )
                            ),
                            CONTEXT:SortKey{}
                        ),
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("not-in-keys")]
            endmodule []"#,
        )
        .expect("map not-in-keys definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("map not-in-keys definition should internalize")
}

fn overload_rewrite_definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortToken{} [hasDomainValues{}()]
                sort SortSub{} []
                sort SortTop{} []
                sort SortState{} []
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                symbol token{}(SortToken{}) : SortSub{} [constructor{}()]
                symbol lower{}(SortSub{}) : SortSub{} [constructor{}()]
                symbol upper{}(SortTop{}) : SortTop{} [constructor{}()]
                symbol overloadState{}(SortTop{}) : SortState{} [constructor{}()]
                symbol overloadResult{}(SortTop{}) : SortState{} [constructor{}()]
                axiom{R} \equals{SortTop{}, R}(
                    upper{}(X:SortTop{}),
                    inj{SortSub{}, SortTop{}}(lower{}(Y:SortSub{}))
                ) [symbol-overload{}(upper{}(), lower{}())]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        overloadState{}(upper{}(X:SortTop{})),
                        \top{SortState{}}()
                    ),
                    overloadResult{}(X:SortTop{})
                ) [label{}("overload-match")]
            endmodule []"#,
    )
    .expect("overload rewrite definition should parse");
    let mut definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("overload rewrite definition should internalize");
    definition
        .sort_graph
        .insert("SortTop", [k_rust_backend::term::Name::from("SortSub")]);
    definition
}

#[cfg(feature = "z3")]
fn ite_rewrite_definition(lhs: &str) -> BackendDefinition {
    let source = r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortValue{} []
                sort SortState{} []
                hooked-symbol ite{}(SortBool{}, SortValue{}, SortValue{}) : SortValue{}
                    [function{}(), total{}(), hook{}("KEQUAL.ite")]
                symbol chosen{}() : SortValue{} [constructor{}()]
                symbol rejected{}() : SortValue{} [constructor{}()]
                symbol state{}(SortValue{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        $LHS,
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("choose")]
            endmodule []"#
        .replace("$LHS", lhs);
    let syntax = parse_definition(&source).expect("ITE definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("ITE definition should internalize")
}

fn scalar_equality_rewrite_definition(
    equality_hook: &str,
    operand_sort: &str,
    sort_hook: &str,
) -> BackendDefinition {
    let source = r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort $SORT{} [hook{}("$SORT_HOOK"), hasDomainValues{}()]
                sort SortState{} []
                hooked-symbol equal{}($SORT{}, $SORT{}) : SortBool{}
                    [function{}(), total{}(), hook{}("$EQUALITY_HOOK")]
                symbol value{}() : $SORT{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol state{}(SortBool{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(equal{}(VALUE:$SORT{}, value{}())),
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("scalar-equality")]
            endmodule []"#
        .replace("$EQUALITY_HOOK", equality_hook)
        .replace("$SORT_HOOK", sort_hook)
        .replace("$SORT", operand_sort);
    let syntax = parse_definition(&source).expect("scalar equality definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("scalar equality definition should internalize")
}

fn boolean_rewrite_definition(lhs: &str) -> BackendDefinition {
    let source = r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortState{} []
                hooked-symbol and{}(SortBool{}, SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.and")]
                hooked-symbol or{}(SortBool{}, SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.or")]
                hooked-symbol not{}(SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.not")]
                symbol state{}(SortBool{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        $LHS,
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("boolean")]
            endmodule []"#
        .replace("$LHS", lhs);
    let syntax = parse_definition(&source).expect("Boolean definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("Boolean definition should internalize")
}

#[test]
fn executes_to_a_stuck_normal_form_and_records_the_trace() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("zero")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("one"))
            ) [label{}("first")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("one")), \top{SortS{}}()),
                \dv{SortS{}}("done")
            ) [label{}("second")]
            "#,
    );

    let result = execute(
        &definition,
        subject(&definition, "zero"),
        ExecutionOptions::default(),
    );
    assert_eq!(result.leaves.len(), 1);
    let leaf = &result.leaves[0];
    assert_eq!(leaf.depth, 2);
    assert_eq!(leaf.halt_reason, HaltReason::Stuck);
    assert_eq!(
        leaf.trace
            .iter()
            .map(|entry| (entry.depth, entry.label.as_deref().unwrap()))
            .collect::<Vec<_>>(),
        vec![(1, "first"), (2, "second")]
    );
    assert!(matches!(
        leaf.pattern.term.kind(),
        TermKind::DomainValue { value, .. } if value.as_ref() == "done"
    ));
}

fn assert_not_iteration_limit(reason: &HaltReason) {
    assert!(!matches!(
        reason,
        HaltReason::Simplification(
            SimplificationError::IterationLimit { .. }
                | SimplificationError::PredicateIterationLimit { .. }
        )
    ));
}

fn long_requires_chain() -> String {
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
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \equals{SortS{}, SortS{}}(
                        chain0{}(),
                        \dv{SortS{}}("done")
                    )
                ),
                \dv{SortS{}}("rewritten")
            ) [label{}("conditional")]
            "#,
    );
    theory
}

fn deep_concrete_recursion_definition() -> BackendDefinition {
    definition(
        r#"
            sort SortElement{} [hasDomainValues{}()]
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortList{}
                [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
            hooked-symbol listUnit{}() : SortList{}
                [function{}(), total{}(), hook{}("LIST.unit")]
            hooked-symbol listItem{}(SortElement{}) : SortList{}
                [function{}(), total{}(), hook{}("LIST.element")]
            hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
                [function{}(), hook{}("LIST.concat"), assoc{}()]
            hooked-symbol intAdd{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.add")]
            symbol size{}(SortList{}) : SortInt{} [function{}()]
            symbol stackState{}(SortList{}) : SortS{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortInt{}, R}(
                    size{}(listUnit{}()),
                    \and{SortInt{}}(
                        \dv{SortInt{}}("0"),
                        \top{SortInt{}}()
                    )
                )
            ) [label{}("size-unit"), simplification{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortInt{}, R}(
                    size{}(
                        listConcat{}(
                            listItem{}(Head:SortElement{}),
                            Tail:SortList{}
                        )
                    ),
                    \and{SortInt{}}(
                        intAdd{}(
                            \dv{SortInt{}}("1"),
                            size{}(Tail:SortList{})
                        ),
                        \top{SortInt{}}()
                    )
                )
            ) [label{}("size-cons"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    stackState{}(Stack:SortList{}),
                    \equals{SortInt{}, SortS{}}(
                        size{}(Stack:SortList{}),
                        \dv{SortInt{}}("1024")
                    )
                ),
                \dv{SortS{}}("done")
            ) [label{}("conditional")]
            "#,
    )
}

fn concrete_chain(definition: &BackendDefinition, depth: usize) -> Term {
    let definition = match internal_term(definition, "listUnit{}()").kind() {
        TermKind::List { definition, .. } => definition.clone(),
        term => panic!("expected native list unit, found {term:?}"),
    };
    Term::list(
        definition,
        (0..depth)
            .map(|index| Term::domain_value(Sort::simple("SortElement"), index.to_string()))
            .collect(),
        None,
    )
}

#[test]
fn execution_keeps_partial_simplification_and_records_budget_exhaustion() {
    let definition = definition(&long_requires_chain());
    let (result, diagnostics) = diagnostic::collect(|| {
        execute(
            &definition,
            subject(&definition, "value"),
            ExecutionOptions::default(),
        )
    });

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one execution leaf, found {:?}", result.leaves);
    };
    assert_eq!(leaf.depth, 0);
    assert!(matches!(
        leaf.halt_reason,
        HaltReason::Indeterminate(IndeterminateReason::Requires { ref rule_id, .. })
            if rule_id == "conditional"
    ));
    assert!(matches!(
        leaf.pattern.term.kind(),
        TermKind::Application { symbol, .. } if symbol.name.as_ref() == "wrap"
    ));
    assert_eq!(
        diagnostics,
        [BackendDiagnostic::SimplificationBudgetExhausted {
            limit: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            subject: BudgetSubject::Predicates,
        }]
    );
}

#[test]
fn deep_concrete_recursion_has_bounded_linear_productive_work() {
    std::thread::Builder::new()
        .name("deep-concrete-recursion".into())
        .stack_size(16 * 1024 * 1024)
        .spawn(deep_concrete_recursion_has_bounded_linear_productive_work_inner)
        .expect("the regression thread should start")
        .join()
        .expect("the regression thread should complete");
}

fn deep_concrete_recursion_has_bounded_linear_productive_work_inner() {
    const DEPTH: usize = 1_024;
    const OVERRIDE: usize = 4_096;

    let definition = deep_concrete_recursion_definition();
    let stack = concrete_chain(&definition, DEPTH);
    let size = Term::application(
        definition.symbols["size"].clone(),
        Vec::new(),
        vec![stack.clone()],
    );
    let simplified = k_rust_backend::simplify::simplify(
        &definition,
        &size,
        SimplificationOptions {
            max_iterations: OVERRIDE,
            ..SimplificationOptions::default()
        },
    )
    .expect("the request-level override should complete finite concrete recursion");

    assert_eq!(
        simplified.term,
        Term::domain_value(Sort::simple("SortInt"), DEPTH.to_string())
    );
    assert_eq!(simplified.applied_rules.len(), 2 * DEPTH + 1);
    assert_eq!(
        simplified
            .applied_rules
            .iter()
            .filter(|rule| rule.as_str() == "size-cons")
            .count(),
        DEPTH
    );
    assert_eq!(
        simplified
            .applied_rules
            .iter()
            .filter(|rule| rule.as_str() == "builtin:INT.add")
            .count(),
        DEPTH
    );
    assert_eq!(
        simplified
            .applied_rules
            .iter()
            .filter(|rule| rule.as_str() == "size-unit")
            .count(),
        1
    );

    let subject = Pattern {
        term: Term::application(
            definition.symbols["stackState"].clone(),
            Vec::new(),
            vec![stack],
        ),
        constraints: Vec::new(),
    };
    let exhausted = execute(&definition, subject.clone(), ExecutionOptions::default());
    let [leaf] = exhausted.leaves.as_slice() else {
        panic!(
            "expected one exhausted execution leaf, found {:?}",
            exhausted.leaves
        );
    };
    assert_not_iteration_limit(&leaf.halt_reason);

    let completed = execute(
        &definition,
        subject,
        ExecutionOptions {
            max_simplification_iterations: OVERRIDE,
            ..ExecutionOptions::default()
        },
    );
    let [leaf] = completed.leaves.as_slice() else {
        panic!(
            "expected one completed execution leaf, found {:?}",
            completed.leaves
        );
    };
    assert_eq!(leaf.depth, 1);
    assert_eq!(leaf.halt_reason, HaltReason::Stuck);
    assert!(matches!(
        leaf.pattern.term.kind(),
        TermKind::DomainValue { value, .. } if value.as_ref() == "done"
    ));
}

#[test]
fn rule_requires_budget_exhaustion_is_not_a_simplification_error() {
    let definition = definition(
        r#"
            symbol expand{}(SortS{}) : SortS{} [function{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    expand{}(X:SortS{}),
                    \and{SortS{}}(
                        expand{}(expand{}(X:SortS{})),
                        \top{SortS{}}()
                    )
                )
            ) [label{}("expand"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \equals{SortS{}, SortS{}}(
                        expand{}(X:SortS{}),
                        X:SortS{}
                    )
                ),
                \dv{SortS{}}("done")
            ) [label{}("conditional")]
            "#,
    );

    let result = execute(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions {
            max_simplification_iterations: 1,
            ..ExecutionOptions::default()
        },
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!(
            "expected one failed rule attempt, found {:?}",
            result.leaves
        );
    };
    assert_not_iteration_limit(&leaf.halt_reason);
}

#[test]
fn terminal_rule_keeps_a_partial_result_after_budget_exhaustion() {
    let definition = definition(
        r#"
            symbol expand{}(SortS{}) : SortS{} [function{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    expand{}(X:SortS{}),
                    \and{SortS{}}(
                        expand{}(expand{}(X:SortS{})),
                        \top{SortS{}}()
                    )
                )
            ) [label{}("expand"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                expand{}(X:SortS{})
            ) [label{}("stop")]
            "#,
    );

    let result = execute(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions {
            max_simplification_iterations: 1,
            terminal_rules: BTreeSet::from(["stop".into()]),
            ..ExecutionOptions::default()
        },
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!(
            "expected one failed terminal result, found {:?}",
            result.leaves
        );
    };
    assert_not_iteration_limit(&leaf.halt_reason);
}

#[test]
fn stopped_branch_keeps_partial_successors_after_budget_exhaustion() {
    let definition = definition(
        r#"
            symbol expand{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    expand{}(X:SortS{}),
                    \and{SortS{}}(
                        expand{}(expand{}(X:SortS{})),
                        \top{SortS{}}()
                    )
                )
            ) [label{}("expand"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("left")
            ) [label{}("left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                expand{}(X:SortS{})
            ) [label{}("middle")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("right")
            ) [label{}("right")]
            "#,
    );
    let initial = subject(&definition, "value");

    let result = execute(
        &definition,
        initial.clone(),
        ExecutionOptions {
            branch_mode: ExecutionBranchMode::StopAtBranch,
            max_simplification_iterations: 1,
            ..ExecutionOptions::default()
        },
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one branch-point leaf, found {:?}", result.leaves);
    };
    assert_eq!(leaf.depth, 0);
    assert_eq!(leaf.pattern, initial);
    assert_not_iteration_limit(&leaf.halt_reason);
}

#[test]
fn execution_preserves_user_log_effects() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortString{} [hasDomainValues{}()]
                sort SortK{} []
                symbol dotk{}() : SortK{} [constructor{}()]
                hooked-symbol log{}(SortString{}) : SortK{}
                    [function{}(), total{}(), hook{}("IO.logString")]
            endmodule []"#,
    )
    .unwrap();
    let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
    let initial = definition
        .internalize_term(
            &parse_pattern(r#"log{}(\dv{SortString{}}("one line"))"#).unwrap(),
            &[],
        )
        .unwrap();

    let result = execute(
        &definition,
        Pattern {
            term: initial,
            constraints: Vec::new(),
        },
        ExecutionOptions::default(),
    );

    assert_eq!(result.effects, [BuiltinEffect::UserLog("one line".into())]);
    assert!(matches!(
        result.leaves[0].pattern.term.kind(),
        TermKind::Application { symbol, .. } if symbol.name.as_ref() == "dotk"
    ));
}

#[test]
fn builtin_effect_observer_is_observational() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortString{} [hasDomainValues{}()]
                sort SortK{} []
                symbol dotk{}() : SortK{} [constructor{}()]
                hooked-symbol log{}(SortString{}) : SortK{}
                    [function{}(), total{}(), hook{}("IO.logString")]
            endmodule []"#,
    )
    .unwrap();
    let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
    let initial = Pattern {
        term: definition
            .internalize_term(
                &parse_pattern(r#"log{}(\dv{SortString{}}("one line"))"#).unwrap(),
                &[],
            )
            .unwrap(),
        constraints: Vec::new(),
    };
    let expected = execute(&definition, initial.clone(), ExecutionOptions::default());
    let mut observed = Vec::new();
    let actual = execute_with_solver_and_observer(
        &definition,
        initial,
        ExecutionOptions::default(),
        &NoSolver,
        |effect| observed.push(effect.clone()),
    );

    assert_eq!(actual, expected);
    assert_eq!(observed, actual.effects);
}

#[test]
fn execution_interrupts_native_hooks_at_the_step_deadline() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                hooked-symbol pow{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.pow")]
                symbol state{}(SortInt{}) : SortState{} [constructor{}()]
            endmodule []"#,
    )
    .unwrap();
    let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
    let initial = definition
        .internalize_pattern(
            &parse_pattern(r#"state{}(pow{}(\dv{SortInt{}}("2"), \dv{SortInt{}}("10")))"#).unwrap(),
            &[],
        )
        .unwrap();

    let result = execute(
        &definition,
        initial,
        ExecutionOptions {
            step_timeout: Some(Duration::ZERO),
            ..ExecutionOptions::default()
        },
    );

    assert!(matches!(
        result.leaves.as_slice(),
        [ExecutionLeaf {
            halt_reason: HaltReason::Timeout(StepTimeoutMode::Manual(timeout)),
            ..
        }] if timeout.is_zero()
    ));
}

#[test]
fn execution_stops_before_work_when_the_request_is_cancelled() {
    let definition = definition("");
    let initial = subject(&definition, "zero");
    let token = CancellationToken::new();
    token.cancel();

    let result = token.scope(|| execute(&definition, initial.clone(), ExecutionOptions::default()));

    assert_eq!(
        result.leaves,
        [ExecutionLeaf {
            pattern: initial,
            depth: 0,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            halt_reason: HaltReason::Cancelled,
        }]
    );
}

#[test]
fn stops_exactly_at_the_requested_depth_bound() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                wrap{}(X:SortS{})
            ) [label{}("loop")]
            "#,
    );

    let result = execute(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions {
            max_depth: 3,
            ..ExecutionOptions::default()
        },
    );
    assert_eq!(result.leaves.len(), 1);
    assert_eq!(result.leaves[0].depth, 3);
    assert_eq!(result.leaves[0].trace.len(), 3);
    assert_eq!(result.leaves[0].halt_reason, HaltReason::DepthBound);
}

#[test]
fn stuck_branch_takes_precedence_over_a_depth_bounded_branch() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("start")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("loop"))
            ) [label{}("start-loop")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("start")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("done"))
            ) [label{}("start-done")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("loop")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("loop"))
            ) [label{}("loop")]
            "#,
    );

    let result = execute(
        &definition,
        subject(&definition, "start"),
        ExecutionOptions {
            max_depth: 2,
            ..ExecutionOptions::default()
        },
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected only the stuck leaf, found {:?}", result.leaves);
    };
    assert_eq!(leaf.pattern, subject(&definition, "done"));
    assert_eq!(leaf.depth, 1);
    assert_eq!(leaf.halt_reason, HaltReason::Stuck);
}

fn stop_rule_definition() -> BackendDefinition {
    definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(\dv{SortS{}}("start")),
                    \top{SortS{}}()
                ),
                wrap{}(\dv{SortS{}}("middle"))
            ) [label{}("first")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(\dv{SortS{}}("middle")),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("stop")]
            "#,
    )
}

#[test]
fn stops_before_applying_a_cut_point_rule() {
    let definition = stop_rule_definition();
    let result = execute(
        &definition,
        subject(&definition, "start"),
        ExecutionOptions {
            cut_point_rules: BTreeSet::from(["stop".into()]),
            ..ExecutionOptions::default()
        },
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one cut-point leaf, found {:?}", result.leaves);
    };
    assert_eq!(leaf.depth, 1);
    assert_eq!(leaf.pattern, subject(&definition, "middle"));
    assert_eq!(leaf.trace.len(), 1);
    let HaltReason::CutPointRule { rule, next_states } = &leaf.halt_reason else {
        panic!("expected a cut-point halt, found {:?}", leaf.halt_reason);
    };
    assert_eq!(rule, "stop");
    assert_eq!(next_states.len(), 1);
    assert_eq!(
        next_states[0].pattern.term,
        internal_term(&definition, r#"\dv{SortS{}}("done")"#)
    );
}

#[test]
fn stops_after_applying_a_terminal_rule() {
    let definition = stop_rule_definition();
    let result = execute(
        &definition,
        subject(&definition, "start"),
        ExecutionOptions {
            terminal_rules: BTreeSet::from(["stop".into()]),
            ..ExecutionOptions::default()
        },
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one terminal leaf, found {:?}", result.leaves);
    };
    assert_eq!(leaf.depth, 2);
    assert_eq!(
        leaf.pattern.term,
        internal_term(&definition, r#"\dv{SortS{}}("done")"#)
    );
    assert_eq!(leaf.trace.len(), 2);
    assert_eq!(
        leaf.halt_reason,
        HaltReason::TerminalRule {
            rule: "stop".into()
        }
    );
}

fn unconditional_branch_definition() -> BackendDefinition {
    definition(
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
    )
}

fn converging_execution_definition() -> BackendDefinition {
    definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("initial")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("left"))
            ) [label{}("initial-left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("initial")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("right"))
            ) [label{}("initial-right")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("left")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("merged"))
            ) [label{}("left-merged")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("right")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("merged"))
            ) [label{}("right-merged")]
            "#,
    )
}

#[test]
fn converging_branches_yield_one_final_leaf() {
    let definition = converging_execution_definition();
    let result = execute(
        &definition,
        subject(&definition, "initial"),
        ExecutionOptions::default(),
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!(
            "expected one merged final configuration: {:?}",
            result.leaves
        );
    };
    assert_eq!(leaf.pattern, subject(&definition, "merged"));
    assert_eq!(leaf.depth, 2);
    assert_eq!(leaf.halt_reason, HaltReason::Stuck);
    assert_eq!(
        leaf.trace
            .iter()
            .map(|entry| entry.label.as_deref().unwrap())
            .collect::<Vec<_>>(),
        ["initial-left", "left-merged"]
    );
}

#[test]
fn equal_configurations_with_different_halt_reasons_merge_to_the_first() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("a")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("b"))
            ) [label{}("a-b")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("a")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("d"))
            ) [label{}("a-d")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("b")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("d"))
            ) [label{}("b-d")]
            "#,
    );
    let result = execute(
        &definition,
        subject(&definition, "a"),
        ExecutionOptions {
            max_depth: 2,
            ..ExecutionOptions::default()
        },
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!(
            "expected the first final configuration only: {:?}",
            result.leaves
        );
    };
    assert_eq!(leaf.pattern, subject(&definition, "d"));
    assert_eq!(leaf.depth, 1);
    assert_eq!(leaf.halt_reason, HaltReason::Stuck);
}

#[test]
fn bottom_leaves_are_not_merged() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("a")), \top{SortS{}}()),
                \bottom{SortS{}}()
            ) [label{}("bottom")]
            "#,
    );
    let initial = subject(&definition, "a");
    let result = execute_disjunction_with_solver_and_observer(
        &definition,
        vec![initial.clone(), initial],
        ExecutionOptions::default(),
        &NoSolver,
        |_| {},
    );

    assert_eq!(result.leaves.len(), 2);
    assert!(
        result
            .leaves
            .iter()
            .all(|leaf| leaf.halt_reason == HaltReason::Trivial)
    );
}

#[test]
fn breadth_bound_frontier_is_merged() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("a")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("merged"))
            ) [label{}("first")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("a")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("merged"))
            ) [label{}("second")]
            "#,
    );
    let result = execute(
        &definition,
        subject(&definition, "a"),
        ExecutionOptions {
            max_breadth: Some(1),
            ..ExecutionOptions::default()
        },
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one merged breadth frontier: {:?}", result.leaves);
    };
    assert_eq!(leaf.pattern, subject(&definition, "merged"));
    assert_eq!(leaf.halt_reason, HaltReason::BreadthBound);
}

#[test]
fn observation_filter_installation_is_atomic() {
    let definition = unconditional_branch_definition();

    assert_eq!(
        ObservationOptions::with_rules(&definition, ["left", "missing"]),
        Err(ObservationFilterError::UnknownRule("missing".into()))
    );
    assert!(ObservationOptions::with_rules(&definition, ["left", "right"]).is_ok());
}

#[test]
fn single_rewrite_emits_one_committed_observation() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("done")
            ) [label{}("step")]
            "#,
    );
    let before = subject(&definition, "value");
    let result = execute_observed(
        &definition,
        before.clone(),
        ExecutionOptions::default(),
        &ObservationOptions::all(),
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one execution leaf");
    };
    let [ObservationEvent::Transition(observation)] = leaf.observations.as_slice() else {
        panic!(
            "expected one committed observation: {:?}",
            leaf.observations
        );
    };
    assert_eq!(observation.class, TransitionClass::Rewrite);
    assert_eq!(observation.id.rule, "step");
    assert_eq!(observation.id.target, PatternDigest::of(&observation.after));
    assert_eq!(observation.rule_label.as_deref(), Some("step"));
    assert_eq!(observation.bindings.len(), 1);
    assert!(observation.introduced_predicates.is_empty());
    assert_eq!(observation.before, before);
    assert_eq!(observation.after, leaf.pattern);
    assert!(observation.effects.is_empty());
}

#[test]
fn failed_side_condition_emits_no_committed_observation() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \bottom{SortS{}}()),
                \dv{SortS{}}("unreachable")
            ) [label{}("failed")]
            "#,
    );
    let result = execute_observed(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions::default(),
        &ObservationOptions::all(),
    );

    assert_eq!(result.leaves.len(), 1);
    assert!(result.leaves[0].observations.is_empty());
    assert!(result.leaves[0].branch.is_empty());
}

#[test]
fn sibling_branches_own_independent_ordered_streams() {
    let definition = unconditional_branch_definition();
    let result = execute_observed(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions::default(),
        &ObservationOptions::all(),
    );

    assert_eq!(result.leaves.len(), 2);
    let streams = result
        .leaves
        .iter()
        .map(|leaf| {
            leaf.observations
                .iter()
                .map(|event| match event {
                    ObservationEvent::Transition(observation) => observation.id.rule.as_str(),
                    ObservationEvent::Uncommitted(_) => panic!("unexpected rollback"),
                })
                .collect::<Vec<_>>()
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(streams, BTreeSet::from([vec!["left"], vec!["right"]]));
    assert!(result.leaves.iter().all(|leaf| leaf.branch.len() == 1));
}

#[test]
fn observation_on_preserves_non_observation_outputs() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("done")
            ) [label{}("step")]
            "#,
    );
    let initial = subject(&definition, "value");
    let expected = execute(&definition, initial.clone(), ExecutionOptions::default());
    let mut actual = execute_observed(
        &definition,
        initial,
        ExecutionOptions::default(),
        &ObservationOptions::all(),
    );

    assert!(!actual.leaves[0].observations.is_empty());
    for leaf in &mut actual.leaves {
        leaf.branch.clear();
        leaf.observations.clear();
    }
    assert_eq!(actual, expected);
}

#[test]
fn valid_observation_filter_suppresses_events_but_preserves_branch_identity() {
    let definition = unconditional_branch_definition();
    let options = ObservationOptions::with_rules(&definition, ["left"]).unwrap();
    let result = execute_observed(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions::default(),
        &options,
    );

    assert!(result.leaves.iter().all(|leaf| leaf.branch.len() == 1));
    assert_eq!(
        result
            .leaves
            .iter()
            .filter(|leaf| !leaf.observations.is_empty())
            .count(),
        1
    );
}

#[test]
fn transition_classes_distinguish_function_equations_from_rewrites() {
    let definition = definition(
        r#"
            symbol value{}() : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \top{R}()),
                \equals{SortS{}, R}(
                    value{}(),
                    \and{SortS{}}(
                        \dv{SortS{}}("value"),
                        \top{SortS{}}()
                    )
                )
            ) [label{}("value")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("done")
            ) [label{}("step")]
            "#,
    );
    let initial = Pattern {
        term: internal_term(&definition, r#"wrap{}(value{}())"#),
        constraints: Vec::new(),
    };
    let result = execute_observed(
        &definition,
        initial,
        ExecutionOptions::default(),
        &ObservationOptions::all(),
    );

    assert_eq!(
        result.leaves[0]
            .observations
            .iter()
            .map(|event| match event {
                ObservationEvent::Transition(observation) => observation.class,
                ObservationEvent::Uncommitted(_) => panic!("unexpected rollback"),
            })
            .collect::<Vec<_>>(),
        [TransitionClass::FunctionEquation, TransitionClass::Rewrite]
    );
}

#[test]
fn terminal_result_simplification_is_observed_in_order() {
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
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                identity{}(\dv{SortS{}}("done"))
            ) [label{}("stop")]
            "#,
    );
    let result = execute_observed(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions {
            terminal_rules: BTreeSet::from(["stop".into()]),
            ..ExecutionOptions::default()
        },
        &ObservationOptions::all(),
    );

    assert_eq!(
        result.leaves[0]
            .observations
            .iter()
            .map(|event| match event {
                ObservationEvent::Transition(observation) => {
                    (observation.id.rule.as_str(), observation.class)
                }
                ObservationEvent::Uncommitted(_) => panic!("unexpected rollback"),
            })
            .collect::<Vec<_>>(),
        [
            ("stop", TransitionClass::Rewrite),
            ("identity", TransitionClass::Simplification),
        ]
    );
}

#[test]
fn builtin_observation_owns_its_user_log_effect() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortString{} [hasDomainValues{}()]
                sort SortK{} []
                symbol dotk{}() : SortK{} [constructor{}()]
                hooked-symbol log{}(SortString{}) : SortK{}
                    [function{}(), total{}(), hook{}("IO.logString")]
            endmodule []"#,
    )
    .unwrap();
    let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
    let initial = definition
        .internalize_pattern(
            &parse_pattern(r#"log{}(\dv{SortString{}}("one line"))"#).unwrap(),
            &[],
        )
        .unwrap();
    let result = execute_observed(
        &definition,
        initial.clone(),
        ExecutionOptions::default(),
        &ObservationOptions::all(),
    );

    let [ObservationEvent::Transition(observation)] = result.leaves[0].observations.as_slice()
    else {
        panic!("expected one builtin observation");
    };
    assert_eq!(observation.id.rule, "builtin:IO.logString");
    assert_eq!(observation.class, TransitionClass::Builtin);
    assert_eq!(observation.before, initial);
    assert_eq!(observation.after, result.leaves[0].pattern);
    assert_eq!(
        observation.effects,
        [BuiltinEffect::UserLog("one line".into())]
    );
    assert_eq!(observation.effects, result.effects);
}

#[test]
fn symbolic_remainder_emits_a_distinct_observation_class() {
    struct IndeterminateSatSolver;

    impl SmtSolver for IndeterminateSatSolver {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &Substitution,
        ) -> Result<Satisfiability, SmtError> {
            Ok(Satisfiability::Sat)
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Result<Validity, SmtError> {
            Ok(Validity::Indeterminate)
        }
    }

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
    let result = execute_observed_with_solver(
        &definition,
        symbolic_subject(&definition),
        ExecutionOptions::default(),
        &IndeterminateSatSolver,
        &ObservationOptions::all(),
    );

    let remainder = result
        .leaves
        .iter()
        .flat_map(|leaf| &leaf.observations)
        .find_map(|event| match event {
            ObservationEvent::Transition(observation)
                if observation.class == TransitionClass::Remainder =>
            {
                Some(observation)
            }
            ObservationEvent::Transition(_) | ObservationEvent::Uncommitted(_) => None,
        })
        .expect("expected one retained symbolic remainder");
    assert_eq!(remainder.id.rule, "remainder:negative");
    assert_eq!(remainder.before, symbolic_subject(&definition));
    assert!(matches!(
        remainder.after.constraints.as_slice(),
        [Predicate::Not(_)]
    ));
}

#[test]
fn stops_at_a_rewrite_branch_when_requested() {
    let definition = unconditional_branch_definition();
    let initial = subject(&definition, "value");

    let result = execute(
        &definition,
        initial.clone(),
        ExecutionOptions {
            branch_mode: ExecutionBranchMode::StopAtBranch,
            ..ExecutionOptions::default()
        },
    );

    assert_eq!(result.leaves.len(), 1);
    assert_eq!(result.leaves[0].pattern, initial);
    assert_eq!(result.leaves[0].depth, 0);
    let HaltReason::Branch {
        branches,
        remainder,
    } = &result.leaves[0].halt_reason
    else {
        panic!("expected an unconditional branch point");
    };
    assert_eq!(branches.len(), 2);
    assert!(remainder.is_none());
}

#[test]
fn stopped_branch_retains_effects_from_every_reported_successor() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortString{} [hasDomainValues{}()]
                sort SortK{} []
                symbol initial{}() : SortK{} [constructor{}()]
                symbol dotk{}() : SortK{} [constructor{}()]
                hooked-symbol log{}(SortString{}) : SortK{}
                    [function{}(), hook{}("IO.logString")]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(initial{}(), \top{SortK{}}()),
                    log{}(\dv{SortString{}}("left"))
                ) [label{}("left")]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(initial{}(), \top{SortK{}}()),
                    log{}(\dv{SortString{}}("right"))
                ) [label{}("right")]
            endmodule []"#,
    )
    .unwrap();
    let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
    let initial = definition
        .internalize_pattern(&parse_pattern("initial{}()").unwrap(), &[])
        .unwrap();

    let mut observed = Vec::new();
    let result = execute_with_solver_and_observer(
        &definition,
        initial,
        ExecutionOptions {
            branch_mode: ExecutionBranchMode::StopAtBranch,
            ..ExecutionOptions::default()
        },
        &NoSolver,
        |effect| observed.push(effect.clone()),
    );

    assert!(matches!(
        result.leaves[0].halt_reason,
        HaltReason::Branch { .. }
    ));
    assert_eq!(
        result.effects,
        [
            BuiltinEffect::UserLog("left".into()),
            BuiltinEffect::UserLog("right".into()),
        ]
    );
    assert_eq!(observed, result.effects);
}

#[test]
fn normalizes_branch_payloads_before_reporting_branching() {
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
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                identity{}(\dv{SortS{}}("left"))
            ) [label{}("left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                identity{}(\dv{SortS{}}("right"))
            ) [label{}("right")]
            "#,
    );

    let result = execute(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions {
            branch_mode: ExecutionBranchMode::StopAtBranch,
            ..ExecutionOptions::default()
        },
    );

    let HaltReason::Branch { branches, .. } = &result.leaves[0].halt_reason else {
        panic!("expected a normalized branch point");
    };
    assert_eq!(
        branches
            .iter()
            .map(|branch| match branch.pattern.term.kind() {
                TermKind::DomainValue { value, .. } => value.as_ref(),
                other => panic!("branch payload was not normalized: {other:?}"),
            })
            .collect::<Vec<_>>(),
        vec!["left", "right"]
    );
}

#[test]
fn continues_after_result_simplification_prunes_to_one_branch() {
    let definition = definition(
        r#"
            symbol dead{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    dead{}(X:SortS{}),
                    \and{SortS{}}(
                        \dv{SortS{}}("dead"),
                        \bottom{SortS{}}()
                    )
                )
            ) [label{}("dead"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                dead{}(\dv{SortS{}}("left"))
            ) [label{}("left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("right")
            ) [label{}("right")]
            "#,
    );

    let result = execute(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions {
            branch_mode: ExecutionBranchMode::StopAtBranch,
            ..ExecutionOptions::default()
        },
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected the one viable branch to continue");
    };
    assert_eq!(leaf.depth, 1);
    assert_eq!(leaf.halt_reason, HaltReason::Stuck);
    assert_eq!(
        leaf.pattern.term,
        internal_term(&definition, r#"\dv{SortS{}}("right")"#)
    );
}

#[test]
fn rolled_back_branch_effects_are_classified_without_committing() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortString{} [hasDomainValues{}()]
                sort SortK{} []
                symbol initial{}() : SortK{} [constructor{}()]
                symbol dotk{}() : SortK{} [constructor{}()]
                hooked-symbol log{}(SortString{}) : SortK{}
                    [function{}(), hook{}("IO.logString")]
                symbol dead{}(SortK{}) : SortK{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortK{}, R}(
                        dead{}(X:SortK{}),
                        \and{SortK{}}(X:SortK{}, \bottom{SortK{}}())
                    )
                ) [label{}("dead"), simplification{}()]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(initial{}(), \top{SortK{}}()),
                    dead{}(log{}(\dv{SortString{}}("rolled back")))
                ) [label{}("left")]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(initial{}(), \top{SortK{}}()),
                    dotk{}()
                ) [label{}("right")]
            endmodule []"#,
    )
    .unwrap();
    let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
    let initial = definition
        .internalize_pattern(&parse_pattern("initial{}()").unwrap(), &[])
        .unwrap();

    let result = execute_observed(
        &definition,
        initial,
        ExecutionOptions {
            branch_mode: ExecutionBranchMode::StopAtBranch,
            ..ExecutionOptions::default()
        },
        &ObservationOptions::all(),
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected the one viable branch to continue");
    };
    assert_eq!(leaf.depth, 1);
    assert_eq!(
        leaf.observations
            .iter()
            .map(|event| match event {
                ObservationEvent::Transition(observation) => observation.id.rule.as_str(),
                ObservationEvent::Uncommitted(_) => panic!("rollback leaked into leaf"),
            })
            .collect::<Vec<_>>(),
        ["right"]
    );
    assert!(result.effects.is_empty());
    let [discarded] = result.discarded.as_slice() else {
        panic!("expected one discarded transition: {:?}", result.discarded);
    };
    assert_eq!(discarded.id.rule, "left");
    assert_eq!(discarded.rule_label.as_deref(), Some("left"));
    assert_eq!(
        discarded.effects,
        [BuiltinEffect::UserLog("rolled back".into())]
    );
    assert_eq!(discarded.reason, UncommittedReason::RolledBack);
}

#[test]
fn explores_each_rewrite_branch_by_default() {
    let definition = unconditional_branch_definition();

    let result = execute(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions::default(),
    );
    assert_eq!(result.leaves.len(), 2);
    assert!(
        result
            .leaves
            .iter()
            .all(|leaf| leaf.depth == 1 && leaf.halt_reason == HaltReason::Stuck)
    );
    assert_eq!(
        result
            .leaves
            .iter()
            .map(|leaf| leaf.trace[0].label.as_deref().unwrap())
            .collect::<Vec<_>>(),
        vec!["left", "right"]
    );
}

#[test]
fn breadth_bound_returns_the_live_execution_frontier() {
    let definition = unconditional_branch_definition();

    let result = execute(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions {
            max_breadth: Some(1),
            ..ExecutionOptions::default()
        },
    );

    assert_eq!(result.leaves.len(), 2);
    assert!(
        result
            .leaves
            .iter()
            .all(|leaf| leaf.depth == 1 && leaf.halt_reason == HaltReason::BreadthBound)
    );
    assert_eq!(
        result
            .leaves
            .iter()
            .map(|leaf| match leaf.pattern.term.kind() {
                TermKind::DomainValue { value, .. } => value.as_ref(),
                other => panic!("expected a domain value, found {other:?}"),
            })
            .collect::<Vec<_>>(),
        vec!["left", "right"]
    );
}

#[test]
fn zero_breadth_returns_the_initial_configuration() {
    let definition = unconditional_branch_definition();
    let initial = subject(&definition, "value");

    let result = execute(
        &definition,
        initial.clone(),
        ExecutionOptions {
            max_breadth: Some(0),
            ..ExecutionOptions::default()
        },
    );

    assert_eq!(result.leaves.len(), 1);
    assert_eq!(result.leaves[0].pattern, initial);
    assert_eq!(result.leaves[0].halt_reason, HaltReason::BreadthBound);
}

#[test]
fn any_mode_uses_the_first_applicable_rule() {
    let definition = unconditional_branch_definition();

    let result = execute(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions {
            mode: ExecutionMode::Any,
            ..ExecutionOptions::default()
        },
    );

    // Equal priority: the first applicable rule in declaration order wins.
    assert_eq!(result.leaves.len(), 1);
    assert_eq!(result.leaves[0].depth, 1);
    assert!(matches!(
        result.leaves[0].pattern.term.kind(),
        TermKind::DomainValue { value, .. } if value.as_ref() == "left"
    ));
    assert_eq!(result.leaves[0].trace[0].label.as_deref(), Some("left"));
}

#[cfg(feature = "z3")]
#[test]
fn any_mode_passes_only_the_first_rules_remainder_to_later_rules() {
    let definition = definition(
        r#"
            symbol fallback{}(SortS{}) : SortS{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(\dv{SortS{}}("a")),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("first")
            ) [label{}("specific")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(fallback{}(X:SortS{})),
                    \top{SortS{}}()
                ),
                fallback{}(X:SortS{})
            ) [label{}("fallback")]
            "#,
    );
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let result = execute_with_solver(
        &definition,
        Pattern {
            term: internal_term(&definition, "wrap{}(Y:SortS{})"),
            constraints: Vec::new(),
        },
        ExecutionOptions {
            mode: ExecutionMode::Any,
            ..ExecutionOptions::default()
        },
        &solver,
    );

    assert_eq!(result.leaves.len(), 3);
    let specific = result
        .leaves
        .iter()
        .find(|leaf| {
            matches!(
                leaf.pattern.term.kind(),
                TermKind::DomainValue { value, .. } if value.as_ref() == "first"
            )
        })
        .expect("the first rule should own its matching branch");
    let fallback = result
        .leaves
        .iter()
        .find(|leaf| {
            matches!(
                leaf.pattern.term.kind(),
                TermKind::Application { symbol, .. } if symbol.name.as_ref() == "fallback"
            )
        })
        .expect("the later rule should receive the first rule's remainder");
    let uncovered = result
        .leaves
        .iter()
        .find(|leaf| leaf.pattern.term == internal_term(&definition, "wrap{}(Y:SortS{})"))
        .expect("the complement of both partial rules should remain visible");
    assert!(!specific.pattern.constraints.is_empty());
    assert!(
        fallback
            .pattern
            .constraints
            .iter()
            .any(|predicate| matches!(predicate, Predicate::Not(_)))
    );
    assert_eq!(
        uncovered
            .pattern
            .constraints
            .iter()
            .filter(|predicate| matches!(predicate, Predicate::Not(_)))
            .count(),
        2
    );
}

#[cfg(feature = "z3")]
#[test]
fn sequential_remainders_retain_the_initial_antecedent() {
    // Rules are tried in declaration order: `second` (X = 1 or 2) covers half of the
    // antecedent Y = 0 or 1 and leaves the Y = 0 remainder to `first`. Declared the other
    // way round, `first` covers the whole antecedent and no remainder is ever formed.
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \or{SortS{}}(
                        \equals{SortS{}, SortS{}}(X:SortS{}, \dv{SortS{}}("1")),
                        \equals{SortS{}, SortS{}}(X:SortS{}, \dv{SortS{}}("2")),
                        \bottom{SortS{}}()
                    )
                ),
                \dv{SortS{}}("second")
            ) [label{}("second")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \or{SortS{}}(
                        \equals{SortS{}, SortS{}}(X:SortS{}, \dv{SortS{}}("0")),
                        \equals{SortS{}, SortS{}}(X:SortS{}, \dv{SortS{}}("1")),
                        \bottom{SortS{}}()
                    )
                ),
                \dv{SortS{}}("first")
            ) [label{}("first")]
            "#,
    );
    let variable = Term::variable(Variable::new("Y", Sort::simple("SortS")));
    let initial_antecedent = Predicate::Or(vec![
        Predicate::Equals(
            variable.clone(),
            Term::domain_value(Sort::simple("SortS"), "0"),
        ),
        Predicate::Equals(variable, Term::domain_value(Sort::simple("SortS"), "1")),
    ]);
    let initial = Pattern {
        term: internal_term(&definition, "wrap{}(Y:SortS{})"),
        constraints: vec![initial_antecedent.clone()],
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder,
        ..
    } = rewrite_step_sequential_with_solver(&definition, &initial, &mut fresh, &solver)
    else {
        panic!("the two partial rules must expose both successors");
    };

    assert_eq!(branches.len(), 2);
    assert!(branches.iter().all(|branch| {
        branch.before.constraints.contains(&initial_antecedent)
            && branch.pattern.constraints.contains(&initial_antecedent)
    }));
    assert!(
        remainder.is_none(),
        "nothing outside the antecedent is live"
    );
}

#[test]
fn rewrites_through_matching_injective_function_heads() {
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(injectiveFunction{}(X:SortS{})),
                    \top{SortS{}}()
                ),
                wrap{}(X:SortS{})
            ) [label{}("injective-match")]
            "#,
    );
    let value = r#"\dv{SortS{}}("value")"#;
    let subject = Pattern {
        term: internal_term(
            &definition,
            &format!("wrap{{}}(injectiveFunction{{}}({value}))"),
        ),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh) else {
        panic!("injective heads should decompose during rewrite matching");
    };

    assert_eq!(
        applied.pattern.term,
        internal_term(&definition, &format!("wrap{{}}({value})"))
    );
    assert!(applied.pattern.constraints.is_empty());
}

#[test]
fn rewrites_through_a_direct_symbol_overload() {
    let definition = overload_rewrite_definition();
    let value = r#"token{}(\dv{SortToken{}}("value"))"#;
    let subject = Pattern {
        term: internal_term(
            &definition,
            &format!("overloadState{{}}(inj{{SortSub{{}}, SortTop{{}}}}(lower{{}}({value})))"),
        ),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh) else {
        panic!("directly overloaded constructors should match during rewriting");
    };

    assert_eq!(
        applied.pattern.term,
        internal_term(
            &definition,
            &format!("overloadResult{{}}(inj{{SortSub{{}}, SortTop{{}}}}({value}))"),
        )
    );
    assert!(applied.pattern.constraints.is_empty());
}

#[cfg(feature = "z3")]
#[test]
fn narrows_an_injected_variable_to_a_lesser_overload() {
    let definition = overload_rewrite_definition();
    let subject = Pattern {
        term: internal_term(
            &definition,
            "overloadState{}(inj{SortSub{}, SortTop{}}(CONFIG:SortSub{}))",
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("overload narrowing should retain applied and complementary branches");
    };
    let [branch] = branches.as_slice() else {
        panic!("expected one overload narrowing branch, found {branches:?}");
    };
    let TermKind::Application { arguments, .. } = branch.pattern.term.kind() else {
        panic!("expected the overload result constructor");
    };
    let TermKind::Injection { term: result, .. } = arguments[0].kind() else {
        panic!("the narrowed argument should remain injected to SortTop");
    };
    let TermKind::Variable(fresh_variable) = result.kind() else {
        panic!("the lesser overload argument should be fresh");
    };
    assert!(fresh_variable.name.starts_with("Ex#Overload0"));
    let [Predicate::Equals(configuration, value)] = branch.pattern.constraints.as_slice() else {
        panic!("expected the overload narrowing equality");
    };
    assert!(matches!(
        configuration.kind(),
        TermKind::Variable(variable) if variable.name.as_ref() == "CONFIG"
    ));
    assert!(matches!(
        value.kind(),
        TermKind::Application { symbol, arguments, .. }
            if symbol.name.as_ref() == "lower"
                && matches!(arguments[0].kind(), TermKind::Variable(variable) if variable == fresh_variable)
    ));
    let [Predicate::Not(remainder_condition)] = remainder.pattern.constraints.as_slice() else {
        panic!("expected a negated complementary condition");
    };
    assert!(matches!(
        remainder_condition.as_ref(),
        Predicate::Exists(variable, equality)
            if variable == fresh_variable
                && equality.as_ref() == &branch.pattern.constraints[0]
    ));
}

#[test]
fn unifies_kequal_operands_when_matching_true() {
    let definition = kequal_rewrite_definition("state{}(equal{}(VALUE:SortValue{}, chosen{}()))");
    let subject = Pattern {
        term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("true"))"#),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh) else {
        panic!("true K equality should unify its operands");
    };
    assert_eq!(applied.pattern.term, internal_term(&definition, "done{}()"));
    assert!(applied.pattern.constraints.is_empty());
    assert!(applied.substitution.iter().any(|(variable, value)| {
        variable.name.ends_with("VALUE") && value == &internal_term(&definition, "chosen{}()")
    }));
}

#[test]
fn unifies_integer_equality_operands_when_matching_true() {
    let definition = scalar_equality_rewrite_definition("INT.eq", "SortInt", "INT.Int");
    let subject = Pattern {
        term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("true"))"#),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh) else {
        panic!("true integer equality should unify its operands");
    };
    assert!(applied.substitution.iter().any(|(variable, value)| {
        variable.name.ends_with("VALUE") && value == &internal_term(&definition, "value{}()")
    }));
}

#[test]
fn unifies_string_equality_operands_when_matching_true() {
    let definition = scalar_equality_rewrite_definition("STRING.eq", "SortString", "STRING.String");
    let subject = Pattern {
        term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("true"))"#),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh) else {
        panic!("true string equality should unify its operands");
    };
    assert!(applied.substitution.iter().any(|(variable, value)| {
        variable.name.ends_with("VALUE") && value == &internal_term(&definition, "value{}()")
    }));
}

#[test]
fn unifies_both_conjunction_operands_when_matching_true() {
    let definition =
        boolean_rewrite_definition("state{}(and{}(LEFT:SortBool{}, RIGHT:SortBool{}))");
    let subject = Pattern {
        term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("true"))"#),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh) else {
        panic!("true conjunction should bind both operands to true");
    };
    assert_eq!(applied.substitution.len(), 2);
    assert!(applied.substitution.iter().all(|(variable, value)| {
        (variable.name.ends_with("LEFT") || variable.name.ends_with("RIGHT"))
            && value == &Term::domain_value(Sort::simple("SortBool"), "true")
    }));
}

#[test]
fn unifies_both_disjunction_operands_when_matching_false() {
    let definition = boolean_rewrite_definition("state{}(or{}(LEFT:SortBool{}, RIGHT:SortBool{}))");
    let subject = Pattern {
        term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("false"))"#),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh) else {
        panic!("false disjunction should bind both operands to false");
    };
    assert_eq!(applied.substitution.len(), 2);
    assert!(applied.substitution.iter().all(|(variable, value)| {
        (variable.name.ends_with("LEFT") || variable.name.ends_with("RIGHT"))
            && value == &Term::domain_value(Sort::simple("SortBool"), "false")
    }));
}

#[test]
fn unifies_negation_operand_with_the_opposite_boolean() {
    let definition = boolean_rewrite_definition("state{}(not{}(VALUE:SortBool{}))");
    let subject = Pattern {
        term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("true"))"#),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh) else {
        panic!("negation should bind its operand to the opposite Boolean");
    };
    assert!(applied.substitution.iter().any(|(variable, value)| {
        variable.name.ends_with("VALUE")
            && value == &Term::domain_value(Sort::simple("SortBool"), "false")
    }));
}

#[cfg(feature = "z3")]
#[test]
fn constrains_configuration_conjunction_operands_when_matching_true() {
    let definition = boolean_rewrite_definition(r#"state{}(\dv{SortBool{}}("true"))"#);
    let subject = Pattern {
        term: internal_term(
            &definition,
            "state{}(and{}(LEFT:SortBool{}, RIGHT:SortBool{}))",
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("configuration conjunction should retain its complementary state");
    };
    let [branch] = branches.as_slice() else {
        panic!("expected one conjunction branch, found {branches:?}");
    };
    let expected = ["LEFT", "RIGHT"]
        .map(|name| Predicate::Term(internal_term(&definition, &format!("{name}:SortBool{{}}"))))
        .to_vec();
    assert_eq!(branch.pattern.constraints, expected);
    assert_eq!(
        remainder.pattern.constraints,
        [Predicate::Not(Box::new(Predicate::And(expected)))]
    );
}

#[cfg(feature = "z3")]
#[test]
fn negates_kequal_operand_unification_when_matching_false() {
    let definition = kequal_rewrite_definition(
        "stateWithContext{}(equal{}(VALUE:SortValue{}, chosen{}()), CONTEXT:SortValue{})",
    );
    let subject = Pattern {
        term: internal_term(
            &definition,
            r#"stateWithContext{}(\dv{SortBool{}}("false"), SYMBOLIC:SortValue{})"#,
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("false K equality should retain disequality and complementary branches");
    };
    let [branch] = branches.as_slice() else {
        panic!("expected one disequality branch, found {branches:?}");
    };
    let [disequality @ Predicate::Not(inner)] = branch.pattern.constraints.as_slice() else {
        panic!("expected the negated operand equality");
    };
    let Predicate::Equals(left, right) = inner.as_ref() else {
        panic!("expected an equality beneath the negation");
    };
    let TermKind::Variable(fresh_variable) = left.kind() else {
        panic!("the unbound equality operand should be freshened");
    };
    assert!(fresh_variable.name.starts_with("Ex#VALUE"));
    assert_eq!(right, &internal_term(&definition, "chosen{}()"));
    assert!(matches!(
        remainder.pattern.constraints.as_slice(),
        [Predicate::Not(complement)]
            if matches!(complement.as_ref(), Predicate::Exists(variable, condition)
                if variable == fresh_variable && condition.as_ref() == disequality)
    ));
}

#[cfg(feature = "z3")]
#[test]
fn constrains_configuration_kequal_operands_when_matching_true() {
    let definition = kequal_rewrite_definition(r#"state{}(\dv{SortBool{}}("true"))"#);
    let subject = Pattern {
        term: internal_term(
            &definition,
            "state{}(equal{}(CONFIG:SortValue{}, chosen{}()))",
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("configuration equality should retain applied and complementary branches");
    };
    let [branch] = branches.as_slice() else {
        panic!("expected one configuration equality branch, found {branches:?}");
    };
    let condition = Predicate::Equals(
        internal_term(&definition, "CONFIG:SortValue{}"),
        internal_term(&definition, "chosen{}()"),
    );
    assert_eq!(
        branch.pattern.constraints.as_slice(),
        std::slice::from_ref(&condition)
    );
    assert_eq!(
        remainder.pattern.constraints,
        [Predicate::Not(Box::new(condition))]
    );
}

#[cfg(feature = "z3")]
#[test]
fn splits_symbolic_if_then_else_during_rewrite_matching() {
    let definition = ite_rewrite_definition("state{}(chosen{}())");
    let subject = Pattern {
        term: internal_term(
            &definition,
            "state{}(ite{}(CONDITION:SortBool{}, chosen{}(), rejected{}()))",
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("one viable ITE branch should retain its complementary state");
    };
    let [branch] = branches.as_slice() else {
        panic!("only the selected constructor should match, found {branches:?}");
    };
    assert_eq!(branch.pattern.term, internal_term(&definition, "done{}()"));
    let selected = Predicate::Term(internal_term(&definition, "CONDITION:SortBool{}"));
    assert_eq!(
        branch.pattern.constraints.as_slice(),
        std::slice::from_ref(&selected)
    );
    assert_eq!(
        remainder.pattern.constraints,
        [Predicate::Not(Box::new(selected))]
    );
}

#[cfg(feature = "z3")]
#[test]
fn splits_symbolic_if_then_else_on_the_rule_side() {
    let definition =
        ite_rewrite_definition("state{}(ite{}(CONDITION:SortBool{}, chosen{}(), rejected{}()))");
    let subject = Pattern {
        term: internal_term(&definition, "state{}(chosen{}())"),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Finished(applied) =
        rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("the viable rule-side ITE branch should match exhaustively");
    };
    assert_eq!(applied.pattern.term, internal_term(&definition, "done{}()"));
    assert!(applied.pattern.constraints.is_empty());
    assert!(applied.substitution.iter().any(|(variable, value)| {
        variable.name.ends_with("CONDITION")
            && value == &Term::domain_value(Sort::simple("SortBool"), "true")
    }));
}

#[cfg(feature = "z3")]
#[test]
fn recursively_splits_nested_symbolic_if_then_else() {
    let definition = ite_rewrite_definition("state{}(chosen{}())");
    let subject = Pattern {
        term: internal_term(
            &definition,
            "state{}(ite{}(OUTER:SortBool{}, ite{}(INNER:SortBool{}, chosen{}(), rejected{}()), rejected{}()))",
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("the nested viable path should retain its complementary state");
    };
    let [branch] = branches.as_slice() else {
        panic!("only one nested ITE path should match, found {branches:?}");
    };
    let expected = ["OUTER", "INNER"]
        .map(|name| Predicate::Term(internal_term(&definition, &format!("{name}:SortBool{{}}"))))
        .to_vec();
    assert_eq!(branch.pattern.constraints, expected);
    assert_eq!(
        remainder.pattern.constraints,
        [Predicate::Not(Box::new(Predicate::And(expected)))]
    );
}

#[test]
fn branches_for_every_concrete_set_element_selection() {
    let definition = set_selection_definition();
    let first = r#"\dv{SortElement{}}("first")"#;
    let second = r#"\dv{SortElement{}}("second")"#;
    let subject = Pattern {
        term: internal_term(
            &definition,
            &format!("state{{}}(setConcat{{}}(setItem{{}}({first}), setItem{{}}({second})))"),
        ),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: None,
        ..
    } = rewrite_step(&definition, &subject, &mut fresh)
    else {
        panic!("set selection should produce one exhaustive branch per element");
    };
    let mut actual = branches
        .iter()
        .map(|branch| branch.pattern.term.clone())
        .collect::<Vec<_>>();
    actual.sort();
    let mut expected = vec![
        internal_term(
            &definition,
            &format!("picked{{}}({first}, setItem{{}}({second}))"),
        ),
        internal_term(
            &definition,
            &format!("picked{{}}({second}, setItem{{}}({first}))"),
        ),
    ];
    expected.sort();

    assert_eq!(actual, expected);
    assert!(
        branches
            .iter()
            .all(|branch| branch.pattern.constraints.is_empty())
    );
}

#[cfg(feature = "z3")]
#[test]
fn narrows_a_closed_set_pattern_into_an_empty_subject_frame() {
    let definition = closed_collection_frame_definition();
    let subject = Pattern {
        term: internal_term(
            &definition,
            r#"setState{}(setConcat{}(setItem{}(\dv{SortElement{}}("first")), FRAME:SortSet{}))"#,
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("closed Set matching should produce applied and complementary branches");
    };
    let [branch] = branches.as_slice() else {
        panic!("the empty-frame assignment should be unique: {branches:?}");
    };
    let frame_is_empty = Predicate::Equals(
        internal_term(&definition, "FRAME:SortSet{}"),
        internal_term(&definition, "setUnit{}()"),
    );

    assert_eq!(
        branch.pattern.term,
        internal_term(&definition, "setDone{}()")
    );
    assert_eq!(
        branch.pattern.constraints.as_slice(),
        std::slice::from_ref(&frame_is_empty)
    );
    assert_eq!(remainder.pattern.term, subject.term);
    assert_eq!(
        remainder.pattern.constraints,
        [Predicate::Not(Box::new(frame_is_empty))]
    );
}

#[cfg(feature = "z3")]
#[test]
fn narrows_a_closed_list_pattern_into_an_empty_subject_frame() {
    let definition = closed_collection_frame_definition();
    let subject = Pattern {
        term: internal_term(
            &definition,
            r#"listState{}(listConcat{}(listItem{}(\dv{SortElement{}}("first")), FRAME:SortList{}))"#,
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("closed List matching should produce applied and complementary branches");
    };
    let [branch] = branches.as_slice() else {
        panic!("the empty-frame assignment should be unique: {branches:?}");
    };
    let frame_is_empty = Predicate::Equals(
        internal_term(&definition, "FRAME:SortList{}"),
        internal_term(&definition, "listUnit{}()"),
    );

    assert_eq!(
        branch.pattern.term,
        internal_term(&definition, "listDone{}()")
    );
    assert_eq!(
        branch.pattern.constraints.as_slice(),
        std::slice::from_ref(&frame_is_empty)
    );
    assert_eq!(remainder.pattern.term, subject.term);
    assert_eq!(
        remainder.pattern.constraints,
        [Predicate::Not(Box::new(frame_is_empty))]
    );
}

#[cfg(feature = "z3")]
#[test]
fn branches_for_set_elements_while_preserving_an_open_subject_frame() {
    let definition = set_selection_definition();
    let first = r#"\dv{SortElement{}}("first")"#;
    let second = r#"\dv{SortElement{}}("second")"#;
    let subject = Pattern {
        term: internal_term(
            &definition,
            &format!(
                "state{{}}(setConcat{{}}(setConcat{{}}(setItem{{}}({first}), setItem{{}}({second})), SUBJECTREST:SortSet{{}}))"
            ),
        ),
        constraints: Vec::new(),
    };
    let mut fresh = 0;
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();

    let result = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver);
    let RewriteResult::Branch {
        branches,
        remainder,
        ..
    } = result.clone()
    else {
        panic!(
            "set selection should preserve the opaque subject frame in every branch: {result:#?}"
        );
    };
    let mut actual = branches
        .iter()
        .map(|branch| branch.pattern.term.clone())
        .collect::<Vec<_>>();
    actual.sort();
    let mut expected = vec![
        internal_term(
            &definition,
            &format!(
                "picked{{}}({first}, setConcat{{}}(setItem{{}}({second}), SUBJECTREST:SortSet{{}}))"
            ),
        ),
        internal_term(
            &definition,
            &format!(
                "picked{{}}({second}, setConcat{{}}(setItem{{}}({first}), SUBJECTREST:SortSet{{}}))"
            ),
        ),
    ];
    let fresh_frame = Variable::new("Ex#Frame!0", Sort::simple("SortSet"));
    let fresh_element = Variable::new("Ex#ELEMENT!1", Sort::simple("SortElement"));
    let fresh_terms = Substitution::from([
        (
            Variable::new("FRAME", Sort::simple("SortSet")),
            Term::variable(fresh_frame.clone()),
        ),
        (
            Variable::new("RULEELEMENT", Sort::simple("SortElement")),
            Term::variable(fresh_element.clone()),
        ),
    ]);
    expected.push(substitute(
            &internal_term(
                &definition,
                &format!(
                    "picked{{}}(RULEELEMENT:SortElement{{}}, setConcat{{}}(setConcat{{}}(setItem{{}}({first}), setItem{{}}({second})), FRAME:SortSet{{}}))"
                ),
            ),
            &fresh_terms,
        ));
    expected.sort();

    assert_eq!(actual, expected);
    assert!(
        branches
            .iter()
            .all(|branch| !branch.pattern.constraints.is_empty())
    );
    let frame_branch = branches
        .iter()
        .find(|branch| {
            branch
                .pattern
                .term
                .attributes()
                .variables
                .contains(&fresh_frame)
        })
        .expect("one branch should move the rule element into the subject frame");
    let assigned_frame = substitute(
        &internal_term(
            &definition,
            "setConcat{}(setItem{}(RULEELEMENT:SortElement{}), FRAME:SortSet{})",
        ),
        &fresh_terms,
    );
    assert!(
        frame_branch
            .pattern
            .constraints
            .contains(&Predicate::Equals(
                internal_term(&definition, "SUBJECTREST:SortSet{}"),
                assigned_frame,
            ))
    );
    let first = internal_term(&definition, first);
    let second = internal_term(&definition, second);
    let fresh_element_term = Term::variable(fresh_element.clone());
    let fresh_frame_term = Term::variable(fresh_frame.clone());
    for explicit in [&first, &second] {
        assert!(frame_branch.pattern.constraints.iter().any(|predicate| {
            matches!(predicate, Predicate::Not(inner)
                    if matches!(inner.as_ref(), Predicate::Equals(left, right)
                        if (left == explicit && right == &fresh_element_term)
                            || (left == &fresh_element_term && right == explicit)))
        }));
    }
    for element in [&first, &second, &fresh_element_term] {
        assert!(
            frame_branch
                .pattern
                .constraints
                .contains(&Predicate::Not(Box::new(Predicate::In(
                    element.clone(),
                    fresh_frame_term.clone()
                ),)))
        );
    }
    assert!(remainder.is_some());
}

#[cfg(feature = "z3")]
#[test]
fn rewrites_after_cancelling_common_opaque_set_chunks() {
    let definition = opaque_set_narrowing_definition();
    let subject = Pattern {
        term: internal_term(
            &definition,
            "state{}(setConcat{}(setItem{}(CONFIG:SortElement{}), setConcat{}(opaqueA{}(), setConcat{}(opaqueB{}(), setConcat{}(REST:SortSet{}, opaqueA{}())))))",
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(_),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("common opaque chunks should cancel before Set frame narrowing");
    };
    let [branch] = branches.as_slice() else {
        panic!("the residual Set frame has one solution: {branches:?}");
    };
    let TermKind::Application {
        symbol, arguments, ..
    } = branch.pattern.term.kind()
    else {
        panic!("rewrite result should be selected(RULE)");
    };
    assert_eq!(symbol.name.as_ref(), "selected");
    let [selected] = arguments.as_slice() else {
        panic!("selected should retain one element");
    };
    assert_eq!(
        selected,
        &internal_term(&definition, "CONFIG:SortElement{}")
    );
    assert!(
        branch.pattern.constraints.contains(&Predicate::Equals(
            internal_term(&definition, "REST:SortSet{}"),
            internal_term(&definition, "setUnit{}()"),
        )),
        "missing residual frame binding: {:#?}",
        branch.pattern.constraints
    );
    assert!(
        branch
            .pattern
            .constraints
            .contains(&Predicate::Ceil(internal_term(
                &definition,
                "setConcat{}(opaqueA{}(), setConcat{}(opaqueB{}(), opaqueB{}()))",
            ),))
    );
}

#[test]
fn branches_for_every_concrete_map_key_selection() {
    let definition = map_selection_definition();
    let first_key = r#"\dv{SortKey{}}("first")"#;
    let first_value = r#"\dv{SortValue{}}("first-value")"#;
    let second_key = r#"\dv{SortKey{}}("second")"#;
    let second_value = r#"\dv{SortValue{}}("second-value")"#;
    let subject = Pattern {
        term: internal_term(
            &definition,
            &format!(
                "mapState{{}}(mapConcat{{}}(mapItem{{}}({first_key}, {first_value}), mapItem{{}}({second_key}, {second_value})))"
            ),
        ),
        constraints: Vec::new(),
    };
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: None,
        ..
    } = rewrite_step(&definition, &subject, &mut fresh)
    else {
        panic!("map selection should produce one exhaustive branch per key");
    };
    let mut actual = branches
        .iter()
        .map(|branch| branch.pattern.term.clone())
        .collect::<Vec<_>>();
    actual.sort();
    let mut expected = vec![
        internal_term(
            &definition,
            &format!(
                "mapPicked{{}}({first_key}, {first_value}, mapItem{{}}({second_key}, {second_value}))"
            ),
        ),
        internal_term(
            &definition,
            &format!(
                "mapPicked{{}}({second_key}, {second_value}, mapItem{{}}({first_key}, {first_value}))"
            ),
        ),
    ];
    expected.sort();

    assert_eq!(actual, expected);
    assert!(
        branches
            .iter()
            .all(|branch| branch.pattern.constraints.is_empty())
    );
}

#[cfg(feature = "z3")]
#[test]
fn narrows_an_open_configuration_map_against_a_closed_rule_map() {
    let definition = closed_map_narrowing_definition();
    let subject = Pattern {
        term: internal_term(
            &definition,
            "mapState{}(mapConcat{}(mapItem{}(KEY:SortKey{}, VALUE:SortValue{}), REST:SortMap{}))",
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(_),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("symmetric Map unification should narrow both entry choices");
    };
    assert_eq!(branches.len(), 2);
    assert!(
        branches
            .iter()
            .all(|branch| branch.pattern.term == internal_term(&definition, "done{}()"))
    );

    for (key, value, remainder_key, remainder_value) in [
        ("first", "first-value", "second", "second-value"),
        ("second", "second-value", "first", "first-value"),
    ] {
        let key_binding = Predicate::Equals(
            internal_term(&definition, "KEY:SortKey{}"),
            internal_term(&definition, &format!(r#"\dv{{SortKey{{}}}}("{key}")"#)),
        );
        let value_binding = Predicate::Equals(
            internal_term(&definition, "VALUE:SortValue{}"),
            internal_term(&definition, &format!(r#"\dv{{SortValue{{}}}}("{value}")"#)),
        );
        let rest_binding = Predicate::Equals(
            internal_term(&definition, "REST:SortMap{}"),
            internal_term(
                &definition,
                &format!(
                    r#"mapItem{{}}(\dv{{SortKey{{}}}}("{remainder_key}"), \dv{{SortValue{{}}}}("{remainder_value}"))"#
                ),
            ),
        );
        assert!(branches.iter().any(|branch| {
            branch.pattern.constraints.contains(&key_binding)
                && branch.pattern.constraints.contains(&value_binding)
                && branch.pattern.constraints.contains(&rest_binding)
        }));
    }
}

#[cfg(feature = "z3")]
#[test]
fn composes_function_and_collection_unification_before_rewriting() {
    let definition = closed_map_narrowing_definition();
    let subject = Pattern {
        term: internal_term(
            &definition,
            "mixedState{}(CONFIG:SortValue{}, mapConcat{}(mapItem{}(KEY:SortKey{}, VALUE:SortValue{}), REST:SortMap{}))",
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(_),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("mixed first-order and collection equations should produce rewrite branches");
    };
    assert_eq!(branches.len(), 2);

    let mut selected_keys = Vec::new();
    for branch in &branches {
        let TermKind::Application {
            symbol, arguments, ..
        } = branch.pattern.term.kind()
        else {
            panic!("rewrite result should be selected(RULE)");
        };
        assert_eq!(symbol.name.as_ref(), "selected");
        let [fresh_rule] = arguments.as_slice() else {
            panic!("selected should retain exactly one fresh rule variable");
        };
        assert!(matches!(fresh_rule.kind(), TermKind::Variable(variable)
                if variable.name.starts_with("Ex#RULE")));
        let configuration_binding = Predicate::Equals(
            internal_term(&definition, "CONFIG:SortValue{}"),
            Term::application(
                definition.symbols["select"].clone(),
                Vec::new(),
                vec![fresh_rule.clone()],
            ),
        );
        assert!(branch.pattern.constraints.contains(&configuration_binding));

        let key_binding = branch.pattern.constraints.iter().find_map(|predicate| {
            let Predicate::Equals(left, right) = predicate else {
                return None;
            };
            (left == &internal_term(&definition, "KEY:SortKey{}")).then_some(right.clone())
        });
        selected_keys.push(key_binding.expect("each branch should constrain the Map key"));
    }
    selected_keys.sort();
    assert_eq!(
        selected_keys,
        [
            internal_term(&definition, r#"\dv{SortKey{}}("first")"#),
            internal_term(&definition, r#"\dv{SortKey{}}("second")"#),
        ]
    );
}

#[cfg(feature = "z3")]
#[test]
fn narrows_concrete_rule_map_keys_against_symbolic_configuration_keys() {
    let definition = symbolic_map_key_definition();
    let wanted = r#"\dv{SortKey{}}("wanted")"#;
    let selected_value = r#"\dv{SortValue{}}("selected")"#;
    let other_key = r#"\dv{SortKey{}}("other")"#;
    let other_value = r#"\dv{SortValue{}}("other-value")"#;
    let subject = Pattern {
        term: internal_term(
            &definition,
            &format!(
                "mapState{{}}(mapConcat{{}}(mapItem{{}}(KEY:SortKey{{}}, {selected_value}), mapItem{{}}({other_key}, {other_value})))"
            ),
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch {
        branches,
        remainder: Some(remainder),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("symbolic key selection should retain its complementary branch");
    };
    let [branch] = branches.as_slice() else {
        panic!("expected one symbolic key selection, found {branches:?}");
    };
    assert_eq!(
        branch.pattern.term,
        internal_term(
            &definition,
            &format!("mapPicked{{}}({selected_value}, mapItem{{}}({other_key}, {other_value}))")
        )
    );
    let selected = Predicate::Equals(
        internal_term(&definition, "KEY:SortKey{}"),
        internal_term(&definition, wanted),
    );
    assert_eq!(
        branch.pattern.constraints.as_slice(),
        std::slice::from_ref(&selected)
    );
    assert_eq!(
        remainder.pattern.constraints,
        [Predicate::Not(Box::new(selected))]
    );
}

#[cfg(feature = "z3")]
#[test]
fn does_not_rebind_configuration_variables_during_map_matching() {
    let definition = shared_symbolic_map_key_definition();
    let entry = internal_term(&definition, "ENTRY:SortKey{}");
    let requested = internal_term(&definition, "REQUESTED:SortKey{}");
    let subject = Pattern {
        term: internal_term(
            &definition,
            "request{}(mapConcat{}(mapItem{}(ENTRY:SortKey{}, VALUE:SortValue{}), MAP:SortMap{}), REQUESTED:SortKey{})",
        ),
        constraints: vec![Predicate::Not(Box::new(Predicate::Equals(
            entry, requested,
        )))],
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let result = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver);
    let RewriteResult::Branch { branches, .. } = result else {
        panic!("explicit and subject-frame selections should branch: {result:?}");
    };

    assert_eq!(branches.len(), 3);
    assert!(
        branches
            .iter()
            .any(|branch| branch.pattern.term == internal_term(&definition, "different{}()"))
    );
    assert!(branches.iter().all(|branch| {
        branch
            .substitution
            .keys()
            .all(|variable| variable.name.starts_with("Rule#"))
    }));
}

#[cfg(feature = "z3")]
#[test]
fn branches_for_map_keys_while_preserving_an_open_subject_frame() {
    let definition = map_selection_definition();
    let first_key = r#"\dv{SortKey{}}("first")"#;
    let first_value = r#"\dv{SortValue{}}("first-value")"#;
    let second_key = r#"\dv{SortKey{}}("second")"#;
    let second_value = r#"\dv{SortValue{}}("second-value")"#;
    let subject = Pattern {
        term: internal_term(
            &definition,
            &format!(
                "mapState{{}}(mapConcat{{}}(mapConcat{{}}(mapItem{{}}({first_key}, {first_value}), mapItem{{}}({second_key}, {second_value})), SUBJECTREST:SortMap{{}}))"
            ),
        ),
        constraints: Vec::new(),
    };
    let mut fresh = 0;
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();

    let result = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver);
    let RewriteResult::Branch {
        branches,
        remainder,
        ..
    } = result.clone()
    else {
        panic!(
            "map selection should preserve the opaque subject frame in every branch: {result:#?}"
        );
    };
    let mut actual = branches
        .iter()
        .map(|branch| branch.pattern.term.clone())
        .collect::<Vec<_>>();
    actual.sort();
    let mut expected = vec![
        internal_term(
            &definition,
            &format!(
                "mapPicked{{}}({first_key}, {first_value}, mapConcat{{}}(mapItem{{}}({second_key}, {second_value}), SUBJECTREST:SortMap{{}}))"
            ),
        ),
        internal_term(
            &definition,
            &format!(
                "mapPicked{{}}({second_key}, {second_value}, mapConcat{{}}(mapItem{{}}({first_key}, {first_value}), SUBJECTREST:SortMap{{}}))"
            ),
        ),
    ];
    let fresh_frame = Variable::new("Ex#Frame!0", Sort::simple("SortMap"));
    let fresh_key = Variable::new("Ex#KEY!1", Sort::simple("SortKey"));
    let fresh_value = Variable::new("Ex#VALUE!2", Sort::simple("SortValue"));
    let fresh_terms = Substitution::from([
        (
            Variable::new("FRAME", Sort::simple("SortMap")),
            Term::variable(fresh_frame.clone()),
        ),
        (
            Variable::new("RULEKEY", Sort::simple("SortKey")),
            Term::variable(fresh_key.clone()),
        ),
        (
            Variable::new("RULEVALUE", Sort::simple("SortValue")),
            Term::variable(fresh_value.clone()),
        ),
    ]);
    expected.push(substitute(
            &internal_term(
                &definition,
                &format!(
                    "mapPicked{{}}(RULEKEY:SortKey{{}}, RULEVALUE:SortValue{{}}, mapConcat{{}}(mapConcat{{}}(mapItem{{}}({first_key}, {first_value}), mapItem{{}}({second_key}, {second_value})), FRAME:SortMap{{}}))"
                ),
            ),
            &fresh_terms,
        ));
    expected.sort();

    assert_eq!(actual, expected);
    assert!(
        branches
            .iter()
            .all(|branch| !branch.pattern.constraints.is_empty())
    );
    let frame_branch = branches
        .iter()
        .find(|branch| {
            branch
                .pattern
                .term
                .attributes()
                .variables
                .contains(&fresh_frame)
        })
        .expect("one branch should move the rule entry into the subject frame");
    let assigned_frame = substitute(
        &internal_term(
            &definition,
            "mapConcat{}(mapItem{}(RULEKEY:SortKey{}, RULEVALUE:SortValue{}), FRAME:SortMap{})",
        ),
        &fresh_terms,
    );
    assert!(
        frame_branch
            .pattern
            .constraints
            .contains(&Predicate::Equals(
                internal_term(&definition, "SUBJECTREST:SortMap{}"),
                assigned_frame,
            ))
    );
    let first = internal_term(&definition, first_key);
    let second = internal_term(&definition, second_key);
    let fresh_key_term = Term::variable(fresh_key.clone());
    let fresh_frame_term = Term::variable(fresh_frame.clone());
    for explicit in [&first, &second] {
        assert!(frame_branch.pattern.constraints.iter().any(|predicate| {
            matches!(predicate, Predicate::Not(inner)
                    if matches!(inner.as_ref(), Predicate::Equals(left, right)
                        if (left == explicit && right == &fresh_key_term)
                            || (left == &fresh_key_term && right == explicit)))
        }));
    }
    for key in [&first, &second, &fresh_key_term] {
        assert!(
            frame_branch
                .pattern
                .constraints
                .contains(&Predicate::Not(Box::new(Predicate::In(
                    key.clone(),
                    fresh_frame_term.clone()
                ),)))
        );
    }
    let remainder = remainder.expect("symbolic selection should retain a complement");
    let quantified = remainder
        .pattern
        .constraints
        .iter()
        .filter_map(|predicate| {
            let Predicate::Not(complement) = predicate else {
                return None;
            };
            let mut quantified = BTreeSet::new();
            let mut complement = complement.as_ref();
            while let Predicate::Exists(variable, body) = complement {
                quantified.insert(variable.clone());
                complement = body;
            }
            quantified.contains(&fresh_frame).then_some(quantified)
        })
        .next()
        .unwrap_or_else(|| panic!("the frame complement should be quantified: {remainder:#?}"));
    assert_eq!(
        quantified,
        BTreeSet::from([fresh_frame, fresh_key, fresh_value])
    );
}

#[cfg(feature = "z3")]
#[test]
fn emits_frame_definedness_on_the_single_entry_path() {
    let definition = map_selection_definition();
    let first_key = r#"\dv{SortKey{}}("first")"#;
    let first_value = r#"\dv{SortValue{}}("first-value")"#;
    let subject_rest = internal_term(&definition, "SUBJECTREST:SortMap{}");
    let subject = Pattern {
        term: internal_term(
            &definition,
            &format!(
                "mapState{{}}(mapConcat{{}}(mapItem{{}}({first_key}, {first_value}), SUBJECTREST:SortMap{{}}))"
            ),
        ),
        constraints: Vec::new(),
    };
    let mut fresh = 0;
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();

    let RewriteResult::Branch {
        branches,
        remainder: Some(_),
        ..
    } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("the explicit and subject-frame selections should both be retained");
    };
    assert_eq!(branches.len(), 2);
    let explicit_term = internal_term(
        &definition,
        &format!("mapPicked{{}}({first_key}, {first_value}, SUBJECTREST:SortMap{{}})"),
    );
    let explicit = branches
        .iter()
        .find(|branch| branch.pattern.term == explicit_term)
        .expect("one branch should select the explicit entry");
    assert!(
        explicit
            .pattern
            .constraints
            .contains(&Predicate::Not(Box::new(Predicate::In(
                internal_term(&definition, first_key),
                subject_rest
            ),)))
    );
}

#[cfg(feature = "z3")]
#[test]
fn decomposes_false_map_membership_over_known_entries_and_a_remainder() {
    let definition = map_not_in_keys_rewrite_definition();
    let subject = Pattern {
        term: internal_term(
            &definition,
            r#"state{}(\dv{SortBool{}}("false"), SYMBOLIC:SortKey{})"#,
        ),
        constraints: Vec::new(),
    };
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let mut fresh = 0;

    let RewriteResult::Branch { branches, .. } =
        rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("false map membership should produce a constrained rewrite branch");
    };
    let [branch] = branches.as_slice() else {
        panic!("expected one map membership branch, found {branches:?}");
    };
    assert!(branch.pattern.constraints.iter().any(|condition| {
            matches!(condition, Predicate::Not(inner) if matches!(inner.as_ref(), Predicate::Equals(..)))
        }));
    let membership_conditions = branch
        .pattern
        .constraints
        .iter()
        .filter(|condition| {
            let term = match condition {
                Predicate::Equals(left, _) => Some(left),
                Predicate::Not(inner) => match inner.as_ref() {
                    Predicate::Term(term) => Some(term),
                    _ => None,
                },
                _ => None,
            };
            term.is_some_and(|term| {
                matches!(term.kind(), TermKind::Application { symbol, .. }
                        if symbol.attributes.hook.as_deref() == Some("MAP.in_keys"))
            })
        })
        .count();
    assert_eq!(membership_conditions, 2);
}

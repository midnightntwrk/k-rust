//! Public contracts of `k_rust_backend::rewrite`.

use std::{
    collections::BTreeSet,
    fmt::{Debug, Write},
    time::Duration,
};

#[cfg(feature = "z3")]
use k_rust_backend::substitution::substitute;
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
    smt::{NoSolver, Satisfiability, SmtError, SmtSolver, TranslationError, Validity},
    substitution::Substitution,
    term::{Sort, Term, TermKind, Variable},
    timeout::StepTimeoutMode,
    transition::{
        ExecutionIoState, ObservationEvent, ObservationFilterError, ObservationOptions,
        PatternDigest, TransitionClass, UncommittedReason,
    },
};
use k_rust_kore::{
    kore::parser::{parse_definition, parse_pattern},
    measure::{Counter, snapshot},
    names::BuiltinSort,
};
use sha2::{Digest, Sha256};

use crate::support::{
    ScriptedQuery, ScriptedSolver, ground_cell_set_definition, ground_overload_definition,
    internal_term,
};

fn assert_be08_capture(name: &str, value: &impl Debug, expected_sha256: &str) {
    let rendered = format!("{value:#?}");
    let mut actual = String::with_capacity(64);
    for byte in Sha256::digest(rendered.as_bytes()) {
        write!(actual, "{byte:02x}").unwrap();
    }
    if std::env::var_os("KRUST_BE08_CAPTURE").is_some() {
        eprintln!("BE08 capture {name}: sha256={actual}\n{rendered}");
    } else {
        assert_eq!(actual, expected_sha256, "BE08 capture {name}:\n{rendered}");
    }
}

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

fn console_io_definition(axioms: &str) -> BackendDefinition {
    let source = format!(
        r#"[]
            module MAIN
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                hooked-sort SortString{{}} [hook{{}}("STRING.String"), hasDomainValues{{}}()]
                sort SortIOError{{}} []
                sort SortIOInt{{}} []
                sort SortIOString{{}} []
                sort SortK{{}} []
                symbol inj{{From, To}}(From) : To [sortInjection{{}}(), injective{{}}()]
                symbol dotk{{}}() : SortK{{}} [constructor{{}}(), total{{}}()]
                symbol Lbl'Hash'EOF{{}}() : SortIOError{{}} [constructor{{}}(), total{{}}()]
                symbol initial{{}}() : SortK{{}} [constructor{{}}(), total{{}}()]
                symbol pending{{}}(SortK{{}}) : SortK{{}} [constructor{{}}(), total{{}}()]
                symbol pair{{}}(SortK{{}}, SortK{{}}) : SortK{{}} [constructor{{}}(), total{{}}()]
                symbol intPair{{}}(SortIOInt{{}}, SortIOInt{{}}) : SortK{{}} [constructor{{}}(), total{{}}()]
                symbol keepInt{{}}(SortIOInt{{}}) : SortK{{}} [constructor{{}}(), total{{}}()]
                symbol keepString{{}}(SortIOString{{}}) : SortK{{}} [constructor{{}}(), total{{}}()]
                symbol dead{{}}(SortK{{}}) : SortK{{}} [function{{}}(), total{{}}()]
                symbol deadInt{{}}(SortIOInt{{}}) : SortK{{}} [function{{}}(), total{{}}()]
                hooked-symbol getc{{}}(SortInt{{}}) : SortIOInt{{}}
                    [function{{}}(), total{{}}(), hook{{}}("IO.getc")]
                hooked-symbol read{{}}(SortInt{{}}, SortInt{{}}) : SortIOString{{}}
                    [function{{}}(), total{{}}(), hook{{}}("IO.read")]
                hooked-symbol putc{{}}(SortInt{{}}, SortInt{{}}) : SortK{{}}
                    [function{{}}(), total{{}}(), hook{{}}("IO.putc")]
                hooked-symbol write{{}}(SortInt{{}}, SortString{{}}) : SortK{{}}
                    [function{{}}(), total{{}}(), hook{{}}("IO.write")]
                {axioms}
            endmodule []"#
    );
    let syntax = parse_definition(&source).expect("console definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("console definition should internalize")
}

fn console_pattern(definition: &BackendDefinition, pattern: &str) -> Pattern {
    definition
        .internalize_pattern(&parse_pattern(pattern).expect("pattern should parse"), &[])
        .expect("pattern should internalize")
}

#[test]
fn direct_rewrite_rejects_a_nested_surviving_macro_without_recovery() {
    let source = r#"[]
        module MAIN
            sort SortS{} []
            symbol state{}(SortS{}) : SortS{} [constructor{}(), total{}()]
            symbol c{}(SortS{}) : SortS{} [constructor{}(), total{}()]
            symbol a{}() : SortS{} [constructor{}(), total{}()]
            symbol done{}() : SortS{} [constructor{}(), total{}()]
            symbol m{}(SortS{}) : SortS{}
                [functional{}(), injective{}(), macro{}(), no-evaluators{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(state{}(c{}(X:SortS{})), \top{SortS{}}()),
                done{}()
            ) [label{}("execute")]
        endmodule []"#;
    let syntax = parse_definition(source).expect("definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
    let subject = Pattern {
        term: internal_term(&definition, "state{}(m{}(a{}()))"),
        constraints: Vec::new(),
    };
    let before = snapshot();
    let mut fresh = 0;

    let result = rewrite_step(&definition, &subject, &mut fresh);
    let delta = snapshot().delta(&before);

    assert_eq!(
        result,
        RewriteResult::Indeterminate {
            pattern: subject.clone(),
            reason: IndeterminateReason::SurvivingMacroOrAlias { symbol: "m".into() },
        }
    );
    assert_eq!(fresh, 0);
    assert_eq!(delta.get(Counter::RewriteIndeterminateRecoveries), 0);
    assert_eq!(delta.get(Counter::MatchingPairs), 0);

    let before = snapshot();
    let execution = execute(
        &definition,
        subject,
        ExecutionOptions {
            max_depth: 0,
            ..ExecutionOptions::default()
        },
    );
    let delta = snapshot().delta(&before);
    let [leaf] = execution.leaves.as_slice() else {
        panic!("expected one invalid-input leaf: {execution:?}");
    };
    assert_eq!(
        leaf.halt_reason,
        HaltReason::Indeterminate(IndeterminateReason::SurvivingMacroOrAlias {
            symbol: "m".into(),
        })
    );
    assert_eq!(leaf.depth, 0);
    assert_eq!(delta.get(Counter::SimplifyRounds), 0);
    assert_eq!(delta.get(Counter::RewriteIndeterminateRecoveries), 0);
    assert_eq!(delta.get(Counter::MatchingPairs), 0);

    let constrained = Pattern {
        term: internal_term(&definition, "state{}(a{}())"),
        constraints: vec![Predicate::Equals(
            internal_term(&definition, "m{}(a{}())"),
            internal_term(&definition, "a{}()"),
        )],
    };
    let before = snapshot();
    let rewrite = rewrite_step(&definition, &constrained, &mut 0);
    assert!(matches!(
        rewrite,
        RewriteResult::Indeterminate {
            reason: IndeterminateReason::SurvivingMacroOrAlias { ref symbol },
            ..
        } if symbol.as_ref() == "m"
    ));
    let execution = execute(
        &definition,
        constrained.clone(),
        ExecutionOptions {
            max_depth: 0,
            max_breadth: Some(0),
            ..ExecutionOptions::default()
        },
    );
    assert!(matches!(
        execution.leaves.as_slice(),
        [ExecutionLeaf {
            halt_reason: HaltReason::Indeterminate(
                IndeterminateReason::SurvivingMacroOrAlias { symbol }
            ),
            ..
        }] if symbol.as_ref() == "m"
    ));
    let state_search = k_rust_backend::search::search_graph(
        &definition,
        constrained.clone(),
        k_rust_backend::search::SearchOptions {
            max_breadth: Some(0),
            ..k_rust_backend::search::SearchOptions::default()
        },
    );
    assert!(matches!(
        state_search.incomplete.as_slice(),
        [k_rust_backend::search::IncompleteSearch::Indeterminate {
            reason: IndeterminateReason::SurvivingMacroOrAlias { symbol },
            ..
        }] if symbol.as_ref() == "m"
    ));
    let path_search = k_rust_backend::search::search_paths(
        &definition,
        constrained,
        k_rust_backend::search::SearchOptions {
            max_results: Some(0),
            ..k_rust_backend::search::SearchOptions::default()
        },
    );
    assert!(matches!(
        path_search.incomplete.as_slice(),
        [k_rust_backend::search::IncompleteSearch::Indeterminate {
            reason: IndeterminateReason::SurvivingMacroOrAlias { symbol },
            ..
        }] if symbol.as_ref() == "m"
    ));
    let delta = snapshot().delta(&before);
    assert_eq!(delta.get(Counter::SimplifyRounds), 0);
    assert_eq!(delta.get(Counter::RewriteIndeterminateRecoveries), 0);
    assert_eq!(delta.get(Counter::MatchingPairs), 0);
}

#[test]
fn spawning_a_distinct_normalized_ground_cell_has_no_residual_inequality() {
    let definition = ground_cell_set_definition();
    let value = r#"\dv{SortValue{}}("a")"#;
    let subject = Pattern {
        term: internal_term(
            &definition,
            &format!("spawnDistinct{{}}(setItem{{}}(cell{{}}(f{{}}({value}))))"),
        ),
        constraints: Vec::new(),
    };

    let solver = FixedSolver {
        satisfiability: Ok(Satisfiability::Sat),
        validity: Ok(Validity::Indeterminate),
    };
    let result = rewrite_step_with_solver(&definition, &subject, &mut 0, &solver);
    let RewriteResult::Finished(applied) = result else {
        panic!("the rule must produce a successor rather than a trivial result: {result:?}");
    };
    assert_eq!(applied.unique_id, "spawn-distinct");
    assert_eq!(
        applied.pattern.term,
        internal_term(
            &definition,
            &format!(
                "spawnDistinct{{}}(setConcat{{}}(setItem{{}}(cell{{}}(f{{}}({value}))), setItem{{}}(cell{{}}(g{{}}({value})))))"
            ),
        ),
    );
    assert!(applied.pattern.constraints.is_empty());
}

#[test]
fn spawning_a_duplicate_ground_cell_uses_set_idempotence_without_a_constraint() {
    let definition = ground_cell_set_definition();
    let value = r#"\dv{SortValue{}}("a")"#;
    let subject = Pattern {
        term: internal_term(
            &definition,
            &format!("spawnDuplicate{{}}(setItem{{}}(cell{{}}(f{{}}({value}))))"),
        ),
        constraints: Vec::new(),
    };

    let solver = FixedSolver {
        satisfiability: Ok(Satisfiability::Sat),
        validity: Ok(Validity::Indeterminate),
    };
    let result = rewrite_step_with_solver(&definition, &subject, &mut 0, &solver);
    let RewriteResult::Finished(applied) = result else {
        panic!("the idempotent set rule must produce a successor: {result:?}");
    };
    assert_eq!(applied.unique_id, "spawn-duplicate");
    assert_eq!(applied.pattern.term, subject.term);
    assert!(applied.pattern.constraints.is_empty());
}

#[test]
fn ground_non_result_overload_heats_without_a_remainder_branch() {
    let definition = ground_overload_definition();
    let subject = Pattern {
        term: internal_term(
            &definition,
            "state{}(exps{}(fun{}(), inj{SortVals{}, SortExps{}}(dotVals{}())))",
        ),
        constraints: Vec::new(),
    };

    let result = rewrite_step(&definition, &subject, &mut 0);
    let RewriteResult::Finished(applied) = result else {
        panic!("the ground heating condition must be decided: {result:?}");
    };
    assert_eq!(applied.unique_id, "heat-non-result");
    assert_eq!(
        applied.pattern.term,
        internal_term(&definition, "heated{}()")
    );
    assert!(applied.pattern.constraints.is_empty());
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

fn cell_map_coverage_definition() -> BackendDefinition {
    let syntax = parse_definition(include_str!("../fixtures/cell-map-coverage.kore"))
        .expect("cell-map coverage fixture should parse");
    BackendDefinition::internalize(&syntax, "CELL-MAP-COVERAGE")
        .expect("cell-map coverage fixture should internalize")
}

fn cell_map_thread(definition: &BackendDefinition, key: &str, head: &str) -> Term {
    internal_term(
        definition,
        &format!(
            "mapItem{{}}(\\dv{{SortKey{{}}}}(\"{key}\"), thread{{}}(\\dv{{SortKey{{}}}}(\"{key}\"), kseq{{}}({head}, dotk{{}}())))"
        ),
    )
}

fn cell_map_state(definition: &BackendDefinition, entries: &[Term]) -> Pattern {
    let map = entries
        .iter()
        .cloned()
        .reduce(|left, right| {
            Term::application(
                definition.symbols["mapConcat"].clone(),
                Vec::new(),
                vec![left, right],
            )
        })
        .expect("a cell-map test state has at least one thread");
    Pattern {
        term: Term::application(
            definition.symbols["cellState"].clone(),
            Vec::new(),
            vec![map],
        ),
        constraints: Vec::new(),
    }
}

fn cell_set_coverage_definition() -> BackendDefinition {
    let syntax = parse_definition(include_str!("../fixtures/cell-set-coverage.kore"))
        .expect("cell-set coverage fixture should parse");
    BackendDefinition::internalize(&syntax, "CELL-SET-COVERAGE")
        .expect("cell-set coverage fixture should internalize")
}

fn cell_set_task(definition: &BackendDefinition, head: &str) -> Term {
    internal_term(
        definition,
        &format!("setItem{{}}(task{{}}(kseq{{}}({head}, dotk{{}}())))"),
    )
}

fn cell_set_state(definition: &BackendDefinition, entries: &[Term]) -> Pattern {
    let set = entries
        .iter()
        .cloned()
        .reduce(|left, right| {
            Term::application(
                definition.symbols["setConcat"].clone(),
                Vec::new(),
                vec![left, right],
            )
        })
        .expect("a cell-set test state has at least one task");
    Pattern {
        term: Term::application(
            definition.symbols["cellState"].clone(),
            Vec::new(),
            vec![set],
        ),
        constraints: Vec::new(),
    }
}

#[test]
fn cell_map_heating_rejects_rigid_heads_and_allows_a_lower_priority_rule() {
    let definition = cell_map_coverage_definition();
    let int_head = r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("0"))"#;
    let stmt_head = "inj{SortStmt{}, SortKItem{}}(stmt{}())";

    for entries in [
        vec![cell_map_thread(&definition, "first", int_head)],
        vec![
            cell_map_thread(&definition, "first", int_head),
            cell_map_thread(&definition, "second", stmt_head),
        ],
    ] {
        let subject = cell_map_state(&definition, &entries);
        let result = rewrite_step(&definition, &subject, &mut 0);
        let RewriteResult::Finished(applied) = result else {
            panic!("an impossible heating match must not block the fallback: {result:?}");
        };
        assert_eq!(applied.unique_id, "fallback");
        assert_eq!(
            applied.pattern.term,
            internal_term(&definition, "fallback{}()")
        );
        assert!(applied.pattern.constraints.is_empty());
    }
}

#[test]
fn cell_map_heating_selects_the_entry_with_the_literal_anywhere_head() {
    let definition = cell_map_coverage_definition();
    let other = cell_map_thread(
        &definition,
        "first",
        r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("0"))"#,
    );
    let matching = cell_map_thread(
        &definition,
        "second",
        "inj{SortExp{}, SortKItem{}}(heat{}(expA{}(), expB{}()))",
    );
    let subject = cell_map_state(&definition, &[other.clone(), matching]);

    let result = rewrite_step(&definition, &subject, &mut 0);
    let RewriteResult::Finished(applied) = result else {
        panic!("the literal heating head should select exactly one cell: {result:?}");
    };
    assert_eq!(applied.unique_id, "heat");
    assert_eq!(
        applied.pattern.term,
        Term::application(
            definition.symbols["heated"].clone(),
            Vec::new(),
            vec![
                internal_term(&definition, r#"\dv{SortKey{}}("second")"#),
                internal_term(&definition, "expA{}()"),
                internal_term(&definition, "expB{}()"),
                other,
            ],
        )
    );
    assert!(applied.pattern.constraints.is_empty());
}

#[test]
fn cell_set_heating_rejects_rigid_heads_and_selects_the_literal_anywhere_head() {
    let definition = cell_set_coverage_definition();
    let int_head = r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("0"))"#;
    let stmt_head = "inj{SortStmt{}, SortKItem{}}(stmt{}())";
    for entries in [
        vec![cell_set_task(&definition, int_head)],
        vec![
            cell_set_task(&definition, int_head),
            cell_set_task(&definition, stmt_head),
        ],
    ] {
        let subject = cell_set_state(&definition, &entries);
        let result = rewrite_step(&definition, &subject, &mut 0);
        let RewriteResult::Finished(applied) = result else {
            panic!("an impossible Set-cell heating match must allow the fallback: {result:?}");
        };
        assert_eq!(applied.unique_id, "fallback");
        assert!(applied.pattern.constraints.is_empty());
    }

    let other = cell_set_task(&definition, "inj{SortExp{}, SortKItem{}}(expA{}())");
    let matching = cell_set_task(
        &definition,
        "inj{SortExp{}, SortKItem{}}(heat{}(expA{}(), expB{}()))",
    );
    let subject = cell_set_state(&definition, &[other.clone(), matching]);
    let result = rewrite_step(&definition, &subject, &mut 0);
    let RewriteResult::Finished(applied) = result else {
        panic!("the literal heating head should select exactly one Set element: {result:?}");
    };
    assert_eq!(applied.unique_id, "heat");
    assert_eq!(
        applied.pattern.term,
        Term::application(
            definition.symbols["heated"].clone(),
            Vec::new(),
            vec![
                internal_term(&definition, "expA{}()"),
                internal_term(&definition, "expB{}()"),
                other,
            ],
        )
    );
    assert!(applied.pattern.constraints.is_empty());
}

#[test]
fn any_mode_keeps_one_collection_candidate_while_all_keeps_both() {
    let definition = cell_set_coverage_definition();
    let subject = cell_set_state(
        &definition,
        &[
            cell_set_task(
                &definition,
                "inj{SortExp{}, SortKItem{}}(heat{}(expA{}(), expB{}()))",
            ),
            cell_set_task(
                &definition,
                "inj{SortExp{}, SortKItem{}}(heat{}(expB{}(), expA{}()))",
            ),
        ],
    );

    let RewriteResult::Branch { branches, .. } = rewrite_step(&definition, &subject, &mut 0) else {
        panic!("all mode must retain both Set candidates");
    };
    assert_eq!(branches.len(), 2);

    let before = snapshot();
    let result = rewrite_step_sequential_with_solver(&definition, &subject, &mut 0, &NoSolver);
    let delta = snapshot().delta(&before);
    let RewriteResult::Finished(applied) = result else {
        panic!("any mode must retain one Set candidate: {result:?}");
    };
    assert_eq!(applied.unique_id, "heat");
    assert!(applied.pattern.constraints.is_empty());
    assert_eq!(delta.get(Counter::RewriteRulesApplied), 1);
}

fn ground_anywhere_defense_definition() -> BackendDefinition {
    let source = include_str!("../fixtures/rewrite-coverage.kore").replace(
        "endmodule []",
        r#"axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(state{}(ordinaryFunction{}(E:SortS{})), \top{SortS{}}()),
    heated{}(E:SortS{})
  ) [label{}("ground-defense"), priority{}("41")]
endmodule []"#,
    );
    let syntax = parse_definition(&source).expect("ground defense definition should parse");
    BackendDefinition::internalize(&syntax, "REWRITE-COVERAGE")
        .expect("ground defense definition should internalize")
}

#[test]
fn concrete_anywhere_head_rejects_a_different_rigid_head() {
    let definition = rewrite_coverage_definition();
    let subject = Pattern {
        term: internal_term(&definition, "state{}(id{}())"),
        constraints: Vec::new(),
    };
    assert!(subject.term.attributes().constructor_like);
    let mut fresh = 0;
    let result = rewrite_step(&definition, &subject, &mut fresh);
    let RewriteResult::Finished(applied) = result else {
        panic!("a different anywhere head must not block the applicable lookup: {result:?}");
    };
    assert_eq!(applied.unique_id, "lookup");
    assert_eq!(fresh, 0);
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
            &format!("state{{}}(ordinaryFunction{{}}(E:SortS{{}})), {requires}"),
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
            let heated = branches
                .iter()
                .find(|branch| branch.unique_id == "heat")
                .expect("the covered high-priority branch remains visible");
            assert_eq!(
                heated.pattern.term,
                internal_term(&definition, "heated{}(id{}())")
            );
            assert_eq!(
                heated.pattern.constraints,
                vec![Predicate::Equals(
                    internal_term(&definition, "ordinaryFunction{}(id{}())"),
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
fn ground_anywhere_fragments_do_not_enable_narrowing() {
    let definition = ground_anywhere_defense_definition();
    let subject = Pattern {
        term: internal_term(&definition, "state{}(overloadedList{}(id{}()))"),
        constraints: Vec::new(),
    };
    assert!(!subject.term.attributes().constructor_like);
    assert!(subject.term.concrete_after_normalization());
    let solver = FixedSolver {
        satisfiability: Ok(Satisfiability::Sat),
        validity: Ok(Validity::Indeterminate),
    };
    let mut fresh = 0;
    let result = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver);
    assert!(matches!(
        result,
        RewriteResult::Indeterminate {
            reason: IndeterminateReason::Instantiation {
                ref rule_id,
                ref missing_variables,
            },
            ..
        } if rule_id == "ground-defense" && missing_variables.len() == 1
    ));
    assert_eq!(fresh, 0, "a ground configuration must not be narrowed");
}

#[test]
fn symbolic_anywhere_fragments_still_enable_narrowing() {
    let definition = ground_anywhere_defense_definition();
    let subject = Pattern {
        term: internal_term(&definition, "state{}(overloadedList{}(SUBJECT:SortS{}))"),
        constraints: Vec::new(),
    };
    assert!(!subject.term.concrete_after_normalization());
    let solver = FixedSolver {
        satisfiability: Ok(Satisfiability::Sat),
        validity: Ok(Validity::Indeterminate),
    };
    let mut fresh = 0;
    let RewriteResult::Branch { branches, .. } =
        rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
    else {
        panic!("a symbolic configuration must retain narrowing")
    };
    assert!(
        branches
            .iter()
            .any(|branch| branch.unique_id == "ground-defense")
    );
    assert!(fresh > 0);
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
    assert!(branches.iter().any(|branch| branch.unique_id == "heat"));
    assert_eq!(fresh, 1);
    assert!(
        remainder
            .pattern
            .constraints
            .iter()
            .any(|predicate| matches!(predicate, Predicate::Not(inner)
            if matches!(inner.as_ref(), Predicate::Exists(..))))
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

    assert!(matches!(
        result,
        RewriteResult::Trivial(pattern, _) if pattern == subject
    ));
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

    assert!(
        matches!(
            &result,
            RewriteResult::Trivial(pattern, applications)
                if pattern == &subject
                    && matches!(applications.as_slice(), [TrivialApplication {
                        rule_id,
                        label: Some(label),
                        obligation: Predicate::False,
                        ..
                    }] if rule_id == "bottom" && label == "bottom")
        ),
        "{result:#?}"
    );
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
            halt_reason: HaltReason::Trivial {
                depth: 1,
                rule_id: Some(rule_id),
                label: Some(label),
                obligation: Predicate::False,
            },
            ..
        }] if rule_id == "bottom" && label == "bottom"
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

    assert!(matches!(
        rewrite_step(&definition, &initial, &mut fresh),
        RewriteResult::Trivial(pattern, _) if pattern == initial
    ));
    assert!(matches!(
        execute(&definition, initial.clone(), ExecutionOptions::default())
            .leaves
            .as_slice(),
        [ExecutionLeaf {
            depth: 0,
            halt_reason: HaltReason::Trivial { .. },
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
        remainder,
        trivial,
        ..
    } = rewrite_step_with_solver(&definition, &initial, &mut fresh, &solver)
    else {
        panic!("the step should retain both the trivial sub-case and lower fallback");
    };
    assert_eq!(branches.len(), 1);
    assert_eq!(branches[0].unique_id, "fallback");
    assert!(remainder.is_none());
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

    let execution = execute_with_solver(&definition, initial, ExecutionOptions::default(), &solver);
    let [leaf] = execution.leaves.as_slice() else {
        panic!("the complement should reach the fallback exactly once");
    };
    assert!(matches!(leaf.halt_reason, HaltReason::Stuck));
    assert!(matches!(
        leaf.pattern.term.kind(),
        TermKind::DomainValue { value, .. } if value == "20"
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
        TermKind::DomainValue { value, .. } if value == "survivor"
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
        TermKind::DomainValue { value, .. } if value == "20"
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
            halt_reason: HaltReason::Vacuous {
                depth: 0,
                rule_id: None,
                label: None,
                constraint: Predicate::False,
            },
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

    assert!(
        matches!(
            rewritten.leaves.as_slice(),
            [ExecutionLeaf {
                pattern: Pattern { term, constraints },
                depth: 1,
                halt_reason: HaltReason::Vacuous {
                    depth: 1,
                    rule_id: Some(rule_id),
                    label: Some(label),
                    constraint,
                },
                ..
            }] if term == &internal_term(&definition, "d{}()")
                && rule_id == "step"
                && label == "step"
                && matches!(constraint, Predicate::And(predicates)
                    if predicates.iter().any(|predicate| matches!(predicate, Predicate::False)))
                && constraints.iter().any(|predicate| matches!(predicate, Predicate::False))
        ),
        "{rewritten:#?}"
    );
    assert!(matches!(
        stuck.leaves.as_slice(),
        [ExecutionLeaf {
            depth: 0,
            halt_reason: HaltReason::Vacuous {
                depth: 0,
                rule_id: None,
                label: None,
                ..
            },
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

fn be08_s0_definition() -> BackendDefinition {
    symbolic_remainder_definition(
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
    )
}

fn be08_s1_definition() -> BackendDefinition {
    let mut rules = String::new();
    for index in 0..8 {
        rules.push_str(&format!(
            r#"
            axiom{{}} \rewrites{{SortInt{{}}}}(
                \and{{SortInt{{}}}}(
                    wrap{{}}(X:SortInt{{}}),
                    \equals{{SortBool{{}}, SortInt{{}}}}(
                        lt{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("{index}")),
                        \dv{{SortBool{{}}}}("true")
                    )
                ),
                \dv{{SortInt{{}}}}("{}")
            ) [label{{}}("be08-symbolic-{index}"), priority{{}}("{}")]
            "#,
            100 + index,
            10 + index * 10,
        ));
    }
    rules.push_str(
        r#"
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
            \dv{SortInt{}}("200")
        ) [label{}("be08-fallback-a"), priority{}("90")]
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
            \dv{SortInt{}}("201")
        ) [label{}("be08-fallback-b"), priority{}("90")]
        "#,
    );
    symbolic_remainder_definition(&rules)
}

fn be08_portable_definition(rules: &str) -> BackendDefinition {
    let source = r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            sort SortString{} [hasDomainValues{}()]
            sort SortIOError{} []
            sort SortIOInt{} []
            sort SortK{} []
            symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
            symbol Lbl'Hash'EOF{}() : SortIOError{} [constructor{}(), total{}()]
            symbol state{}(SortInt{}) : SortK{} [constructor{}(), total{}(), injective{}()]
            symbol dotk{}() : SortK{} [constructor{}(), total{}()]
            symbol done{}() : SortK{} [constructor{}(), total{}()]
            symbol tag{}(SortInt{}) : SortK{} [constructor{}(), total{}(), injective{}()]
            symbol dead{}(SortK{}) : SortK{} [function{}(), total{}()]
            symbol expand{}(SortK{}) : SortK{} [function{}(), total{}()]
            symbol opaque{}() : SortBool{} [function{}(), total{}(), no-evaluators{}()]
            symbol isIOInt{}(SortIOInt{}) : SortBool{}
                [function{}(), total{}(), no-evaluators{}()]
            symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), smt-hook{}("<")]
            hooked-symbol getc{}(SortInt{}) : SortIOInt{}
                [function{}(), total{}(), hook{}("IO.getc")]
            hooked-symbol log{}(SortString{}) : SortK{}
                [function{}(), hook{}("IO.logString")]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortK{}, R}(
                    dead{}(X:SortK{}),
                    \and{SortK{}}(X:SortK{}, \bottom{SortK{}}())
                )
            ) [label{}("dead"), simplification{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortK{}, R}(
                    expand{}(X:SortK{}),
                    \and{SortK{}}(expand{}(expand{}(X:SortK{})), \top{SortK{}}())
                )
            ) [label{}("expand"), simplification{}()]
            $RULES
        endmodule []"#
        .replace("$RULES", rules);
    let syntax = parse_definition(&source).expect("BE08 portable definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("BE08 portable definition should internalize")
}

fn be08_portable_subject(definition: &BackendDefinition) -> Pattern {
    definition
        .internalize_pattern(&parse_pattern("state{}(X:SortInt{})").unwrap(), &[])
        .unwrap()
}

fn be08_stopped_options() -> ExecutionOptions {
    ExecutionOptions {
        branch_mode: ExecutionBranchMode::StopAtBranch,
        ..ExecutionOptions::default()
    }
}

fn be08_indeterminate_solver(sat_answers: usize, validity_answers: usize) -> ScriptedSolver {
    ScriptedSolver::new(
        (0..sat_answers).map(|_| Ok(Satisfiability::Sat)),
        (0..validity_answers).map(|_| Ok(Validity::Indeterminate)),
    )
}

fn rewritten_value(result: RewriteResult) -> String {
    let RewriteResult::Finished(applied) = result else {
        panic!("expected finished rewrite, found {result:?}");
    };
    let TermKind::DomainValue { value, .. } = applied.pattern.term.kind() else {
        panic!("expected domain value, found {:?}", applied.pattern.term);
    };
    value.as_utf8().unwrap().to_owned()
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
fn element_variable_bindings_to_set_patterns_do_not_rewrite() {
    // `wrap(I) => pair(I, I)` is an axiom for every element `I`; instantiating it at the set
    // variable `@Y` is not justified, so the step is indeterminate rather than a rewrite.
    let definition = definition(
        r#"
            symbol pair{}(SortS{}, SortS{}) : SortS{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(I:SortS{}), \top{SortS{}}()),
                pair{}(I:SortS{}, I:SortS{})
            ) [label{}("duplicate")]
            "#,
    );
    let mut fresh = 0;

    let set_subject = Pattern {
        term: internal_term(&definition, "wrap{}(@Y:SortS{})"),
        constraints: Vec::new(),
    };
    assert!(matches!(
        rewrite_step(&definition, &set_subject, &mut fresh),
        RewriteResult::Indeterminate {
            reason: IndeterminateReason::Match { rule_id, remainder, .. },
            ..
        } if rule_id == "duplicate" && remainder.is_empty()
    ));

    let element_subject = Pattern {
        term: internal_term(&definition, "wrap{}(X:SortS{})"),
        constraints: Vec::new(),
    };
    let RewriteResult::Finished(applied) = rewrite_step(&definition, &element_subject, &mut fresh)
    else {
        panic!("an element variable subject should rewrite");
    };
    assert_eq!(
        applied.pattern.term,
        internal_term(&definition, "pair{}(X:SortS{}, X:SortS{})")
    );
}

#[test]
fn untranslatable_requires_is_an_smt_indeterminate_leaf() {
    // A `requires` the SMT encoding cannot pose is still a constraint of the rule instance,
    // so the attempt is indeterminate and the leaf names the encoding limit, not a failure.
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
    let pattern = Pattern {
        term: internal_term(&definition, "wrap{}(Y:SortS{})"),
        constraints: Vec::new(),
    };
    let untranslatable = TranslationError::NonBooleanAnd(internal_term(
        &definition,
        r"\and{SortS{}}(Y:SortS{}, Z:SortS{})",
    ));
    let solver = FixedSolver {
        satisfiability: Ok(Satisfiability::Sat),
        validity: Err(SmtError::Translation(untranslatable.clone())),
    };
    let mut fresh = 0;

    assert!(matches!(
        rewrite_step_with_solver(&definition, &pattern, &mut fresh, &solver),
        RewriteResult::Indeterminate {
            reason: IndeterminateReason::Smt {
                rule_id,
                error: SmtError::Translation(error),
            },
            ..
        } if rule_id == "conditional" && error == untranslatable
    ));
}

/// The rewriter's leaf for one solver verdict.
enum VerdictLeaf {
    /// The step rewrites and its successor carries exactly these constraints.
    Finished(Vec<Predicate>),
    /// The step is trivial on the pre-step pattern.
    Trivial,
    /// The step is an `IndeterminateReason::Smt` leaf naming this error.
    Smt(SmtError),
}

/// Every verdict of a solver over one rewrite step on `subject`, as the rewriter's leaf.
fn assert_solver_verdicts(
    definition: &BackendDefinition,
    subject: &Pattern,
    verdicts: &[(Result<Validity, SmtError>, VerdictLeaf)],
) {
    for (validity, expected) in verdicts {
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: validity.clone(),
        };
        let mut fresh = 0;
        let result = rewrite_step_with_solver(definition, subject, &mut fresh, &solver);
        match expected {
            VerdictLeaf::Finished(constraints) => {
                let RewriteResult::Finished(applied) = result else {
                    panic!("{validity:?} should rewrite, got {result:?}");
                };
                assert_eq!(&applied.pattern.constraints, constraints, "{validity:?}");
            }
            VerdictLeaf::Trivial => {
                assert!(
                    matches!(result, RewriteResult::Trivial(pattern, _) if pattern == *subject),
                    "{validity:?}"
                );
            }
            VerdictLeaf::Smt(error) => {
                assert!(
                    matches!(
                        &result,
                        RewriteResult::Indeterminate {
                            reason: IndeterminateReason::Smt { error: leaf, .. },
                            ..
                        } if leaf == error
                    ),
                    "{validity:?}: {result:?}"
                );
            }
        }
    }
}

#[test]
fn rhs_definedness_obligation_verdicts_are_mapped_per_site() {
    // The obligation `\ceil(partial(X))` of the rule's right-hand side is decided under the
    // rule instance's knowledge: refuted, or inconsistent with that knowledge, means the
    // instance is empty and the step is trivial on the pre-step pattern; every verdict the
    // solver does not reach carries the obligation into the successor.
    let definition = definition(
        r#"
            symbol partial{}(SortS{}) : SortS{} [function{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                wrap{}(partial{}(X:SortS{}))
            ) [label{}("partialize")]
            "#,
    );
    let subject = Pattern {
        term: internal_term(&definition, r#"wrap{}(\dv{SortS{}}("start"))"#),
        constraints: Vec::new(),
    };
    let obligation = Predicate::Ceil(internal_term(
        &definition,
        r#"partial{}(\dv{SortS{}}("start"))"#,
    ));
    let untranslatable = TranslationError::NonBooleanAnd(internal_term(
        &definition,
        r"\and{SortS{}}(Y:SortS{}, Z:SortS{})",
    ));

    assert_solver_verdicts(
        &definition,
        &subject,
        &[
            (Ok(Validity::Valid), VerdictLeaf::Finished(Vec::new())),
            (Ok(Validity::Invalid), VerdictLeaf::Trivial),
            (Ok(Validity::InconsistentGroundTruth), VerdictLeaf::Trivial),
            (
                Ok(Validity::Indeterminate),
                VerdictLeaf::Finished(vec![obligation.clone()]),
            ),
            (
                Ok(Validity::Unknown("timeout".into())),
                VerdictLeaf::Finished(vec![obligation.clone()]),
            ),
            (
                Err(SmtError::Translation(untranslatable)),
                VerdictLeaf::Finished(vec![obligation.clone()]),
            ),
            (
                Err(SmtError::Unavailable),
                VerdictLeaf::Finished(vec![obligation]),
            ),
        ],
    );
}

#[test]
fn ensures_verdicts_are_mapped_per_site_in_the_rewriter() {
    // An `ensures` is a conjunct of the successor by definition: valid, it is dropped;
    // refuted or inconsistent with the rule instance's knowledge, the step is trivial on the
    // pre-step pattern; an open implication or a missing solver carries it; a solver that
    // was asked and did not answer, or could not pose the query, is an indeterminate leaf.
    let definition = definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \and{SortS{}}(
                    \dv{SortS{}}("done"),
                    \equals{SortS{}, SortS{}}(X:SortS{}, \dv{SortS{}}("expected"))
                )
            ) [label{}("ensured")]
            "#,
    );
    let subject = Pattern {
        term: internal_term(&definition, "wrap{}(Z:SortS{})"),
        constraints: Vec::new(),
    };
    let ensures = Predicate::Equals(
        internal_term(&definition, "Z:SortS{}"),
        internal_term(&definition, r#"\dv{SortS{}}("expected")"#),
    );
    let untranslatable = TranslationError::NonBooleanAnd(internal_term(
        &definition,
        r"\and{SortS{}}(Y:SortS{}, Z:SortS{})",
    ));

    assert_solver_verdicts(
        &definition,
        &subject,
        &[
            (Ok(Validity::Valid), VerdictLeaf::Finished(Vec::new())),
            (Ok(Validity::Invalid), VerdictLeaf::Trivial),
            (Ok(Validity::InconsistentGroundTruth), VerdictLeaf::Trivial),
            (
                Ok(Validity::Indeterminate),
                VerdictLeaf::Finished(vec![ensures.clone()]),
            ),
            (
                Err(SmtError::Unavailable),
                VerdictLeaf::Finished(vec![ensures]),
            ),
            (
                Ok(Validity::Unknown("timeout".into())),
                VerdictLeaf::Smt(SmtError::Unknown("timeout".into())),
            ),
            (
                Err(SmtError::Translation(untranslatable.clone())),
                VerdictLeaf::Smt(SmtError::Translation(untranslatable)),
            ),
        ],
    );
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

/// T1 / I1, I3. Complete result and branch constraints captured at 40b5d6d214cdd833e027a814744d9f98c5e7542d.
#[cfg(feature = "z3")]
#[test]
fn cascades_a_remainder_through_every_lower_priority_group() {
    let definition = be08_s1_definition();
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let result = execute_with_solver(
        &definition,
        symbolic_subject(&definition),
        be08_stopped_options(),
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
        panic!("expected ten complete branches and no remainder: {result:#?}");
    };
    assert_eq!(
        branches
            .iter()
            .map(|branch| branch.label.as_deref().unwrap())
            .collect::<Vec<_>>(),
        [
            "be08-fallback-a",
            "be08-fallback-b",
            "be08-symbolic-7",
            "be08-symbolic-6",
            "be08-symbolic-5",
            "be08-symbolic-4",
            "be08-symbolic-3",
            "be08-symbolic-2",
            "be08-symbolic-1",
            "be08-symbolic-0",
        ]
    );
    assert!(result.discarded.is_empty());
    assert_be08_capture(
        "T1 complete ExecutionResult",
        &result,
        "a35579acc1f5e824cf717ad1205e11d3e61c779cca6b8ee5fc1bbc1d7fe801c6",
    );
}

/// T2 / I3, I4. Complete constraints captured at 40b5d6d214cdd833e027a814744d9f98c5e7542d.
#[cfg(feature = "z3")]
#[test]
fn stopped_branch_reports_lower_groups_before_the_first_productive_group() {
    let definition = be08_s0_definition();
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let result = execute_with_solver(
        &definition,
        symbolic_subject(&definition),
        be08_stopped_options(),
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
        panic!("expected four complete branches and no remainder: {result:#?}");
    };
    assert_eq!(
        branches
            .iter()
            .map(|branch| branch.label.as_deref().unwrap())
            .collect::<Vec<_>>(),
        ["zero-a", "zero-b", "negative", "positive"]
    );
    assert!(result.discarded.is_empty());
    assert_be08_capture(
        "T2 complete ExecutionResult",
        &result,
        "ea380a26a24994f8f20363e3daf30dff00542a67a52ff66f865fe0600e33deb5",
    );
}

/// T7 / I4. Complete remainder captured at 40b5d6d214cdd833e027a814744d9f98c5e7542d.
#[cfg(feature = "z3")]
#[test]
fn cascade_keeps_the_remainder_when_lower_groups_are_stuck() {
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
                \and{SortInt{}}(wrap{}(X:SortInt{}), \bottom{SortInt{}}()),
                \dv{SortInt{}}("50")
            ) [label{}("lower-stuck"), priority{}("50")]
            "#,
    );
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let result = execute_with_solver(
        &definition,
        symbolic_subject(&definition),
        be08_stopped_options(),
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
        panic!("expected one branch and a retained remainder: {result:#?}");
    };
    assert_eq!(branches.len(), 1);
    assert_eq!(remainder.rule_ids, ["negative"]);
    assert!(matches!(
        remainder.pattern.constraints.as_slice(),
        [Predicate::Not(_)]
    ));
    assert!(result.discarded.is_empty());
    assert_be08_capture(
        "T7 complete ExecutionResult",
        &result,
        "e859e1363abecd5d7c0435e6487107409af0790d00d68cf339ddc603441eb254",
    );
}

/// Any mode returns its complete remainder without a second rewrite round.
#[cfg(feature = "z3")]
#[test]
fn any_mode_stopped_branch_uses_the_steps_remainder() {
    let definition = symbolic_remainder_definition(
        r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("10")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("100")
            ) [label{}("conditional"), priority{}("10")]
            "#,
    );
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let result = execute_with_solver(
        &definition,
        symbolic_subject(&definition),
        ExecutionOptions {
            mode: ExecutionMode::Any,
            branch_mode: ExecutionBranchMode::StopAtBranch,
            ..ExecutionOptions::default()
        },
        &solver,
    );

    let [
        ExecutionLeaf {
            halt_reason: HaltReason::Branch { branches, .. },
            ..
        },
    ] = result.leaves.as_slice()
    else {
        panic!("expected the Any-mode stopped branch: {result:#?}");
    };
    assert_eq!(
        branches
            .iter()
            .map(|branch| branch.label.as_deref().unwrap())
            .collect::<Vec<_>>(),
        ["conditional"]
    );
    let HaltReason::Branch {
        remainder: Some(remainder),
        ..
    } = &result.leaves[0].halt_reason
    else {
        panic!("expected the step to retain the satisfiable remainder: {result:#?}");
    };
    assert_eq!(remainder.rule_ids, ["conditional"]);
    assert_be08_capture(
        "T15 complete ExecutionResult",
        &result,
        "5e2d1522e27fcbdcfaed3393ffad649d3f4f916a8b15610428fc4774741a5949",
    );
}

/// A lower-group failure is confined to the remainder so higher-priority branches survive.
#[test]
fn later_group_simplification_error_is_reported_on_the_remainder() {
    let definition = be08_portable_definition(
        r#"
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(
                state{}(X:SortInt{}),
                \equals{SortBool{}, SortK{}}(
                    lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                    \dv{SortBool{}}("true")
                )
            ),
            log{}(\dv{SortString{}}("first"))
        ) [label{}("first"), priority{}("10")]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(
                state{}(X:SortInt{}),
                \equals{SortBool{}, SortK{}}(
                    lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                    \dv{SortBool{}}("true")
                )
            ),
            dead{}(log{}(\dv{SortString{}}("trivial")))
        ) [label{}("trivial"), priority{}("10")]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(
                state{}(X:SortInt{}),
                \equals{SortBool{}, SortK{}}(
                    isIOInt{}(getc{}(\dv{SortInt{}}("0"))),
                    \dv{SortBool{}}("true")
                )
            ),
            done{}()
        ) [label{}("lower-error"), priority{}("50")]
        "#,
    );
    let solver = be08_indeterminate_solver(1, 5);
    let initial = be08_portable_subject(&definition);
    let result = execute_observed_with_solver(
        &definition,
        initial.clone(),
        be08_stopped_options(),
        &solver,
        &ObservationOptions::all(),
    );
    let transcript = solver.transcript.borrow().clone();

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one stopped branch leaf: {result:#?}");
    };
    assert_eq!(leaf.pattern, initial);
    let HaltReason::Branch {
        branches,
        remainder: Some(remainder),
    } = &leaf.halt_reason
    else {
        panic!("expected a branch with an indeterminate remainder: {result:#?}");
    };
    assert_eq!(branches.len(), 1, "{result:#?}");
    assert_eq!(branches[0].label.as_deref(), Some("first"));
    assert!(matches!(
        remainder.indeterminate,
        Some(IndeterminateReason::Simplification { .. })
    ));
    assert_eq!(result.discarded.len(), 1, "{result:#?}");
    assert_be08_capture(
        "T8 result and solver transcript",
        &(&result, &transcript),
        "a9ef3d506a17d64d1c49603d8f7839898574059205dda75e910d4b02743b4654",
    );
}

/// Cancellation during the complete step is observed at the execution boundary.
#[test]
fn cancellation_during_lower_group_work_is_observed_after_the_step() {
    let definition = be08_portable_definition(
        r#"
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(
                state{}(X:SortInt{}),
                \equals{SortBool{}, SortK{}}(
                    lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                    \dv{SortBool{}}("true")
                )
            ),
            log{}(\dv{SortString{}}("first"))
        ) [label{}("first"), priority{}("10")]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(
                state{}(X:SortInt{}),
                \equals{SortBool{}, SortK{}}(
                    lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                    \dv{SortBool{}}("true")
                )
            ),
            dead{}(log{}(\dv{SortString{}}("trivial")))
        ) [label{}("trivial"), priority{}("10")]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(
                state{}(X:SortInt{}),
                \equals{SortBool{}, SortK{}}(
                    lt{}(\dv{SortInt{}}("0"), X:SortInt{}),
                    \dv{SortBool{}}("true")
                )
            ),
            log{}(\dv{SortString{}}("lower"))
        ) [label{}("lower"), priority{}("50")]
        "#,
    );
    let token = CancellationToken::new();
    // Query four is the lower group's remainder SAT query in the 40b5d6d transcript.
    let solver = ScriptedSolver::new(
        [Ok(Satisfiability::Sat), Ok(Satisfiability::Unsat)],
        (0..3).map(|_| Ok(Validity::Indeterminate)),
    )
    .cancelling_at(4, token.clone());
    let result = token.scope(|| {
        execute_observed_with_solver(
            &definition,
            be08_portable_subject(&definition),
            be08_stopped_options(),
            &solver,
            &ObservationOptions::all(),
        )
    });
    let transcript = solver.transcript.borrow().clone();

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one cancelled leaf: {result:#?}");
    };
    assert_eq!(transcript.len(), 5, "{transcript:#?}");
    assert!(matches!(
        transcript.get(4),
        Some(ScriptedQuery::IsSat { .. })
    ));
    assert_be08_capture(
        "T9 result and solver transcript",
        &(&result, &transcript),
        "6f3edcdc9cee1d5526a977bbe8aeb730f64713c350a67fc707724247aa31c067",
    );
    assert_eq!(leaf.halt_reason, HaltReason::Cancelled);
    assert!(result.discarded.is_empty(), "{result:#?}");
}

/// T10 / D2. The S2-P2 cascade skips the replay's indeterminate re-attempt and reaches the
/// unconditional lower group; its expected outcome follows D2 in the 40b5d6d design.
#[test]
fn cascade_continues_where_a_reattempt_would_have_been_indeterminate() {
    let definition = be08_portable_definition(
        r#"
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(
                state{}(X:SortInt{}),
                \and{SortK{}}(
                    \equals{SortBool{}, SortK{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("5")),
                        \dv{SortBool{}}("true")
                    ),
                    \equals{SortBool{}, SortK{}}(
                        lt{}(\dv{SortInt{}}("-5"), X:SortInt{}),
                        \dv{SortBool{}}("true")
                    )
                )
            ),
            tag{}(\dv{SortInt{}}("10"))
        ) [label{}("conditional"), priority{}("10")]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(state{}(X:SortInt{}), \top{SortK{}}()),
            tag{}(\dv{SortInt{}}("50"))
        ) [label{}("fallback"), priority{}("50")]
        "#,
    );
    let solver = ScriptedSolver::new(
        [Ok(Satisfiability::Sat)],
        [
            Ok(Validity::Indeterminate),
            Ok(Validity::Unknown("BE08 scripted unknown".into())),
            Ok(Validity::Indeterminate),
            Ok(Validity::Indeterminate),
            Ok(Validity::Indeterminate),
        ],
    );
    let result = execute_with_solver(
        &definition,
        be08_portable_subject(&definition),
        be08_stopped_options(),
        &solver,
    );
    let transcript = solver.transcript.borrow().clone();
    assert!(solver.answers.borrow().is_empty());
    assert_eq!(solver.validity.borrow().len(), 1);

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
        panic!("expected the cascade to reach the unconditional lower group: {result:#?}");
    };
    assert!(matches!(
        transcript.as_slice(),
        [
            ScriptedQuery::CheckPredicates { .. },
            ScriptedQuery::IsSat { .. },
            ScriptedQuery::CheckPredicates { .. },
            ScriptedQuery::CheckPredicates { .. },
            ScriptedQuery::CheckPredicates { .. },
        ]
    ));
    assert_eq!(
        branches
            .iter()
            .map(|branch| branch.label.as_deref().unwrap())
            .collect::<Vec<_>>(),
        ["fallback", "conditional"]
    );
}

/// T12 / I10. Complete leaf and diagnostics captured at 40b5d6d214cdd833e027a814744d9f98c5e7542d.
#[test]
fn lower_group_budget_exhaustion_keeps_partial_successors_under_diagnostic_collection() {
    let definition = be08_portable_definition(
        r#"
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(
                state{}(X:SortInt{}),
                \equals{SortBool{}, SortK{}}(
                    lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                    \dv{SortBool{}}("true")
                )
            ),
            tag{}(\dv{SortInt{}}("10"))
        ) [label{}("first"), priority{}("10")]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(state{}(X:SortInt{}), \top{SortK{}}()),
            expand{}(tag{}(\dv{SortInt{}}("50")))
        ) [label{}("lower-budget"), priority{}("50")]
        "#,
    );
    let solver = be08_indeterminate_solver(1, 3);
    let (result, diagnostics) = diagnostic::collect(|| {
        execute_with_solver(
            &definition,
            be08_portable_subject(&definition),
            ExecutionOptions {
                branch_mode: ExecutionBranchMode::StopAtBranch,
                max_simplification_iterations: 1,
                ..ExecutionOptions::default()
            },
            &solver,
        )
    });
    let transcript = solver.transcript.borrow().clone();
    assert!(solver.answers.borrow().is_empty());
    assert!(solver.validity.borrow().is_empty());

    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    assert_eq!(
        diagnostics,
        [BackendDiagnostic::SimplificationBudgetExhausted {
            limit: 1,
            subject: BudgetSubject::Term,
        }]
    );
    assert_be08_capture(
        "T12 result, diagnostics, and solver transcript",
        &(&result, &diagnostics, &transcript),
        "66bc024d90dbebe65c5463cc12e597e46592bfd652c5035bd9f3e3123af1b813",
    );
}

/// Trivial sub-cases from every productive group remain visible to the driver.
#[test]
fn complete_step_classifies_effects_from_every_group() {
    let definition = be08_portable_definition(
        r#"
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(
                state{}(X:SortInt{}),
                \equals{SortBool{}, SortK{}}(
                    lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                    \dv{SortBool{}}("true")
                )
            ),
            log{}(\dv{SortString{}}("first"))
        ) [label{}("first"), priority{}("10")]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(
                state{}(X:SortInt{}),
                \equals{SortBool{}, SortK{}}(
                    lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                    \dv{SortBool{}}("true")
                )
            ),
            dead{}(log{}(\dv{SortString{}}("trivial")))
        ) [label{}("trivial"), priority{}("10")]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(state{}(X:SortInt{}), \top{SortK{}}()),
            dead{}(log{}(\dv{SortString{}}("lower-dead")))
        ) [label{}("lower-dead"), priority{}("50")]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(state{}(X:SortInt{}), \top{SortK{}}()),
            log{}(\dv{SortString{}}("lower-live"))
        ) [label{}("lower-live"), priority{}("50")]
        "#,
    );
    let solver = be08_indeterminate_solver(1, 4);
    let result = execute_observed_with_solver(
        &definition,
        be08_portable_subject(&definition),
        be08_stopped_options(),
        &solver,
        &ObservationOptions::all(),
    );
    let transcript = solver.transcript.borrow().clone();
    assert!(solver.answers.borrow().is_empty());
    assert!(solver.validity.borrow().is_empty());

    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    assert_eq!(result.discarded.len(), 2, "{result:#?}");
    assert_eq!(result.discarded[0].id.rule, "lower-dead");
    assert_eq!(result.discarded[1].id.rule, "trivial");
    assert!(
        result
            .discarded
            .iter()
            .all(|candidate| candidate.reason == UncommittedReason::RolledBack)
    );
    assert_be08_capture(
        "T13 result and solver transcript",
        &(&result, &transcript),
        "14a896d829e9c3d23c27f0a0d569f12a4b8b72b382040754a3e7ca08272aae0c",
    );
}

/// T14 / I6. Cursor, transcript, and result captured at 40b5d6d214cdd833e027a814744d9f98c5e7542d.
#[test]
fn ground_io_candidates_are_rejected_without_touching_the_retained_cursor_across_a_cascade() {
    let definition = console_io_definition(
        r#"
        hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
        symbol opaque{}() : SortBool{} [function{}(), total{}(), no-evaluators{}()]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(
                initial{}(),
                \equals{SortBool{}, SortK{}}(
                    opaque{}(),
                    \dv{SortBool{}}("true")
                )
            ),
            dotk{}()
        ) [label{}("first"), priority{}("10")]
        axiom{R} \implies{R}(
            \top{R}(),
            \equals{SortK{}, R}(
                deadInt{}(X:SortIOInt{}),
                \and{SortK{}}(dotk{}(), \bottom{SortK{}}())
            )
        ) [label{}("dead-int"), simplification{}()]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(initial{}(), \top{SortK{}}()),
            deadInt{}(getc{}(\dv{SortInt{}}("0")))
        ) [label{}("lower-dead"), priority{}("50")]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(initial{}(), \top{SortK{}}()),
            keepInt{}(getc{}(\dv{SortInt{}}("0")))
        ) [label{}("lower-live"), priority{}("50")]
        "#,
    );
    let solver = be08_indeterminate_solver(1, 1);
    let (result, _) = execute_disjunction_with_solver_and_io_state_and_observer_with_initial_status(
        &definition,
        vec![console_pattern(&definition, "initial{}()")],
        be08_stopped_options(),
        &solver,
        ExecutionIoState::new(Vec::from(&b"Z"[..])),
        |_| {},
    );
    let transcript = solver.transcript.borrow().clone();

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one lower-group IO error leaf: {result:#?}");
    };
    assert_eq!(leaf.io.cursor(), 0);
    assert!(leaf.io.transcript().is_empty());
    assert!(matches!(
        leaf.halt_reason,
        HaltReason::Simplification(SimplificationError::UnsupportedHook { ref hook, .. })
            if hook == "IO.getc"
    ));
    assert_be08_capture(
        "T14 result and solver transcript",
        &(&result, &transcript),
        "4d0dfcea473c4dbf87ce626639145e48fccd12daad459f2d594f5f79dc73278f",
    );
}

/// T16 / cut_terminal. Both complete results captured at 40b5d6d214cdd833e027a814744d9f98c5e7542d.
#[test]
fn cut_point_and_terminal_rules_after_a_cascade_that_leaves_one_survivor() {
    let definition = be08_portable_definition(
        r#"
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(
                state{}(X:SortInt{}),
                \equals{SortBool{}, SortK{}}(
                    lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                    \dv{SortBool{}}("true")
                )
            ),
            dead{}(tag{}(\dv{SortInt{}}("10")))
        ) [label{}("first-dead"), priority{}("10")]
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(state{}(X:SortInt{}), \top{SortK{}}()),
            tag{}(\dv{SortInt{}}("50"))
        ) [label{}("stop"), priority{}("50")]
        "#,
    );
    let cut_solver = be08_indeterminate_solver(1, 3);
    let cut = execute_with_solver(
        &definition,
        be08_portable_subject(&definition),
        ExecutionOptions {
            branch_mode: ExecutionBranchMode::StopAtBranch,
            cut_point_rules: BTreeSet::from(["stop".into()]),
            ..ExecutionOptions::default()
        },
        &cut_solver,
    );
    let terminal_solver = be08_indeterminate_solver(1, 3);
    let terminal = execute_with_solver(
        &definition,
        be08_portable_subject(&definition),
        ExecutionOptions {
            branch_mode: ExecutionBranchMode::StopAtBranch,
            terminal_rules: BTreeSet::from(["stop".into()]),
            ..ExecutionOptions::default()
        },
        &terminal_solver,
    );
    assert_be08_capture(
        "T16 cut-point and terminal results",
        &(
            &cut,
            &*cut_solver.transcript.borrow(),
            &terminal,
            &*terminal_solver.transcript.borrow(),
        ),
        "1ee774e100f1ef533d0e6f83ee0472ff6db36ae982eb6a510fa0caeb8746bf4e",
    );
    assert!(cut_solver.answers.borrow().is_empty());
    assert!(cut_solver.validity.borrow().is_empty());
    assert!(terminal_solver.answers.borrow().is_empty());
    assert!(terminal_solver.validity.borrow().is_empty());

    let [cut_leaf] = cut.leaves.as_slice() else {
        panic!("expected one cut-point leaf: {cut:#?}");
    };
    assert_eq!(cut_leaf.depth, 1);
    assert_eq!(cut_leaf.halt_reason, HaltReason::Stuck);
    let [terminal_leaf] = terminal.leaves.as_slice() else {
        panic!("expected one terminal leaf: {terminal:#?}");
    };
    assert_eq!(terminal_leaf.depth, 1);
    assert_eq!(terminal_leaf.halt_reason, HaltReason::Stuck);
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
            value.as_utf8().unwrap().to_owned()
        })
        .collect::<Vec<_>>();
    values.sort();
    assert_eq!(values, ["-1", "20"]);
    assert!(result.leaves.iter().all(|leaf| {
        leaf.trace
            .iter()
            .all(|entry| entry.kind != TraceKind::Remainder)
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
                && matches!(right.kind(), TermKind::DomainValue { value, .. } if value == "0")
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
        TermKind::DomainValue { value, .. } if value == "done"
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
        TermKind::DomainValue { value, .. } if value == "done"
    ));
}

/// Two ground function definitions whose evaluation never reaches a value and never runs
/// out of iteration budget before it runs out of stack: `down(N) = 1 +Int down(N +Int 1)`
/// recurses in the term, and `h(N) = 0 requires h(N +Int 1) ==Int 0` recurses through the
/// condition of its only equation, where every condition starts a fresh iteration budget.
/// Every step of either is a determined ground function step, which the budget does not count.
/// `go-down` and `go-nest` expose `down(N)` and `h(N)` to the simplifier after one rewrite step.
fn stack_exhaustion_definition() -> BackendDefinition {
    definition(
        r#"
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-symbol intAdd{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.add")]
            hooked-symbol intEq{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), hook{}("INT.eq")]
            symbol down{}(SortInt{}) : SortInt{} [function{}()]
            symbol h{}(SortInt{}) : SortInt{} [function{}()]
            symbol startNest{}(SortInt{}) : SortS{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            symbol startDown{}(SortInt{}) : SortS{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            symbol kbox{}(SortInt{}) : SortS{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, N:SortInt{}), \top{R}())),
                \equals{SortInt{}, R}(
                    down{}(X0:SortInt{}),
                    \and{SortInt{}}(
                        intAdd{}(
                            \dv{SortInt{}}("1"),
                            down{}(intAdd{}(N:SortInt{}, \dv{SortInt{}}("1")))
                        ),
                        \top{SortInt{}}()
                    )
                )
            ) [label{}("down")]
            axiom{R} \implies{R}(
                \and{R}(
                    \equals{SortBool{}, R}(
                        intEq{}(h{}(intAdd{}(N:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    ),
                    \and{R}(\in{SortInt{}, R}(X0:SortInt{}, N:SortInt{}), \top{R}())
                ),
                \equals{SortInt{}, R}(
                    h{}(X0:SortInt{}),
                    \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}())
                )
            ) [label{}("h-nest")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(startNest{}(N:SortInt{}), \top{SortS{}}()),
                kbox{}(h{}(N:SortInt{}))
            ) [label{}("go-nest")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(startDown{}(N:SortInt{}), \top{SortS{}}()),
                kbox{}(down{}(N:SortInt{}))
            ) [label{}("go-down")]
            "#,
    )
}

fn int_application(definition: &BackendDefinition, symbol: &str, value: i64) -> Term {
    Term::application(
        definition.symbols[symbol].clone(),
        Vec::new(),
        vec![Term::domain_value(
            Sort::simple("SortInt"),
            value.to_string(),
        )],
    )
}

/// Run `body` on a fresh thread with `stack_size` bytes of stack and return its result; a
/// native stack overflow would abort the test process instead.
fn on_thread_with_stack<T: Send + 'static>(
    name: &str,
    stack_size: usize,
    body: impl FnOnce() -> T + Send + 'static,
) -> T {
    std::thread::Builder::new()
        .name(name.into())
        .stack_size(stack_size)
        .spawn(body)
        .expect("the regression thread should start")
        .join()
        .expect("the regression thread should complete")
}

#[test]
fn unbounded_non_tail_recursion_reports_an_exhausted_stack() {
    let result = on_thread_with_stack("down-unbounded", 64 * 1024 * 1024, || {
        let definition = stack_exhaustion_definition();
        k_rust_backend::simplify::simplify(
            &definition,
            &int_application(&definition, "down", 0),
            SimplificationOptions::unbounded(),
        )
    });
    assert_eq!(result, Err(SimplificationError::StackExhausted));
}

#[test]
fn an_embedder_sized_thread_reports_an_exhausted_stack() {
    // A 2 MiB thread is the Rust default for spawned threads and the size of an ordinary
    // embedder's worker; the guard reads the bounds of whatever thread runs the simplifier.
    let result = on_thread_with_stack("down-2mib", 2 * 1024 * 1024, || {
        let definition = stack_exhaustion_definition();
        k_rust_backend::simplify::simplify(
            &definition,
            &int_application(&definition, "down", 0),
            SimplificationOptions::unbounded(),
        )
    });
    assert_eq!(result, Err(SimplificationError::StackExhausted));
}

#[test]
fn stack_exhaustion_in_an_equation_condition_ends_execution_with_the_error() {
    // Each evaluation of `h`'s condition starts a fresh iteration budget, so only the stack
    // bounds the nesting. The condition fallback must not decide the unsimplified condition:
    // that would block the equation and report a silent `Stuck` with `h(0)` unevaluated.
    let result = on_thread_with_stack("nest-default", 64 * 1024 * 1024, || {
        let definition = stack_exhaustion_definition();
        execute(
            &definition,
            Pattern {
                term: int_application(&definition, "startNest", 0),
                constraints: Vec::new(),
            },
            ExecutionOptions::default(),
        )
    });
    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one leaf, found {:?}", result.leaves);
    };
    assert_eq!(
        leaf.halt_reason,
        HaltReason::Simplification(SimplificationError::StackExhausted)
    );
}

#[test]
fn divergent_ground_recursion_at_the_default_budget_ends_with_an_exhausted_stack() {
    // Every step of `down(0)` is a determined ground function step, so the default iteration
    // budget does not cut it into a `Stuck` state with `down` unevaluated; the thread's stack
    // bounds the recursion and execution reports that as the state's error.
    let result = on_thread_with_stack("down-default", 64 * 1024 * 1024, || {
        let definition = stack_exhaustion_definition();
        execute(
            &definition,
            Pattern {
                term: int_application(&definition, "startDown", 0),
                constraints: Vec::new(),
            },
            ExecutionOptions::default(),
        )
    });
    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one leaf, found {:?}", result.leaves);
    };
    assert_eq!(
        leaf.halt_reason,
        HaltReason::Simplification(SimplificationError::StackExhausted)
    );
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

/// How `size` is defined in `equation_requires_budget_definition`.
#[derive(Clone, Copy)]
enum SizeEquations {
    /// Function equations: each step over a ground chain is a determined step of the
    /// definition's own computation, which the iteration budget does not count.
    Function,
    /// `simplification{}()` equations, which the iteration budget bounds.
    Simplification,
}

/// The end of the `cons` chain in `equation_requires_budget_subject`.
#[derive(Clone, Copy)]
enum ChainTail {
    /// `nil`: the chain is ground.
    Nil,
    /// The variable `WS:SortStack`: every `size` redex on the chain is symbolic.
    Symbolic,
}

/// A `cons` chain, `size` as equations of the kind `size`, and a function `prepare` whose two
/// equations carry `size(S) >=Int 1024` and `size(S) <Int 1024` in their `requires`; the rewrite
/// rule `dispatch` exposes `prepare(S)` to the simplifier. Evaluating `size` over the chain is one
/// lineage as long as the chain, so whenever the budget counts its steps, the budget decides
/// whether either `requires` is decided.
fn equation_requires_budget_definition(size: SizeEquations) -> BackendDefinition {
    let size_equations = match size {
        SizeEquations::Function => {
            r#"
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortStack{}, R}(X0:SortStack{}, nil{}()), \top{R}())),
                \equals{SortInt{}, R}(
                    size{}(X0:SortStack{}),
                    \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}())
                )
            ) [label{}("size-nil")]
            axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(
                        \in{SortStack{}, R}(X0:SortStack{}, cons{}(H:SortInt{}, T:SortStack{})),
                        \top{R}()
                    )
                ),
                \equals{SortInt{}, R}(
                    size{}(X0:SortStack{}),
                    \and{SortInt{}}(
                        intAdd{}(\dv{SortInt{}}("1"), size{}(T:SortStack{})),
                        \top{SortInt{}}()
                    )
                )
            ) [label{}("size-cons")]
            "#
        }
        SizeEquations::Simplification => {
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortInt{}, R}(
                    size{}(nil{}()),
                    \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}())
                )
            ) [label{}("size-nil"), simplification{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortInt{}, R}(
                    size{}(cons{}(H:SortInt{}, T:SortStack{})),
                    \and{SortInt{}}(
                        intAdd{}(\dv{SortInt{}}("1"), size{}(T:SortStack{})),
                        \top{SortInt{}}()
                    )
                )
            ) [label{}("size-cons"), simplification{}()]
            "#
        }
    };
    definition(
        &r#"
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            sort SortStack{} []
            symbol nil{}() : SortStack{} [constructor{}(), total{}()]
            symbol cons{}(SortInt{}, SortStack{}) : SortStack{} [constructor{}(), total{}()]
            hooked-symbol intAdd{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.add")]
            hooked-symbol intGe{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), hook{}("INT.ge")]
            hooked-symbol intLt{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), hook{}("INT.lt")]
            symbol size{}(SortStack{}) : SortInt{} [function{}(), total{}()]
            symbol prepare{}(SortStack{}) : SortS{} [function{}()]
            symbol stackState{}(SortStack{}) : SortS{} [function{}(), total{}(), injective{}(), no-evaluators{}()]
            SIZE_EQUATIONS
            axiom{R} \implies{R}(
                \and{R}(
                    \equals{SortBool{}, R}(
                        intGe{}(size{}(S:SortStack{}), \dv{SortInt{}}("1024")),
                        \dv{SortBool{}}("true")
                    ),
                    \and{R}(\in{SortStack{}, R}(X0:SortStack{}, S:SortStack{}), \top{R}())
                ),
                \equals{SortS{}, R}(
                    prepare{}(X0:SortStack{}),
                    \and{SortS{}}(\dv{SortS{}}("overflow"), \top{SortS{}}())
                )
            ) [label{}("prepare-overflow")]
            axiom{R} \implies{R}(
                \and{R}(
                    \equals{SortBool{}, R}(
                        intLt{}(size{}(S:SortStack{}), \dv{SortInt{}}("1024")),
                        \dv{SortBool{}}("true")
                    ),
                    \and{R}(\in{SortStack{}, R}(X0:SortStack{}, S:SortStack{}), \top{R}())
                ),
                \equals{SortS{}, R}(
                    prepare{}(X0:SortStack{}),
                    \and{SortS{}}(\dv{SortS{}}("ok"), \top{SortS{}}())
                )
            ) [label{}("prepare-ok")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(stackState{}(S:SortStack{}), \top{SortS{}}()),
                prepare{}(S:SortStack{})
            ) [label{}("dispatch")]
            "#
        .replace("SIZE_EQUATIONS", size_equations),
    )
}

fn equation_requires_budget_subject(
    definition: &BackendDefinition,
    depth: usize,
    tail: ChainTail,
) -> Pattern {
    let mut stack = match tail {
        ChainTail::Nil => {
            Term::application(definition.symbols["nil"].clone(), Vec::new(), Vec::new())
        }
        ChainTail::Symbolic => Term::variable(Variable::new("WS", Sort::simple("SortStack"))),
    };
    for index in 0..depth {
        stack = Term::application(
            definition.symbols["cons"].clone(),
            Vec::new(),
            vec![
                Term::domain_value(Sort::simple("SortInt"), index.to_string()),
                stack,
            ],
        );
    }
    Pattern {
        term: Term::application(
            definition.symbols["stackState"].clone(),
            Vec::new(),
            vec![stack],
        ),
        constraints: Vec::new(),
    }
}

/// The execution of `equation_requires_budget_definition` on a chain of `depth` elements, with
/// the diagnostics it emitted and the counters it moved.
struct EquationRequiresRun {
    result: ExecutionResult,
    diagnostics: Vec<BackendDiagnostic>,
    counters: k_rust_kore::measure::Snapshot,
}

fn run_equation_requires_budget(
    size: SizeEquations,
    tail: ChainTail,
    depth: usize,
    max_simplification_iterations: usize,
) -> EquationRequiresRun {
    // The chain is a deep constructor term and `size` recurses once per element. Run on the
    // 64 MiB stack the CLI and RPC workers use, or more for chains whose recursion needs it in a
    // debug build (about 16 KiB of stack per level).
    let stack_size = (64 * 1024 * 1024).max(depth * 32 * 1024);
    on_thread_with_stack("equation-requires-budget", stack_size, move || {
        let definition = equation_requires_budget_definition(size);
        let subject = equation_requires_budget_subject(&definition, depth, tail);
        let before = snapshot();
        let (result, diagnostics) = diagnostic::collect(|| {
            execute(
                &definition,
                subject,
                ExecutionOptions {
                    max_simplification_iterations,
                    ..ExecutionOptions::default()
                },
            )
        });
        EquationRequiresRun {
            result,
            diagnostics,
            counters: snapshot().delta(&before),
        }
    })
}

fn assert_stuck_on_unevaluated_prepare(result: &ExecutionResult) {
    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one execution leaf, found {:?}", result.leaves);
    };
    assert_eq!(leaf.depth, 1);
    assert_eq!(leaf.halt_reason, HaltReason::Stuck);
    assert!(
        matches!(
            leaf.pattern.term.kind(),
            TermKind::Application { symbol, .. } if symbol.name.as_ref() == "prepare"
        ),
        "expected prepare to stay unevaluated, found {:?}",
        leaf.pattern.term
    );
}

/// The diagnostics are exactly one budget exhaustion over `Predicates` for each `prepare`
/// equation, each qualified by the equation it left unapplied; the repeated attempts on the same
/// redex report the same fact once.
fn assert_only_prepare_exhaustions(diagnostics: &[BackendDiagnostic], limit: usize) {
    let exhaustion = BackendDiagnostic::SimplificationBudgetExhausted {
        limit,
        subject: BudgetSubject::Predicates,
    };
    let qualified = |rule_id: &str| {
        [
            exhaustion.clone(),
            BackendDiagnostic::RuleConditionUnsimplified {
                rule_id: rule_id.to_owned(),
                limit,
            },
        ]
    };
    let overflow_first = [qualified("prepare-overflow"), qualified("prepare-ok")].concat();
    let ok_first = [qualified("prepare-ok"), qualified("prepare-overflow")].concat();
    assert!(
        diagnostics == overflow_first.as_slice() || diagnostics == ok_first.as_slice(),
        "diagnostics: {diagnostics:?}"
    );
}

#[test]
fn equation_requires_budget_exhaustion_is_diagnosed_and_keeps_the_halt() {
    let run = run_equation_requires_budget(SizeEquations::Simplification, ChainTail::Nil, 64, 1);

    assert_stuck_on_unevaluated_prepare(&run.result);
    assert_only_prepare_exhaustions(&run.diagnostics, 1);
}

#[test]
fn equation_requires_exhaustion_at_the_default_budget_is_diagnosed() {
    // With `size` as simplification rules, a 1,024-element chain needs more than the default
    // lineage budget to evaluate `size`, so neither `requires` is decided and `prepare` stays
    // unevaluated; the diagnostic is the only observable difference from a genuinely open
    // condition.
    let run = run_equation_requires_budget(
        SizeEquations::Simplification,
        ChainTail::Nil,
        1_024,
        DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
    );

    assert_stuck_on_unevaluated_prepare(&run.result);
    assert_only_prepare_exhaustions(&run.diagnostics, DEFAULT_MAX_SIMPLIFICATION_ITERATIONS);
}

#[test]
fn equation_requires_within_budget_emits_no_exhaustion() {
    let run = run_equation_requires_budget(
        SizeEquations::Simplification,
        ChainTail::Nil,
        64,
        DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
    );

    assert_prepare_evaluates_to(&run.result, "ok");
    assert_eq!(run.diagnostics, []);
}

fn assert_prepare_evaluates_to(result: &ExecutionResult, expected: &str) {
    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one execution leaf, found {:?}", result.leaves);
    };
    assert_eq!(leaf.depth, 1);
    assert_eq!(leaf.halt_reason, HaltReason::Stuck);
    assert!(
        matches!(leaf.pattern.term.kind(), TermKind::DomainValue { value, .. } if value == expected),
        "expected prepare to evaluate to {expected}, found {:?}",
        leaf.pattern.term
    );
}

/// Ground function evaluation longer than the default budget runs to its value: the `requires`
/// of both `prepare` equations are decided, no budget exhaustion is reported, and the work stays
/// linear in the chain (a generous family bound, not a count).
fn assert_ground_function_requires_run_to_their_value(depth: usize) {
    let run = run_equation_requires_budget(
        SizeEquations::Function,
        ChainTail::Nil,
        depth,
        DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
    );

    assert_prepare_evaluates_to(&run.result, "overflow");
    assert_eq!(run.diagnostics, []);
    let bound = 4 * depth as u64 + 64;
    for counter in [Counter::SimplifyRounds, Counter::SimplifyEquationAttempts] {
        let observed = run.counters.get(counter);
        eprintln!("depth {depth}: {counter:?} = {observed} (bound {bound})");
        assert!(
            observed <= bound,
            "{counter:?} = {observed} exceeds the linear bound {bound} at depth {depth}"
        );
    }
}

#[test]
fn ground_function_requires_longer_than_the_default_budget_are_decided() {
    assert_ground_function_requires_run_to_their_value(1_024);
}

#[test]
fn ground_function_requires_far_longer_than_the_default_budget_are_decided() {
    assert_ground_function_requires_run_to_their_value(8_192);
}

#[test]
fn symbolic_function_recursion_still_stops_at_the_budget() {
    // Over a symbolic tail every `size` redex has a variable, so its unfolding is the
    // simplifier's own strategy and the budget still cuts it, with the diagnostic.
    let run = run_equation_requires_budget(
        SizeEquations::Function,
        ChainTail::Symbolic,
        1_024,
        DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
    );

    assert_stuck_on_unevaluated_prepare(&run.result);
    assert_only_prepare_exhaustions(&run.diagnostics, DEFAULT_MAX_SIMPLIFICATION_ITERATIONS);
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
    assert_eq!(result.leaves[0].effects, result.effects);
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

/// `spin(a) = spin(b)` and `spin(b) = spin(a)` are ground function equations that never reach a
/// value and call no hook, so only the step deadline can end their simplification once the
/// iteration budget does not. `go` exposes `spin(a)` to the simplifier after one rewrite step.
fn tail_equation_loop_definition() -> BackendDefinition {
    definition(
        r#"
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            sort SortT{} []
            symbol a{}() : SortT{} [constructor{}(), total{}()]
            symbol b{}() : SortT{} [constructor{}(), total{}()]
            symbol spin{}(SortT{}) : SortInt{} [function{}()]
            symbol start{}(SortT{}) : SortS{} [function{}(), total{}(), injective{}(), no-evaluators{}()]
            symbol kbox{}(SortInt{}) : SortS{} [function{}(), total{}(), injective{}(), no-evaluators{}()]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortT{}, R}(X0:SortT{}, a{}()), \top{R}())),
                \equals{SortInt{}, R}(spin{}(X0:SortT{}), \and{SortInt{}}(spin{}(b{}()), \top{SortInt{}}()))
            ) [label{}("spin-a")]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortT{}, R}(X0:SortT{}, b{}()), \top{R}())),
                \equals{SortInt{}, R}(spin{}(X0:SortT{}), \and{SortInt{}}(spin{}(a{}()), \top{SortInt{}}()))
            ) [label{}("spin-b")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(start{}(T:SortT{}), \top{SortS{}}()),
                kbox{}(spin{}(T:SortT{}))
            ) [label{}("go")]
            "#,
    )
}

/// Execute the tail-loop fixture with the given iteration budget and a short step deadline.
/// The run happens on a worker thread so that a regression, an unbounded loop, fails the test
/// after a generous watchdog instead of hanging the suite.
fn execute_tail_equation_loop(
    max_simplification_iterations: usize,
    step_timeout: Duration,
    terminal_rules: BTreeSet<String>,
) -> ExecutionResult {
    let (sender, receiver) = std::sync::mpsc::channel();
    std::thread::Builder::new()
        .name("tail-equation-loop".into())
        .spawn(move || {
            let definition = tail_equation_loop_definition();
            let a = Term::application(definition.symbols["a"].clone(), Vec::new(), Vec::new());
            let initial = Pattern {
                term: Term::application(definition.symbols["start"].clone(), Vec::new(), vec![a]),
                constraints: Vec::new(),
            };
            let result = execute(
                &definition,
                initial,
                ExecutionOptions {
                    max_simplification_iterations,
                    step_timeout: Some(step_timeout),
                    terminal_rules,
                    ..ExecutionOptions::default()
                },
            );
            let _ = sender.send(result);
        })
        .expect("execution thread should start");
    receiver
        .recv_timeout(Duration::from_secs(120))
        .expect("the step deadline should end the equation loop")
}

#[test]
fn step_deadline_interrupts_an_equation_loop_inside_a_step() {
    // The rewrite step `go` simplifies its successor `kbox(spin(a))`, which never reaches a
    // value. The deadline interrupts that simplification and the step reports its timeout on
    // the state it started from, as it does for a deadline observed between phases.
    let step_timeout = Duration::from_millis(50);

    let result = execute_tail_equation_loop(usize::MAX, step_timeout, BTreeSet::new());

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one execution leaf, found {:?}", result.leaves);
    };
    assert_eq!(
        leaf.halt_reason,
        HaltReason::Timeout(StepTimeoutMode::Manual(step_timeout))
    );
    assert_eq!(leaf.depth, 0);
    assert!(
        matches!(
            leaf.pattern.term.kind(),
            TermKind::Application { symbol, .. } if symbol.name.as_ref() == "start"
        ),
        "expected the pre-step state start(a), found {:?}",
        leaf.pattern.term
    );
}

#[test]
fn step_deadline_ends_a_ground_equation_loop_at_the_default_budget() {
    // Each `spin` step is a determined ground function step, which the default budget does not
    // count; the caller's step deadline is what ends the loop.
    let step_timeout = Duration::from_millis(50);

    let result = execute_tail_equation_loop(
        DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
        step_timeout,
        BTreeSet::new(),
    );

    assert!(
        matches!(
            result.leaves.as_slice(),
            [ExecutionLeaf {
                halt_reason: HaltReason::Timeout(StepTimeoutMode::Manual(timeout)),
                ..
            }] if *timeout == step_timeout
        ),
        "leaves: {:?}",
        result.leaves
    );
}

#[test]
fn step_deadline_ends_an_equation_loop_after_a_terminal_rule() {
    // With `go` terminal the step also simplifies the successor; the interruption is still the
    // step's timeout, not a simplification failure.
    let step_timeout = Duration::from_millis(50);

    let result =
        execute_tail_equation_loop(usize::MAX, step_timeout, BTreeSet::from(["go".to_owned()]));

    assert!(
        matches!(
            result.leaves.as_slice(),
            [ExecutionLeaf {
                halt_reason: HaltReason::Timeout(StepTimeoutMode::Manual(timeout)),
                ..
            }] if *timeout == step_timeout
        ),
        "leaves: {:?}",
        result.leaves
    );
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
            effects: Vec::new(),
            io: k_rust_backend::transition::ExecutionIoState::default(),
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
            .all(|leaf| matches!(leaf.halt_reason, HaltReason::Trivial { .. }))
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
fn terminal_result_resimplification_does_not_duplicate_an_effect() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortString{} [hasDomainValues{}()]
                sort SortK{} []
                sort SortState{} []
                symbol initial{}() : SortState{} [constructor{}()]
                symbol done{}(SortK{}) : SortState{} [constructor{}()]
                symbol dotk{}() : SortK{} [constructor{}()]
                hooked-symbol log{}(SortString{}) : SortK{}
                    [function{}(), hook{}("IO.logString")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(initial{}(), \top{SortState{}}()),
                    done{}(log{}(\dv{SortString{}}("once")))
                ) [label{}("stop")]
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
            terminal_rules: BTreeSet::from(["stop".into()]),
            ..ExecutionOptions::default()
        },
        &NoSolver,
        |effect| observed.push(effect.clone()),
    );

    let expected = [BuiltinEffect::UserLog("once".into())];
    assert_eq!(result.leaves.len(), 1);
    assert!(matches!(
        result.leaves[0].halt_reason,
        HaltReason::TerminalRule { .. }
    ));
    assert_eq!(result.leaves[0].effects, expected);
    assert_eq!(result.effects, expected);
    assert_eq!(observed, expected);
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
fn stopped_branch_keeps_candidate_effects_out_of_the_committed_stream() {
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

    let HaltReason::Branch { branches, .. } = &result.leaves[0].halt_reason else {
        panic!("expected a branch point");
    };
    assert_eq!(
        branches
            .iter()
            .map(|branch| branch.effects.as_slice())
            .collect::<Vec<_>>(),
        [
            [BuiltinEffect::UserLog("left".into())].as_slice(),
            [BuiltinEffect::UserLog("right".into())].as_slice(),
        ]
    );
    assert!(result.leaves[0].effects.is_empty());
    assert!(result.effects.is_empty());
    assert!(observed.is_empty());
}

fn effectful_branch_definition() -> (BackendDefinition, Pattern) {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortString{} [hasDomainValues{}()]
                sort SortK{} []
                sort SortState{} []
                symbol initial{}() : SortState{} [constructor{}()]
                symbol left{}(SortK{}) : SortState{} [constructor{}()]
                symbol right{}(SortK{}) : SortState{} [constructor{}()]
                symbol dotk{}() : SortK{} [constructor{}()]
                hooked-symbol log{}(SortString{}) : SortK{}
                    [function{}(), hook{}("IO.logString")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(initial{}(), \top{SortState{}}()),
                    left{}(log{}(\dv{SortString{}}("left")))
                ) [label{}("left")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(initial{}(), \top{SortState{}}()),
                    right{}(log{}(\dv{SortString{}}("right")))
                ) [label{}("right")]
            endmodule []"#,
    )
    .unwrap();
    let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
    let initial = definition
        .internalize_pattern(&parse_pattern("initial{}()").unwrap(), &[])
        .unwrap();
    (definition, initial)
}

#[test]
fn any_execution_commits_only_the_selected_candidate_effects() {
    let (definition, initial) = effectful_branch_definition();
    let mut observed = Vec::new();

    let result = execute_with_solver_and_observer(
        &definition,
        initial,
        ExecutionOptions {
            mode: ExecutionMode::Any,
            ..ExecutionOptions::default()
        },
        &NoSolver,
        |effect| observed.push(effect.clone()),
    );

    let expected = [BuiltinEffect::UserLog("left".into())];
    assert_eq!(result.leaves.len(), 1);
    assert_eq!(result.leaves[0].trace[0].label.as_deref(), Some("left"));
    assert_eq!(result.leaves[0].effects, expected);
    assert_eq!(result.effects, expected);
    assert_eq!(observed, expected);
}

#[test]
fn all_execution_returns_one_effect_transcript_per_leaf() {
    let (definition, initial) = effectful_branch_definition();
    let mut observed = Vec::new();

    let result = execute_with_solver_and_observer(
        &definition,
        initial,
        ExecutionOptions::default(),
        &NoSolver,
        |effect| observed.push(effect.clone()),
    );

    assert_eq!(result.leaves.len(), 2);
    assert_eq!(
        result
            .leaves
            .iter()
            .map(|leaf| (
                leaf.trace[0].label.as_deref().unwrap(),
                leaf.effects.as_slice(),
            ))
            .collect::<Vec<_>>(),
        [
            ("left", [BuiltinEffect::UserLog("left".into())].as_slice(),),
            ("right", [BuiltinEffect::UserLog("right".into())].as_slice(),),
        ]
    );
    assert!(result.effects.is_empty());
    assert!(observed.is_empty());
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
                TermKind::DomainValue { value, .. } => value.as_utf8().unwrap(),
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
fn failed_higher_priority_candidate_effects_are_only_uncommitted_diagnostics() {
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
                    dead{}(log{}(\dv{SortString{}}("failed high")))
                ) [label{}("high"), priority{}("10")]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(initial{}(), \top{SortK{}}()),
                    log{}(\dv{SortString{}}("lower"))
                ) [label{}("low"), priority{}("50")]
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
        ExecutionOptions::default(),
        &ObservationOptions::all(),
    );

    assert_eq!(result.leaves.len(), 1);
    assert!(
        matches!(result.leaves[0].halt_reason, HaltReason::Trivial { .. }),
        "{result:#?}"
    );
    assert!(result.leaves[0].effects.is_empty());
    assert!(result.effects.is_empty());
    let [discarded] = result.discarded.as_slice() else {
        panic!("expected one failed candidate: {:?}", result.discarded);
    };
    assert_eq!(discarded.id.rule, "high");
    assert_eq!(discarded.rule_label.as_deref(), Some("high"));
    assert_eq!(
        discarded.effects,
        [BuiltinEffect::UserLog("failed high".into())]
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
fn ordinary_execution_clones_prebuffered_input_into_each_branch() {
    let definition = unconditional_branch_definition();
    let input = ExecutionIoState::new(Vec::from(&b"prebuffered"[..]));

    let result = execute_with_io_state(
        &definition,
        subject(&definition, "value"),
        ExecutionOptions::default(),
        input.clone(),
    );

    assert_eq!(result.leaves.len(), 2);
    assert!(result.leaves.iter().all(|leaf| leaf.io == input));
    assert!(result.leaves.iter().all(|leaf| leaf.io.cursor() == 0));
}

#[test]
fn console_write_and_putc_preserve_hook_order_and_exact_bytes() {
    let definition = console_io_definition("");
    let initial = console_pattern(
        &definition,
        r#"pair{}(
            write{}(\dv{SortInt{}}("1"), \dv{SortString{}}("hé")),
            putc{}(\dv{SortInt{}}("2"), \dv{SortInt{}}("255"))
        )"#,
    );

    let result = execute_with_io_state(
        &definition,
        initial,
        ExecutionOptions::default(),
        ExecutionIoState::default(),
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one console leaf: {result:#?}");
    };
    assert_eq!(leaf.io.transcript().len(), 2);
    assert_eq!(leaf.io.transcript()[0].hook, "IO.write");
    assert_eq!(leaf.io.transcript()[0].descriptor, 1);
    assert_eq!(leaf.io.transcript()[0].bytes.as_ref(), "hé".as_bytes());
    assert_eq!(leaf.io.transcript()[1].hook, "IO.putc");
    assert_eq!(leaf.io.transcript()[1].descriptor, 2);
    assert_eq!(leaf.io.transcript()[1].bytes.as_ref(), [255]);
}

#[test]
fn console_getc_reads_unsigned_bytes_and_returns_eof() {
    let definition = console_io_definition("");
    let first = execute_with_io_state(
        &definition,
        console_pattern(&definition, r#"getc{}(\dv{SortInt{}}("0"))"#),
        ExecutionOptions::default(),
        ExecutionIoState::new(Vec::from(&b"\xff"[..])),
    );
    let TermKind::Injection { term, .. } = first.leaves[0].pattern.term.kind() else {
        panic!("getc result was not injected: {first:#?}");
    };
    assert!(matches!(term.kind(), TermKind::DomainValue { value, .. } if value == "255"));
    assert_eq!(first.leaves[0].io.cursor(), 1);

    let eof = execute_with_io_state(
        &definition,
        console_pattern(&definition, r#"getc{}(\dv{SortInt{}}("0"))"#),
        ExecutionOptions::default(),
        ExecutionIoState::default(),
    );
    let TermKind::Injection { term, .. } = eof.leaves[0].pattern.term.kind() else {
        panic!("EOF result was not injected: {eof:#?}");
    };
    assert!(
        matches!(term.kind(), TermKind::Application { symbol, .. } if symbol.name.as_ref() == "Lbl'Hash'EOF")
    );
    assert_eq!(eof.leaves[0].io.cursor(), 0);
}

#[test]
fn console_getc_consumes_sequential_reads_in_term_order() {
    let definition = console_io_definition("");
    let result = execute_with_io_state(
        &definition,
        console_pattern(
            &definition,
            r#"intPair{}(
                getc{}(\dv{SortInt{}}("0")),
                getc{}(\dv{SortInt{}}("0"))
            )"#,
        ),
        ExecutionOptions::default(),
        ExecutionIoState::new(Vec::from(&b"AB"[..])),
    );

    let TermKind::Application { arguments, .. } = result.leaves[0].pattern.term.kind() else {
        panic!("expected pair result: {result:#?}");
    };
    let values = arguments
        .iter()
        .map(|argument| match argument.kind() {
            TermKind::Injection { term, .. } => match term.kind() {
                TermKind::DomainValue { value, .. } => value.as_utf8().unwrap(),
                other => panic!("expected integer: {other:?}"),
            },
            other => panic!("expected injection: {other:?}"),
        })
        .collect::<Vec<_>>();
    assert_eq!(values, ["65", "66"]);
    assert_eq!(result.leaves[0].io.cursor(), 2);
}

#[test]
fn console_read_preserves_arbitrary_short_reads_and_utf8_boundaries() {
    let definition = console_io_definition("");
    let short = execute_with_io_state(
        &definition,
        console_pattern(
            &definition,
            r#"read{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("20"))"#,
        ),
        ExecutionOptions::default(),
        ExecutionIoState::new(vec![0xff, 0x80, 0x00, b'A']),
    );
    let TermKind::Injection { term, .. } = short.leaves[0].pattern.term.kind() else {
        panic!("read result was not injected: {short:#?}");
    };
    assert!(matches!(
        term.kind(),
        TermKind::DomainValue { value, .. }
            if value.as_bytes() == [0xff, 0x80, 0x00, b'A']
    ));
    assert_eq!(short.leaves[0].io.cursor(), 4);

    let eof = execute_with_io_state(
        &definition,
        console_pattern(
            &definition,
            r#"read{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("4"))"#,
        ),
        ExecutionOptions::default(),
        ExecutionIoState::default(),
    );
    let TermKind::Injection { term, .. } = eof.leaves[0].pattern.term.kind() else {
        panic!("read EOF result was not injected: {eof:#?}");
    };
    assert!(matches!(term.kind(), TermKind::DomainValue { value, .. } if value.is_empty()));
    assert_eq!(eof.leaves[0].io.cursor(), 0);

    let first = execute_with_io_state(
        &definition,
        console_pattern(
            &definition,
            r#"read{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("1"))"#,
        ),
        ExecutionOptions::default(),
        ExecutionIoState::new("é".as_bytes().to_vec()),
    );
    let TermKind::Injection { term, .. } = first.leaves[0].pattern.term.kind() else {
        panic!("first split read was not injected: {first:#?}");
    };
    assert!(matches!(
        term.kind(),
        TermKind::DomainValue { value, .. } if value.as_bytes() == [0xc3]
    ));
    assert_eq!(first.leaves[0].io.cursor(), 1);

    let second = execute_with_io_state(
        &definition,
        console_pattern(
            &definition,
            r#"read{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("1"))"#,
        ),
        ExecutionOptions::default(),
        first.leaves[0].io.clone(),
    );
    let TermKind::Injection { term, .. } = second.leaves[0].pattern.term.kind() else {
        panic!("second split read was not injected: {second:#?}");
    };
    assert!(matches!(
        term.kind(),
        TermKind::DomainValue { value, .. } if value.as_bytes() == [0xa9]
    ));
    assert_eq!(second.leaves[0].io.cursor(), 2);
}

#[test]
fn console_write_reproduces_bytes_returned_by_read() {
    let definition = console_io_definition("");
    let read = execute_with_io_state(
        &definition,
        console_pattern(
            &definition,
            r#"read{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("4"))"#,
        ),
        ExecutionOptions::default(),
        ExecutionIoState::new(vec![0xff, 0x80, 0x00, b'A']),
    );
    let TermKind::Injection { term, .. } = read.leaves[0].pattern.term.kind() else {
        panic!("read result was not injected: {read:#?}");
    };
    let TermKind::DomainValue { value, .. } = term.kind() else {
        panic!("read payload was not a domain value: {read:#?}");
    };
    let write = Pattern {
        term: Term::application(
            definition.symbols["write"].clone(),
            Vec::new(),
            vec![
                Term::domain_value(Sort::builtin(BuiltinSort::Int), "1"),
                Term::domain_value(Sort::builtin(BuiltinSort::String), value.clone()),
            ],
        ),
        constraints: Vec::new(),
    };
    let written = execute_with_io_state(
        &definition,
        write,
        ExecutionOptions::default(),
        read.leaves[0].io.clone(),
    );

    assert_eq!(written.leaves[0].io.cursor(), 4);
    assert_eq!(written.leaves[0].io.transcript().len(), 1);
    assert_eq!(
        written.leaves[0].io.transcript()[0].bytes.as_ref(),
        [0xff, 0x80, 0x00, b'A']
    );
}

#[test]
fn console_hooks_reject_wrong_direction_and_symbolic_descriptors_without_mutation() {
    let definition = console_io_definition("");
    for pattern in [
        r#"getc{}(\dv{SortInt{}}("1"))"#,
        r#"read{}(\dv{SortInt{}}("2"), \dv{SortInt{}}("1"))"#,
        r#"putc{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("65"))"#,
        r#"write{}(\dv{SortInt{}}("0"), \dv{SortString{}}("x"))"#,
        r#"getc{}(\dv{SortInt{}}("3"))"#,
        r#"write{}(\dv{SortInt{}}("3"), \dv{SortString{}}("x"))"#,
        r#"putc{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("256"))"#,
        r#"putc{}(\dv{SortInt{}}("2"), \dv{SortInt{}}("-1"))"#,
    ] {
        let result = execute_with_io_state(
            &definition,
            console_pattern(&definition, pattern),
            ExecutionOptions::default(),
            ExecutionIoState::new(Vec::from(&b"input"[..])),
        );
        assert!(matches!(
            result.leaves[0].halt_reason,
            HaltReason::Simplification(SimplificationError::UnsupportedHook { .. })
        ));
        assert_eq!(result.leaves[0].io.cursor(), 0);
        assert!(result.leaves[0].io.transcript().is_empty());
    }

    let symbolic = console_pattern(&definition, "getc{}(D:SortInt{})");
    let result = execute_with_io_state(
        &definition,
        symbolic.clone(),
        ExecutionOptions::default(),
        ExecutionIoState::new(Vec::from(&b"input"[..])),
    );
    assert_eq!(result.leaves[0].pattern, symbolic);
    assert_eq!(result.leaves[0].io.cursor(), 0);
    assert!(result.leaves[0].io.transcript().is_empty());
}

#[test]
fn pure_execution_does_not_enable_console_hooks() {
    let definition = console_io_definition("");
    let initial = console_pattern(
        &definition,
        r#"write{}(\dv{SortInt{}}("1"), \dv{SortString{}}("hidden"))"#,
    );

    let result = execute(&definition, initial, ExecutionOptions::default());

    assert!(matches!(
        result.leaves[0].halt_reason,
        HaltReason::Simplification(SimplificationError::UnsupportedHook { ref hook, .. })
            if hook == "IO.write"
    ));
    assert!(result.leaves[0].io.transcript().is_empty());
}

#[test]
fn search_does_not_enable_console_hooks() {
    let definition = console_io_definition("");
    let result = k_rust_backend::search::search_graph(
        &definition,
        console_pattern(
            &definition,
            r#"write{}(\dv{SortInt{}}("1"), \dv{SortString{}}("hidden"))"#,
        ),
        k_rust_backend::search::SearchOptions::default(),
    );

    assert!(result.states.is_empty());
    assert!(matches!(
        result.incomplete.as_slice(),
        [k_rust_backend::search::IncompleteSearch::Simplification {
            error: SimplificationError::UnsupportedHook { hook, .. },
            ..
        }] if hook == "IO.write"
    ));
}

#[test]
fn execution_disables_console_capability_after_a_symbolic_transition() {
    let definition = console_io_definition(
        r#"
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                pending{}(X:SortK{})
            ) [label{}("make-symbolic")]
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(pending{}(X:SortK{}), \top{SortK{}}()),
                write{}(\dv{SortInt{}}("1"), \dv{SortString{}}("hidden"))
            ) [label{}("write")]
        "#,
    );

    let result = execute_with_io_state(
        &definition,
        console_pattern(&definition, "initial{}()"),
        ExecutionOptions::default(),
        ExecutionIoState::default(),
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one symbolic leaf: {result:#?}");
    };
    assert!(matches!(
        leaf.halt_reason,
        HaltReason::Simplification(SimplificationError::UnsupportedHook { ref hook, .. })
            if hook == "IO.write"
    ));
    assert!(leaf.io.transcript().is_empty());
}

#[test]
fn rejected_console_candidate_does_not_leak_its_transcript() {
    let definition = console_io_definition(
        r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortK{}, R}(
                    dead{}(X:SortK{}),
                    \and{SortK{}}(X:SortK{}, \bottom{SortK{}}())
                )
            ) [label{}("dead"), simplification{}()]
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                dead{}(write{}(\dv{SortInt{}}("1"), \dv{SortString{}}("rolled back")))
            ) [label{}("left")]
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                write{}(\dv{SortInt{}}("2"), \dv{SortString{}}("retained"))
            ) [label{}("right")]
        "#,
    );

    let result = execute_with_io_state(
        &definition,
        console_pattern(&definition, "initial{}()"),
        ExecutionOptions::default(),
        ExecutionIoState::default(),
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one retained branch: {result:#?}");
    };
    assert_eq!(leaf.io.transcript().len(), 1);
    assert_eq!(leaf.io.transcript()[0].descriptor, 2);
    assert_eq!(leaf.io.transcript()[0].bytes.as_ref(), b"retained");
}

#[test]
fn rejected_read_candidate_does_not_advance_the_retained_cursor() {
    let definition = console_io_definition(
        r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortK{}, R}(
                    deadInt{}(X:SortIOInt{}),
                    \and{SortK{}}(dotk{}(), \bottom{SortK{}}())
                )
            ) [label{}("dead-int"), simplification{}()]
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                deadInt{}(getc{}(\dv{SortInt{}}("0")))
            ) [label{}("left")]
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                keepInt{}(getc{}(\dv{SortInt{}}("0")))
            ) [label{}("right")]
        "#,
    );

    let result = execute_with_io_state(
        &definition,
        console_pattern(&definition, "initial{}()"),
        ExecutionOptions::default(),
        ExecutionIoState::new(Vec::from(&b"Z"[..])),
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one retained branch: {result:#?}");
    };
    assert_eq!(leaf.io.cursor(), 1);
    let TermKind::Application { arguments, .. } = leaf.pattern.term.kind() else {
        panic!("expected retained wrapper: {leaf:#?}");
    };
    assert!(matches!(
        arguments[0].kind(),
        TermKind::Injection { term, .. }
            if matches!(term.kind(), TermKind::DomainValue { value, .. } if value == "90")
    ));
}

#[test]
fn console_rewrite_branches_own_independent_transcripts() {
    let definition = console_io_definition(
        r#"
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                write{}(\dv{SortInt{}}("1"), \dv{SortString{}}("left"))
            ) [label{}("left")]
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                write{}(\dv{SortInt{}}("2"), \dv{SortString{}}("right"))
            ) [label{}("right")]
        "#,
    );

    let result = execute_with_io_state(
        &definition,
        console_pattern(&definition, "initial{}()"),
        ExecutionOptions::default(),
        ExecutionIoState::default(),
    );

    assert_eq!(result.leaves.len(), 2);
    assert_eq!(result.leaves[0].io.transcript()[0].bytes.as_ref(), b"left");
    assert_eq!(result.leaves[1].io.transcript()[0].bytes.as_ref(), b"right");
}

#[test]
fn console_rewrite_branches_own_independent_input_cursors() {
    let definition = console_io_definition(
        r#"
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                keepInt{}(getc{}(\dv{SortInt{}}("0")))
            ) [label{}("one")]
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                keepString{}(read{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("2")))
            ) [label{}("two")]
        "#,
    );

    let result = execute_with_io_state(
        &definition,
        console_pattern(&definition, "initial{}()"),
        ExecutionOptions::default(),
        ExecutionIoState::new(Vec::from(&b"abc"[..])),
    );

    assert_eq!(result.leaves.len(), 2);
    assert_eq!(result.leaves[0].io.cursor(), 1);
    assert_eq!(result.leaves[1].io.cursor(), 2);
}

#[test]
fn console_cut_point_keeps_candidate_output_out_of_the_parent_transcript() {
    let definition = console_io_definition(
        r#"
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                write{}(\dv{SortInt{}}("1"), \dv{SortString{}}("candidate"))
            ) [label{}("stop")]
        "#,
    );

    let result = execute_with_io_state(
        &definition,
        console_pattern(&definition, "initial{}()"),
        ExecutionOptions {
            cut_point_rules: BTreeSet::from(["stop".into()]),
            ..ExecutionOptions::default()
        },
        ExecutionIoState::default(),
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one cut-point leaf: {result:#?}");
    };
    assert!(leaf.io.transcript().is_empty());
    let HaltReason::CutPointRule { rule, next_states } = &leaf.halt_reason else {
        panic!("expected a cut-point halt: {leaf:#?}");
    };
    assert_eq!(rule, "stop");
    assert_eq!(next_states.len(), 1);
    assert_eq!(next_states[0].label.as_deref(), Some("stop"));
}

#[test]
fn stopped_console_branch_keeps_candidate_output_out_of_the_parent_transcript() {
    let definition = console_io_definition(
        r#"
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                write{}(\dv{SortInt{}}("1"), \dv{SortString{}}("left"))
            ) [label{}("left")]
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                write{}(\dv{SortInt{}}("2"), \dv{SortString{}}("right"))
            ) [label{}("right")]
        "#,
    );

    let result = execute_with_io_state(
        &definition,
        console_pattern(&definition, "initial{}()"),
        ExecutionOptions {
            branch_mode: ExecutionBranchMode::StopAtBranch,
            ..ExecutionOptions::default()
        },
        ExecutionIoState::default(),
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one stopped branch leaf: {result:#?}");
    };
    assert!(leaf.io.transcript().is_empty());
    let HaltReason::Branch { branches, .. } = &leaf.halt_reason else {
        panic!("expected a branch halt: {leaf:#?}");
    };
    assert_eq!(branches.len(), 2);
}

#[test]
fn console_terminal_rule_commits_the_selected_transition_output() {
    let definition = console_io_definition(
        r#"
            axiom{} \rewrites{SortK{}}(
                \and{SortK{}}(initial{}(), \top{SortK{}}()),
                write{}(\dv{SortInt{}}("2"), \dv{SortString{}}("terminal"))
            ) [label{}("stop")]
        "#,
    );

    let result = execute_with_io_state(
        &definition,
        console_pattern(&definition, "initial{}()"),
        ExecutionOptions {
            terminal_rules: BTreeSet::from(["stop".into()]),
            ..ExecutionOptions::default()
        },
        ExecutionIoState::default(),
    );

    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one terminal leaf: {result:#?}");
    };
    assert_eq!(
        leaf.halt_reason,
        HaltReason::TerminalRule {
            rule: "stop".into()
        }
    );
    assert_eq!(leaf.io.transcript().len(), 1);
    assert_eq!(leaf.io.transcript()[0].hook, "IO.write");
    assert_eq!(leaf.io.transcript()[0].descriptor, 2);
    assert_eq!(leaf.io.transcript()[0].bytes.as_ref(), b"terminal");
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
                TermKind::DomainValue { value, .. } => value.as_utf8().unwrap(),
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
        TermKind::DomainValue { value, .. } if value == "left"
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
                TermKind::DomainValue { value, .. } if value == "first"
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

/// `f(I) => I` over a partial `partial`, so a loop-head state carries the definedness of the
/// operand `f` discarded from under the constructor-like `wrap`.
fn leaf_normal_form_definition(rules: &str) -> BackendDefinition {
    definition(&format!(
        r#"
            symbol partial{{}}(SortS{{}}) : SortS{{}} [function{{}}()]
            symbol f{{}}(SortS{{}}) : SortS{{}} [function{{}}(), total{{}}()]
            axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{SortS{{}}, R}}(
                f{{}}(I:SortS{{}}), \and{{SortS{{}}}}(I:SortS{{}}, \top{{SortS{{}}}}())
            )) [label{{}}("identity"), simplification{{}}()]
            {rules}
            "#
    ))
}

fn simplification_ids(leaf: &ExecutionLeaf) -> Vec<&str> {
    leaf.trace
        .iter()
        .filter(|entry| entry.kind == TraceKind::Simplification)
        .map(|entry| entry.unique_id.as_str())
        .collect()
}

/// The leaf `C[t] /\ \ceil(t)` the loop head builds for `wrap(f(partial("v")))` is externalised
/// as `C[t]`: `wrap` is a total context and application is strict, so the conjunct is entailed.
/// The obligation of an operand that occurs only under a partial symbol is not entailed and
/// stays. The same normal form holds whichever reason halts the state.
fn assert_leaves_in_normal_form(
    definition: &BackendDefinition,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    expected_halt: impl Fn(&HaltReason) -> bool,
) {
    let entailed = execute_with_solver(
        definition,
        Pattern {
            term: internal_term(definition, r#"wrap{}(f{}(partial{}(\dv{SortS{}}("v"))))"#),
            constraints: Vec::new(),
        },
        options.clone(),
        solver,
    );
    let [leaf] = entailed.leaves.as_slice() else {
        panic!("expected one leaf, found {:?}", entailed.leaves);
    };
    assert!(expected_halt(&leaf.halt_reason), "{:?}", leaf.halt_reason);
    assert_eq!(
        leaf.pattern.term,
        internal_term(definition, r#"wrap{}(partial{}(\dv{SortS{}}("v")))"#)
    );
    assert_eq!(leaf.pattern.constraints, Vec::new(), "{leaf:#?}");
    // The loop head applied the equation once; the externalisation applied nothing new.
    assert_eq!(simplification_ids(leaf), ["identity"]);

    let nested = execute_with_solver(
        definition,
        Pattern {
            term: internal_term(
                definition,
                r#"wrap{}(f{}(partial{}(partial{}(\dv{SortS{}}("v")))))"#,
            ),
            constraints: Vec::new(),
        },
        options,
        solver,
    );
    let [leaf] = nested.leaves.as_slice() else {
        panic!("expected one leaf, found {:?}", nested.leaves);
    };
    assert!(expected_halt(&leaf.halt_reason), "{:?}", leaf.halt_reason);
    assert_eq!(
        leaf.pattern.term,
        internal_term(
            definition,
            r#"wrap{}(partial{}(partial{}(\dv{SortS{}}("v"))))"#
        )
    );
    assert_eq!(
        leaf.pattern.constraints,
        vec![Predicate::Ceil(internal_term(
            definition,
            r#"partial{}(\dv{SortS{}}("v"))"#
        ))],
        "{leaf:#?}"
    );
    assert_eq!(simplification_ids(leaf), ["identity"]);
}

#[test]
fn a_stuck_leaf_is_externalised_in_the_simplifier_normal_form() {
    let definition = leaf_normal_form_definition("");

    assert_leaves_in_normal_form(
        &definition,
        ExecutionOptions::default(),
        &NoSolver,
        |halt_reason| matches!(halt_reason, HaltReason::Stuck),
    );
}

#[test]
fn a_depth_bounded_leaf_is_externalised_in_the_simplifier_normal_form() {
    let definition = leaf_normal_form_definition("");

    assert_leaves_in_normal_form(
        &definition,
        ExecutionOptions {
            max_depth: 0,
            ..ExecutionOptions::default()
        },
        &NoSolver,
        |halt_reason| matches!(halt_reason, HaltReason::DepthBound),
    );
}

#[test]
fn an_indeterminate_leaf_is_externalised_in_the_simplifier_normal_form() {
    // The requires `partial(..) = "zero"` is undecidable by equations and the solver answers
    // Unknown, so the state halts as indeterminate; its pattern is still externalised in the
    // normal form and the reason is kept.
    let definition = leaf_normal_form_definition(
        r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \equals{SortS{}, SortS{}}(X:SortS{}, \dv{SortS{}}("zero"))
                ),
                \dv{SortS{}}("conditional")
            ) [label{}("conditional")]
            "#,
    );
    let solver = FixedSolver {
        satisfiability: Ok(Satisfiability::Unknown("fixed".into())),
        validity: Ok(Validity::Indeterminate),
    };

    assert_leaves_in_normal_form(
        &definition,
        ExecutionOptions::default(),
        &solver,
        |halt_reason| matches!(halt_reason, HaltReason::Indeterminate(_)),
    );
}

#[test]
fn a_stuck_leaf_discharges_a_constraint_the_solver_proves_valid() {
    // `partial("w") = "w"` is residual for the equation fixed point; a solver that proves it
    // valid (as a lemma axiom would) makes it redundant in the conjunction, so the leaf drops it.
    let definition = leaf_normal_form_definition("");
    let residual = Predicate::Equals(
        internal_term(&definition, r#"partial{}(\dv{SortS{}}("w"))"#),
        internal_term(&definition, r#"\dv{SortS{}}("w")"#),
    );
    let initial = Pattern {
        term: internal_term(&definition, r#"wrap{}(\dv{SortS{}}("v"))"#),
        constraints: vec![residual.clone()],
    };

    let open = execute_with_solver(
        &definition,
        initial.clone(),
        ExecutionOptions::default(),
        &FixedSolver {
            satisfiability: Ok(Satisfiability::Unknown("fixed".into())),
            validity: Ok(Validity::Indeterminate),
        },
    );
    let [leaf] = open.leaves.as_slice() else {
        panic!("expected one leaf, found {:?}", open.leaves);
    };
    assert!(matches!(leaf.halt_reason, HaltReason::Stuck));
    assert_eq!(leaf.pattern.constraints, vec![residual]);

    let discharged = execute_with_solver(
        &definition,
        initial,
        ExecutionOptions::default(),
        &FixedSolver {
            satisfiability: Ok(Satisfiability::Unknown("fixed".into())),
            validity: Ok(Validity::Valid),
        },
    );
    let [leaf] = discharged.leaves.as_slice() else {
        panic!("expected one leaf, found {:?}", discharged.leaves);
    };
    assert!(matches!(leaf.halt_reason, HaltReason::Stuck));
    assert_eq!(leaf.pattern.constraints, Vec::new(), "{leaf:#?}");
}

/// `top("initial") => pack(partial("v"))` twice, then `pack(X) => top("done")`: the operand
/// `partial("v")` leaves the term at the second step, so its definedness obligation is no
/// longer entailed by the term and every leaf keeps it.
fn branch_then_discard_definition(second_rule: bool) -> BackendDefinition {
    let second = if second_rule {
        r#"
            axiom{} \rewrites{SortC{}}(
                \and{SortC{}}(top{}(\dv{SortS{}}("initial")), \top{SortC{}}()),
                pack{}(partial{}(\dv{SortS{}}("v")))
            ) [label{}("right")]
            "#
    } else {
        ""
    };
    definition(&format!(
        r#"
            sort SortC{{}} []
            symbol top{{}}(SortS{{}}) : SortC{{}} [constructor{{}}()]
            symbol pack{{}}(SortS{{}}) : SortC{{}} [constructor{{}}()]
            symbol partial{{}}(SortS{{}}) : SortS{{}} [function{{}}()]
            axiom{{}} \rewrites{{SortC{{}}}}(
                \and{{SortC{{}}}}(top{{}}(\dv{{SortS{{}}}}("initial")), \top{{SortC{{}}}}()),
                pack{{}}(partial{{}}(\dv{{SortS{{}}}}("v")))
            ) [label{{}}("left")]
            {second}
            axiom{{}} \rewrites{{SortC{{}}}}(
                \and{{SortC{{}}}}(pack{{}}(X:SortS{{}}), \top{{SortC{{}}}}()),
                top{{}}(\dv{{SortS{{}}}}("done"))
            ) [label{{}}("unpack")]
            "#
    ))
}

#[test]
fn a_discarded_operand_keeps_its_definedness_obligation_at_every_leaf() {
    for second_rule in [false, true] {
        let definition = branch_then_discard_definition(second_rule);
        let initial = Pattern {
            term: internal_term(&definition, r#"top{}(\dv{SortS{}}("initial"))"#),
            constraints: Vec::new(),
        };
        let obligation = Predicate::Ceil(internal_term(
            &definition,
            r#"partial{}(\dv{SortS{}}("v"))"#,
        ));

        let explored = execute(&definition, initial.clone(), ExecutionOptions::default());
        assert!(!explored.leaves.is_empty());
        for leaf in &explored.leaves {
            assert!(matches!(leaf.halt_reason, HaltReason::Stuck), "{leaf:#?}");
            assert_eq!(
                leaf.pattern.term,
                internal_term(&definition, r#"top{}(\dv{SortS{}}("done"))"#)
            );
            assert_eq!(
                leaf.pattern.constraints,
                vec![obligation.clone()],
                "{leaf:#?}"
            );
        }

        if !second_rule {
            continue;
        }
        // Stopped at the branch, each payload is `pack(partial("v"))`, whose constructor
        // context entails the obligation: the payload carries no conjunct and loses nothing.
        let stopped = execute(
            &definition,
            initial,
            ExecutionOptions {
                branch_mode: ExecutionBranchMode::StopAtBranch,
                ..ExecutionOptions::default()
            },
        );
        let [leaf] = stopped.leaves.as_slice() else {
            panic!("expected one branch leaf, found {:?}", stopped.leaves);
        };
        let HaltReason::Branch {
            branches,
            remainder,
        } = &leaf.halt_reason
        else {
            panic!("expected a branch leaf, found {:?}", leaf.halt_reason);
        };
        assert!(remainder.is_none());
        assert_eq!(branches.len(), 2, "{branches:#?}");
        for applied in branches {
            assert_eq!(
                applied.pattern.term,
                internal_term(&definition, r#"pack{}(partial{}(\dv{SortS{}}("v")))"#)
            );
            assert_eq!(applied.pattern.constraints, Vec::new(), "{applied:#?}");
        }
    }
}

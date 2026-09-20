//! Differential tests for the stopped-branch priority-group cascade.

use std::{cell::RefCell, collections::VecDeque};

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};
#[cfg(feature = "z3")]
use proptest::{collection::vec, prelude::*};

#[cfg(feature = "z3")]
use super::alpha::assert_step_alpha_equal;
use super::alpha::step_alpha_equal;
use crate::{
    definition::BackendDefinition,
    rewrite::{
        AppliedRule, ExecutionMode, IndeterminateReason, Pattern, RemainderBranch, RewriteResult,
        conjunctively_contains_alpha_equivalent, rewrite_step_all_first_group_for_tests,
        rewrite_step_with_mode,
    },
    rule::Predicate,
    simplify::{DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError, SimplificationOptions},
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    substitution::Substitution,
};

#[cfg(feature = "z3")]
use crate::{smt::Z3Solver, term::Term};

#[derive(Clone, Debug, Eq, PartialEq)]
enum ScriptedQuery {
    IsSat {
        predicates: Vec<Predicate>,
        substitution: Substitution,
    },
    CheckPredicates {
        known: Vec<Predicate>,
        substitution: Substitution,
        checked: Vec<Predicate>,
    },
}

#[derive(Debug)]
struct ScriptedSolver {
    answers: RefCell<VecDeque<Result<Satisfiability, SmtError>>>,
    validity: RefCell<VecDeque<Result<Validity, SmtError>>>,
    transcript: RefCell<Vec<ScriptedQuery>>,
}

impl ScriptedSolver {
    fn new(
        answers: impl IntoIterator<Item = Result<Satisfiability, SmtError>>,
        validity: impl IntoIterator<Item = Result<Validity, SmtError>>,
    ) -> Self {
        Self {
            answers: RefCell::new(answers.into_iter().collect()),
            validity: RefCell::new(validity.into_iter().collect()),
            transcript: RefCell::default(),
        }
    }

    fn record(&self, query: ScriptedQuery) {
        self.transcript.borrow_mut().push(query);
    }
}

impl SmtSolver for ScriptedSolver {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Result<Satisfiability, SmtError> {
        self.record(ScriptedQuery::IsSat {
            predicates: predicates.to_vec(),
            substitution: substitution.clone(),
        });
        self.answers.borrow_mut().pop_front().unwrap_or_else(|| {
            panic!(
                "ScriptedSolver exhausted satisfiability answers after transcript {:#?}",
                self.transcript.borrow()
            )
        })
    }

    fn check_predicates(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Result<Validity, SmtError> {
        self.record(ScriptedQuery::CheckPredicates {
            known: known.to_vec(),
            substitution: substitution.clone(),
            checked: checked.to_vec(),
        });
        self.validity.borrow_mut().pop_front().unwrap_or_else(|| {
            panic!(
                "ScriptedSolver exhausted validity answers after transcript {:#?}",
                self.transcript.borrow()
            )
        })
    }
}

#[cfg(feature = "z3")]
fn definition_source(rules: &str) -> String {
    r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            symbol wrap{}(SortInt{}) : SortInt{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), smt-hook{}("<")]
            symbol le{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), smt-hook{}("<=")]
            $RULES
        endmodule []"#
        .replace("$RULES", rules)
}

#[cfg(feature = "z3")]
fn definition(rules: &str) -> (BackendDefinition, String) {
    let source = definition_source(rules);
    let syntax = parse_definition(&source).expect("generated definition should parse");
    (
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("generated definition should internalize"),
        source,
    )
}

#[cfg(feature = "z3")]
fn internal_term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
        .expect("term should internalize")
}

#[cfg(feature = "z3")]
fn subject(definition: &BackendDefinition, constrained: bool) -> Pattern {
    let constraints = if constrained {
        vec![Predicate::Equals(
            internal_term(definition, r#"le{}(\dv{SortInt{}}("0"), X:SortInt{})"#),
            internal_term(definition, r#"\dv{SortBool{}}("true")"#),
        )]
    } else {
        Vec::new()
    };
    Pattern {
        term: internal_term(definition, "wrap{}(X:SortInt{})"),
        constraints,
    }
}

fn step_parts(result: &RewriteResult) -> (Vec<AppliedRule>, Option<RemainderBranch>) {
    match result {
        RewriteResult::Branch {
            branches,
            remainder,
            ..
        } => (branches.clone(), remainder.clone()),
        RewriteResult::Finished(applied) => (vec![applied.clone()], None),
        _ => (Vec::new(), None),
    }
}

/// The pre-cascade All-mode replay loop deleted in ca120849, copied without control-flow changes.
fn replay_oracle(
    definition: &BackendDefinition,
    branches: &mut Vec<AppliedRule>,
    remainder: &mut Option<RemainderBranch>,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
) -> Result<(), SimplificationError> {
    // Each iteration applies one more rule to the remainder (a strictly smaller applicability
    // space) or ends it as stuck, indeterminate, trivial, or vacuous.
    // Invariant: `remainder` is the part of the parent pattern that `branches` does not yet cover.
    while let Some(current) = remainder.take() {
        match rewrite_step_all_first_group_for_tests(
            definition,
            &current.pattern,
            fresh_counter,
            simplification_options,
            solver,
            assume_initial_defined,
        ) {
            RewriteResult::Finished(applied) => branches.insert(0, applied),
            RewriteResult::Branch {
                branches: mut lower_branches,
                remainder: lower_remainder,
                ..
            } => {
                lower_branches.append(branches);
                *branches = lower_branches;
                *remainder = lower_remainder;
            }
            RewriteResult::Indeterminate {
                reason: IndeterminateReason::Simplification { error, .. },
                ..
            } => return Err(error),
            RewriteResult::Stuck(_) | RewriteResult::Indeterminate { .. } => {
                *remainder = Some(current);
                break;
            }
            RewriteResult::Trivial(_, _) | RewriteResult::Vacuous(_) => break,
        }
    }
    Ok(())
}

fn compare_with_solvers(
    definition: &BackendDefinition,
    initial: &Pattern,
    case: &str,
    exact: bool,
    options: SimplificationOptions,
    cascade_solver: &dyn SmtSolver,
    oracle_solver: &dyn SmtSolver,
) -> Result<(), String> {
    let mut cascade_fresh = 0;
    let mut oracle_fresh = 0;
    let cascade_step = rewrite_step_with_mode(
        definition,
        initial,
        &mut cascade_fresh,
        options,
        cascade_solver,
        ExecutionMode::All,
        false,
    );
    let (cascade_branches, cascade_remainder) = step_parts(&cascade_step);
    let cascade_error = Ok::<(), SimplificationError>(());
    let oracle_step = rewrite_step_all_first_group_for_tests(
        definition,
        initial,
        &mut oracle_fresh,
        options,
        oracle_solver,
        false,
    );
    let (mut oracle_branches, mut oracle_remainder) = step_parts(&oracle_step);
    let oracle_error = replay_oracle(
        definition,
        &mut oracle_branches,
        &mut oracle_remainder,
        &mut oracle_fresh,
        options,
        oracle_solver,
        false,
    );
    let renaming = step_alpha_equal(
        (&cascade_branches, &cascade_remainder, &cascade_error),
        (&oracle_branches, &oracle_remainder, &oracle_error),
    )?;
    if !renaming.is_empty() {
        eprintln!("{case}: accepted non-identity fresh-variable bijection {renaming:?}");
    }
    if exact
        && (cascade_branches != oracle_branches
            || cascade_remainder != oracle_remainder
            || cascade_error != oracle_error)
    {
        return Err("fixture requires exact equality but only alpha equality held".into());
    }
    Ok(())
}

#[cfg(feature = "z3")]
fn compare(
    definition: &BackendDefinition,
    initial: &Pattern,
    case: &str,
    exact: bool,
) -> Result<(), String> {
    let cascade_solver = Z3Solver::new(definition).map_err(|error| format!("{error:?}"))?;
    let oracle_solver = Z3Solver::new(definition).map_err(|error| format!("{error:?}"))?;
    compare_with_solvers(
        definition,
        initial,
        case,
        exact,
        SimplificationOptions::keep_partial(DEFAULT_MAX_SIMPLIFICATION_ITERATIONS),
        &cascade_solver,
        &oracle_solver,
    )
}

#[cfg(feature = "z3")]
fn fixture_rules() -> Vec<(&'static str, String, bool)> {
    let s0 = r#"
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(wrap{}(X:SortInt{}),
                \equals{SortBool{}, SortInt{}}(lt{}(X:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))),
            \dv{SortInt{}}("-1")) [label{}("negative"), priority{}("10")]
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(wrap{}(X:SortInt{}),
                \equals{SortBool{}, SortInt{}}(lt{}(\dv{SortInt{}}("0"), X:SortInt{}), \dv{SortBool{}}("true"))),
            \dv{SortInt{}}("1")) [label{}("positive"), priority{}("10")]
        axiom{} \rewrites{SortInt{}}(\and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
            \dv{SortInt{}}("2")) [label{}("zero-a"), priority{}("50")]
        axiom{} \rewrites{SortInt{}}(\and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
            \dv{SortInt{}}("3")) [label{}("zero-b"), priority{}("50")]
    "#;
    let mut s1 = String::new();
    for index in 0..8 {
        s1.push_str(
            &r#"
                axiom{} \rewrites{SortInt{}}(
                    \and{SortInt{}}(wrap{}(X:SortInt{}),
                        \equals{SortBool{}, SortInt{}}(
                            lt{}(X:SortInt{}, \dv{SortInt{}}("$INDEX")),
                            \dv{SortBool{}}("true"))),
                    \dv{SortInt{}}("$VALUE"))
                    [label{}("be08-symbolic-$INDEX"), priority{}("$PRIORITY")]
            "#
            .replace("$INDEX", &index.to_string())
            .replace("$VALUE", &(100 + index).to_string())
            .replace("$PRIORITY", &(10 + index * 10).to_string()),
        );
    }
    s1.push_str(
        r#"
            axiom{} \rewrites{SortInt{}}(\and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
                \dv{SortInt{}}("200")) [label{}("be08-fallback-a"), priority{}("90")]
            axiom{} \rewrites{SortInt{}}(\and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
                \dv{SortInt{}}("201")) [label{}("be08-fallback-b"), priority{}("90")]
        "#,
    );
    let lower = r#"
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(wrap{}(X:SortInt{}),
                \equals{SortBool{}, SortInt{}}(lt{}(X:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))),
            \dv{SortInt{}}("-1")) [label{}("negative"), priority{}("10")]
        axiom{} \rewrites{SortInt{}}(\and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
            \dv{SortInt{}}("20")) [label{}("fallback"), priority{}("50")]
    "#;
    let complete = r#"
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(wrap{}(X:SortInt{}),
                \equals{SortBool{}, SortInt{}}(lt{}(X:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))),
            \dv{SortInt{}}("-1")) [label{}("negative"), priority{}("10")]
        axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(wrap{}(X:SortInt{}),
                \equals{SortBool{}, SortInt{}}(lt{}(X:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("false"))),
            \dv{SortInt{}}("1")) [label{}("nonnegative"), priority{}("10")]
    "#;
    vec![
        ("S0", s0.into(), true),
        ("S1", s1, true),
        ("symbolic-lower-fallback", lower.into(), false),
        ("complementary-complete", complete.into(), false),
    ]
}

#[cfg(feature = "z3")]
fn t7_different_constructor_fixture() -> (BackendDefinition, Pattern) {
    let source = r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            sort SortCfg{} []
            symbol state{}(SortInt{}) : SortCfg{}
                [constructor{}(), total{}(), injective{}()]
            symbol other{}(SortInt{}) : SortCfg{}
                [constructor{}(), total{}(), injective{}()]
            symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), smt-hook{}("<")]
            axiom{} \rewrites{SortCfg{}}(
                \and{SortCfg{}}(state{}(X:SortInt{}),
                    \equals{SortBool{}, SortCfg{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true"))),
                state{}(\dv{SortInt{}}("-1")))
                [label{}("negative"), priority{}("10")]
            axiom{} \rewrites{SortCfg{}}(
                \and{SortCfg{}}(other{}(X:SortInt{}), \top{SortCfg{}}()),
                other{}(\dv{SortInt{}}("50")))
                [label{}("lower-stuck"), priority{}("50")]
        endmodule []"#;
    let syntax = parse_definition(source).expect("T7 definition should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("T7 definition should internalize");
    let subject = Pattern {
        term: internal_term(&definition, "state{}(X:SortInt{})"),
        constraints: Vec::new(),
    };
    (definition, subject)
}

/// T6: the stopped-branch fixtures agree with the deleted All-mode replay.
#[test]
#[cfg(feature = "z3")]
fn cascade_equals_replay_oracle_on_every_stopped_branch_fixture() {
    for (name, rules, exact) in fixture_rules() {
        let (definition, _) = definition(&rules);
        compare(&definition, &subject(&definition, false), name, exact)
            .unwrap_or_else(|error| panic!("{name}: {error}"));
    }
    let (definition, initial) = t7_different_constructor_fixture();
    compare(
        &definition,
        &initial,
        "T7-different-constructor-lower-group-stuck",
        false,
    )
    .unwrap_or_else(|error| panic!("T7-different-constructor-lower-group-stuck: {error}"));
}

fn portable_definition(rules: &str) -> BackendDefinition {
    let source = r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            sort SortString{} [hasDomainValues{}()]
            sort SortIOInt{} []
            sort SortK{} []
            symbol state{}(SortInt{}) : SortK{} [constructor{}(), total{}(), injective{}()]
            symbol done{}() : SortK{} [constructor{}(), total{}()]
            symbol tag{}(SortInt{}) : SortK{} [constructor{}(), total{}(), injective{}()]
            symbol dead{}(SortK{}) : SortK{} [function{}(), total{}()]
            symbol expand{}(SortK{}) : SortK{} [function{}(), total{}()]
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
    let syntax = parse_definition(&source).expect("portable definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("portable definition should internalize")
}

fn portable_subject(definition: &BackendDefinition) -> Pattern {
    definition
        .internalize_pattern(&parse_pattern("state{}(X:SortInt{})").unwrap(), &[])
        .unwrap()
}

fn scripted_solver(satisfiability_queries: usize, validity_queries: usize) -> ScriptedSolver {
    ScriptedSolver::new(
        (0..satisfiability_queries).map(|_| Ok(Satisfiability::Sat)),
        (0..validity_queries).map(|_| Ok(Validity::Indeterminate)),
    )
}

#[derive(Debug, Default)]
struct D3SearchSolver {
    transcript: RefCell<Vec<ScriptedQuery>>,
}

impl SmtSolver for D3SearchSolver {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Result<Satisfiability, SmtError> {
        self.transcript.borrow_mut().push(ScriptedQuery::IsSat {
            predicates: predicates.to_vec(),
            substitution: substitution.clone(),
        });
        Ok(Satisfiability::Sat)
    }

    fn check_predicates(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Result<Validity, SmtError> {
        self.transcript
            .borrow_mut()
            .push(ScriptedQuery::CheckPredicates {
                known: known.to_vec(),
                substitution: substitution.clone(),
                checked: checked.to_vec(),
            });
        Ok(Validity::Indeterminate)
    }
}

fn conjunction(predicates: &[Predicate]) -> Predicate {
    match predicates {
        [] => Predicate::True,
        [predicate] => predicate.clone(),
        predicates => Predicate::And(predicates.to_vec()),
    }
}

fn reached_instantiate(result: &RewriteResult) -> bool {
    match result {
        RewriteResult::Finished(_) | RewriteResult::Trivial(_, _) => true,
        RewriteResult::Branch {
            branches, trivial, ..
        } => !branches.is_empty() || !trivial.is_empty(),
        RewriteResult::Stuck(_)
        | RewriteResult::Vacuous(_)
        | RewriteResult::Indeterminate { .. } => false,
    }
}

struct D3SearchFixture<'a> {
    name: &'a str,
    condition: &'a str,
    /// Whether simplification should retain `Not(applicability)` alpha equivalently so P12 can
    /// reject the replay generation. `false` cases exercise normalization and must be rejected
    /// earlier by P11 instead.
    p12_guard_retained: bool,
}

/// T11 bounded search: one deleted-replay generation must not instantiate a rule whose
/// generation-zero remainder is already on the path.
///
/// The solver deliberately answers `Sat` to satisfiability and `ImplicationIndeterminate` to
/// validity. A second application therefore means the replay passed P11 and the P12
/// alpha-equivalence guard and reached instantiate, which is the D3 witness. The table includes
/// the three shapes named by the design and adjacent Boolean normalizations. Some negated shapes
/// intentionally do not retain the exact P12 premise: double-negation and De Morgan
/// normalization change `Not(applicability)`, but their normalized path still refutes the
/// original requires at P11.
#[test]
fn d3_bounded_search_finds_no_semantically_empty_reapplication() {
    let fixtures = [
        D3SearchFixture {
            name: "not-equals",
            condition: r#"\equals{SortInt{}, SortK{}}(X:SortInt{}, \dv{SortInt{}}("0"))"#,
            p12_guard_retained: true,
        },
        D3SearchFixture {
            name: "not-hooked-lt-term",
            condition: r#"\equals{SortBool{}, SortK{}}(lt{}(X:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))"#,
            p12_guard_retained: true,
        },
        D3SearchFixture {
            name: "double-negation-from-negated-equals",
            condition: r#"\not{SortK{}}(\equals{SortInt{}, SortK{}}(X:SortInt{}, \dv{SortInt{}}("0")))"#,
            p12_guard_retained: false,
        },
        D3SearchFixture {
            name: "double-negated-requires-normalizes-before-applicability",
            condition: r#"\not{SortK{}}(\not{SortK{}}(\equals{SortInt{}, SortK{}}(X:SortInt{}, \dv{SortInt{}}("0"))))"#,
            p12_guard_retained: true,
        },
        D3SearchFixture {
            name: "hooked-lt-false-double-negation",
            condition: r#"\equals{SortBool{}, SortK{}}(lt{}(X:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("false"))"#,
            p12_guard_retained: false,
        },
        D3SearchFixture {
            name: "de-morgan-over-equalities",
            condition: r#"\or{SortK{}}(\equals{SortInt{}, SortK{}}(X:SortInt{}, \dv{SortInt{}}("0")), \equals{SortInt{}, SortK{}}(X:SortInt{}, \dv{SortInt{}}("1")))"#,
            p12_guard_retained: false,
        },
    ];

    for fixture in fixtures {
        let rules = format!(
            r#"
                axiom{{}} \rewrites{{SortK{{}}}}(
                    \and{{SortK{{}}}}(state{{}}(X:SortInt{{}}), {}),
                    done{{}}()) [label{{}}("d3-search"), priority{{}}("10")]
            "#,
            fixture.condition,
        );
        let definition = portable_definition(&rules);
        let initial = portable_subject(&definition);
        let solver = D3SearchSolver::default();
        let mut fresh_counter = 0;
        let first = rewrite_step_with_mode(
            &definition,
            &initial,
            &mut fresh_counter,
            SimplificationOptions::keep_partial(DEFAULT_MAX_SIMPLIFICATION_ITERATIONS),
            &solver,
            ExecutionMode::All,
            false,
        );
        let (first_branches, remainder) = step_parts(&first);
        let [first_application] = first_branches.as_slice() else {
            panic!(
                "{}: generation zero did not produce exactly one branch: {first:#?}; transcript: {:#?}",
                fixture.name,
                solver.transcript.borrow(),
            );
        };
        let Some(remainder) = remainder else {
            panic!(
                "{}: generation zero did not retain a remainder: {first:#?}; transcript: {:#?}",
                fixture.name,
                solver.transcript.borrow(),
            );
        };
        let applicability = conjunction(&first_application.rule_predicates);
        let negated_applicability = Predicate::Not(Box::new(applicability));
        assert_eq!(
            conjunctively_contains_alpha_equivalent(
                &remainder.pattern.constraints,
                &negated_applicability,
            ),
            fixture.p12_guard_retained,
            "{}: unexpected generation-zero remainder normalization\nremainder: {:#?}\nnegated applicability: {negated_applicability:#?}",
            fixture.name,
            remainder.pattern.constraints,
        );

        let second = rewrite_step_with_mode(
            &definition,
            &remainder.pattern,
            &mut fresh_counter,
            SimplificationOptions::keep_partial(DEFAULT_MAX_SIMPLIFICATION_ITERATIONS),
            &solver,
            ExecutionMode::All,
            false,
        );
        assert!(
            !reached_instantiate(&second),
            "{}: D3 witness: the deleted replay reached instantiate in its first re-attempt\nsecond result: {second:#?}\ntranscript: {:#?}",
            fixture.name,
            solver.transcript.borrow(),
        );
    }
}

fn exact_transcript_projection(
    cascade: &[ScriptedQuery],
    oracle: &[ScriptedQuery],
    oracle_projection: &[usize],
    expected_oracle_queries: usize,
    fixture: &str,
) -> Result<(), String> {
    if oracle.len() != expected_oracle_queries {
        return Err(format!(
            "{fixture}: replay consumed {} queries instead of {expected_oracle_queries}\noracle: {oracle:#?}",
            oracle.len()
        ));
    }
    if oracle_projection.len() != cascade.len() {
        return Err(format!(
            "{fixture}: cascade consumed {} queries instead of the {} queries in the visited-group projection\ncascade: {cascade:#?}",
            cascade.len(),
            oracle_projection.len()
        ));
    }
    if !oracle_projection.windows(2).all(|pair| pair[0] < pair[1])
        || oracle_projection
            .last()
            .is_some_and(|index| *index >= oracle.len())
    {
        return Err(format!(
            "{fixture}: oracle projection indices are not strictly ordered in range: {oracle_projection:?}"
        ));
    }
    let expected = oracle_projection
        .iter()
        .map(|index| oracle[*index].clone())
        .collect::<Vec<_>>();
    if cascade != expected {
        return Err(format!(
            "{fixture}: cascade transcript differs from the exact replay projection for visited groups\nprojection indices: {oracle_projection:?}\nexpected: {expected:#?}\ncascade: {cascade:#?}\noracle: {oracle:#?}"
        ));
    }
    Ok(())
}

#[test]
fn exact_transcript_projection_rejects_missing_or_substituted_queries() {
    let query = |predicate| ScriptedQuery::CheckPredicates {
        known: Vec::new(),
        substitution: Substitution::new(),
        checked: vec![predicate],
    };
    let oracle = vec![query(Predicate::True), query(Predicate::False)];
    assert!(exact_transcript_projection(&oracle[..1], &oracle, &[0, 1], 2, "missing").is_err());
    let substituted = vec![query(Predicate::True), query(Predicate::True)];
    assert!(exact_transcript_projection(&substituted, &oracle, &[0, 1], 2, "substituted").is_err());
}

struct PortableFixture<'a> {
    name: &'a str,
    rules: &'a str,
    max_iterations: usize,
    oracle_projection: &'a [usize],
    expected_oracle_queries: usize,
    cascade_consumption: (usize, usize),
    oracle_consumption: (usize, usize),
}

/// T6 portable fixtures: T8, T12, and T13 use equal scripts and check the cascade transcript as
/// the replay transcript projected onto the queries made by the groups the cascade visits.
#[test]
fn cascade_equals_replay_oracle_on_portable_stopped_branch_fixtures() {
    let fixtures = [
        PortableFixture {
            name: "T8-later-simplification-error",
            rules: r#"
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(state{}(X:SortInt{}),
                        \equals{SortBool{}, SortK{}}(lt{}(X:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))),
                    log{}(\dv{SortString{}}("first"))) [label{}("first"), priority{}("10")]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(state{}(X:SortInt{}),
                        \equals{SortBool{}, SortK{}}(lt{}(X:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))),
                    dead{}(log{}(\dv{SortString{}}("trivial")))) [label{}("trivial"), priority{}("10")]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(state{}(X:SortInt{}),
                        \equals{SortBool{}, SortK{}}(isIOInt{}(getc{}(\dv{SortInt{}}("0"))), \dv{SortBool{}}("true"))),
                    done{}()) [label{}("lower-error"), priority{}("50")]
            "#,
            max_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            oracle_projection: &[0],
            expected_oracle_queries: 1,
            cascade_consumption: (0, 1),
            oracle_consumption: (0, 1),
        },
        PortableFixture {
            name: "T12-lower-budget",
            rules: r#"
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(state{}(X:SortInt{}),
                        \equals{SortBool{}, SortK{}}(lt{}(X:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))),
                    tag{}(\dv{SortInt{}}("10"))) [label{}("first"), priority{}("10")]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(state{}(X:SortInt{}), \top{SortK{}}()),
                    expand{}(tag{}(\dv{SortInt{}}("50")))) [label{}("lower-budget"), priority{}("50")]
            "#,
            max_iterations: 1,
            oracle_projection: &[0, 1],
            expected_oracle_queries: 2,
            cascade_consumption: (1, 1),
            oracle_consumption: (1, 1),
        },
        PortableFixture {
            name: "T13-effects",
            rules: r#"
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(state{}(X:SortInt{}),
                        \equals{SortBool{}, SortK{}}(lt{}(X:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))),
                    log{}(\dv{SortString{}}("first"))) [label{}("first"), priority{}("10")]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(state{}(X:SortInt{}),
                        \equals{SortBool{}, SortK{}}(lt{}(X:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))),
                    dead{}(log{}(\dv{SortString{}}("trivial")))) [label{}("trivial"), priority{}("10")]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(state{}(X:SortInt{}), \top{SortK{}}()),
                    dead{}(log{}(\dv{SortString{}}("lower-dead")))) [label{}("lower-dead"), priority{}("50")]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(state{}(X:SortInt{}), \top{SortK{}}()),
                    log{}(\dv{SortString{}}("lower-live"))) [label{}("lower-live"), priority{}("50")]
            "#,
            max_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            oracle_projection: &[0],
            expected_oracle_queries: 1,
            cascade_consumption: (0, 1),
            oracle_consumption: (0, 1),
        },
    ];

    for fixture in fixtures {
        let definition = portable_definition(fixture.rules);
        let cascade_solver =
            scripted_solver(fixture.cascade_consumption.0, fixture.cascade_consumption.1);
        let oracle_solver =
            scripted_solver(fixture.oracle_consumption.0, fixture.oracle_consumption.1);
        compare_with_solvers(
            &definition,
            &portable_subject(&definition),
            fixture.name,
            false,
            SimplificationOptions::keep_partial(fixture.max_iterations),
            &cascade_solver,
            &oracle_solver,
        )
        .unwrap_or_else(|error| panic!("{}: {error}", fixture.name));
        exact_transcript_projection(
            &cascade_solver.transcript.borrow(),
            &oracle_solver.transcript.borrow(),
            fixture.oracle_projection,
            fixture.expected_oracle_queries,
            fixture.name,
        )
        .unwrap_or_else(|error| panic!("{error}"));
        assert!(
            cascade_solver.answers.borrow().is_empty()
                && cascade_solver.validity.borrow().is_empty(),
            "{}: cascade did not consume its exact answer script",
            fixture.name
        );
        assert!(
            oracle_solver.answers.borrow().is_empty() && oracle_solver.validity.borrow().is_empty(),
            "{}: replay did not consume its exact answer script",
            fixture.name
        );
    }
}

#[cfg(feature = "z3")]
#[derive(Clone, Copy, Debug)]
enum Condition {
    True,
    Less(i8),
    Greater(i8),
    Equal(i8),
}

#[cfg(feature = "z3")]
#[derive(Clone, Debug)]
struct GeneratedRule {
    condition: Condition,
    trivial: bool,
}

#[cfg(feature = "z3")]
#[derive(Clone, Debug)]
struct GeneratedCase {
    groups: Vec<Vec<GeneratedRule>>,
    constrained: bool,
    force_lower_unconditional: bool,
}

#[cfg(feature = "z3")]
fn generated_groups() -> impl Strategy<Value = Vec<Vec<GeneratedRule>>> {
    let condition = prop_oneof![
        Just(Condition::True),
        (-1i8..=1).prop_map(Condition::Less),
        (-1i8..=1).prop_map(Condition::Greater),
        (-1i8..=1).prop_map(Condition::Equal),
    ];
    vec(
        vec(
            (condition, any::<bool>())
                .prop_map(|(condition, trivial)| GeneratedRule { condition, trivial }),
            1..=3,
        ),
        2..=5,
    )
    .prop_map(|mut groups| {
        let mut kept_trivial = false;
        for rule in groups.iter_mut().flatten() {
            if rule.trivial && !kept_trivial {
                kept_trivial = true;
            } else {
                rule.trivial = false;
            }
        }
        groups
    })
}

#[cfg(feature = "z3")]
fn generated_cases() -> impl Strategy<Value = GeneratedCase> {
    (generated_groups(), any::<bool>(), any::<bool>()).prop_map(
        |(groups, constrained, force_lower_unconditional)| GeneratedCase {
            groups,
            constrained,
            force_lower_unconditional,
        },
    )
}

#[cfg(feature = "z3")]
fn condition_source(condition: Condition) -> String {
    match condition {
        Condition::True => r#"\top{SortInt{}}()"#.into(),
        Condition::Less(value) => format!(
            r#"\equals{{SortBool{{}}, SortInt{{}}}}(lt{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("{value}")), \dv{{SortBool{{}}}}("true"))"#
        ),
        Condition::Greater(value) => format!(
            r#"\equals{{SortBool{{}}, SortInt{{}}}}(lt{{}}(\dv{{SortInt{{}}}}("{value}"), X:SortInt{{}}), \dv{{SortBool{{}}}}("true"))"#
        ),
        Condition::Equal(value) => format!(
            r#"\equals{{SortInt{{}}, SortInt{{}}}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("{value}"))"#
        ),
    }
}

#[cfg(feature = "z3")]
fn generated_definition(groups: &[Vec<GeneratedRule>]) -> (BackendDefinition, String) {
    let mut rules = String::new();
    for (group_index, group) in groups.iter().enumerate() {
        for (rule_index, rule) in group.iter().enumerate() {
            let result = 100 + group_index * 10 + rule_index;
            let rhs = if rule.trivial {
                format!(
                    r#"\and{{SortInt{{}}}}(\dv{{SortInt{{}}}}("{result}"), \equals{{SortBool{{}}, SortInt{{}}}}(\dv{{SortBool{{}}}}("true"), \dv{{SortBool{{}}}}("false")))"#
                )
            } else {
                format!(r#"\dv{{SortInt{{}}}}("{result}")"#)
            };
            rules.push_str(
                &r#"
                    axiom{} \rewrites{SortInt{}}(
                        \and{SortInt{}}(wrap{}(X:SortInt{}), $CONDITION),
                        $RESULT)
                        [label{}("generated-$GROUP-$RULE"), priority{}("$PRIORITY")]
                "#
                .replace("$CONDITION", &condition_source(rule.condition))
                .replace("$RESULT", &rhs)
                .replace("$GROUP", &group_index.to_string())
                .replace("$RULE", &rule_index.to_string())
                .replace("$PRIORITY", &(10 + group_index * 10).to_string()),
            );
        }
    }
    definition(&rules)
}

#[cfg(feature = "z3")]
proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// T5: exactly 64 generated priority-group cases compare cascade with replay under Z3.
    #[test]
    fn cascade_equals_replay_oracle_on_generated_priority_groups(
        mut case in generated_cases()
    ) {
        if case.force_lower_unconditional {
            case.groups[1][0].condition = Condition::True;
            case.groups[1][0].trivial = false;
        }
        let (definition, rendered) = generated_definition(&case.groups);
        let initial = subject(&definition, case.constrained);
        let result = compare(&definition, &initial, "generated", false);
        prop_assert!(
            result.is_ok(),
            "cascade/replay mismatch: {result:?}\nconstrained: {}\nforced lower unconditional: {}\ngenerated definition:\n{rendered}",
            case.constrained,
            case.force_lower_unconditional,
        );
    }
}

#[cfg(feature = "z3")]
#[test]
fn replay_oracle_smoke_uses_one_global_alpha_gate() {
    let (definition, _) = definition(&fixture_rules()[0].1);
    let options = SimplificationOptions::keep_partial(DEFAULT_MAX_SIMPLIFICATION_ITERATIONS);
    let cascade_solver = Z3Solver::new(&definition).unwrap();
    let oracle_solver = Z3Solver::new(&definition).unwrap();
    let mut cascade_fresh = 0;
    let mut oracle_fresh = 0;
    let cascade = rewrite_step_with_mode(
        &definition,
        &subject(&definition, false),
        &mut cascade_fresh,
        options,
        &cascade_solver,
        ExecutionMode::All,
        false,
    );
    let (branches, remainder) = step_parts(&cascade);
    let error = Ok::<(), SimplificationError>(());
    let initial = rewrite_step_all_first_group_for_tests(
        &definition,
        &subject(&definition, false),
        &mut oracle_fresh,
        options,
        &oracle_solver,
        false,
    );
    let (mut replayed, mut replay_remainder) = step_parts(&initial);
    let replay_error = replay_oracle(
        &definition,
        &mut replayed,
        &mut replay_remainder,
        &mut oracle_fresh,
        options,
        &oracle_solver,
        false,
    );
    assert_step_alpha_equal(
        (&branches, &remainder, &error),
        (&replayed, &replay_remainder, &replay_error),
        "S0 smoke",
    );
}

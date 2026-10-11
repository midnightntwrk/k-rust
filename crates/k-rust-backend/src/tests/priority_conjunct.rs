//! Priority conjuncts of rewrite left-hand sides are discharged at load (`priority_conjunct`).
//!
//! In `--strategy all`, and for a concrete subject in either strategy, a rule of priority `p` is
//! offered only subjects to which no executable rule of smaller priority applies, so a conjunct
//! `\not(A{}())` whose alias `A` denotes only configurations where such a rule applies holds on
//! every subject the rule is offered: the load replaces it by `\top` and never unfolds `A`.
//! Whether a symbolic `any` step can pass to a lower priority instances that a later application
//! group of a higher rule covers is open and independent of these conjuncts. One it cannot show so refuses the load, as does any other negated
//! configuration in a rewrite left-hand side, which no predicate of a rule expresses.

use indoc::indoc;
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::{
        BackendDefinition, DefinitionError, DisjunctFailure, DisjunctStep, PriorityConjunctFailure,
    },
    rewrite::{ExecutionMode, Pattern, RewriteResult, rewrite_step_with_mode},
    rule::{Predicate, RulePatternError, SentenceKey},
    simplify::SimplificationOptions,
    smt::{NoSolver, SmtSolver},
    term::Name,
};

/// Two levels of priority aliases: `priorityLE35` names `r0` (priority 35, no variables) by a
/// bare application of its left-hand-side alias, `priorityLE40` nests `priorityLE35` and names
/// `r1` and `r2` (priority 40); `r1` and `r2` carry `priorityLE35`, `r3` (priority 50) carries
/// `priorityLE40`.
pub(crate) const FIXTURE: &str = indoc! {r#"
    []
    module PRIO
      sort SortS{} []
      symbol a{}() : SortS{} [constructor{}(), functional{}()]
      symbol b{}() : SortS{} [constructor{}(), functional{}()]
      symbol c{}() : SortS{} [constructor{}(), functional{}()]
      symbol d{}() : SortS{} [constructor{}(), functional{}()]
      symbol e{}() : SortS{} [constructor{}(), functional{}()]
      symbol g{}(SortS{}) : SortS{} [constructor{}(), functional{}()]
      symbol f{}(SortS{}) : SortS{} [constructor{}(), functional{}()]
      alias rule0LHS{}() : SortS{} where rule0LHS{}() := \and{SortS{}}(\top{SortS{}}(), f{}(e{}())) []
      alias rule1LHS{}(SortS{}) : SortS{}
      where rule1LHS{}(VarY:SortS{}) := \and{SortS{}}(\top{SortS{}}(), f{}(g{}(VarY:SortS{}))) []
      alias rule2LHS{}() : SortS{} where rule2LHS{}() := \and{SortS{}}(\top{SortS{}}(), f{}(a{}())) []
      alias rule3LHS{}(SortS{}) : SortS{}
      where rule3LHS{}(VarX:SortS{}) := \and{SortS{}}(\top{SortS{}}(), f{}(VarX:SortS{})) []
      alias priorityLE35{}() : SortS{} where priorityLE35{}() := \or{SortS{}}(rule0LHS{}(), \bottom{SortS{}}()) []
      alias priorityLE40{}() : SortS{}
      where priorityLE40{}() := \or{SortS{}}(priorityLE35{}(), \or{SortS{}}(
        \exists{SortS{}}(VarY:SortS{}, rule1LHS{}(VarY:SortS{})), \or{SortS{}}(rule2LHS{}(), \bottom{SortS{}}()))) []
      axiom{} \rewrites{SortS{}}(rule0LHS{}(), \and{SortS{}}(\top{SortS{}}(), a{}())) [priority{}("35"), label{}("r0")]
      axiom{} \rewrites{SortS{}}(\and{SortS{}}(\not{SortS{}}(priorityLE35{}()), rule1LHS{}(VarY:SortS{})),
        \and{SortS{}}(\top{SortS{}}(), b{}())) [priority{}("40"), label{}("r1")]
      axiom{} \rewrites{SortS{}}(\and{SortS{}}(\not{SortS{}}(priorityLE35{}()), rule2LHS{}()),
        \and{SortS{}}(\top{SortS{}}(), b{}())) [priority{}("40"), label{}("r2")]
      axiom{} \rewrites{SortS{}}(\and{SortS{}}(\not{SortS{}}(priorityLE40{}()), rule3LHS{}(VarX:SortS{})),
        \and{SortS{}}(\top{SortS{}}(), c{}())) [priority{}("50"), label{}("r3")]
    endmodule []
"#};

/// The left-hand sides of `r1`, `r2` and `r3` as `FIXTURE` writes them, with their conjuncts.
const R1_LHS: &str = r"\and{SortS{}}(\not{SortS{}}(priorityLE35{}()), rule1LHS{}(VarY:SortS{}))";
const R2_LHS: &str = r"\and{SortS{}}(\not{SortS{}}(priorityLE35{}()), rule2LHS{}())";
const R3_LHS: &str = r"\and{SortS{}}(\not{SortS{}}(priorityLE40{}()), rule3LHS{}(VarX:SortS{}))";

/// The sentence indices of the rules in `FIXTURE`'s module.
const R0: usize = 14;
const R1: usize = 15;
const R3: usize = 17;

/// `text` with each `(from, to)` replacement applied once.
fn replaced(text: &str, replacements: &[(&str, &str)]) -> String {
    replacements
        .iter()
        .fold(text.to_owned(), |text, (from, to)| {
            assert!(text.contains(from), "the definition contains {from}");
            text.replacen(from, to, 1)
        })
}

/// `FIXTURE` with each `(from, to)` replacement applied once.
fn variant(replacements: &[(&str, &str)]) -> String {
    replaced(FIXTURE, replacements)
}

/// `FIXTURE` with every priority conjunct removed, the aliases kept.
fn without_conjuncts() -> String {
    variant(&[
        (R1_LHS, r"rule1LHS{}(VarY:SortS{})"),
        (R2_LHS, r"rule2LHS{}()"),
        (R3_LHS, r"rule3LHS{}(VarX:SortS{})"),
    ])
}

fn load(text: &str) -> Result<BackendDefinition, DefinitionError> {
    BackendDefinition::internalize(
        &parse_definition(text).expect("the definition parses"),
        "PRIO",
    )
}

fn loaded(text: &str) -> BackendDefinition {
    load(text).expect("the definition loads")
}

fn sentence(index: usize) -> Box<SentenceKey> {
    Box::new((Name::from("PRIO"), index))
}

fn path(steps: &[(&str, usize)]) -> Vec<DisjunctStep> {
    steps
        .iter()
        .map(|&(alias, index)| (alias.to_owned(), index))
        .collect()
}

/// The results of one step of `start` in `--strategy all` with `solver`, each rendered as a
/// constrained pattern, in the order the step gives them; refused when a configuration is left
/// over.
fn one_step(definition: &BackendDefinition, start: &str, solver: &dyn SmtSolver) -> Vec<String> {
    let term = definition
        .internalize_term(&parse_pattern(start).expect("the start parses"), &[])
        .expect("the start internalizes");
    let subject = Pattern {
        term,
        constraints: Vec::new(),
    };
    let result = rewrite_step_with_mode(
        definition,
        &subject,
        &mut crate::fresh::FreshCounter::default(),
        SimplificationOptions::default(),
        solver,
        ExecutionMode::All,
        false,
    )
    .expect("no stop is armed");
    let applied = match result {
        RewriteResult::Finished(applied) => vec![applied],
        RewriteResult::Branch {
            branches,
            remainder: None,
            trivial,
            ..
        } if trivial.is_empty() => branches,
        result => panic!("{start} does not take exactly its expected rules: {result:?}"),
    };
    applied
        .iter()
        .map(|applied| {
            for constraint in &applied.pattern.constraints {
                assert!(
                    !matches!(constraint, Predicate::Term(_)),
                    "{start} is constrained by a configuration read as a predicate: {constraint:?}"
                );
            }
            crate::externalize::constrained_pattern(&applied.pattern).to_string()
        })
        .collect()
}

/// The results of one step of `start`, rendered, in order, none under an ill-sorted condition.
fn one_step_terms(
    definition: &BackendDefinition,
    start: &str,
    solver: &dyn SmtSolver,
) -> Vec<String> {
    one_step(definition, start, solver)
        .into_iter()
        .map(|rendered| {
            assert!(
                !rendered.contains(r#"\dv{SortS{}}"#),
                "{start} gives a result under an ill-sorted condition: {rendered}"
            );
            rendered
        })
        .collect()
}

#[test]
fn a_discharged_conjunct_leaves_the_rule_written_without_it() {
    let with = loaded(FIXTURE);
    let without = loaded(&without_conjuncts());
    assert_eq!(with.rewrite_theory(), without.rewrite_theory());
}

#[test]
fn a_discharged_conjunct_is_top_among_the_stored_axioms() {
    let with = loaded(FIXTURE);
    let top = loaded(&variant(&[
        (
            r"\not{SortS{}}(priorityLE35{}()), rule1LHS",
            r"\top{SortS{}}(), rule1LHS",
        ),
        (
            r"\not{SortS{}}(priorityLE35{}()), rule2LHS",
            r"\top{SortS{}}(), rule2LHS",
        ),
        (
            r"\not{SortS{}}(priorityLE40{}()), rule3LHS",
            r"\top{SortS{}}(), rule3LHS",
        ),
    ]));
    assert_eq!(with.axioms(), top.axioms());
}

/// One step from each start gives the results the priorities give, with and without conjuncts:
/// `r0` on `f(e)`, `r1` on `f(g(_))`, `r2` on `f(a)`, `r3` on the rest of `f(_)`, and no
/// configuration left over.
#[test]
fn one_step_takes_the_rules_the_priorities_select() {
    let with = loaded(FIXTURE);
    let without = loaded(&without_conjuncts());
    for (start, expected) in [
        ("f{}(a{}())", vec!["b{}()"]),
        ("f{}(d{}())", vec!["c{}()"]),
        ("f{}(g{}(d{}()))", vec!["b{}()"]),
        ("f{}(e{}())", vec!["a{}()"]),
    ] {
        let results = one_step_terms(&with, start, &NoSolver);
        assert_eq!(results, expected, "{start}");
        assert_eq!(
            results,
            one_step_terms(&without, start, &NoSolver),
            "{start}"
        );
    }
}

/// From `f(X)`, one result per rule, each under the condition that selects it: `a` with
/// `X = e`, `b` with `X = a`, `b` with `X = g(Y')`, and `c` where none of those holds. Deciding
/// that the remainders are satisfiable takes a solver.
#[cfg(feature = "z3")]
#[test]
fn one_symbolic_step_branches_once_per_rule_under_its_selecting_condition() {
    let with = loaded(FIXTURE);
    let without = loaded(&without_conjuncts());
    let start = "f{}(X:SortS{})";
    let results = one_step_terms(
        &with,
        start,
        &crate::smt::Z3Solver::new(&with).expect("the solver starts"),
    );
    assert_eq!(
        results,
        one_step_terms(
            &without,
            start,
            &crate::smt::Z3Solver::new(&without).expect("the solver starts"),
        )
    );
    let mut results = results;
    results.sort();
    let mut expected = [
        r"\and{SortS{}}(a{}(), \equals{SortS{}, SortS{}}(X:SortS{}, e{}()))",
        concat!(
            r"\and{SortS{}}(b{}(), \and{SortS{}}(",
            r"\not{SortS{}}(\equals{SortS{}, SortS{}}(X:SortS{}, e{}())), ",
            r"\equals{SortS{}, SortS{}}(X:SortS{}, a{}())))"
        ),
        concat!(
            r"\and{SortS{}}(b{}(), \and{SortS{}}(",
            r"\not{SortS{}}(\equals{SortS{}, SortS{}}(X:SortS{}, e{}())), ",
            r"\equals{SortS{}, SortS{}}(X:SortS{}, g{}(Ex-hVarY-b0:SortS{}))))"
        ),
        concat!(
            r"\and{SortS{}}(c{}(), \and{SortS{}}(",
            r"\not{SortS{}}(\equals{SortS{}, SortS{}}(X:SortS{}, e{}())), ",
            r"\not{SortS{}}(\exists{SortS{}}(Ex-hVarY-b0:SortS{}, ",
            r"\equals{SortS{}, SortS{}}(X:SortS{}, g{}(Ex-hVarY-b0:SortS{})))), ",
            r"\not{SortS{}}(\equals{SortS{}, SortS{}}(X:SortS{}, a{}()))))"
        ),
    ];
    expected.sort_unstable();
    assert_eq!(results, expected);
}

#[test]
fn a_disjunct_naming_a_rule_under_a_renaming_of_its_variables_is_accepted() {
    loaded(&variant(&[(
        r"\exists{SortS{}}(VarY:SortS{}, rule1LHS{}(VarY:SortS{}))",
        r"\exists{SortS{}}(VarZ:SortS{}, rule1LHS{}(VarZ:SortS{}))",
    )]));
}

#[test]
fn a_conjunct_naming_a_rule_of_the_carriers_own_priority_is_refused() {
    let refused = load(&variant(&[(
        r#"[priority{}("50"), label{}("r3")]"#,
        r#"[priority{}("40"), label{}("r3")]"#,
    )]));
    assert_eq!(
        refused.err(),
        Some(DefinitionError::PriorityConjunct {
            sentence: sentence(R3),
            alias: "priorityLE40".to_owned(),
            failure: PriorityConjunctFailure::NotStrictlyHigher {
                named: 40,
                own: 40,
                rule: (Name::from("PRIO"), R1),
                path: path(&[("priorityLE40", 1)]),
            },
        })
    );
}

/// The only priority that is too high is reached through `priorityLE35`, nested in the alias the
/// rule carries: the refusal names the path to it.
#[test]
fn a_priority_reached_only_through_nesting_is_refused_with_its_path() {
    let refused = load(&variant(&[
        (
            r#"[priority{}("35"), label{}("r0")]"#,
            r#"[priority{}("60"), label{}("r0")]"#,
        ),
        (R1_LHS, r"rule1LHS{}(VarY:SortS{})"),
        (R2_LHS, r"rule2LHS{}()"),
    ]));
    assert_eq!(
        refused.err(),
        Some(DefinitionError::PriorityConjunct {
            sentence: sentence(R3),
            alias: "priorityLE40".to_owned(),
            failure: PriorityConjunctFailure::NotStrictlyHigher {
                named: 60,
                own: 50,
                rule: (Name::from("PRIO"), R0),
                path: path(&[("priorityLE40", 0), ("priorityLE35", 0)]),
            },
        })
    );
}

#[test]
fn a_disjunct_naming_no_rule_is_refused_at_the_first_carrier() {
    let refused = load(&variant(&[(
        r"\or{SortS{}}(rule0LHS{}(), \bottom{SortS{}}())",
        r"\or{SortS{}}(rule0LHS{}(), \or{SortS{}}(f{}(d{}()), \bottom{SortS{}}()))",
    )]));
    assert_eq!(
        refused.err(),
        Some(DefinitionError::PriorityConjunct {
            sentence: sentence(R1),
            alias: "priorityLE35".to_owned(),
            failure: PriorityConjunctFailure::Disjunct {
                path: path(&[("priorityLE35", 1)]),
                reason: DisjunctFailure::NamesNoRule,
            },
        })
    );
}

#[test]
fn a_disjunct_naming_only_a_non_executable_rule_is_refused() {
    let refused = load(&variant(&[(
        r#"[priority{}("40"), label{}("r1")]"#,
        r#"[priority{}("40"), label{}("r1"), non-executable{}()]"#,
    )]));
    assert_eq!(
        refused.err(),
        Some(DefinitionError::PriorityConjunct {
            sentence: sentence(R3),
            alias: "priorityLE40".to_owned(),
            failure: PriorityConjunctFailure::Disjunct {
                path: path(&[("priorityLE40", 1)]),
                reason: DisjunctFailure::NamedRuleNotExecutable,
            },
        })
    );
}

#[test]
fn a_negated_configuration_in_a_rewrite_left_hand_side_is_refused() {
    for negated in [
        r"\not{SortS{}}(f{}(a{}()))",
        // Under connectives, still in predicate position.
        r"\not{SortS{}}(\exists{SortS{}}(VarZ:SortS{}, \or{SortS{}}(f{}(g{}(VarZ:SortS{})), \bottom{SortS{}}())))",
    ] {
        let refused = load(&variant(&[(
            r"\not{SortS{}}(priorityLE40{}()), rule3LHS",
            &format!("{negated}, rule3LHS"),
        )]));
        assert_eq!(
            refused.err(),
            Some(DefinitionError::RulePattern(
                RulePatternError::NegatedConfiguration {
                    sentence: sentence(R3)
                }
            )),
            "{negated}"
        );
    }
}

/// A negated nullary alias of a predicate is a condition, not a priority conjunct: it is read as
/// the condition its body states, here one that holds, so `r3` takes `f(d)` to `c`.
#[test]
fn a_negated_nullary_alias_of_a_predicate_is_read_as_a_condition() {
    let definition = loaded(&variant(&[
        (
            r"axiom{} \rewrites{SortS{}}(rule0LHS{}()",
            concat!(
                r"alias cond{}() : SortS{} where cond{}() := \equals{SortS{}, SortS{}}(a{}(), b{}()) []",
                "\n",
                r"axiom{} \rewrites{SortS{}}(rule0LHS{}()",
            ),
        ),
        (
            r"\not{SortS{}}(priorityLE40{}()), rule3LHS",
            r"\not{SortS{}}(cond{}()), rule3LHS",
        ),
    ]));
    assert_eq!(
        one_step_terms(&definition, "f{}(d{}())", &NoSolver),
        ["c{}()"]
    );
}

/// A non-executable rule is offered no subject, so its conjunct is not checked, here one naming
/// a rule of its own priority.
#[test]
fn a_conjunct_of_a_non_executable_rule_is_not_checked() {
    loaded(&variant(&[(
        r#"[priority{}("50"), label{}("r3")]"#,
        r#"[priority{}("40"), label{}("r3"), non-executable{}()]"#,
    )]));
}

/// A negated predicate states a condition on the rule's variables, not a set of configurations.
#[test]
fn a_negated_predicate_in_a_rewrite_left_hand_side_is_accepted() {
    loaded(&variant(&[(
        r"\not{SortS{}}(priorityLE40{}()), rule3LHS",
        r"\not{SortS{}}(\equals{SortS{}, SortS{}}(VarX:SortS{}, a{}())), rule3LHS",
    )]));
}

/// The fixture with `rBig`, a priority-40 rule on `f(al0(X))` named by `priorityLE40`, where
/// `al0` applies `al1` twice and so on to `al<length-1>`, and `r4`, a second priority-50 carrier
/// of `priorityLE40`; `conjuncts` keeps the priority conjuncts or removes them all.
fn budget_fixture(length: usize, conjuncts: bool) -> String {
    let mut declarations = String::from(
        "  symbol p{}(SortS{}, SortS{}) : SortS{} [constructor{}(), functional{}()]\n",
    );
    for index in 0..length {
        let body = if index + 1 == length {
            "p{}(X:SortS{}, X:SortS{})".to_owned()
        } else {
            let next = index + 1;
            format!("p{{}}(al{next}{{}}(X:SortS{{}}), al{next}{{}}(X:SortS{{}}))")
        };
        declarations.push_str(&format!(
            "  alias al{index}{{}}(SortS{{}}) : SortS{{}} where al{index}{{}}(X:SortS{{}}) := {body} []\n"
        ));
    }
    declarations.push_str(
        "  alias ruleBigLHS{}(SortS{}) : SortS{}\n  where ruleBigLHS{}(X:SortS{}) := \\and{SortS{}}(\\top{SortS{}}(), f{}(al0{}(X:SortS{}))) []\n",
    );
    let r4_lhs = if conjuncts {
        r"\and{SortS{}}(\not{SortS{}}(priorityLE40{}()), f{}(c{}()))"
    } else {
        r"\and{SortS{}}(\top{SortS{}}(), f{}(c{}()))"
    };
    let rules = format!(
        "  axiom{{}} \\rewrites{{SortS{{}}}}(ruleBigLHS{{}}(X:SortS{{}}), \\and{{SortS{{}}}}(\\top{{SortS{{}}}}(), d{{}}())) [priority{{}}(\"40\"), label{{}}(\"rBig\")]\n  \
         axiom{{}} \\rewrites{{SortS{{}}}}({r4_lhs}, \\and{{SortS{{}}}}(\\top{{SortS{{}}}}(), d{{}}())) [priority{{}}(\"50\"), label{{}}(\"r4\")]\nendmodule []"
    );
    let base = if conjuncts {
        FIXTURE.to_owned()
    } else {
        without_conjuncts()
    };
    replaced(
        &base,
        &[
            (
                "  alias rule0LHS",
                &format!("{declarations}  alias rule0LHS"),
            ),
            (
                r"\or{SortS{}}(rule2LHS{}(), \bottom{SortS{}}())",
                r"\or{SortS{}}(rule2LHS{}(), \or{SortS{}}(\exists{SortS{}}(X:SortS{}, ruleBigLHS{}(X:SortS{})), \bottom{SortS{}}()))",
            ),
            ("endmodule []", &rules),
        ],
    )
}

/// Priority aliases are never unfolded. Without conjuncts, `rBig` applies the chain once; let
/// `length` be the shortest chain whose unfolding the budget refuses, so the chain one shorter
/// loads. With `r3` and `r4` carrying `priorityLE40`, which names `rBig`, unfolding the priority
/// alias would add two more copies of that shorter chain: three copies of a chain cost more than
/// one of a chain one longer, which each level doubles, so that variant loads only when the
/// priority alias is not unfolded.
#[test]
fn priority_aliases_are_never_unfolded() {
    let length = (1..=64)
        .find(|&length| match load(&budget_fixture(length, false)) {
            Ok(_) => false,
            Err(DefinitionError::AliasUnfoldingTooLarge { .. }) => true,
            Err(error) => panic!("the conjunct-free chain of {length} is refused: {error}"),
        })
        .expect("a chain of aliases each applying the next twice exceeds the unfolding budget");
    assert!(length > 1, "the fixture alone exceeds the unfolding budget");
    loaded(&budget_fixture(length - 1, true));
}

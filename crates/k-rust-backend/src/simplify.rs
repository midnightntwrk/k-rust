//! Recursive equation simplification to a bounded fixed point.

use std::{collections::BTreeMap, sync::Arc};

use crate::{
    builtin::{BuiltinError, evaluate as evaluate_builtin},
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms},
    rewrite::{Truth, check_concreteness, predicates_truth, substitute_predicates},
    rule::{Predicate, RewriteRule, RuleRhs, TermIndex, Theory, term_index},
    smt::{NoSolver, SmtError, SmtSolver, Validity},
    substitution::{Substitution, substitute},
    term::{Term, TermKind, Variable},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SimplificationOptions {
    pub max_iterations: usize,
}

impl Default for SimplificationOptions {
    fn default() -> Self {
        Self {
            max_iterations: 100,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Simplification {
    pub term: Term,
    pub constraints: Vec<Predicate>,
    pub applied_rules: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SimplificationError {
    Builtin(BuiltinError),
    IndeterminateMatch {
        rule_id: String,
        substitution: Substitution,
        remainder: Vec<(Term, Term)>,
    },
    IndeterminateRequires {
        rule_id: String,
        predicates: Vec<Predicate>,
    },
    IndeterminateConcreteness {
        rule_id: String,
        variable: Variable,
    },
    ConflictingResults {
        rule_ids: Vec<String>,
    },
    Smt {
        rule_id: String,
        error: SmtError,
    },
    InconsistentGroundTruth {
        rule_id: String,
    },
    IterationLimit {
        limit: usize,
        term: Term,
    },
}

pub fn simplify(
    definition: &BackendDefinition,
    term: &Term,
    options: SimplificationOptions,
) -> Result<Simplification, SimplificationError> {
    simplify_with_solver(definition, term, &[], options, &NoSolver)
}

pub fn simplify_with_solver(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Simplification, SimplificationError> {
    let mut remaining = options.max_iterations;
    simplify_with_budget(
        definition,
        term,
        known_predicates,
        options.max_iterations,
        &mut remaining,
        solver,
    )
}

fn simplify_with_budget(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    limit: usize,
    remaining: &mut usize,
    solver: &dyn SmtSolver,
) -> Result<Simplification, SimplificationError> {
    let children = simplify_children(definition, term, known_predicates, limit, remaining, solver)?;
    let root = simplify_root(definition, &children.term, known_predicates, solver)?;
    let mut constraints = children.constraints;
    constraints.extend(root.constraints);
    let mut applied_rules = children.applied_rules;
    applied_rules.extend(root.applied_rules);
    if root.term == children.term {
        return Ok(Simplification {
            term: root.term,
            constraints,
            applied_rules,
        });
    }
    if *remaining == 0 {
        return Err(SimplificationError::IterationLimit {
            limit,
            term: root.term,
        });
    }
    *remaining -= 1;
    let next = simplify_with_budget(
        definition,
        &root.term,
        known_predicates,
        limit,
        remaining,
        solver,
    )?;
    constraints.extend(next.constraints);
    applied_rules.extend(next.applied_rules);
    Ok(Simplification {
        term: next.term,
        constraints,
        applied_rules,
    })
}

fn simplify_children(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    limit: usize,
    remaining: &mut usize,
    solver: &dyn SmtSolver,
) -> Result<Simplification, SimplificationError> {
    let mut constraints = Vec::new();
    let mut applied_rules = Vec::new();
    let mut child = |term: &Term| {
        let result =
            simplify_with_budget(definition, term, known_predicates, limit, remaining, solver)?;
        constraints.extend(result.constraints);
        applied_rules.extend(result.applied_rules);
        Ok::<_, SimplificationError>(result.term)
    };
    let term = match term.kind() {
        TermKind::And(left, right) => Term::and(child(left)?, child(right)?),
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => Term::application(
            symbol.clone(),
            sort_arguments.clone(),
            arguments
                .iter()
                .map(&mut child)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        TermKind::Injection {
            source,
            target,
            term,
        } => Term::injection(source.clone(), target.clone(), child(term)?),
        TermKind::Map {
            definition,
            entries,
            rest,
        } => Term::map(
            definition.clone(),
            entries
                .iter()
                .map(|(key, value)| Ok((child(key)?, child(value)?)))
                .collect::<Result<Vec<_>, SimplificationError>>()?,
            rest.as_ref().map(&mut child).transpose()?,
        ),
        TermKind::List {
            definition,
            heads,
            rest,
        } => Term::list(
            definition.clone(),
            heads
                .iter()
                .map(&mut child)
                .collect::<Result<Vec<_>, _>>()?,
            rest.as_ref()
                .map(|(middle, tails)| {
                    Ok((
                        child(middle)?,
                        tails
                            .iter()
                            .map(&mut child)
                            .collect::<Result<Vec<_>, SimplificationError>>()?,
                    ))
                })
                .transpose()?,
        ),
        TermKind::Set {
            definition,
            elements,
            rest,
        } => Term::set(
            definition.clone(),
            elements
                .iter()
                .map(&mut child)
                .collect::<Result<Vec<_>, _>>()?,
            rest.as_ref().map(&mut child).transpose()?,
        ),
        TermKind::DomainValue { .. } | TermKind::Variable(_) => term.clone(),
    };
    Ok(Simplification {
        term,
        constraints,
        applied_rules,
    })
}

fn simplify_root(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    solver: &dyn SmtSolver,
) -> Result<Simplification, SimplificationError> {
    if let Some(result) = evaluate_builtin(term).map_err(SimplificationError::Builtin)? {
        let TermKind::Application { symbol, .. } = term.kind() else {
            unreachable!("only applications have builtin hooks")
        };
        return Ok(Simplification {
            term: result,
            constraints: Vec::new(),
            applied_rules: vec![format!(
                "builtin:{}",
                symbol
                    .attributes
                    .hook
                    .as_deref()
                    .expect("evaluated builtin has a hook")
            )],
        });
    }
    if let Some(result) = apply_theory(
        definition,
        &definition.function_theory,
        term,
        known_predicates,
        solver,
    )? {
        return Ok(result);
    }
    if let Some(result) = apply_theory(
        definition,
        &definition.simplification_theory,
        term,
        known_predicates,
        solver,
    )? {
        return Ok(result);
    }
    Ok(Simplification {
        term: term.clone(),
        constraints: Vec::new(),
        applied_rules: Vec::new(),
    })
}

fn apply_theory(
    definition: &BackendDefinition,
    theory: &Theory,
    term: &Term,
    known_predicates: &[Predicate],
    solver: &dyn SmtSolver,
) -> Result<Option<Simplification>, SimplificationError> {
    let groups = applicable_groups(theory, &term_index(term));
    for rules in groups.values() {
        let mut results = Vec::new();
        for rule in rules {
            match apply_equation(definition, rule, term, known_predicates, solver)? {
                EquationAttempt::NotApplicable => {}
                EquationAttempt::Applied(result) => results.push(result),
            }
        }
        match results.len() {
            0 => {}
            1 => return Ok(results.pop()),
            _ => {
                let first = &results[0].term;
                if results.iter().all(|result| &result.term == first) {
                    return Ok(results.into_iter().next());
                }
                return Err(SimplificationError::ConflictingResults {
                    rule_ids: results
                        .into_iter()
                        .flat_map(|result| result.applied_rules)
                        .collect(),
                });
            }
        }
    }
    Ok(None)
}

fn applicable_groups(theory: &Theory, index: &TermIndex) -> BTreeMap<u8, Vec<Arc<RewriteRule>>> {
    let mut result = BTreeMap::new();
    let indexes = if index == &TermIndex::Variable {
        vec![index]
    } else {
        vec![index, &TermIndex::Variable]
    };
    for index in indexes {
        if let Some(groups) = theory.get(index) {
            for (priority, rules) in groups {
                result
                    .entry(*priority)
                    .or_insert_with(Vec::new)
                    .extend(rules.iter().cloned());
            }
        }
    }
    result
}

enum EquationAttempt {
    NotApplicable,
    Applied(Simplification),
}

fn apply_equation(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    term: &Term,
    known_predicates: &[Predicate],
    solver: &dyn SmtSolver,
) -> Result<EquationAttempt, SimplificationError> {
    let substitution =
        match match_terms(MatchMode::Evaluate, &definition.sort_graph, &rule.lhs, term) {
            MatchResult::Failed(_) => return Ok(EquationAttempt::NotApplicable),
            MatchResult::Indeterminate {
                substitution,
                remainder,
            } => {
                return Err(SimplificationError::IndeterminateMatch {
                    rule_id: rule.attributes.unique_id.clone(),
                    substitution,
                    remainder,
                });
            }
            MatchResult::Success(substitution) => substitution,
        };
    if let Some(variable) = check_concreteness(rule, &substitution) {
        return Err(SimplificationError::IndeterminateConcreteness {
            rule_id: rule.attributes.unique_id.clone(),
            variable,
        });
    }
    let requires = substitute_predicates(&rule.requires, &substitution);
    match predicates_truth(&requires) {
        Truth::False => return Ok(EquationAttempt::NotApplicable),
        Truth::Unknown => {
            if !requires
                .iter()
                .all(|predicate| known_predicates.contains(predicate))
            {
                match solver.check_predicates(known_predicates, &Substitution::new(), &requires) {
                    Ok(Validity::Valid) => {}
                    Ok(Validity::Invalid) => return Ok(EquationAttempt::NotApplicable),
                    Ok(Validity::InconsistentGroundTruth) => {
                        return Err(SimplificationError::InconsistentGroundTruth {
                            rule_id: rule.attributes.unique_id.clone(),
                        });
                    }
                    Ok(Validity::Indeterminate) | Err(SmtError::Unavailable) => {
                        return Err(SimplificationError::IndeterminateRequires {
                            rule_id: rule.attributes.unique_id.clone(),
                            predicates: requires,
                        });
                    }
                    Ok(Validity::Unknown(reason)) => {
                        return Err(SimplificationError::Smt {
                            rule_id: rule.attributes.unique_id.clone(),
                            error: SmtError::Unknown(reason),
                        });
                    }
                    Err(error) => {
                        return Err(SimplificationError::Smt {
                            rule_id: rule.attributes.unique_id.clone(),
                            error,
                        });
                    }
                }
            }
        }
        Truth::True => {}
    }
    let RuleRhs::Term(rhs) = &rule.rhs else {
        return Ok(EquationAttempt::NotApplicable);
    };
    let rhs = substitute(rhs, &substitution);
    let ensures = substitute_predicates(&rule.ensures, &substitution);
    match predicates_truth(&ensures) {
        Truth::False => Ok(EquationAttempt::NotApplicable),
        Truth::True => Ok(EquationAttempt::Applied(Simplification {
            term: rhs,
            constraints: Vec::new(),
            applied_rules: vec![rule.attributes.unique_id.clone()],
        })),
        Truth::Unknown => {
            match solver.check_predicates(known_predicates, &Substitution::new(), &ensures) {
                Ok(Validity::Invalid) => {
                    return Ok(EquationAttempt::NotApplicable);
                }
                Ok(
                    Validity::Valid
                    | Validity::Indeterminate
                    | Validity::InconsistentGroundTruth
                    | Validity::Unknown(_),
                )
                | Err(SmtError::Unavailable) => {}
                Err(error) => {
                    return Err(SimplificationError::Smt {
                        rule_id: rule.attributes.unique_id.clone(),
                        error,
                    });
                }
            }
            Ok(EquationAttempt::Applied(Simplification {
                term: rhs,
                constraints: ensures,
                applied_rules: vec![rule.attributes.unique_id.clone()],
            }))
        }
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;

    fn definition(axioms: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} [hasDomainValues{{}}()]
                symbol wrap{{}}(SortS{{}}) : SortS{{}} [constructor{{}}()]
                symbol f{{}}(SortS{{}}) : SortS{{}} [function{{}}()]
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
    fn evaluates_hooked_functions_bottom_up() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hasDomainValues{}()]
                symbol add{}(SortInt{}, SortInt{}) : SortInt{}
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

    #[cfg(feature = "z3")]
    #[test]
    fn z3_disambiguates_symbolic_equation_requires() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
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
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let input = term(&definition, "f{}(Y:SortInt{})");
        let variable = Term::variable(Variable::new("Y", crate::term::Sort::simple("SortInt")));
        let run = |value: &str| {
            simplify_with_solver(
                &definition,
                &input,
                &[Predicate::Equals(
                    variable.clone(),
                    Term::domain_value(crate::term::Sort::simple("SortInt"), value),
                )],
                SimplificationOptions::default(),
                &solver,
            )
            .unwrap()
        };

        assert_eq!(run("5").term, variable);
        assert_eq!(run("15").term, input);
    }

    #[test]
    fn reports_unknown_requires_instead_of_skipping_to_lower_priority() {
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

        assert!(matches!(
            simplify(&definition, &input, SimplificationOptions::default()),
            Err(SimplificationError::IndeterminateRequires { rule_id, .. })
                if rule_id == "conditional"
        ));
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
                SimplificationOptions { max_iterations: 3 },
            ),
            Err(SimplificationError::IterationLimit { limit: 3, .. })
        ));
    }
}

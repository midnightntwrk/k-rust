//! Priority-aware rewrite steps over internalized backend theories.

use std::collections::BTreeSet;

use crate::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms},
    rule::{Concreteness, ConstraintKind, Predicate, RewriteRule, RuleRhs, TermIndex, term_index},
    substitution::{Substitution, substitute},
    term::{Sort, Term, TermKind, Variable},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pattern {
    pub term: Term,
    pub constraints: Vec<Predicate>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AppliedRule {
    pub pattern: Pattern,
    pub label: Option<String>,
    pub unique_id: String,
    pub substitution: Substitution,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RewriteResult {
    Stuck(Pattern),
    Trivial(Pattern),
    Finished(AppliedRule),
    Branch {
        original: Pattern,
        branches: Vec<AppliedRule>,
    },
    Indeterminate {
        pattern: Pattern,
        reason: IndeterminateReason,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IndeterminateReason {
    Match {
        rule_id: String,
        substitution: Substitution,
        remainder: Vec<(Term, Term)>,
    },
    Requires {
        rule_id: String,
        predicates: Vec<Predicate>,
    },
    Concreteness {
        rule_id: String,
        variable: Variable,
    },
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Truth {
    True,
    False,
    #[default]
    Unknown,
}

pub fn rewrite_step(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
) -> RewriteResult {
    let index = term_index(&pattern.term);
    let priority_groups = applicable_groups(definition, &index);
    if priority_groups.is_empty() {
        return RewriteResult::Stuck(pattern.clone());
    }
    let mut saw_trivial = false;
    for rules in priority_groups.values() {
        let mut applied = Vec::new();
        for rule in rules {
            match apply_rule(definition, rule, pattern, fresh_counter) {
                RuleAttempt::NotApplicable => {}
                RuleAttempt::Trivial => saw_trivial = true,
                RuleAttempt::Applied(result) => applied.push(result),
                RuleAttempt::Indeterminate(reason) => {
                    return RewriteResult::Indeterminate {
                        pattern: pattern.clone(),
                        reason,
                    };
                }
            }
        }
        match applied.len() {
            0 => {}
            1 => return RewriteResult::Finished(applied.pop().unwrap()),
            _ => {
                return RewriteResult::Branch {
                    original: pattern.clone(),
                    branches: applied,
                };
            }
        }
    }
    if saw_trivial {
        RewriteResult::Trivial(pattern.clone())
    } else {
        RewriteResult::Stuck(pattern.clone())
    }
}

fn applicable_groups(
    definition: &BackendDefinition,
    index: &TermIndex,
) -> std::collections::BTreeMap<u8, Vec<std::sync::Arc<RewriteRule>>> {
    let mut groups = std::collections::BTreeMap::new();
    let covered = if index == &TermIndex::Variable {
        vec![index]
    } else {
        vec![index, &TermIndex::Variable]
    };
    for covered in covered {
        if let Some(found) = definition.rewrite_theory.get(covered) {
            for (priority, rules) in found {
                groups
                    .entry(*priority)
                    .or_insert_with(Vec::new)
                    .extend(rules.iter().cloned());
            }
        }
    }
    groups
}

enum RuleAttempt {
    NotApplicable,
    Trivial,
    Applied(AppliedRule),
    Indeterminate(IndeterminateReason),
}

fn apply_rule(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    fresh_counter: &mut u64,
) -> RuleAttempt {
    let substitution = match match_terms(
        MatchMode::Rewrite,
        &definition.sort_graph,
        &rule.lhs,
        &pattern.term,
    ) {
        MatchResult::Failed(_) => return RuleAttempt::NotApplicable,
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } => {
            return RuleAttempt::Indeterminate(IndeterminateReason::Match {
                rule_id: rule.attributes.unique_id.clone(),
                substitution,
                remainder,
            });
        }
        MatchResult::Success(substitution) => substitution,
    };

    if let Some(variable) = check_concreteness(rule, &substitution) {
        return RuleAttempt::Indeterminate(IndeterminateReason::Concreteness {
            rule_id: rule.attributes.unique_id.clone(),
            variable,
        });
    }
    let requires = substitute_predicates(&rule.requires, &substitution);
    match predicates_truth(&requires) {
        Truth::False => return RuleAttempt::NotApplicable,
        Truth::Unknown => {
            return RuleAttempt::Indeterminate(IndeterminateReason::Requires {
                rule_id: rule.attributes.unique_id.clone(),
                predicates: requires,
            });
        }
        Truth::True => {}
    }

    let RuleRhs::Term(rhs) = &rule.rhs else {
        return RuleAttempt::NotApplicable;
    };
    let existential_substitution = freshen_existentials(rule, pattern, fresh_counter);
    let rhs = substitute(&substitute(rhs, &substitution), &existential_substitution);
    let ensures = substitute_predicates(
        &substitute_predicates(&rule.ensures, &substitution),
        &existential_substitution,
    );
    if predicates_truth(&ensures) == Truth::False {
        return RuleAttempt::Trivial;
    }
    let mut constraints = pattern.constraints.clone();
    constraints.extend(ensures);
    RuleAttempt::Applied(AppliedRule {
        pattern: Pattern {
            term: rhs,
            constraints,
        },
        label: rule.attributes.label.clone(),
        unique_id: rule.attributes.unique_id.clone(),
        substitution,
    })
}

fn check_concreteness(rule: &RewriteRule, substitution: &Substitution) -> Option<Variable> {
    let constrained = match &rule.attributes.concreteness {
        Concreteness::Unconstrained => return None,
        Concreteness::All(kind) => rule
            .lhs
            .attributes()
            .variables
            .iter()
            .cloned()
            .map(|variable| (variable, *kind))
            .collect::<Vec<_>>(),
        Concreteness::Some(constrained) => constrained
            .iter()
            .filter_map(|((name, sort), kind)| {
                rule.lhs
                    .attributes()
                    .variables
                    .iter()
                    .find(|variable| {
                        variable.name.as_ref().strip_prefix("Rule#") == Some(name.as_ref())
                            && sort_name(&variable.sort) == Some(sort.as_ref())
                    })
                    .cloned()
                    .map(|variable| (variable, *kind))
            })
            .collect(),
    };
    constrained.into_iter().find_map(|(variable, kind)| {
        let Some(term) = substitution.get(&variable) else {
            return Some(variable);
        };
        let concrete = term.attributes().constructor_like;
        let satisfied = match kind {
            ConstraintKind::Concrete => concrete,
            ConstraintKind::Symbolic => !concrete,
        };
        (!satisfied).then_some(variable)
    })
}

fn sort_name(sort: &Sort) -> Option<&str> {
    match sort {
        Sort::Application { name, .. } => Some(name.as_ref()),
        Sort::Variable(_) => None,
    }
}

fn freshen_existentials(
    rule: &RewriteRule,
    pattern: &Pattern,
    fresh_counter: &mut u64,
) -> Substitution {
    let mut names_to_avoid = pattern
        .term
        .attributes()
        .variables
        .iter()
        .map(|variable| variable.name.clone())
        .collect::<BTreeSet<_>>();
    rule.existentials
        .iter()
        .cloned()
        .map(|variable| {
            let name = loop {
                let name = format!("{}!{}", variable.name, *fresh_counter);
                *fresh_counter += 1;
                if names_to_avoid.insert(name.as_str().into()) {
                    break name;
                }
            };
            let term = Term::variable(Variable::new(name, variable.sort.clone()));
            (variable, term)
        })
        .collect()
}

fn substitute_predicates(predicates: &[Predicate], substitution: &Substitution) -> Vec<Predicate> {
    predicates
        .iter()
        .map(|predicate| substitute_predicate(predicate, substitution))
        .collect()
}

fn substitute_predicate(predicate: &Predicate, substitution: &Substitution) -> Predicate {
    match predicate {
        Predicate::True => Predicate::True,
        Predicate::False => Predicate::False,
        Predicate::Term(term) => Predicate::Term(substitute(term, substitution)),
        Predicate::Equals(left, right) => Predicate::Equals(
            substitute(left, substitution),
            substitute(right, substitution),
        ),
        Predicate::Ceil(term) => Predicate::Ceil(substitute(term, substitution)),
        Predicate::Floor(term) => Predicate::Floor(substitute(term, substitution)),
        Predicate::In(left, right) => Predicate::In(
            substitute(left, substitution),
            substitute(right, substitution),
        ),
        Predicate::Not(inner) => {
            Predicate::Not(Box::new(substitute_predicate(inner, substitution)))
        }
        Predicate::And(inner) => Predicate::And(substitute_predicates(inner, substitution)),
        Predicate::Or(inner) => Predicate::Or(substitute_predicates(inner, substitution)),
        Predicate::Implies(left, right) => Predicate::Implies(
            Box::new(substitute_predicate(left, substitution)),
            Box::new(substitute_predicate(right, substitution)),
        ),
        Predicate::Iff(left, right) => Predicate::Iff(
            Box::new(substitute_predicate(left, substitution)),
            Box::new(substitute_predicate(right, substitution)),
        ),
        Predicate::Exists(variable, inner) => Predicate::Exists(
            variable.clone(),
            Box::new(substitute_predicate(
                inner,
                &without_variable(substitution, variable),
            )),
        ),
        Predicate::Forall(variable, inner) => Predicate::Forall(
            variable.clone(),
            Box::new(substitute_predicate(
                inner,
                &without_variable(substitution, variable),
            )),
        ),
    }
}

fn without_variable(substitution: &Substitution, variable: &Variable) -> Substitution {
    let mut substitution = substitution.clone();
    substitution.remove(variable);
    substitution
}

fn predicates_truth(predicates: &[Predicate]) -> Truth {
    predicates.iter().fold(Truth::True, |result, predicate| {
        and_truth(result, predicate_truth(predicate))
    })
}

fn predicate_truth(predicate: &Predicate) -> Truth {
    match predicate {
        Predicate::True => Truth::True,
        Predicate::False => Truth::False,
        Predicate::Term(term) => bool_term_truth(term),
        Predicate::Equals(left, right) if left == right => Truth::True,
        Predicate::Equals(left, right)
            if left.attributes().constructor_like && right.attributes().constructor_like =>
        {
            Truth::False
        }
        Predicate::Not(inner) => match predicate_truth(inner) {
            Truth::True => Truth::False,
            Truth::False => Truth::True,
            Truth::Unknown => Truth::Unknown,
        },
        Predicate::And(inner) => predicates_truth(inner),
        Predicate::Or(inner) => inner.iter().fold(Truth::False, |result, predicate| {
            or_truth(result, predicate_truth(predicate))
        }),
        Predicate::Implies(left, right) => or_truth(
            match predicate_truth(left) {
                Truth::True => Truth::False,
                Truth::False => Truth::True,
                Truth::Unknown => Truth::Unknown,
            },
            predicate_truth(right),
        ),
        Predicate::Iff(left, right) => match (predicate_truth(left), predicate_truth(right)) {
            (Truth::True, Truth::True) | (Truth::False, Truth::False) => Truth::True,
            (Truth::True, Truth::False) | (Truth::False, Truth::True) => Truth::False,
            _ => Truth::Unknown,
        },
        Predicate::Ceil(term) if term.attributes().constructor_like => Truth::True,
        Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Exists(..)
        | Predicate::Forall(..) => Truth::Unknown,
    }
}

fn bool_term_truth(term: &Term) -> Truth {
    match term.kind() {
        TermKind::DomainValue { sort, value }
            if sort == &Sort::simple("SortBool") && value.as_ref() == "true" =>
        {
            Truth::True
        }
        TermKind::DomainValue { sort, value }
            if sort == &Sort::simple("SortBool") && value.as_ref() == "false" =>
        {
            Truth::False
        }
        _ => Truth::Unknown,
    }
}

fn and_truth(left: Truth, right: Truth) -> Truth {
    match (left, right) {
        (Truth::False, _) | (_, Truth::False) => Truth::False,
        (Truth::True, Truth::True) => Truth::True,
        _ => Truth::Unknown,
    }
}

fn or_truth(left: Truth, right: Truth) -> Truth {
    match (left, right) {
        (Truth::True, _) | (_, Truth::True) => Truth::True,
        (Truth::False, Truth::False) => Truth::False,
        _ => Truth::Unknown,
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
                {axioms}
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
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
    fn freshens_existential_variables_on_each_application() {
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
        let second = rewrite_step(&definition, &pattern, &mut fresh);
        let names = [first, second].map(|result| {
            let RewriteResult::Finished(applied) = result else {
                panic!("rule should apply");
            };
            applied
                .pattern
                .term
                .attributes()
                .variables
                .iter()
                .next()
                .unwrap()
                .name
                .clone()
        });
        assert_ne!(names[0], names[1]);
    }
}

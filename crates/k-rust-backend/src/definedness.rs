//! Definedness analysis for rewrite rules and partial-function applications.

use std::sync::Arc;

use crate::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rewrite::substitute_predicates,
    rule::{Predicate, RewriteRule, RuleRhs, TermIndex, term_index},
    simplify::{SimplificationOptions, simplify_predicates_with_solver},
    smt::NoSolver,
    term::{FunctionType, SymbolType, Term, TermKind},
};

pub(crate) fn discharge_rewrite_definedness(definition: &mut BackendDefinition) {
    let mut discharged = Vec::new();
    {
        let definition: &BackendDefinition = definition;
        for (index, groups) in &definition.rewrite_theory {
            for (priority, rules) in groups {
                for (position, rule) in rules.iter().enumerate() {
                    discharged.push((
                        index.clone(),
                        *priority,
                        position,
                        rule_is_defined(definition, rule),
                    ));
                }
            }
        }
    }

    for (index, priority, position, is_defined) in discharged {
        if !is_defined {
            continue;
        }
        let rule = Arc::make_mut(
            &mut definition
                .rewrite_theory
                .get_mut(&index)
                .expect("indexed rewrite group should remain present")
                .get_mut(&priority)
                .expect("indexed rewrite priority should remain present")[position],
        );
        rule.attributes.preserves_definedness = true;
        rule.computed_attributes.undefined_symbols.clear();
    }
}

fn rule_is_defined(definition: &BackendDefinition, rule: &RewriteRule) -> bool {
    if rule.computed_attributes.undefined_symbols.is_empty() {
        return true;
    }
    let RuleRhs::Term(rhs) = &rule.rhs else {
        return false;
    };
    let lhs = ceil_term(definition, &rule.lhs);
    let requires = rule
        .requires
        .iter()
        .flat_map(|predicate| ceil_predicate(definition, predicate))
        .collect::<Vec<_>>();
    let mut rhs = ceil_term(definition, rhs);
    rhs.retain(|predicate| !lhs.contains(predicate) && !requires.contains(predicate));
    requires.is_empty() && rhs.is_empty()
}

pub fn ceil_term(definition: &BackendDefinition, term: &Term) -> Vec<Predicate> {
    let mut predicates = match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial) => {
            if let Some(mut predicates) = apply_ceil_equation(definition, term) {
                for argument in arguments {
                    predicates.extend(ceil_term(definition, argument));
                }
                predicates
            } else {
                vec![Predicate::Ceil(term.clone())]
            }
        }
        TermKind::Application { arguments, .. } => arguments
            .iter()
            .flat_map(|argument| ceil_term(definition, argument))
            .collect(),
        TermKind::And(left, right) => {
            let mut predicates = ceil_term(definition, left);
            predicates.extend(ceil_term(definition, right));
            predicates
        }
        TermKind::Injection { term, .. } => ceil_term(definition, term),
        TermKind::Map { entries, rest, .. } => {
            let mut predicates = entries
                .iter()
                .flat_map(|(key, value)| {
                    ceil_term(definition, key)
                        .into_iter()
                        .chain(ceil_term(definition, value))
                })
                .collect::<Vec<_>>();
            if let Some(rest) = rest {
                predicates.extend(ceil_term(definition, rest));
            }
            for (position, (left, _)) in entries.iter().enumerate() {
                for (right, _) in &entries[position + 1..] {
                    predicates.push(Predicate::Not(Box::new(Predicate::Equals(
                        left.clone(),
                        right.clone(),
                    ))));
                }
                if let Some(rest) = rest {
                    predicates.push(not_in_collection(definition, "MAP.in_keys", left, rest));
                }
            }
            predicates
        }
        TermKind::List { heads, rest, .. } => heads
            .iter()
            .chain(
                rest.iter()
                    .flat_map(|(middle, tails)| std::iter::once(middle).chain(tails)),
            )
            .flat_map(|term| ceil_term(definition, term))
            .collect(),
        TermKind::Set { elements, rest, .. } => {
            let mut predicates = elements
                .iter()
                .flat_map(|element| ceil_term(definition, element))
                .collect::<Vec<_>>();
            if let Some(rest) = rest {
                predicates.extend(ceil_term(definition, rest));
            }
            for (position, left) in elements.iter().enumerate() {
                for right in &elements[position + 1..] {
                    predicates.push(Predicate::Not(Box::new(Predicate::Equals(
                        left.clone(),
                        right.clone(),
                    ))));
                }
                if let Some(rest) = rest {
                    predicates.push(not_in_collection(definition, "SET.in", left, rest));
                }
            }
            predicates
        }
        TermKind::DomainValue { .. } => Vec::new(),
        TermKind::Variable(variable) if variable.name.starts_with("Ex#") => Vec::new(),
        TermKind::Variable(_) => vec![Predicate::Ceil(term.clone())],
    };
    deduplicate(&mut predicates);
    predicates
}

fn apply_ceil_equation(definition: &BackendDefinition, term: &Term) -> Option<Vec<Predicate>> {
    let indexes = [term_index(term), TermIndex::Variable];
    for index in indexes {
        let Some(groups) = definition.ceil_theory.get(&index) else {
            continue;
        };
        for rules in groups.values() {
            for rule in rules {
                // This analysis has no path condition with which to discharge a conditional
                // ceil equation. Applying it here would incorrectly treat the equation as
                // unconditional; runtime predicate simplification handles conditional rules.
                if !rule.requires.is_empty() {
                    continue;
                }
                let MatchResult::Success(substitution) =
                    match_terms_in_definition(MatchMode::Evaluate, definition, &rule.lhs, term)
                else {
                    continue;
                };
                let RuleRhs::Predicates(predicates) = &rule.rhs else {
                    continue;
                };
                let predicates = substitute_predicates(predicates, &substitution);
                return Some(
                    simplify_predicates_with_solver(
                        definition,
                        &predicates,
                        &[],
                        SimplificationOptions::default(),
                        &NoSolver,
                    )
                    .unwrap_or(predicates)
                    .into_iter()
                    .filter(|predicate| predicate != &Predicate::True)
                    .collect(),
                );
            }
        }
    }
    None
}

fn ceil_predicate(definition: &BackendDefinition, predicate: &Predicate) -> Vec<Predicate> {
    match predicate {
        Predicate::True | Predicate::False => Vec::new(),
        Predicate::Term(term) | Predicate::Ceil(term) | Predicate::Floor(term) => {
            ceil_term(definition, term)
        }
        Predicate::Equals(left, right) | Predicate::In(left, right) => ceil_term(definition, left)
            .into_iter()
            .chain(ceil_term(definition, right))
            .collect(),
        Predicate::Not(inner) | Predicate::Exists(_, inner) | Predicate::Forall(_, inner) => {
            ceil_predicate(definition, inner)
        }
        Predicate::And(inner) | Predicate::Or(inner) => inner
            .iter()
            .flat_map(|predicate| ceil_predicate(definition, predicate))
            .collect(),
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            ceil_predicate(definition, left)
                .into_iter()
                .chain(ceil_predicate(definition, right))
                .collect()
        }
    }
}

fn not_in_collection(
    definition: &BackendDefinition,
    hook: &str,
    element: &Term,
    collection: &Term,
) -> Predicate {
    let application = definition.symbols.values().find_map(|symbol| {
        (symbol.attributes.hook.as_deref() == Some(hook)
            && symbol.argument_sorts.as_slice() == [element.sort(), collection.sort()])
        .then(|| {
            Term::application(
                symbol.clone(),
                Vec::new(),
                vec![element.clone(), collection.clone()],
            )
        })
    });
    application.map_or_else(
        || Predicate::Not(Box::new(Predicate::In(element.clone(), collection.clone()))),
        |application| Predicate::Not(Box::new(Predicate::Term(application))),
    )
}

fn deduplicate(predicates: &mut Vec<Predicate>) {
    let mut unique = Vec::with_capacity(predicates.len());
    for predicate in predicates.drain(..) {
        if !unique.contains(&predicate) {
            unique.push(predicate);
        }
    }
    *predicates = unique;
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::rewrite::{Pattern, RewriteResult, rewrite_step};
    use crate::term::Sort;

    fn definition(extra_axioms: &str) -> BackendDefinition {
        let source = r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
                symbol partial{}(SortS{}) : SortS{} [function{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                    partial{}(X:SortS{})
                ) [label{}("uses-partial")]
                $EXTRA
            endmodule []"#
            .replace("$EXTRA", extra_axioms);
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn rewrite_rule(definition: &BackendDefinition) -> &Arc<RewriteRule> {
        definition
            .rewrite_theory
            .values()
            .flat_map(|groups| groups.values())
            .flatten()
            .next()
            .expect("rewrite rule should be indexed")
    }

    #[test]
    fn ceil_equations_discharge_partial_rhs_obligations() {
        let definition = definition(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{R, R}(
                    \ceil{SortS{}, R}(partial{}(X:SortS{})),
                    \top{R}()
                )
            ) [label{}("partial-defined")]
            "#,
        );
        let rule = rewrite_rule(&definition);

        assert!(rule.attributes.preserves_definedness);
        assert!(rule.computed_attributes.undefined_symbols.is_empty());
    }

    #[test]
    fn unresolved_partial_rhs_becomes_a_definedness_constraint() {
        let definition = definition("");
        let subject = definition
            .internalize_term(
                &parse_pattern(r#"wrap{}(\dv{SortS{}}("value"))"#).unwrap(),
                &[],
            )
            .unwrap();
        let mut fresh = 0;

        let RewriteResult::Finished(applied) = rewrite_step(
            &definition,
            &Pattern {
                term: subject,
                constraints: Vec::new(),
            },
            &mut fresh,
        ) else {
            panic!("the symbolic definedness branch should be retained");
        };
        assert_eq!(applied.unique_id, "uses-partial");
        assert!(matches!(
            applied.pattern.constraints.as_slice(),
            [Predicate::Ceil(term)]
                if matches!(term.kind(), TermKind::Application { symbol, .. } if symbol.name.as_ref() == "partial")
        ));
    }

    #[test]
    fn simplifies_an_instantiated_rhs_before_checking_definedness() {
        let definition = definition(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    partial{}(X:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("evaluate-partial"), simplification{}()]
            "#,
        );
        let subject = definition
            .internalize_term(
                &parse_pattern(r#"wrap{}(\dv{SortS{}}("value"))"#).unwrap(),
                &[],
            )
            .unwrap();
        let mut fresh = 0;

        let RewriteResult::Finished(applied) = rewrite_step(
            &definition,
            &Pattern {
                term: subject,
                constraints: Vec::new(),
            },
            &mut fresh,
        ) else {
            panic!("evaluated RHS should be defined");
        };
        assert_eq!(
            applied.pattern.term,
            Term::domain_value(Sort::simple("SortS"), "value")
        );
    }

    #[test]
    fn lhs_definedness_assumptions_cancel_identical_rhs_obligations() {
        let source = r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol partial{}(SortS{}) : SortS{} [function{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(partial{}(X:SortS{}), \top{SortS{}}()),
                    partial{}(X:SortS{})
                ) [label{}("preserved")]
            endmodule []"#;
        let syntax = parse_definition(source).unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();

        assert!(
            rewrite_rule(&definition)
                .computed_attributes
                .undefined_symbols
                .is_empty()
        );
    }
}

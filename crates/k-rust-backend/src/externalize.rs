//! Conversion of internal backend terms and constrained patterns back to KORE.

use k_rust_kore::kore::ast as kore;

use crate::{
    rewrite::{Pattern, Truth, predicates_truth},
    rule::Predicate,
    term::{CollectionSymbols, Sort, Term, TermKind, Variable},
};

pub fn term(term: &Term) -> kore::Pattern {
    match term.kind() {
        TermKind::And(left, right) => kore::Pattern::And {
            sort: sort(&term.sort()),
            arguments: vec![self::term(left), self::term(right)],
        },
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => application(
            &symbol.name,
            sort_arguments.iter().map(sort).collect(),
            arguments.iter().map(self::term).collect(),
        ),
        TermKind::DomainValue {
            sort: value_sort,
            value,
        } => kore::Pattern::DomainValue {
            sort: sort(value_sort),
            value: value.to_string(),
        },
        TermKind::Variable(variable) => kore::Pattern::Variable(variable_pattern(variable)),
        TermKind::Injection {
            source,
            target,
            term,
        } => application(
            "inj",
            vec![sort(source), sort(target)],
            vec![self::term(term)],
        ),
        TermKind::Map {
            definition,
            entries,
            rest,
        } => {
            let components = entries
                .iter()
                .map(|(key, value)| {
                    application(
                        &definition.symbols.element,
                        Vec::new(),
                        vec![self::term(key), self::term(value)],
                    )
                })
                .chain(rest.iter().map(self::term))
                .collect();
            collection(&definition.symbols, components)
        }
        TermKind::List {
            definition,
            heads,
            rest,
        } => {
            let mut components = heads
                .iter()
                .map(|item| {
                    application(
                        &definition.symbols.element,
                        Vec::new(),
                        vec![self::term(item)],
                    )
                })
                .collect::<Vec<_>>();
            if let Some((middle, tails)) = rest {
                components.push(self::term(middle));
                components.extend(tails.iter().map(|item| {
                    application(
                        &definition.symbols.element,
                        Vec::new(),
                        vec![self::term(item)],
                    )
                }));
            }
            collection(&definition.symbols, components)
        }
        TermKind::Set {
            definition,
            elements,
            rest,
        } => {
            let components = elements
                .iter()
                .map(|element| {
                    application(
                        &definition.symbols.element,
                        Vec::new(),
                        vec![self::term(element)],
                    )
                })
                .chain(rest.iter().map(self::term))
                .collect();
            collection(&definition.symbols, components)
        }
    }
}

pub fn constrained_pattern(pattern: &Pattern) -> kore::Pattern {
    let result_sort = pattern.term.sort();
    if predicates_truth(&pattern.constraints) == Truth::False {
        return kore::Pattern::Bottom {
            sort: sort(&result_sort),
        };
    }
    let mut predicates = pattern
        .constraints
        .iter()
        .map(|predicate| predicate_pattern(predicate, &result_sort))
        .collect::<Vec<_>>();
    let Some(predicate) = predicates.pop() else {
        return term(&pattern.term);
    };
    let predicate = if predicates.is_empty() {
        predicate
    } else {
        predicates.push(predicate);
        kore::Pattern::And {
            sort: sort(&result_sort),
            arguments: predicates,
        }
    };
    kore::Pattern::And {
        sort: sort(&result_sort),
        arguments: vec![term(&pattern.term), predicate],
    }
}

pub fn predicate_pattern(predicate: &Predicate, result_sort: &Sort) -> kore::Pattern {
    predicate_pattern_with_terms(predicate, result_sort, false)
}

/// Externalize a predicate as its direct KORE syntax, preserving bare term patterns.
pub fn ml_pattern(predicate: &Predicate, result_sort: &Sort) -> kore::Pattern {
    predicate_pattern_with_terms(predicate, result_sort, true)
}

fn predicate_pattern_with_terms(
    predicate: &Predicate,
    result_sort: &Sort,
    preserve_terms: bool,
) -> kore::Pattern {
    match predicate {
        Predicate::True => kore::Pattern::Top {
            sort: sort(result_sort),
        },
        Predicate::False => kore::Pattern::Bottom {
            sort: sort(result_sort),
        },
        Predicate::Term(value) if preserve_terms => term(value),
        Predicate::Term(value) => kore::Pattern::Equals {
            operand_sort: sort(&value.sort()),
            result_sort: sort(result_sort),
            left: Box::new(kore::Pattern::DomainValue {
                sort: sort(&value.sort()),
                value: "true".into(),
            }),
            right: Box::new(term(value)),
        },
        Predicate::Equals(left, right) => {
            let (left, right) = if is_boolean_domain_value(right) && !is_boolean_domain_value(left)
            {
                (right, left)
            } else {
                (left, right)
            };
            kore::Pattern::Equals {
                operand_sort: sort(&left.sort()),
                result_sort: sort(result_sort),
                left: Box::new(term(left)),
                right: Box::new(term(right)),
            }
        }
        Predicate::Ceil(value) => kore::Pattern::Ceil {
            operand_sort: sort(&value.sort()),
            result_sort: sort(result_sort),
            argument: Box::new(term(value)),
        },
        Predicate::Floor(value) => kore::Pattern::Floor {
            operand_sort: sort(&value.sort()),
            result_sort: sort(result_sort),
            argument: Box::new(term(value)),
        },
        Predicate::In(left, right) => kore::Pattern::In {
            operand_sort: sort(&left.sort()),
            result_sort: sort(result_sort),
            left: Box::new(term(left)),
            right: Box::new(term(right)),
        },
        Predicate::Not(inner) => kore::Pattern::Not {
            sort: sort(result_sort),
            argument: Box::new(predicate_pattern_with_terms(
                inner,
                result_sort,
                preserve_terms,
            )),
        },
        Predicate::And(inner) => kore::Pattern::And {
            sort: sort(result_sort),
            arguments: inner
                .iter()
                .map(|predicate| {
                    predicate_pattern_with_terms(predicate, result_sort, preserve_terms)
                })
                .collect(),
        },
        Predicate::Or(inner) => kore::Pattern::Or {
            sort: sort(result_sort),
            arguments: inner
                .iter()
                .map(|predicate| {
                    predicate_pattern_with_terms(predicate, result_sort, preserve_terms)
                })
                .collect(),
        },
        Predicate::Implies(left, right) => kore::Pattern::Implies {
            sort: sort(result_sort),
            left: Box::new(predicate_pattern_with_terms(
                left,
                result_sort,
                preserve_terms,
            )),
            right: Box::new(predicate_pattern_with_terms(
                right,
                result_sort,
                preserve_terms,
            )),
        },
        Predicate::Iff(left, right) => kore::Pattern::Iff {
            sort: sort(result_sort),
            left: Box::new(predicate_pattern_with_terms(
                left,
                result_sort,
                preserve_terms,
            )),
            right: Box::new(predicate_pattern_with_terms(
                right,
                result_sort,
                preserve_terms,
            )),
        },
        Predicate::Exists(variable, inner) => kore::Pattern::Exists {
            sort: sort(result_sort),
            variable: variable_pattern(variable),
            body: Box::new(predicate_pattern_with_terms(
                inner,
                result_sort,
                preserve_terms,
            )),
        },
        Predicate::Forall(variable, inner) => kore::Pattern::Forall {
            sort: sort(result_sort),
            variable: variable_pattern(variable),
            body: Box::new(predicate_pattern_with_terms(
                inner,
                result_sort,
                preserve_terms,
            )),
        },
    }
}

fn is_boolean_domain_value(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::DomainValue {
            sort: Sort::Application { name, arguments },
            value,
        } if name.as_ref() == "SortBool"
            && arguments.is_empty()
            && matches!(value.as_ref(), "true" | "false")
    )
}

pub fn sort(value: &Sort) -> kore::Sort {
    match value {
        Sort::Application { name, arguments } => kore::Sort::Application {
            name: name.to_string(),
            arguments: arguments.iter().map(sort).collect(),
        },
        Sort::Variable(name) => kore::Sort::Variable(name.to_string()),
    }
}

fn variable_pattern(variable: &Variable) -> kore::Variable {
    kore::Variable {
        kind: match variable.kind {
            crate::term::VariableKind::Element => kore::VariableKind::Element,
            crate::term::VariableKind::Set => kore::VariableKind::Set,
        },
        name: variable.name.to_string(),
        sort: sort(&variable.sort),
    }
}

fn application(
    name: &str,
    sort_parameters: Vec<kore::Sort>,
    arguments: Vec<kore::Pattern>,
) -> kore::Pattern {
    kore::Pattern::Application {
        symbol: kore::Symbol {
            name: name.to_owned(),
            sort_parameters,
        },
        arguments,
    }
}

fn collection(symbols: &CollectionSymbols, mut components: Vec<kore::Pattern>) -> kore::Pattern {
    let Some(mut result) = components.pop() else {
        return application(&symbols.unit, Vec::new(), Vec::new());
    };
    while let Some(component) = components.pop() {
        result = application(&symbols.concat, Vec::new(), vec![component, result]);
    }
    result
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::definition::BackendDefinition;

    #[test]
    fn internal_terms_round_trip_through_external_kore() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hasDomainValues{}()]
                sort SortMap{} [hook{}("MAP.Map")]
                symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit"), unit{}()]
                symbol mapItem{}(SortInt{}, SortInt{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element"), element{}()]
                symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let syntax = parse_pattern(
            r#"mapConcat{}(
                mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("2")),
                M:SortMap{}
            )"#,
        )
        .unwrap();
        let internal = definition.internalize_term(&syntax, &[]).unwrap();
        let external = term(&internal);

        assert_eq!(
            definition.internalize_term(&external, &[]).unwrap(),
            internal
        );
    }

    #[test]
    fn preserves_set_variable_kind_across_externalization() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} []
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let syntax = parse_pattern("@M:SortS{}").unwrap();
        let internal = definition.internalize_term(&syntax, &[]).unwrap();

        assert_eq!(term(&internal), syntax);
    }

    #[test]
    fn externalizes_ordered_collections_right_associatively() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hasDomainValues{}()]
                sort SortList{} [hook{}("LIST.List")]
                symbol listUnit{}() : SortList{}
                    [function{}(), total{}(), hook{}("LIST.unit"), unit{}()]
                symbol listItem{}(SortInt{}) : SortList{}
                    [function{}(), total{}(), hook{}("LIST.element"), element{}()]
                symbol listConcat{}(SortList{}, SortList{}) : SortList{}
                    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let syntax = parse_pattern(
            r#"listConcat{}(
                listItem{}(\dv{SortInt{}}("1")),
                listConcat{}(
                    listItem{}(\dv{SortInt{}}("2")),
                    listItem{}(\dv{SortInt{}}("3"))
                )
            )"#,
        )
        .unwrap();
        let internal = definition.internalize_term(&syntax, &[]).unwrap();

        assert_eq!(term(&internal), syntax);
    }

    #[test]
    fn constrained_patterns_preserve_predicate_result_sorts() {
        let value = Term::domain_value(Sort::simple("SortInt"), "1");
        let pattern = Pattern {
            term: value.clone(),
            constraints: vec![Predicate::Equals(value.clone(), value)],
        };

        assert!(matches!(
            constrained_pattern(&pattern),
            kore::Pattern::And { sort, arguments }
                if sort == kore::Sort::Application {
                    name: "SortInt".into(),
                    arguments: Vec::new(),
                } && arguments.len() == 2
        ));
    }

    #[test]
    fn constrained_patterns_group_predicates_and_collapse_bottom() {
        let sort = Sort::simple("SortInt");
        let value = Term::domain_value(sort.clone(), "1");
        let x = Term::variable(Variable::new("X", sort.clone()));
        let y = Term::variable(Variable::new("Y", sort.clone()));
        let grouped = constrained_pattern(&Pattern {
            term: value.clone(),
            constraints: vec![
                Predicate::Equals(x, value.clone()),
                Predicate::Equals(y, value.clone()),
            ],
        });
        let bottom = constrained_pattern(&Pattern {
            term: value,
            constraints: vec![Predicate::False],
        });

        assert!(matches!(
            grouped,
            kore::Pattern::And { arguments, .. }
                if arguments.len() == 2
                    && matches!(&arguments[1], kore::Pattern::And { arguments, .. } if arguments.len() == 2)
        ));
        assert!(matches!(bottom, kore::Pattern::Bottom { .. }));
    }

    #[test]
    fn bare_predicates_compare_true_before_the_predicate_term() {
        let boolean_sort = Sort::simple("SortBool");
        let value = Term::domain_value(boolean_sort.clone(), "condition");

        assert_eq!(
            predicate_pattern(&Predicate::Term(value.clone()), &boolean_sort),
            kore::Pattern::Equals {
                operand_sort: sort(&boolean_sort),
                result_sort: sort(&boolean_sort),
                left: Box::new(kore::Pattern::DomainValue {
                    sort: sort(&boolean_sort),
                    value: "true".into(),
                }),
                right: Box::new(term(&value)),
            }
        );
    }

    #[test]
    fn boolean_equalities_place_domain_values_first() {
        let boolean_sort = Sort::simple("SortBool");
        let value = Term::variable(Variable::new("P", boolean_sort.clone()));
        let false_value = Term::domain_value(boolean_sort.clone(), "false");

        assert!(matches!(
            predicate_pattern(
                &Predicate::Equals(value, false_value),
                &Sort::simple("SortGeneratedTopCell"),
            ),
            kore::Pattern::Equals { left, right, .. }
                if matches!(left.as_ref(), kore::Pattern::DomainValue { value, .. } if value == "false")
                    && matches!(right.as_ref(), kore::Pattern::Variable(variable) if variable.name == "P")
        ));
    }
}

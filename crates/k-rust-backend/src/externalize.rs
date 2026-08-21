//! Conversion of internal backend terms and constrained patterns back to KORE.

use k_rust_kore::kore::ast as kore;

use crate::{
    definition::BackendDefinition,
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

/// Externalize a Booster path constraint through its Boolean term representation.
///
/// Booster stores path predicates as `SortBool` terms and wraps each one in an ML equality to
/// `true`. Substitutions remain ordinary typed ML equalities and use [`predicate_pattern`]
/// directly instead.
pub fn booster_predicate_pattern(
    definition: &BackendDefinition,
    predicate: &Predicate,
    result_sort: &Sort,
) -> kore::Pattern {
    predicate_as_boolean_term(definition, predicate).map_or_else(
        || predicate_pattern(predicate, result_sort),
        |term| predicate_pattern(&Predicate::Term(term), result_sort),
    )
}

/// Externalize the predicate attached to an applied rule in an execute response.
///
/// Booster reports rule provenance as a logical KORE predicate even though the same condition is
/// retained on the successor state as a Boolean K term. This conversion is intentionally only a
/// projection: execution keeps the original Boolean term so unresolved `KEQUAL` applications are
/// not mistaken for semantic equality during simplification.
pub fn booster_rule_predicate_pattern(predicate: &Predicate, result_sort: &Sort) -> kore::Pattern {
    predicate_pattern(&logical_rule_predicate(predicate), result_sort)
}

fn logical_rule_predicate(predicate: &Predicate) -> Predicate {
    let recurse = logical_rule_predicate;
    match predicate {
        Predicate::Term(term) => {
            boolean_term_predicate(term, true).unwrap_or_else(|| Predicate::Term(term.clone()))
        }
        Predicate::Equals(left, right) => {
            if let Some(value) = boolean_domain_value(right) {
                boolean_term_predicate(left, value)
                    .unwrap_or_else(|| Predicate::Equals(left.clone(), right.clone()))
            } else if let Some(value) = boolean_domain_value(left) {
                boolean_term_predicate(right, value)
                    .unwrap_or_else(|| Predicate::Equals(left.clone(), right.clone()))
            } else {
                Predicate::Equals(left.clone(), right.clone())
            }
        }
        Predicate::Not(inner) => Predicate::Not(Box::new(recurse(inner))),
        Predicate::And(inner) => Predicate::And(inner.iter().map(recurse).collect()),
        Predicate::Or(inner) => Predicate::Or(inner.iter().map(recurse).collect()),
        Predicate::Implies(left, right) => {
            Predicate::Implies(Box::new(recurse(left)), Box::new(recurse(right)))
        }
        Predicate::Iff(left, right) => {
            Predicate::Iff(Box::new(recurse(left)), Box::new(recurse(right)))
        }
        Predicate::Exists(variable, inner) => {
            Predicate::Exists(variable.clone(), Box::new(recurse(inner)))
        }
        Predicate::Forall(variable, inner) => {
            Predicate::Forall(variable.clone(), Box::new(recurse(inner)))
        }
        Predicate::True
        | Predicate::False
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(_, _) => predicate.clone(),
    }
}

fn boolean_term_predicate(term: &Term, expected: bool) -> Option<Predicate> {
    if let Some(value) = boolean_domain_value(term) {
        return Some(if value == expected {
            Predicate::True
        } else {
            Predicate::False
        });
    }
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    let hook = symbol.attributes.hook.as_deref()?;
    let operand = |index, expected| {
        arguments
            .get(index)
            .and_then(|term| boolean_term_predicate(term, expected))
    };
    match (hook, arguments.as_slice()) {
        ("BOOL.not", [_]) => operand(0, !expected),
        ("BOOL.and", [_, _]) => Some(if expected {
            Predicate::And(vec![operand(0, true)?, operand(1, true)?])
        } else {
            Predicate::Or(vec![operand(0, false)?, operand(1, false)?])
        }),
        ("BOOL.or", [_, _]) => Some(if expected {
            Predicate::Or(vec![operand(0, true)?, operand(1, true)?])
        } else {
            Predicate::And(vec![operand(0, false)?, operand(1, false)?])
        }),
        (hook, [left, right]) if hook.ends_with(".eq") || hook.ends_with(".ne") => {
            let equality = Predicate::Equals(left.clone(), right.clone());
            let equality_expected = expected == hook.ends_with(".eq");
            Some(if equality_expected {
                equality
            } else {
                Predicate::Not(Box::new(equality))
            })
        }
        _ => None,
    }
}

fn predicate_as_boolean_term(
    definition: &BackendDefinition,
    predicate: &Predicate,
) -> Option<Term> {
    let boolean_sort = definition.sorts.iter().find_map(|(name, info)| {
        (info.hook.as_deref() == Some("BOOL.Bool") && info.parameters.is_empty())
            .then(|| Sort::simple(name.clone()))
    })?;
    let boolean =
        |value| Term::domain_value(boolean_sort.clone(), if value { "true" } else { "false" });
    let hooked = |hook: &str, arguments: Vec<Term>| {
        definition
            .symbols
            .values()
            .find(|symbol| {
                symbol.attributes.hook.as_deref() == Some(hook)
                    && symbol.sort_variables.is_empty()
                    && symbol.argument_sorts == arguments.iter().map(Term::sort).collect::<Vec<_>>()
            })
            .map(|symbol| Term::application(symbol.clone(), Vec::new(), arguments))
    };
    let recurse = |predicate| predicate_as_boolean_term(definition, predicate);
    match predicate {
        Predicate::True => Some(boolean(true)),
        Predicate::False => Some(boolean(false)),
        Predicate::Term(term) if term.sort() == boolean_sort => Some(term.clone()),
        Predicate::Equals(left, right) => {
            let bool_value = |term: &Term| match term.kind() {
                TermKind::DomainValue { sort, value } if sort == &boolean_sort => {
                    match value.as_ref() {
                        "true" => Some(true),
                        "false" => Some(false),
                        _ => None,
                    }
                }
                _ => None,
            };
            if left.sort() == boolean_sort
                && let Some(value) = bool_value(right)
            {
                return if value {
                    Some(left.clone())
                } else {
                    hooked("BOOL.not", vec![left.clone()])
                };
            }
            if right.sort() == boolean_sort
                && let Some(value) = bool_value(left)
            {
                return if value {
                    Some(right.clone())
                } else {
                    hooked("BOOL.not", vec![right.clone()])
                };
            }
            definition
                .symbols
                .values()
                .find(|symbol| {
                    symbol
                        .attributes
                        .hook
                        .as_deref()
                        .is_some_and(|hook| hook.ends_with(".eq"))
                        && symbol.sort_variables.is_empty()
                        && symbol.result_sort == boolean_sort
                        && symbol.argument_sorts == [left.sort(), right.sort()]
                })
                .map(|symbol| {
                    Term::application(
                        symbol.clone(),
                        Vec::new(),
                        vec![left.clone(), right.clone()],
                    )
                })
        }
        Predicate::Not(inner) => hooked("BOOL.not", vec![recurse(inner)?]),
        Predicate::And(inner) => {
            let mut terms = inner
                .iter()
                .map(recurse)
                .collect::<Option<Vec<_>>>()?
                .into_iter();
            let mut result = terms.next().unwrap_or_else(|| boolean(true));
            for term in terms {
                result = hooked("BOOL.and", vec![result, term])?;
            }
            Some(result)
        }
        Predicate::Or(inner) => {
            let mut terms = inner
                .iter()
                .map(recurse)
                .collect::<Option<Vec<_>>>()?
                .into_iter();
            let mut result = terms.next().unwrap_or_else(|| boolean(false));
            for term in terms {
                result = hooked("BOOL.or", vec![result, term])?;
            }
            Some(result)
        }
        Predicate::Implies(left, right) => {
            hooked("BOOL.implies", vec![recurse(left)?, recurse(right)?])
        }
        Predicate::Iff(left, right) => hooked("BOOL.eq", vec![recurse(left)?, recurse(right)?]),
        Predicate::Term(_)
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(_, _)
        | Predicate::Exists(_, _)
        | Predicate::Forall(_, _) => None,
    }
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
    boolean_domain_value(term).is_some()
}

fn boolean_domain_value(term: &Term) -> Option<bool> {
    let TermKind::DomainValue {
        sort: Sort::Application { name, arguments },
        value,
    } = term.kind()
    else {
        return None;
    };
    if name.as_ref() != "SortBool" || !arguments.is_empty() {
        return None;
    }
    match value.as_ref() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
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

    #[test]
    fn booster_constraints_reify_typed_equalities_as_boolean_terms() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-symbol intEq{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq")]
                hooked-symbol boolEq{}(SortBool{}, SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.eq")]
                hooked-symbol boolNot{}(SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.not")]
                symbol condition{}() : SortBool{} [function{}(), total{}()]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let int_sort = Sort::simple("SortInt");
        let result_sort = Sort::simple("SortGeneratedTopCell");
        let x = Term::variable(Variable::new("X", int_sort.clone()));
        let one = Term::domain_value(int_sort, "1");

        let pattern =
            booster_predicate_pattern(&definition, &Predicate::Equals(x, one), &result_sort);

        assert!(matches!(
            pattern,
            kore::Pattern::Equals {
                operand_sort,
                left,
                right,
                ..
            } if operand_sort == sort(&Sort::simple("SortBool"))
                && matches!(left.as_ref(), kore::Pattern::DomainValue { value, .. } if value == "true")
                && matches!(right.as_ref(), kore::Pattern::Application { symbol, .. } if symbol.name == "intEq")
        ));

        let condition = definition
            .internalize_term(&parse_pattern("condition{}()").unwrap(), &[])
            .unwrap();
        let truth = Term::domain_value(Sort::simple("SortBool"), "true");
        let pattern = booster_predicate_pattern(
            &definition,
            &Predicate::Equals(condition, truth.clone()),
            &result_sort,
        );
        assert!(matches!(
            pattern,
            kore::Pattern::Equals { right, .. }
                if matches!(right.as_ref(), kore::Pattern::Application { symbol, .. } if symbol.name == "condition")
        ));

        let condition = definition
            .internalize_term(
                &parse_pattern(r#"boolNot{}(intEq{}(X:SortInt{}, \dv{SortInt{}}("1")))"#).unwrap(),
                &[],
            )
            .unwrap();
        let logical =
            booster_rule_predicate_pattern(&Predicate::Equals(truth, condition), &result_sort);
        assert!(matches!(
            logical,
            kore::Pattern::Not { argument, .. }
                if matches!(argument.as_ref(), kore::Pattern::Equals { left, right, .. }
                    if matches!(left.as_ref(), kore::Pattern::Variable(variable) if variable.name == "X")
                        && matches!(right.as_ref(), kore::Pattern::DomainValue { value, .. } if value == "1"))
        ));
    }
}

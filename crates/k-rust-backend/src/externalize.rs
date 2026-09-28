//! Conversion of internal backend terms and constrained patterns back to KORE: one structural
//! pass per pattern; a responsibility, not an algorithm; no counter, no worklist. Conjunction,
//! disjunction, and substitution builders take the caller's binding order and shape because
//! printed KORE and RPC JSON are contracts. The same conversion is also available one node at a
//! time, as an [`External`] pattern source, for readers that must not hold the whole tree.

use std::{borrow::Cow, cmp::Ordering, collections::BTreeSet};

use k_rust_kore::kore::ast as kore;
use k_rust_kore::kore::node::{PatternNode, PatternSource};
use k_rust_kore::names::{BuiltinSort, WellKnownSymbol};

use crate::{
    definition::BackendDefinition,
    rewrite::{Pattern, Truth, predicates_truth},
    rule::Predicate,
    substitution::Substitution,
    term::{
        CollectionSymbols, Sort, Term, TermKind, Variable,
        names::{HookName, HookNamespace, VariableProvenance, split_fresh_counter, split_marker},
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConjunctionShape {
    LeftNested,
    Flat,
    Balanced,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BindingOrder {
    Container,
    NameThenSort,
    Natural,
}

pub fn natural_name_order(left: &str, right: &str) -> Ordering {
    fn trailing_number(name: &str) -> (&str, &str) {
        let prefix_length = name
            .trim_end_matches(|character: char| character.is_ascii_digit())
            .len();
        (&name[..prefix_length], &name[prefix_length..])
    }

    fn normalized(number: &str) -> &str {
        let number = number.trim_start_matches('0');
        if number.is_empty() { "0" } else { number }
    }

    let (left_prefix, left_number) = trailing_number(left);
    let (right_prefix, right_number) = trailing_number(right);
    if left_prefix == right_prefix && !left_number.is_empty() && !right_number.is_empty() {
        let left_value = normalized(left_number);
        let right_value = normalized(right_number);
        return left_value
            .len()
            .cmp(&right_value.len())
            .then_with(|| left_value.cmp(right_value))
            .then_with(|| left_number.len().cmp(&right_number.len()))
            .then_with(|| left.cmp(right));
    }
    left.cmp(right)
}

pub fn conjunction(
    sort: &kore::Sort,
    patterns: Vec<kore::Pattern>,
    shape: ConjunctionShape,
) -> Option<kore::Pattern> {
    connective(sort, patterns, shape, true)
}

pub fn disjunction(
    sort: &kore::Sort,
    patterns: Vec<kore::Pattern>,
    shape: ConjunctionShape,
) -> Option<kore::Pattern> {
    connective(sort, patterns, shape, false)
}

fn connective(
    sort: &kore::Sort,
    mut patterns: Vec<kore::Pattern>,
    shape: ConjunctionShape,
    and: bool,
) -> Option<kore::Pattern> {
    let node = |arguments| {
        if and {
            kore::Pattern::And {
                sort: sort.clone(),
                arguments,
            }
        } else {
            kore::Pattern::Or {
                sort: sort.clone(),
                arguments,
            }
        }
    };
    match patterns.len() {
        0 => None,
        1 => patterns.pop(),
        _ => Some(match shape {
            ConjunctionShape::Flat => node(patterns),
            ConjunctionShape::LeftNested => {
                let mut patterns = patterns.into_iter();
                let mut result = patterns.next().expect("the length was checked");
                for pattern in patterns {
                    result = node(vec![result, pattern]);
                }
                result
            }
            ConjunctionShape::Balanced => {
                /// The balanced tree over the next `length` (at least 1) operands of `patterns`:
                /// the operand itself when `length` is 1, otherwise a binary node whose left
                /// subtree holds the next `length / 2` operands and whose right subtree holds the
                /// `length - length / 2` after them. Each operand is moved out once, in order.
                fn balanced(
                    patterns: &mut impl Iterator<Item = kore::Pattern>,
                    length: usize,
                    node: &impl Fn(Vec<kore::Pattern>) -> kore::Pattern,
                ) -> kore::Pattern {
                    if length == 1 {
                        return patterns
                            .next()
                            .expect("the caller asks for at most the operands that remain");
                    }
                    let middle = length / 2;
                    let left = balanced(patterns, middle, node);
                    let right = balanced(patterns, length - middle, node);
                    node(vec![left, right])
                }
                let length = patterns.len();
                balanced(&mut patterns.into_iter(), length, &node)
            }
        }),
    }
}

/// The bindings of `substitution` in the order `order` names; the sorts are stable, so bindings
/// that compare equal keep their container order.
pub fn ordered_bindings(
    substitution: &Substitution,
    order: BindingOrder,
) -> Vec<(&Variable, &Term)> {
    let mut bindings = substitution.iter().collect::<Vec<_>>();
    match order {
        BindingOrder::Container => {}
        BindingOrder::NameThenSort => bindings.sort_by(|(left, _), (right, _)| {
            left.name
                .cmp(&right.name)
                .then_with(|| left.sort.cmp(&right.sort))
        }),
        BindingOrder::Natural => bindings.sort_by(|(left, _), (right, _)| {
            natural_name_order(&left.name, &right.name).then_with(|| left.sort.cmp(&right.sort))
        }),
    }
    bindings
}

pub fn substitution_pattern(
    substitution: &Substitution,
    result_sort: &Sort,
    order: BindingOrder,
    shape: ConjunctionShape,
) -> Option<kore::Pattern> {
    let patterns = ordered_bindings(substitution, order)
        .into_iter()
        .map(|(variable, value)| {
            predicate_pattern(
                &Predicate::Equals(Term::variable(variable.clone()), value.clone()),
                result_sort,
            )
        })
        .collect();
    conjunction(&sort(result_sort), patterns, shape)
}

pub fn predicates_pattern(
    predicates: &[Predicate],
    result_sort: &Sort,
    render: impl Fn(&Predicate) -> kore::Pattern,
    shape: ConjunctionShape,
) -> Option<kore::Pattern> {
    conjunction(
        &sort(result_sort),
        predicates
            .iter()
            .filter(|predicate| !matches!(predicate, Predicate::True))
            .map(render)
            .collect(),
        shape,
    )
}

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
            value: value.clone(),
        },
        TermKind::Variable(variable) => kore::Pattern::Variable(variable_pattern(variable)),
        TermKind::Injection {
            source,
            target,
            term,
        } => application(
            WellKnownSymbol::Inj.as_str(),
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
    predicate_pattern(
        &logical_rule_predicate(&Sort::builtin(BuiltinSort::Bool), predicate),
        result_sort,
    )
}

/// Externalize applied-rule provenance using the definition's declared `BOOL.Bool` sort.
pub fn booster_rule_predicate_pattern_in_definition(
    definition: &BackendDefinition,
    predicate: &Predicate,
    result_sort: &Sort,
) -> kore::Pattern {
    declared_boolean_sort(definition).map_or_else(
        || predicate_pattern(predicate, result_sort),
        |boolean_sort| {
            predicate_pattern(
                &logical_rule_predicate(&boolean_sort, predicate),
                result_sort,
            )
        },
    )
}

fn logical_rule_predicate(boolean_sort: &Sort, predicate: &Predicate) -> Predicate {
    let recurse = |predicate| logical_rule_predicate(boolean_sort, predicate);
    match predicate {
        Predicate::Term(term) => boolean_term_predicate(boolean_sort, term, true)
            .unwrap_or_else(|| Predicate::Term(term.clone())),
        Predicate::Equals(left, right) => {
            if let Some(value) = boolean_domain_value_of_sort(boolean_sort, right) {
                boolean_term_predicate(boolean_sort, left, value)
                    .unwrap_or_else(|| Predicate::Equals(left.clone(), right.clone()))
            } else if let Some(value) = boolean_domain_value_of_sort(boolean_sort, left) {
                boolean_term_predicate(boolean_sort, right, value)
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

fn boolean_term_predicate(boolean_sort: &Sort, term: &Term, expected: bool) -> Option<Predicate> {
    if let Some(value) = boolean_domain_value_of_sort(boolean_sort, term) {
        return Some(if value == expected {
            Predicate::True
        } else {
            Predicate::False
        });
    }
    if term.sort() != *boolean_sort {
        return None;
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
            .and_then(|term| boolean_term_predicate(boolean_sort, term, expected))
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
        (hook, [left, right])
            if HookName::parse(hook).is_some_and(|hook| {
                matches!(hook.operation, "eq" | "ne") && hook.kind() != HookNamespace::Float
            }) =>
        {
            let equality = Predicate::Equals(left.clone(), right.clone());
            let equality_expected =
                expected == HookName::parse(hook).is_some_and(|hook| hook.operation == "eq");
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
    let boolean_sort = declared_boolean_sort(definition)?;
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
                    match value.as_utf8().ok()? {
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
                        .and_then(HookName::parse)
                        .is_some_and(|hook| {
                            hook.operation == "eq" && hook.kind() != HookNamespace::Float
                        })
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
            operand_sort: Box::new(sort(&value.sort())),
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
                operand_sort: Box::new(sort(&left.sort())),
                result_sort: sort(result_sort),
                left: Box::new(term(left)),
                right: Box::new(term(right)),
            }
        }
        Predicate::Ceil(value) => kore::Pattern::Ceil {
            operand_sort: Box::new(sort(&value.sort())),
            result_sort: sort(result_sort),
            argument: Box::new(term(value)),
        },
        Predicate::Floor(value) => kore::Pattern::Floor {
            operand_sort: Box::new(sort(&value.sort())),
            result_sort: sort(result_sort),
            argument: Box::new(term(value)),
        },
        Predicate::In(left, right) => kore::Pattern::In {
            operand_sort: Box::new(sort(&left.sort())),
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
            variable: Box::new(variable_pattern(variable)),
            body: Box::new(predicate_pattern_with_terms(
                inner,
                result_sort,
                preserve_terms,
            )),
        },
        Predicate::Forall(variable, inner) => kore::Pattern::Forall {
            sort: sort(result_sort),
            variable: Box::new(variable_pattern(variable)),
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

fn declared_boolean_sort(definition: &BackendDefinition) -> Option<Sort> {
    definition.sorts.iter().find_map(|(name, info)| {
        (info.hook.as_deref() == Some("BOOL.Bool") && info.parameters.is_empty())
            .then(|| Sort::simple(name.clone()))
    })
}

fn boolean_domain_value_of_sort(boolean_sort: &Sort, term: &Term) -> Option<bool> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    if sort != boolean_sort {
        return None;
    }
    match value.as_utf8().ok()? {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

fn boolean_domain_value(term: &Term) -> Option<bool> {
    boolean_domain_value_of_sort(&Sort::builtin(BuiltinSort::Bool), term)
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
        name: external_variable_name(&variable.name),
        sort: sort(&variable.sort),
    }
}

/// Externalize an internal variable name as the KORE identifier the reference engines print.
///
/// Booster keeps the `Rule#`/`Ex#` provenance markers internally and drops the `#` when it
/// externalizes them (`Booster.Pattern.Util.externaliseRuleMarker`); the backend's `Eq#` equation
/// marker follows the same rule. Kore stores a fresh name as a base plus a counter and appends the
/// counter's digits to the base on output (`Kore.Syntax.Variable.externalizeFreshVariableName`);
/// `fresh_variable` writes that counter as `!N`, so `Ex#Frame!0` externalizes as `ExFrame0`. Any
/// other character outside the identifier grammar of `Kore/Parser/Lexer.x` (`[a-zA-Z0-9'-]`, a
/// leading `@` for set variables) is written as the apostrophe-delimited word K's identifier
/// encoding uses, so the result always lexes. Like the reference's, the mapping is not injective;
/// the K frontend never produces names starting with `Rule`, `Ex` or `Eq` without the `Var`
/// prefix, so externalized names do not collide with user variables.
pub fn external_variable_name(name: &str) -> String {
    let (marker, rest) = split_marker(name, &VariableProvenance::ALL);
    let marker = marker.map_or("", VariableProvenance::external_prefix);
    let (base, counter) = split_fresh_counter(rest);
    let mut external = String::with_capacity(name.len());
    for (index, character) in marker
        .chars()
        .chain(base.chars())
        .chain(counter.chars())
        .enumerate()
    {
        match character {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '\'' | '-' => external.push(character),
            '@' if index == 0 => external.push(character),
            '#' => external.push_str("'Hash'"),
            '!' => external.push_str("'Bang'"),
            other => {
                use std::fmt::Write;
                write!(external, "'{:04x}'", u32::from(other)).expect("writing to a string");
            }
        }
    }
    external
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
    // Invariant: `result` is the right-nested `symbols.concat` of the components popped so far, in their original order; each iteration pops one entry of `components` and pushes none.
    while let Some(component) = components.pop() {
        result = application(&symbols.concat, Vec::new(), vec![component, result]);
    }
    result
}

/// The sort a predicate's connectives and equalities are written at: given, or the sort of a
/// constrained pattern's term.
#[derive(Clone, Copy, Debug)]
pub enum ResultSort<'t> {
    Given(&'t Sort),
    OfTerm(&'t Term),
}

impl ResultSort<'_> {
    fn external(self) -> kore::Sort {
        match self {
            Self::Given(result_sort) => sort(result_sort),
            Self::OfTerm(term) => sort(&term.sort()),
        }
    }
}

/// A KORE pattern given by backend data, externalized one node at a time
/// ([`PatternSource::node`]) as a reader reaches it.
///
/// A backend term is a DAG that shares subterms, and its KORE text writes every shared subterm
/// out at each of its uses, so the externalized tree can be far larger than the term. A source
/// holds only references into the backend data, and its node is a function of the node it
/// denotes: printing it with `Printer::write_source`, comparing it with
/// [`k_rust_kore::kore::node::compare`], or flattening it never holds more than the path being
/// read.
///
/// Each source materializes (`k_rust_kore::kore::node::materialize`) to the tree the builder of
/// the same name returns: [`term`], [`predicate_pattern`], [`ml_pattern`],
/// [`constrained_pattern`], [`conjunction`], and [`disjunction`]. The builders stay the direct
/// recursive construction because building a whole tree through nodes costs about half again
/// as many instructions; `tests::externalize` checks that both agree node for node.
#[derive(Clone, Copy, Debug)]
pub enum External<'t> {
    /// The term.
    Term(&'t Term),
    /// The variable, as the term `Term::variable` of it.
    Variable(&'t Variable),
    /// `\dv{S}("true")`, where `S` is the sort of the term: the left side of the equality that
    /// states a Boolean term.
    TrueValue(&'t Term),
    /// The right-nested `concat` of the components of the map, list, or set term from the
    /// component with the given index on, which is less than the number of components; the
    /// collection's `unit` when it has none.
    Components(&'t Term, usize),
    /// The `element` application of a map entry.
    MapElement(&'t str, &'t Term, &'t Term),
    /// The `element` application of a list or set item.
    Element(&'t str, &'t Term),
    /// The predicate as [`predicate_pattern`] (or, preserving bare terms, [`ml_pattern`])
    /// writes it at `sort`.
    Predicate {
        predicate: &'t Predicate,
        sort: ResultSort<'t>,
        preserve_terms: bool,
    },
    /// The equality `predicate_pattern` writes for the binding of `variable` to `value`, that is
    /// for `Predicate::Equals(Term::variable(variable), value)`.
    Binding {
        variable: &'t Variable,
        value: &'t Term,
        sort: &'t Sort,
    },
    /// The constrained pattern, as [`constrained_pattern`] writes it.
    Constrained(&'t Pattern),
    /// The `\and` of the (at least two) constraints of the pattern, at the sort of its term.
    Constraints(&'t Pattern),
    /// The operands joined in the given shape by `\and` (`and`) or `\or` at `sort`, as
    /// [`conjunction`] and [`disjunction`] join two or more. A `Flat` connective is one node
    /// over its operands, of any number; a nested shape has at least two.
    Connective {
        and: bool,
        shape: ConjunctionShape,
        sort: &'t kore::Sort,
        operands: &'t [External<'t>],
    },
    /// `\top` at the sort.
    Top(&'t kore::Sort),
    /// `\bottom` at the sort.
    Bottom(&'t kore::Sort),
}

/// The source of [`conjunction`] (`and`) or [`disjunction`] of `operands`: `None` for none, the
/// operand itself for one.
pub fn connective_source<'t>(
    sort: &'t kore::Sort,
    operands: &'t [External<'t>],
    shape: ConjunctionShape,
    and: bool,
) -> Option<External<'t>> {
    match operands {
        [] => None,
        [operand] => Some(*operand),
        operands => Some(External::Connective {
            and,
            shape,
            sort,
            operands,
        }),
    }
}

/// The number of components `term` has as a collection (map entries, list items, and set
/// elements, each rest counting as one), and the collection's symbols.
fn components(term: &Term) -> (usize, &CollectionSymbols) {
    match term.kind() {
        TermKind::Map {
            definition,
            entries,
            rest,
        } => (
            entries.len() + usize::from(rest.is_some()),
            &definition.symbols,
        ),
        TermKind::List {
            definition,
            heads,
            rest,
        } => (
            heads.len() + rest.as_ref().map_or(0, |(_, tails)| 1 + tails.len()),
            &definition.symbols,
        ),
        TermKind::Set {
            definition,
            elements,
            rest,
        } => (
            elements.len() + usize::from(rest.is_some()),
            &definition.symbols,
        ),
        _ => unreachable!("only a collection has components"),
    }
}

/// The component of the collection `term` at `index`.
fn component(term: &Term, index: usize) -> External<'_> {
    match term.kind() {
        TermKind::Map {
            definition,
            entries,
            rest,
        } => {
            let element = &definition.symbols.element;
            match entries.get(index) {
                Some((key, value)) => External::MapElement(element, key, value),
                None => External::Term(rest.as_ref().expect("the index is below the count")),
            }
        }
        TermKind::List {
            definition,
            heads,
            rest,
        } => {
            let element = &definition.symbols.element;
            if let Some(item) = heads.get(index) {
                External::Element(element, item)
            } else {
                let (middle, tails) = rest.as_ref().expect("the index is below the count");
                match index - heads.len() {
                    0 => External::Term(middle),
                    tail => External::Element(element, &tails[tail - 1]),
                }
            }
        }
        TermKind::Set {
            definition,
            elements,
            rest,
        } => {
            let element = &definition.symbols.element;
            match elements.get(index) {
                Some(item) => External::Element(element, item),
                None => External::Term(rest.as_ref().expect("the index is below the count")),
            }
        }
        _ => unreachable!("only a collection has components"),
    }
}

fn application_node<'t>(
    name: &str,
    sort_parameters: Vec<kore::Sort>,
    arguments: Vec<External<'t>>,
) -> PatternNode<'t, External<'t>> {
    PatternNode::Application {
        symbol: Cow::Owned(kore::Symbol {
            name: name.to_owned(),
            sort_parameters,
        }),
        arguments,
    }
}

fn term_node(term: &Term) -> PatternNode<'_, External<'_>> {
    match term.kind() {
        TermKind::And(left, right) => PatternNode::And {
            sort: Cow::Owned(sort(&term.sort())),
            arguments: vec![External::Term(left), External::Term(right)],
        },
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => application_node(
            &symbol.name,
            sort_arguments.iter().map(sort).collect(),
            arguments.iter().map(External::Term).collect(),
        ),
        TermKind::DomainValue {
            sort: value_sort,
            value,
        } => PatternNode::DomainValue {
            sort: Cow::Owned(sort(value_sort)),
            value: Cow::Borrowed(value),
        },
        TermKind::Variable(variable) => {
            PatternNode::Variable(Cow::Owned(variable_pattern(variable)))
        }
        TermKind::Injection {
            source,
            target,
            term,
        } => application_node(
            WellKnownSymbol::Inj.as_str(),
            vec![sort(source), sort(target)],
            vec![External::Term(term)],
        ),
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. } => {
            External::Components(term, 0).node()
        }
    }
}

/// The node of `predicate` at `result_sort`: `\top`/`\bottom` for the constants, the ML
/// connective of the same name otherwise, and an equality for a bare Boolean term unless
/// `preserve_terms`. An equality puts a Boolean domain value on the left when only its right
/// side is one.
fn predicate_node<'t>(
    predicate: &'t Predicate,
    result_sort: ResultSort<'t>,
    preserve_terms: bool,
) -> PatternNode<'t, External<'t>> {
    let recurse = |predicate| External::Predicate {
        predicate,
        sort: result_sort,
        preserve_terms,
    };
    let sort_of = |term: &Term| Cow::Owned(sort(&term.sort()));
    let result = || Cow::Owned(result_sort.external());
    match predicate {
        Predicate::True => PatternNode::Top { sort: result() },
        Predicate::False => PatternNode::Bottom { sort: result() },
        Predicate::Term(value) if preserve_terms => term_node(value),
        Predicate::Term(value) => PatternNode::Equals {
            operand_sort: sort_of(value),
            result_sort: result(),
            left: External::TrueValue(value),
            right: External::Term(value),
        },
        Predicate::Equals(left, right) => {
            let (left, right) = if is_boolean_domain_value(right) && !is_boolean_domain_value(left)
            {
                (right, left)
            } else {
                (left, right)
            };
            PatternNode::Equals {
                operand_sort: sort_of(left),
                result_sort: result(),
                left: External::Term(left),
                right: External::Term(right),
            }
        }
        Predicate::Ceil(value) => PatternNode::Ceil {
            operand_sort: sort_of(value),
            result_sort: result(),
            argument: External::Term(value),
        },
        Predicate::Floor(value) => PatternNode::Floor {
            operand_sort: sort_of(value),
            result_sort: result(),
            argument: External::Term(value),
        },
        Predicate::In(left, right) => PatternNode::In {
            operand_sort: sort_of(left),
            result_sort: result(),
            left: External::Term(left),
            right: External::Term(right),
        },
        Predicate::Not(inner) => PatternNode::Not {
            sort: result(),
            argument: recurse(inner),
        },
        Predicate::And(inner) => PatternNode::And {
            sort: result(),
            arguments: inner.iter().map(recurse).collect(),
        },
        Predicate::Or(inner) => PatternNode::Or {
            sort: result(),
            arguments: inner.iter().map(recurse).collect(),
        },
        Predicate::Implies(left, right) => PatternNode::Implies {
            sort: result(),
            left: recurse(left),
            right: recurse(right),
        },
        Predicate::Iff(left, right) => PatternNode::Iff {
            sort: result(),
            left: recurse(left),
            right: recurse(right),
        },
        Predicate::Exists(variable, inner) => PatternNode::Exists {
            sort: result(),
            variable: Cow::Owned(variable_pattern(variable)),
            body: recurse(inner),
        },
        Predicate::Forall(variable, inner) => PatternNode::Forall {
            sort: result(),
            variable: Cow::Owned(variable_pattern(variable)),
            body: recurse(inner),
        },
    }
}

impl<'t> PatternSource<'t> for External<'t> {
    #[cfg(feature = "measure")]
    fn node_identity(&self) -> Option<usize> {
        match self {
            Self::Term(term) => Some(term.allocation_identity()),
            _ => None,
        }
    }

    fn node(self) -> PatternNode<'t, Self> {
        match self {
            Self::Term(term) => term_node(term),
            Self::Variable(variable) => {
                PatternNode::Variable(Cow::Owned(variable_pattern(variable)))
            }
            Self::TrueValue(term) => PatternNode::DomainValue {
                sort: Cow::Owned(sort(&term.sort())),
                value: Cow::Owned("true".into()),
            },
            Self::Components(term, index) => {
                let (count, symbols) = components(term);
                if count == 0 {
                    return application_node(&symbols.unit, Vec::new(), Vec::new());
                }
                let first = component(term, index);
                if index + 1 == count {
                    return first.node();
                }
                application_node(
                    &symbols.concat,
                    Vec::new(),
                    vec![first, Self::Components(term, index + 1)],
                )
            }
            Self::MapElement(element, key, value) => application_node(
                element,
                Vec::new(),
                vec![Self::Term(key), Self::Term(value)],
            ),
            Self::Element(element, item) => {
                application_node(element, Vec::new(), vec![Self::Term(item)])
            }
            Self::Predicate {
                predicate,
                sort,
                preserve_terms,
            } => predicate_node(predicate, sort, preserve_terms),
            Self::Binding {
                variable,
                value,
                sort: result_sort,
            } => {
                // `Term::variable(variable)` is not a domain value, so the value goes on the
                // left exactly when it is a Boolean domain value.
                let (operand_sort, left, right) = if is_boolean_domain_value(value) {
                    (value.sort(), Self::Term(value), Self::Variable(variable))
                } else {
                    (
                        variable.sort.clone(),
                        Self::Variable(variable),
                        Self::Term(value),
                    )
                };
                PatternNode::Equals {
                    operand_sort: Cow::Owned(sort(&operand_sort)),
                    result_sort: Cow::Owned(sort(result_sort)),
                    left,
                    right,
                }
            }
            Self::Constrained(pattern) => {
                let result_sort = || Cow::Owned(sort(&pattern.term.sort()));
                if predicates_truth(&pattern.constraints) == Truth::False {
                    return PatternNode::Bottom {
                        sort: result_sort(),
                    };
                }
                let predicate = match pattern.constraints.as_slice() {
                    [] => return term_node(&pattern.term),
                    [predicate] => Self::Predicate {
                        predicate,
                        sort: ResultSort::OfTerm(&pattern.term),
                        preserve_terms: false,
                    },
                    _ => Self::Constraints(pattern),
                };
                PatternNode::And {
                    sort: result_sort(),
                    arguments: vec![Self::Term(&pattern.term), predicate],
                }
            }
            Self::Constraints(pattern) => PatternNode::And {
                sort: Cow::Owned(sort(&pattern.term.sort())),
                arguments: pattern
                    .constraints
                    .iter()
                    .map(|predicate| Self::Predicate {
                        predicate,
                        sort: ResultSort::OfTerm(&pattern.term),
                        preserve_terms: false,
                    })
                    .collect(),
            },
            Self::Connective {
                and,
                shape,
                sort,
                operands,
            } => {
                let part = |operands| {
                    connective_source(sort, operands, shape, and).expect(
                        "a nested connective splits two or more operands into non-empty parts",
                    )
                };
                let arguments = match shape {
                    ConjunctionShape::Flat => operands.to_vec(),
                    ConjunctionShape::LeftNested => {
                        let (last, init) = operands
                            .split_last()
                            .expect("a connective has at least two operands");
                        vec![part(init), *last]
                    }
                    ConjunctionShape::Balanced => {
                        let (left, right) = operands.split_at(operands.len() / 2);
                        vec![part(left), part(right)]
                    }
                };
                let sort = Cow::Borrowed(sort);
                if and {
                    PatternNode::And { sort, arguments }
                } else {
                    PatternNode::Or { sort, arguments }
                }
            }
            Self::Top(sort) => PatternNode::Top {
                sort: Cow::Borrowed(sort),
            },
            Self::Bottom(sort) => PatternNode::Bottom {
                sort: Cow::Borrowed(sort),
            },
        }
    }

    /// Equal backend terms (and equal collection suffixes of equal terms) externalize to equal
    /// patterns, because externalization reads only the term's structure; `Term`'s `Eq` is
    /// structural equality and answers a shared or differently hashed pair in O(1).
    fn same_pattern(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Term(left), Self::Term(right)) => left == right,
            (Self::Components(left, i), Self::Components(right, j)) => i == j && left == right,
            _ => false,
        }
    }
}

impl External<'_> {
    /// A superset of the backend variables whose externalized forms occur in this pattern, when
    /// it is a term, a suffix of a collection term, or a collection item; `None` otherwise.
    pub fn term_variables(&self) -> Option<&BTreeSet<Variable>> {
        match self {
            Self::Term(term) | Self::Components(term, _) | Self::Element(_, term) => {
                Some(&term.attributes().variables)
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::definition::BackendDefinition;

    #[cfg(feature = "measure")]
    #[test]
    fn source_node_count_sees_shared_backend_allocations() {
        let leaf = Term::domain_value(Sort::simple("SortInt"), "1");
        let mut root = leaf;
        for _ in 0..30 {
            root = Term::and(root.clone(), root);
        }
        let (written, distinct) = k_rust_kore::kore::node::measure_nodes(External::Term(&root));
        assert_eq!((written, distinct), (2u64.pow(31) - 1, 31));
    }

    /// Kore/Parser/Lexer.x:57 admits `[a-zA-Z][a-zA-Z0-9'\-]*` as an identifier. Booster keeps
    /// the `Ex#`/`Rule#` provenance markers internally and externalizes them by dropping the `#`
    /// (Booster/Pattern/Util.hs externaliseRuleMarker); Kore externalizes a fresh name's counter
    /// by appending its digits to the base (Kore/Syntax/Variable.hs externalizeFreshVariableName).
    #[test]
    fn fresh_and_marked_variable_names_externalize_as_kore_identifiers() {
        let map = Sort::simple("SortMap");
        let item = Sort::simple("SortKItem");
        let cases = [
            (Variable::new("Ex#Frame!0", map.clone()), "ExFrame0"),
            (
                Variable::new("Ex#Var'Unds'K!1", item.clone()),
                "ExVar'Unds'K1",
            ),
            (Variable::new("Eq#VarROOT", item.clone()), "EqVarROOT"),
            (Variable::new("Rule#X", item.clone()), "RuleX"),
            (Variable::new("VarM", map), "VarM"),
            (Variable::new("Var'Unds'Gen0", item), "Var'Unds'Gen0"),
        ];
        for (variable, expected) in cases {
            let external = term(&Term::variable(variable.clone()));
            let kore::Pattern::Variable(external_variable) = &external else {
                panic!("a variable externalizes as a variable: {external:?}");
            };
            assert_eq!(external_variable.name, expected, "{}", variable.name);
            let printed = external.to_string();
            assert_eq!(
                parse_pattern(&printed).unwrap_or_else(|error| panic!("{printed}: {error:?}")),
                external,
                "{printed} round-trips through the KORE parser"
            );
        }
    }

    #[test]
    fn internal_terms_round_trip_through_external_kore() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hasDomainValues{}()]
                hooked-sort SortMap{} [hook{}("MAP.Map")]
                hooked-symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit"), unit{}()]
                hooked-symbol mapItem{}(SortInt{}, SortInt{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element"), element{}()]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
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
                hooked-sort SortList{} [hook{}("LIST.List")]
                hooked-symbol listUnit{}() : SortList{}
                    [function{}(), total{}(), hook{}("LIST.unit"), unit{}()]
                hooked-symbol listItem{}(SortInt{}) : SortList{}
                    [function{}(), total{}(), hook{}("LIST.element"), element{}()]
                hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
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
            &constrained_pattern(&pattern),
            kore::Pattern::And { sort, arguments }
                if sort == &kore::Sort::Application {
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
            &grouped,
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
                operand_sort: Box::new(sort(&boolean_sort)),
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
            &predicate_pattern(
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
            &pattern,
            kore::Pattern::Equals {
                operand_sort,
                left,
                right,
                ..
            } if **operand_sort == sort(&Sort::simple("SortBool"))
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
            &pattern,
            kore::Pattern::Equals { right, .. }
                if matches!(right.as_ref(), kore::Pattern::Application { symbol, .. } if symbol.name == "condition")
        ));

        let condition = definition
            .internalize_term(
                &parse_pattern(r#"boolNot{}(intEq{}(X:SortInt{}, \dv{SortInt{}}("1")))"#).unwrap(),
                &[],
            )
            .unwrap();
        let logical = booster_rule_predicate_pattern_in_definition(
            &definition,
            &Predicate::Equals(truth, condition),
            &result_sort,
        );
        assert!(matches!(
            &logical,
            kore::Pattern::Not { argument, .. }
                if matches!(argument.as_ref(), kore::Pattern::Equals { left, right, .. }
                    if matches!(left.as_ref(), kore::Pattern::Variable(variable) if variable.name == "X")
                        && matches!(right.as_ref(), kore::Pattern::DomainValue { value, .. } if value == "1"))
        ));
    }

    #[test]
    fn rule_provenance_uses_the_declared_boolean_sort() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortTruth{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortBool{} [hasDomainValues{}()]
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-symbol intEqTruth{}(SortInt{}, SortInt{}) : SortTruth{}
                    [function{}(), total{}(), hook{}("INT.eq")]
                hooked-symbol opaqueEqLookalike{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("TEST.eq")]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let result_sort = Sort::simple("SortInt");
        let renamed_truth = Term::domain_value(Sort::simple("SortTruth"), "true");
        let renamed_condition = definition
            .internalize_term(
                &parse_pattern(r#"intEqTruth{}(X:SortInt{}, \dv{SortInt{}}("1"))"#).unwrap(),
                &[],
            )
            .unwrap();

        let renamed = booster_rule_predicate_pattern_in_definition(
            &definition,
            &Predicate::Equals(renamed_truth, renamed_condition),
            &result_sort,
        );
        assert!(matches!(
            &renamed,
            kore::Pattern::Equals { operand_sort, left, right, .. }
                if **operand_sort == sort(&Sort::simple("SortInt"))
                    && matches!(left.as_ref(), kore::Pattern::Variable(variable) if variable.name == "X")
                    && matches!(right.as_ref(), kore::Pattern::DomainValue { value, .. } if value == "1")
        ));
        definition.verify_standalone_pattern(&renamed).unwrap();

        let lookalike_truth = Term::domain_value(Sort::simple("SortBool"), "true");
        let lookalike_condition = definition
            .internalize_term(
                &parse_pattern(r#"opaqueEqLookalike{}(X:SortInt{}, \dv{SortInt{}}("1"))"#).unwrap(),
                &[],
            )
            .unwrap();
        let lookalike = booster_rule_predicate_pattern_in_definition(
            &definition,
            &Predicate::Equals(lookalike_truth, lookalike_condition),
            &result_sort,
        );
        assert!(matches!(
            &lookalike,
            kore::Pattern::Equals { operand_sort, left, right, .. }
                if **operand_sort == sort(&Sort::simple("SortBool"))
                    && matches!(left.as_ref(), kore::Pattern::DomainValue { value, .. } if value == "true")
                    && matches!(right.as_ref(), kore::Pattern::Application { symbol, .. }
                        if symbol.name == "opaqueEqLookalike")
        ));
        definition.verify_standalone_pattern(&lookalike).unwrap();
    }

    #[test]
    fn float_equality_stays_a_boolean_term_in_both_projection_directions() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort SortFloat{} [hook{}("FLOAT.Float"), hasDomainValues{}()]
                hooked-symbol floatEq{}(SortFloat{}, SortFloat{}) : SortBool{}
                    [function{}(), total{}(), hook{}("FLOAT.eq")]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let result_sort = Sort::simple("SortFloat");
        let float_sort = Sort::simple("SortFloat");
        let x = Term::variable(Variable::new("X", float_sort.clone()));
        let float_equality = definition
            .internalize_term(
                &parse_pattern("floatEq{}(X:SortFloat{}, X:SortFloat{})").unwrap(),
                &[],
            )
            .unwrap();
        let truth = Term::domain_value(Sort::simple("SortBool"), "true");

        let rule_predicate = booster_rule_predicate_pattern_in_definition(
            &definition,
            &Predicate::Equals(truth, float_equality),
            &result_sort,
        );
        assert!(matches!(
            &rule_predicate,
            kore::Pattern::Equals { operand_sort, right, .. }
                if **operand_sort == sort(&Sort::simple("SortBool"))
                    && matches!(right.as_ref(), kore::Pattern::Application { symbol, .. }
                        if symbol.name == "floatEq")
        ));
        definition
            .verify_standalone_pattern(&rule_predicate)
            .unwrap();

        let matching_equality =
            booster_predicate_pattern(&definition, &Predicate::Equals(x.clone(), x), &result_sort);
        assert!(matches!(
            &matching_equality,
            kore::Pattern::Equals { operand_sort, left, right, .. }
                if **operand_sort == sort(&float_sort)
                    && matches!(left.as_ref(), kore::Pattern::Variable(variable) if variable.name == "X")
                    && matches!(right.as_ref(), kore::Pattern::Variable(variable) if variable.name == "X")
        ));
        definition
            .verify_standalone_pattern(&matching_equality)
            .unwrap();
    }

    /// The balanced shape as it was built from a borrowed slice, cloning each operand: the
    /// oracle for the owned build in `connective`.
    fn balanced_from_slice(
        sort: &kore::Sort,
        patterns: &[kore::Pattern],
        and: bool,
    ) -> kore::Pattern {
        if let [pattern] = patterns {
            return pattern.clone();
        }
        let middle = patterns.len() / 2;
        let arguments = vec![
            balanced_from_slice(sort, &patterns[..middle], and),
            balanced_from_slice(sort, &patterns[middle..], and),
        ];
        if and {
            kore::Pattern::And {
                sort: sort.clone(),
                arguments,
            }
        } else {
            kore::Pattern::Or {
                sort: sort.clone(),
                arguments,
            }
        }
    }

    proptest::proptest! {
        /// `conjunction`/`disjunction` with `ConjunctionShape::Balanced` equal the tree the
        /// slice-based build returns (same split point `length / 2` at every node, operands in
        /// order), for 2 to 70 distinct operands, and return the single operand for one.
        #[test]
        fn balanced_owned_build_equals_slice_build(length in 1usize..=70, and in proptest::bool::ANY) {
            let result_sort = sort(&Sort::simple("SortS"));
            let operands = (0..length)
                .map(|index| kore::Pattern::DomainValue {
                    sort: result_sort.clone(),
                    value: index.to_string().into(),
                })
                .collect::<Vec<_>>();
            let expected = balanced_from_slice(&result_sort, &operands, and);
            let actual = if and {
                conjunction(&result_sort, operands, ConjunctionShape::Balanced)
            } else {
                disjunction(&result_sort, operands, ConjunctionShape::Balanced)
            };
            proptest::prop_assert_eq!(actual, Some(expected));
        }
    }
}

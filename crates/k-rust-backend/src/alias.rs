//! Validated expansion of KORE alias applications.

use std::collections::{BTreeMap, BTreeSet};

use k_rust_kore::kore::ast as kore;

use crate::definition::DefinitionError;

#[derive(Clone, Debug)]
pub(crate) struct AliasDefinition {
    sort_parameters: Vec<String>,
    parameters: Vec<kore::Variable>,
    right: kore::Pattern,
}

pub(crate) fn collect(
    modules: &[&kore::Module],
) -> Result<BTreeMap<String, AliasDefinition>, DefinitionError> {
    let mut aliases = BTreeMap::new();
    for module in modules {
        for sentence in &module.sentences {
            let kore::Sentence::AliasDeclaration {
                alias,
                argument_sorts,
                left,
                right,
                ..
            } = sentence
            else {
                continue;
            };
            let sort_parameters = alias
                .sort_parameters
                .iter()
                .map(|sort| match sort {
                    kore::Sort::Variable(name) => Ok(name.clone()),
                    kore::Sort::Application { .. } => Err(DefinitionError::InvalidSortParameter),
                })
                .collect::<Result<Vec<_>, _>>()?;
            if let Some(duplicate) = first_duplicate(sort_parameters.iter()) {
                return Err(DefinitionError::DuplicateParameter(duplicate.clone()));
            }
            let kore::Pattern::Application { symbol, arguments } = left.as_ref() else {
                return Err(DefinitionError::MalformedAlias(format!(
                    "alias {} must have an application on the left",
                    alias.name
                )));
            };
            if symbol.name != alias.name || symbol.sort_parameters != alias.sort_parameters {
                return Err(DefinitionError::MalformedAlias(format!(
                    "alias {} has a mismatched left-hand symbol",
                    alias.name
                )));
            }
            if arguments.len() != argument_sorts.len() {
                return Err(DefinitionError::WrongAliasArity {
                    alias: alias.name.clone(),
                    expected: argument_sorts.len(),
                    actual: arguments.len(),
                });
            }
            let parameters = arguments
                .iter()
                .zip(argument_sorts)
                .map(|(argument, expected_sort)| {
                    let kore::Pattern::Variable(variable) = argument else {
                        return Err(DefinitionError::MalformedAlias(format!(
                            "alias {} left-hand arguments must be variables",
                            alias.name
                        )));
                    };
                    if &variable.sort != expected_sort {
                        return Err(DefinitionError::MalformedAlias(format!(
                            "alias {} left-hand variable {} has the wrong sort",
                            alias.name, variable.name
                        )));
                    }
                    Ok(variable.clone())
                })
                .collect::<Result<Vec<_>, _>>()?;
            if let Some(duplicate) =
                first_duplicate(parameters.iter().map(|variable| &variable.name))
            {
                return Err(DefinitionError::DuplicateParameter(duplicate.clone()));
            }
            let definition = AliasDefinition {
                sort_parameters,
                parameters,
                right: (**right).clone(),
            };
            if aliases.insert(alias.name.clone(), definition).is_some() {
                return Err(DefinitionError::DuplicateAlias(alias.name.clone()));
            }
        }
    }
    validate_expansions(&aliases)?;
    Ok(aliases)
}

fn first_duplicate<'a>(values: impl IntoIterator<Item = &'a String>) -> Option<&'a String> {
    let mut seen = BTreeSet::new();
    values.into_iter().find(|value| !seen.insert(*value))
}

fn validate_expansions(aliases: &BTreeMap<String, AliasDefinition>) -> Result<(), DefinitionError> {
    for (name, alias) in aliases {
        let application = kore::Pattern::Application {
            symbol: kore::Symbol {
                name: name.clone(),
                sort_parameters: alias
                    .sort_parameters
                    .iter()
                    .cloned()
                    .map(kore::Sort::Variable)
                    .collect(),
            },
            arguments: alias
                .parameters
                .iter()
                .cloned()
                .map(kore::Pattern::Variable)
                .collect(),
        };
        expand(&application, aliases)?;
    }
    Ok(())
}

pub(crate) fn expand(
    pattern: &kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
) -> Result<kore::Pattern, DefinitionError> {
    expand_with(
        pattern,
        aliases,
        &BTreeMap::new(),
        &BTreeMap::new(),
        &mut Vec::new(),
    )
}

fn expand_with(
    pattern: &kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
    sorts: &BTreeMap<String, kore::Sort>,
    terms: &BTreeMap<kore::Variable, kore::Pattern>,
    stack: &mut Vec<String>,
) -> Result<kore::Pattern, DefinitionError> {
    use kore::Pattern;

    let recurse = |pattern: &Pattern, stack: &mut Vec<String>| {
        expand_with(pattern, aliases, sorts, terms, stack)
    };
    match pattern {
        Pattern::String(value) => Ok(Pattern::String(value.clone())),
        Pattern::Variable(variable) => Ok(terms
            .get(variable)
            .cloned()
            .unwrap_or_else(|| Pattern::Variable(substitute_variable(variable, sorts)))),
        Pattern::Application { symbol, arguments } => {
            let symbol = substitute_symbol(symbol, sorts);
            let arguments = arguments
                .iter()
                .map(|argument| recurse(argument, stack))
                .collect::<Result<Vec<_>, _>>()?;
            let Some(alias) = aliases.get(&symbol.name) else {
                return Ok(Pattern::Application { symbol, arguments });
            };
            if symbol.sort_parameters.len() != alias.sort_parameters.len() {
                return Err(DefinitionError::WrongAliasSortArgumentCount {
                    alias: symbol.name,
                    expected: alias.sort_parameters.len(),
                    actual: symbol.sort_parameters.len(),
                });
            }
            if arguments.len() != alias.parameters.len() {
                return Err(DefinitionError::WrongAliasArity {
                    alias: symbol.name,
                    expected: alias.parameters.len(),
                    actual: arguments.len(),
                });
            }
            if let Some(start) = stack.iter().position(|name| name == &symbol.name) {
                let mut cycle = stack[start..].to_vec();
                cycle.push(symbol.name);
                return Err(DefinitionError::AliasCycle(cycle));
            }
            let alias_sorts = alias
                .sort_parameters
                .iter()
                .cloned()
                .zip(symbol.sort_parameters)
                .collect::<BTreeMap<_, _>>();
            let alias_terms = alias
                .parameters
                .iter()
                .cloned()
                .zip(arguments)
                .collect::<BTreeMap<_, _>>();
            stack.push(symbol.name);
            let result = expand_with(&alias.right, aliases, &alias_sorts, &alias_terms, stack);
            stack.pop();
            result
        }
        Pattern::Top { sort } => Ok(Pattern::Top {
            sort: substitute_sort(sort, sorts),
        }),
        Pattern::Bottom { sort } => Ok(Pattern::Bottom {
            sort: substitute_sort(sort, sorts),
        }),
        Pattern::And { sort, arguments } => Ok(Pattern::And {
            sort: substitute_sort(sort, sorts),
            arguments: expand_many(arguments, aliases, sorts, terms, stack)?,
        }),
        Pattern::Or { sort, arguments } => Ok(Pattern::Or {
            sort: substitute_sort(sort, sorts),
            arguments: expand_many(arguments, aliases, sorts, terms, stack)?,
        }),
        Pattern::Not { sort, argument } => Ok(Pattern::Not {
            sort: substitute_sort(sort, sorts),
            argument: Box::new(recurse(argument, stack)?),
        }),
        Pattern::Next { sort, argument } => Ok(Pattern::Next {
            sort: substitute_sort(sort, sorts),
            argument: Box::new(recurse(argument, stack)?),
        }),
        Pattern::Implies { sort, left, right } => Ok(Pattern::Implies {
            sort: substitute_sort(sort, sorts),
            left: Box::new(recurse(left, stack)?),
            right: Box::new(recurse(right, stack)?),
        }),
        Pattern::Iff { sort, left, right } => Ok(Pattern::Iff {
            sort: substitute_sort(sort, sorts),
            left: Box::new(recurse(left, stack)?),
            right: Box::new(recurse(right, stack)?),
        }),
        Pattern::Rewrites { sort, left, right } => Ok(Pattern::Rewrites {
            sort: substitute_sort(sort, sorts),
            left: Box::new(recurse(left, stack)?),
            right: Box::new(recurse(right, stack)?),
        }),
        Pattern::Exists {
            sort,
            variable,
            body,
        } => expand_binder(
            BinderKind::Exists,
            Some(sort),
            variable,
            body,
            aliases,
            sorts,
            terms,
            stack,
        ),
        Pattern::Forall {
            sort,
            variable,
            body,
        } => expand_binder(
            BinderKind::Forall,
            Some(sort),
            variable,
            body,
            aliases,
            sorts,
            terms,
            stack,
        ),
        Pattern::Mu { variable, body } => expand_binder(
            BinderKind::Mu,
            None,
            variable,
            body,
            aliases,
            sorts,
            terms,
            stack,
        ),
        Pattern::Nu { variable, body } => expand_binder(
            BinderKind::Nu,
            None,
            variable,
            body,
            aliases,
            sorts,
            terms,
            stack,
        ),
        Pattern::Ceil {
            operand_sort,
            result_sort,
            argument,
        } => Ok(Pattern::Ceil {
            operand_sort: substitute_sort(operand_sort, sorts),
            result_sort: substitute_sort(result_sort, sorts),
            argument: Box::new(recurse(argument, stack)?),
        }),
        Pattern::Floor {
            operand_sort,
            result_sort,
            argument,
        } => Ok(Pattern::Floor {
            operand_sort: substitute_sort(operand_sort, sorts),
            result_sort: substitute_sort(result_sort, sorts),
            argument: Box::new(recurse(argument, stack)?),
        }),
        Pattern::Equals {
            operand_sort,
            result_sort,
            left,
            right,
        } => Ok(Pattern::Equals {
            operand_sort: substitute_sort(operand_sort, sorts),
            result_sort: substitute_sort(result_sort, sorts),
            left: Box::new(recurse(left, stack)?),
            right: Box::new(recurse(right, stack)?),
        }),
        Pattern::In {
            operand_sort,
            result_sort,
            left,
            right,
        } => Ok(Pattern::In {
            operand_sort: substitute_sort(operand_sort, sorts),
            result_sort: substitute_sort(result_sort, sorts),
            left: Box::new(recurse(left, stack)?),
            right: Box::new(recurse(right, stack)?),
        }),
        Pattern::DomainValue { sort, value } => Ok(Pattern::DomainValue {
            sort: substitute_sort(sort, sorts),
            value: value.clone(),
        }),
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => {
            if aliases.contains_key(&symbol.name) {
                let Some(application) = associative_application(*associativity, symbol, arguments)
                else {
                    return Ok(pattern.clone());
                };
                return recurse(&application, stack);
            }
            Ok(Pattern::AssociativeApplication {
                associativity: *associativity,
                symbol: substitute_symbol(symbol, sorts),
                arguments: expand_many(arguments, aliases, sorts, terms, stack)?,
            })
        }
    }
}

fn associative_application(
    associativity: kore::Associativity,
    symbol: &kore::Symbol,
    arguments: &[kore::Pattern],
) -> Option<kore::Pattern> {
    let application = |arguments| kore::Pattern::Application {
        symbol: symbol.clone(),
        arguments,
    };
    match associativity {
        kore::Associativity::Left => {
            let mut arguments = arguments.iter().cloned();
            let first = arguments.next()?;
            Some(arguments.fold(first, |left, right| application(vec![left, right])))
        }
        kore::Associativity::Right => {
            let (last, rest) = arguments.split_last()?;
            Some(
                rest.iter()
                    .rev()
                    .cloned()
                    .fold(last.clone(), |right, left| application(vec![left, right])),
            )
        }
    }
}

fn expand_many(
    patterns: &[kore::Pattern],
    aliases: &BTreeMap<String, AliasDefinition>,
    sorts: &BTreeMap<String, kore::Sort>,
    terms: &BTreeMap<kore::Variable, kore::Pattern>,
    stack: &mut Vec<String>,
) -> Result<Vec<kore::Pattern>, DefinitionError> {
    patterns
        .iter()
        .map(|pattern| expand_with(pattern, aliases, sorts, terms, stack))
        .collect()
}

#[derive(Clone, Copy)]
enum BinderKind {
    Exists,
    Forall,
    Mu,
    Nu,
}

#[allow(clippy::too_many_arguments)]
fn expand_binder(
    kind: BinderKind,
    sort: Option<&kore::Sort>,
    variable: &kore::Variable,
    body: &kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
    sorts: &BTreeMap<String, kore::Sort>,
    terms: &BTreeMap<kore::Variable, kore::Pattern>,
    stack: &mut Vec<String>,
) -> Result<kore::Pattern, DefinitionError> {
    let mut body_terms = terms.clone();
    body_terms.remove(variable);
    let substituted_variable = substitute_variable(variable, sorts);
    let body_free = free_variables(body);
    let (variable, body) = if body_terms.iter().any(|(parameter, replacement)| {
        body_free.contains(parameter) && free_variables(replacement).contains(&substituted_variable)
    }) {
        let fresh = fresh_variable(variable, body, &body_terms);
        let body = rename_bound_occurrences(body, variable, &fresh);
        (substitute_variable(&fresh, sorts), body)
    } else {
        (substituted_variable, body.clone())
    };
    let body = Box::new(expand_with(&body, aliases, sorts, &body_terms, stack)?);
    Ok(match kind {
        BinderKind::Exists => kore::Pattern::Exists {
            sort: substitute_sort(sort.expect("exists has a result sort"), sorts),
            variable,
            body,
        },
        BinderKind::Forall => kore::Pattern::Forall {
            sort: substitute_sort(sort.expect("forall has a result sort"), sorts),
            variable,
            body,
        },
        BinderKind::Mu => kore::Pattern::Mu { variable, body },
        BinderKind::Nu => kore::Pattern::Nu { variable, body },
    })
}

fn fresh_variable(
    variable: &kore::Variable,
    body: &kore::Pattern,
    terms: &BTreeMap<kore::Variable, kore::Pattern>,
) -> kore::Variable {
    let mut names = BTreeSet::new();
    collect_variable_names(body, &mut names);
    for (parameter, replacement) in terms {
        names.insert(parameter.name.clone());
        collect_variable_names(replacement, &mut names);
    }
    for index in 0usize.. {
        let name = format!("{}Alias{index}", variable.name);
        if names.insert(name.clone()) {
            return kore::Variable {
                kind: variable.kind,
                name,
                sort: variable.sort.clone(),
            };
        }
    }
    unreachable!("the set of finite variable names cannot exhaust every suffix")
}

fn collect_variable_names(pattern: &kore::Pattern, names: &mut BTreeSet<String>) {
    use kore::Pattern;

    match pattern {
        Pattern::Variable(variable) => {
            names.insert(variable.name.clone());
        }
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                collect_variable_names(argument, names);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => collect_variable_names(argument, names),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            collect_variable_names(left, names);
            collect_variable_names(right, names);
        }
        Pattern::Exists { variable, body, .. }
        | Pattern::Forall { variable, body, .. }
        | Pattern::Mu { variable, body }
        | Pattern::Nu { variable, body } => {
            names.insert(variable.name.clone());
            collect_variable_names(body, names);
        }
        Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

fn rename_bound_occurrences(
    pattern: &kore::Pattern,
    old: &kore::Variable,
    new: &kore::Variable,
) -> kore::Pattern {
    use kore::Pattern;

    let recurse = |pattern: &Pattern| rename_bound_occurrences(pattern, old, new);
    match pattern {
        Pattern::String(value) => Pattern::String(value.clone()),
        Pattern::Variable(variable) => Pattern::Variable(if variable == old {
            new.clone()
        } else {
            variable.clone()
        }),
        Pattern::Application { symbol, arguments } => Pattern::Application {
            symbol: symbol.clone(),
            arguments: arguments.iter().map(recurse).collect(),
        },
        Pattern::Top { sort } => Pattern::Top { sort: sort.clone() },
        Pattern::Bottom { sort } => Pattern::Bottom { sort: sort.clone() },
        Pattern::And { sort, arguments } => Pattern::And {
            sort: sort.clone(),
            arguments: arguments.iter().map(recurse).collect(),
        },
        Pattern::Or { sort, arguments } => Pattern::Or {
            sort: sort.clone(),
            arguments: arguments.iter().map(recurse).collect(),
        },
        Pattern::Not { sort, argument } => Pattern::Not {
            sort: sort.clone(),
            argument: Box::new(recurse(argument)),
        },
        Pattern::Next { sort, argument } => Pattern::Next {
            sort: sort.clone(),
            argument: Box::new(recurse(argument)),
        },
        Pattern::Implies { sort, left, right } => Pattern::Implies {
            sort: sort.clone(),
            left: Box::new(recurse(left)),
            right: Box::new(recurse(right)),
        },
        Pattern::Iff { sort, left, right } => Pattern::Iff {
            sort: sort.clone(),
            left: Box::new(recurse(left)),
            right: Box::new(recurse(right)),
        },
        Pattern::Rewrites { sort, left, right } => Pattern::Rewrites {
            sort: sort.clone(),
            left: Box::new(recurse(left)),
            right: Box::new(recurse(right)),
        },
        Pattern::Exists {
            sort,
            variable,
            body,
        } => Pattern::Exists {
            sort: sort.clone(),
            variable: variable.clone(),
            body: if variable == old {
                body.clone()
            } else {
                Box::new(recurse(body))
            },
        },
        Pattern::Forall {
            sort,
            variable,
            body,
        } => Pattern::Forall {
            sort: sort.clone(),
            variable: variable.clone(),
            body: if variable == old {
                body.clone()
            } else {
                Box::new(recurse(body))
            },
        },
        Pattern::Mu { variable, body } => Pattern::Mu {
            variable: variable.clone(),
            body: if variable == old {
                body.clone()
            } else {
                Box::new(recurse(body))
            },
        },
        Pattern::Nu { variable, body } => Pattern::Nu {
            variable: variable.clone(),
            body: if variable == old {
                body.clone()
            } else {
                Box::new(recurse(body))
            },
        },
        Pattern::Ceil {
            operand_sort,
            result_sort,
            argument,
        } => Pattern::Ceil {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: Box::new(recurse(argument)),
        },
        Pattern::Floor {
            operand_sort,
            result_sort,
            argument,
        } => Pattern::Floor {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: Box::new(recurse(argument)),
        },
        Pattern::Equals {
            operand_sort,
            result_sort,
            left,
            right,
        } => Pattern::Equals {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: Box::new(recurse(left)),
            right: Box::new(recurse(right)),
        },
        Pattern::In {
            operand_sort,
            result_sort,
            left,
            right,
        } => Pattern::In {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: Box::new(recurse(left)),
            right: Box::new(recurse(right)),
        },
        Pattern::DomainValue { sort, value } => Pattern::DomainValue {
            sort: sort.clone(),
            value: value.clone(),
        },
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => Pattern::AssociativeApplication {
            associativity: *associativity,
            symbol: symbol.clone(),
            arguments: arguments.iter().map(recurse).collect(),
        },
    }
}

fn free_variables(pattern: &kore::Pattern) -> BTreeSet<kore::Variable> {
    use kore::Pattern;

    match pattern {
        Pattern::Variable(variable) => BTreeSet::from([variable.clone()]),
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            arguments.iter().flat_map(free_variables).collect()
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => free_variables(argument),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => free_variables(left)
            .into_iter()
            .chain(free_variables(right))
            .collect(),
        Pattern::Exists { variable, body, .. }
        | Pattern::Forall { variable, body, .. }
        | Pattern::Mu { variable, body }
        | Pattern::Nu { variable, body } => {
            let mut variables = free_variables(body);
            variables.remove(variable);
            variables
        }
        Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => BTreeSet::new(),
    }
}

fn substitute_symbol(symbol: &kore::Symbol, sorts: &BTreeMap<String, kore::Sort>) -> kore::Symbol {
    kore::Symbol {
        name: symbol.name.clone(),
        sort_parameters: symbol
            .sort_parameters
            .iter()
            .map(|sort| substitute_sort(sort, sorts))
            .collect(),
    }
}

fn substitute_variable(
    variable: &kore::Variable,
    sorts: &BTreeMap<String, kore::Sort>,
) -> kore::Variable {
    kore::Variable {
        kind: variable.kind,
        name: variable.name.clone(),
        sort: substitute_sort(&variable.sort, sorts),
    }
}

fn substitute_sort(sort: &kore::Sort, sorts: &BTreeMap<String, kore::Sort>) -> kore::Sort {
    match sort {
        kore::Sort::Variable(name) => sorts.get(name).cloned().unwrap_or_else(|| sort.clone()),
        kore::Sort::Application { name, arguments } => kore::Sort::Application {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_sort(argument, sorts))
                .collect(),
        },
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;

    #[test]
    fn alpha_renames_alias_binders_to_avoid_capture() {
        let definition = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                alias bind{}(SortValue{}) : SortValue{}
                    where bind{}(X:SortValue{}) := \exists{SortValue{}}(
                        Y:SortValue{},
                        \and{SortValue{}}(X:SortValue{}, Y:SortValue{})
                    ) []
            endmodule []
        "#})
        .expect("alias definition should parse");
        let modules = definition.modules.iter().collect::<Vec<_>>();
        let aliases = collect(&modules).expect("alias definition should validate");
        let application = parse_pattern(indoc! {r#"
            bind{}(
                \and{SortValue{}}(Y:SortValue{}, YAlias0:SortValue{})
            )
        "#})
        .expect("alias application should parse");
        let expected = parse_pattern(indoc! {r#"
            \exists{SortValue{}}(
                YAlias1:SortValue{},
                \and{SortValue{}}(
                    \and{SortValue{}}(Y:SortValue{}, YAlias0:SortValue{}),
                    YAlias1:SortValue{}
                )
            )
        "#})
        .expect("expected expansion should parse");

        assert_eq!(expand(&application, &aliases).unwrap(), expected);
    }

    #[test]
    fn alpha_renaming_respects_nested_shadowing() {
        let definition = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                alias bind{}(SortValue{}) : SortValue{}
                    where bind{}(X:SortValue{}) := \exists{SortValue{}}(
                        Y:SortValue{},
                        \and{SortValue{}}(
                            X:SortValue{},
                            \exists{SortValue{}}(Y:SortValue{}, Y:SortValue{})
                        )
                    ) []
            endmodule []
        "#})
        .expect("alias definition should parse");
        let modules = definition.modules.iter().collect::<Vec<_>>();
        let aliases = collect(&modules).expect("alias definition should validate");
        let application =
            parse_pattern("bind{}(Y:SortValue{})").expect("alias application should parse");
        let expected = parse_pattern(indoc! {r#"
            \exists{SortValue{}}(
                YAlias0:SortValue{},
                \and{SortValue{}}(
                    Y:SortValue{},
                    \exists{SortValue{}}(Y:SortValue{}, Y:SortValue{})
                )
            )
        "#})
        .expect("expected expansion should parse");

        assert_eq!(expand(&application, &aliases).unwrap(), expected);
    }

    #[test]
    fn expands_aliases_through_associative_wrappers() {
        let definition = parse_definition(indoc! {r#"
            []
            module MAIN
                sort S{} []
                symbol f{}(S{}, S{}) : S{} []
                symbol a{}() : S{} []
                symbol b{}() : S{} []
                symbol c{}() : S{} []
                alias pair{}(S{}, S{}) : S{}
                    where pair{}(X:S{}, Y:S{}) := f{}(X:S{}, Y:S{}) []
            endmodule []
        "#})
        .expect("alias definition should parse");
        let modules = definition.modules.iter().collect::<Vec<_>>();
        let aliases = collect(&modules).expect("alias definition should validate");
        let left = parse_pattern(r"\left-assoc{}(pair{}(a{}(), b{}(), c{}()))")
            .expect("left-associative alias application should parse");
        let right = parse_pattern(r"\right-assoc{}(pair{}(a{}(), b{}(), c{}()))")
            .expect("right-associative alias application should parse");

        assert_eq!(
            expand(&left, &aliases).unwrap(),
            parse_pattern("f{}(f{}(a{}(), b{}()), c{}())").unwrap()
        );
        assert_eq!(
            expand(&right, &aliases).unwrap(),
            parse_pattern("f{}(a{}(), f{}(b{}(), c{}()))").unwrap()
        );
    }
}

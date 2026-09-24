//! ```toml algorithm
//! id = "kompile.kore.axioms"
//! name = "generated KORE axiom emission"
//! sites = ["generated_axioms", "constructor_productions"]
//! variable = "P = productions; S = sorts; O = overloads; R = rules"
//! counters = []
//! no_counter = "generated-axiom emission has no dedicated counter"
//!
//! [[cost]]
//! mode = "one module"
//! bound = "O(P^2 + S x (P + S log S) + O^2 + R)"
//! ```
//!
//! Generated KORE syntax and semantic axiom families.
//! Complexity: O(P² + S(P + S log S) + O²) over productions, sorts, and overloads; no dedicated counter.

use super::equations::substitute_equation_sort;
use super::*;

pub(super) struct GeneratedAxioms {
    pub(super) semantics: Vec<KoreSentence>,
    pub(super) syntax: Vec<KoreSentence>,
}

pub(super) fn generated_axioms(
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
    overloads: &OverloadOrder<'_>,
    subsorts: &PartialOrder<Sort>,
    constructors: &BTreeSet<ProductionId>,
) -> Result<GeneratedAxioms, ModuleToKoreError> {
    let mut semantics = Vec::new();
    let mut syntax = Vec::new();
    let mut no_confusion_pairs = BTreeSet::new();
    for (id, production) in productions.productions() {
        if let Some(axiom) = subsort_axiom(production) {
            semantics.push(axiom.clone());
            syntax.push(axiom);
            continue;
        }
        if is_builtin_production(production) || is_bracket_production(production) {
            continue;
        }
        semantics.extend(algebraic_axioms(id, production, subsorts)?);
        if let Some(axiom) = functional_axiom(production) {
            semantics.push(axiom);
        }
        if constructors.contains(&id) {
            semantics.extend(no_confusion_axioms(
                id,
                productions,
                constructors,
                &mut no_confusion_pairs,
            ));
        }
    }
    semantics.extend(no_junk_axioms(productions, sorts, subsorts));

    for (lesser, _) in overloads.catalog().productions() {
        let Some(greater_productions) = overloads.order().relations_from(&lesser) else {
            continue;
        };
        // Invariant: `semantics` and `syntax` hold one overload axiom for every production before `greater` in catalog order that `greater_productions` contains; this scan of `overloads.catalog().productions()` runs once per `lesser`, O(n^2) in the catalog size.
        for (greater, _) in overloads.catalog().productions() {
            if greater_productions.contains(&greater) {
                let axiom = overload_axiom(overloads, lesser, greater)?;
                semantics.push(axiom.clone());
                syntax.push(axiom);
            }
        }
    }
    Ok(GeneratedAxioms { semantics, syntax })
}

pub(super) fn constructor_productions(
    productions: &ProductionCatalog<'_>,
    _overloads: &OverloadOrder<'_>,
    rules: &crate::definition::RuleCatalog<'_>,
) -> BTreeSet<ProductionId> {
    let anywhere_labels = rules
        .rules()
        .filter(|(_, rule)| rule.attributes().has(AttributeKey::Anywhere))
        .map(|(_, rule)| match_rule_label(rule))
        .collect::<BTreeSet<_>>();
    productions
        .productions()
        .filter_map(|(id, production)| {
            let Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } = production
            else {
                return None;
            };
            if is_bracket_production(production) {
                return None;
            }
            let algebraic =
                attributes.has_any(&[AttributeKey::Assoc, AttributeKey::Comm, AttributeKey::Idem]);
            let is_macro = attributes.has_any(&AttributeKey::MACRO_LIKE);
            (!attributes.has(AttributeKey::Function)
                && !algebraic
                && !is_macro
                && !anywhere_labels.contains(label)
                && !is_builtin_label(&label.name)
                && !is_token_production(attributes))
            .then_some(id)
        })
        .collect()
}

fn no_confusion_axioms(
    id: ProductionId,
    productions: &ProductionCatalog<'_>,
    constructors: &BTreeSet<ProductionId>,
    emitted_pairs: &mut BTreeSet<(ProductionId, ProductionId)>,
) -> Vec<KoreSentence> {
    let production = productions.production(id);
    let Some(current) = generated_production(production) else {
        return Vec::new();
    };
    let mut axioms = Vec::new();
    if !current.arguments.is_empty() {
        let left = generated_application(&current, "X");
        let right = generated_application(&current, "Y");
        let merged = Pattern::Application {
            symbol: current.symbol.clone(),
            arguments: current
                .arguments
                .iter()
                .enumerate()
                .map(|(index, sort)| Pattern::And {
                    sort: sort.clone(),
                    arguments: vec![
                        generated_variable("X", index, sort),
                        generated_variable("Y", index, sort),
                    ],
                })
                .collect(),
        };
        axioms.push(KoreSentence::Axiom {
            parameters: current.parameters.clone(),
            pattern: Box::new(Pattern::Implies {
                sort: current.result.clone(),
                left: Box::new(Pattern::And {
                    sort: current.result.clone(),
                    arguments: vec![left, right],
                }),
                right: Box::new(merged),
            }),
            attributes: marker_attribute(KoreAttribute::Constructor),
        });
    }

    let result_head = match production {
        Sentence::Production { sort, .. } => SortHead::from(sort),
        _ => unreachable!("production catalogs contain productions"),
    };
    // Invariant: `emitted_pairs` holds both orderings of every constructor pair that already has a no-confusion axiom, so each unordered pair is emitted once; this scan of `productions.productions()` runs once per constructor `id`, O(n^2) in the catalog size.
    for (other_id, other_production) in productions.productions() {
        if other_id == id
            || !constructors.contains(&other_id)
            || emitted_pairs.contains(&(id, other_id))
        {
            continue;
        }
        let Sentence::Production {
            sort: other_sort, ..
        } = other_production
        else {
            unreachable!("production catalogs contain productions")
        };
        if SortHead::from(other_sort) != result_head {
            continue;
        }
        let Some(other) = generated_production(other_production) else {
            continue;
        };
        emitted_pairs.insert((id, other_id));
        emitted_pairs.insert((other_id, id));
        axioms.push(KoreSentence::Axiom {
            parameters: current.parameters.clone(),
            pattern: Box::new(Pattern::Not {
                sort: current.result.clone(),
                argument: Box::new(Pattern::And {
                    sort: current.result.clone(),
                    arguments: vec![
                        generated_application(&current, "X"),
                        generated_application(&other, "Y"),
                    ],
                }),
            }),
            attributes: marker_attribute(KoreAttribute::Constructor),
        });
    }
    axioms
}

struct GeneratedProduction {
    parameters: Vec<String>,
    symbol: Symbol,
    arguments: Vec<KoreSort>,
    result: KoreSort,
}

fn generated_production(production: &Sentence) -> Option<GeneratedProduction> {
    let Sentence::Production {
        label: Some(label),
        parameters,
        sort,
        items,
        ..
    } = production
    else {
        return None;
    };
    Some(GeneratedProduction {
        parameters: generated_sort_parameters(parameters),
        symbol: encode_kore_label_with_formals(label, parameters),
        arguments: items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => {
                    Some(encode_kore_sort_with_formals(sort, parameters))
                }
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect(),
        result: encode_kore_sort_with_formals(sort, parameters),
    })
}

fn generated_application(production: &GeneratedProduction, prefix: &str) -> Pattern {
    Pattern::Application {
        symbol: production.symbol.clone(),
        arguments: production
            .arguments
            .iter()
            .enumerate()
            .map(|(index, sort)| generated_variable(prefix, index, sort))
            .collect(),
    }
}

fn generated_variable(prefix: &str, index: usize, sort: &KoreSort) -> Pattern {
    Pattern::Variable(Variable {
        kind: VariableKind::Element,
        name: format!("{prefix}{index}"),
        sort: sort.clone(),
    })
}

fn no_junk_axioms(
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
    subsorts: &PartialOrder<Sort>,
) -> Vec<KoreSentence> {
    let mut axioms = Vec::new();
    for sort in sorts.sorted_all_sorts() {
        let result_sort = encode_kore_sort(sort);
        let result_head = SortHead::from(sort);
        let mut alternatives = Vec::new();
        let mut variable_names = BTreeMap::new();
        let mut used_variable_names = BTreeSet::new();
        let mut variable_suffixes = BTreeMap::new();
        let mut has_token = false;
        // Invariant: `alternatives` holds one pattern for every admitted labelled non-token production of `result_head` before this one, plus exactly one top pattern if any token production precedes it, as tracked by `has_token`; this scan of `productions.productions()` runs once per sort, O(|sorts| * |productions|).
        for (_, production) in productions.productions() {
            let Sentence::Production {
                label,
                sort: production_sort,
                attributes,
                ..
            } = production
            else {
                unreachable!("production catalogs contain productions")
            };
            if SortHead::from(production_sort) != result_head
                || attributes.has(AttributeKey::Function)
                || is_subsort_production(production)
                || is_builtin_production(production)
                || is_macro_production(production)
                || is_bracket_production(production)
            {
                continue;
            }
            if attributes.has(AttributeKey::Token) {
                // A token production parses to domain values of its sort, which no symbol
                // generates, so `\top` is its complete alternative; its symbol is never a
                // generator, whatever its label or its position among the sort's productions.
                if !has_token {
                    alternatives.push(Pattern::Top {
                        sort: result_sort.clone(),
                    });
                    has_token = true;
                }
            } else if label.is_some()
                && let Some(production) = generated_production_for_sort(production, sort)
            {
                let variables = production
                    .arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument_sort)| {
                        consistent_generated_variable(
                            &format!("X{index}"),
                            argument_sort,
                            &mut variable_names,
                            &mut used_variable_names,
                            &mut variable_suffixes,
                        )
                    })
                    .collect::<Vec<_>>();
                let mut alternative = Pattern::Application {
                    symbol: production.symbol,
                    arguments: variables.iter().cloned().map(Pattern::Variable).collect(),
                };
                for variable in variables.into_iter().rev() {
                    alternative = Pattern::Exists {
                        sort: result_sort.clone(),
                        variable,
                        body: Box::new(alternative),
                    };
                }
                alternatives.push(alternative);
            }
        }
        if sort.name != BuiltinSort::K.k_name() {
            // Invariant: `alternatives` has gained one injection alternative for every strict subsort of `sort` before `subsort`; this scan of `sorts.sorted_all_sorts()` runs once per sort of the same list, O(|sorts|^2).
            for subsort in sorts
                .sorted_all_sorts()
                .filter(|subsort| subsorts.less_than(subsort, sort))
            {
                let subsort = encode_kore_sort(subsort);
                let variable = consistent_generated_variable(
                    "Val",
                    &subsort,
                    &mut variable_names,
                    &mut used_variable_names,
                    &mut variable_suffixes,
                );
                alternatives.push(Pattern::Exists {
                    sort: result_sort.clone(),
                    variable: variable.clone(),
                    body: Box::new(Pattern::Application {
                        symbol: Symbol {
                            name: WellKnownSymbol::Inj.as_str().into(),
                            sort_parameters: vec![subsort, result_sort.clone()],
                        },
                        arguments: vec![Pattern::Variable(variable)],
                    }),
                });
            }
        }
        if !has_token
            && sorts
                .attributes_for(&result_head)
                .is_some_and(|attributes| attributes.has(AttributeKey::Token))
        {
            alternatives.push(Pattern::Top {
                sort: result_sort.clone(),
            });
        }
        if alternatives.is_empty() {
            continue;
        }
        alternatives.push(Pattern::Bottom {
            sort: result_sort.clone(),
        });
        let pattern = Pattern::Or {
            sort: result_sort.clone(),
            arguments: alternatives,
        };
        axioms.push(KoreSentence::Axiom {
            parameters: Vec::new(),
            pattern: Box::new(pattern),
            attributes: marker_attribute(KoreAttribute::Constructor),
        });
    }
    axioms
}

fn consistent_generated_variable(
    base: &str,
    sort: &KoreSort,
    assigned: &mut BTreeMap<(String, KoreSort), String>,
    used: &mut BTreeSet<String>,
    suffixes: &mut BTreeMap<String, usize>,
) -> Variable {
    let key = (base.to_owned(), sort.clone());
    let name = assigned.get(&key).cloned().unwrap_or_else(|| {
        let name = if used.insert(base.to_owned()) {
            base.to_owned()
        } else {
            let suffix = suffixes.entry(base.to_owned()).or_insert(2);
            // Invariant: every `{base}V{n}` with `n` below `suffix` is already in `used`; each iteration increments `suffix`, and `used` is finite, so an unused candidate is reached.
            loop {
                let candidate = format!("{base}V{suffix}");
                *suffix += 1;
                if used.insert(candidate.clone()) {
                    break candidate;
                }
            }
        };
        assigned.insert(key, name.clone());
        name
    });
    Variable {
        kind: VariableKind::Element,
        name,
        sort: sort.clone(),
    }
}

fn generated_production_for_sort(
    production: &Sentence,
    target: &Sort,
) -> Option<GeneratedProduction> {
    let Sentence::Production {
        label: Some(label),
        parameters,
        sort,
        items,
        ..
    } = production
    else {
        return None;
    };
    let mut substitution = BTreeMap::new();
    match_sort_parameters(sort, target, parameters, &mut substitution)?;
    let concrete_label = Label::with_parameters(
        &label.name,
        label
            .parameters
            .iter()
            .map(|sort| substitute_equation_sort(sort, &substitution))
            .collect(),
    );
    Some(GeneratedProduction {
        parameters: Vec::new(),
        symbol: encode_kore_label(&concrete_label),
        arguments: items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(encode_kore_sort(
                    &substitute_equation_sort(sort, &substitution),
                )),
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect(),
        result: encode_kore_sort(target),
    })
}

// Invariant: each call matches one node of `pattern` against `concrete` and recurses only into their `parameters`, so the finite `pattern` bounds the calls; `substitution` binds every element of `parameters` met so far to one concrete sort.
fn match_sort_parameters(
    pattern: &Sort,
    concrete: &Sort,
    parameters: &[Sort],
    substitution: &mut BTreeMap<Sort, Sort>,
) -> Option<()> {
    if parameters.contains(pattern) {
        return match substitution.get(pattern) {
            Some(existing) if existing != concrete => None,
            Some(_) => Some(()),
            None => {
                substitution.insert(pattern.clone(), concrete.clone());
                Some(())
            }
        };
    }
    if pattern.name != concrete.name || pattern.parameters.len() != concrete.parameters.len() {
        return None;
    }
    for (pattern, concrete) in pattern.parameters.iter().zip(&concrete.parameters) {
        match_sort_parameters(pattern, concrete, parameters, substitution)?;
    }
    Some(())
}

fn is_subsort_production(production: &Sentence) -> bool {
    matches!(
        production,
        Sentence::Production { label: None, items, .. }
            if matches!(items.as_slice(), [ProductionItem::NonTerminal { .. }])
    )
}

fn is_macro_production(production: &Sentence) -> bool {
    production.attributes().has_any(&AttributeKey::MACRO_LIKE)
}

fn functional_axiom(production: &Sentence) -> Option<KoreSentence> {
    let Sentence::Production {
        label: Some(label),
        parameters,
        sort,
        items,
        attributes,
    } = production
    else {
        return None;
    };
    if attributes.has(AttributeKey::Function) && !attributes.has(AttributeKey::Total) {
        return None;
    }
    let result_sort = encode_kore_sort_with_formals(sort, parameters);
    let arguments = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => {
                Some(encode_kore_sort_with_formals(sort, parameters))
            }
            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
        })
        .enumerate()
        .map(|(index, sort)| {
            Pattern::Variable(Variable {
                kind: VariableKind::Element,
                name: format!("K{index}"),
                sort,
            })
        })
        .collect();
    let value = Variable {
        kind: VariableKind::Element,
        name: "Val".into(),
        sort: result_sort.clone(),
    };
    Some(KoreSentence::Axiom {
        parameters: generated_axiom_parameters(parameters),
        pattern: Box::new(Pattern::Exists {
            sort: KoreSort::Variable("R".into()),
            variable: value.clone(),
            body: Box::new(Pattern::Equals {
                operand_sort: result_sort,
                result_sort: KoreSort::Variable("R".into()),
                left: Box::new(Pattern::Variable(value)),
                right: Box::new(Pattern::Application {
                    symbol: encode_kore_label_with_formals(label, parameters),
                    arguments,
                }),
            }),
        }),
        attributes: marker_attribute(KoreAttribute::Functional),
    })
}

fn is_builtin_production(production: &Sentence) -> bool {
    matches!(
        production,
        Sentence::Production { label: Some(label), .. } if is_builtin_label(&label.name)
    )
}

fn algebraic_axioms(
    id: ProductionId,
    production: &Sentence,
    subsorts: &PartialOrder<Sort>,
) -> Result<Vec<KoreSentence>, ModuleToKoreError> {
    let Sentence::Production {
        label,
        parameters,
        sort,
        items,
        attributes,
    } = production
    else {
        unreachable!("production catalogs contain productions")
    };
    let assoc = attributes.has(AttributeKey::Assoc);
    let idem = attributes.has(AttributeKey::Idem);
    let unit = attributes
        .string(AttributeKey::Unit)
        .filter(|_| attributes.has(AttributeKey::Function));
    if !assoc && !idem && unit.is_none() {
        return Ok(Vec::new());
    }
    let Some(label) = label else {
        return Err(invalid_algebraic(
            id,
            if assoc {
                "assoc"
            } else if idem {
                "idem"
            } else {
                "unit"
            },
            "the production has no symbol label",
        ));
    };
    let arguments = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort),
            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
        })
        .collect::<Vec<_>>();
    let symbol = encode_kore_label_with_formals(label, parameters);
    let result_sort = encode_kore_sort_with_formals(sort, parameters);
    let axiom_parameters = generated_axiom_parameters(parameters);
    let mut axioms = Vec::new();

    if assoc {
        if arguments.len() != 2 {
            return Err(invalid_algebraic(
                id,
                "assoc",
                format!("expected arity 2, found {}", arguments.len()),
            ));
        }
        if !arguments
            .iter()
            .all(|argument| subsorts.less_than_eq(sort, argument))
        {
            return Err(invalid_algebraic(
                id,
                "assoc",
                "the result sort must be a subsort of both argument sorts",
            ));
        }
        let variables = ["K1", "K2", "K3"].map(|name| Variable {
            kind: VariableKind::Element,
            name: name.into(),
            sort: result_sort.clone(),
        });
        let apply = |arguments| Pattern::Application {
            symbol: symbol.clone(),
            arguments,
        };
        axioms.push(KoreSentence::Axiom {
            parameters: axiom_parameters.clone(),
            pattern: Box::new(Pattern::Equals {
                operand_sort: result_sort.clone(),
                result_sort: KoreSort::Variable("R".into()),
                left: Box::new(apply(vec![
                    apply(vec![
                        Pattern::Variable(variables[0].clone()),
                        Pattern::Variable(variables[1].clone()),
                    ]),
                    Pattern::Variable(variables[2].clone()),
                ])),
                right: Box::new(apply(vec![
                    Pattern::Variable(variables[0].clone()),
                    apply(vec![
                        Pattern::Variable(variables[1].clone()),
                        Pattern::Variable(variables[2].clone()),
                    ]),
                ])),
            }),
            attributes: marker_attribute(KoreAttribute::Assoc),
        });
    }

    if idem {
        if arguments.len() != 2 {
            return Err(invalid_algebraic(
                id,
                "idem",
                format!("expected arity 2, found {}", arguments.len()),
            ));
        }
        if arguments.iter().any(|argument| *argument != sort) {
            return Err(invalid_algebraic(
                id,
                "idem",
                "the result and both argument sorts must be equal",
            ));
        }
        let variable = Variable {
            kind: VariableKind::Element,
            name: "K".into(),
            sort: result_sort.clone(),
        };
        axioms.push(KoreSentence::Axiom {
            parameters: axiom_parameters.clone(),
            pattern: Box::new(Pattern::Equals {
                operand_sort: result_sort.clone(),
                result_sort: KoreSort::Variable("R".into()),
                left: Box::new(Pattern::Application {
                    symbol: symbol.clone(),
                    arguments: vec![
                        Pattern::Variable(variable.clone()),
                        Pattern::Variable(variable.clone()),
                    ],
                }),
                right: Box::new(Pattern::Variable(variable)),
            }),
            attributes: marker_attribute(KoreAttribute::Idem),
        });
    }

    if let Some(unit) = unit {
        if arguments.len() != 2 {
            return Err(invalid_algebraic(
                id,
                "unit",
                format!("expected arity 2, found {}", arguments.len()),
            ));
        }
        if arguments.iter().any(|argument| *argument != sort) {
            return Err(invalid_algebraic(
                id,
                "unit",
                "the result and both argument sorts must be equal",
            ));
        }
        let variable = Variable {
            kind: VariableKind::Element,
            name: "K".into(),
            sort: result_sort.clone(),
        };
        let unit = Pattern::Application {
            symbol: encode_kore_label(&Label::new(unit)),
            arguments: Vec::new(),
        };
        for arguments in [
            vec![Pattern::Variable(variable.clone()), unit.clone()],
            vec![unit, Pattern::Variable(variable.clone())],
        ] {
            axioms.push(KoreSentence::Axiom {
                parameters: axiom_parameters.clone(),
                pattern: Box::new(Pattern::Equals {
                    operand_sort: result_sort.clone(),
                    result_sort: KoreSort::Variable("R".into()),
                    left: Box::new(Pattern::Application {
                        symbol: symbol.clone(),
                        arguments,
                    }),
                    right: Box::new(Pattern::Variable(variable.clone())),
                }),
                attributes: marker_attribute(KoreAttribute::Unit),
            });
        }
    }

    Ok(axioms)
}

fn invalid_algebraic(
    production: ProductionId,
    attribute: &'static str,
    message: impl Into<String>,
) -> ModuleToKoreError {
    ModuleToKoreError::InvalidAlgebraicProduction {
        production: production.0,
        attribute,
        message: message.into(),
    }
}

fn generated_axiom_parameters(parameters: &[Sort]) -> Vec<String> {
    let mut names = vec!["R".into()];
    names.extend(generated_sort_parameters(parameters));
    names
}

fn generated_sort_parameters(parameters: &[Sort]) -> Vec<String> {
    parameters
        .iter()
        .map(|parameter| {
            let KoreSort::Variable(name) = encode_kore_sort_with_formals(parameter, parameters)
            else {
                unreachable!("production parameters encode as KORE sort variables")
            };
            name
        })
        .collect()
}

fn marker_attribute(attribute: KoreAttribute) -> Attributes {
    Attributes(vec![Pattern::Application {
        symbol: Symbol {
            name: attribute.as_str().into(),
            sort_parameters: Vec::new(),
        },
        arguments: Vec::new(),
    }])
}

fn subsort_axiom(production: &Sentence) -> Option<KoreSentence> {
    let Sentence::Production {
        label: None,
        parameters,
        sort,
        items,
        ..
    } = production
    else {
        return None;
    };
    let [ProductionItem::NonTerminal { sort: subsort, .. }] = items.as_slice() else {
        return None;
    };
    if sort.name == BuiltinSort::K.k_name() {
        return None;
    }

    let subsort = encode_kore_sort_with_formals(subsort, parameters);
    let sort = encode_kore_sort_with_formals(sort, parameters);
    let value = Variable {
        kind: VariableKind::Element,
        name: "Val".into(),
        sort: sort.clone(),
    };
    let from = Variable {
        kind: VariableKind::Element,
        name: "From".into(),
        sort: subsort.clone(),
    };
    let injection = Pattern::Application {
        symbol: Symbol {
            name: WellKnownSymbol::Inj.as_str().into(),
            sort_parameters: vec![subsort.clone(), sort.clone()],
        },
        arguments: vec![Pattern::Variable(from)],
    };
    Some(KoreSentence::Axiom {
        parameters: vec!["R".into()],
        pattern: Box::new(Pattern::Exists {
            sort: KoreSort::Variable("R".into()),
            variable: value.clone(),
            body: Box::new(Pattern::Equals {
                operand_sort: sort.clone(),
                result_sort: KoreSort::Variable("R".into()),
                left: Box::new(Pattern::Variable(value)),
                right: Box::new(injection),
            }),
        }),
        attributes: Attributes(vec![Pattern::Application {
            symbol: Symbol {
                name: KoreAttribute::Subsort.as_str().into(),
                sort_parameters: vec![subsort, sort],
            },
            arguments: Vec::new(),
        }]),
    })
}

fn overload_axiom(
    overloads: &OverloadOrder<'_>,
    lesser_id: ProductionId,
    greater_id: ProductionId,
) -> Result<KoreSentence, ModuleToKoreError> {
    let lesser = overload_production(overloads, lesser_id)?;
    let greater = overload_production(overloads, greater_id)?;
    if lesser.arguments.len() != greater.arguments.len() {
        return Err(ModuleToKoreError::InvalidOverloadProduction {
            production: lesser_id.0,
            message: format!(
                "its arity {} does not match production #{} with arity {}",
                lesser.arguments.len(),
                greater_id.0,
                greater.arguments.len()
            ),
        });
    }

    let variables = lesser
        .arguments
        .iter()
        .enumerate()
        .map(|(index, sort)| Variable {
            kind: VariableKind::Element,
            name: format!("K{index}"),
            sort: sort.clone(),
        })
        .collect::<Vec<_>>();
    let greater_arguments = variables
        .iter()
        .zip(&lesser.arguments)
        .zip(&greater.arguments)
        .map(|((variable, lesser_sort), greater_sort)| {
            inject_if_needed(
                Pattern::Variable(variable.clone()),
                lesser_sort,
                greater_sort,
            )
        })
        .collect();
    let lesser_application = Pattern::Application {
        symbol: lesser.symbol.clone(),
        arguments: variables.into_iter().map(Pattern::Variable).collect(),
    };
    let right = inject_if_needed(lesser_application, &lesser.result, &greater.result);
    Ok(KoreSentence::Axiom {
        parameters: vec!["R".into()],
        pattern: Box::new(Pattern::Equals {
            operand_sort: greater.result,
            result_sort: KoreSort::Variable("R".into()),
            left: Box::new(Pattern::Application {
                symbol: greater.symbol.clone(),
                arguments: greater_arguments,
            }),
            right: Box::new(right),
        }),
        attributes: Attributes(vec![Pattern::Application {
            symbol: Symbol {
                name: KoreAttribute::SymbolOverload.as_str().into(),
                sort_parameters: Vec::new(),
            },
            arguments: vec![
                Pattern::Application {
                    symbol: greater.symbol,
                    arguments: Vec::new(),
                },
                Pattern::Application {
                    symbol: lesser.symbol,
                    arguments: Vec::new(),
                },
            ],
        }]),
    })
}

struct OverloadProduction {
    symbol: Symbol,
    arguments: Vec<KoreSort>,
    result: KoreSort,
}

fn overload_production(
    overloads: &OverloadOrder<'_>,
    id: ProductionId,
) -> Result<OverloadProduction, ModuleToKoreError> {
    let Sentence::Production {
        label,
        parameters,
        sort,
        items,
        ..
    } = overloads.production(id)
    else {
        unreachable!("overload catalogs contain productions")
    };
    let Some(label) = label else {
        return Err(ModuleToKoreError::InvalidOverloadProduction {
            production: id.0,
            message: "the production has no symbol label".into(),
        });
    };
    Ok(OverloadProduction {
        symbol: encode_kore_label_with_formals(label, parameters),
        arguments: items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => {
                    Some(encode_kore_sort_with_formals(sort, parameters))
                }
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect(),
        result: encode_kore_sort_with_formals(sort, parameters),
    })
}

fn inject_if_needed(pattern: Pattern, from: &KoreSort, to: &KoreSort) -> Pattern {
    if from == to {
        pattern
    } else {
        Pattern::Application {
            symbol: Symbol {
                name: WellKnownSymbol::Inj.as_str().into(),
                sort_parameters: vec![from.clone(), to.clone()],
            },
            arguments: vec![pattern],
        }
    }
}

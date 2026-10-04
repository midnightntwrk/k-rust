//! ```toml algorithm
//! id = "kompile.kore.axioms"
//! name = "generated KORE axiom emission"
//! sites = ["generated_axioms"]
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
use crate::definition::production_kind::{
    ClosedInstance, NoJunkAlternative, NoJunkAxiom, ProductionKind, ResultSorts, UnitInstance,
    mentions_parameter,
};
use crate::definition::relations::SubsortDeclaration;
use crate::kompile::passes::{Placement, has_subsort_axiom};

pub(super) struct GeneratedAxioms {
    pub(super) semantics: Vec<KoreSentence>,
    pub(super) syntax: Vec<KoreSentence>,
}

pub(super) fn generated_axioms(
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
    overloads: &OverloadOrder<'_>,
    subsorts: &PartialOrder<Sort>,
    roles: &SymbolRoles,
) -> Result<GeneratedAxioms, ModuleToKoreError> {
    let mut semantics = Vec::new();
    let mut syntax = Vec::new();
    let mut no_confusion_pairs = BTreeSet::new();
    for (id, production) in productions.productions() {
        let kind = ProductionKind::of(production);
        match kind {
            ProductionKind::Subsort => {
                // An injection into `K` has no subsort axiom and declares no symbol; like any
                // unlabelled production it still reaches `algebraic_axioms`, which rejects an
                // algebraic attribute on it.
                if let Some(axiom) = subsort_axiom(production) {
                    semantics.push(axiom.clone());
                    syntax.push(axiom);
                    continue;
                }
            }
            // The prelude declares and axiomatises a builtin, and no term contains a bracket.
            ProductionKind::Builtin | ProductionKind::Bracket(_) => continue,
            ProductionKind::Function { .. }
            | ProductionKind::MacroProduction
            | ProductionKind::Token { .. }
            | ProductionKind::Unlabelled
            | ProductionKind::Algebraic
            | ProductionKind::Base => {}
        }
        semantics.extend(algebraic_axioms(
            id,
            production,
            kind,
            subsorts,
            productions,
        )?);
        let claims = roles.claims(id);
        if claims.functional()
            && let Some(axiom) = functional_axiom(production)
        {
            semantics.push(axiom);
        }
        if claims.no_confusion() {
            semantics.extend(no_confusion_axioms(
                id,
                productions,
                roles,
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
                let axiom = overload_axiom(overloads, lesser, greater, subsorts)?;
                if cfg!(debug_assertions) {
                    let head = |id| match overloads.production(id) {
                        Sentence::Production { sort, .. } => SortHead::from(sort),
                        Sentence::SyntaxSort { .. }
                        | Sentence::SortSynonym { .. }
                        | Sentence::SyntaxLexical { .. }
                        | Sentence::SyntaxAssociativity { .. }
                        | Sentence::SyntaxPriority { .. }
                        | Sentence::ContextAlias { .. }
                        | Sentence::Context { .. }
                        | Sentence::Rule { .. }
                        | Sentence::Claim { .. }
                        | Sentence::Configuration { .. }
                        | Sentence::Bubble { .. } => {
                            unreachable!("overload catalogs contain productions")
                        }
                    };
                    roles.debug_assert_overload_axiom(
                        overloads,
                        lesser,
                        greater,
                        head(lesser) == head(greater),
                    );
                }
                semantics.push(axiom.clone());
                syntax.push(axiom);
            }
        }
    }
    Ok(GeneratedAxioms { semantics, syntax })
}

/// The injectivity axiom of the no-confusion symbol `id` and its disjointness from every other
/// no-confusion symbol of its sort ([`SymbolClaims::no_confusion`]).
///
/// A schema's disjointness from each instance sort's constructors is its `constructor`
/// attribute's claim. No sort-generic disjointness axiom is emitted: pairing by a parameter's
/// spelling binds nothing.
/// Productions with the same result head are disjoint at the most general common instance of
/// their result sorts, with independent formals renamed apart and all remaining variables bound.
#[deny(clippy::wildcard_enum_match_arm)]
fn no_confusion_axioms(
    id: ProductionId,
    productions: &ProductionCatalog<'_>,
    roles: &SymbolRoles,
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

    let result_sorts = ResultSorts::of(production);
    // Invariant: `emitted_pairs` holds both orderings of every matching-head no-confusion pair
    // already considered, including pairs whose results do not unify, so each is considered once; this scan of
    // `productions.productions()` runs once per no-confusion `id`, O(n^2) in the catalog size.
    for (other_id, other_production) in productions.productions() {
        if other_id == id
            || !roles.claims(other_id).no_confusion()
            || emitted_pairs.contains(&(id, other_id))
        {
            continue;
        }
        match (&result_sorts, ResultSorts::of(other_production)) {
            (ResultSorts::Head(a), ResultSorts::Head(b)) if *a == b => {}
            (ResultSorts::Head(_), ResultSorts::Head(_))
            | (ResultSorts::Head(_), ResultSorts::Every)
            | (ResultSorts::Every, ResultSorts::Head(_))
            | (ResultSorts::Every, ResultSorts::Every) => continue,
        }
        let Some(other) = generated_production(other_production) else {
            continue;
        };
        emitted_pairs.insert((id, other_id));
        emitted_pairs.insert((other_id, id));
        let Some(pattern) = disjointness_pattern(&current, other) else {
            continue;
        };
        axioms.push(KoreSentence::Axiom {
            parameters: pattern.sort_variables().into_iter().collect(),
            pattern: Box::new(pattern),
            attributes: marker_attribute(KoreAttribute::Constructor),
        });
    }
    axioms
}

#[derive(Clone)]
struct GeneratedProduction {
    parameters: Vec<String>,
    symbol: Symbol,
    arguments: Vec<KoreSort>,
    result: KoreSort,
}

impl GeneratedProduction {
    fn substitute_sorts(&mut self, substitution: &BTreeMap<String, KoreSort>) {
        for sort in self
            .symbol
            .sort_parameters
            .iter_mut()
            .chain(&mut self.arguments)
            .chain(std::iter::once(&mut self.result))
        {
            *sort = substitute_kore_sort(sort, substitution);
        }
    }
}

fn disjointness_pattern(
    current: &GeneratedProduction,
    mut other: GeneratedProduction,
) -> Option<Pattern> {
    let mut occupied = current
        .parameters
        .iter()
        .chain(&other.parameters)
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut renames = BTreeMap::new();
    for parameter in &other.parameters {
        let mut suffix = 1;
        let fresh = loop {
            let candidate = format!("{parameter}'{suffix}");
            if occupied.insert(candidate.clone()) {
                break candidate;
            }
            suffix += 1;
        };
        renames.insert(parameter.clone(), KoreSort::Variable(fresh));
    }
    other.substitute_sorts(&renames);
    let substitution = unify_kore_sorts(&current.result, &other.result)?;
    let mut current = current.clone();
    current.substitute_sorts(&substitution);
    other.substitute_sorts(&substitution);
    Some(Pattern::Not {
        sort: current.result.clone(),
        argument: Box::new(Pattern::And {
            sort: current.result.clone(),
            arguments: vec![
                generated_application(&current, "X"),
                generated_application(&other, "Y"),
            ],
        }),
    })
}

/// First-order unification of KORE sorts: a variable may denote any finite sort term, while
/// applications must have equal heads and arities. The occurs check excludes cyclic bindings.
/// Substitution chains are followed when solving each equation and when instantiating a sort.
fn unify_kore_sorts(left: &KoreSort, right: &KoreSort) -> Option<BTreeMap<String, KoreSort>> {
    let mut substitution = BTreeMap::new();
    let mut equations = vec![(left.clone(), right.clone())];
    // Invariant: solutions of the remaining equations under `substitution` are exactly the
    // unifiers of the original pair; each step removes an equality, decomposes applications,
    // or eliminates an unbound variable without introducing a cycle.
    while let Some((left, right)) = equations.pop() {
        let left = substitute_kore_sort(&left, &substitution);
        let right = substitute_kore_sort(&right, &substitution);
        if left == right {
            continue;
        }
        match (left.into_parts(), right.into_parts()) {
            ((other_name, other_arguments), (name, None))
            | ((name, None), (other_name, other_arguments)) => {
                let sort = match other_arguments {
                    None => KoreSort::Variable(other_name),
                    Some(arguments) => KoreSort::Application {
                        name: other_name,
                        arguments,
                    },
                };
                if kore_sort_contains_variable(&sort, &name) {
                    return None;
                }
                substitution.insert(name, sort);
            }
            ((left_name, Some(left_arguments)), (right_name, Some(right_arguments))) => {
                if left_name != right_name || left_arguments.len() != right_arguments.len() {
                    return None;
                }
                equations.extend(left_arguments.into_iter().zip(right_arguments).rev());
            }
        }
    }
    Some(substitution)
}

fn substitute_kore_sort(sort: &KoreSort, substitution: &BTreeMap<String, KoreSort>) -> KoreSort {
    match sort {
        KoreSort::Variable(name) => substitution.get(name).map_or_else(
            || sort.clone(),
            |sort| substitute_kore_sort(sort, substitution),
        ),
        KoreSort::Application { name, arguments } => KoreSort::Application {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|sort| substitute_kore_sort(sort, substitution))
                .collect(),
        },
    }
}

fn kore_sort_contains_variable(sort: &KoreSort, variable: &str) -> bool {
    match sort {
        KoreSort::Variable(name) => name == variable,
        KoreSort::Application { arguments, .. } => arguments
            .iter()
            .any(|sort| kore_sort_contains_variable(sort, variable)),
    }
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

/// The no-junk axiom of every concrete sort whose axiom is statable ([`NoJunkAxiom`]) and has an
/// alternative.
#[deny(clippy::wildcard_enum_match_arm)]
fn no_junk_axioms(
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
    subsorts: &PartialOrder<Sort>,
) -> Vec<KoreSentence> {
    let mut axioms = Vec::new();
    for sort in sorts.sorted_all_sorts() {
        let generators = match NoJunkAxiom::of(productions, sorts, subsorts, sort) {
            NoJunkAxiom::Stated(generators) => generators,
            // A generator's free sort parameters put its applications at every instantiation
            // among the sort's values, which no finite disjunction lists.
            NoJunkAxiom::Unstatable { generator } => {
                debug_assert!(
                    matches!(
                        productions.production(generator),
                        Sentence::Production { parameters, .. } if !parameters.is_empty()
                    ),
                    "only a generator with sort parameters can leave one free at {sort:?}"
                );
                continue;
            }
        };
        if generators.is_empty() {
            continue;
        }
        let result_sort = encode_kore_sort(sort);
        let mut variable_names = BTreeMap::new();
        let mut used_variable_names = BTreeSet::new();
        let mut variable_suffixes = BTreeMap::new();
        let mut alternatives = generators
            .alternatives()
            .map(|alternative| match alternative {
                NoJunkAlternative::DomainValues => Pattern::Top {
                    sort: result_sort.clone(),
                },
                NoJunkAlternative::Generator(instance) => {
                    let production = generated_production_for_sort(
                        productions.production(instance.production()),
                        instance,
                        sort,
                    );
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
                            variable: Box::new(variable),
                            body: Box::new(alternative),
                        };
                    }
                    alternative
                }
                NoJunkAlternative::Injection(witness) => {
                    let variable = consistent_generated_variable(
                        "Val",
                        &encode_kore_sort(witness.source()),
                        &mut variable_names,
                        &mut used_variable_names,
                        &mut variable_suffixes,
                    );
                    Pattern::Exists {
                        sort: result_sort.clone(),
                        variable: Box::new(variable.clone()),
                        body: Box::new(
                            witness.clone().apply_kore(Pattern::Variable(variable), &[]),
                        ),
                    }
                }
            })
            .collect::<Vec<_>>();
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

/// The symbol of the generator `production` instantiated at `target` by `instance`'s
/// substitution, with its argument sorts and result sort `target`.
///
/// `instance` binds every sort parameter of `production`, so every sort this encodes is closed
/// and the closed encoding applies.
fn generated_production_for_sort(
    production: &Sentence,
    instance: &ClosedInstance,
    target: &Sort,
) -> GeneratedProduction {
    let Sentence::Production {
        label,
        parameters,
        items,
        ..
    } = production
    else {
        unreachable!("production catalogs contain productions")
    };
    let Some(label) = label else {
        unreachable!(
            "a generator's kind is base or algebraic, which only a labelled production has"
        )
    };
    let substitution = instance.substitution();
    let label_parameters = label
        .parameters
        .iter()
        .map(|sort| substitute_equation_sort(sort, substitution))
        .collect::<Vec<_>>();
    let arguments = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => {
                Some(substitute_equation_sort(sort, substitution))
            }
            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
        })
        .collect::<Vec<_>>();
    if cfg!(debug_assertions) {
        // A parameter spelled like a sort the substitution introduces is told apart from that
        // sort by spelling alone, so the test covers the parameters no binding mentions.
        let checked = parameters
            .iter()
            .filter(|parameter| {
                !substitution
                    .values()
                    .any(|image| mentions_parameter(image, std::slice::from_ref(*parameter)))
            })
            .cloned()
            .collect::<Vec<_>>();
        debug_assert!(
            !label_parameters
                .iter()
                .chain(&arguments)
                .any(|sort| mentions_parameter(sort, &checked)),
            "the closed instance of `{}` leaves a sort parameter of {checked:?} in an encoded sort",
            label.name
        );
    }
    GeneratedProduction {
        parameters: Vec::new(),
        symbol: encode_kore_label(&Label::with_parameters(&label.name, label_parameters)),
        arguments: arguments.iter().map(encode_kore_sort).collect(),
        result: encode_kore_sort(target),
    }
}

/// `∃ Val. Val = f(K0, …)` for a labelled production `f`; its caller emits it only when the
/// production's claims are [`SymbolClaims::functional`].
fn functional_axiom(production: &Sentence) -> Option<KoreSentence> {
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
            variable: Box::new(value.clone()),
            body: Box::new(Pattern::Equals {
                operand_sort: Box::new(result_sort),
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

fn algebraic_axioms(
    id: ProductionId,
    production: &Sentence,
    kind: ProductionKind,
    subsorts: &PartialOrder<Sort>,
    productions: &ProductionCatalog<'_>,
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
    let comm = attributes.has(AttributeKey::Comm) && kind == ProductionKind::Algebraic;
    let unit = attributes
        .string(AttributeKey::Unit)
        .filter(|_| attributes.has(AttributeKey::Function) || assoc);
    if attributes.has(AttributeKey::Injective) {
        for (key, name) in [
            (AttributeKey::Assoc, "assoc"),
            (AttributeKey::Comm, "comm"),
            (AttributeKey::Idem, "idem"),
        ] {
            if attributes.has(key) {
                return Err(invalid_algebraic(
                    id,
                    name,
                    format!(
                        "injective contradicts the {name} axiom, which identifies applications with different arguments"
                    ),
                ));
            }
        }
    }
    if !assoc && !idem && !comm && unit.is_none() {
        return Ok(Vec::new());
    }
    let Some(label) = label else {
        return Err(invalid_algebraic(
            id,
            if assoc {
                "assoc"
            } else if idem {
                "idem"
            } else if comm {
                "comm"
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
                operand_sort: Box::new(result_sort.clone()),
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

    if comm {
        if arguments.len() != 2 {
            return Err(invalid_algebraic(
                id,
                "comm",
                format!("expected arity 2, found {}", arguments.len()),
            ));
        }
        if arguments[0] != arguments[1] {
            return Err(invalid_algebraic(
                id,
                "comm",
                "both argument sorts must be equal",
            ));
        }
        let argument_sort = encode_kore_sort_with_formals(arguments[0], parameters);
        let variables = ["K1", "K2"].map(|name| Variable {
            kind: VariableKind::Element,
            name: name.into(),
            sort: argument_sort.clone(),
        });
        let apply = |arguments| Pattern::Application {
            symbol: symbol.clone(),
            arguments,
        };
        axioms.push(KoreSentence::Axiom {
            parameters: axiom_parameters.clone(),
            pattern: Box::new(Pattern::Equals {
                operand_sort: Box::new(result_sort.clone()),
                result_sort: KoreSort::Variable("R".into()),
                left: Box::new(apply(vec![
                    Pattern::Variable(variables[0].clone()),
                    Pattern::Variable(variables[1].clone()),
                ])),
                right: Box::new(apply(vec![
                    Pattern::Variable(variables[1].clone()),
                    Pattern::Variable(variables[0].clone()),
                ])),
            }),
            attributes: marker_attribute(KoreAttribute::Comm),
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
                operand_sort: Box::new(result_sort.clone()),
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
        let instance = UnitInstance::of(productions, unit, sort)
            .map_err(|error| invalid_algebraic(id, "unit", error.to_string()))?;
        let unit = Pattern::Application {
            symbol: encode_kore_label_with_formals(instance.label(), parameters),
            arguments: Vec::new(),
        };
        for arguments in [
            vec![Pattern::Variable(variable.clone()), unit.clone()],
            vec![unit, Pattern::Variable(variable.clone())],
        ] {
            axioms.push(KoreSentence::Axiom {
                parameters: axiom_parameters.clone(),
                pattern: Box::new(Pattern::Equals {
                    operand_sort: Box::new(result_sort.clone()),
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
            let (name, None) = encode_kore_sort_with_formals(parameter, parameters).into_parts()
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
    let Some(SubsortDeclaration::Pair { child, parent }) = SubsortDeclaration::of(production)
    else {
        return None;
    };
    if !has_subsort_axiom(parent) {
        return None;
    }

    let subsort = encode_kore_sort(child);
    let sort = encode_kore_sort(parent);
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
            variable: Box::new(value.clone()),
            body: Box::new(Pattern::Equals {
                operand_sort: Box::new(sort.clone()),
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

/// `f_greater(place(K0), …) = place(f_lesser(K0, …))`: the overload axiom relating the lesser
/// production `lesser_id` to the greater `greater_id`, where `place` puts each lesser argument and
/// the lesser application at the greater production's sort ([`kore_place`]).
///
/// The overload order relates the pair when every sort of the lesser production is below or equal
/// to the greater's in the declared order, which contains `KItem < K`; an argument or result that
/// crosses `K` is placed as the one-element sequence, the embedding of an item in `K`. A pair
/// with sort parameters is compared with its formals as the sorts they are written as, which
/// stand for the axiom's sort variables. A pair that cannot be placed has no overload axiom and is
/// rejected.
fn overload_axiom(
    overloads: &OverloadOrder<'_>,
    lesser_id: ProductionId,
    greater_id: ProductionId,
    subsorts: &PartialOrder<Sort>,
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

    let formals = lesser
        .formals
        .iter()
        .chain(greater.formals)
        .cloned()
        .collect::<Vec<_>>();
    let unplaceable = |what: String, actual: &Sort, expected: &Sort| {
        ModuleToKoreError::InvalidOverloadProduction {
            production: lesser_id.0,
            message: format!(
                "{what} of sort {actual} cannot be placed at sort {expected} of production #{}",
                greater_id.0
            ),
        }
    };
    let variables = lesser
        .arguments
        .iter()
        .enumerate()
        .map(|(index, (_, sort))| Variable {
            kind: VariableKind::Element,
            name: format!("K{index}"),
            sort: sort.clone(),
        })
        .collect::<Vec<_>>();
    let greater_arguments = variables
        .iter()
        .zip(&lesser.arguments)
        .zip(&greater.arguments)
        .enumerate()
        .map(
            |(index, ((variable, (lesser_sort, _)), (greater_sort, _)))| {
                kore_place(
                    lesser_sort,
                    greater_sort,
                    Pattern::Variable(variable.clone()),
                    subsorts,
                    &formals,
                )
                .ok_or_else(|| unplaceable(format!("argument {index}"), lesser_sort, greater_sort))
            },
        )
        .collect::<Result<Vec<_>, _>>()?;
    let lesser_application = Pattern::Application {
        symbol: lesser.symbol.clone(),
        arguments: variables.into_iter().map(Pattern::Variable).collect(),
    };
    let right = kore_place(
        lesser.sort,
        greater.sort,
        lesser_application,
        subsorts,
        &formals,
    )
    .ok_or_else(|| unplaceable("the result".into(), lesser.sort, greater.sort))?;
    Ok(KoreSentence::Axiom {
        parameters: vec!["R".into()],
        pattern: Box::new(Pattern::Equals {
            operand_sort: Box::new(greater.result),
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

/// An overload production's symbol and sorts: each argument sort as declared beside its KORE
/// encoding, and the result sort both ways.
struct OverloadProduction<'a> {
    symbol: Symbol,
    formals: &'a [Sort],
    arguments: Vec<(&'a Sort, KoreSort)>,
    sort: &'a Sort,
    result: KoreSort,
}

fn overload_production<'a>(
    overloads: &'a OverloadOrder<'_>,
    id: ProductionId,
) -> Result<OverloadProduction<'a>, ModuleToKoreError> {
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
        formals: parameters,
        arguments: items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => {
                    Some((sort, encode_kore_sort_with_formals(sort, parameters)))
                }
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect(),
        sort,
        result: encode_kore_sort_with_formals(sort, parameters),
    })
}

/// `pattern` of sort `actual` placed at a position of sort `expected`, or `None` when no value of
/// `actual` is a value of `expected` in the emitted theory.
///
/// The pattern is unchanged when the sorts are equal, and injected into `expected` when a chain of
/// subsort axioms leads there ([`crate::kompile::passes::Injectable::between`]). Otherwise a value of `K` is a sequence of
/// items, so at `K` the pattern becomes the one-element sequence `kseq{}(item, dotk{}())`, whose
/// item is the pattern injected into `KItem` unless it already is a `KItem`; above `K`, that
/// sequence is injected from `K` into `expected`. `formals` are the sort parameters of the
/// sentence, encoded as sort variables.
fn kore_place(
    actual: &Sort,
    expected: &Sort,
    pattern: Pattern,
    subsorts: &PartialOrder<Sort>,
    formals: &[Sort],
) -> Option<Pattern> {
    Some(Placement::between(actual, expected, subsorts)?.apply_kore(pattern, formals))
}

#[cfg(test)]
mod tests {
    use serde_json::Value;

    use super::*;
    use crate::definition::compute_overloads;

    #[test]
    fn kore_sort_unification_checks_cycles_and_repeated_variables() {
        let variable = |name: &str| KoreSort::Variable(name.into());
        let application = |name: &str, arguments| KoreSort::Application {
            name: name.into(),
            arguments,
        };
        let x = variable("X");
        let y = variable("Y");
        let a = application("A", vec![]);
        let b = application("B", vec![]);
        for (left, right) in [
            (x.clone(), application("F", vec![x.clone()])),
            (
                application("Pair", vec![x.clone(), y.clone()]),
                application("Pair", vec![y.clone(), application("F", vec![x.clone()])]),
            ),
            (
                application("Pair", vec![x.clone(), x.clone()]),
                application("Pair", vec![a.clone(), b]),
            ),
            (application("F", vec![x.clone()]), application("F", vec![])),
        ] {
            assert_eq!(unify_kore_sorts(&left, &right), None, "{left:?}, {right:?}");
            assert_eq!(unify_kore_sorts(&right, &left), None, "{right:?}, {left:?}");
        }
        let left = application("Pair", vec![x.clone(), x.clone()]);
        let right = application("Pair", vec![y.clone(), application("F", vec![a.clone()])]);
        let substitution = unify_kore_sorts(&left, &right).unwrap();
        let expected = application("F", vec![a]);
        assert_eq!(substitute_kore_sort(&x, &substitution), expected);
        assert_eq!(substitute_kore_sort(&y, &substitution), expected);
        assert_eq!(
            substitute_kore_sort(&left, &substitution),
            substitute_kore_sort(&right, &substitution)
        );
    }

    fn sort(name: &str) -> Sort {
        Sort::new(name)
    }

    fn order(edges: &[(&str, &str)]) -> PartialOrder<Sort> {
        PartialOrder::new(
            edges
                .iter()
                .map(|(lesser, greater)| (sort(lesser), sort(greater))),
        )
        .expect("the test order is acyclic")
    }

    fn production(
        label: Option<&str>,
        result: &str,
        arguments: &[&str],
        overload: Option<&str>,
    ) -> Sentence {
        let mut attributes = KAttributes::default();
        if let Some(group) = overload {
            attributes.set(AttributeKey::Overload, Value::String(group.into()));
        }
        Sentence::Production {
            label: label.map(Label::new),
            parameters: Vec::new(),
            sort: sort(result),
            items: arguments
                .iter()
                .map(|argument| ProductionItem::NonTerminal {
                    sort: sort(argument),
                    name: None,
                })
                .collect(),
            attributes,
        }
    }

    fn id_of(overloads: &OverloadOrder<'_>, label: &str) -> ProductionId {
        overloads
            .productions()
            .find_map(|(id, sentence)| {
                let Sentence::Production {
                    label: Some(found), ..
                } = sentence
                else {
                    return None;
                };
                (found.name == label).then_some(id)
            })
            .unwrap_or_else(|| panic!("the test declares {label}"))
    }

    /// The overload axiom relating the production labelled `lesser` to the one labelled `greater`.
    fn overload(
        productions: &[Sentence],
        subsorts: &PartialOrder<Sort>,
        lesser: &str,
        greater: &str,
    ) -> Result<String, ModuleToKoreError> {
        let overloads = compute_overloads(productions, subsorts).expect("no overload cycle");
        let lesser = id_of(&overloads, lesser);
        let greater = id_of(&overloads, greater);
        assert!(
            overloads.order().less_than(&lesser, &greater),
            "the overload order relates the pair"
        );
        overload_axiom(&overloads, lesser, greater, subsorts).map(|axiom| axiom.to_string())
    }

    #[test]
    fn an_overload_argument_across_k_is_placed_as_the_one_element_sequence() {
        // syntax Foo ::= f(K) [overload(f)]
        // syntax Foo ::= f(Int) [overload(f)]
        let productions = [
            production(Some("fK"), "Foo", &["K"], Some("f")),
            production(Some("fInt"), "Foo", &["Int"], Some("f")),
        ];
        let subsorts = order(&[("KItem", "K"), ("Int", "KItem"), ("Foo", "KItem")]);
        let axiom = overload(&productions, &subsorts, "fInt", "fK").expect("the pair is placeable");
        assert!(
            axiom.contains("LblfK{}(kseq{}(inj{SortInt{}, SortKItem{}}(K0:SortInt{}), dotk{}()))"),
            "{axiom}"
        );
        assert!(!axiom.contains("inj{SortInt{}, SortK{}}"), "{axiom}");
        assert!(axiom.contains("LblfInt{}(K0:SortInt{})"), "{axiom}");
    }

    #[test]
    fn an_overload_result_across_k_is_placed_as_the_one_element_sequence() {
        // syntax K ::= g(Int) [overload(g)]
        // syntax Bar ::= g(Int) [overload(g)]
        let productions = [
            production(Some("gK"), "K", &["Int"], Some("g")),
            production(Some("gBar"), "Bar", &["Int"], Some("g")),
        ];
        let subsorts = order(&[("KItem", "K"), ("Int", "KItem"), ("Bar", "KItem")]);
        let axiom = overload(&productions, &subsorts, "gBar", "gK").expect("the pair is placeable");
        assert!(
            axiom
                .contains("kseq{}(inj{SortBar{}, SortKItem{}}(LblgBar{}(K0:SortInt{})), dotk{}())"),
            "{axiom}"
        );
        assert!(!axiom.contains("inj{SortBar{}, SortK{}}"), "{axiom}");
    }

    #[test]
    fn an_overload_argument_above_k_injects_the_sequence_from_k() {
        let productions = [
            production(Some("hKList"), "Foo", &["KList"], Some("h")),
            production(Some("hInt"), "Foo", &["Int"], Some("h")),
        ];
        let subsorts = order(&[("KItem", "K"), ("K", "KList"), ("Int", "KItem")]);
        let axiom =
            overload(&productions, &subsorts, "hInt", "hKList").expect("the pair is placeable");
        assert!(
            axiom.contains(
                "LblhKList{}(inj{SortK{}, SortKList{}}(kseq{}(inj{SortInt{}, SortKItem{}}(K0:SortInt{}), dotk{}())))"
            ),
            "{axiom}"
        );
        assert!(!axiom.contains("inj{SortInt{}, SortKList{}}"), "{axiom}");
    }

    #[test]
    fn an_overload_along_subsort_axioms_injects_directly() {
        let productions = [
            production(Some("pExp"), "Exp", &["Exp"], Some("p")),
            production(Some("pVal"), "Val", &["Int"], Some("p")),
        ];
        let subsorts = order(&[("Int", "Val"), ("Val", "Exp")]);
        let axiom =
            overload(&productions, &subsorts, "pVal", "pExp").expect("the pair is placeable");
        assert!(
            axiom.contains(
                "LblpExp{}(inj{SortInt{}, SortExp{}}(K0:SortInt{})), inj{SortVal{}, SortExp{}}(LblpVal{}(K0:SortInt{}))"
            ),
            "{axiom}"
        );
    }

    #[test]
    fn an_overload_pair_that_cannot_be_placed_is_rejected() {
        // A parser sort declared below `K` is neither injected into `KItem` nor into `K`.
        let productions = [
            production(Some("qK"), "Foo", &["K"], Some("q")),
            production(Some("qParser"), "Foo", &["#Parser"], Some("q")),
        ];
        let subsorts = order(&[("KItem", "K"), ("#Parser", "K")]);
        let error = overload(&productions, &subsorts, "qParser", "qK")
            .expect_err("a parser sort has no embedding in K");
        let ModuleToKoreError::InvalidOverloadProduction { message, .. } = &error else {
            panic!("expected InvalidOverloadProduction, got {error}");
        };
        assert!(
            message.contains("argument 0 of sort #Parser cannot be placed at sort K"),
            "{message}"
        );
    }

    #[test]
    fn the_no_junk_axiom_above_k_lists_only_injections_along_subsort_axioms() {
        // syntax K ::= KItem, syntax KList ::= K, syntax KItem ::= Int
        let declarations = ["K", "KItem", "KList", "Int"].map(|name| Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: sort(name),
            attributes: KAttributes::default(),
        });
        let productions = [
            production(None, "K", &["KItem"], None),
            production(None, "KList", &["K"], None),
            production(None, "KItem", &["Int"], None),
        ];
        let sorts = SortCatalog::from_visible(declarations.iter());
        let catalog = ProductionCatalog::from_visible(productions.iter());
        let subsorts = order(&[("KItem", "K"), ("K", "KList"), ("Int", "KItem")]);
        let axioms = no_junk_axioms(&catalog, &sorts, &subsorts)
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        let klist = axioms
            .iter()
            .find(|axiom| axiom.contains("\\or{SortKList{}}"))
            .unwrap_or_else(|| panic!("KList has a no-junk axiom: {axioms:?}"));
        assert!(klist.contains("inj{SortK{}, SortKList{}}"), "{klist}");
        assert!(!klist.contains("inj{SortInt{}, SortKList{}}"), "{klist}");
        assert!(!klist.contains("inj{SortKItem{}, SortKList{}}"), "{klist}");
        let k_item = axioms
            .iter()
            .find(|axiom| axiom.contains("\\or{SortKItem{}}"))
            .unwrap_or_else(|| panic!("KItem has a no-junk axiom: {axioms:?}"));
        assert!(k_item.contains("inj{SortInt{}, SortKItem{}}"), "{k_item}");
        assert!(
            !axioms.iter().any(|axiom| axiom.contains("\\or{SortK{}}")),
            "K has no injection alternative: {axioms:?}"
        );
    }
}

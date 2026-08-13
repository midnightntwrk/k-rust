//! Production-aware insertion of explicit KORE subsort injections.

use std::collections::BTreeMap;
use std::fmt;

use crate::definition::{
    Definition, LabelHead, PartialOrder, ProductionCatalog, ProductionId, ResolveError,
    ResolvedDefinition, Sentence, SortCatalog, SortHead,
};
use crate::kast::{Label, Sort, Term};

const K_SORT: &str = "K";
const K_ITEM_SORT: &str = "KItem";
const BOOL_SORT: &str = "Bool";

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SortInjectionError {
    Definition(ResolveError),
    MissingModule(String),
    CircularSubsort(Vec<Sort>),
    MissingSort(&'static str),
    UnknownLabel(String),
    AmbiguousLabel {
        label: String,
        productions: usize,
    },
    InvalidResolvedProduction {
        label: String,
        production: usize,
        message: String,
    },
    InvalidArity {
        label: String,
        expected: usize,
        actual: usize,
    },
    MissingParameters {
        label: String,
        expected: usize,
        actual: usize,
    },
    IncompatibleSorts {
        sorts: Vec<Sort>,
        expected: Option<Sort>,
    },
}

impl fmt::Display for SortInjectionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition(error) => error.fmt(formatter),
            Self::MissingModule(module) => {
                write!(formatter, "sort-injection module {module:?} was not found")
            }
            Self::CircularSubsort(path) => write!(
                formatter,
                "cannot add sort injections with circular subsorts: {}",
                path.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" > ")
            ),
            Self::MissingSort(construct) => {
                write!(formatter, "cannot recover the sort of {construct}")
            }
            Self::UnknownLabel(label) => {
                write!(formatter, "cannot find a production for KLabel {label:?}")
            }
            Self::AmbiguousLabel { label, productions } => write!(
                formatter,
                "KLabel {label:?} has {productions} productions and no resolved production identity"
            ),
            Self::InvalidResolvedProduction {
                label,
                production,
                message,
            } => write!(
                formatter,
                "resolved production #{production} for KLabel {label:?} is invalid: {message}"
            ),
            Self::InvalidArity {
                label,
                expected,
                actual,
            } => write!(
                formatter,
                "KLabel {label:?} expects {expected} arguments but received {actual}"
            ),
            Self::MissingParameters {
                label,
                expected,
                actual,
            } => write!(
                formatter,
                "KLabel {label:?} expects {expected} sort parameters but carries {actual}"
            ),
            Self::IncompatibleSorts { sorts, expected } => {
                write!(
                    formatter,
                    "cannot compute a unique least upper bound for {}",
                    sorts
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
                if let Some(expected) = expected {
                    write!(formatter, " below expected sort {expected}")?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for SortInjectionError {}

/// Adds explicit `inj{From,To}` applications using one resolved module's syntax.
#[derive(Clone, Debug)]
pub struct SortInjector<'a> {
    productions: ProductionCatalog<'a>,
    sorts: SortCatalog<'a>,
    subsorts: PartialOrder<Sort>,
}

impl<'a> SortInjector<'a> {
    pub fn new(
        definition: &'a ResolvedDefinition,
        module: &str,
    ) -> Result<Self, SortInjectionError> {
        let module = definition
            .module_id(module)
            .ok_or_else(|| SortInjectionError::MissingModule(module.to_owned()))?;
        let subsorts = definition
            .subsorts(module)
            .map_err(|cycle| SortInjectionError::CircularSubsort(cycle.path))?;
        Ok(Self {
            productions: definition.production_catalog(module),
            sorts: definition.sort_catalog(module),
            subsorts,
        })
    }

    /// Add injections to a standalone term in the supplied top-level sort.
    pub fn inject(&self, term: &Term, expected: &Sort) -> Result<Term, SortInjectionError> {
        self.inject_with_position(term, expected, false)
    }

    /// Infer a standalone term's top sort and add every injection below it.
    pub fn inject_at_top(&self, term: &Term) -> Result<Term, SortInjectionError> {
        let top = self.term_sort(term, None)?;
        self.inject_with_position(term, &top, false)
    }

    /// Match Java's sentence boundary: rule/claim conditions are always `Bool`.
    pub fn inject_sentence(&self, sentence: &Sentence) -> Result<Sentence, SortInjectionError> {
        match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } => Ok(Sentence::Rule {
                body: self.inject_rule_body(body)?,
                requires: self.inject(requires, &Sort::new(BOOL_SORT))?,
                ensures: self.inject(ensures, &Sort::new(BOOL_SORT))?,
                attributes: attributes.clone(),
            }),
            Sentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            } => Ok(Sentence::Claim {
                body: self.inject_rule_body(body)?,
                requires: self.inject(requires, &Sort::new(BOOL_SORT))?,
                ensures: self.inject(ensures, &Sort::new(BOOL_SORT))?,
                attributes: attributes.clone(),
            }),
            _ => Ok(sentence.clone()),
        }
    }

    fn inject_rule_body(&self, body: &Term) -> Result<Term, SortInjectionError> {
        let body = if has_rewrite(body) {
            Term::Rewrite {
                left: Box::new(rewrite_projection(body, false)),
                right: Box::new(rewrite_projection(body, true)),
            }
        } else {
            body.clone()
        };
        self.inject_at_top(&body)
    }

    pub fn term_sort(
        &self,
        term: &Term,
        expected: Option<&Sort>,
    ) -> Result<Sort, SortInjectionError> {
        // A semantic cast on an application records the intended overload/context, not a
        // replacement for the selected production's result sort. In particular, `{P}:K` where
        // `P:KItem` must still materialize the KItem-to-K sequence wrapper.
        if !matches!(term.unannotated(), Term::Apply { .. })
            && let Some(sort) = term.metadata().and_then(|metadata| metadata.sort.clone())
        {
            return Ok(sort);
        }
        match term.unannotated() {
            Term::InjectedLabel(_) => Ok(Sort::new(K_ITEM_SORT)),
            Term::Rewrite { left, right } => {
                let left = self.term_sort(left, expected)?;
                let right = self.term_sort(right, expected)?;
                self.least_upper_bound(&[left, right], expected)
            }
            Term::As { pattern, alias } => {
                let pattern = self.term_sort(pattern, expected)?;
                let alias = self.term_sort(alias, expected)?;
                self.least_upper_bound(&[pattern, alias], expected)
            }
            Term::Variable { sort, .. } => Ok(sort
                .clone()
                .or_else(|| expected.cloned())
                .unwrap_or_else(|| Sort::new(K_SORT))),
            Term::Sequence(_) => Ok(Sort::new(K_SORT)),
            Term::Token { sort, .. } => Ok(sort.clone()),
            Term::Apply { label, arguments } => {
                if label.name == "inj" {
                    return label.parameters.get(1).cloned().ok_or_else(|| {
                        SortInjectionError::MissingParameters {
                            label: label.name.clone(),
                            expected: 2,
                            actual: label.parameters.len(),
                        }
                    });
                }
                if let Some(sort) = semantic_cast_sort(label) {
                    return Ok(sort);
                }
                if label.name == "#OuterCast" {
                    let [argument] = arguments.as_slice() else {
                        return Err(SortInjectionError::InvalidArity {
                            label: label.name.clone(),
                            expected: 1,
                            actual: arguments.len(),
                        });
                    };
                    return self.term_sort(argument, expected);
                }
                match label.name.as_str() {
                    "#Top" | "#Bottom" | "#And" | "#Or" | "#Not" | "#Implies" | "#AG"
                    | "weakExistsFinally" | "weakAlwaysFinally" => {
                        return label.parameters.first().cloned().ok_or_else(|| {
                            SortInjectionError::MissingParameters {
                                label: label.name.clone(),
                                expected: 1,
                                actual: label.parameters.len(),
                            }
                        });
                    }
                    "#Ceil" | "#Floor" | "#Equals" => {
                        return label.parameters.get(1).cloned().ok_or_else(|| {
                            SortInjectionError::MissingParameters {
                                label: label.name.clone(),
                                expected: 2,
                                actual: label.parameters.len(),
                            }
                        });
                    }
                    "#Exists" | "#Forall" => {
                        return label.parameters.last().cloned().ok_or_else(|| {
                            SortInjectionError::MissingParameters {
                                label: label.name.clone(),
                                expected: 1,
                                actual: 0,
                            }
                        });
                    }
                    "#fun2" if arguments.len() >= 2 => {
                        return self.term_sort(&arguments[0], expected);
                    }
                    "#fun3" if arguments.len() >= 3 => {
                        return self.term_sort(&arguments[1], expected);
                    }
                    "#let" if arguments.len() >= 3 => {
                        return self.term_sort(&arguments[2], expected);
                    }
                    "_:=K_" | "_:/=K_" => return Ok(Sort::new(BOOL_SORT)),
                    _ => {}
                }
                let signature = self.signature(term, label, arguments)?;
                Ok(signature.result)
            }
            Term::Annotated { .. } => unreachable!(),
        }
    }

    fn inject_with_position(
        &self,
        term: &Term,
        expected: &Sort,
        is_lhs: bool,
    ) -> Result<Term, SortInjectionError> {
        let actual = self.term_sort(term, Some(expected))?;
        if actual == *expected {
            return self.visit_children(term, &actual, is_lhs);
        }

        let visited = self.visit_children(term, &actual, is_lhs)?;
        if expected.name == K_SORT {
            if actual.name == K_ITEM_SORT {
                return Ok(Term::Sequence(vec![visited]));
            }
            return Ok(Term::Sequence(vec![injection(
                actual,
                Sort::new(K_ITEM_SORT),
                visited,
            )]));
        }
        if let Some(wrapped) =
            self.collection_wrapper(term, &actual, expected, visited.clone(), is_lhs)?
        {
            return Ok(wrapped);
        }
        Ok(injection(actual, expected.clone(), visited))
    }

    fn collection_wrapper(
        &self,
        term: &Term,
        actual: &Sort,
        expected: &Sort,
        visited: Term,
        is_lhs: bool,
    ) -> Result<Option<Term>, SortInjectionError> {
        let hook = self
            .sorts
            .attributes_for(&SortHead::from(expected))
            .and_then(|attributes| attributes.get_str("hook"));
        if !matches!(hook, Some("MAP.Map" | "SET.Set" | "LIST.List")) {
            return Ok(None);
        }
        let Term::Apply { label, arguments } = term.unannotated() else {
            return Ok(None);
        };
        for (_, production) in self.productions.sorted_productions() {
            let Sentence::Production { attributes, .. } = production else {
                unreachable!()
            };
            let (Some(wrapped_label), Some(element_label)) = (
                attributes.get_str("wrapElement"),
                attributes.get_str("element"),
            ) else {
                continue;
            };
            let wraps_actual = self
                .productions
                .productions_for(&LabelHead::new(wrapped_label))
                .iter()
                .any(|id| {
                    matches!(
                        self.productions.production(*id),
                        Sentence::Production { sort, .. } if sort == actual
                    )
                });
            if !wraps_actual {
                continue;
            }
            let is_map = attributes.get("comm").is_some()
                && attributes.get("idem").is_none()
                && attributes.get("bag").is_none();
            if !is_map {
                return Ok(Some(Term::apply(element_label, vec![visited])));
            }

            let element_ids = self
                .productions
                .productions_for(&LabelHead::new(element_label));
            let Some(element_id) = element_ids.first() else {
                return Err(SortInjectionError::UnknownLabel(element_label.into()));
            };
            let Sentence::Production { items, .. } = self.productions.production(*element_id)
            else {
                unreachable!()
            };
            let key_sort = items.iter().find_map(|item| match item {
                crate::definition::ProductionItem::NonTerminal { sort, .. } => Some(sort),
                _ => None,
            });
            let Some(key_sort) = key_sort else {
                return Err(SortInjectionError::InvalidArity {
                    label: element_label.into(),
                    expected: 2,
                    actual: 0,
                });
            };
            let key = if label.name == wrapped_label {
                arguments
                    .first()
                    .cloned()
                    .ok_or_else(|| SortInjectionError::InvalidArity {
                        label: label.name.clone(),
                        expected: 1,
                        actual: 0,
                    })?
            } else {
                Term::apply(format!("{}Key", expected.name), vec![visited.clone()])
            };
            let key = self.inject_with_position(&key, key_sort, is_lhs)?;
            return Ok(Some(Term::apply(element_label, vec![key, visited])));
        }
        Ok(None)
    }

    fn visit_children(
        &self,
        term: &Term,
        actual: &Sort,
        is_lhs: bool,
    ) -> Result<Term, SortInjectionError> {
        let rebuilt = match term.unannotated() {
            Term::Apply { label, .. } if label.name == "inj" => return Ok(term.clone()),
            Term::Apply { label, arguments }
                if semantic_cast_sort(label).is_some() || label.name == "#OuterCast" =>
            {
                let [argument] = arguments.as_slice() else {
                    return Err(SortInjectionError::InvalidArity {
                        label: label.name.clone(),
                        expected: 1,
                        actual: arguments.len(),
                    });
                };
                Term::Apply {
                    label: label.clone(),
                    arguments: vec![self.inject_with_position(argument, actual, is_lhs)?],
                }
            }
            Term::Apply { label, arguments } => {
                let signature = self.signature(term, label, arguments)?;
                let arguments = arguments
                    .iter()
                    .zip(signature.arguments.iter())
                    .map(|(argument, expected)| {
                        self.inject_with_position(argument, expected, is_lhs)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Term::Apply {
                    label: signature.label,
                    arguments,
                }
            }
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.inject_with_position(left, actual, true)?),
                right: Box::new(self.inject_with_position(right, actual, false)?),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.inject_with_position(pattern, actual, is_lhs)?),
                alias: Box::new(with_variable_sort(alias, actual)),
            },
            Term::Sequence(items) => {
                let items = items
                    .iter()
                    .map(|item| {
                        let context = if is_lhs {
                            Sort::new(K_ITEM_SORT)
                        } else {
                            Sort::new(K_SORT)
                        };
                        let item_sort = self.term_sort(item, Some(&context))?;
                        let expected = if item_sort.name == K_SORT {
                            Sort::new(K_SORT)
                        } else {
                            Sort::new(K_ITEM_SORT)
                        };
                        self.inject_with_position(item, &expected, is_lhs)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Term::Sequence(items)
            }
            Term::InjectedLabel(label) => Term::InjectedLabel(label.clone()),
            Term::Variable { name, .. } => Term::Variable {
                name: name.clone(),
                sort: Some(actual.clone()),
            },
            Term::Token { token, sort } => Term::Token {
                token: token.clone(),
                sort: sort.clone(),
            },
            Term::Annotated { .. } => unreachable!(),
        };
        Ok(copy_metadata(term, rebuilt))
    }

    fn signature(
        &self,
        term: &Term,
        label: &Label,
        arguments: &[Term],
    ) -> Result<InstantiatedSignature, SortInjectionError> {
        let production = self.production(term, label)?;
        let Sentence::Production {
            parameters,
            sort,
            items,
            ..
        } = production
        else {
            unreachable!()
        };
        let argument_sorts = items
            .iter()
            .filter_map(|item| match item {
                crate::definition::ProductionItem::NonTerminal { sort, .. } => Some(sort),
                _ => None,
            })
            .collect::<Vec<_>>();
        if argument_sorts.len() != arguments.len() {
            return Err(SortInjectionError::InvalidArity {
                label: label.name.clone(),
                expected: argument_sorts.len(),
                actual: arguments.len(),
            });
        }
        if parameters.len() != label.parameters.len() {
            return Err(SortInjectionError::MissingParameters {
                label: label.name.clone(),
                expected: parameters.len(),
                actual: label.parameters.len(),
            });
        }
        let substitution = parameters
            .iter()
            .cloned()
            .zip(label.parameters.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        Ok(InstantiatedSignature {
            label: label.clone(),
            arguments: argument_sorts
                .into_iter()
                .map(|sort| substitute_sort(sort, &substitution))
                .collect(),
            result: substitute_sort(sort, &substitution),
        })
    }

    fn production(&self, term: &Term, label: &Label) -> Result<&'a Sentence, SortInjectionError> {
        if let Some(resolved) = term.metadata().and_then(|metadata| metadata.production) {
            if resolved.0 >= self.productions.len() {
                return Err(SortInjectionError::InvalidResolvedProduction {
                    label: label.name.clone(),
                    production: resolved.0,
                    message: format!(
                        "the active production catalog contains only {} productions",
                        self.productions.len()
                    ),
                });
            }
            let production = self.productions.production(ProductionId(resolved.0));
            let Sentence::Production {
                label: production_label,
                ..
            } = production
            else {
                unreachable!()
            };
            if production_label
                .as_ref()
                .is_none_or(|production_label| production_label.name != label.name)
            {
                return Err(SortInjectionError::InvalidResolvedProduction {
                    label: label.name.clone(),
                    production: resolved.0,
                    message: "the production belongs to a different KLabel".into(),
                });
            }
            return Ok(production);
        }
        let ids = self.productions.productions_for(&LabelHead::from(label));
        if ids.len() > 1
            && let Some(sort) = term.metadata().and_then(|metadata| metadata.sort.as_ref())
        {
            let matching = ids
                .iter()
                .filter(|id| {
                    matches!(
                        self.productions.production(**id),
                        Sentence::Production { sort: result, .. } if result == sort
                    )
                })
                .collect::<Vec<_>>();
            if let [id] = matching.as_slice() {
                return Ok(self.productions.production(**id));
            }
        }
        match ids {
            [] => Err(SortInjectionError::UnknownLabel(label.name.clone())),
            [id] => Ok(self.productions.production(*id)),
            ids => Err(SortInjectionError::AmbiguousLabel {
                label: label.name.clone(),
                productions: ids.len(),
            }),
        }
    }

    pub(crate) fn least_upper_bound(
        &self,
        sorts: &[Sort],
        expected: Option<&Sort>,
    ) -> Result<Sort, SortInjectionError> {
        let mut unique = sorts.to_vec();
        unique.sort();
        unique.dedup();
        if let [sort] = unique.as_slice() {
            return Ok(sort.clone());
        }
        let mut bounds = self.subsorts.upper_bounds(&unique);
        if let Some(expected) = expected {
            bounds.retain(|bound| self.subsorts.less_than_eq(bound, expected));
        }
        let minima = self.subsorts.minimal(&bounds);
        if minima.len() == 1 {
            Ok(minima.into_iter().next().expect("one minimum"))
        } else {
            Err(SortInjectionError::IncompatibleSorts {
                sorts: unique,
                expected: expected.cloned(),
            })
        }
    }
}

#[derive(Clone, Debug)]
struct InstantiatedSignature {
    label: Label,
    arguments: Vec<Sort>,
    result: Sort,
}

pub fn add_sort_injections(
    definition: &Definition,
    module: &str,
    term: &Term,
) -> Result<Term, SortInjectionError> {
    let resolved =
        ResolvedDefinition::resolve(definition).map_err(SortInjectionError::Definition)?;
    add_sort_injections_from_resolved(&resolved, module, term)
}

/// Materialize sort injections across every rule and claim before final KORE lowering.
pub fn add_sort_injections_to_definition(
    definition: &Definition,
) -> Result<Definition, SortInjectionError> {
    let resolved =
        ResolvedDefinition::resolve(definition).map_err(SortInjectionError::Definition)?;
    let mut output = definition.clone();
    for module in &mut output.modules {
        let injector = SortInjector::new(&resolved, &module.name)?;
        for sentence in &mut module.local_sentences {
            *sentence = injector.inject_sentence(sentence)?;
        }
    }
    Ok(output)
}

pub fn add_sort_injections_from_resolved(
    definition: &ResolvedDefinition,
    module: &str,
    term: &Term,
) -> Result<Term, SortInjectionError> {
    SortInjector::new(definition, module)?.inject_at_top(term)
}

fn injection(from: Sort, to: Sort, term: Term) -> Term {
    Term::Apply {
        label: Label::with_parameters("inj", vec![from, to]),
        arguments: vec![term],
    }
}

fn copy_metadata(source: &Term, term: Term) -> Term {
    if let Some(metadata) = source.metadata() {
        term.with_metadata(metadata.clone())
    } else {
        term
    }
}

fn semantic_cast_sort(label: &Label) -> Option<Sort> {
    label
        .name
        .strip_prefix("#SemanticCastTo")
        .filter(|name| !name.is_empty())
        .and_then(|name| crate::kast::parser::parse_sort_text(name).ok())
}

fn substitute_sort(sort: &Sort, substitution: &BTreeMap<Sort, Sort>) -> Sort {
    substitution.get(sort).cloned().unwrap_or_else(|| {
        Sort::with_parameters(
            &sort.name,
            sort.parameters
                .iter()
                .map(|parameter| substitute_sort(parameter, substitution))
                .collect(),
        )
    })
}

fn has_rewrite(term: &Term) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| {
        found |= matches!(term, Term::Rewrite { .. });
    });
    found
}

fn rewrite_projection(term: &Term, right: bool) -> Term {
    match term.unannotated() {
        Term::Rewrite {
            left,
            right: rewrite_right,
        } => {
            if right {
                rewrite_projection(rewrite_right, true)
            } else {
                left.as_ref().clone()
            }
        }
        Term::Apply { label, arguments } => {
            let projected = Term::Apply {
                label: label.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| rewrite_projection(argument, right))
                    .collect(),
            };
            copy_metadata(term, compact_injections(projected))
        }
        Term::Sequence(items) => copy_metadata(
            term,
            Term::Sequence(
                items
                    .iter()
                    .map(|item| rewrite_projection(item, right))
                    .collect(),
            ),
        ),
        Term::As { pattern, alias } => {
            if right {
                alias.as_ref().clone()
            } else {
                copy_metadata(
                    term,
                    Term::As {
                        pattern: Box::new(rewrite_projection(pattern, false)),
                        alias: alias.clone(),
                    },
                )
            }
        }
        _ => term.clone(),
    }
}

fn compact_injections(term: Term) -> Term {
    let Term::Apply { label, arguments } = term.unannotated() else {
        return term;
    };
    let [outer_from, outer_to] = label.parameters.as_slice() else {
        return term;
    };
    let [argument] = arguments.as_slice() else {
        return term;
    };
    let Term::Apply {
        label: inner_label,
        arguments: inner_arguments,
    } = argument.unannotated()
    else {
        return term;
    };
    let [inner_from, inner_to] = inner_label.parameters.as_slice() else {
        return term;
    };
    if label.name != "inj" || inner_label.name != "inj" || inner_to != outer_from {
        return term;
    }
    Term::Apply {
        label: Label::with_parameters("inj", vec![inner_from.clone(), outer_to.clone()]),
        arguments: inner_arguments.clone(),
    }
}

fn with_variable_sort(term: &Term, sort: &Sort) -> Term {
    match term.unannotated() {
        Term::Variable { name, .. } => copy_metadata(
            term,
            Term::Variable {
                name: name.clone(),
                sort: Some(sort.clone()),
            },
        ),
        _ => term.clone(),
    }
}

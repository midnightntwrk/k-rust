//! Production-aware insertion of explicit KORE subsort injections.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use serde_json::json;

use crate::definition::{
    Definition, LabelHead, PartialOrder, ProductionCatalog, ProductionId, ResolveError,
    ResolvedDefinition, Sentence, SortCatalog, SortHead, sentence_equivalent,
};
use crate::kast::{Label, Sort, Term};
use crate::provenance::{GeneratingPass, record_generated_origins};

const K_SORT: &str = "K";
const K_ITEM_SORT: &str = "KItem";
const BOOL_SORT: &str = "Bool";
const SORT_PARAMETER: &str = "#SortParam";

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
    InvalidImportedMetadata {
        module: String,
        message: String,
    },
    Sentence {
        module: String,
        sentence: usize,
        source: Option<String>,
        line: Option<u32>,
        error: Box<SortInjectionError>,
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
            Self::InvalidImportedMetadata { module, message } => write!(
                formatter,
                "cannot rebase production metadata from module {module:?}: {message}"
            ),
            Self::Sentence {
                module,
                sentence,
                source,
                line,
                error,
            } => {
                if let Some(source) = source {
                    write!(formatter, "{source}")?;
                    if let Some(line) = line {
                        write!(formatter, ":{line}")?;
                    }
                    write!(formatter, ": ")?;
                } else {
                    write!(formatter, "sentence {sentence} of module {module:?}: ")?;
                }
                error.fmt(formatter)
            }
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
    next_sort_parameter: Cell<usize>,
    used_sort_parameters: RefCell<BTreeSet<String>>,
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
            next_sort_parameter: Cell::new(0),
            used_sort_parameters: RefCell::new(BTreeSet::new()),
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

    pub(crate) fn is_user_list_sort(&self, sort: &Sort) -> bool {
        self.sorts.list_sorts().contains(sort)
    }

    /// Match Java's sentence boundary: rule/claim conditions are always `Bool`.
    pub fn inject_sentence(&self, sentence: &Sentence) -> Result<Sentence, SortInjectionError> {
        self.next_sort_parameter.set(0);
        self.used_sort_parameters.borrow_mut().clear();
        match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } => {
                let body = self.inject_rule_body(body)?;
                let requires = self.inject(requires, &Sort::new(BOOL_SORT))?;
                let ensures = self.inject(ensures, &Sort::new(BOOL_SORT))?;
                Ok(Sentence::Rule {
                    body,
                    requires,
                    ensures,
                    attributes: self.sentence_attributes(attributes),
                })
            }
            Sentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            } => {
                let body = self.inject_rule_body(body)?;
                let requires = self.inject(requires, &Sort::new(BOOL_SORT))?;
                let ensures = self.inject(ensures, &Sort::new(BOOL_SORT))?;
                Ok(Sentence::Claim {
                    body,
                    requires,
                    ensures,
                    attributes: self.sentence_attributes(attributes),
                })
            }
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
        let top = self.fresh_sort_parameter();
        let actual = self.term_sort(&body, Some(&top))?;
        self.inject_with_position(&body, &actual, false)
    }

    fn sentence_attributes(
        &self,
        attributes: &crate::definition::Attributes,
    ) -> crate::definition::Attributes {
        let mut attributes = attributes.clone();
        let parameters = self.used_sort_parameters.borrow();
        if !parameters.is_empty() {
            attributes.insert(
                "sortParams",
                json!({
                    "node": "KSort",
                    "name": "",
                    "params": parameters.iter().map(|name| json!({
                        "node": "KSort",
                        "name": name,
                        "params": [],
                    })).collect::<Vec<_>>(),
                }),
            );
        }
        attributes
    }

    fn fresh_sort_parameter(&self) -> Sort {
        let index = self.next_sort_parameter.get();
        self.next_sort_parameter.set(index + 1);
        Sort::with_parameters(SORT_PARAMETER, vec![Sort::new(format!("Q{index}"))])
    }

    pub fn term_sort(
        &self,
        term: &Term,
        expected: Option<&Sort>,
    ) -> Result<Sort, SortInjectionError> {
        // A semantic cast on an application records the intended overload/context, not a
        // replacement for the selected production's result sort. In particular, `{P}:K` where
        // `P:KItem` must still materialize the KItem-to-K sequence wrapper.
        if !matches!(term.unannotated(), Term::Apply { .. } | Term::Token { .. })
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
                if matches!(
                    label.name.as_str(),
                    "#Top"
                        | "#Bottom"
                        | "#And"
                        | "#Or"
                        | "#Not"
                        | "#Implies"
                        | "#Ceil"
                        | "#Floor"
                        | "#Equals"
                        | "#Exists"
                        | "#Forall"
                        | "#AG"
                        | "weakExistsFinally"
                        | "weakAlwaysFinally"
                ) && self.has_production(term, label)
                {
                    return Ok(self.signature(term, label, arguments, expected)?.result);
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
                let signature = self.signature(term, label, arguments, expected)?;
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
        if let Some(wrapped) = self.user_list_wrapper(&actual, expected, visited.clone()) {
            return Ok(wrapped);
        }
        Ok(injection(actual, expected.clone(), visited))
    }

    fn user_list_wrapper(&self, actual: &Sort, expected: &Sort, visited: Term) -> Option<Term> {
        if !self.is_user_list_sort(expected) || self.is_user_list_sort(actual) {
            return None;
        }
        let mut recursive = self
            .productions
            .productions_for_sort(&SortHead::from(expected))
            .iter()
            .filter_map(|id| match self.productions.production(*id) {
                Sentence::Production {
                    label: Some(label),
                    parameters,
                    sort,
                    items,
                    attributes,
                } if parameters.is_empty()
                    && sort == expected
                    && attributes.get("userList").is_some() =>
                {
                    let arguments = items
                        .iter()
                        .filter_map(|item| match item {
                            crate::definition::ProductionItem::NonTerminal { sort, .. } => {
                                Some(sort)
                            }
                            crate::definition::ProductionItem::Terminal(_)
                            | crate::definition::ProductionItem::RegexTerminal { .. } => None,
                        })
                        .collect::<Vec<_>>();
                    match arguments.as_slice() {
                        [child, list]
                            if *list == expected
                                && (actual == *child
                                    || self.subsorts.less_than_eq(actual, child)) =>
                        {
                            Some((label.clone(), false))
                        }
                        [list, child]
                            if *list == expected
                                && (actual == *child
                                    || self.subsorts.less_than_eq(actual, child)) =>
                        {
                            Some((label.clone(), true))
                        }
                        _ => None,
                    }
                }
                _ => None,
            });
        let (recursive_label, list_first) = recursive.next()?;
        if recursive.next().is_some() {
            return None;
        }

        let mut terminators = self
            .productions
            .productions_for_sort(&SortHead::from(expected))
            .iter()
            .filter_map(|id| match self.productions.production(*id) {
                Sentence::Production {
                    label: Some(label),
                    parameters,
                    sort,
                    items,
                    attributes,
                } if parameters.is_empty()
                    && sort == expected
                    && attributes.get("userList").is_some()
                    && !items.iter().any(|item| {
                        matches!(item, crate::definition::ProductionItem::NonTerminal { .. })
                    }) =>
                {
                    Some(label.clone())
                }
                _ => None,
            });
        let terminator = terminators.next()?;
        if terminators.next().is_some() {
            return None;
        }
        let terminator = Term::Apply {
            label: terminator,
            arguments: Vec::new(),
        };
        let arguments = if list_first {
            vec![terminator, visited]
        } else {
            vec![visited, terminator]
        };
        Some(Term::Apply {
            label: recursive_label,
            arguments,
        })
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
        if actual.name == SORT_PARAMETER
            && let Some(parameter) = actual.parameters.first()
        {
            self.used_sort_parameters
                .borrow_mut()
                .insert(parameter.name.clone());
        }
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
                let signature = self.signature(term, label, arguments, Some(actual))?;
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
                Term::sequence(items)
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
        expected: Option<&Sort>,
    ) -> Result<InstantiatedSignature, SortInjectionError> {
        let expected = term
            .metadata()
            .and_then(|metadata| metadata.sort.as_ref())
            .or(expected);
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
        let substitution = if parameters.is_empty() {
            BTreeMap::new()
        } else {
            let expected = expected
                .cloned()
                .unwrap_or_else(|| self.fresh_sort_parameter());
            let fresh = parameters
                .iter()
                .map(|parameter| {
                    if parameter == sort {
                        expected.clone()
                    } else {
                        self.fresh_sort_parameter()
                    }
                })
                .collect::<Vec<_>>();
            let fresh_substitution = parameters
                .iter()
                .cloned()
                .zip(fresh.iter().cloned())
                .collect::<BTreeMap<_, _>>();
            let mut matches = BTreeMap::<Sort, Vec<Sort>>::new();
            for ((declared, argument), fresh_expected) in argument_sorts.iter().zip(arguments).zip(
                argument_sorts
                    .iter()
                    .map(|sort| substitute_sort(sort, &fresh_substitution)),
            ) {
                let actual = self.term_sort(argument, Some(&fresh_expected))?;
                match_sort(parameters, declared, &actual, &mut matches);
            }
            let result_only_parameter = parameters.iter().any(|parameter| {
                contains_sort(sort, parameter)
                    && !argument_sorts
                        .iter()
                        .any(|argument| contains_sort(argument, parameter))
            });
            if result_only_parameter {
                match_sort(parameters, sort, &expected, &mut matches);
            }
            parameters
                .iter()
                .cloned()
                .zip(fresh)
                .map(|(parameter, fallback)| {
                    let inferred = matches
                        .remove(&parameter)
                        .map(|sorts| self.parametric_lub(&sorts, &fallback))
                        .transpose()?
                        .unwrap_or(fallback);
                    Ok((parameter, inferred))
                })
                .collect::<Result<BTreeMap<_, _>, SortInjectionError>>()?
        };
        let instantiated_parameters = parameters
            .iter()
            .map(|parameter| substitute_sort(parameter, &substitution))
            .collect::<Vec<_>>();
        Ok(InstantiatedSignature {
            label: Label::with_parameters(&label.name, instantiated_parameters),
            arguments: argument_sorts
                .into_iter()
                .map(|sort| substitute_sort(sort, &substitution))
                .collect(),
            result: substitute_sort(sort, &substitution),
        })
    }

    fn has_production(&self, term: &Term, label: &Label) -> bool {
        term.metadata()
            .and_then(|metadata| metadata.production)
            .is_some()
            || !self
                .productions
                .productions_for(&LabelHead::from(label))
                .is_empty()
    }

    fn parametric_lub(&self, sorts: &[Sort], fallback: &Sort) -> Result<Sort, SortInjectionError> {
        let concrete = sorts
            .iter()
            .filter(|sort| sort.name != SORT_PARAMETER)
            .cloned()
            .collect::<Vec<_>>();
        if concrete.is_empty() {
            return Ok(sorts.first().cloned().unwrap_or_else(|| fallback.clone()));
        }
        self.least_upper_bound(
            &concrete,
            (fallback.name != SORT_PARAMETER).then_some(fallback),
        )
    }

    fn production(&self, term: &Term, label: &Label) -> Result<&'a Sentence, SortInjectionError> {
        let mut invalid_resolved = None;
        if let Some(resolved) = term.metadata().and_then(|metadata| metadata.production) {
            if resolved.0 >= self.productions.len() {
                invalid_resolved = Some(SortInjectionError::InvalidResolvedProduction {
                    label: label.name.clone(),
                    production: resolved.0,
                    message: format!(
                        "the active production catalog contains only {} productions",
                        self.productions.len()
                    ),
                });
            } else {
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
                    .is_some_and(|production_label| production_label.name == label.name)
                {
                    return Ok(production);
                }
                invalid_resolved = Some(SortInjectionError::InvalidResolvedProduction {
                    label: label.name.clone(),
                    production: resolved.0,
                    message: "the production belongs to a different KLabel".into(),
                });
            }
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
            [] => Err(invalid_resolved
                .unwrap_or_else(|| SortInjectionError::UnknownLabel(label.name.clone()))),
            [id] => Ok(self.productions.production(*id)),
            ids => Err(
                invalid_resolved.unwrap_or_else(|| SortInjectionError::AmbiguousLabel {
                    label: label.name.clone(),
                    productions: ids.len(),
                }),
            ),
        }
    }

    pub(crate) fn least_upper_bound(
        &self,
        sorts: &[Sort],
        expected: Option<&Sort>,
    ) -> Result<Sort, SortInjectionError> {
        let mut unique = sorts
            .iter()
            .filter(|sort| sort.name != SORT_PARAMETER)
            .cloned()
            .collect::<Vec<_>>();
        if unique.is_empty() {
            return sorts
                .first()
                .cloned()
                .or_else(|| expected.cloned())
                .ok_or_else(|| SortInjectionError::IncompatibleSorts {
                    sorts: Vec::new(),
                    expected: expected.cloned(),
                });
        }
        unique.sort();
        unique.dedup();
        if let [sort] = unique.as_slice() {
            return Ok(sort.clone());
        }
        let mut bounds = self.subsorts.upper_bounds(&unique);
        if let Some(expected) = expected
            && expected.name != SORT_PARAMETER
            && expected.parameters.is_empty()
        {
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

/// Materialize sort injections across the compiled main module and its imports.
pub fn add_sort_injections_to_definition(
    definition: &Definition,
) -> Result<Definition, SortInjectionError> {
    add_sort_injections_to_definition_inner(definition).map(|output| {
        record_generated_origins(definition, output, GeneratingPass::AddSortInjections)
    })
}

fn add_sort_injections_to_definition_inner(
    definition: &Definition,
) -> Result<Definition, SortInjectionError> {
    let resolved =
        ResolvedDefinition::resolve(definition).map_err(SortInjectionError::Definition)?;
    let target = resolved.main_module_id();
    let target_modules = resolved
        .transitive_imports(target)
        .into_iter()
        .chain(std::iter::once(target))
        .collect::<BTreeSet<_>>();
    let target_injector = SortInjector::new(&resolved, definition.main_module.as_str())?;
    let mut output = definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        if !target_modules.contains(&module_id) {
            continue;
        }
        let source_catalog = resolved.production_catalog(module_id);
        for (sentence_index, sentence) in module.local_sentences.iter_mut().enumerate() {
            let mut input = sentence.clone();
            if module_id != target && target_modules.contains(&module_id) {
                super::passes::rebase_sentence(
                    &mut input,
                    &source_catalog,
                    &target_injector.productions,
                    &sentence_equivalent,
                )
                .map_err(|message| {
                    SortInjectionError::InvalidImportedMetadata {
                        module: module.name.clone(),
                        message,
                    }
                })?;
            }
            let mut injected = target_injector.inject_sentence(&input).map_err(|error| {
                SortInjectionError::Sentence {
                    module: module.name.clone(),
                    sentence: sentence_index,
                    source: sentence.attributes().source().map(str::to_owned),
                    line: sentence
                        .attributes()
                        .location()
                        .map(|location| location.start_line),
                    error: Box::new(error),
                }
            })?;
            if module_id != target && target_modules.contains(&module_id) {
                localize_sentence_metadata(
                    &mut injected,
                    &target_injector.productions,
                    &source_catalog,
                );
            }
            *sentence = injected;
        }
    }
    Ok(output)
}

fn localize_sentence_metadata(
    sentence: &mut Sentence,
    source: &ProductionCatalog<'_>,
    target: &ProductionCatalog<'_>,
) {
    let localize = |term: &mut Term| {
        let taken = std::mem::replace(term, Term::Sequence(Vec::new()));
        *term = localize_term_metadata(taken, source, target);
    };
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => {
            localize(body);
            localize(requires);
            localize(ensures);
        }
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => {
            localize(body);
            localize(requires);
        }
        Sentence::Configuration { body, ensures, .. } => {
            localize(body);
            localize(ensures);
        }
        _ => {}
    }
}

fn localize_term_metadata(
    term: Term,
    source: &ProductionCatalog<'_>,
    target: &ProductionCatalog<'_>,
) -> Term {
    let mut metadata = term.metadata().cloned().unwrap_or_default();
    if let Some(resolved) = metadata.production {
        metadata.production = (resolved.0 < source.len())
            .then(|| {
                target.productions().find_map(|(id, candidate)| {
                    sentence_equivalent(source.production(ProductionId(resolved.0)), candidate)
                        .then_some(crate::kast::ResolvedProductionId(id.0))
                })
            })
            .flatten();
    }
    let rebuilt = match term.into_unannotated() {
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(localize_term_metadata(*left, source, target)),
            right: Box::new(localize_term_metadata(*right, source, target)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(localize_term_metadata(*pattern, source, target)),
            alias: Box::new(localize_term_metadata(*alias, source, target)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| localize_term_metadata(item, source, target))
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| localize_term_metadata(argument, source, target))
                .collect(),
        },
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!(),
    };
    rebuilt.with_metadata(metadata)
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

fn contains_sort(sort: &Sort, needle: &Sort) -> bool {
    sort == needle
        || sort
            .parameters
            .iter()
            .any(|parameter| contains_sort(parameter, needle))
}

fn match_sort(
    formal_parameters: &[Sort],
    declared: &Sort,
    actual: &Sort,
    matches: &mut BTreeMap<Sort, Vec<Sort>>,
) {
    if formal_parameters.contains(declared) {
        matches
            .entry(declared.clone())
            .or_default()
            .push(actual.clone());
        return;
    }
    if declared.name == actual.name && declared.parameters.len() == actual.parameters.len() {
        for (declared, actual) in declared.parameters.iter().zip(&actual.parameters) {
            match_sort(formal_parameters, declared, actual, matches);
        }
    }
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
            Term::sequence(items.iter().map(|item| rewrite_projection(item, right))),
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

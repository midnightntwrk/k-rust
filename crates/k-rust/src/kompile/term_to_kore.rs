//! Conversion from user-facing K terms to backend-facing KORE patterns.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::definition::{
    Definition, LabelHead, PartialOrder, ProductionCatalog, ProductionId, ResolveError,
    ResolvedDefinition, Sentence, SortCatalog, SortHead,
};
use crate::kast::{self, Label, Sort, Term};
use crate::kore::ast::{Pattern, Symbol, Variable, VariableKind};

use super::module_to_kore::{encode_kore_identifier, encode_kore_label};

/// A failure to recover information required by KORE from the compact public KAST.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TermConversionError {
    Definition(ResolveError),
    MissingModule(String),
    CircularSubsort(Vec<Sort>),
    UnsupportedInjectedLabel,
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
    MissingSort(&'static str),
    IncompatibleSorts {
        left: Sort,
        right: Sort,
    },
    AmbiguousCommonSort {
        left: Sort,
        right: Sort,
        sorts: Vec<Sort>,
    },
    InvalidBuiltin {
        label: String,
        message: String,
    },
    InvalidToken {
        sort: Sort,
        message: String,
    },
}

impl fmt::Display for TermConversionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition(error) => error.fmt(formatter),
            Self::MissingModule(module) => {
                write!(formatter, "KORE source module {module:?} was not found")
            }
            Self::CircularSubsort(path) => write!(
                formatter,
                "cannot convert terms with circular subsorts: {}",
                path.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" > ")
            ),
            Self::UnsupportedInjectedLabel => {
                formatter.write_str("cannot translate an injected KLabel to KORE")
            }
            Self::UnknownLabel(label) => {
                write!(formatter, "cannot determine the sort of KLabel {label:?}")
            }
            Self::AmbiguousLabel { label, productions } => write!(
                formatter,
                "cannot determine the sort of overloaded KLabel {label:?} from {productions} productions"
            ),
            Self::InvalidResolvedProduction {
                label,
                production,
                message,
            } => write!(
                formatter,
                "resolved production #{production} for KLabel {label:?} is invalid: {message}"
            ),
            Self::MissingSort(construct) => {
                write!(formatter, "{construct} has no recoverable sort")
            }
            Self::IncompatibleSorts { left, right } => {
                write!(
                    formatter,
                    "sorts {left} and {right} have no common upper bound"
                )
            }
            Self::AmbiguousCommonSort { left, right, sorts } => write!(
                formatter,
                "sorts {left} and {right} have multiple least common upper bounds: {}",
                sorts
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::InvalidBuiltin { label, message } => {
                write!(formatter, "invalid {label} application: {message}")
            }
            Self::InvalidToken { sort, message } => {
                write!(formatter, "invalid {sort} token: {message}")
            }
        }
    }
}

impl std::error::Error for TermConversionError {}

/// Converts terms using the productions, sort hooks, and subsorts visible from a module.
#[derive(Clone, Debug)]
pub struct TermConverter<'a> {
    productions: ProductionCatalog<'a>,
    sorts: SortCatalog<'a>,
    subsorts: PartialOrder<Sort>,
    sort_variables: BTreeSet<String>,
}

impl<'a> TermConverter<'a> {
    pub fn new(
        definition: &'a ResolvedDefinition,
        module: &str,
    ) -> Result<Self, TermConversionError> {
        let module = definition
            .module_id(module)
            .ok_or_else(|| TermConversionError::MissingModule(module.to_owned()))?;
        let subsorts = definition
            .subsorts(module)
            .map_err(|cycle| TermConversionError::CircularSubsort(cycle.path))?;
        Ok(Self {
            productions: definition.production_catalog(module),
            sorts: definition.sort_catalog(module),
            subsorts,
            sort_variables: BTreeSet::new(),
        })
    }

    /// Treat the supplied K sort names as KORE sort variables during conversion.
    pub fn with_sort_variables(&self, variables: impl IntoIterator<Item = String>) -> Self {
        let mut converter = self.clone();
        converter.sort_variables = variables.into_iter().collect();
        converter
    }

    pub fn convert(&self, term: &Term) -> Result<Pattern, TermConversionError> {
        self.pattern(term)
    }

    pub fn convert_sort(&self, sort: &Sort) -> crate::kore::ast::Sort {
        self.kore_sort(sort)
    }

    pub fn convert_label(&self, label: &Label) -> Symbol {
        let mut symbol = encode_kore_label(label);
        symbol.sort_parameters = label
            .parameters
            .iter()
            .map(|sort| self.kore_sort(sort))
            .collect();
        symbol
    }

    pub(crate) fn infer_sort(&self, term: &Term) -> Result<Sort, TermConversionError> {
        self.term_sort(term)
    }

    fn pattern(&self, term: &Term) -> Result<Pattern, TermConversionError> {
        match term.unannotated() {
            Term::InjectedLabel(_) => Err(TermConversionError::UnsupportedInjectedLabel),
            Term::Rewrite { left, right } => {
                let sort = self.common_sort(&self.term_sort(left)?, &self.term_sort(right)?)?;
                Ok(Pattern::Rewrites {
                    sort: self.kore_sort(&sort),
                    left: Box::new(self.pattern(left)?),
                    right: Box::new(self.pattern(right)?),
                })
            }
            Term::As { pattern, alias } => {
                let sort = self.common_sort(&self.term_sort(pattern)?, &self.term_sort(alias)?)?;
                Ok(Pattern::And {
                    sort: self.kore_sort(&sort),
                    arguments: vec![self.pattern(pattern)?, self.pattern(alias)?],
                })
            }
            Term::Variable { name, sort } => Ok(Pattern::Variable(self.variable(name, sort))),
            Term::Sequence(items) => self.sequence(items),
            Term::Apply { label, arguments } => self.application(label, arguments),
            Term::Token { token, sort } => Ok(Pattern::DomainValue {
                sort: self.kore_sort(sort),
                value: self.token_value(token, sort)?,
            }),
            Term::Annotated { .. } => unreachable!(),
        }
    }

    fn application(
        &self,
        label: &Label,
        arguments: &[Term],
    ) -> Result<Pattern, TermConversionError> {
        let patterns = || {
            arguments
                .iter()
                .map(|argument| self.pattern(argument))
                .collect::<Result<Vec<_>, _>>()
        };
        match label.name.as_str() {
            "#Top" => {
                self.require_arity(label, arguments, 0)?;
                Ok(Pattern::Top {
                    sort: self.parameter(label, 0)?,
                })
            }
            "#Bottom" => {
                self.require_arity(label, arguments, 0)?;
                Ok(Pattern::Bottom {
                    sort: self.parameter(label, 0)?,
                })
            }
            "#And" => Ok(Pattern::And {
                sort: self.parameter(label, 0)?,
                arguments: patterns()?,
            }),
            "#Or" => Ok(Pattern::Or {
                sort: self.parameter(label, 0)?,
                arguments: patterns()?,
            }),
            "#Not" => {
                self.require_arity(label, arguments, 1)?;
                Ok(Pattern::Not {
                    sort: self.parameter(label, 0)?,
                    argument: Box::new(self.pattern(&arguments[0])?),
                })
            }
            "#Implies" => {
                self.require_arity(label, arguments, 2)?;
                Ok(Pattern::Implies {
                    sort: self.parameter(label, 0)?,
                    left: Box::new(self.pattern(&arguments[0])?),
                    right: Box::new(self.pattern(&arguments[1])?),
                })
            }
            "#Ceil" | "#Floor" => {
                self.require_arity(label, arguments, 1)?;
                let operand_sort = self.parameter(label, 0)?;
                let result_sort = self.parameter(label, 1)?;
                let argument = Box::new(self.pattern(&arguments[0])?);
                if label.name == "#Ceil" {
                    Ok(Pattern::Ceil {
                        operand_sort,
                        result_sort,
                        argument,
                    })
                } else {
                    Ok(Pattern::Floor {
                        operand_sort,
                        result_sort,
                        argument,
                    })
                }
            }
            "#Equals" => {
                self.require_arity(label, arguments, 2)?;
                Ok(Pattern::Equals {
                    operand_sort: self.parameter(label, 0)?,
                    result_sort: self.parameter(label, 1)?,
                    left: Box::new(self.pattern(&arguments[0])?),
                    right: Box::new(self.pattern(&arguments[1])?),
                })
            }
            "#Exists" | "#Forall" => self.quantifier(label, arguments),
            "#AG" => Ok(Pattern::Application {
                symbol: Symbol {
                    name: "allPathGlobally".into(),
                    sort_parameters: label
                        .parameters
                        .iter()
                        .map(|sort| self.kore_sort(sort))
                        .collect(),
                },
                arguments: patterns()?,
            }),
            "weakExistsFinally" | "weakAlwaysFinally" => Ok(Pattern::Application {
                symbol: Symbol {
                    name: label.name.clone(),
                    sort_parameters: label
                        .parameters
                        .iter()
                        .map(|sort| self.kore_sort(sort))
                        .collect(),
                },
                arguments: patterns()?,
            }),
            _ => Ok(Pattern::Application {
                symbol: self.convert_label(label),
                arguments: patterns()?,
            }),
        }
    }

    fn quantifier(
        &self,
        label: &Label,
        arguments: &[Term],
    ) -> Result<Pattern, TermConversionError> {
        self.require_arity(label, arguments, 2)?;
        let Term::Variable { name, sort } = arguments[0].unannotated() else {
            return Err(TermConversionError::InvalidBuiltin {
                label: label.name.clone(),
                message: "the first argument must be a variable".into(),
            });
        };
        let variable = self.variable(name, sort);
        let sort = self.parameter(label, label.parameters.len().saturating_sub(1))?;
        let body = Box::new(self.pattern(&arguments[1])?);
        if label.name == "#Exists" {
            Ok(Pattern::Exists {
                sort,
                variable,
                body,
            })
        } else {
            Ok(Pattern::Forall {
                sort,
                variable,
                body,
            })
        }
    }

    fn parameter(
        &self,
        label: &Label,
        index: usize,
    ) -> Result<crate::kore::ast::Sort, TermConversionError> {
        label
            .parameters
            .get(index)
            .map(|sort| self.kore_sort(sort))
            .ok_or_else(|| TermConversionError::InvalidBuiltin {
                label: label.name.clone(),
                message: format!("missing sort parameter {}", index + 1),
            })
    }

    fn require_arity(
        &self,
        label: &Label,
        arguments: &[Term],
        expected: usize,
    ) -> Result<(), TermConversionError> {
        if arguments.len() == expected {
            Ok(())
        } else {
            Err(TermConversionError::InvalidBuiltin {
                label: label.name.clone(),
                message: format!("expected {expected} arguments, found {}", arguments.len()),
            })
        }
    }

    fn sequence(&self, items: &[Term]) -> Result<Pattern, TermConversionError> {
        let Some((last, prefix)) = items.split_last() else {
            return Ok(application("dotk", Vec::new()));
        };
        let mut result = if self.term_sort(last)? == Sort::new("K") {
            self.pattern(last)?
        } else {
            application(
                "kseq",
                vec![self.pattern(last)?, application("dotk", Vec::new())],
            )
        };
        for item in prefix.iter().rev() {
            let symbol = if self.term_sort(item)? == Sort::new("K") {
                "append"
            } else {
                "kseq"
            };
            result = application(symbol, vec![self.pattern(item)?, result]);
        }
        Ok(result)
    }

    fn variable(&self, name: &str, sort: &Option<Sort>) -> Variable {
        let (kind, name) = name.strip_prefix('@').map_or_else(
            || {
                (
                    VariableKind::Element,
                    format!("Var{}", encode_kore_identifier(name)),
                )
            },
            |name| {
                (
                    VariableKind::Set,
                    format!("@Var{}", encode_kore_identifier(name)),
                )
            },
        );
        Variable {
            kind,
            name,
            sort: self.kore_sort(sort.as_ref().unwrap_or(&Sort::new("K"))),
        }
    }

    fn kore_sort(&self, sort: &Sort) -> crate::kore::ast::Sort {
        if sort.parameters.is_empty() && self.sort_variables.contains(&sort.name) {
            crate::kore::ast::Sort::Variable(sort.name.clone())
        } else {
            crate::kore::ast::Sort::Application {
                name: format!("Sort{}", encode_kore_identifier(&sort.name)),
                arguments: sort
                    .parameters
                    .iter()
                    .map(|parameter| self.kore_sort(parameter))
                    .collect(),
            }
        }
    }

    fn token_value(&self, token: &str, sort: &Sort) -> Result<String, TermConversionError> {
        let hook = self
            .sorts
            .attributes_for(&SortHead::from(sort))
            .and_then(|attributes| attributes.get_str("hook"));
        match hook {
            Some("STRING.String") => self.unquote_token(token, sort),
            Some("BYTES.Bytes") => token
                .strip_prefix('b')
                .ok_or_else(|| TermConversionError::InvalidToken {
                    sort: sort.clone(),
                    message: "expected a leading `b`".into(),
                })
                .and_then(|token| self.unquote_token(token, sort)),
            _ => Ok(token.to_owned()),
        }
    }

    fn unquote_token(&self, token: &str, sort: &Sort) -> Result<String, TermConversionError> {
        kast::string::unquote(token).map_err(|message| TermConversionError::InvalidToken {
            sort: sort.clone(),
            message,
        })
    }

    fn term_sort(&self, term: &Term) -> Result<Sort, TermConversionError> {
        if let Some(sort) = term.metadata().and_then(|metadata| metadata.sort.clone()) {
            return Ok(sort);
        }
        match term.unannotated() {
            Term::InjectedLabel(_) => Err(TermConversionError::UnsupportedInjectedLabel),
            Term::Rewrite { left, right }
            | Term::As {
                pattern: left,
                alias: right,
            } => self.common_sort(&self.term_sort(left)?, &self.term_sort(right)?),
            Term::Variable { sort, .. } => sort
                .clone()
                .ok_or(TermConversionError::MissingSort("variable")),
            Term::Sequence(_) => Ok(Sort::new("K")),
            Term::Token { sort, .. } => Ok(sort.clone()),
            Term::Apply { label, arguments } => self.application_sort(term, label, arguments),
            Term::Annotated { .. } => unreachable!(),
        }
    }

    fn application_sort(
        &self,
        term: &Term,
        label: &Label,
        arguments: &[Term],
    ) -> Result<Sort, TermConversionError> {
        if let Some(sort) = semantic_cast_sort(label) {
            return Ok(sort);
        }
        if label.name == "#OuterCast" {
            return arguments
                .first()
                .ok_or_else(|| invalid_sort(label))
                .and_then(|argument| self.term_sort(argument));
        }
        match label.name.as_str() {
            "inj" => {
                return label
                    .parameters
                    .get(1)
                    .cloned()
                    .ok_or_else(|| invalid_sort(label));
            }
            "#Ceil" | "#Floor" | "#Equals" => {
                return label
                    .parameters
                    .get(1)
                    .cloned()
                    .ok_or_else(|| invalid_sort(label));
            }
            "#Top" | "#Bottom" | "#And" | "#Or" | "#Not" | "#Implies" | "#AG"
            | "weakExistsFinally" | "weakAlwaysFinally" => {
                return label
                    .parameters
                    .first()
                    .cloned()
                    .ok_or_else(|| invalid_sort(label));
            }
            "#Exists" | "#Forall" => {
                return label
                    .parameters
                    .last()
                    .cloned()
                    .ok_or_else(|| invalid_sort(label));
            }
            _ => {}
        }
        if let Some(resolved) = term.metadata().and_then(|metadata| metadata.production) {
            if resolved.0 >= self.productions.len() {
                return Err(TermConversionError::InvalidResolvedProduction {
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
                parameters,
                sort,
                ..
            } = production
            else {
                unreachable!()
            };
            if production_label
                .as_ref()
                .is_none_or(|production_label| production_label.name != label.name)
            {
                return Err(TermConversionError::InvalidResolvedProduction {
                    label: label.name.clone(),
                    production: resolved.0,
                    message: "the production belongs to a different KLabel".into(),
                });
            }
            return Ok(production_result_sort(parameters, sort, label));
        }

        let ids = self.productions.productions_for(&LabelHead::from(label));
        if ids.is_empty() {
            return Err(TermConversionError::UnknownLabel(label.name.clone()));
        }
        if ids.len() != 1 {
            return Err(TermConversionError::AmbiguousLabel {
                label: label.name.clone(),
                productions: ids.len(),
            });
        }
        let Sentence::Production {
            parameters, sort, ..
        } = self.productions.production(ids[0])
        else {
            unreachable!()
        };
        Ok(production_result_sort(parameters, sort, label))
    }

    fn common_sort(&self, left: &Sort, right: &Sort) -> Result<Sort, TermConversionError> {
        if self.subsorts.less_than_eq(left, right) {
            return Ok(right.clone());
        }
        if self.subsorts.less_than_eq(right, left) {
            return Ok(left.clone());
        }
        let bounds = self.subsorts.upper_bounds([left, right]);
        if bounds.is_empty() {
            return Err(TermConversionError::IncompatibleSorts {
                left: left.clone(),
                right: right.clone(),
            });
        }
        let minima = self.subsorts.minimal(&bounds);
        if minima.len() == 1 {
            Ok(minima.into_iter().next().expect("one minimum"))
        } else {
            Err(TermConversionError::AmbiguousCommonSort {
                left: left.clone(),
                right: right.clone(),
                sorts: minima.into_iter().collect(),
            })
        }
    }
}

/// Resolve a definition and convert one K term in the selected module.
pub fn term_to_kore(
    definition: &Definition,
    module: &str,
    term: &Term,
) -> Result<Pattern, TermConversionError> {
    let resolved =
        ResolvedDefinition::resolve(definition).map_err(TermConversionError::Definition)?;
    term_to_kore_from_resolved(&resolved, module, term)
}

/// Convert one K term while reusing an already-resolved definition.
pub fn term_to_kore_from_resolved(
    definition: &ResolvedDefinition,
    module: &str,
    term: &Term,
) -> Result<Pattern, TermConversionError> {
    TermConverter::new(definition, module)?.convert(term)
}

fn application(name: &str, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: name.into(),
            sort_parameters: Vec::new(),
        },
        arguments,
    }
}

fn semantic_cast_sort(label: &Label) -> Option<Sort> {
    label
        .name
        .strip_prefix("#SemanticCastTo")
        .filter(|name| !name.is_empty())
        .and_then(|name| kast::parser::parse_sort_text(name).ok())
}

fn invalid_sort(label: &Label) -> TermConversionError {
    TermConversionError::InvalidBuiltin {
        label: label.name.clone(),
        message: "missing result sort parameter".into(),
    }
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

fn production_result_sort(parameters: &[Sort], sort: &Sort, label: &Label) -> Sort {
    let substitution = parameters
        .iter()
        .cloned()
        .zip(label.parameters.iter().cloned())
        .collect::<BTreeMap<_, _>>();
    substitute_sort(sort, &substitution)
}

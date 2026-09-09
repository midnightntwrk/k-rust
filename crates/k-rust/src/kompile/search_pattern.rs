//! Compilation of one surface K search pattern into a verified-shape KORE target.

use std::collections::BTreeSet;
use std::fmt;

use crate::definition::{Attributes, ResolvedDefinition, Sentence, sentence_equivalent};
use crate::inner::{RuleError, parse_rule_content};
use crate::kast::{Sort, Term};
use crate::kore::ast::{Pattern, VariableKind};

use super::fresh_names::GeneratedVariableIdentity;
use super::passes::{
    expand_macros_in_terms_from_resolved, rebase_sentence, resolve_anon_vars_in_sentence,
    resolve_semantic_casts_with_predicates_in_sentence,
};
use super::sort_injections::{SortInjectionError, SortInjector, rewrite_projection};
use super::term_to_kore::{TermConversionError, TermConverter};
use super::{ConcretizeCellsError, concretize_cells_in_sentence, encode_kore_identifier};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct KoreVariableIdentity {
    pub kind: VariableKind,
    pub name: String,
}

impl KoreVariableIdentity {
    pub fn element(name: impl Into<String>) -> Self {
        Self {
            kind: VariableKind::Element,
            name: name.into(),
        }
    }

    pub fn set(name: impl Into<String>) -> Self {
        Self {
            kind: VariableKind::Set,
            name: name.into(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompiledSearchPattern {
    pub pattern: Pattern,
    pub generated_anonymous_variables: BTreeSet<KoreVariableIdentity>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CompileSearchPatternError {
    Rule(RuleError),
    MissingExecutionModule(String),
    ProductionRebase(String),
    CellConcretization(ConcretizeCellsError),
    MacroExpansion(String),
    SortInjection(SortInjectionError),
    TermConversion(TermConversionError),
    ExpectedGeneratedTopCell { actual: Sort },
}

impl fmt::Display for CompileSearchPatternError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Rule(error) => error.fmt(formatter),
            Self::MissingExecutionModule(module) => {
                write!(
                    formatter,
                    "compiled execution module {module:?} was not found"
                )
            }
            Self::ProductionRebase(message) => {
                write!(
                    formatter,
                    "could not rebase parsed pattern productions: {message}"
                )
            }
            Self::CellConcretization(error) => error.fmt(formatter),
            Self::MacroExpansion(message) => {
                write!(
                    formatter,
                    "search-pattern macro expansion failed: {message}"
                )
            }
            Self::SortInjection(error) => error.fmt(formatter),
            Self::TermConversion(error) => error.fmt(formatter),
            Self::ExpectedGeneratedTopCell { actual } => write!(
                formatter,
                "search pattern body has sort {actual}; expected GeneratedTopCell"
            ),
        }
    }
}

impl std::error::Error for CompileSearchPatternError {}

impl From<RuleError> for CompileSearchPatternError {
    fn from(error: RuleError) -> Self {
        Self::Rule(error)
    }
}

impl From<ConcretizeCellsError> for CompileSearchPatternError {
    fn from(error: ConcretizeCellsError) -> Self {
        Self::CellConcretization(error)
    }
}

impl From<SortInjectionError> for CompileSearchPatternError {
    fn from(error: SortInjectionError) -> Self {
        Self::SortInjection(error)
    }
}

impl From<TermConversionError> for CompileSearchPatternError {
    fn from(error: TermConversionError) -> Self {
        Self::TermConversion(error)
    }
}

/// Compile a complete `#RuleContent` surface pattern in the parsing and execution contexts
/// produced by one definition compilation.
pub fn compile_search_pattern(
    parsing_definition: &ResolvedDefinition,
    execution_definition: &ResolvedDefinition,
    module: &str,
    contents: &str,
    attributes: Attributes,
) -> Result<CompiledSearchPattern, CompileSearchPatternError> {
    let mut sentence = parse_rule_content(parsing_definition, module, contents, attributes)?;
    let parsing_module = parsing_definition
        .module_id(module)
        .expect("parse_rule_content checked the parsing module");
    let execution_module = execution_definition
        .module_id(module)
        .ok_or_else(|| CompileSearchPatternError::MissingExecutionModule(module.to_owned()))?;
    rebase_sentence(
        &mut sentence,
        &parsing_definition.production_catalog(parsing_module),
        &execution_definition.production_catalog(execution_module),
        &sentence_equivalent,
    )
    .map_err(CompileSearchPatternError::ProductionRebase)?;

    let (sentence, mut generated) = resolve_anon_vars_in_sentence(sentence);
    let sentence = resolve_semantic_casts_with_predicates_in_sentence(sentence);
    let (sentence, cell_generated) =
        concretize_cells_in_sentence(execution_definition, module, sentence)?;
    generated.extend(cell_generated);

    let Sentence::Rule {
        body,
        requires,
        ensures: _,
        attributes: _,
    } = sentence
    else {
        unreachable!("parse_rule_content always returns a Rule sentence")
    };
    let body = rewrite_projection(&body, false);
    let expanded =
        expand_macros_in_terms_from_resolved(execution_definition, module, vec![body, requires])
            .map_err(CompileSearchPatternError::MacroExpansion)?;
    generated.extend(expanded.generated_variables);
    let [body, requires]: [Term; 2] = expanded
        .terms
        .try_into()
        .expect("two input roots produce two expanded roots");

    let top = Sort::new("GeneratedTopCell");
    let bool_sort = Sort::new("Bool");
    let injector = SortInjector::new(execution_definition, module)?;
    let actual = injector.term_sort(&body, None)?;
    if actual != top {
        return Err(CompileSearchPatternError::ExpectedGeneratedTopCell { actual });
    }
    let body = injector.inject(&body, &top)?;
    let requires_is_true = is_true(&requires);
    let requires = (!requires_is_true)
        .then(|| injector.inject(&requires, &bool_sort))
        .transpose()?;

    let converter =
        TermConverter::new_with_generated_anonymous(execution_definition, module, &generated)?;
    let body = converter.convert(&body)?;
    let top_kore = converter.convert_sort(&top);
    let bool_kore = converter.convert_sort(&bool_sort);
    let condition = if let Some(requires) = requires {
        Pattern::Equals {
            operand_sort: bool_kore.clone(),
            result_sort: top_kore.clone(),
            left: Box::new(converter.convert(&requires)?),
            right: Box::new(Pattern::DomainValue {
                sort: bool_kore,
                value: "true".into(),
            }),
        }
    } else {
        Pattern::Top {
            sort: top_kore.clone(),
        }
    };
    let pattern = Pattern::And {
        sort: top_kore,
        arguments: vec![body, condition],
    };

    let occurring = variable_identities(&pattern);
    let generated_anonymous_variables = generated
        .into_iter()
        .map(encode_generated_identity)
        .filter(|identity| occurring.contains(identity))
        .collect();
    Ok(CompiledSearchPattern {
        pattern,
        generated_anonymous_variables,
    })
}

fn is_true(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Token { token, sort } if token == "true" && sort == &Sort::new("Bool")
    )
}

fn encode_generated_identity(identity: GeneratedVariableIdentity) -> KoreVariableIdentity {
    match identity.kind {
        VariableKind::Element => {
            KoreVariableIdentity::element(format!("Var{}", encode_kore_identifier(&identity.name)))
        }
        VariableKind::Set => {
            let name = identity.name.strip_prefix('@').unwrap_or(&identity.name);
            KoreVariableIdentity::set(format!("@Var{}", encode_kore_identifier(name)))
        }
    }
}

fn variable_identities(pattern: &Pattern) -> BTreeSet<KoreVariableIdentity> {
    fn collect(pattern: &Pattern, output: &mut BTreeSet<KoreVariableIdentity>) {
        match pattern {
            Pattern::Variable(variable) => {
                output.insert(KoreVariableIdentity {
                    kind: variable.kind,
                    name: variable.name.clone(),
                });
            }
            Pattern::Application { arguments, .. }
            | Pattern::And { arguments, .. }
            | Pattern::Or { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. } => {
                for argument in arguments {
                    collect(argument, output);
                }
            }
            Pattern::Not { argument, .. }
            | Pattern::Next { argument, .. }
            | Pattern::Ceil { argument, .. }
            | Pattern::Floor { argument, .. } => collect(argument, output),
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. }
            | Pattern::Equals { left, right, .. }
            | Pattern::In { left, right, .. } => {
                collect(left, output);
                collect(right, output);
            }
            Pattern::Exists { variable, body, .. }
            | Pattern::Forall { variable, body, .. }
            | Pattern::Mu { variable, body }
            | Pattern::Nu { variable, body } => {
                output.insert(KoreVariableIdentity {
                    kind: variable.kind,
                    name: variable.name.clone(),
                });
                collect(body, output);
            }
            Pattern::String(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => {}
        }
    }

    let mut output = BTreeSet::new();
    collect(pattern, &mut output);
    output
}

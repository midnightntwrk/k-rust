//! Ordered frontend compilation passes that transform flat definitions.

use std::fmt;

use crate::{
    definition::{
        Definition, LabelHead, ProductionCatalog, ResolvedDefinition, Sentence, sentence_equivalent,
    },
    diagnostic::{Diagnostic, DiagnosticCode},
    kast::{ResolvedProductionId, Term},
};

mod add_implicit_computation_cell;
mod check_simplification;
mod concretize_cells;
mod constant_folding;
mod expand_macros;
mod generate_sort_helpers;
mod guard_or_patterns;
mod number_sentences;
mod propagate_macro;
mod resolve_anon_vars;
mod resolve_contexts;
mod resolve_fresh_config_constants;
mod resolve_fresh_constants;
mod resolve_fun;
mod resolve_function_with_config;
mod resolve_heat_cool;
mod resolve_io;
mod resolve_semantic_casts;
mod resolve_strict;
mod subsort_kitem;

pub use add_implicit_computation_cell::add_implicit_computation_cell;
pub use check_simplification::{CheckSimplificationError, check_simplification_rules};
pub use concretize_cells::{ConcretizeCellsError, concretize_cells};
pub use constant_folding::{ConstantFoldingError, constant_fold};
pub use expand_macros::{ExpandMacrosError, expand_macros};
pub use generate_sort_helpers::{generate_sort_predicate_syntax, generate_sort_projections};
pub use guard_or_patterns::guard_or_patterns;
pub use number_sentences::number_sentences;
pub use propagate_macro::propagate_macro_attributes;
pub use resolve_anon_vars::resolve_anon_vars;
pub use resolve_contexts::{ResolveContextsError, resolve_contexts};
pub use resolve_fresh_config_constants::{
    ResolveFreshConfigConstantsError, resolve_fresh_config_constants,
};
pub use resolve_fresh_constants::{ResolveFreshConstantsError, resolve_fresh_constants};
pub use resolve_fun::{ResolveFunError, resolve_fun};
pub use resolve_function_with_config::{
    ResolveFunctionWithConfigError, resolve_config_var, resolve_function_with_config,
};
pub use resolve_heat_cool::{ResolveHeatCoolError, resolve_heat_cool_attributes};
pub use resolve_io::{ResolveIoError, resolve_io};
pub use resolve_semantic_casts::resolve_semantic_casts;
pub use resolve_strict::{ResolveStrictError, resolve_strict};
pub use subsort_kitem::{SubsortKItemError, subsort_kitem};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveCommError {
    pub diagnostics: Vec<Diagnostic>,
}

/// Rebase parser production indexes after a pass adds or removes productions.
///
/// Parsed terms intentionally store compact catalog indexes. Compilation passes preserve those
/// terms while changing the catalog around them, so every production-changing pass must translate
/// surviving indexes before the next resolved-definition boundary.
fn rebase_local_metadata(before: &Definition, after: Definition) -> Result<Definition, String> {
    rebase_local_metadata_by(before, after, sentence_equivalent)
}

fn rebase_local_metadata_by(
    before: &Definition,
    mut after: Definition,
    production_matches: impl Fn(&Sentence, &Sentence) -> bool,
) -> Result<Definition, String> {
    let before = ResolvedDefinition::resolve(before).map_err(|error| error.to_string())?;
    let after_resolved = ResolvedDefinition::resolve(&after).map_err(|error| error.to_string())?;
    for module in &mut after.modules {
        let Some(before_module) = before.module_id(&module.name) else {
            continue;
        };
        let Some(after_module) = after_resolved.module_id(&module.name) else {
            continue;
        };
        let source = before.production_catalog(before_module);
        let target = after_resolved.production_catalog(after_module);
        for sentence in &mut module.local_sentences {
            rebase_sentence(sentence, &source, &target, &production_matches)?;
        }
    }
    Ok(after)
}

fn rebase_sentence(
    sentence: &mut Sentence,
    source: &ProductionCatalog<'_>,
    target: &ProductionCatalog<'_>,
    production_matches: &impl Fn(&Sentence, &Sentence) -> bool,
) -> Result<(), String> {
    let rebase = |term: &mut Term| {
        let taken = std::mem::replace(term, Term::Sequence(Vec::new()));
        *term = rebase_term(taken, source, target, production_matches)?;
        Ok::<_, String>(())
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
            rebase(body)?;
            rebase(requires)?;
            rebase(ensures)?;
        }
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => {
            rebase(body)?;
            rebase(requires)?;
        }
        Sentence::Configuration { body, ensures, .. } => {
            rebase(body)?;
            rebase(ensures)?;
        }
        _ => {}
    }
    Ok(())
}

fn rebase_term(
    term: Term,
    source: &ProductionCatalog<'_>,
    target: &ProductionCatalog<'_>,
    production_matches: &impl Fn(&Sentence, &Sentence) -> bool,
) -> Result<Term, String> {
    let mut metadata = term.metadata().cloned().unwrap_or_default();
    if let Some(ResolvedProductionId(index)) = metadata.production {
        if index >= source.len() {
            return Err(format!(
                "production metadata #{index} exceeds source catalog length {}",
                source.len()
            ));
        }
        let production = source.production(crate::definition::ProductionId(index));
        let rebased = target
            .productions()
            .find_map(|(id, candidate)| production_matches(production, candidate).then_some(id))
            .ok_or_else(|| {
                format!(
                    "source production metadata #{index} has no equivalent in the transformed catalog"
                )
            })?;
        metadata.production = Some(ResolvedProductionId(rebased.0));
    }
    let rebuilt = match term.into_unannotated() {
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(rebase_term(*left, source, target, production_matches)?),
            right: Box::new(rebase_term(*right, source, target, production_matches)?),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rebase_term(*pattern, source, target, production_matches)?),
            alias: Box::new(rebase_term(*alias, source, target, production_matches)?),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| rebase_term(item, source, target, production_matches))
                .collect::<Result<_, _>>()?,
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| rebase_term(argument, source, target, production_matches))
                .collect::<Result<_, _>>()?,
        },
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!(),
    };
    Ok(rebuilt.with_metadata(metadata))
}

impl fmt::Display for ResolveCommError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "commutative simplification resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveCommError {}

/// Duplicate commutative simplification rules with the matched LHS arguments reversed.
///
/// This is Java's first KORE backend pass. The rule-level `comm` attribute is removed because the
/// backend assigns it a different meaning; the production itself must also carry `comm`.
pub fn resolve_comm(definition: &Definition) -> Result<Definition, ResolveCommError> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| ResolveCommError {
        diagnostics: vec![Diagnostic {
            severity: crate::diagnostic::Severity::Error,
            code: DiagnosticCode::InvalidCommutativeSimplification,
            message: error.to_string(),
            source: None,
            location: None,
        }],
    })?;
    let mut output = definition.clone();
    let mut diagnostics = Vec::new();

    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = resolved.production_catalog(module_id);
        let mut sentences = Vec::with_capacity(module.local_sentences.len());
        for sentence in &module.local_sentences {
            let Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } = sentence
            else {
                sentences.push(sentence.clone());
                continue;
            };
            if attributes.get("simplification").is_none() || attributes.get("comm").is_none() {
                sentences.push(sentence.clone());
                continue;
            }

            let mut attributes = attributes.clone();
            attributes.remove("comm");
            let swapped = commute_lhs(body, true, &productions, sentence, &mut diagnostics);
            if swapped != *body {
                sentences.push(Sentence::Rule {
                    body: swapped,
                    requires: requires.clone(),
                    ensures: ensures.clone(),
                    attributes: attributes.clone(),
                });
            }
            sentences.push(Sentence::Rule {
                body: body.clone(),
                requires: requires.clone(),
                ensures: ensures.clone(),
                attributes,
            });
        }
        module.local_sentences = sentences;
    }

    if diagnostics.is_empty() {
        Ok(output)
    } else {
        diagnostics.sort();
        Err(ResolveCommError { diagnostics })
    }
}

fn commute_lhs(
    term: &Term,
    on_lhs: bool,
    productions: &crate::definition::ProductionCatalog<'_>,
    sentence: &Sentence,
    diagnostics: &mut Vec<Diagnostic>,
) -> Term {
    match term {
        Term::Annotated { term, metadata } => {
            commute_lhs(term, on_lhs, productions, sentence, diagnostics)
                .with_metadata(metadata.clone())
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(commute_lhs(left, true, productions, sentence, diagnostics)),
            right: Box::new(commute_lhs(
                right,
                false,
                productions,
                sentence,
                diagnostics,
            )),
        },
        Term::Apply { label, arguments } if label.name == "#withConfig" => Term::Apply {
            label: label.clone(),
            arguments: arguments
                .iter()
                .map(|argument| commute_lhs(argument, on_lhs, productions, sentence, diagnostics))
                .collect(),
        },
        Term::Apply { .. } if !on_lhs => term.clone(),
        Term::Apply { label, arguments } => {
            let Some(attributes) = productions.attributes_for(&LabelHead::from(label)) else {
                return term.clone();
            };
            if attributes.get("comm").is_some() {
                if let [left, right] = arguments.as_slice() {
                    Term::Apply {
                        label: label.clone(),
                        arguments: vec![right.clone(), left.clone()],
                    }
                } else {
                    term.clone()
                }
            } else {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidCommutativeSimplification,
                    format!(
                        "Used 'comm' attribute on simplification rule but {} is not comm.",
                        label.name
                    ),
                    sentence,
                ));
                term.clone()
            }
        }
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(commute_lhs(
                pattern,
                on_lhs,
                productions,
                sentence,
                diagnostics,
            )),
            alias: Box::new(commute_lhs(
                alias,
                on_lhs,
                productions,
                sentence,
                diagnostics,
            )),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .iter()
                .map(|item| commute_lhs(item, on_lhs, productions, sentence, diagnostics))
                .collect(),
        ),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => term.clone(),
    }
}

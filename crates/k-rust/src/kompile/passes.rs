//! Shared pass scaffolding resolves views, clones and transforms definitions, records origins, and retargets production metadata.
//! Cost is the pass traversal plus resolution, measured by the kompile counters and named timing phase.
//!
//! Ordered frontend compilation passes that transform flat definitions.

use std::{fmt, sync::Arc};

use crate::definition::AttributeKey;
use crate::{
    definition::{Definition, LabelHead, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode},
    kast::{InternalLabel, Term},
    provenance::GeneratingPass,
};

mod add_implicit_computation_cell;
mod check_simplification;
mod concretize_cells;
mod constant_folding;
mod expand_macros;
mod finalize;
mod generate_sort_helpers;
mod guard_or_patterns;
mod minimize_term_construction;
mod number_sentences;
mod propagate_macro;
mod remove_unit;
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

pub(crate) use super::retarget::retarget_production_identities;
pub(crate) use add_implicit_computation_cell::add_implicit_computation_cell_pass;
pub use add_implicit_computation_cell::{
    AddImplicitComputationCellError, add_implicit_computation_cell,
};
pub(crate) use check_simplification::check_simplification_rules_pass;
pub use check_simplification::{CheckSimplificationError, check_simplification_rules};
pub(crate) use concretize_cells::concretize_cells_pass;
pub use concretize_cells::{ConcretizeCellsError, concretize_cells, concretize_cells_in_sentence};
pub(crate) use constant_folding::constant_fold_pass;
pub use constant_folding::{ConstantFoldingError, constant_fold};
pub(crate) use expand_macros::expand_macros_in_terms_from_resolved;
pub(crate) use expand_macros::expand_macros_pass;
pub use expand_macros::{
    ExpandMacrosError, MacroExpansionDefinition, expand_macros, expand_macros_in_term,
    expand_macros_in_term_with_scope,
};
pub use finalize::{add_cool_like_attributes, add_semantics_module, generate_sort_predicate_rules};
pub(crate) use finalize::{
    add_cool_like_attributes_pass, add_semantics_module_pass, generate_sort_predicate_rules_pass,
};
pub use generate_sort_helpers::{
    generate_sort_predicate_syntax, generate_sort_projections, regenerate_sort_predicate_syntax,
};
pub(crate) use generate_sort_helpers::{
    generate_sort_predicate_syntax_pass, generate_sort_projections_pass,
    regenerate_sort_predicate_syntax_pass,
};
pub(crate) use guard_or_patterns::guard_or_patterns_pass;
pub use guard_or_patterns::{GuardOrPatternsError, guard_or_patterns};
pub use minimize_term_construction::minimize_term_construction;
pub(crate) use minimize_term_construction::minimize_term_construction_pass;
pub(crate) use number_sentences::number_sentence;
pub use number_sentences::number_sentences;
pub(crate) use number_sentences::number_sentences_pass;
pub use propagate_macro::propagate_macro_attributes;
pub(crate) use propagate_macro::{propagate_macro_attribute, propagate_macro_attributes_pass};
pub(crate) use remove_unit::remove_unit_pass;
pub use remove_unit::{RemoveUnitError, remove_unit};
pub(crate) use resolve_anon_vars::resolve_anon_vars_pass;
pub use resolve_anon_vars::{resolve_anon_vars, resolve_anon_vars_in_sentence};
pub(crate) use resolve_contexts::resolve_contexts_pass;
pub use resolve_contexts::{ResolveContextsError, resolve_contexts};
pub(crate) use resolve_fresh_config_constants::resolve_fresh_config_constants_pass;
pub use resolve_fresh_config_constants::{
    ResolveFreshConfigConstantsError, resolve_fresh_config_constants,
};
pub(crate) use resolve_fresh_constants::resolve_fresh_constants_pass;
pub use resolve_fresh_constants::{ResolveFreshConstantsError, resolve_fresh_constants};
pub(crate) use resolve_fun::resolve_fun_pass;
pub use resolve_fun::{ResolveFunError, resolve_fun};
pub use resolve_function_with_config::{
    ResolveFunctionWithConfigError, resolve_config_var, resolve_function_with_config,
};
pub(crate) use resolve_function_with_config::{
    resolve_config_var_pass, resolve_function_with_config_pass,
};
pub(crate) use resolve_heat_cool::resolve_heat_cool_attributes_pass;
pub use resolve_heat_cool::{ResolveHeatCoolError, resolve_heat_cool_attributes};
pub(crate) use resolve_io::resolve_io_pass;
pub use resolve_io::{ResolveIoError, resolve_io};
pub use resolve_semantic_casts::{
    ResolveSemanticCastsError, resolve_semantic_casts, resolve_semantic_casts_in_sentence,
    resolve_semantic_casts_with_predicates_in_sentence,
};
pub(crate) use resolve_semantic_casts::{
    is_anonymous, resolve_semantic_casts_pass, semantic_cast_variable_sorts,
};
pub(crate) use resolve_strict::resolve_strict_pass;
pub use resolve_strict::{ResolveStrictError, resolve_strict};
pub use subsort_kitem::{SubsortKItemError, subsort_kitem};
pub(crate) use subsort_kitem::{implicit_less_than_eq, subsort_kitem_pass, with_kitem_subsorts};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveCommError {
    pub diagnostics: Vec<Diagnostic>,
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
    super::pipeline::run_standalone(
        definition,
        resolve_comm_pass,
        Some(GeneratingPass::ResolveComm),
    )
}

pub(crate) fn resolve_comm_pass(
    input: &super::pipeline::PassInput<'_>,
    _: &mut super::pipeline::PipelineState,
) -> Result<Definition, ResolveCommError> {
    let resolved = input.resolved_raw().map_err(|error| ResolveCommError {
        diagnostics: vec![Diagnostic {
            severity: crate::diagnostic::Severity::Error,
            code: DiagnosticCode::InvalidCommutativeSimplification,
            message: error.to_string(),
            source: None,
            location: None,
        }],
    })?;
    let mut output = input.definition.clone();
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
            } = &**sentence
            else {
                sentences.push(sentence.clone());
                continue;
            };
            if !attributes.has(AttributeKey::Simplification) || !attributes.has(AttributeKey::Comm)
            {
                sentences.push(sentence.clone());
                continue;
            }

            let mut attributes = attributes.clone();
            attributes.unset(AttributeKey::Comm);
            let swapped = commute_lhs(body, true, &productions, sentence, &mut diagnostics);
            if swapped != *body {
                sentences.push(Arc::new(Sentence::Rule {
                    body: swapped,
                    requires: requires.clone(),
                    ensures: ensures.clone(),
                    attributes: attributes.clone(),
                }));
            }
            sentences.push(Arc::new(Sentence::Rule {
                body: body.clone(),
                requires: requires.clone(),
                ensures: ensures.clone(),
                attributes,
            }));
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

// Invariant: each call rebuilds one node of `term` and recurses only into its direct subterms, with `on_lhs` set true under the left side of a rewrite and false under its right side; the finite `term` bounds the calls.
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
        Term::Apply { label, arguments } if label.is(InternalLabel::WithConfig) => Term::Apply {
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
            if attributes.has(AttributeKey::Comm) {
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

//! Shared pass scaffolding resolves views, clones and transforms definitions, records origins, and retargets production metadata.
//! Cost is the pass traversal plus resolution, measured by the kompile counters and named timing phase.
//!
//! Ordered frontend compilation passes that transform flat definitions.
//!
//! A pass decides which sentence kinds it rewrites in one exhaustive `match` that names every
//! [`Sentence`] variant, so a new variant forces a decision in every pass. `matches!`, `if let`
//! and `let … else` over `Sentence` only select the single kind a pass is about, or project a
//! kind already decided, because clippy's `wildcard_enum_match_arm` cannot see them.

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
mod initializer_totality;
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
    ExpandMacrosError, ExpandedProgram, MacroExpansionDefinition, expand_macros,
    expand_macros_in_term, expand_macros_in_term_with_scope,
};
pub use finalize::{add_cool_like_attributes, add_semantics_module, generate_sort_predicate_rules};
pub(crate) use finalize::{
    add_cool_like_attributes_pass, add_semantics_module_pass, generate_sort_predicate_rules_pass,
};
pub(crate) use generate_sort_helpers::{
    SoleGenerator, generate_sort_predicate_syntax_pass, generate_sort_projections_pass,
    regenerate_sort_predicate_syntax_pass, sort_predicate_in_module,
};
pub use generate_sort_helpers::{
    generate_sort_predicate_syntax, generate_sort_projections, regenerate_sort_predicate_syntax,
};
pub(crate) use guard_or_patterns::guard_or_patterns_pass;
pub use guard_or_patterns::{GuardOrPatternsError, guard_or_patterns};
pub(crate) use initializer_totality::{DefinedInitializer, declare_deferred_totality_pass};
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
pub(crate) use resolve_fun::{
    CoveringLambda, DefinedBody, LambdaSorts, LocalFunction, closure_variables, lambda_sorts,
    resolve_fun_pass,
};
pub use resolve_fun::{ResolveFunError, resolve_fun};
pub(crate) use resolve_function_with_config::{
    FunctionRuleWithContext, resolve_config_var_pass, resolve_function_with_config_pass,
};
pub use resolve_function_with_config::{
    ResolveFunctionWithConfigError, resolve_config_var, resolve_function_with_config,
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
    resolve_semantic_casts_pass, semantic_cast_variable_sorts,
};
pub(crate) use resolve_strict::resolve_strict_pass;
pub use resolve_strict::{ResolveStrictError, resolve_strict};
pub(crate) use subsort_kitem::{
    Injectable, Placement, PlacementKind, has_subsort_axiom, placeable, subsort_kitem_pass,
    with_kitem_subsorts,
};
pub use subsort_kitem::{SubsortKItemError, subsort_kitem};

/// Make the `BOOL` module visible in `module`, which holds a sentence whose generated condition
/// uses `BOOL`'s connectives (`_andBool_`, `notBool_`).
///
/// A rule condition is a `Bool` term, and the side conditions compilation states for a sentence
/// (the result test of a heating or cooling rule, the negation of a `:/=K` match, the conjunction
/// of a cell fragment's sort tests) are `Bool` formulas built from those connectives. The sentence
/// the user wrote means the same whether or not its module imports `BOOL`: the condition is part
/// of the lowering, not of the user's syntax. So compilation makes the connectives visible where
/// the generated sentence is checked ([`import_for_generated`]). `BOOL` declares functions over
/// `Bool` only, whose sort `BASIC-K` already provides.
pub(super) fn import_bool(
    module: &mut crate::definition::FlatModule,
    resolved: &crate::definition::ResolvedDefinition,
) -> bool {
    import_for_generated(module, resolved, crate::kast::WellKnownModule::Bool)
}

/// Make `required` visible in `module`, which holds a sentence that compilation wrote with
/// symbols `required` declares.
///
/// The import is private, so it reaches no module that imports `module`, and passes run after
/// rule parsing, so it changes no parse. A module that already sees `required` is unchanged.
///
/// Returns `false`, and changes nothing, when the definition has no module `required` (a
/// `--no-prelude` definition that does not provide one); the caller reports the sentence that
/// needs it ([`missing_module_message`]).
pub(super) fn import_for_generated(
    module: &mut crate::definition::FlatModule,
    resolved: &crate::definition::ResolvedDefinition,
    required: crate::kast::WellKnownModule,
) -> bool {
    let name = required.as_str();
    let Some(required) = resolved.module_id(name) else {
        return false;
    };
    if module.name == name || module.imports.iter().any(|import| import.name == name) {
        return true;
    }
    let visible = resolved
        .module_id(&module.name)
        .is_some_and(|module_id| resolved.transitive_imports(module_id).contains(&required));
    if !visible {
        module.imports.insert(
            0,
            crate::definition::FlatImport {
                name: name.into(),
                public: false,
            },
        );
    }
    true
}

/// The error message for a sentence whose generated condition needs `BOOL` in a definition
/// that has no `BOOL` module ([`import_bool`]).
pub(super) fn missing_bool_message(what: &str) -> String {
    missing_module_message(
        what,
        "a Bool side condition",
        crate::kast::WellKnownModule::Bool,
    )
}

/// The error message for a sentence whose lowering, described by `what` and `generated`, needs
/// the module `required` in a definition that has none ([`import_for_generated`]).
pub(super) fn missing_module_message(
    what: &str,
    generated: &str,
    required: crate::kast::WellKnownModule,
) -> String {
    format!(
        "{what} generates {generated}, which needs the module {}, but the definition does not contain it.",
        required.as_str()
    )
}

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
/// This is the first KORE-backend pass. The rule-level `comm` attribute is removed because the
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
            input_addresses: Vec::new(),
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

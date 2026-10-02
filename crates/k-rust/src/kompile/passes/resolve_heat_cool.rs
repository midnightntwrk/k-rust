//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Lower `heat` and `cool` attributes into explicit side conditions.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{fmt, mem};

use crate::definition::AttributeKey;
use crate::{
    definition::{Definition, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode},
    kast::{FrontendSort, Label, Sort, Term},
    provenance::GeneratingPass,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveHeatCoolError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveHeatCoolError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "heat/cool attribute resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveHeatCoolError {}

/// Apply Java's `ResolveHeatCoolAttribute` transformation.
pub fn resolve_heat_cool_attributes(
    definition: &Definition,
) -> Result<Definition, ResolveHeatCoolError> {
    super::super::pipeline::run_standalone(
        definition,
        resolve_heat_cool_attributes_pass,
        Some(GeneratingPass::ResolveHeatCool),
    )
}

pub(crate) fn resolve_heat_cool_attributes_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveHeatCoolError> {
    let resolved = input.resolved_raw().map_err(|error| ResolveHeatCoolError {
        diagnostics: vec![Diagnostic {
            severity: crate::diagnostic::Severity::Error,
            code: DiagnosticCode::InvalidHeatCool,
            message: error.to_string(),
            source: None,
            location: None,
            input_addresses: Vec::new(),
        }],
    })?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    let mut diagnostics = Vec::new();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);
        let sorts = views.sort_catalog(module_id);
        // Invariant: every heat or cool rule or context of `module.local_sentences` before `sentence` has its `requires` conjoined with its result predicate on `HOLE` (negated for heat), and `diagnostics` holds one error for each such sentence whose predicate is missing; each iteration consumes one sentence.
        for sentence in &mut module.local_sentences {
            // Only heat and cool sentences change. Their attributes are checked before taking a
            // mutable sentence, which copies a shared one, so every other sentence stays shared;
            // the kind is decided below.
            if !sentence.attributes().has(AttributeKey::Heat)
                && !sentence.attributes().has(AttributeKey::Cool)
            {
                continue;
            }
            let sentence = crate::definition::sentence_mut(sentence);
            let attributes = sentence.attributes();
            let heat = attributes.has(AttributeKey::Heat);
            let cool = attributes.has(AttributeKey::Cool);
            if !heat && !cool {
                continue;
            }
            // Heat/cool lowering is defined only for rules and contexts, the sentences that state
            // evaluation steps. Every other kind is left unchanged before the result predicate is
            // resolved, so an unrelated production or claim never fails for a missing predicate.
            match sentence {
                Sentence::Rule { .. } | Sentence::Context { .. } => {}
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => continue,
            }
            let result_sort = attributes
                .string(AttributeKey::Result)
                .unwrap_or(FrontendSort::KResult.as_str());
            let predicate_label = Label::sort_predicate(&Sort::new(result_sort)).name;
            // A declared result sort whose role has no sort predicate (a numeral, a `#` sort) has
            // no K terms, so no strict argument can ever cool to it.
            if let Err(missing) = super::sort_predicate_in_module(productions, sorts, result_sort) {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidHeatCool,
                    format!(
                        "Definition is missing function {predicate_label} required for strictness. {}",
                        missing.remedy(result_sort, &predicate_label)
                    ),
                    sentence,
                ));
                continue;
            }
            let requires = match sentence {
                Sentence::Rule { requires, .. } | Sentence::Context { requires, .. } => requires,
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => unreachable!("the kind is decided above"),
            };
            let predicate = Term::apply(predicate_label, vec![Term::variable("HOLE")]);
            let condition = if heat {
                Term::apply("notBool_", vec![predicate])
            } else {
                predicate
            };
            let original = mem::replace(requires, Term::Sequence(Vec::new()));
            *requires = Term::apply("_andBool_", vec![original, condition]);
        }
    }
    if diagnostics.is_empty() {
        Ok(output)
    } else {
        diagnostics.sort();
        diagnostics.dedup();
        Err(ResolveHeatCoolError { diagnostics })
    }
}

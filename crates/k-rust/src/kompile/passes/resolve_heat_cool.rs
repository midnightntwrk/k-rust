//! Lower `heat` and `cool` attributes into explicit side conditions.

use std::{fmt, mem};

use crate::{
    definition::{Definition, LabelHead, ResolvedDefinition, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode},
    kast::Term,
    provenance::{GeneratingPass, record_generated_origins},
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
    resolve_heat_cool_attributes_inner(definition)
        .map(|output| record_generated_origins(definition, output, GeneratingPass::ResolveHeatCool))
}

fn resolve_heat_cool_attributes_inner(
    definition: &Definition,
) -> Result<Definition, ResolveHeatCoolError> {
    let resolved =
        ResolvedDefinition::resolve(definition).map_err(|error| ResolveHeatCoolError {
            diagnostics: vec![Diagnostic {
                severity: crate::diagnostic::Severity::Error,
                code: DiagnosticCode::InvalidHeatCool,
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
        let sorts = resolved.sort_catalog(module_id);
        for sentence in &mut module.local_sentences {
            let attributes = sentence.attributes();
            let heat = attributes.get("heat").is_some();
            let cool = attributes.get("cool").is_some();
            if !heat && !cool {
                continue;
            }
            let result_sort = attributes.get_str("result").unwrap_or("KResult");
            let predicate_label = format!("is{result_sort}");
            let predicate_exists = !productions
                .productions_for(&LabelHead::new(predicate_label.clone()))
                .is_empty()
                || sorts
                    .all_sorts()
                    .iter()
                    .any(|sort| sort.to_string() == result_sort);
            if !predicate_exists {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidHeatCool,
                    format!(
                        "Definition is missing function {predicate_label} required for strictness. Please either declare sort {result_sort} or declare 'syntax Bool ::= {predicate_label}(K) [symbol({predicate_label}), function]'"
                    ),
                    sentence,
                ));
                continue;
            }
            let requires = match sentence {
                Sentence::Rule { requires, .. } | Sentence::Context { requires, .. } => requires,
                _ => continue,
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
        Err(ResolveHeatCoolError { diagnostics })
    }
}

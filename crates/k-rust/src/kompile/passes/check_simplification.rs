//! Validate simplification-rule heads after macro expansion.

use std::fmt;

use crate::{
    definition::{Definition, LabelHead, ResolvedDefinition, Sentence, match_rule_label},
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckSimplificationError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for CheckSimplificationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "simplification checking produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for CheckSimplificationError {}

/// Require every local simplification rule to match a functional or matching-logic symbol.
pub fn check_simplification_rules(
    definition: &Definition,
) -> Result<Definition, CheckSimplificationError> {
    let resolved =
        ResolvedDefinition::resolve(definition).map_err(|error| CheckSimplificationError {
            diagnostics: vec![Diagnostic {
                severity: Severity::Error,
                code: DiagnosticCode::InvalidSimplification,
                message: error.to_string(),
                source: None,
                location: None,
            }],
        })?;
    let mut diagnostics = Vec::new();
    for module in &definition.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = resolved.production_catalog(module_id);
        for sentence in &module.local_sentences {
            if !matches!(sentence, Sentence::Rule { attributes, .. } if attributes.get("simplification").is_some())
            {
                continue;
            }
            let label = match_rule_label(sentence);
            let valid = productions
                .attributes_for(&LabelHead::from(&label))
                .is_some_and(|attributes| {
                    attributes.get("function").is_some()
                        || attributes.get("functional").is_some()
                        || attributes.get("mlOp").is_some()
                });
            if !valid {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidSimplification,
                    "Simplification rules expect function/functional/mlOp symbols at the top of the left hand side term.",
                    sentence,
                ));
            }
        }
    }
    if diagnostics.is_empty() {
        Ok(definition.clone())
    } else {
        diagnostics.sort();
        diagnostics.dedup();
        Err(CheckSimplificationError { diagnostics })
    }
}

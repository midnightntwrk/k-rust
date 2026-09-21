//! This D12 transformation pass resolves required views, transforms sentences and terms, records origins, and rebases metadata when needed.
//! Its named `--timings` phase measures total cost; kompile counters measure resolution, rebasing, and transformed sentences.
//!
//! Propagate production macro kinds onto their defining rules.

use crate::definition::AttributeKey;
use crate::{
    definition::{Definition, LabelHead, Sentence},
    kast::Term,
};

/// Apply Java's `PropagateMacro` transformation.
pub fn propagate_macro_attributes(definition: &Definition) -> Result<Definition, String> {
    super::super::pipeline::run_standalone(definition, propagate_macro_attributes_pass, None)
}

pub(crate) fn propagate_macro_attributes_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, String> {
    let resolved = input.resolved_raw().map_err(|error| error.to_string())?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);
        for sentence in &mut module.local_sentences {
            let Sentence::Rule {
                body, attributes, ..
            } = sentence
            else {
                continue;
            };
            if attributes.has(AttributeKey::Simplification) {
                continue;
            }
            let Term::Rewrite { left, .. } = body.unannotated() else {
                continue;
            };
            let Term::Apply { label, .. } = left.unannotated() else {
                continue;
            };
            if !productions.macro_labels().contains(label) {
                continue;
            }
            let Some(production_attributes) = productions.attributes_for(&LabelHead::from(label))
            else {
                continue;
            };
            if let Some(attribute) = AttributeKey::MACRO_LIKE
                .into_iter()
                .find(|attribute| production_attributes.has(*attribute))
            {
                attributes.mark(attribute);
            }
        }
    }
    Ok(output)
}

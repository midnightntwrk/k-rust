//! Propagate production macro kinds onto their defining rules.

use crate::definition::AttributeKey;
use crate::{
    definition::{Definition, LabelHead, ResolvedDefinition, Sentence},
    kast::Term,
};

/// Apply Java's `PropagateMacro` transformation.
pub fn propagate_macro_attributes(definition: &Definition) -> Result<Definition, String> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| error.to_string())?;
    let mut output = definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = resolved.production_catalog(module_id);
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

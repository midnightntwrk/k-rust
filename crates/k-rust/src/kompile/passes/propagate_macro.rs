//! Propagate production macro kinds onto their defining rules.

use serde_json::Value;

use crate::{
    definition::{Definition, LabelHead, ResolvedDefinition, Sentence},
    kast::Term,
};

const MACRO_ATTRIBUTES: &[&str] = &["macro", "macro-rec", "alias", "alias-rec"];

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
            if attributes.get("simplification").is_some() {
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
            if let Some(attribute) = MACRO_ATTRIBUTES
                .iter()
                .find(|attribute| production_attributes.get(attribute).is_some())
            {
                attributes.insert(*attribute, Value::String(String::new()));
            }
        }
    }
    Ok(output)
}

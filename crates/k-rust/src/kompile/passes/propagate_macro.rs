//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Propagate production macro kinds onto their defining rules.

use crate::definition::AttributeKey;
use crate::{
    definition::{Definition, LabelHead, ProductionCatalog, ResolveError, Sentence},
    kast::Term,
};

/// Apply Java's `PropagateMacro` transformation.
pub fn propagate_macro_attributes(definition: &Definition) -> Result<Definition, ResolveError> {
    super::super::pipeline::run_standalone(definition, propagate_macro_attributes_pass, None)
}

pub(crate) fn propagate_macro_attributes_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveError> {
    let resolved = input.resolved_raw().map_err(Clone::clone)?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);
        for sentence in &mut module.local_sentences {
            propagate_macro_attribute(crate::definition::sentence_mut(sentence), productions);
        }
    }
    Ok(output)
}

/// Mark one rule with the macro kind of the production its top-level rewrite's left side applies.
///
/// `productions` is the catalog of the module that declares the rule. Simplification rules and
/// sentences that are not rules are left unchanged.
pub(crate) fn propagate_macro_attribute(
    sentence: &mut Sentence,
    productions: &ProductionCatalog<'_>,
) {
    let Sentence::Rule {
        body, attributes, ..
    } = sentence
    else {
        return;
    };
    if attributes.has(AttributeKey::Simplification) {
        return;
    }
    let Term::Rewrite { left, .. } = body.unannotated() else {
        return;
    };
    let Term::Apply { label, .. } = left.unannotated() else {
        return;
    };
    if !productions.macro_labels().contains(label) {
        return;
    }
    let Some(production_attributes) = productions.attributes_for(&LabelHead::from(label)) else {
        return;
    };
    if let Some(attribute) = AttributeKey::MACRO_LIKE
        .into_iter()
        .find(|attribute| production_attributes.has(*attribute))
    {
        attributes.mark(attribute);
    }
}

//! A conservative compiled-output equivalence check for mutant classification.

use std::collections::BTreeMap;

use k_rust::{
    kore::{
        ast::{Attributes, Definition, Pattern, Sentence},
        parser::{ParseError, parse_definition},
    },
    names::KoreAttribute,
};

use crate::ValidatedDefinition;

/// Whether two sides have identical executable compiler output.
///
/// The comparison retains every distinct emitted sentence, its first occurrence order, its `UNIQUE_ID`,
/// and every attribute except KORE `Source`, `Location`, and rule `label`.
/// Those attributes identify written origins for diagnostics and observation
/// attribution; they do not change backend execution. Identical `UNIQUE_ID`
/// axioms are counted once, as the backend collapses equal executable copies.
/// The check also retains syntax and macro KORE, configuration variable sorts,
/// the source rewrite order, and compile options.
/// Diagnostic messages and the input-address relation describe compilation
/// provenance and do not enter execution. This is intentionally stricter than
/// semantic equivalence: equal output proves equivalence, but differing output
/// can still have equal behavior.
///
/// A parse error fails closed; callers must not classify that side as equivalent.
pub fn equivalent_compilation(
    baseline: &ValidatedDefinition,
    mutant: &ValidatedDefinition,
) -> Result<bool, ParseError> {
    let left = baseline.artifacts();
    let right = mutant.artifacts();
    if baseline.compile_options() != mutant.compile_options()
        || left.configuration_variables != right.configuration_variables
        || left.execution_rewrite_order != right.execution_rewrite_order
    {
        return Ok(false);
    }

    for (left, right) in [
        (&left.definition_kore, &right.definition_kore),
        (&left.syntax_definition_kore, &right.syntax_definition_kore),
        (&left.macros_kore, &right.macros_kore),
    ] {
        if left.trim().is_empty() || right.trim().is_empty() {
            if left.trim() != right.trim() {
                return Ok(false);
            }
            continue;
        }
        if normalized_kore(left)? != normalized_kore(right)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn normalized_kore(source: &str) -> Result<Definition, ParseError> {
    let mut definition = parse_definition(source)?;
    strip_origin_attributes(&mut definition.attributes);
    for module in &mut definition.modules {
        strip_origin_attributes(&mut module.attributes);
        for sentence in &mut module.sentences {
            let attributes = match sentence {
                Sentence::Import { attributes, .. }
                | Sentence::SortDeclaration { attributes, .. }
                | Sentence::SymbolDeclaration { attributes, .. }
                | Sentence::AliasDeclaration { attributes, .. }
                | Sentence::Axiom { attributes, .. }
                | Sentence::Claim { attributes, .. } => attributes,
            };
            strip_origin_attributes(attributes);
            if let Sentence::Axiom { attributes, .. } = sentence
                && rule_identity(attributes).is_some()
            {
                attributes.0.retain(|attribute| {
                    !matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == KoreAttribute::Label.as_str())
                });
            }
        }
        let mut seen = BTreeMap::<Vec<u8>, Vec<Sentence>>::new();
        module.sentences.retain(|sentence| {
            let Sentence::Axiom { attributes, .. } = sentence else {
                return true;
            };
            let Some(id) = rule_identity(attributes) else {
                return true;
            };
            let prior = seen.entry(id).or_default();
            if prior.contains(sentence) {
                false
            } else {
                prior.push(sentence.clone());
                true
            }
        });
    }
    Ok(definition)
}

fn rule_identity(attributes: &Attributes) -> Option<Vec<u8>> {
    attributes.0.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments }
            if symbol.name == KoreAttribute::UniqueId.as_str() =>
        {
            let [Pattern::String(id)] = arguments.as_slice() else {
                return None;
            };
            Some(id.as_bytes().to_vec())
        }
        _ => None,
    })
}

fn strip_origin_attributes(attributes: &mut Attributes) {
    attributes.0.retain(|attribute| {
        !matches!(
            attribute,
            Pattern::Application { symbol, .. }
                if symbol.name == KoreAttribute::Source.as_str()
                    || symbol.name == KoreAttribute::Location.as_str()
        )
    });
}

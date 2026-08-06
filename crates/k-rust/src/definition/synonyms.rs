//! Java-compatible application of visible sort synonyms to productions.

use crate::kast::Sort;

use super::{Definition, ProductionItem, ResolveError, ResolvedDefinition, Sentence};

/// Apply every module's visible sort-synonym map to its local productions.
///
/// Like K's `ApplySynonyms`, this is a single, exact lookup. It rewrites only
/// production result sorts and nonterminal sorts; production parameters and
/// sort-synonym declarations remain unchanged.
pub fn apply_sort_synonyms(definition: &Definition) -> Result<Definition, ResolveError> {
    let resolved = ResolvedDefinition::resolve(definition)?;
    let mut transformed = definition.clone();

    for module in &mut transformed.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("every flat module was added to the resolved definition");
        let synonyms = resolved.sort_catalog(module_id).synonym_map().clone();

        for sentence in &mut module.local_sentences {
            apply_to_sentence(sentence, &synonyms);
        }
    }

    Ok(transformed)
}

fn apply_to_sentence(sentence: &mut Sentence, synonyms: &std::collections::BTreeMap<Sort, Sort>) {
    let Sentence::Production { sort, items, .. } = sentence else {
        return;
    };

    replace(sort, synonyms);
    for item in items {
        if let ProductionItem::NonTerminal { sort, .. } = item {
            replace(sort, synonyms);
        }
    }
}

fn replace(sort: &mut Sort, synonyms: &std::collections::BTreeMap<Sort, Sort>) {
    if let Some(replacement) = synonyms.get(sort) {
        *sort = replacement.clone();
    }
}

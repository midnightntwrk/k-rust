//! This D12 transformation pass resolves required views, transforms sentences and terms, records origins, and rebases metadata when needed.
//! Its named `--timings` phase measures total cost; kompile counters measure resolution, rebasing, and transformed sentences.
//!
//! Add backend subsort declarations from every user sort to `KItem`.

use std::fmt;

use crate::names::BuiltinSort;
use crate::{
    definition::{
        Attributes, Definition, ProductionItem, ResolvedDefinition, Sentence, retain_new_sentences,
    },
    kast::{FrontendSort, Sort},
    provenance::{GeneratingPass, record_generated_origins},
};

use super::rebase_local_metadata;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SubsortKItemError(pub String);

impl fmt::Display for SubsortKItemError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for SubsortKItemError {}

/// Apply Java's `Kompile.subsortKItem` module transformation.
pub fn subsort_kitem(definition: &Definition) -> Result<Definition, SubsortKItemError> {
    let resolved = ResolvedDefinition::resolve(definition)
        .map_err(|error| SubsortKItemError(error.to_string()))?;
    let mut output = definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let sorts = resolved.sort_catalog(module_id);
        let visible = resolved.sentences(module_id);
        let mut generated = Vec::new();
        // Invariant: preceding items have been processed in encounter order, and the remaining iterator shrinks by one each iteration.
        for sort in sorts.all_sorts() {
            if is_parser_sort(sort) {
                continue;
            }
            let production = Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: Sort::builtin(BuiltinSort::KItem),
                items: vec![ProductionItem::NonTerminal {
                    sort: sort.clone(),
                    name: None,
                }],
                attributes: Attributes::default(),
            };
            generated.push(production);
        }
        let generated = retain_new_sentences(
            visible.iter().copied().chain(module.local_sentences.iter()),
            generated,
        );
        module.local_sentences.extend(generated);
    }
    let output = rebase_local_metadata(definition, output).map_err(SubsortKItemError)?;
    Ok(record_generated_origins(
        definition,
        output,
        GeneratingPass::SubsortKItem,
    ))
}

fn is_parser_sort(sort: &Sort) -> bool {
    [BuiltinSort::K, BuiltinSort::KItem, BuiltinSort::KConfigVar]
        .iter()
        .any(|builtin| sort.name == builtin.k_name())
        || [
            FrontendSort::KBott,
            FrontendSort::KLabel,
            FrontendSort::KList,
            FrontendSort::KString,
        ]
        .iter()
        .any(|frontend| sort.name == frontend.as_str())
        || sort.name.starts_with('#')
        || sort.name.parse::<u64>().is_ok()
}

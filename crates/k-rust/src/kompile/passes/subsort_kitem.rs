//! Add backend subsort declarations from every user sort to `KItem`.

use std::fmt;

use crate::{
    definition::{Attributes, Definition, ProductionItem, ResolvedDefinition, Sentence},
    kast::Sort,
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
        for sort in sorts.all_sorts() {
            if is_parser_sort(sort) {
                continue;
            }
            let production = Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: Sort::new("KItem"),
                items: vec![ProductionItem::NonTerminal {
                    sort: sort.clone(),
                    name: None,
                }],
                attributes: Attributes::default(),
            };
            if !visible.contains(&&production) && !module.local_sentences.contains(&production) {
                module.local_sentences.push(production);
            }
        }
    }
    rebase_local_metadata(definition, output).map_err(SubsortKItemError)
}

fn is_parser_sort(sort: &Sort) -> bool {
    matches!(
        sort.name.as_str(),
        "KBott" | "K" | "KLabel" | "KList" | "KItem" | "KConfigVar" | "KString"
    ) || sort.name.starts_with('#')
        || sort.name.parse::<u64>().is_ok()
}

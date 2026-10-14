//! The program grammar's own formats, for [`crate::Mode::Program`].
//!
//! `kast --output program` formats each production with the Java frontend's `Formatter`, which
//! reads the production's authored `format` attribute: `%N` names the N-th production item
//! (terminal or non-terminal), `%n %i %d` lay out, and any other `%x` prints `x`, so the colour
//! codes `%c` and `%r` print the letters `c` and `r`. `syntaxDefinition.kore` records only the
//! format `kprint` reads, in which authored and generated colour codes cannot be told apart, so the
//! authored formats are read from the frontend definition.

use std::collections::BTreeMap;

use k_rust::definition::{Definition, ProductionItem, Sentence};
use k_rust::kompile::encode_kore_label;

/// One production item, as the Java formatter sees it.
#[derive(Clone, Debug)]
pub(crate) enum Item {
    Terminal(String),
    NonTerminal,
    Regex,
}

/// A production with an authored `format` attribute.
#[derive(Clone, Debug)]
pub(crate) struct ProgramProduction {
    pub items: Vec<Item>,
    pub format: String,
    pub color: Option<String>,
    pub colors: Option<Vec<String>>,
}

impl ProgramProduction {
    /// The colour of the `index`-th terminal (`Formatter.color`).
    pub fn terminal_color(&self, index: usize) -> Option<&str> {
        self.color
            .as_deref()
            .or_else(|| self.colors.as_ref()?.get(index).map(String::as_str))
    }
}

/// The first production of each label that carries an authored `format` and is not `unparseAvoid`, by KORE symbol name.
pub(crate) fn program_productions(definition: &Definition) -> BTreeMap<String, ProgramProduction> {
    let mut productions = BTreeMap::new();
    let mut seen = std::collections::BTreeSet::new();
    for module in &definition.modules {
        for sentence in &module.local_sentences {
            let Sentence::Production {
                label: Some(label),
                items,
                attributes,
                ..
            } = &**sentence
            else {
                continue;
            };
            if attributes.get("unparseAvoid").is_some() || attributes.get("bracket").is_some() {
                continue;
            }
            let symbol = encode_kore_label(label).name;
            if !seen.insert(symbol.clone()) {
                continue;
            }
            let Some(format) = attributes.get_str("format") else {
                continue;
            };
            productions.insert(
                symbol,
                ProgramProduction {
                    items: items
                        .iter()
                        .map(|item| match item {
                            ProductionItem::Terminal(text) => Item::Terminal(text.clone()),
                            ProductionItem::NonTerminal { .. } => Item::NonTerminal,
                            ProductionItem::RegexTerminal { .. } => Item::Regex,
                        })
                        .collect(),
                    format: format.to_owned(),
                    color: attributes.get_str("color").map(str::to_owned),
                    colors: attributes.get_str("colors").map(|colors| {
                        colors
                            .split(',')
                            .map(|color| color.trim().to_owned())
                            .collect()
                    }),
                },
            );
        }
    }
    productions
}

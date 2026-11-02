//! The program grammar's own formats, for [`crate::Mode::Program`].
//!
//! [`crate::Mode::Program`] formats each production with its authored `format` attribute: `%N`
//! names the N-th production item (terminal or non-terminal), `%n %i %d` lay out, the colour
//! codes `%c` and `%r` print nothing, and any other `%x` prints `x`. `syntaxDefinition.kore`
//! records only the format `kprint` reads, in which authored and generated colour codes cannot be
//! told apart, so the authored formats are read from the frontend definition.

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

/// The user lists of `definition` ([`crate::user_list`]): each sort whose `userList` productions
/// are one cons `Elem "sep" Sort` and one terminator, by the cons's KORE symbol name, as the
/// program parser reads them. A list of another shape (a parametric one, or a left-recursive
/// `NeList`), which the parser reads by its productions as written, prints in K's spelling; its
/// cons is recorded too, since a one-element list of it is its element's text.
pub(crate) fn user_lists(definition: &Definition) -> crate::user_list::UserLists {
    type Productions<'d> = (Vec<&'d Sentence>, Vec<&'d Sentence>, bool);
    let mut by_sort = BTreeMap::<String, Productions<'_>>::new();
    for module in &definition.modules {
        for sentence in &module.local_sentences {
            let Sentence::Production {
                parameters,
                sort,
                items,
                attributes,
                ..
            } = &**sentence
            else {
                continue;
            };
            if attributes.get("userList").is_none()
                || attributes.get("userListTerminator").is_some()
            {
                continue;
            }
            let nonterminals = items
                .iter()
                .filter(|item| matches!(item, ProductionItem::NonTerminal { .. }))
                .count();
            let (conses, terminators, parametric) = by_sort.entry(sort.name.clone()).or_default();
            *parametric |= !parameters.is_empty();
            match nonterminals {
                2 => conses.push(sentence),
                0 => terminators.push(sentence),
                _ => {}
            }
        }
    }
    let mut lists = crate::user_list::UserLists::default();
    for (sort, (conses, terminators, parametric)) in by_sort {
        for cons in &conses {
            if let Sentence::Production {
                label: Some(label),
                items,
                ..
            } = &**cons
            {
                let separator = items
                    .iter()
                    .find_map(|item| match item {
                        ProductionItem::Terminal(text) => Some(text.as_str()),
                        _ => None,
                    })
                    .unwrap_or_default();
                lists.insert_other(encode_kore_label(label).name, separator);
            }
        }
        if parametric {
            continue;
        }
        let (
            [
                Sentence::Production {
                    label: Some(cons),
                    items,
                    attributes,
                    ..
                },
            ],
            [
                Sentence::Production {
                    label: Some(terminator),
                    ..
                },
            ],
        ) = (conses.as_slice(), terminators.as_slice())
        else {
            continue;
        };
        let [
            ProductionItem::NonTerminal { .. },
            ProductionItem::Terminal(separator),
            ProductionItem::NonTerminal { sort: tail, .. },
        ] = items.as_slice()
        else {
            continue;
        };
        if tail.name != sort {
            continue;
        }
        lists.insert(
            encode_kore_label(cons).name,
            encode_kore_label(terminator).name,
            separator,
            attributes.get_str("userList") == Some("+"),
        );
    }
    lists
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

//! Generation and collapse of Scala-compatible record productions.

use std::collections::{BTreeMap, BTreeSet};

use crate::definition::ProductionItem;
use crate::kast::{Sort, Term};

use super::{Grammar, Item, ParseError, ParsedTerm, RecordProduction, RecordProductionKind};

impl Grammar {
    pub(super) fn add_record_productions(&mut self, original: usize) -> Result<(), ParseError> {
        if !is_prefix_production(&self.productions[original]) {
            return Ok(());
        }

        let production = &self.productions[original];
        let result = production.result.clone();
        let label = production.label.clone();
        let suffix = match production.items.last() {
            Some(Item::Terminal(value)) => value.clone(),
            _ => return Ok(()),
        };
        let mut prefix = production
            .items
            .iter()
            .take_while(|item| matches!(item, Item::Terminal(_)))
            .filter_map(|item| match item {
                Item::Terminal(value) => Some(ProductionItem::Terminal(value.clone())),
                Item::NonTerminal(_) | Item::Regex { .. } => None,
            })
            .collect::<Vec<_>>();
        prefix.push(ProductionItem::Terminal("...".into()));

        let named = production
            .items
            .iter()
            .filter_map(|item| match item {
                Item::NonTerminal(sort) => Some(sort.clone()),
                Item::Terminal(_) | Item::Regex { .. } => None,
            })
            .zip(production.field_names.iter())
            .filter_map(|(sort, name)| name.clone().map(|name| (name, sort)))
            .collect::<Vec<_>>();

        match named.as_slice() {
            [] => {
                prefix.push(ProductionItem::Terminal(suffix));
                self.add_record_production(
                    result,
                    prefix,
                    label,
                    RecordProduction {
                        original,
                        kind: RecordProductionKind::Zero,
                    },
                )?;
            }
            [(name, sort)] => {
                let mut zero = prefix.clone();
                zero.push(ProductionItem::Terminal(suffix.clone()));
                self.add_record_production(
                    result.clone(),
                    zero,
                    label.clone(),
                    RecordProduction {
                        original,
                        kind: RecordProductionKind::Zero,
                    },
                )?;

                prefix.extend([
                    ProductionItem::Terminal(name.clone()),
                    ProductionItem::Terminal(":".into()),
                    nonterminal(sort.clone()),
                    ProductionItem::Terminal(suffix),
                ]);
                self.add_record_production(
                    result,
                    prefix,
                    label,
                    RecordProduction {
                        original,
                        kind: RecordProductionKind::One(name.clone()),
                    },
                )?;
            }
            _ => {
                let base = Sort::new(format!("#Record{original}"));
                let non_empty = Sort::new(format!("#Record{original}Ne"));
                let item = Sort::new(format!("#Record{original}Item"));

                prefix.extend([nonterminal(base.clone()), ProductionItem::Terminal(suffix)]);
                self.add_record_production(
                    result,
                    prefix,
                    label.clone(),
                    RecordProduction {
                        original,
                        kind: RecordProductionKind::Main,
                    },
                )?;
                self.add_record_production(
                    base.clone(),
                    Vec::new(),
                    label.clone(),
                    RecordProduction {
                        original,
                        kind: RecordProductionKind::Empty,
                    },
                )?;
                self.add_record_production(
                    base,
                    vec![nonterminal(non_empty.clone())],
                    None,
                    RecordProduction {
                        original,
                        kind: RecordProductionKind::Subsort,
                    },
                )?;
                self.add_record_production(
                    non_empty.clone(),
                    vec![
                        nonterminal(non_empty.clone()),
                        ProductionItem::Terminal(",".into()),
                        nonterminal(item.clone()),
                    ],
                    label.clone(),
                    RecordProduction {
                        original,
                        kind: RecordProductionKind::Repeat,
                    },
                )?;
                self.add_record_production(
                    non_empty,
                    vec![nonterminal(item.clone())],
                    None,
                    RecordProduction {
                        original,
                        kind: RecordProductionKind::Subsort,
                    },
                )?;
                for (name, sort) in named {
                    self.add_record_production(
                        item.clone(),
                        vec![
                            ProductionItem::Terminal(name.clone()),
                            ProductionItem::Terminal(":".into()),
                            nonterminal(sort),
                        ],
                        label.clone(),
                        RecordProduction {
                            original,
                            kind: RecordProductionKind::Item(name),
                        },
                    )?;
                }
            }
        }
        Ok(())
    }

    fn add_record_production(
        &mut self,
        result: Sort,
        items: Vec<ProductionItem>,
        label: Option<crate::kast::Label>,
        record: RecordProduction,
    ) -> Result<(), ParseError> {
        let index = self.productions.len();
        self.add(result, items, label, false, false)?;
        self.productions[index].record = Some(record);
        Ok(())
    }

    pub(super) fn collapse_record_productions(
        &self,
        term: ParsedTerm,
    ) -> Result<ParsedTerm, ParseError> {
        let mut names = BTreeSet::new();
        collect_variable_names(&term, &mut names);
        let mut next = 0;
        self.collapse_records(term, &mut names, &mut next)
    }

    fn collapse_records(
        &self,
        term: ParsedTerm,
        names: &mut BTreeSet<String>,
        next: &mut usize,
    ) -> Result<ParsedTerm, ParseError> {
        match term {
            ParsedTerm::Term(_) => Ok(term),
            ParsedTerm::Ambiguity(alternatives) => alternatives
                .into_iter()
                .map(|term| self.collapse_records(term, names, next))
                .collect::<Result<BTreeSet<_>, _>>()
                .map(|alternatives| ParsedTerm::Ambiguity(alternatives.into())),
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } if self.productions[production].record.is_some() => {
                let collapsed =
                    self.collapse_record(production, children.into_inner(), metadata, names, next)?;
                self.collapse_records(collapsed, names, next)
            }
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } => Ok(ParsedTerm::Production {
                production,
                metadata,
                children: children
                    .into_iter()
                    .map(|term| self.collapse_records(term, names, next))
                    .collect::<Result<_, _>>()?,
            }),
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("record productions collapse before sort inference")
            }
        }
    }

    fn collapse_record(
        &self,
        production: usize,
        children: Vec<ParsedTerm>,
        root_metadata: super::TermMetadata,
        names: &mut BTreeSet<String>,
        next: &mut usize,
    ) -> Result<ParsedTerm, ParseError> {
        let record = self.productions[production]
            .record
            .clone()
            .expect("record production checked by caller");
        let original = record.original;
        let mut fields = BTreeMap::new();
        let mut iterator = ParsedTerm::Production {
            production,
            children: children.into(),
            metadata: root_metadata.clone(),
        };

        loop {
            let ParsedTerm::Production {
                production,
                mut children,
                ..
            } = iterator
            else {
                return Err(record_error("malformed generated record production"));
            };
            let metadata = self.productions[production]
                .record
                .as_ref()
                .ok_or_else(|| record_error("malformed generated record production"))?;
            if metadata.original != original {
                return Err(record_error("mismatched generated record production"));
            }
            match &metadata.kind {
                RecordProductionKind::Zero | RecordProductionKind::Empty => break,
                RecordProductionKind::Main | RecordProductionKind::Subsort => {
                    if children.len() != 1 {
                        return Err(record_error("malformed generated record list"));
                    }
                    iterator = children.pop().expect("length was one");
                }
                RecordProductionKind::One(key) | RecordProductionKind::Item(key) => {
                    if children.len() != 1 {
                        return Err(record_error("malformed generated record item"));
                    }
                    insert_field(&mut fields, key, children.pop().expect("length was one"))?;
                    break;
                }
                RecordProductionKind::Repeat => {
                    if children.len() != 2 {
                        return Err(record_error("malformed generated record list"));
                    }
                    let item = children.pop().expect("length was two");
                    let (key, value) = self.record_item(item, original)?;
                    insert_field(&mut fields, &key, value)?;
                    iterator = children.pop().expect("one child remains");
                }
            }
        }

        let children = self.productions[original]
            .field_names
            .iter()
            .map(|field| {
                if let Some(value) = field.as_ref().and_then(|field| fields.remove(field)) {
                    return value;
                }
                let stem = field.as_deref().unwrap_or("Gen");
                let name = loop {
                    let candidate = format!("_{stem}{}", *next);
                    *next += 1;
                    if names.insert(candidate.clone()) {
                        break candidate;
                    }
                };
                ParsedTerm::Term(Term::Variable { name, sort: None })
            })
            .collect();
        Ok(ParsedTerm::Production {
            production: original,
            children,
            metadata: root_metadata,
        })
    }

    fn record_item(
        &self,
        term: ParsedTerm,
        original: usize,
    ) -> Result<(String, ParsedTerm), ParseError> {
        let ParsedTerm::Production {
            production,
            mut children,
            ..
        } = term
        else {
            return Err(record_error("malformed generated record item"));
        };
        let metadata = self.productions[production]
            .record
            .as_ref()
            .ok_or_else(|| record_error("malformed generated record item"))?;
        let RecordProductionKind::Item(key) = &metadata.kind else {
            return Err(record_error("malformed generated record item"));
        };
        if metadata.original != original || children.len() != 1 {
            return Err(record_error("malformed generated record item"));
        }
        Ok((key.clone(), children.pop().expect("length was one")))
    }
}

fn is_prefix_production(production: &super::Production) -> bool {
    let mut state = 0;
    for item in &production.items {
        match (state, item) {
            (0, Item::Terminal(value)) if value == "(" => state = 1,
            (0, Item::Terminal(_)) => {}
            (1, Item::NonTerminal(_)) => state = 2,
            (1, Item::Terminal(value)) if value == ")" => state = 4,
            (2, Item::Terminal(value)) if value == "," => state = 3,
            (2, Item::Terminal(value)) if value == ")" => state = 4,
            (3, Item::NonTerminal(_)) => state = 2,
            _ => return false,
        }
    }
    state == 4
}

fn collect_variable_names(term: &ParsedTerm, names: &mut BTreeSet<String>) {
    match term {
        ParsedTerm::Term(term) => {
            if let Term::Variable { name, .. } = term.unannotated() {
                names.insert(name.clone());
            }
        }
        ParsedTerm::Production { children, .. } => {
            for child in children {
                collect_variable_names(child, names);
            }
        }
        ParsedTerm::InstantiatedProduction { .. } => {
            unreachable!("record variables are collected before sort inference")
        }
        ParsedTerm::Ambiguity(alternatives) => {
            for alternative in alternatives {
                collect_variable_names(alternative, names);
            }
        }
    }
}

fn insert_field(
    fields: &mut BTreeMap<String, ParsedTerm>,
    key: &str,
    value: ParsedTerm,
) -> Result<(), ParseError> {
    if fields.insert(key.to_owned(), value).is_some() {
        Err(record_error(format!(
            "Duplicate record production key: {key}"
        )))
    } else {
        Ok(())
    }
}

fn nonterminal(sort: Sort) -> ProductionItem {
    ProductionItem::NonTerminal { sort, name: None }
}

fn record_error(message: impl Into<String>) -> ParseError {
    ParseError::RecordProduction {
        message: message.into(),
    }
}

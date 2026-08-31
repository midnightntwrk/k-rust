//! Generation and collapse of Scala-compatible record productions.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use crate::definition::ProductionItem;
use crate::kast::{Sort, Term, TermSpan};

#[cfg(test)]
use super::ParsedTerm;
use super::{
    Grammar, Item, PackedNode, PackedTerm, ParseError, RecordProduction, RecordProductionKind,
    canonical_packed_error, cmp_packed_structurally, packed_terms_in_structural_order,
};

type PackedRecordResult = Result<Rc<PackedTerm>, ParseError>;
type PackedRecordMemo = HashMap<*const PackedTerm, (Rc<PackedTerm>, PackedRecordResult)>;

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

    #[cfg(test)]
    pub(super) fn collapse_record_productions(
        &self,
        term: ParsedTerm,
        mut names: BTreeSet<String>,
    ) -> Result<ParsedTerm, ParseError> {
        let mut next = 0;
        let mut generated = BTreeMap::new();
        self.collapse_records(term, &mut names, &mut generated, &mut next)
    }

    pub(super) fn collapse_packed_record_productions(
        &self,
        term: Rc<PackedTerm>,
        mut names: BTreeSet<String>,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let mut generated = BTreeMap::new();
        let mut next = 0;
        let mut memo = HashMap::new();
        self.collapse_packed_records(term, &mut names, &mut generated, &mut next, &mut memo)
    }

    fn collapse_packed_records(
        &self,
        term: Rc<PackedTerm>,
        names: &mut BTreeSet<String>,
        generated: &mut BTreeMap<(TermSpan, usize, usize), String>,
        next: &mut usize,
        memo: &mut PackedRecordMemo,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let identity = Rc::as_ptr(&term);
        if let Some((_, collapsed)) = memo.get(&identity) {
            return collapsed.clone();
        }
        let collapsed = match &term.node {
            PackedNode::InstantiatedProduction { .. } => {
                unreachable!("instantiated productions are created after record collapse")
            }
            PackedNode::Term(_) => Ok(Rc::clone(&term)),
            PackedNode::Ambiguity(alternatives) => {
                let mut retained = BTreeSet::new();
                let mut errors = Vec::new();
                for alternative in packed_terms_in_structural_order(alternatives) {
                    match self.collapse_packed_records(
                        Rc::clone(&alternative),
                        names,
                        generated,
                        next,
                        memo,
                    ) {
                        Ok(collapsed) => match &collapsed.node {
                            PackedNode::Ambiguity(nested) => {
                                for nested in packed_terms_in_structural_order(nested) {
                                    retained.insert(nested);
                                }
                            }
                            _ => {
                                retained.insert(collapsed);
                            }
                        },
                        Err(error) => errors.push((alternative, error)),
                    }
                }
                if retained.is_empty() {
                    Err(canonical_packed_error(errors))
                } else {
                    Ok(PackedTerm::ambiguity(retained))
                }
            }
            PackedNode::Production {
                production,
                children,
                metadata,
            } if self.productions[*production].record.is_some() => self
                .collapse_packed_record(*production, children, metadata, names, generated, next)
                .and_then(|collapsed| {
                    self.collapse_packed_records(collapsed, names, generated, next, memo)
                }),
            PackedNode::Production {
                production,
                children,
                metadata,
            } => {
                let mut collapsed_children = Vec::with_capacity(children.len());
                let mut errors = Vec::new();
                for child in children {
                    match self.collapse_packed_records(
                        Rc::clone(child),
                        names,
                        generated,
                        next,
                        memo,
                    ) {
                        Ok(collapsed) => collapsed_children.push(collapsed),
                        Err(error) => errors.push((Rc::clone(child), error)),
                    }
                }
                if errors.is_empty() {
                    Ok(PackedTerm::production(
                        *production,
                        collapsed_children,
                        metadata.clone(),
                    ))
                } else {
                    Err(canonical_packed_error(errors))
                }
            }
        };
        memo.insert(identity, (term, collapsed.clone()));
        collapsed
    }

    fn collapse_packed_record(
        &self,
        production: usize,
        children: &[Rc<PackedTerm>],
        root_metadata: &super::TermMetadata,
        names: &mut BTreeSet<String>,
        generated: &mut BTreeMap<(TermSpan, usize, usize), String>,
        next: &mut usize,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let record = self.productions[production]
            .record
            .clone()
            .expect("record production checked by caller");
        let original = record.original;
        let iterator = PackedTerm::production(production, children.to_vec(), root_metadata.clone());
        let mut alternatives = BTreeSet::new();
        let mut field_alternatives = self
            .collect_packed_record_fields(iterator, original)?
            .into_iter()
            .collect::<Vec<_>>();
        field_alternatives.sort_by(cmp_packed_record_fields);
        for mut fields in field_alternatives {
            let children = self.productions[original]
                .field_names
                .iter()
                .enumerate()
                .map(|(index, field)| {
                    if let Some(value) = field.as_ref().and_then(|field| fields.remove(field)) {
                        return value;
                    }
                    let stem = field.as_deref().unwrap_or("Gen");
                    let key = root_metadata.span.map(|span| (span, original, index));
                    if let Some(name) = key.as_ref().and_then(|key| generated.get(key)) {
                        return PackedTerm::leaf(Term::Variable {
                            name: name.clone(),
                            sort: None,
                        });
                    }
                    let name = loop {
                        let candidate = format!("_{stem}{}", *next);
                        *next += 1;
                        if names.insert(candidate.clone()) {
                            break candidate;
                        }
                    };
                    if let Some(key) = key {
                        generated.insert(key, name.clone());
                    }
                    PackedTerm::leaf(Term::Variable { name, sort: None })
                })
                .collect();
            alternatives.insert(PackedTerm::production(
                original,
                children,
                root_metadata.clone(),
            ));
        }
        Ok(PackedTerm::ambiguity(alternatives))
    }

    fn collect_packed_record_fields(
        &self,
        term: Rc<PackedTerm>,
        original: usize,
    ) -> Result<BTreeSet<BTreeMap<String, Rc<PackedTerm>>>, ParseError> {
        if let PackedNode::Ambiguity(alternatives) = &term.node {
            let mut fields = BTreeSet::new();
            for alternative in packed_terms_in_structural_order(alternatives) {
                fields.extend(self.collect_packed_record_fields(alternative, original)?);
            }
            return Ok(fields);
        }
        let PackedNode::Production {
            production,
            children,
            ..
        } = &term.node
        else {
            return Err(record_error("malformed generated record production"));
        };
        let metadata = self.productions[*production]
            .record
            .as_ref()
            .ok_or_else(|| record_error("malformed generated record production"))?;
        if metadata.original != original {
            return Err(record_error("mismatched generated record production"));
        }
        match &metadata.kind {
            RecordProductionKind::Zero | RecordProductionKind::Empty => {
                Ok(BTreeSet::from([BTreeMap::new()]))
            }
            RecordProductionKind::Main | RecordProductionKind::Subsort => {
                let [child] = children.as_slice() else {
                    return Err(record_error("malformed generated record list"));
                };
                self.collect_packed_record_fields(Rc::clone(child), original)
            }
            RecordProductionKind::One(key) | RecordProductionKind::Item(key) => {
                let [child] = children.as_slice() else {
                    return Err(record_error("malformed generated record item"));
                };
                Ok(BTreeSet::from([BTreeMap::from([(
                    key.clone(),
                    Rc::clone(child),
                )])]))
            }
            RecordProductionKind::Repeat => {
                let [prefix, item] = children.as_slice() else {
                    return Err(record_error("malformed generated record list"));
                };
                let items = self.collect_packed_record_items(Rc::clone(item), original)?;
                let prefixes = self.collect_packed_record_fields(Rc::clone(prefix), original)?;
                let mut fields = BTreeSet::new();
                for prefix in prefixes {
                    for (key, value) in &items {
                        let mut candidate = prefix.clone();
                        insert_packed_field(&mut candidate, key, Rc::clone(value))?;
                        fields.insert(candidate);
                    }
                }
                Ok(fields)
            }
        }
    }

    fn collect_packed_record_items(
        &self,
        term: Rc<PackedTerm>,
        original: usize,
    ) -> Result<BTreeSet<(String, Rc<PackedTerm>)>, ParseError> {
        if let PackedNode::Ambiguity(alternatives) = &term.node {
            let mut items = BTreeSet::new();
            for alternative in packed_terms_in_structural_order(alternatives) {
                items.extend(self.collect_packed_record_items(alternative, original)?);
            }
            Ok(items)
        } else {
            Ok(BTreeSet::from([self.packed_record_item(term, original)?]))
        }
    }

    fn packed_record_item(
        &self,
        term: Rc<PackedTerm>,
        original: usize,
    ) -> Result<(String, Rc<PackedTerm>), ParseError> {
        let PackedNode::Production {
            production,
            children,
            ..
        } = &term.node
        else {
            return Err(record_error("malformed generated record item"));
        };
        let metadata = self.productions[*production]
            .record
            .as_ref()
            .ok_or_else(|| record_error("malformed generated record item"))?;
        let RecordProductionKind::Item(key) = &metadata.kind else {
            return Err(record_error("malformed generated record item"));
        };
        let [child] = children.as_slice() else {
            return Err(record_error("malformed generated record item"));
        };
        if metadata.original != original {
            return Err(record_error("mismatched generated record item"));
        }
        Ok((key.clone(), Rc::clone(child)))
    }

    #[cfg(test)]
    fn collapse_records(
        &self,
        term: ParsedTerm,
        names: &mut BTreeSet<String>,
        generated: &mut BTreeMap<(TermSpan, usize, usize), String>,
        next: &mut usize,
    ) -> Result<ParsedTerm, ParseError> {
        match term {
            ParsedTerm::Term(_) => Ok(term),
            ParsedTerm::Ambiguity(alternatives) => alternatives
                .into_iter()
                .map(|term| self.collapse_records(term, names, generated, next))
                .collect::<Result<BTreeSet<_>, _>>()
                .map(ParsedTerm::Ambiguity),
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } if self.productions[production].record.is_some() => {
                let collapsed =
                    self.collapse_record(production, children, metadata, names, generated, next)?;
                self.collapse_records(collapsed, names, generated, next)
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
                    .map(|term| self.collapse_records(term, names, generated, next))
                    .collect::<Result<_, _>>()?,
            }),
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("record productions collapse before sort inference")
            }
        }
    }

    #[cfg(test)]
    fn collapse_record(
        &self,
        production: usize,
        children: Vec<ParsedTerm>,
        root_metadata: super::TermMetadata,
        names: &mut BTreeSet<String>,
        generated: &mut BTreeMap<(TermSpan, usize, usize), String>,
        next: &mut usize,
    ) -> Result<ParsedTerm, ParseError> {
        let record = self.productions[production]
            .record
            .clone()
            .expect("record production checked by caller");
        let original = record.original;
        let iterator = ParsedTerm::Production {
            production,
            children,
            metadata: root_metadata.clone(),
        };
        let mut alternatives = BTreeSet::new();
        for mut fields in self.collect_record_fields(iterator, original)? {
            let children = self.productions[original]
                .field_names
                .iter()
                .enumerate()
                .map(|(index, field)| {
                    if let Some(value) = field.as_ref().and_then(|field| fields.remove(field)) {
                        return value;
                    }
                    let stem = field.as_deref().unwrap_or("Gen");
                    let key = root_metadata.span.map(|span| (span, original, index));
                    if let Some(name) = key.as_ref().and_then(|key| generated.get(key)) {
                        return ParsedTerm::Term(Term::Variable {
                            name: name.clone(),
                            sort: None,
                        });
                    }
                    let name = loop {
                        let candidate = format!("_{stem}{}", *next);
                        *next += 1;
                        if names.insert(candidate.clone()) {
                            break candidate;
                        }
                    };
                    if let Some(key) = key {
                        generated.insert(key, name.clone());
                    }
                    ParsedTerm::Term(Term::Variable { name, sort: None })
                })
                .collect();
            alternatives.insert(ParsedTerm::Production {
                production: original,
                children,
                metadata: root_metadata.clone(),
            });
        }
        Ok(if alternatives.len() == 1 {
            alternatives.pop_first().expect("length was one")
        } else {
            ParsedTerm::Ambiguity(alternatives)
        })
    }

    #[cfg(test)]
    fn collect_record_fields(
        &self,
        term: ParsedTerm,
        original: usize,
    ) -> Result<BTreeSet<BTreeMap<String, ParsedTerm>>, ParseError> {
        if let ParsedTerm::Ambiguity(alternatives) = term {
            let mut fields = BTreeSet::new();
            for alternative in alternatives {
                fields.extend(self.collect_record_fields(alternative, original)?);
            }
            return Ok(fields);
        }
        let ParsedTerm::Production {
            production,
            mut children,
            ..
        } = term
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
            RecordProductionKind::Zero | RecordProductionKind::Empty => {
                Ok(BTreeSet::from([BTreeMap::new()]))
            }
            RecordProductionKind::Main | RecordProductionKind::Subsort => {
                if children.len() != 1 {
                    return Err(record_error("malformed generated record list"));
                }
                self.collect_record_fields(children.pop().expect("length was one"), original)
            }
            RecordProductionKind::One(key) | RecordProductionKind::Item(key) => {
                if children.len() != 1 {
                    return Err(record_error("malformed generated record item"));
                }
                Ok(BTreeSet::from([BTreeMap::from([(
                    key.clone(),
                    children.pop().expect("length was one"),
                )])]))
            }
            RecordProductionKind::Repeat => {
                if children.len() != 2 {
                    return Err(record_error("malformed generated record list"));
                }
                let item = children.pop().expect("length was two");
                let items = self.collect_record_items(item, original)?;
                let prefixes = self
                    .collect_record_fields(children.pop().expect("one child remains"), original)?;
                let mut fields = BTreeSet::new();
                for prefix in prefixes {
                    for (key, value) in &items {
                        let mut candidate = prefix.clone();
                        insert_field(&mut candidate, key, value.clone())?;
                        fields.insert(candidate);
                    }
                }
                Ok(fields)
            }
        }
    }

    #[cfg(test)]
    fn collect_record_items(
        &self,
        term: ParsedTerm,
        original: usize,
    ) -> Result<BTreeSet<(String, ParsedTerm)>, ParseError> {
        if let ParsedTerm::Ambiguity(alternatives) = term {
            let mut items = BTreeSet::new();
            for alternative in alternatives {
                items.extend(self.collect_record_items(alternative, original)?);
            }
            Ok(items)
        } else {
            Ok(BTreeSet::from([self.record_item(term, original)?]))
        }
    }

    #[cfg(test)]
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

#[cfg(test)]
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

fn insert_packed_field(
    fields: &mut BTreeMap<String, Rc<PackedTerm>>,
    key: &str,
    value: Rc<PackedTerm>,
) -> Result<(), ParseError> {
    if fields.insert(key.to_owned(), value).is_some() {
        Err(record_error(format!(
            "Duplicate record production key: {key}"
        )))
    } else {
        Ok(())
    }
}

fn cmp_packed_record_fields(
    left: &BTreeMap<String, Rc<PackedTerm>>,
    right: &BTreeMap<String, Rc<PackedTerm>>,
) -> std::cmp::Ordering {
    left.iter()
        .zip(right)
        .map(|((left_key, left_value), (right_key, right_value))| {
            left_key
                .cmp(right_key)
                .then_with(|| cmp_packed_structurally(left_value, right_value))
        })
        .find(|ordering| !ordering.is_eq())
        .unwrap_or_else(|| left.len().cmp(&right.len()))
}

fn nonterminal(sort: Sort) -> ProductionItem {
    ProductionItem::NonTerminal { sort, name: None }
}

fn record_error(message: impl Into<String>) -> ParseError {
    ParseError::RecordProduction {
        message: message.into(),
    }
}

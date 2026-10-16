//! ```toml algorithm
//! id = "parser.grammar.records"
//! name = "generation of record-pattern productions"
//! sites = ["Grammar::add_record_productions", "Grammar::add_record_production"]
//! variable = "F = record fields"
//! counters = []
//! no_counter = "record-production generation has no dedicated counter"
//!
//! [[cost]]
//! mode = "one record declaration"
//! bound = "O(F)"
//! ```
//!
//! ```toml algorithm
//! id = "parser.disambiguation.collapse_records"
//! name = "collapse of generated record syntax"
//! sites = ["Grammar::collapse_packed_record_productions"]
//! variable = "N = packed nodes; F = record fields; X = field maps produced by collect_packed_record_fields, the product of the prefix and item alternatives"
//! counters = []
//! no_counter = "record collapse has no dedicated counter"
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one parse forest"
//! bound = "O(N + X x F) plus the structural ordering of the alternatives of each ambiguity with a record production below it, whose pair comparisons the pass shares"
//! ```
//!
//! Generation and collapse of the record-pattern productions of a prefix production: the forms
//! `f(... a: P, b: Q)` that give some of its named arguments, in declaration order, and leave the
//! others unconstrained (K user manual, "Record-like KApply Patterns").
//!
//! Production generation is O(fields). Packed collapse visits each shared node once through a
//! pointer memo, while field collection recurses without a memo and multiplies prefix and item
//! alternatives; generated field names saturate a reserved-name set.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use k_rust_kore::measure::{self, Algorithm};

use crate::definition::ProductionItem;
use crate::kast::{Sort, Term, TermSpan};

use super::{
    Grammar, Item, PackedNode, PackedTerm, ParseError, RecordProduction, RecordProductionKind,
    StructuralOrder, canonical_packed_error, cmp_packed_structurally,
    packed_terms_in_structural_order,
};
#[cfg(test)]
use super::{ParsedParts, ParsedTerm};

type PackedRecordResult = Result<Rc<PackedTerm>, ParseError>;
type PackedRecordMemo = HashMap<*const PackedTerm, (Rc<PackedTerm>, PackedRecordResult)>;

/// The order in which one record collapse visits the alternatives of an ambiguity.
///
/// The order is observable only below a record production: collapsing a record allocates
/// generated field names in visiting order, and only a record's field collection fails. A node
/// with no record production at or below it collapses to an equal node, without error and
/// without touching the names, whatever order its ambiguities are visited in, so the
/// alternatives of such an ambiguity are visited in the order of their set, and the others
/// in structural order, which fixes the names generated.
#[derive(Default)]
struct RecordCollapseOrder {
    structural: StructuralOrder,
    /// Whether a record production occurs at or below each node asked about, by address; each
    /// entry keeps its node alive, so no other node takes the address meanwhile.
    records: HashMap<*const PackedTerm, (Rc<PackedTerm>, bool)>,
}

impl RecordCollapseOrder {
    /// The alternatives of `ambiguity` in visiting order.
    fn alternatives(
        &mut self,
        grammar: &Grammar,
        ambiguity: &Rc<PackedTerm>,
        alternatives: &BTreeSet<Rc<PackedTerm>>,
    ) -> Vec<Rc<PackedTerm>> {
        if self.has_record(grammar, ambiguity) {
            self.structural.sorted(alternatives)
        } else {
            alternatives.iter().cloned().collect()
        }
    }

    /// Whether a record production occurs at or below `term`.
    fn has_record(&mut self, grammar: &Grammar, term: &Rc<PackedTerm>) -> bool {
        if let Some((_, known)) = self.records.get(&Rc::as_ptr(term)) {
            return *known;
        }
        let found = crate::stack::guarded(|| match &term.node {
            PackedNode::Term(_) => false,
            PackedNode::Ambiguity(alternatives) => alternatives
                .iter()
                .any(|alternative| self.has_record(grammar, alternative)),
            PackedNode::Production {
                production,
                children,
                ..
            }
            | PackedNode::InstantiatedProduction {
                production,
                children,
                ..
            } => {
                grammar.productions[*production].record.is_some()
                    || children.iter().any(|child| self.has_record(grammar, child))
            }
        });
        self.records
            .insert(Rc::as_ptr(term), (Rc::clone(term), found));
        found
    }
}

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
        let _span = measure::algorithm_span(Algorithm::ParserDisambiguationCollapseRecords);
        let mut generated = BTreeMap::new();
        let mut next = 0;
        let mut memo = HashMap::new();
        self.collapse_packed_records(
            term,
            &mut names,
            &mut generated,
            &mut next,
            &mut memo,
            &mut RecordCollapseOrder::default(),
        )
    }

    fn collapse_packed_records(
        &self,
        term: Rc<PackedTerm>,
        names: &mut BTreeSet<String>,
        generated: &mut BTreeMap<(TermSpan, usize, usize), String>,
        next: &mut usize,
        memo: &mut PackedRecordMemo,
        order: &mut RecordCollapseOrder,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        crate::stack::guarded(|| {
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
                    // Invariant: every processed alternative is memoized recursively, and the
                    // alternatives are processed in a deterministic order, structural where a
                    // record below allocates generated names in it (`RecordCollapseOrder`);
                    // `retained` holds the successful flattened results.
                    for alternative in order.alternatives(self, &term, alternatives) {
                        match self.collapse_packed_records(
                            Rc::clone(&alternative),
                            names,
                            generated,
                            next,
                            memo,
                            order,
                        ) {
                            Ok(collapsed) => match &collapsed.node {
                                PackedNode::Ambiguity(nested) => {
                                    retained.extend(nested.iter().cloned());
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
                        self.collapse_packed_records(collapsed, names, generated, next, memo, order)
                    }),
                PackedNode::Production {
                    production,
                    children,
                    metadata,
                } => {
                    let mut collapsed_children = Vec::with_capacity(children.len());
                    let mut errors = Vec::new();
                    // Invariant: each completed prefix of `collapsed_children` corresponds to the
                    // same prefix of input children; errors retain the original child identity.
                    for child in children {
                        match self.collapse_packed_records(
                            Rc::clone(child),
                            names,
                            generated,
                            next,
                            memo,
                            order,
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
        })
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
                        return PackedTerm::leaf(omitted_field_variable(
                            name.clone(),
                            root_metadata.span,
                        ));
                    }
                    // Invariant: every rejected candidate is already reserved and `next`
                    // strictly increases until the first definition-wide fresh name is inserted.
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
                    PackedTerm::leaf(omitted_field_variable(name, root_metadata.span))
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
        crate::stack::guarded(|| {
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
                    let prefixes =
                        self.collect_packed_record_fields(Rc::clone(prefix), original)?;
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
        })
    }

    fn collect_packed_record_items(
        &self,
        term: Rc<PackedTerm>,
        original: usize,
    ) -> Result<BTreeSet<(String, Rc<PackedTerm>)>, ParseError> {
        crate::stack::guarded(|| {
            if let PackedNode::Ambiguity(alternatives) = &term.node {
                let mut items = BTreeSet::new();
                for alternative in packed_terms_in_structural_order(alternatives) {
                    items.extend(self.collect_packed_record_items(alternative, original)?);
                }
                Ok(items)
            } else {
                Ok(BTreeSet::from([self.packed_record_item(term, original)?]))
            }
        })
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
        crate::stack::guarded(|| match term.into_parts() {
            ParsedParts::Term(leaf) => Ok(ParsedTerm::Term(leaf)),
            ParsedParts::Ambiguity(alternatives) => alternatives
                .into_iter()
                .map(|term| self.collapse_records(term, names, generated, next))
                .collect::<Result<BTreeSet<_>, _>>()
                .map(ParsedTerm::Ambiguity),
            ParsedParts::Production {
                production,
                children,
                metadata,
            } if self.productions[production].record.is_some() => {
                let collapsed =
                    self.collapse_record(production, children, metadata, names, generated, next)?;
                self.collapse_records(collapsed, names, generated, next)
            }
            ParsedParts::Production {
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
            ParsedParts::InstantiatedProduction { .. } => {
                unreachable!("record productions collapse before sort inference")
            }
        })
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
                        return ParsedTerm::Term(omitted_field_variable(
                            name.clone(),
                            root_metadata.span,
                        ));
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
                    ParsedTerm::Term(omitted_field_variable(name, root_metadata.span))
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
        crate::stack::guarded(|| {
            let (production, mut children) = match term.into_parts() {
                ParsedParts::Ambiguity(alternatives) => {
                    let mut fields = BTreeSet::new();
                    for alternative in alternatives {
                        fields.extend(self.collect_record_fields(alternative, original)?);
                    }
                    return Ok(fields);
                }
                ParsedParts::Production {
                    production,
                    children,
                    ..
                } => (production, children),
                _ => return Err(record_error("malformed generated record production")),
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
                    let prefixes = self.collect_record_fields(
                        children.pop().expect("one child remains"),
                        original,
                    )?;
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
        })
    }

    #[cfg(test)]
    fn collect_record_items(
        &self,
        term: ParsedTerm,
        original: usize,
    ) -> Result<BTreeSet<(String, ParsedTerm)>, ParseError> {
        crate::stack::guarded(|| match term.into_parts() {
            ParsedParts::Ambiguity(alternatives) => {
                let mut items = BTreeSet::new();
                for alternative in alternatives {
                    items.extend(self.collect_record_items(alternative, original)?);
                }
                Ok(items)
            }
            term => Ok(BTreeSet::from([
                self.record_item(ParsedTerm::from(term), original)?
            ])),
        })
    }

    #[cfg(test)]
    fn record_item(
        &self,
        term: ParsedTerm,
        original: usize,
    ) -> Result<(String, ParsedTerm), ParseError> {
        let ParsedParts::Production {
            production,
            mut children,
            ..
        } = term.into_parts()
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

/// The anonymous variable that stands for an omitted field of a record pattern written at
/// `span`.
///
/// The variable is part of the term written at `span`, so it is given that span. Every collapse
/// of the pattern gives the field one name (`generated`, keyed by the span, the original
/// production and the field), and the name is reserved for it, so no other variable of the
/// forest has it. The span and the name together therefore identify one source occurrence,
/// whichever reading of the pattern's text contains it, which is the identity sort inference
/// gives an anonymous variable across the trees of a forest (`TypingVariable::Anonymous`). A tree
/// holds at most one node of the original production at that span, since the production's `(`
/// and `)` are terminals, so the variable occurs once in a tree, as an anonymous variable does.
/// A pattern without a span gives the field a new name in each collapse and no identity, and
/// its variable stays without a span.
fn omitted_field_variable(name: String, span: Option<TermSpan>) -> Term {
    let variable = Term::Variable { name, sort: None };
    match span {
        Some(span) => variable.with_metadata(super::TermMetadata {
            span: Some(span),
            ..super::TermMetadata::default()
        }),
        None => variable,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kast::TermMetadata;

    /// Record collapse orders an ambiguity's alternatives structurally exactly when a record
    /// production occurs below it, through any number of shared nodes: there the order
    /// allocates generated names. Elsewhere it keeps the order of the set.
    #[test]
    fn alternatives_are_ordered_only_above_a_record_production() {
        let mut grammar = Grammar::default();
        for label in ["wrap", "record"] {
            grammar
                .add(
                    Sort::new("K"),
                    vec![ProductionItem::NonTerminal {
                        sort: Sort::new("K"),
                        name: None,
                    }],
                    Some(crate::kast::Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
        }
        grammar.productions[1].record = Some(RecordProduction {
            original: 0,
            kind: RecordProductionKind::Main,
        });
        let leaf = |name: &str| PackedTerm::leaf(Term::variable(name));
        let wrap = |child| PackedTerm::production(0, vec![child], TermMetadata::default());
        let record = PackedTerm::production(1, vec![leaf("R")], TermMetadata::default());
        let shared = wrap(wrap(record));
        let record_free = (0..8).map(|index| wrap(leaf(&format!("V{index}"))));
        let plain = record_free.clone().collect::<BTreeSet<_>>();
        let above = record_free
            .chain([wrap(Rc::clone(&shared))])
            .collect::<BTreeSet<_>>();
        let mut order = RecordCollapseOrder::default();

        let ambiguity = PackedTerm::ambiguity(plain.clone());
        assert_eq!(
            order.alternatives(&grammar, &ambiguity, &plain),
            plain.iter().cloned().collect::<Vec<_>>()
        );
        let ambiguity = PackedTerm::ambiguity(above.clone());
        assert_eq!(
            order.alternatives(&grammar, &ambiguity, &above),
            packed_terms_in_structural_order(&above)
        );
        assert!(order.has_record(&grammar, &shared));
        assert!(!order.has_record(&grammar, &wrap(leaf("V0"))));
        assert_ne!(
            plain.iter().cloned().collect::<Vec<_>>(),
            packed_terms_in_structural_order(&plain),
            "the set order must differ from the structural order for the test to tell them apart"
        );
    }
}

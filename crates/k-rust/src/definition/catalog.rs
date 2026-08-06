//! Deterministic indexes over the productions visible from a resolved module.

use std::collections::{BTreeMap, BTreeSet};

use super::ast::{ProductionItem, Sentence};
use super::ordering::{compare_sentences, sentence_equivalent};
use super::resolve::{ModuleId, ResolvedDefinition};
use crate::kast::{Label, Sort};

const FUNCTION_ATTRIBUTE: &str = "function";
const TOKEN_ATTRIBUTE: &str = "token";

/// A production identity scoped to one [`ProductionCatalog`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProductionId(pub usize);

impl std::fmt::Display for ProductionId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "production #{}", self.0)
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LabelHead(String);

impl LabelHead {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&Label> for LabelHead {
    fn from(label: &Label) -> Self {
        Self(label.name.clone())
    }
}

impl std::fmt::Display for LabelHead {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SortHead(String);

impl SortHead {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&Sort> for SortHead {
    fn from(sort: &Sort) -> Self {
        Self(sort.name.clone())
    }
}

impl std::fmt::Display for SortHead {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ProductionSignature {
    pub arguments: Vec<Sort>,
    pub result: Sort,
}

/// All production views derived from one module's visible sentence set.
///
/// IDs follow deterministic dependency-first sentence order. Scala-same
/// productions are collapsed before IDs are assigned.
#[derive(Clone, Debug)]
pub struct ProductionCatalog<'a> {
    productions: Vec<&'a Sentence>,
    local: BTreeSet<ProductionId>,
    sorted: Vec<ProductionId>,
    by_label: BTreeMap<LabelHead, Vec<ProductionId>>,
    by_sort: BTreeMap<SortHead, Vec<ProductionId>>,
    token_by_sort: BTreeMap<Sort, Vec<ProductionId>>,
    function_labels: BTreeSet<LabelHead>,
    signatures: BTreeMap<LabelHead, BTreeSet<ProductionSignature>>,
}

impl<'a> ProductionCatalog<'a> {
    pub fn new(
        visible_sentences: impl IntoIterator<Item = &'a Sentence>,
        local_sentences: impl IntoIterator<Item = &'a Sentence>,
    ) -> Self {
        let mut productions: Vec<&'a Sentence> = Vec::new();
        for sentence in visible_sentences {
            if matches!(sentence, Sentence::Production { .. })
                && !productions
                    .iter()
                    .any(|existing| sentence_equivalent(existing, sentence))
            {
                productions.push(sentence);
            }
        }

        let local_sentences = local_sentences
            .into_iter()
            .filter(|sentence| matches!(sentence, Sentence::Production { .. }))
            .collect::<Vec<_>>();
        let local = productions
            .iter()
            .enumerate()
            .filter(|(_, production)| {
                local_sentences
                    .iter()
                    .any(|local| sentence_equivalent(production, local))
            })
            .map(|(index, _)| ProductionId(index))
            .collect();

        let mut sorted = (0..productions.len()).map(ProductionId).collect::<Vec<_>>();
        sorted.sort_by(|left, right| {
            compare_sentences(productions[left.0], productions[right.0])
                .expect("productions always have Scala ordering")
                .then(left.cmp(right))
        });

        let mut catalog = Self {
            productions,
            local,
            sorted,
            by_label: BTreeMap::new(),
            by_sort: BTreeMap::new(),
            token_by_sort: BTreeMap::new(),
            function_labels: BTreeSet::new(),
            signatures: BTreeMap::new(),
        };
        catalog.build_indexes();
        catalog
    }

    pub fn from_visible(sentences: impl IntoIterator<Item = &'a Sentence>) -> Self {
        Self::new(sentences, std::iter::empty())
    }

    pub fn len(&self) -> usize {
        self.productions.len()
    }

    pub fn is_empty(&self) -> bool {
        self.productions.is_empty()
    }

    pub fn ids(&self) -> impl ExactSizeIterator<Item = ProductionId> {
        (0..self.len()).map(ProductionId)
    }

    pub fn production(&self, id: ProductionId) -> &'a Sentence {
        self.productions[id.0]
    }

    pub fn productions(&self) -> impl ExactSizeIterator<Item = (ProductionId, &'a Sentence)> + '_ {
        self.ids().map(|id| (id, self.production(id)))
    }

    pub fn local_ids(&self) -> &BTreeSet<ProductionId> {
        &self.local
    }

    pub fn local_productions(
        &self,
    ) -> impl ExactSizeIterator<Item = (ProductionId, &'a Sentence)> + '_ {
        self.local
            .iter()
            .copied()
            .map(|id| (id, self.production(id)))
    }

    pub fn is_local(&self, id: ProductionId) -> bool {
        self.local.contains(&id)
    }

    pub fn sorted_ids(&self) -> &[ProductionId] {
        &self.sorted
    }

    pub fn sorted_productions(
        &self,
    ) -> impl ExactSizeIterator<Item = (ProductionId, &'a Sentence)> + '_ {
        self.sorted
            .iter()
            .copied()
            .map(|id| (id, self.production(id)))
    }

    pub fn productions_by_label(&self) -> &BTreeMap<LabelHead, Vec<ProductionId>> {
        &self.by_label
    }

    pub fn productions_for(&self, label: &LabelHead) -> &[ProductionId] {
        self.by_label.get(label).map_or(&[], Vec::as_slice)
    }

    pub fn productions_by_sort(&self) -> &BTreeMap<SortHead, Vec<ProductionId>> {
        &self.by_sort
    }

    pub fn productions_for_sort(&self, sort: &SortHead) -> &[ProductionId] {
        self.by_sort.get(sort).map_or(&[], Vec::as_slice)
    }

    pub fn token_productions_by_sort(&self) -> &BTreeMap<Sort, Vec<ProductionId>> {
        &self.token_by_sort
    }

    pub fn token_productions_for(&self, sort: &Sort) -> &[ProductionId] {
        self.token_by_sort.get(sort).map_or(&[], Vec::as_slice)
    }

    pub fn defined_labels(&self) -> impl ExactSizeIterator<Item = &LabelHead> {
        self.by_label.keys()
    }

    pub fn local_labels(&self) -> BTreeSet<LabelHead> {
        self.local
            .iter()
            .filter_map(|id| production_label(self.production(*id)).map(LabelHead::from))
            .collect()
    }

    pub fn function_labels(&self) -> &BTreeSet<LabelHead> {
        &self.function_labels
    }

    pub fn signatures(&self) -> &BTreeMap<LabelHead, BTreeSet<ProductionSignature>> {
        &self.signatures
    }

    pub fn signatures_for(&self, label: &LabelHead) -> Option<&BTreeSet<ProductionSignature>> {
        self.signatures.get(label)
    }

    fn build_indexes(&mut self) {
        for id in self.ids().collect::<Vec<_>>() {
            let Sentence::Production {
                label,
                parameters,
                sort,
                items,
                attributes,
            } = self.production(id)
            else {
                unreachable!()
            };
            self.by_sort
                .entry(SortHead::from(sort))
                .or_default()
                .push(id);
            if attributes.get(TOKEN_ATTRIBUTE).is_some() {
                self.token_by_sort.entry(sort.clone()).or_default().push(id);
            }
            let Some(label) = label else {
                continue;
            };
            let head = LabelHead::from(label);
            self.by_label.entry(head.clone()).or_default().push(id);
            if attributes.get(FUNCTION_ATTRIBUTE).is_some() {
                self.function_labels.insert(head.clone());
            }
            if parameters.is_empty() {
                self.signatures
                    .entry(head)
                    .or_default()
                    .insert(ProductionSignature {
                        arguments: items
                            .iter()
                            .filter_map(|item| match item {
                                ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                                ProductionItem::RegexTerminal { .. }
                                | ProductionItem::Terminal(_) => None,
                            })
                            .collect(),
                        result: sort.clone(),
                    });
            }
        }
    }
}

impl ResolvedDefinition {
    pub fn production_catalog(&self, module: ModuleId) -> ProductionCatalog<'_> {
        ProductionCatalog::new(
            self.sentences(module),
            self.module(module).local_sentences.iter(),
        )
    }
}

fn production_label(sentence: &Sentence) -> Option<&Label> {
    let Sentence::Production { label, .. } = sentence else {
        return None;
    };
    label.as_ref()
}

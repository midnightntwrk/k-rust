//! Production catalogs group visible productions and build label, sort, hook, and identity indexes in declaration order.
//! Construction costs O(n log n + buckets * eq) with indexed equivalence; `Counter::KompileProductionCatalogsBuilt` measures builds after CQ-12's counter commit.
//!
//! Deterministic indexes over the productions visible from a resolved module.

use std::collections::{BTreeMap, BTreeSet};
use std::{
    marker::PhantomData,
    sync::{Arc, OnceLock},
};

use k_rust_kore::measure::{self, Counter};

use super::ast::{Attributes, ProductionItem, Sentence};
use super::attribute_keys::AttributeKey;
use super::equivalence::{dedup_by_equivalence, production_identity, sentence_equivalent};
use super::resolve::{ModuleId, ResolvedDefinition};
use crate::kast::{Label, ProductionIdentity, Sort};

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
pub struct SortHead {
    name: String,
    parameters: usize,
}

impl SortHead {
    pub fn new(name: impl Into<String>, parameters: usize) -> Self {
        Self {
            name: name.into(),
            parameters,
        }
    }

    pub fn nullary(name: impl Into<String>) -> Self {
        Self::new(name, 0)
    }

    pub fn as_str(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> usize {
        self.parameters
    }
}

impl From<&Sort> for SortHead {
    fn from(sort: &Sort) -> Self {
        Self::new(sort.name.clone(), sort.parameters.len())
    }
}

impl std::fmt::Display for SortHead {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.name)?;
        if self.parameters != 0 {
            formatter.write_str("{")?;
            for parameter in 0..self.parameters {
                if parameter != 0 {
                    formatter.write_str(",")?;
                }
                write!(formatter, "S{parameter}")?;
            }
            formatter.write_str("}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ProductionSignature {
    pub arguments: Vec<Sort>,
    pub result: Sort,
}

/// Owned projection of the production variant of `SentenceKey`.
///
/// Equivalent productions always have equal keys. Non-equivalent productions may share a key
/// and are distinguished by `sentence_equivalent` inside the bucket.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProductionKey {
    label: Option<Label>,
    parameters: Vec<Sort>,
    sort: Sort,
    items: usize,
    first: Option<FirstProductionItem>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum FirstProductionItem {
    NonTerminal(Sort, Option<String>),
    Regex(String),
    Terminal(String),
}

impl ProductionKey {
    fn of(sentence: &Sentence) -> Self {
        let Sentence::Production {
            label,
            parameters,
            sort,
            items,
            ..
        } = sentence
        else {
            unreachable!("production catalogs contain only productions")
        };
        Self {
            label: label.clone(),
            parameters: parameters.clone(),
            sort: sort.clone(),
            items: items.len(),
            first: items.first().map(|item| match item {
                ProductionItem::NonTerminal { sort, name } => {
                    FirstProductionItem::NonTerminal(sort.clone(), name.clone())
                }
                ProductionItem::RegexTerminal { regex, .. } => {
                    FirstProductionItem::Regex(regex.clone())
                }
                ProductionItem::Terminal(text) => FirstProductionItem::Terminal(text.clone()),
            }),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FreshGeneratorError {
    MissingLabel {
        production: ProductionId,
        sort: Sort,
    },
    MultipleGenerators {
        sort: Sort,
        labels: BTreeSet<Label>,
    },
}

impl std::fmt::Display for FreshGeneratorError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingLabel { production, sort } => {
                write!(
                    formatter,
                    "{production} is an unlabeled fresh generator for sort {sort}"
                )
            }
            Self::MultipleGenerators { sort, labels } => write!(
                formatter,
                "found more than one fresh generator for sort {sort}: {}",
                labels
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl std::error::Error for FreshGeneratorError {}

/// All production views derived from one module's visible sentence set.
///
/// IDs follow deterministic dependency-first sentence order. Scala-same
/// productions are collapsed before IDs are assigned.
#[derive(Clone, Debug)]
pub struct ProductionCatalog<'a> {
    productions: Vec<Arc<Sentence>>,
    identities: Vec<ProductionIdentity>,
    by_identity: BTreeMap<ProductionIdentity, ProductionId>,
    local: BTreeSet<ProductionId>,
    by_label: BTreeMap<LabelHead, Vec<ProductionId>>,
    by_sort: BTreeMap<SortHead, Vec<ProductionId>>,
    token_by_sort: BTreeMap<Sort, Vec<ProductionId>>,
    function_labels: BTreeSet<LabelHead>,
    signatures: BTreeMap<LabelHead, BTreeSet<ProductionSignature>>,
    attributes_by_label: BTreeMap<LabelHead, Attributes>,
    result_sort_by_label: BTreeMap<LabelHead, Sort>,
    macro_labels: BTreeSet<Label>,
    by_key: OnceLock<BTreeMap<ProductionKey, Vec<ProductionId>>>,
    marker: PhantomData<&'a Sentence>,
}

impl<'a> ProductionCatalog<'a> {
    pub fn new(
        visible_sentences: impl IntoIterator<Item = &'a Sentence>,
        local_sentences: impl IntoIterator<Item = &'a Sentence>,
    ) -> Self {
        let productions = dedup_by_equivalence(
            visible_sentences
                .into_iter()
                .filter(|sentence| matches!(sentence, Sentence::Production { .. })),
        );
        Self::from_productions(productions, local_sentences)
    }

    #[allow(dead_code)]
    pub(crate) fn from_deduplicated(
        visible_sentences: impl IntoIterator<Item = &'a Sentence>,
        local_sentences: impl IntoIterator<Item = &'a Sentence>,
    ) -> Self {
        let productions = visible_sentences
            .into_iter()
            .filter(|sentence| matches!(sentence, Sentence::Production { .. }))
            .collect::<Vec<_>>();
        debug_assert!(
            productions_are_deduplicated(&productions),
            "ProductionCatalog::from_deduplicated received equivalent productions"
        );
        Self::from_productions(productions, local_sentences)
    }

    pub(crate) fn from_deduplicated_arcs(
        visible_sentences: impl IntoIterator<Item = Arc<Sentence>>,
        local_sentences: impl IntoIterator<Item = Arc<Sentence>>,
    ) -> Self {
        let productions = visible_sentences
            .into_iter()
            .filter(|sentence| matches!(&**sentence, Sentence::Production { .. }))
            .collect::<Vec<_>>();
        debug_assert!(productions_are_deduplicated(
            &productions.iter().map(Arc::as_ref).collect::<Vec<_>>()
        ));
        Self::from_arc_productions(productions, local_sentences)
    }

    fn from_productions(
        productions: Vec<&'a Sentence>,
        local_sentences: impl IntoIterator<Item = &'a Sentence>,
    ) -> Self {
        Self::from_arc_productions(
            productions
                .into_iter()
                .map(|sentence| Arc::new(sentence.clone()))
                .collect(),
            local_sentences
                .into_iter()
                .filter(|sentence| matches!(sentence, Sentence::Production { .. }))
                .map(|sentence| Arc::new(sentence.clone())),
        )
    }

    fn from_arc_productions(
        productions: Vec<Arc<Sentence>>,
        local_sentences: impl IntoIterator<Item = Arc<Sentence>>,
    ) -> Self {
        let local_sentences = local_sentences
            .into_iter()
            .filter(|sentence| matches!(&**sentence, Sentence::Production { .. }))
            .collect::<Vec<_>>();

        let mut catalog = Self {
            productions,
            identities: Vec::new(),
            by_identity: BTreeMap::new(),
            local: BTreeSet::new(),
            by_label: BTreeMap::new(),
            by_sort: BTreeMap::new(),
            token_by_sort: BTreeMap::new(),
            function_labels: BTreeSet::new(),
            signatures: BTreeMap::new(),
            attributes_by_label: BTreeMap::new(),
            result_sort_by_label: BTreeMap::new(),
            macro_labels: BTreeSet::new(),
            by_key: OnceLock::new(),
            marker: PhantomData,
        };
        catalog.local = local_sentences
            .into_iter()
            .filter_map(|local| catalog.find_equivalent(local.as_ref()))
            .collect();
        catalog.build_indexes();
        measure::bump(Counter::KompileProductionCatalogsBuilt);
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

    pub fn production(&self, id: ProductionId) -> &Sentence {
        &self.productions[id.0]
    }

    /// Return the content identity aligned with `id`.
    pub fn identity(&self, id: ProductionId) -> ProductionIdentity {
        self.identities[id.0]
    }

    /// Find the catalog position for a content identity.
    pub fn lookup(&self, identity: &ProductionIdentity) -> Option<ProductionId> {
        self.by_identity.get(identity).copied()
    }

    /// Find the smallest ID structurally equivalent to `source`.
    pub(crate) fn find_equivalent(&self, source: &Sentence) -> Option<ProductionId> {
        self.by_key
            .get_or_init(|| {
                let mut by_key = BTreeMap::<_, Vec<_>>::new();
                for (id, production) in self.productions() {
                    by_key
                        .entry(ProductionKey::of(production))
                        .or_default()
                        .push(id);
                }
                by_key
            })
            .get(&ProductionKey::of(source))?
            .iter()
            .copied()
            .find(|id| sentence_equivalent(source, self.production(*id)))
    }

    pub fn productions(&self) -> impl ExactSizeIterator<Item = (ProductionId, &Sentence)> + '_ {
        self.ids().map(|id| (id, self.production(id)))
    }

    pub fn local_ids(&self) -> &BTreeSet<ProductionId> {
        &self.local
    }

    pub fn local_productions(
        &self,
    ) -> impl ExactSizeIterator<Item = (ProductionId, &Sentence)> + '_ {
        self.local
            .iter()
            .copied()
            .map(|id| (id, self.production(id)))
    }

    pub fn is_local(&self, id: ProductionId) -> bool {
        self.local.contains(&id)
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

    pub fn attributes_by_label(&self) -> &BTreeMap<LabelHead, Attributes> {
        &self.attributes_by_label
    }

    pub fn attributes_for(&self, label: &LabelHead) -> Option<&Attributes> {
        self.attributes_by_label.get(label)
    }

    /// Scala's `sortFor`, made deterministic by selecting the first stable ID.
    pub fn result_sort_by_label(&self) -> &BTreeMap<LabelHead, Sort> {
        &self.result_sort_by_label
    }

    pub fn result_sort_for(&self, label: &LabelHead) -> Option<&Sort> {
        self.result_sort_by_label.get(label)
    }

    pub fn macro_labels(&self) -> &BTreeSet<Label> {
        &self.macro_labels
    }

    pub fn fresh_generators(&self) -> Result<BTreeMap<Sort, Label>, FreshGeneratorError> {
        let mut grouped = BTreeMap::<Sort, BTreeSet<Label>>::new();
        for (id, production) in self.productions() {
            let Sentence::Production {
                label,
                sort,
                attributes,
                ..
            } = production
            else {
                unreachable!()
            };
            if !attributes.has(AttributeKey::FreshGenerator) {
                continue;
            }
            let Some(label) = label else {
                return Err(FreshGeneratorError::MissingLabel {
                    production: id,
                    sort: sort.clone(),
                });
            };
            grouped
                .entry(sort.clone())
                .or_default()
                .insert(label.clone());
        }
        grouped
            .into_iter()
            .map(|(sort, labels)| {
                if labels.len() != 1 {
                    return Err(FreshGeneratorError::MultipleGenerators { sort, labels });
                }
                Ok((sort, labels.into_iter().next().expect("length was one")))
            })
            .collect()
    }

    fn build_indexes(&mut self) {
        for id in self.ids().collect::<Vec<_>>() {
            let identity = production_identity(self.production(id))
                .expect("production catalogs contain only productions");
            self.identities.push(identity);
            let previous = self.by_identity.insert(identity, id);
            debug_assert!(
                previous.is_none(),
                "distinct catalog productions have the same ProductionIdentity"
            );
            let sentence = self.production(id).clone();
            let Sentence::Production {
                label,
                parameters,
                sort,
                items,
                attributes,
            } = &sentence
            else {
                unreachable!()
            };
            self.by_sort
                .entry(SortHead::from(sort))
                .or_default()
                .push(id);
            if attributes.has(AttributeKey::Token) {
                self.token_by_sort.entry(sort.clone()).or_default().push(id);
            }
            if attributes.has_any(&AttributeKey::MACRO_LIKE) {
                self.macro_labels
                    .insert(label.clone().unwrap_or_else(|| Label::new("")));
            }
            let Some(label) = label else {
                continue;
            };
            let head = LabelHead::from(label);
            self.by_label.entry(head.clone()).or_default().push(id);
            if attributes.has(AttributeKey::Function) {
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

        for (head, ids) in &self.by_label {
            self.attributes_by_label.insert(
                head.clone(),
                Attributes::merge(ids.iter().map(|id| self.production(*id).attributes()))
                    .unwrap_or_else(|error| error.merged),
            );
            let Sentence::Production { sort, .. } = self.production(ids[0]) else {
                unreachable!()
            };
            self.result_sort_by_label.insert(head.clone(), sort.clone());
        }
    }
}

impl ResolvedDefinition {
    pub fn production_catalog(&self, module: ModuleId) -> ProductionCatalog<'_> {
        self.production_catalogs[module.0.index()]
            .get_or_init(|| {
                ProductionCatalog::from_deduplicated_arcs(
                    self.sentence_arcs(module),
                    self.local_sentence_arcs(module),
                )
            })
            .clone()
    }
}

fn productions_are_deduplicated(productions: &[&Sentence]) -> bool {
    let mut by_key = BTreeMap::<ProductionKey, Vec<&Sentence>>::new();
    for &production in productions {
        let bucket = by_key.entry(ProductionKey::of(production)).or_default();
        if bucket
            .iter()
            .any(|candidate| sentence_equivalent(candidate, production))
        {
            return false;
        }
        bucket.push(production);
    }
    true
}

fn production_label(sentence: &Sentence) -> Option<&Label> {
    let Sentence::Production { label, .. } = sentence else {
        return None;
    };
    label.as_ref()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "from_deduplicated received equivalent productions")]
    fn deduplicated_constructor_checks_its_precondition() {
        let production = Sentence::Production {
            label: Some(Label::new("same")),
            parameters: Vec::new(),
            sort: Sort::new("Sort"),
            items: Vec::new(),
            attributes: Attributes::default(),
        };

        let _ = ProductionCatalog::from_deduplicated([&production, &production], []);
    }

    #[test]
    fn identity_index_round_trips_every_catalog_position() {
        let first = Sentence::Production {
            label: Some(Label::new("first")),
            parameters: Vec::new(),
            sort: Sort::new("Sort"),
            items: Vec::new(),
            attributes: Attributes::default(),
        };
        let second = Sentence::Production {
            label: Some(Label::new("second")),
            parameters: Vec::new(),
            sort: Sort::new("Sort"),
            items: Vec::new(),
            attributes: Attributes::default(),
        };
        let catalog = ProductionCatalog::from_visible([&first, &second]);

        for id in catalog.ids() {
            assert_eq!(catalog.lookup(&catalog.identity(id)), Some(id));
        }
    }
}

//! Derived subsort and production-overload relations.

use std::collections::{BTreeMap, BTreeSet};

use super::ast::{ProductionItem, Sentence};
use super::ordering::{compare_sentences, sentence_equivalent};
use super::partial_order::{Cycle, PartialOrder};
use super::resolve::{ModuleId, ResolvedDefinition};
use crate::kast::Sort;

const KLABEL_ATTRIBUTE: &str = "klabel";
const OVERLOAD_ATTRIBUTE: &str = "overload";

/// An index into the deterministic production list owned by an [`OverloadOrder`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProductionId(pub usize);

impl std::fmt::Display for ProductionId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "production #{}", self.0)
    }
}

#[derive(Clone, Debug)]
pub struct OverloadOrder<'a> {
    productions: Vec<&'a Sentence>,
    order: PartialOrder<ProductionId>,
}

impl<'a> OverloadOrder<'a> {
    pub fn order(&self) -> &PartialOrder<ProductionId> {
        &self.order
    }

    pub fn production(&self, id: ProductionId) -> &'a Sentence {
        self.productions[id.0]
    }

    pub fn productions(&self) -> impl ExactSizeIterator<Item = (ProductionId, &'a Sentence)> + '_ {
        self.productions
            .iter()
            .enumerate()
            .map(|(index, sentence)| (ProductionId(index), *sentence))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    CircularSubsort(Cycle<Sort>),
    CircularOverload(Cycle<ProductionId>),
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CircularSubsort(error) => error.fmt(formatter),
            Self::CircularOverload(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for Error {}

/// Compute Scala's semantic or syntactic subsort relation.
///
/// Unlabeled injections participate in both relations. Labeled injections only
/// participate in the syntactic relation, and parametric productions participate
/// in neither.
pub fn compute_subsorts<'a>(
    sentences: impl IntoIterator<Item = &'a Sentence>,
    syntactic: bool,
) -> Result<PartialOrder<Sort>, Cycle<Sort>> {
    let relations = sentences
        .into_iter()
        .filter_map(|sentence| {
            let Sentence::Production {
                label,
                parameters,
                sort,
                items,
                ..
            } = sentence
            else {
                return None;
            };
            let [
                ProductionItem::NonTerminal {
                    sort: child_sort, ..
                },
            ] = items.as_slice()
            else {
                return None;
            };
            (parameters.is_empty() && (label.is_none() || syntactic))
                .then(|| (child_sort.clone(), sort.clone()))
        })
        .collect::<BTreeSet<_>>();
    PartialOrder::new(relations)
}

/// Compute Scala's combined explicit and legacy production-overload relation.
pub fn compute_overloads<'a>(
    sentences: impl IntoIterator<Item = &'a Sentence>,
    subsorts: &PartialOrder<Sort>,
) -> Result<OverloadOrder<'a>, Cycle<ProductionId>> {
    let mut productions = sentences
        .into_iter()
        .filter(|sentence| matches!(sentence, Sentence::Production { .. }))
        .collect::<Vec<_>>();
    productions.sort_by(|left, right| {
        compare_sentences(left, right).expect("productions always have Scala ordering")
    });

    let mut explicit = BTreeMap::<String, Vec<ProductionId>>::new();
    let mut legacy = BTreeMap::<String, Vec<ProductionId>>::new();
    for (index, production) in productions.iter().enumerate() {
        let id = ProductionId(index);
        let Sentence::Production {
            label, attributes, ..
        } = production
        else {
            unreachable!()
        };
        if let Some(group) = attributes.get_str(OVERLOAD_ATTRIBUTE) {
            explicit.entry(group.into()).or_default().push(id);
        }
        if let Some(group) = attributes
            .get_str(KLABEL_ATTRIBUTE)
            .or_else(|| label.as_ref().map(|label| label.name.as_str()))
        {
            legacy.entry(group.into()).or_default().push(id);
        }
    }

    let mut relations = BTreeSet::new();
    for group in explicit.values() {
        add_overload_group(&mut relations, group, &productions, subsorts, false);
    }
    for group in legacy.values() {
        add_overload_group(&mut relations, group, &productions, subsorts, true);
    }

    Ok(OverloadOrder {
        productions,
        order: PartialOrder::new(relations)?,
    })
}

fn add_overload_group(
    relations: &mut BTreeSet<(ProductionId, ProductionId)>,
    group: &[ProductionId],
    productions: &[&Sentence],
    subsorts: &PartialOrder<Sort>,
    require_lesser_label: bool,
) {
    for &lesser in group {
        for &greater in group {
            let lesser_sentence = productions[lesser.0];
            let lesser_has_label =
                matches!(lesser_sentence, Sentence::Production { label: Some(_), .. });
            if (!require_lesser_label || lesser_has_label)
                && production_less_than(lesser_sentence, productions[greater.0], subsorts)
            {
                relations.insert((lesser, greater));
            }
        }
    }
}

impl ResolvedDefinition {
    pub fn subsorts(&self, module: ModuleId) -> Result<PartialOrder<Sort>, Cycle<Sort>> {
        compute_subsorts(self.sentences(module), false)
    }

    pub fn syntactic_subsorts(&self, module: ModuleId) -> Result<PartialOrder<Sort>, Cycle<Sort>> {
        compute_subsorts(self.sentences(module), true)
    }

    pub fn overloads(&self, module: ModuleId) -> Result<OverloadOrder<'_>, Error> {
        let sentences = self.sentences(module);
        let subsorts =
            compute_subsorts(sentences.iter().copied(), false).map_err(Error::CircularSubsort)?;
        compute_overloads(sentences, &subsorts).map_err(Error::CircularOverload)
    }
}

fn production_less_than(
    lesser: &Sentence,
    greater: &Sentence,
    subsorts: &PartialOrder<Sort>,
) -> bool {
    let Some((lesser_sort, lesser_arguments)) = production_sorts(lesser) else {
        return false;
    };
    let Some((greater_sort, greater_arguments)) = production_sorts(greater) else {
        return false;
    };
    lesser_arguments.len() == greater_arguments.len()
        && subsorts.less_than_eq(lesser_sort, greater_sort)
        && lesser_arguments
            .iter()
            .zip(&greater_arguments)
            .all(|(lesser, greater)| subsorts.less_than_eq(lesser, greater))
        && (lesser_sort != greater_sort || lesser_arguments != greater_arguments)
        && !sentence_equivalent(lesser, greater)
}

fn production_sorts(sentence: &Sentence) -> Option<(&Sort, Vec<&Sort>)> {
    let Sentence::Production { sort, items, .. } = sentence else {
        return None;
    };
    Some((
        sort,
        items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort),
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect(),
    ))
}

//! Derived subsort, overload, priority, and associativity relations.

use std::collections::{BTreeMap, BTreeSet};

use super::ast::{Associativity, ProductionItem, Sentence};
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

/// The tag pairs constrained by syntax associativity declarations.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct AssociativityRelations {
    pub left: BTreeSet<(String, String)>,
    pub right: BTreeSet<(String, String)>,
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

/// Compute Scala's priority order from adjacent syntax-priority blocks.
///
/// For `A B > C > D E`, the direct relations are `A/C`, `B/C`, `C/D`,
/// and `C/E`; the partial order supplies the transitive relations.
pub fn compute_priorities<'a>(
    sentences: impl IntoIterator<Item = &'a Sentence>,
) -> Result<PartialOrder<String>, Cycle<String>> {
    let mut relations = BTreeSet::new();
    for sentence in sentences {
        let Sentence::SyntaxPriority { priorities, .. } = sentence else {
            continue;
        };
        for adjacent in priorities.windows(2) {
            for greater_precedence in &adjacent[0] {
                for lesser_precedence in &adjacent[1] {
                    relations.insert((greater_precedence.clone(), lesser_precedence.clone()));
                }
            }
        }
    }
    PartialOrder::new(relations)
}

/// Compute the exact tag-pair sets used for left and right associativity.
///
/// A non-associative group is deliberately included in both sets, matching
/// Scala's `buildAssoc` and allowing consumers to reject either nesting side.
pub fn compute_associativities<'a>(
    sentences: impl IntoIterator<Item = &'a Sentence>,
) -> AssociativityRelations {
    let mut relations = AssociativityRelations::default();
    for sentence in sentences {
        let Sentence::SyntaxAssociativity {
            associativity,
            tags,
            ..
        } = sentence
        else {
            continue;
        };
        let targets: &mut [&mut BTreeSet<(String, String)>] = match associativity {
            Associativity::Left => &mut [&mut relations.left],
            Associativity::Right => &mut [&mut relations.right],
            Associativity::NonAssoc => &mut [&mut relations.left, &mut relations.right],
            Associativity::Unspecified => &mut [],
        };
        for target in targets {
            for parent in tags {
                for child in tags {
                    target.insert((parent.clone(), child.clone()));
                }
            }
        }
    }
    relations
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

    pub fn priorities(&self, module: ModuleId) -> Result<PartialOrder<String>, Cycle<String>> {
        compute_priorities(self.sentences(module))
    }

    pub fn associativities(&self, module: ModuleId) -> AssociativityRelations {
        compute_associativities(self.sentences(module))
    }

    pub fn left_assoc(&self, module: ModuleId) -> BTreeSet<(String, String)> {
        self.associativities(module).left
    }

    pub fn right_assoc(&self, module: ModuleId) -> BTreeSet<(String, String)> {
        self.associativities(module).right
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

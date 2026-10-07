//! ```toml algorithm
//! id = "definition.relations.build"
//! name = "construction of subsort, overload, priority, and associativity relations"
//! sites = ["compute_subsorts", "compute_disambiguation_subsorts", "disambiguation_subsort_pairs", "compute_priorities", "compute_associativities", "compute_overloads", "ResolvedDefinition::subsorts", "ResolvedDefinition::overloads", "ResolvedDefinition::priorities"]
//! variable = "P = productions; C = partial-order closure work; g_i = productions in overload group i; a = production arity; q = PartialOrder::less_than_eq cost; eq = sentence-equivalence cost; t_j = tags in associativity declaration j"
//! counters = ["KompilePartialOrdersBuilt", "KompileProductionCatalogsBuilt", "KompileSentenceEquivalenceChecks"]
//! consumes = [
//!   { type = "k_rust::definition::ResolvedDefinition", role = "resolved definition" },
//!   { type = "k_rust::definition::ProductionCatalog<'a>", role = "production lookup" },
//! ]
//! produces = [
//!   { type = "k_rust::definition::PartialOrder<k_rust::kast::Sort>", role = "subsort order" },
//!   { type = "k_rust::definition::PartialOrder<String>", role = "priority order" },
//! ]
//!
//! [[cost]]
//! mode = "one module"
//! bound = "O(P^2 + C)"
//!
//! [[cost]]
//! mode = "compute_overloads"
//! bound = "O(sum g_i^2 x (a x q + eq) + C), plus one ProductionCatalog::from_visible"
//!
//! [[cost]]
//! mode = "compute_associativities"
//! bound = "O(sum t_j^2) tag-pair insertions"
//! ```
//!
//! Five relation builders scan one module's productions and return deterministic partial orders.
//! Complexity: O(P² + closure) over production pairs and partial-order construction.
//! One-shot helpers rebuild per call; `DefinitionViews` memoises each result by module.
//!
//! Derived subsort, overload, priority, and associativity relations.

use std::collections::{BTreeMap, BTreeSet};

use super::ast::{Associativity, ProductionItem, Sentence};
use super::catalog::{ProductionCatalog, ProductionId};
use super::equivalence::sentence_equivalent;
use super::partial_order::{Cycle, PartialOrder};
use super::resolve::{ModuleId, ResolvedDefinition};
use crate::definition::AttributeKey;
use crate::kast::Sort;
use crate::kast::sort_role::KernelSort;

#[derive(Clone, Debug)]
pub struct OverloadOrder<'a> {
    catalog: ProductionCatalog<'a>,
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

    pub fn production(&self, id: ProductionId) -> &Sentence {
        self.catalog.production(id)
    }

    pub fn productions(&self) -> impl ExactSizeIterator<Item = (ProductionId, &Sentence)> + '_ {
        self.catalog.productions()
    }

    pub fn catalog(&self) -> &ProductionCatalog<'a> {
        &self.catalog
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

/// What an unlabelled production whose only item is a nonterminal states about the sort order.
///
/// The order relates sorts, and KORE states it with subsort axioms between sorts.
/// A production with sort parameters states no pair and has no subsort axiom.
/// Only the two kernel shapes state facts K fixes for every sort; every other parametric
/// subsort declaration is unsupported.
pub(crate) enum SubsortDeclaration<'a> {
    /// No sort parameters: `child < parent`, a pair of both relations and a subsort axiom.
    Pair { child: &'a Sort, parent: &'a Sort },
    /// `{S} KItem ::= S`: every sort of K terms is a KItem, which compilation states per sort.
    KernelTop,
    /// `{S} S ::= KBott`: the parse-time bottom is below every sort.
    KernelBottom,
    /// Any other subsort-shaped production with parameters states no fact of the order.
    Parametric,
}

impl<'a> SubsortDeclaration<'a> {
    pub(crate) fn of(production: &'a Sentence) -> Option<Self> {
        let Sentence::Production {
            label: None,
            parameters,
            sort,
            items,
            ..
        } = production
        else {
            return None;
        };
        let [ProductionItem::NonTerminal { sort: child, .. }] = items.as_slice() else {
            return None;
        };
        if parameters.is_empty() {
            Some(Self::Pair {
                child,
                parent: sort,
            })
        } else if *sort == KernelSort::KItem.sort() && parameters.contains(child) {
            Some(Self::KernelTop)
        } else if parameters.contains(sort) && *child == KernelSort::KBott.sort() {
            Some(Self::KernelBottom)
        } else {
            Some(Self::Parametric)
        }
    }
}

/// Compute the semantic or the syntactic subsort relation.
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
        .filter_map(|sentence| subsort_pair(sentence, syntactic))
        .collect::<BTreeSet<_>>();
    PartialOrder::new(relations)
}

/// Compute the semantic subsort relation used by K's rule disambiguation grammar.
///
/// The rule grammar temporarily adds `ListSort ::= ElementSort` for every lowered
/// user list. Those edges participate in sort inference and overload selection,
/// but they do not change the definition's ordinary semantic subsort lattice.
pub fn compute_disambiguation_subsorts(
    sentences: &[&Sentence],
) -> Result<PartialOrder<Sort>, Cycle<Sort>> {
    let mut relations = compute_subsorts(sentences.iter().copied(), false)?
        .direct_relations()
        .clone();
    relations.extend(
        sentences
            .iter()
            .filter_map(|sentence| user_list_subsort_pair(sentence)),
    );
    PartialOrder::new(relations)
}

/// The direct pairs of [`compute_disambiguation_subsorts`]: the semantic subsort pairs of the
/// unlabeled, non-parametric unary productions, plus `(element, list)` for every non-parametric
/// user list.
///
/// No order is built, so a cyclic relation is returned as it is.
pub(crate) fn disambiguation_subsort_pairs(sentences: &[&Sentence]) -> BTreeSet<(Sort, Sort)> {
    sentences
        .iter()
        .flat_map(|sentence| disambiguation_subsort_pairs_of(sentence))
        .collect()
}

/// Whether `sentence` states the pair `(lesser, greater)` of [`disambiguation_subsort_pairs`].
pub(crate) fn states_disambiguation_subsort(
    sentence: &Sentence,
    lesser: &Sort,
    greater: &Sort,
) -> bool {
    disambiguation_subsort_pairs_of(sentence)
        .any(|(child, parent)| child == *lesser && parent == *greater)
}

fn disambiguation_subsort_pairs_of(sentence: &Sentence) -> impl Iterator<Item = (Sort, Sort)> {
    subsort_pair(sentence, false)
        .into_iter()
        .chain(user_list_subsort_pair(sentence))
}

/// The `(child, sort)` pair a non-parametric unary production states: in the semantic relation
/// only when it is unlabeled, in the syntactic relation always.
fn subsort_pair(sentence: &Sentence, syntactic: bool) -> Option<(Sort, Sort)> {
    match SubsortDeclaration::of(sentence) {
        Some(SubsortDeclaration::Pair { child, parent }) => {
            return Some((child.clone(), parent.clone()));
        }
        Some(
            SubsortDeclaration::KernelTop
            | SubsortDeclaration::KernelBottom
            | SubsortDeclaration::Parametric,
        ) => return None,
        None => {}
    }
    let Sentence::Production {
        label: Some(_),
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
    (parameters.is_empty() && syntactic).then(|| (child_sort.clone(), sort.clone()))
}

/// The `(element, list)` pair a non-parametric user-list production states, which the rule
/// grammar adds as `List ::= Element`.
fn user_list_subsort_pair(sentence: &Sentence) -> Option<(Sort, Sort)> {
    let Sentence::Production {
        parameters,
        sort,
        items,
        attributes,
        ..
    } = sentence
    else {
        return None;
    };
    if !parameters.is_empty() || !attributes.has(AttributeKey::UserList) {
        return None;
    }
    let nonterminals = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort),
            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
        })
        .collect::<Vec<_>>();
    let child = match nonterminals.as_slice() {
        [list, child] if *list == sort && *child != sort => Some(*child),
        [child, list] if *list == sort && *child != sort => Some(*child),
        _ => None,
    };
    child.map(|child| (child.clone(), sort.clone()))
}

/// Compute the priority order from adjacent syntax-priority blocks.
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
                // Invariant: `relations` contains every pair from the earlier windows of `priorities`, from the earlier `greater_precedence` entries of `adjacent[0]`, and from the earlier entries of `adjacent[1]`; each iteration consumes one entry of `adjacent[1]`, so each window costs O(|adjacent[0]| * |adjacent[1]|) insertions.
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
/// A non-associative group is included in both sets: it forbids the nesting on either side,
/// where `left` and `right` each forbid it on one.
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
                // Invariant: `target` contains `(parent, c)` for every `c` of `tags` before `child`, and `(p, c)` for every earlier `p` and every `c` of `tags`; each iteration consumes one entry of `tags`, so each `target` costs O(|tags|^2) insertions.
                for child in tags {
                    target.insert((parent.clone(), child.clone()));
                }
            }
        }
    }
    relations
}

/// Compute the production-overload relation over two kinds of groups: productions that share an
/// `overload` attribute value, and productions that share a `klabel` (or, without one, a label).
pub fn compute_overloads<'a>(
    sentences: impl IntoIterator<Item = &'a Sentence>,
    subsorts: &PartialOrder<Sort>,
) -> Result<OverloadOrder<'a>, Cycle<ProductionId>> {
    let catalog = ProductionCatalog::from_visible(sentences);
    compute_overloads_from_catalog(catalog, subsorts)
}

/// Compute overloads from an existing production catalog without rebuilding its indexes.
pub fn compute_overloads_with_catalog<'a>(
    catalog: &ProductionCatalog<'a>,
    subsorts: &PartialOrder<Sort>,
) -> Result<OverloadOrder<'a>, Cycle<ProductionId>> {
    compute_overloads_from_catalog(catalog.clone(), subsorts)
}

fn compute_overloads_from_catalog<'a>(
    catalog: ProductionCatalog<'a>,
    subsorts: &PartialOrder<Sort>,
) -> Result<OverloadOrder<'a>, Cycle<ProductionId>> {
    let mut explicit = BTreeMap::<String, Vec<ProductionId>>::new();
    let mut legacy = BTreeMap::<String, Vec<ProductionId>>::new();
    for (id, production) in catalog.productions() {
        let Sentence::Production {
            label, attributes, ..
        } = production
        else {
            unreachable!()
        };
        if let Some(group) = attributes.string(AttributeKey::Overload) {
            explicit.entry(group.into()).or_default().push(id);
        }
        if let Some(group) = attributes
            .string(AttributeKey::Klabel)
            .or_else(|| label.as_ref().map(|label| label.name.as_str()))
        {
            legacy.entry(group.into()).or_default().push(id);
        }
    }

    let mut relations = BTreeSet::new();
    for group in explicit.values() {
        add_overload_group(&mut relations, group, &catalog, subsorts, false);
    }
    for group in legacy.values() {
        add_overload_group(&mut relations, group, &catalog, subsorts, true);
    }

    Ok(OverloadOrder {
        catalog,
        order: PartialOrder::new(relations)?,
    })
}

fn add_overload_group(
    relations: &mut BTreeSet<(ProductionId, ProductionId)>,
    group: &[ProductionId],
    catalog: &ProductionCatalog<'_>,
    subsorts: &PartialOrder<Sort>,
    require_lesser_label: bool,
) {
    for &lesser in group {
        // Invariant: `relations` contains `(l, g)` for every pair of `group` already visited, with an earlier `lesser` or an earlier `greater`, that satisfies the label requirement and `production_less_than`; each iteration consumes one entry of `group`, so a group costs O(|group|^2) comparisons.
        for &greater in group {
            let lesser_sentence = catalog.production(lesser);
            let lesser_has_label =
                matches!(lesser_sentence, Sentence::Production { label: Some(_), .. });
            if (!require_lesser_label || lesser_has_label)
                && production_less_than(lesser_sentence, catalog.production(greater), subsorts)
            {
                relations.insert((lesser, greater));
            }
        }
    }
}

impl ResolvedDefinition {
    /// Compute the semantic subsort relation.
    ///
    /// This accessor recomputes on every call; use `DefinitionViews` inside a loop.
    pub fn subsorts(&self, module: ModuleId) -> Result<PartialOrder<Sort>, Cycle<Sort>> {
        compute_subsorts(self.sentences(module), false)
    }

    /// Compute the syntactic subsort relation.
    ///
    /// This accessor recomputes on every call; use `DefinitionViews` inside a loop.
    pub fn syntactic_subsorts(&self, module: ModuleId) -> Result<PartialOrder<Sort>, Cycle<Sort>> {
        compute_subsorts(self.sentences(module), true)
    }

    /// Compute the overload relation from the memoised production catalog.
    pub fn overloads(&self, module: ModuleId) -> Result<OverloadOrder<'_>, Error> {
        let sentences = self.sentences(module);
        let subsorts =
            compute_subsorts(sentences.iter().copied(), false).map_err(Error::CircularSubsort)?;
        compute_overloads_with_catalog(&self.production_catalog(module), &subsorts)
            .map_err(Error::CircularOverload)
    }

    /// Compute the syntax priority relation.
    ///
    /// This accessor recomputes on every call; use `DefinitionViews` inside a loop.
    pub fn priorities(&self, module: ModuleId) -> Result<PartialOrder<String>, Cycle<String>> {
        compute_priorities(self.sentences(module))
    }

    /// Compute syntax associativity relations.
    ///
    /// This accessor recomputes on every call; use `DefinitionViews` inside a loop.
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

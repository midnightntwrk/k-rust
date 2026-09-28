use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    DescriptorApplicationRef, DescriptorBundle, DescriptorPayload, DescriptorProductionOwner,
    DescriptorSortRef, GrammarDescriptor, ItemKind, StableItemId,
};

use crate::{AnalysisError, AnalysisErrorKind};

/// Deterministic open-sort relation computed from a stable descriptor bundle.
///
/// Direct edges remain distinct from their transitive closure. Constructor
/// membership includes the directly declared sort and every transitive parent,
/// and diamonds are deduplicated by stable identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OpenSortAnalysis {
    direct_parents: BTreeMap<StableItemId, Vec<StableItemId>>,
    transitive_parents: BTreeMap<StableItemId, Vec<StableItemId>>,
    member_sorts: BTreeMap<StableItemId, Vec<StableItemId>>,
    constructors_by_sort: BTreeMap<StableItemId, Vec<StableItemId>>,
}

impl OpenSortAnalysis {
    /// Returns direct `subsort -> supersort` edges in canonical order.
    #[must_use]
    pub const fn direct_parents(&self) -> &BTreeMap<StableItemId, Vec<StableItemId>> {
        &self.direct_parents
    }

    /// Returns strict transitive parents for every sort in canonical order.
    #[must_use]
    pub const fn transitive_parents(&self) -> &BTreeMap<StableItemId, Vec<StableItemId>> {
        &self.transitive_parents
    }

    /// Returns every direct or inherited sort containing each constructor.
    #[must_use]
    pub const fn member_sorts(&self) -> &BTreeMap<StableItemId, Vec<StableItemId>> {
        &self.member_sorts
    }

    /// Returns direct and inherited constructors visible through each sort.
    #[must_use]
    pub const fn constructors_by_sort(&self) -> &BTreeMap<StableItemId, Vec<StableItemId>> {
        &self.constructors_by_sort
    }
}

/// Computes the target-neutral open-sort relation from stable descriptors.
///
/// # Errors
///
/// Rejects duplicate declaration IDs, absent/wrongly-kinded sort references,
/// and direct or indirect subsort cycles. Rules do not participate in this
/// deliberately small analysis.
pub fn analyze_open_sorts(bundle: &DescriptorBundle) -> Result<OpenSortAnalysis, AnalysisError> {
    let kinds = descriptor_kinds(bundle)?;
    let OpenSortEdges {
        mut direct_parents,
        mut constructors,
    } = open_sort_edges(bundle, &kinds)?;

    for parents in direct_parents.values_mut() {
        parents.sort();
        parents.dedup();
    }

    let mut transitive_parents: BTreeMap<StableItemId, Vec<StableItemId>> = BTreeMap::new();
    for sort in direct_parents.keys() {
        let mut visiting = Vec::new();
        let mut closure = BTreeSet::new();
        visit_parents(sort, sort, &direct_parents, &mut visiting, &mut closure)?;
        transitive_parents.insert(sort.clone(), closure.into_iter().collect());
    }

    constructors.sort();
    let mut member_sorts = BTreeMap::new();
    let mut constructors_by_sort = direct_parents
        .keys()
        .cloned()
        .map(|sort| (sort, Vec::new()))
        .collect::<BTreeMap<_, _>>();
    for (constructor, direct_sort) in constructors {
        let mut memberships = BTreeSet::from([direct_sort.clone()]);
        if let Some(parents) = transitive_parents.get(&direct_sort) {
            memberships.extend(parents.iter().cloned());
        }
        let memberships = memberships.into_iter().collect::<Vec<_>>();
        for sort in &memberships {
            let Some(members) = constructors_by_sort.get_mut(sort) else {
                return Err(AnalysisError::new(
                    AnalysisErrorKind::UnresolvedReference,
                    format!("member sort `{}` has no declaration", display_item(sort)),
                ));
            };
            members.push(constructor.clone());
        }
        member_sorts.insert(constructor, memberships);
    }
    for members in constructors_by_sort.values_mut() {
        members.sort();
        members.dedup();
    }

    Ok(OpenSortAnalysis {
        direct_parents,
        transitive_parents,
        member_sorts,
        constructors_by_sort,
    })
}

/// Maps every descriptor identity to its item kind, rejecting duplicates.
fn descriptor_kinds(
    bundle: &DescriptorBundle,
) -> Result<BTreeMap<StableItemId, ItemKind>, AnalysisError> {
    let mut kinds = BTreeMap::new();
    for descriptor in &bundle.descriptors {
        if kinds
            .insert(descriptor.id.clone(), descriptor.id.item_kind())
            .is_some()
        {
            return Err(AnalysisError::new(
                AnalysisErrorKind::DuplicateItemId,
                format!("duplicate stable item `{}`", display_item(&descriptor.id)),
            ));
        }
    }
    Ok(kinds)
}

/// Direct subsort edges and `(constructor, declared sort)` memberships, before
/// canonical ordering.
struct OpenSortEdges {
    direct_parents: BTreeMap<StableItemId, Vec<StableItemId>>,
    constructors: Vec<(StableItemId, StableItemId)>,
}

fn open_sort_edges(
    bundle: &DescriptorBundle,
    kinds: &BTreeMap<StableItemId, ItemKind>,
) -> Result<OpenSortEdges, AnalysisError> {
    let mut direct_parents: BTreeMap<StableItemId, Vec<StableItemId>> = BTreeMap::new();
    let mut constructors = Vec::new();
    for descriptor in &bundle.descriptors {
        match &descriptor.payload {
            DescriptorPayload::Sort(sort) => {
                require_kind(&descriptor.id, ItemKind::Sort, kinds)?;
                let mut parents = sort.parents.clone();
                parents.sort();
                parents.dedup();
                for parent in &parents {
                    require_kind(parent, ItemKind::Sort, kinds)?;
                }
                direct_parents
                    .entry(descriptor.id.clone())
                    .or_default()
                    .extend(parents);
            }
            DescriptorPayload::Constructor(constructor) => {
                require_kind(&descriptor.id, ItemKind::Constructor, kinds)?;
                if let DescriptorSortRef::Declared(sort) = &constructor.sort {
                    require_kind(sort, ItemKind::Sort, kinds)?;
                    constructors.push((descriptor.id.clone(), sort.clone()));
                }
            }
            DescriptorPayload::StructuredRule(_)
            | DescriptorPayload::FixedConfiguration(_)
            | DescriptorPayload::Cell(_)
            | DescriptorPayload::ConfigurationRule(_)
            | DescriptorPayload::HeadRule(_)
            | DescriptorPayload::ContextAlias(_) => {}
            DescriptorPayload::Grammar(grammar) => match grammar.as_ref() {
                GrammarDescriptor::Production(production) => {
                    if let DescriptorProductionOwner::Constructor { constructor } =
                        &production.owner
                        && let DescriptorApplicationRef::Declared(id) = &constructor.application
                        && let DescriptorSortRef::Declared(sort) = &production.result_sort.sort
                    {
                        constructors.push((id.clone(), sort.clone()));
                    }
                }
                GrammarDescriptor::Subsort {
                    subsort, supersort, ..
                } => {
                    if let (
                        DescriptorSortRef::Declared(subsort),
                        DescriptorSortRef::Declared(supersort),
                    ) = (&subsort.sort, &supersort.sort)
                    {
                        direct_parents
                            .entry(subsort.clone())
                            .or_default()
                            .push(supersort.clone());
                    }
                }
                GrammarDescriptor::Precedence { .. } | GrammarDescriptor::Associativity { .. } => {}
            },
        }
    }
    Ok(OpenSortEdges {
        direct_parents,
        constructors,
    })
}

fn visit_parents(
    root: &StableItemId,
    current: &StableItemId,
    graph: &BTreeMap<StableItemId, Vec<StableItemId>>,
    visiting: &mut Vec<StableItemId>,
    closure: &mut BTreeSet<StableItemId>,
) -> Result<(), AnalysisError> {
    if let Some(position) = visiting.iter().position(|item| item == current) {
        let mut cycle = visiting[position..]
            .iter()
            .map(display_item)
            .collect::<Vec<_>>();
        cycle.push(display_item(current));
        return Err(AnalysisError::new(
            AnalysisErrorKind::SortCycle,
            format!("open-sort relation contains cycle: {}", cycle.join(" -> ")),
        ));
    }
    visiting.push(current.clone());
    for parent in graph
        .get(current)
        .expect("resolved sort has a direct-parent entry")
    {
        if parent == root {
            let mut cycle = visiting.iter().map(display_item).collect::<Vec<_>>();
            cycle.push(display_item(root));
            return Err(AnalysisError::new(
                AnalysisErrorKind::SortCycle,
                format!("open-sort relation contains cycle: {}", cycle.join(" -> ")),
            ));
        }
        closure.insert(parent.clone());
        visit_parents(root, parent, graph, visiting, closure)?;
    }
    visiting.pop();
    Ok(())
}

fn require_kind(
    id: &StableItemId,
    expected: ItemKind,
    kinds: &BTreeMap<StableItemId, ItemKind>,
) -> Result<(), AnalysisError> {
    let Some(actual) = kinds.get(id) else {
        return Err(AnalysisError::new(
            AnalysisErrorKind::UnresolvedReference,
            format!("stable reference `{}` has no declaration", display_item(id)),
        ));
    };
    if *actual != expected {
        return Err(AnalysisError::new(
            AnalysisErrorKind::ReferenceKindMismatch,
            format!(
                "stable reference `{}` has kind {actual}, but {expected} is required",
                display_item(id)
            ),
        ));
    }
    Ok(())
}

fn display_item(id: &StableItemId) -> String {
    id.to_string()
}

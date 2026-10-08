use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    Descriptor, DescriptorApplicationRef, DescriptorDeclaration, DescriptorIndex,
    DescriptorPayload, DescriptorProductionItem, DescriptorProductionOwner, DescriptorSortRef,
    GeneratedProductionKind, GrammarDescriptor, ProductionFieldId, StableItemId,
    generated_production_id,
};
use krs_ir_levels::{SemanticSortRef, SemanticTerm};

use super::error::DescriptorLoweringError;

#[derive(Clone, Debug)]
pub(super) struct ProductionSignature {
    pub(super) result_sort: SemanticSortRef,
    pub(super) fields: Vec<(ProductionFieldId, SemanticSortRef)>,
}

pub(super) fn semantic_sort_ref(sort: &DescriptorSortRef) -> SemanticSortRef {
    match sort {
        DescriptorSortRef::Declared(id) => SemanticSortRef::Declared(id.clone()),
        DescriptorSortRef::Builtin(sort) => SemanticSortRef::Builtin(*sort),
        DescriptorSortRef::Cell(id) => SemanticSortRef::Cell(id.clone()),
    }
}

pub(super) fn build_semantic_sort_parents(
    descriptors: &[&Descriptor],
) -> BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>> {
    let mut parents = BTreeMap::<SemanticSortRef, BTreeSet<SemanticSortRef>>::new();
    for descriptor in descriptors {
        match descriptor.payload() {
            DescriptorPayload::Sort(sort) => {
                parents
                    .entry(SemanticSortRef::Declared(descriptor.id().clone()))
                    .or_default()
                    .extend(sort.parents.iter().cloned().map(SemanticSortRef::Declared));
            }
            DescriptorPayload::Grammar(grammar) => {
                if let GrammarDescriptor::Subsort {
                    subsort, supersort, ..
                } = grammar.as_ref()
                {
                    parents
                        .entry(semantic_sort_ref(&subsort.sort))
                        .or_default()
                        .insert(semantic_sort_ref(&supersort.sort));
                }
            }
            DescriptorPayload::Constructor(_)
            | DescriptorPayload::StructuredRule(_)
            | DescriptorPayload::FixedConfiguration(_)
            | DescriptorPayload::Cell(_)
            | DescriptorPayload::ConfigurationRule(_)
            | DescriptorPayload::HeadRule(_)
            | DescriptorPayload::ContextAlias(_) => {}
        }
    }
    // K makes every generated cell sort a subsort of KItem, so a whole-group
    // binder (`FrameCell`, KF-016) may stand wherever a KItem is expected.
    let k_item = descriptors
        .iter()
        .map(|descriptor| descriptor.id())
        .find(|id| {
            id.item_kind() == krs_ir::ItemKind::Sort
                && id.item_name() == "KItem"
                && id.package().k_namespace() == "KRS-FRAMEWORK"
                && id.package().cargo_name() == "krs"
                && id.package().cargo_source() == "framework"
        });
    if let Some(k_item) = k_item {
        for descriptor in descriptors {
            if matches!(descriptor.payload(), DescriptorPayload::Cell(_)) {
                parents
                    .entry(SemanticSortRef::Cell(descriptor.id().clone()))
                    .or_default()
                    .insert(SemanticSortRef::Declared(k_item.clone()));
            }
        }
    }
    parents
}

pub(super) fn semantic_is_subsort(
    candidate: &SemanticSortRef,
    expected: &SemanticSortRef,
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> bool {
    if candidate == expected {
        return true;
    }
    let mut pending = vec![candidate.clone()];
    let mut visited = BTreeSet::new();
    while let Some(sort) = pending.pop() {
        if !visited.insert(sort.clone()) {
            continue;
        }
        for parent in parents.get(&sort).into_iter().flatten() {
            if parent == expected {
                return true;
            }
            pending.push(parent.clone());
        }
    }
    false
}

pub(super) fn build_production_catalog(
    descriptors: &[&Descriptor],
) -> Result<BTreeMap<StableItemId, ProductionSignature>, DescriptorLoweringError> {
    let mut catalog = BTreeMap::new();
    for descriptor in descriptors {
        let DescriptorPayload::Grammar(grammar) = descriptor.payload() else {
            continue;
        };
        let GrammarDescriptor::Production(production) = grammar.as_ref() else {
            continue;
        };
        let id = match &production.owner {
            DescriptorProductionOwner::Constructor { constructor } => {
                let DescriptorApplicationRef::Declared(id) = &constructor.application else {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "constructor production owner",
                        detail: "constructor grammar cannot be owned by a builtin operation"
                            .to_owned(),
                    });
                };
                id.clone()
            }
            DescriptorProductionOwner::TokenSort { .. } => {
                generated_production_id(descriptor.id(), GeneratedProductionKind::Token).map_err(
                    |error| DescriptorLoweringError::InvalidGeneratedIdentity(error.to_string()),
                )?
            }
            DescriptorProductionOwner::BracketSort { .. } => {
                generated_production_id(descriptor.id(), GeneratedProductionKind::Bracket).map_err(
                    |error| DescriptorLoweringError::InvalidGeneratedIdentity(error.to_string()),
                )?
            }
        };
        let fields = production
            .items
            .iter()
            .filter_map(|item| match item {
                DescriptorProductionItem::NonTerminal { field, sort, .. } => {
                    Some((field.clone(), semantic_sort_ref(&sort.sort)))
                }
                DescriptorProductionItem::Terminal { .. }
                | DescriptorProductionItem::RegexTerminal { .. } => None,
            })
            .collect();
        if catalog
            .insert(
                id.clone(),
                ProductionSignature {
                    result_sort: semantic_sort_ref(&production.result_sort.sort),
                    fields,
                },
            )
            .is_some()
        {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "production catalog",
                detail: format!("more than one grammar descriptor owns {id}"),
            });
        }
    }
    if let Some(descriptor) = descriptors.iter().find(|descriptor| {
        matches!(descriptor.payload(), DescriptorPayload::Constructor(_))
            && !catalog.contains_key(descriptor.id())
    }) {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "constructor",
            detail: format!("no grammar descriptor owns constructor {}", descriptor.id()),
        });
    }
    Ok(catalog)
}

pub(super) struct DeclarationCatalog<'a> {
    pub(super) descriptors: &'a DescriptorIndex<'a>,
    pub(super) metadata: &'a BTreeMap<StableItemId, DescriptorDeclaration>,
}

pub(super) fn common_sequence_item_sort(
    descriptor: &Descriptor,
    items: &[SemanticTerm],
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<SemanticSortRef, DescriptorLoweringError> {
    if items.is_empty() {
        return Ok(SemanticSortRef::k_sequence());
    }
    let mut common = semantic_sort_closure(items[0].sort(), parents);
    for item in &items[1..] {
        let candidates = semantic_sort_closure(item.sort(), parents);
        common.retain(|candidate| candidates.contains(candidate));
    }
    let most_specific = common
        .iter()
        .filter(|candidate| {
            !common
                .iter()
                .any(|other| other != *candidate && semantic_is_subsort(other, candidate, parents))
        })
        .cloned()
        .collect::<Vec<_>>();
    let [item_sort] = most_specific.as_slice() else {
        return Err(DescriptorLoweringError::InvalidTerm {
            id: Box::new(descriptor.id().clone()),
            detail: "K sequence items do not have one most-specific common sort".into(),
        });
    };
    Ok(item_sort.clone())
}

pub(super) fn semantic_sort_closure(
    start: &SemanticSortRef,
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> BTreeSet<SemanticSortRef> {
    let mut pending = vec![start.clone()];
    let mut closure = BTreeSet::new();
    while let Some(sort) = pending.pop() {
        if !closure.insert(sort.clone()) {
            continue;
        }
        if let Some(direct) = parents.get(&sort) {
            pending.extend(direct.iter().cloned());
        }
    }
    closure
}

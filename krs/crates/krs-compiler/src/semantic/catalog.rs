use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    Descriptor, DescriptorDeclaration, DescriptorIndex, DescriptorPayload, DescriptorProduction,
    DescriptorProductionItem, DescriptorSortRef, GrammarDescriptor, ProductionFieldId,
    StableItemId,
};
use krs_ir_levels::{SemanticSortRef, SemanticTerm};

use super::error::DescriptorLoweringError;

#[derive(Clone, Debug)]
pub(super) struct ProductionSignature {
    pub(super) result_sort: SemanticSortRef,
    pub(super) fields: Vec<(ProductionFieldId, SemanticSortRef)>,
    /// Whether this is a `#[k::token]` production, whose result sort is a token sort.
    pub(super) token: bool,
    /// Sort parameters of a parametric production, in declaration order
    /// (KF-027); empty for every other production.
    pub(super) parameters: Vec<krs_ir_levels::SortParameterId>,
    /// Whether the production is a function, whose applications denote
    /// equation results rather than values of their own.
    pub(super) function: bool,
}

pub(super) fn semantic_sort_ref(sort: &DescriptorSortRef) -> SemanticSortRef {
    match sort {
        DescriptorSortRef::Declared(id) => SemanticSortRef::Declared(id.clone()),
        DescriptorSortRef::Builtin(sort) => SemanticSortRef::Builtin(*sort),
        DescriptorSortRef::Cell(id) => SemanticSortRef::Cell(id.clone()),
        DescriptorSortRef::Parameter(name) => {
            SemanticSortRef::Parameter(krs_ir_levels::SortParameterId::new(name.clone()))
        }
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
        let productions: Vec<&DescriptorProduction> = match grammar.as_ref() {
            GrammarDescriptor::Production(production) => vec![production],
            GrammarDescriptor::Tokens { productions } => productions.iter().collect(),
            _ => continue,
        };
        for production in productions {
            let id = super::grammar::production_owner_id(descriptor, production)?;
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
                        token: matches!(
                            production.owner,
                            krs_ir::DescriptorProductionOwner::TokenSort { .. }
                        ),
                        parameters: production
                            .parameters
                            .iter()
                            .map(|parameter| match &parameter.sort {
                                DescriptorSortRef::Parameter(name) => {
                                    krs_ir_levels::SortParameterId::new(name.clone())
                                }
                                other => krs_ir_levels::SortParameterId::new(format!("{other:?}")),
                            })
                            .collect(),
                        function: production.attributes.iter().any(|attribute| {
                            matches!(
                                attribute,
                                krs_ir::DescriptorProductionAttribute::Function { .. }
                            )
                        }),
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

/// The item sort of a `[..]` sequence: its items' one most-specific common sort.
///
/// In a rule result (`splice`), an item of sort `K` (`io::write`, `io::putc`, `io::log`)
/// splices into the sequence as K's `~>` does: the sequence's items then have sort `K`, and
/// every other item injects into `KItem`. A pattern keeps the single common sort.
pub(super) fn common_sequence_item_sort(
    descriptor: &Descriptor,
    items: &[SemanticTerm],
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    splice: bool,
) -> Result<SemanticSortRef, DescriptorLoweringError> {
    if items.is_empty() {
        return Ok(SemanticSortRef::k_sequence());
    }
    let k_item = items
        .iter()
        .any(|item| *item.sort() == SemanticSortRef::k_sequence());
    if splice && k_item {
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
            detail: if k_item {
                "K sequence items do not have one most-specific common sort; a `K` item splices \
                 into a sequence only in a rule result"
                    .into()
            } else {
                "K sequence items do not have one most-specific common sort".into()
            },
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

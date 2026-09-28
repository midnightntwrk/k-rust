use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    Descriptor, DescriptorApplicationRef, DescriptorDeclaration, DescriptorPayload,
    DescriptorProductionItem, DescriptorProductionOwner, DescriptorSortRef,
    GeneratedProductionKind, GrammarDescriptor, ProductionFieldId, SemanticSortRef, SemanticTerm,
    StableItemId, generated_production_id,
};

use super::error::DescriptorLoweringError;

#[derive(Clone, Debug)]
pub(super) struct ProductionSignature {
    pub(super) result_sort: SemanticSortRef,
    pub(super) fields: Vec<(ProductionFieldId, SemanticSortRef)>,
    pub(super) grammar_owned: bool,
}

pub(super) fn semantic_sort_ref(sort: &DescriptorSortRef) -> SemanticSortRef {
    match sort {
        DescriptorSortRef::Declared(id) => SemanticSortRef::Declared(id.clone()),
        DescriptorSortRef::Builtin(sort) => SemanticSortRef::Builtin(*sort),
    }
}

pub(super) fn build_semantic_sort_parents(
    descriptors: &[&Descriptor],
) -> BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>> {
    let mut parents = BTreeMap::<SemanticSortRef, BTreeSet<SemanticSortRef>>::new();
    for descriptor in descriptors {
        match &descriptor.payload {
            DescriptorPayload::Sort(sort) => {
                parents
                    .entry(SemanticSortRef::Declared(descriptor.id.clone()))
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
        let DescriptorPayload::Grammar(grammar) = &descriptor.payload else {
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
                generated_production_id(&descriptor.id, GeneratedProductionKind::Token).map_err(
                    |error| DescriptorLoweringError::InvalidGeneratedIdentity(error.to_string()),
                )?
            }
            DescriptorProductionOwner::BracketSort { .. } => {
                generated_production_id(&descriptor.id, GeneratedProductionKind::Bracket).map_err(
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
                    grammar_owned: true,
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
    for descriptor in descriptors {
        let DescriptorPayload::Constructor(constructor) = &descriptor.payload else {
            continue;
        };
        if catalog.contains_key(&descriptor.id) {
            continue;
        }
        let fields = constructor_field_order(&descriptor.id, constructor)?
            .into_iter()
            .map(|name| {
                let field = constructor
                    .fields
                    .iter()
                    .find(|field| field.name == name)
                    .expect("field order is validated against declarations");
                let sort = field.sort.clone().ok_or_else(|| {
                    DescriptorLoweringError::UnsupportedShape {
                        node: "constructor field",
                        detail: format!("constructor {} field {name:?} has no sort", descriptor.id),
                    }
                })?;
                Ok((ProductionFieldId::new(name)?, semantic_sort_ref(&sort)))
            })
            .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
        catalog.insert(
            descriptor.id.clone(),
            ProductionSignature {
                result_sort: semantic_sort_ref(&constructor.sort),
                fields,
                grammar_owned: false,
            },
        );
    }
    Ok(catalog)
}

pub(super) struct DeclarationCatalog<'a> {
    pub(super) descriptors: &'a BTreeMap<StableItemId, &'a Descriptor>,
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
            id: Box::new(descriptor.id.clone()),
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

fn constructor_field_order(
    production: &StableItemId,
    constructor: &krs_ir::ConstructorDescriptor,
) -> Result<Vec<String>, DescriptorLoweringError> {
    if constructor.fields.is_empty() {
        return Ok(Vec::new());
    }
    let source = constructor
        .syntax
        .as_deref()
        .unwrap_or_else(|| production.item_name());
    let mut names = Vec::new();
    let mut index = 0_usize;
    while index < source.len() {
        let Some(open) = source[index..].find('{') else {
            break;
        };
        let open = index + open;
        let remainder = &source[open + 1..];
        let Some(close) = remainder.find('}') else {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "constructor syntax",
                detail: format!("constructor {production} has an unclosed placeholder"),
            });
        };
        names.push(remainder[..close].to_owned());
        index = open + close + 2;
    }
    if names.len() != constructor.fields.len()
        || names.iter().collect::<BTreeSet<_>>().len() != names.len()
        || names
            .iter()
            .any(|name| !constructor.fields.iter().any(|field| &field.name == name))
    {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "constructor syntax",
            detail: format!("constructor {production} has inconsistent field placeholders"),
        });
    }
    Ok(names)
}

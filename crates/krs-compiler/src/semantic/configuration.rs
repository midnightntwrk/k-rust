use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    CellAttribute, CellCollectionType, CellMultiplicity, ConfigurationRoot, Descriptor,
    DescriptorCellDeclaration, DescriptorFixedConfiguration, DescriptorInitializerCell,
    DescriptorInitializerStateTerm, DescriptorPayload, DescriptorTerm, FixedCell,
    FixedConfiguration, FixedConfigurationVariable, FixedInitializerCell, ItemKind, MapOperation,
    ProtocolCellContent, ProtocolInitializerCellContent, ProtocolInitializerStateTerm,
    ProtocolMapBody, ProvenanceKey, SemanticConfiguration, SemanticId, SemanticSortRef,
    SemanticTerm, StableItemId,
};

use super::catalog::{ProductionSignature, common_sequence_item_sort, semantic_sort_ref};
use super::error::DescriptorLoweringError;
use super::infer::{StructuredTermBuilder, initial_binding_constraints};
use super::origin::{generated_semantic_id, semantic_cell_id, semantic_origin};
use super::references::{require_cell_field, require_descriptor};

pub(super) fn lower_fixed_configuration_descriptor(
    descriptor: &Descriptor,
    configuration: &DescriptorFixedConfiguration,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticConfiguration, DescriptorLoweringError> {
    let configuration_id = generated_semantic_id("configuration", &descriptor.id, None)?;
    let root = match &configuration.root {
        krs_ir::DescriptorConfigurationRoot::GeneratedTop => ConfigurationRoot::GeneratedTop,
        krs_ir::DescriptorConfigurationRoot::Named { key, name } => ConfigurationRoot::named(
            semantic_origin(descriptor, key.clone(), "configuration-root")?,
            name.clone(),
        )?,
    };
    let mut visiting = BTreeSet::new();
    let cells = lower_cell_declaration(
        descriptor,
        &configuration.declaration,
        declarations,
        &mut visiting,
    )?;

    let mut binding_sorts = BTreeMap::new();
    let mut variables = Vec::with_capacity(configuration.initializer.variables.len());
    for variable in &configuration.initializer.variables {
        let id = SemanticId::new(variable.binding.clone())?;
        let sort = semantic_sort_ref(&variable.sort.sort);
        binding_sorts.insert(variable.binding.clone(), sort.clone());
        variables.push(FixedConfigurationVariable::new(
            semantic_origin(
                descriptor,
                variable.binding_key.clone(),
                "configuration-variable",
            )?,
            id,
            variable.external_name.clone(),
            sort,
            variable.main_key.is_some(),
        )?);
    }
    let initializer = configuration
        .initializer
        .cells
        .iter()
        .map(|cell| {
            lower_initializer_cell(
                descriptor,
                cell,
                declarations,
                sort_parents,
                catalog,
                &binding_sorts,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let initializer_id = SemanticId::new(format!("{}.init", configuration_id.as_str()))?;
    Ok(FixedConfiguration::new(
        semantic_origin(
            descriptor,
            configuration.declaration.key.clone(),
            "fixed-configuration",
        )?,
        configuration_id,
        root,
        cells,
        semantic_origin(
            descriptor,
            configuration.initializer.key.clone(),
            "fixed-initializer",
        )?,
        initializer_id,
        variables,
        initializer,
    )?)
}

fn lower_cell_declaration(
    descriptor: &Descriptor,
    declaration: &DescriptorCellDeclaration,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    visiting: &mut BTreeSet<StableItemId>,
) -> Result<Vec<FixedCell<SemanticSortRef, SemanticId>>, DescriptorLoweringError> {
    let mut cells = Vec::with_capacity(declaration.fields.len());
    for field in &declaration.fields {
        let id = semantic_cell_id(&field.reference.cell)?;
        let name = field
            .emitted_name
            .as_ref()
            .map_or_else(|| field.rust_field.clone(), |name| name.value.clone());
        let mut attributes = Vec::with_capacity(3);
        if let Some(color) = &field.color {
            attributes.push(CellAttribute::color(
                semantic_origin(descriptor, color.key.clone(), "cell-color")?,
                color.value.clone(),
            )?);
        }
        if let Some(multiplicity) = &field.multiplicity {
            debug_assert_eq!(multiplicity.value, "*");
            attributes.push(CellAttribute::multiplicity(
                semantic_origin(descriptor, multiplicity.key.clone(), "cell-multiplicity")?,
                CellMultiplicity::Star,
            ));
        }
        if let Some(cell_type) = &field.cell_type {
            let value = match cell_type.value.as_str() {
                "Bag" => CellCollectionType::Bag,
                "List" => CellCollectionType::List,
                "Map" => CellCollectionType::Map,
                "Set" => CellCollectionType::Set,
                _ => unreachable!("protocol validation rejects unsupported cell types"),
            };
            attributes.push(CellAttribute::collection_type(
                semantic_origin(descriptor, cell_type.key.clone(), "cell-type")?,
                value,
            ));
        }
        let origin = semantic_origin(
            descriptor,
            field.reference.key.clone(),
            "fixed-cell-declaration",
        )?;
        let cell = match &field.content {
            ProtocolCellContent::Leaf { sort, .. } => {
                FixedCell::leaf(origin, id, name, attributes, semantic_sort_ref(&sort.sort))?
            }
            ProtocolCellContent::Nested { declaration } => {
                if !visiting.insert(declaration.declaration.clone()) {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "nested cell declaration",
                        detail: format!(
                            "cyclic nominal cell declaration at {}",
                            declaration.declaration
                        ),
                    });
                }
                let nested =
                    require_descriptor(&declaration.declaration, ItemKind::Cell, declarations)?;
                let DescriptorPayload::Cell(nested_declaration) = &nested.payload else {
                    unreachable!("kind-checked descriptor has a cell payload")
                };
                let children =
                    lower_cell_declaration(nested, nested_declaration, declarations, visiting)?;
                visiting.remove(&declaration.declaration);
                FixedCell::nested(origin, id, name, attributes, children)?
            }
        };
        cells.push(cell);
    }
    Ok(cells)
}

fn lower_initializer_cell(
    descriptor: &Descriptor,
    cell: &DescriptorInitializerCell,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<FixedInitializerCell<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let declared = require_cell_field(&cell.field.cell, declarations)?;
    let id = semantic_cell_id(&cell.field.cell)?;
    let origin = semantic_origin(descriptor, cell.key.clone(), "initializer-cell")?;
    match (&cell.content, &declared.content) {
        (
            ProtocolInitializerCellContent::Leaf { value, .. },
            ProtocolCellContent::Leaf { sort, .. },
        ) => Ok(FixedInitializerCell::term(
            origin,
            id,
            lower_initializer_state(
                descriptor,
                value,
                &semantic_sort_ref(&sort.sort),
                &cell.key,
                sort_parents,
                catalog,
                binding_sorts,
            )?,
        )),
        (
            ProtocolInitializerCellContent::Nested { children, .. },
            ProtocolCellContent::Nested { .. },
        ) => {
            let children = children
                .iter()
                .map(|child| {
                    lower_initializer_cell(
                        descriptor,
                        child,
                        declarations,
                        sort_parents,
                        catalog,
                        binding_sorts,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(FixedInitializerCell::children(origin, id, children)?)
        }
        _ => Err(DescriptorLoweringError::ParserReferenceDisagreement {
            id: Box::new(cell.field.cell.owner.clone()),
            detail: "initializer content disagrees with the declared cell family".into(),
        }),
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_initializer_state(
    descriptor: &Descriptor,
    state: &DescriptorInitializerStateTerm,
    declared_sort: &SemanticSortRef,
    fallback_key: &ProvenanceKey,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<SemanticTerm, DescriptorLoweringError> {
    let lower_term = |term: &DescriptorTerm, expected_sort: Option<&SemanticSortRef>| {
        lower_initializer_term(
            descriptor,
            term,
            expected_sort,
            sort_parents,
            catalog,
            binding_sorts,
        )
    };
    match state {
        ProtocolInitializerStateTerm::Term(term) => lower_term(&term.term, Some(declared_sort)),
        ProtocolInitializerStateTerm::KSequence(sequence) => {
            if *declared_sort != SemanticSortRef::k_sequence() {
                return Err(DescriptorLoweringError::InvalidTerm {
                    id: Box::new(descriptor.id.clone()),
                    detail: "K sequence initializes a non-KSequence cell".into(),
                });
            }
            let items = sequence
                .items
                .iter()
                .map(|item| lower_term(&item.value.term, None))
                .collect::<Result<Vec<_>, _>>()?;
            let item_sort = common_sequence_item_sort(descriptor, &items, sort_parents)?;
            let key = sequence
                .payload_key
                .as_ref()
                .or(sequence.dot_k_key.as_ref())
                .unwrap_or(fallback_key);
            Ok(SemanticTerm::k_sequence(
                semantic_origin(descriptor, key.clone(), "initializer-k-sequence")?,
                item_sort,
                items,
            ))
        }
        ProtocolInitializerStateTerm::Map(map) => {
            if *declared_sort != SemanticSortRef::map() {
                return Err(DescriptorLoweringError::InvalidTerm {
                    id: Box::new(descriptor.id.clone()),
                    detail: "map initializes a non-Map cell".into(),
                });
            }
            let key = map.payload_key.as_ref().unwrap_or(fallback_key);
            let (operation, arguments) = match &map.body {
                ProtocolMapBody::Empty { .. } => (MapOperation::Empty, Vec::new()),
                ProtocolMapBody::Items { items } => {
                    let mut arguments = Vec::with_capacity(items.len() * 2);
                    for item in items {
                        arguments.push(lower_term(&item.key.term, None)?);
                        arguments.push(lower_term(&item.value.term, None)?);
                    }
                    (MapOperation::Item, arguments)
                }
                ProtocolMapBody::Update {
                    base, key, value, ..
                } => (
                    MapOperation::Update,
                    vec![
                        lower_term(&base.term, Some(&SemanticSortRef::map()))?,
                        lower_term(&key.term, None)?,
                        lower_term(&value.term, None)?,
                    ],
                ),
            };
            Ok(SemanticTerm::map(
                semantic_origin(descriptor, key.clone(), "initializer-map")?,
                operation,
                arguments,
            ))
        }
    }
}

fn lower_initializer_term(
    descriptor: &Descriptor,
    term: &DescriptorTerm,
    expected_sort: Option<&SemanticSortRef>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<SemanticTerm, DescriptorLoweringError> {
    let binding_names = binding_sorts.keys().cloned().collect::<BTreeSet<_>>();
    let mut builder = StructuredTermBuilder {
        descriptor,
        catalog,
        declarations: None,
        k_item_sort: None,
        sort_parents,
        binding_names: &binding_names,
        pattern_key: None,
        binding_sorts: BTreeMap::new(),
        binding_constraints: initial_binding_constraints(binding_sorts),
        wildcard_offset: 0,
        wildcards: Vec::new(),
    };
    builder.infer(term, expected_sort, false)?;
    builder.resolve_binding_sorts()?;
    builder.lower(term, expected_sort, false)
}

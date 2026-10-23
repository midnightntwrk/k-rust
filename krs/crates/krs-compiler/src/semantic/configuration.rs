use std::collections::{BTreeMap, BTreeSet};

use krs_diagnostic::codes;
use krs_ir::{
    BuiltinSort, CellAttribute, CellMultiplicity, CellStream, CellWrapper, ConfigurationRoot,
    Descriptor, DescriptorCellDeclaration, DescriptorCellField, DescriptorFixedConfiguration,
    DescriptorIndex, DescriptorInitializerCell, DescriptorInitializerStateTerm, DescriptorTerm,
    FixedCell, FixedConfiguration, FixedConfigurationVariable, FixedInitializerCell,
    FixedInitializerContent, NodeOrigin, ProtocolCellContent, ProtocolInitializerCellContent,
    ProtocolInitializerStateTerm, ProtocolMapBody, ProvenanceKey, SemanticId, SourceRange,
    StableItemId,
};
use krs_ir_levels::{
    IrTermKind, ListOperands, MapEntry, MapOperands, SemanticConfiguration, SemanticSortRef,
    SemanticTerm,
};

use super::catalog::{ProductionSignature, common_sequence_item_sort, semantic_sort_ref};
use super::collection_types::{CollectionTyping, Root, SortType, Walker};
use super::error::DescriptorLoweringError;
use super::infer::{CollectionUse, StructuredTermBuilder, initial_binding_constraints};
use super::origin::{generated_semantic_id, semantic_cell_id, semantic_origin};
use super::references::require_cell_field;

pub(super) fn lower_fixed_configuration_descriptor(
    descriptor: &Descriptor,
    configuration: &DescriptorFixedConfiguration,
    declarations: &DescriptorIndex<'_>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticConfiguration, DescriptorLoweringError> {
    let configuration_id = generated_semantic_id("configuration", descriptor.id(), None)?;
    let root = match &configuration.root {
        krs_ir::DescriptorConfigurationRoot::GeneratedTop => ConfigurationRoot::GeneratedTop,
        krs_ir::DescriptorConfigurationRoot::Named { key, name } => ConfigurationRoot::named(
            semantic_origin(descriptor, key.clone(), "configuration-root")?,
            name.clone(),
        )?,
    };
    let mut visiting = BTreeSet::new();
    let mut console = ConsoleCells::default();
    let cells = lower_cell_declaration(
        descriptor,
        &configuration.declaration,
        declarations,
        &mut visiting,
        &mut CellScope {
            console: &mut console,
            repeated: None,
        },
    )?;
    check_unambiguous_cell_sorts(&cells)?;

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
    let typing = initializer_typing(
        descriptor,
        configuration,
        declarations,
        catalog,
        sort_parents,
    )?;
    let initializer = configuration
        .initializer
        .cells
        .iter()
        .map(|cell| {
            lower_initializer_cell(
                descriptor,
                cell,
                declarations,
                &InitializerTables {
                    sort_parents,
                    catalog,
                    binding_sorts: &binding_sorts,
                    collections: &typing,
                },
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    console.check_initializers(&initializer)?;
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

/// Rejects a nominal `#[k::cell]` declaration that is the content of more
/// than one nested cell: its generated K cell sort would name two cells
/// (KF-016).
fn check_unambiguous_cell_sorts(
    cells: &[FixedCell<SemanticSortRef, SemanticId>],
) -> Result<(), DescriptorLoweringError> {
    fn walk<'a>(
        cells: &'a [FixedCell<SemanticSortRef, SemanticId>],
        seen: &mut BTreeMap<&'a StableItemId, Vec<&'a FixedCell<SemanticSortRef, SemanticId>>>,
    ) {
        for cell in cells {
            if let Some(declaration) = cell.declaration() {
                seen.entry(declaration).or_default().push(cell);
            }
            if let krs_ir::FixedCellContent::Children { children } = cell.content() {
                walk(children, seen);
            }
        }
    }
    let mut seen = BTreeMap::new();
    walk(cells, &mut seen);
    for (declaration, fields) in seen {
        if let [_, second, ..] = fields.as_slice() {
            return Err(DescriptorLoweringError::AmbiguousCellSort {
                declaration: Box::new(declaration.clone()),
                fields: fields.iter().map(|cell| cell.name().to_owned()).collect(),
                range: second
                    .origin()
                    .origin()
                    .exact_authored_range()
                    .map(Box::new),
            });
        }
    }
    Ok(())
}

/// Stream and exit cells seen so far, for the KF-035 shape checks.
#[derive(Default)]
struct ConsoleCells {
    /// Stream cells by stream: emitted name, identity, and attribute range.
    streams: BTreeMap<CellStream, (String, SemanticId, Option<Box<SourceRange>>)>,
    /// The exit cell's emitted name.
    exit: Option<String>,
}

/// Where a cell declaration sits: the console accumulator and the nearest repeated ancestor.
struct CellScope<'a> {
    console: &'a mut ConsoleCells,
    repeated: Option<String>,
}

fn console_error(reason: String, origin: &NodeOrigin) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidConsoleCell {
        reason,
        range: origin.origin().exact_authored_range().map(Box::new),
    }
}

impl ConsoleCells {
    /// Check a `stream` or `exit` cell where it is declared (KF-035).
    fn check_declaration(
        &mut self,
        attribute: &CellAttribute,
        name: &str,
        id: &SemanticId,
        content: &ProtocolCellContent<
            krs_ir::DescriptorSortReference,
            krs_ir::DescriptorCellDeclarationReference,
        >,
        repeated: Option<&str>,
    ) -> Result<(), DescriptorLoweringError> {
        let (sort, wrapper) = match content {
            ProtocolCellContent::Leaf { sort, wrapper, .. } => {
                (Some(semantic_sort_ref(&sort.sort)), Some(*wrapper))
            }
            ProtocolCellContent::Nested { .. } => (None, None),
        };
        match attribute {
            CellAttribute::Stream { origin, value } => {
                if wrapper == Some(CellWrapper::KCell) {
                    return Err(console_error(
                        format!(
                            "the computation cell `{name}` cannot be a stream cell; declare the stream in a separate List cell"
                        ),
                        origin,
                    ));
                }
                if sort != Some(SemanticSortRef::Builtin(BuiltinSort::List)) {
                    return Err(console_error(
                        format!(
                            "stream cell `{name}` must have sort List: K keeps the stream's buffered content in a List"
                        ),
                        origin,
                    ));
                }
                if let Some((first, ..)) = self.streams.get(value) {
                    return Err(console_error(
                        format!(
                            "cells `{first}` and `{name}` both declare stream = \"{}\"; K connects at most one cell to each stream",
                            value.as_str()
                        ),
                        origin,
                    ));
                }
                self.streams.insert(
                    *value,
                    (
                        name.to_owned(),
                        id.clone(),
                        origin.origin().exact_authored_range().map(Box::new),
                    ),
                );
            }
            CellAttribute::Exit { origin } => {
                if wrapper == Some(CellWrapper::KCell) {
                    return Err(console_error(
                        format!(
                            "the computation cell `{name}` cannot be the exit cell; declare the exit status in a separate Int cell"
                        ),
                        origin,
                    ));
                }
                if sort != Some(SemanticSortRef::Builtin(BuiltinSort::Int)) {
                    return Err(console_error(
                        format!(
                            "exit cell `{name}` must have sort Int: its final value is the process exit status"
                        ),
                        origin,
                    ));
                }
                if let Some(repeated) = repeated {
                    return Err(console_error(
                        format!(
                            "exit cell `{name}` is inside the repeated cell `{repeated}`; K reads the exit status from one cell, so it must be outside every multiplicity cell"
                        ),
                        origin,
                    ));
                }
                if let Some(first) = &self.exit {
                    return Err(console_error(
                        format!(
                            "cells `{first}` and `{name}` are both exit cells; a definition has at most one"
                        ),
                        origin,
                    ));
                }
                self.exit = Some(name.to_owned());
            }
            CellAttribute::Color { .. }
            | CellAttribute::Multiplicity { .. }
            | CellAttribute::CollectionType { .. }
            | CellAttribute::Initial { .. } => {}
        }
        Ok(())
    }

    /// Require every stream cell to start as `list::empty()`: K replaces its content.
    fn check_initializers(
        &self,
        cells: &[FixedInitializerCell<SemanticId, SemanticTerm>],
    ) -> Result<(), DescriptorLoweringError> {
        for cell in cells {
            match cell.content() {
                FixedInitializerContent::Term { term } => {
                    let Some((name, _, range)) =
                        self.streams.values().find(|(_, id, _)| id == cell.cell())
                    else {
                        continue;
                    };
                    if !matches!(term.kind(), IrTermKind::List(operands) if matches!(**operands, ListOperands::Empty))
                    {
                        return Err(DescriptorLoweringError::InvalidConsoleCell {
                            reason: format!(
                                "stream cell `{name}` must be initialized with `list::empty()`: K replaces its content with the stream"
                            ),
                            range: cell
                                .origin()
                                .origin()
                                .exact_authored_range()
                                .map(Box::new)
                                .or_else(|| range.clone()),
                        });
                    }
                }
                FixedInitializerContent::Children { children } => {
                    self.check_initializers(children)?;
                }
            }
        }
        Ok(())
    }
}

/// The K attributes of one cell field, with the collection placement check
/// K needs (KF-023): a `*` cell is its parent's only child.
fn cell_attributes(
    descriptor: &Descriptor,
    declaration: &DescriptorCellDeclaration,
    field: &DescriptorCellField,
    name: &str,
) -> Result<Vec<CellAttribute>, DescriptorLoweringError> {
    let mut attributes = Vec::with_capacity(5);
    if let Some(color) = &field.color {
        attributes.push(CellAttribute::color(
            semantic_origin(descriptor, color.key.clone(), "cell-color")?,
            color.value.clone(),
        )?);
    }
    if let Some(multiplicity) = &field.multiplicity {
        let value = CellMultiplicity::from_k(&multiplicity.value).ok_or_else(|| {
            DescriptorLoweringError::UnsupportedShape {
                node: "cell multiplicity",
                detail: format!("unsupported multiplicity {:?}", multiplicity.value),
            }
        })?;
        if value == CellMultiplicity::Star && declaration.fields.len() != 1 {
            return Err(super::cell_states::collection_error(
                descriptor,
                codes::analysis::COLLECTION_SIBLINGS,
                &multiplicity.key,
                format!(
                    "the collection cell `{name}` shares its parent with other cells; K requires a `multiplicity = \"*\"` cell to be its parent's only child, so give it a `#[k::cell]` struct of its own"
                ),
            ));
        }
        attributes.push(CellAttribute::multiplicity(
            semantic_origin(descriptor, multiplicity.key.clone(), "cell-multiplicity")?,
            value,
        ));
    }
    if let Some(cell_type) = &field.cell_type {
        attributes.push(CellAttribute::collection_type(
            semantic_origin(descriptor, cell_type.key.clone(), "cell-type")?,
            cell_type.value.into(),
        ));
    }
    if let Some(stream) = &field.stream {
        attributes.push(CellAttribute::stream(
            semantic_origin(descriptor, stream.key.clone(), "cell-stream")?,
            stream.value,
        ));
    }
    if let Some(exit) = &field.exit {
        attributes.push(CellAttribute::exit(semantic_origin(
            descriptor,
            exit.key.clone(),
            "cell-exit",
        )?));
    }
    if let Some(initial) = &field.initial {
        attributes.push(CellAttribute::initial(semantic_origin(
            descriptor,
            initial.key.clone(),
            "cell-initial",
        )?));
    }
    Ok(attributes)
}

fn lower_cell_declaration(
    descriptor: &Descriptor,
    declaration: &DescriptorCellDeclaration,
    declarations: &DescriptorIndex<'_>,
    visiting: &mut BTreeSet<StableItemId>,
    scope: &mut CellScope<'_>,
) -> Result<Vec<FixedCell<SemanticSortRef, SemanticId>>, DescriptorLoweringError> {
    let mut cells = Vec::with_capacity(declaration.fields.len());
    for field in &declaration.fields {
        let id = semantic_cell_id(&field.reference.cell)?;
        let name = field
            .emitted_name
            .as_ref()
            .map_or_else(|| field.rust_field.clone(), |name| name.value.clone());
        let attributes = cell_attributes(descriptor, declaration, field, &name)?;
        let repeated = if field.multiplicity.is_some() {
            Some(name.clone())
        } else {
            scope.repeated.clone()
        };
        for attribute in &attributes {
            scope.console.check_declaration(
                attribute,
                &name,
                &id,
                &field.content,
                repeated.as_deref(),
            )?;
        }
        let origin = semantic_origin(
            descriptor,
            field.reference.key.clone(),
            "fixed-cell-declaration",
        )?;
        let cell = match &field.content {
            ProtocolCellContent::Leaf { sort, .. } => {
                // A collection type has the right number of arguments.
                let arguments = SortType::of_cell(field, descriptor)?
                    .map_or_else(Vec::new, |ty| ty.ir_arguments());
                FixedCell::leaf(origin, id, name, attributes, semantic_sort_ref(&sort.sort))?
                    .with_arguments(arguments)
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
                let (nested, nested_declaration) =
                    declarations.cell_descriptor(&declaration.declaration)?;
                let children = lower_cell_declaration(
                    nested,
                    nested_declaration,
                    declarations,
                    visiting,
                    &mut CellScope {
                        console: scope.console,
                        repeated,
                    },
                )?;
                visiting.remove(&declaration.declaration);
                FixedCell::nested(origin, id, name, attributes, children)?
                    .with_declaration(declaration.declaration.clone())
            }
        };
        cells.push(cell.with_field(field.rust_field.clone()));
    }
    Ok(cells)
}

/// What the terms of a configuration's initializer are lowered against.
struct InitializerTables<'a> {
    sort_parents: &'a BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    /// The configuration variables' sorts.
    binding_sorts: &'a BTreeMap<String, SemanticSortRef>,
    /// The element types of the initializer's typed cells.
    collections: &'a CollectionTyping,
}

/// The element types of an initializer: each leaf cell's value at the
/// cell's type. A configuration variable's Rust type is the cell's, which
/// rustc checks, so it fits.
fn initializer_typing(
    descriptor: &Descriptor,
    configuration: &DescriptorFixedConfiguration,
    declarations: &DescriptorIndex<'_>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<CollectionTyping, DescriptorLoweringError> {
    fn roots<'t>(
        walker: &Walker<'_>,
        cells: &'t [DescriptorInitializerCell],
        declarations: &DescriptorIndex<'_>,
        output: &mut Vec<Root<'t>>,
    ) -> Result<(), DescriptorLoweringError> {
        for cell in cells {
            match &cell.content {
                ProtocolInitializerCellContent::Leaf { value, .. } => {
                    let ty =
                        walker.cell_type(require_cell_field(&cell.field.cell, declarations)?)?;
                    match value {
                        ProtocolInitializerStateTerm::Term(term) => output.push(Root::Term {
                            term: &term.term,
                            ty,
                            subject: false,
                        }),
                        ProtocolInitializerStateTerm::Map(map) => {
                            output.push(Root::InitializerMap { map, ty });
                        }
                        ProtocolInitializerStateTerm::KSequence(sequence) => {
                            output.extend(sequence.items.iter().map(|item| Root::Term {
                                term: &item.value.term,
                                ty: None,
                                subject: false,
                            }));
                        }
                    }
                }
                ProtocolInitializerCellContent::Nested { children, .. } => {
                    roots(walker, children, declarations, output)?;
                }
            }
        }
        Ok(())
    }
    let mut walker = Walker::new(descriptor, Some(declarations), catalog, sort_parents);
    walker.checked_binders(
        configuration
            .initializer
            .variables
            .iter()
            .map(|variable| variable.binding.as_str()),
    );
    let mut output = Vec::new();
    roots(
        &walker,
        &configuration.initializer.cells,
        declarations,
        &mut output,
    )?;
    walker.run(&output)
}

fn lower_initializer_cell(
    descriptor: &Descriptor,
    cell: &DescriptorInitializerCell,
    declarations: &DescriptorIndex<'_>,
    tables: &InitializerTables<'_>,
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
                tables,
            )?,
        )),
        (
            ProtocolInitializerCellContent::Nested { children, .. },
            ProtocolCellContent::Nested { .. },
        ) => {
            let children = children
                .iter()
                .map(|child| lower_initializer_cell(descriptor, child, declarations, tables))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(FixedInitializerCell::children(origin, id, children)?)
        }
        _ => Err(DescriptorLoweringError::ParserReferenceDisagreement {
            id: Box::new(cell.field.cell.owner.clone()),
            detail: "initializer content disagrees with the declared cell family".into(),
        }),
    }
}

fn lower_initializer_state(
    descriptor: &Descriptor,
    state: &DescriptorInitializerStateTerm,
    declared_sort: &SemanticSortRef,
    fallback_key: &ProvenanceKey,
    tables: &InitializerTables<'_>,
) -> Result<SemanticTerm, DescriptorLoweringError> {
    let sort_parents = tables.sort_parents;
    let lower_term = |term: &DescriptorTerm, expected_sort: Option<&SemanticSortRef>| {
        lower_initializer_term(descriptor, term, expected_sort, tables)
    };
    // A key or value of a typed map is lowered at its element sort.
    let element = |term: &DescriptorTerm| {
        tables
            .collections
            .element(term)
            .map(|site| site.sort.clone())
    };
    match state {
        ProtocolInitializerStateTerm::Term(term) => lower_term(&term.term, Some(declared_sort)),
        ProtocolInitializerStateTerm::KSequence(sequence) => {
            if *declared_sort != SemanticSortRef::k_sequence() {
                return Err(DescriptorLoweringError::invalid_term(
                    descriptor.id(),
                    "K sequence initializes a non-KSequence cell",
                ));
            }
            let items = sequence
                .items
                .iter()
                .map(|item| lower_term(&item.value.term, None))
                .collect::<Result<Vec<_>, _>>()?;
            let item_sort = common_sequence_item_sort(descriptor, &items, sort_parents, false)?;
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
                return Err(DescriptorLoweringError::invalid_term(
                    descriptor.id(),
                    "map initializes a non-Map cell",
                ));
            }
            let key = map.payload_key.as_ref().unwrap_or(fallback_key);
            let operands = match &map.body {
                ProtocolMapBody::Empty { .. } => MapOperands::Empty,
                ProtocolMapBody::Items { items } => {
                    let mut entries = Vec::with_capacity(items.len());
                    for item in items {
                        entries.push(MapEntry {
                            key: lower_term(&item.key.term, element(&item.key.term).as_ref())?,
                            value: lower_term(
                                &item.value.term,
                                element(&item.value.term).as_ref(),
                            )?,
                        });
                    }
                    MapOperands::items(entries).map_err(|error| {
                        DescriptorLoweringError::invalid_term(descriptor.id(), error.to_string())
                    })?
                }
                ProtocolMapBody::Update {
                    base, key, value, ..
                } => MapOperands::Update {
                    map: lower_term(&base.term, Some(&SemanticSortRef::map()))?,
                    key: lower_term(&key.term, element(&key.term).as_ref())?,
                    value: lower_term(&value.term, element(&value.term).as_ref())?,
                },
            };
            Ok(SemanticTerm::map(
                semantic_origin(descriptor, key.clone(), "initializer-map")?,
                operands,
            ))
        }
    }
}

fn lower_initializer_term(
    descriptor: &Descriptor,
    term: &DescriptorTerm,
    expected_sort: Option<&SemanticSortRef>,
    tables: &InitializerTables<'_>,
) -> Result<SemanticTerm, DescriptorLoweringError> {
    let InitializerTables {
        sort_parents,
        catalog,
        binding_sorts,
        collections,
    } = *tables;
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
        result_wildcards: false,
        locals: super::infer::LocalBinders::default(),
        head_pending: false,
        operators: super::operators::OperatorInference::default(),
        declared_binders: BTreeMap::new(),
        subject_keys: BTreeMap::new(),
        record_updates: super::record_updates::RecordUpdateState::default(),
        collections: CollectionUse::new(collections),
    };
    builder.infer_sentence(|builder| builder.infer(term, expected_sort, false))?;
    builder.resolve_binding_sorts()?;
    builder.lower(term, expected_sort, false)
}

/// The `stream = "stdin"` cells of a configuration declaration, by identity, with their emitted names.
pub(super) fn stdin_cells(
    declaration: &DescriptorCellDeclaration,
    declarations: &DescriptorIndex<'_>,
) -> Result<BTreeMap<SemanticId, String>, DescriptorLoweringError> {
    let mut cells = BTreeMap::new();
    collect_stdin_cells(declaration, declarations, &mut BTreeSet::new(), &mut cells)?;
    Ok(cells)
}

fn collect_stdin_cells(
    declaration: &DescriptorCellDeclaration,
    declarations: &DescriptorIndex<'_>,
    visiting: &mut BTreeSet<StableItemId>,
    cells: &mut BTreeMap<SemanticId, String>,
) -> Result<(), DescriptorLoweringError> {
    for field in &declaration.fields {
        if field
            .stream
            .as_ref()
            .is_some_and(|stream| stream.value == CellStream::Stdin)
        {
            let name = field
                .emitted_name
                .as_ref()
                .map_or_else(|| field.rust_field.clone(), |name| name.value.clone());
            cells.insert(semantic_cell_id(&field.reference.cell)?, name);
        }
        if let ProtocolCellContent::Nested { declaration } = &field.content
            && visiting.insert(declaration.declaration.clone())
        {
            let (_, nested) = declarations.cell_descriptor(&declaration.declaration)?;
            collect_stdin_cells(nested, declarations, visiting, cells)?;
            visiting.remove(&declaration.declaration);
        }
    }
    Ok(())
}

/// Reject a clause over a stdin stream cell in any shape but the read K's stream rules unblock
/// (`crate::console`).
pub(super) fn check_stdin_reads(
    clauses: &[krs_ir::ConfigurationClause<SemanticId, SemanticTerm>],
    stdin: &BTreeMap<SemanticId, String>,
) -> Result<(), DescriptorLoweringError> {
    for (index, clause) in clauses.iter().enumerate() {
        let Some(name) = stdin.get(clause.cell()) else {
            continue;
        };
        if crate::console::stdin_read(clauses, index).is_none() {
            return Err(DescriptorLoweringError::InvalidConsoleCell {
                reason: format!(
                    "a rule over the stdin stream cell `{name}` must consume its front item, as \
                     `{name}: list::concat(list::item(x), rest) => rest` with `x` bound by \
                     `where x: Sort` and `rest` used nowhere else; K's stream rules supply input \
                     only to that read"
                ),
                range: clause
                    .origin()
                    .origin()
                    .exact_authored_range()
                    .map(Box::new),
            });
        }
    }
    Ok(())
}

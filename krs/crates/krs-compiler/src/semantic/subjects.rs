//! The subject of every configuration-typed sentence, judged against the definition's one
//! configuration.
//!
//! A configuration-typed sentence (a configuration rule, a head rule, a context alias, a
//! function context) is lowered against the definition's configuration, and is about its
//! subject: the whole configuration, or one `#[k::cell]` group at its one position.
//! [`krs_ir::subject::scope`] resolves the subject to the cells the sentence may name; this module
//! reads the configuration as the [`CellTree`] that resolution takes, asks it for each sentence,
//! and checks that every cell the sentence names is one of them.
//!
//! The collector resolves a subject and the names a sentence writes against the same tree, so a
//! subject without a scope is a descriptor that disagrees with its configuration. A cell written
//! with its owner (`Group::cell` in a `cells!` term) is a name the collector takes as written: a
//! cell of a group the configuration does not hold, or outside the group the sentence is about,
//! is the author's mistake, refused here.

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};

use krs_ir::cell_kind::{CellView, Content, DescriptorCell};
use krs_ir::subject::{CellTree, SubjectError, SubjectScope, TreeCell, scope};
use krs_ir::{
    Descriptor, DescriptorCellDeclaration, DescriptorCellField, DescriptorCellIdentity,
    DescriptorConfigurationReference, DescriptorIndex, DescriptorPayload, DescriptorSubject,
    ProtocolCellContent, ProtocolHeadRuleExtra, ProvenanceKey, StableItemId,
};

use super::error::DescriptorLoweringError;
use super::origin::key_range;
use super::references::{declared_multiplicity, require_cell_field};

/// The definition's configuration read as a preorder tree, each cell beside the declaration
/// field that declares it.
struct ConfigurationTree<'a> {
    /// The configuration's identity.
    configuration: &'a StableItemId,
    cells: Vec<TreeCell>,
    /// For each cell, the descriptor of its owner and its declared field.
    fields: Vec<(&'a Descriptor, &'a DescriptorCellField)>,
}

impl CellTree for ConfigurationTree<'_> {
    fn cells(&self) -> &[TreeCell] {
        &self.cells
    }
}

impl<'a> ConfigurationTree<'a> {
    /// The tree of `configuration`'s declaration.
    ///
    /// # Errors
    ///
    /// Returns the lookup error of a nested declaration that names no `#[k::cell]` declaration,
    /// or the unsupported-shape error of a cyclic one, as lowering the configuration does.
    fn of(
        configuration: &'a Descriptor,
        declaration: &'a DescriptorCellDeclaration,
        declarations: &DescriptorIndex<'a>,
    ) -> Result<Self, DescriptorLoweringError> {
        let mut tree = Self {
            configuration: configuration.id(),
            cells: Vec::new(),
            fields: Vec::new(),
        };
        tree.push(
            configuration,
            declaration,
            None,
            declarations,
            &mut BTreeSet::new(),
        )?;
        Ok(tree)
    }

    fn push(
        &mut self,
        owner: &'a Descriptor,
        declaration: &'a DescriptorCellDeclaration,
        parent: Option<usize>,
        declarations: &DescriptorIndex<'a>,
        visiting: &mut BTreeSet<&'a StableItemId>,
    ) -> Result<(), DescriptorLoweringError> {
        for field in &declaration.fields {
            let index = self.cells.len();
            let view = DescriptorCell::new(field, declarations);
            let nested = match &field.content {
                ProtocolCellContent::Nested { declaration } => Some(&declaration.declaration),
                ProtocolCellContent::Leaf { .. } => None,
            };
            self.cells.push(TreeCell {
                identity: field.reference.cell.clone(),
                parent,
                group: nested.cloned(),
                multiplicity: declared_multiplicity(field, declarations),
                computation: matches!(view.content(), Content::Computation),
            });
            self.fields.push((owner, field));
            if let Some(group) = nested {
                if !visiting.insert(group) {
                    return Err(DescriptorLoweringError::unsupported_shape(
                        "nested cell declaration",
                        format!("cyclic nominal cell declaration at {group}"),
                    ));
                }
                let (descriptor, nested) = declarations.cell_descriptor(group)?;
                self.push(descriptor, nested, Some(index), declarations, visiting)?;
                visiting.remove(group);
            }
        }
        Ok(())
    }
}

/// One configuration-typed part of a descriptor: the configuration reference it is typed by,
/// and every cell it names with the provenance of the name.
struct TypedPart<'a> {
    configuration: &'a StableItemId,
    subject: Option<&'a DescriptorSubject>,
    /// The type path's provenance, absent for a table clause, which writes no type.
    key: Option<&'a ProvenanceKey>,
    cells: Vec<(&'a DescriptorCellIdentity, Option<&'a ProvenanceKey>)>,
}

impl<'a> TypedPart<'a> {
    fn of_reference(reference: &'a DescriptorConfigurationReference) -> Self {
        Self {
            configuration: &reference.configuration,
            subject: reference.subject.as_ref(),
            key: Some(&reference.key),
            cells: Vec::new(),
        }
    }

    fn with_cells(
        mut self,
        cells: impl IntoIterator<Item = &'a krs_ir::DescriptorCellReference>,
    ) -> Self {
        self.cells
            .extend(cells.into_iter().map(|cell| (&cell.cell, Some(&cell.key))));
        self
    }
}

/// The configuration-typed parts of `descriptor`, each with the cells it names.
fn typed_parts(descriptor: &Descriptor) -> Vec<TypedPart<'_>> {
    fn rule_cells(cells: &krs_ir::DescriptorRuleCells) -> Vec<&krs_ir::DescriptorCellReference> {
        cells.cells.iter().map(|cell| &cell.field).collect()
    }
    match descriptor.payload() {
        DescriptorPayload::ConfigurationRule(rule) => {
            let mut parts = vec![
                TypedPart::of_reference(&rule.subject_configuration)
                    .with_cells(rule_cells(&rule.subject)),
            ];
            if let Some(result_configuration) = &rule.result_configuration {
                parts.push(
                    TypedPart::of_reference(result_configuration)
                        .with_cells(rule.result.as_ref().map(rule_cells).unwrap_or_default()),
                );
            }
            parts
        }
        DescriptorPayload::HeadRule(rule) => {
            let mut cells = Vec::new();
            if let Some(computation) = &rule.computation_cell {
                cells.push((&computation.cell, computation.key.as_ref()));
            }
            for extra in &rule.extras {
                let (ProtocolHeadRuleExtra::HaveMap { cell, .. }
                | ProtocolHeadRuleExtra::UpdateMap { cell, .. }
                | ProtocolHeadRuleExtra::RewriteCell { cell, .. }
                | ProtocolHeadRuleExtra::RewriteState { cell, .. }
                | ProtocolHeadRuleExtra::RewriteList { cell, .. }) = extra;
                cells.push((&cell.cell, Some(&cell.key)));
            }
            vec![TypedPart {
                configuration: &rule.configuration,
                subject: rule.subject.as_ref(),
                key: rule.configuration_key.as_ref(),
                cells,
            }]
        }
        DescriptorPayload::ContextAlias(alias) => {
            vec![
                TypedPart::of_reference(&alias.configuration)
                    .with_cells(rule_cells(&alias.pattern)),
            ]
        }
        DescriptorPayload::StructuredRule(rule) => rule
            .function_context
            .iter()
            .map(|context| {
                TypedPart::of_reference(&context.configuration)
                    .with_cells(rule_cells(&context.cells))
            })
            .collect(),
        DescriptorPayload::Sort(_)
        | DescriptorPayload::Constructor(_)
        | DescriptorPayload::Grammar(_)
        | DescriptorPayload::FixedConfiguration(_)
        | DescriptorPayload::Cell(_)
        | DescriptorPayload::Constant(_) => Vec::new(),
    }
}

/// Checks the subject of every configuration-typed sentence of `descriptors` against the
/// definition's one configuration: the subject has a scope, and every cell the sentence names is
/// in it.
///
/// # Errors
///
/// - [`DescriptorLoweringError::AmbiguousCellSort`] when the subject is a group the configuration
///   holds at several positions: the configuration itself is refused for that group;
/// - [`DescriptorLoweringError::ParserReferenceDisagreement`] when the subject has no scope
///   otherwise (a group the configuration does not hold, or holds below an optional or a
///   collection cell), which the collector refuses before;
/// - [`DescriptorLoweringError::CellOutsideSubject`] for a named cell outside the scope.
pub(super) fn check_subjects(
    descriptors: &[&Descriptor],
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    let mut tree = None;
    // The scope of each subject met so far: most sentences share one.
    let mut scopes = BTreeMap::new();
    for descriptor in descriptors {
        for part in typed_parts(descriptor) {
            let tree = match &tree {
                Some(tree) => tree,
                // A malformed declaration is the configuration's error, whichever sentence
                // reads it first.
                None => tree.insert(
                    configuration_tree(part.configuration, declarations)
                        .map_err(|error| error.within(part.configuration, None))?,
                ),
            };
            if part.configuration != tree.configuration {
                // One configuration is selected, so another identity resolves to none.
                declarations
                    .configuration(part.configuration)
                    .map_err(|error| {
                        DescriptorLoweringError::from(error).within(descriptor.id(), None)
                    })?;
            }
            check_part(descriptor, &part, tree, declarations, &mut scopes)
                .map_err(|error| error.within(descriptor.id(), None))?;
        }
    }
    Ok(())
}

/// The tree of the configuration `id`, which validation of stable references resolved: the
/// definition's only one.
fn configuration_tree<'a>(
    id: &StableItemId,
    declarations: &DescriptorIndex<'a>,
) -> Result<ConfigurationTree<'a>, DescriptorLoweringError> {
    let configuration = declarations.configuration(id)?;
    let Some(owner) = declarations.get(id) else {
        unreachable!("a configuration found by its identity has a descriptor")
    };
    ConfigurationTree::of(owner, &configuration.declaration, declarations)
}

fn check_part<'a>(
    descriptor: &Descriptor,
    part: &TypedPart<'a>,
    tree: &ConfigurationTree<'_>,
    declarations: &DescriptorIndex<'_>,
    scopes: &mut BTreeMap<Option<&'a DescriptorSubject>, SubjectScope>,
) -> Result<(), DescriptorLoweringError> {
    let type_range = || {
        part.key
            .and_then(|key| key_range(descriptor, key))
            .map(Box::new)
    };
    let nameable = match scopes.entry(part.subject) {
        Entry::Occupied(entry) => &entry.into_mut().nameable,
        Entry::Vacant(entry) => {
            let scope = scope(tree, part.subject).map_err(|error| {
                let Some(DescriptorSubject::Group { declaration }) = part.subject else {
                    unreachable!("the whole configuration always has a scope")
                };
                subject_error(declaration, error, tree, type_range())
            })?;
            &entry.insert(scope).nameable
        }
    };
    for (cell, key) in &part.cells {
        // A name its owner does not declare is a descriptor that disagrees with its
        // declarations, which collection resolved the name against; only a declared cell can be
        // outside the subject.
        require_cell_field(cell, declarations)?;
        if !nameable.contains(*cell) {
            return Err(DescriptorLoweringError::CellOutsideSubject {
                item: Box::new(descriptor.id().clone()),
                cell: Box::new((*cell).clone()),
                configuration: Box::new(tree.configuration.clone()),
                group: part
                    .subject
                    .map(|DescriptorSubject::Group { declaration }| Box::new(declaration.clone())),
                range: key
                    .and_then(|key| key_range(descriptor, key))
                    .map(Box::new)
                    .or_else(type_range),
            });
        }
    }
    Ok(())
}

/// The refusal of a group subject without a scope.
fn subject_error(
    group: &StableItemId,
    error: SubjectError,
    tree: &ConfigurationTree<'_>,
    range: Option<Box<krs_ir::SourceRange>>,
) -> DescriptorLoweringError {
    let configuration = tree.configuration.item_name();
    let reason = match error {
        // Two fields hold the group, so its cells have two positions and its K cell sort names
        // two cells: the configuration is the mistake, and the sentence is refused as it is.
        SubjectError::SeveralPositions { positions } => {
            // The fields are named by their K cell names, as the configuration's own refusal
            // names them, so the configuration gets one text whichever check finds it.
            let second = positions.get(1).and_then(|index| tree.fields.get(*index));
            return DescriptorLoweringError::AmbiguousCellSort {
                declaration: Box::new(group.clone()),
                fields: positions
                    .iter()
                    .map(|index| {
                        let field = tree.fields[*index].1;
                        field
                            .emitted_name
                            .as_ref()
                            .map_or_else(|| field.rust_field.clone(), |name| name.value.clone())
                    })
                    .collect(),
                range: second
                    .and_then(|(owner, field)| key_range(owner, &field.reference.key))
                    .map(Box::new),
            };
        }
        SubjectError::NotInConfiguration => format!("no cell of `{configuration}` holds it"),
        SubjectError::BelowOptional { ancestor } => format!(
            "it sits below the optional cell `{}`",
            tree.fields[ancestor].1.rust_field
        ),
        SubjectError::BelowCollection { ancestor } => format!(
            "it sits below the collection cell `{}`",
            tree.fields[ancestor].1.rust_field
        ),
    };
    DescriptorLoweringError::ParserReferenceDisagreement {
        id: Box::new(group.clone()),
        detail: format!(
            "the sentence is about the group `{}`, which has no one fixed position in the configuration `{configuration}`: {reason}",
            group.item_name()
        ),
        range,
    }
}

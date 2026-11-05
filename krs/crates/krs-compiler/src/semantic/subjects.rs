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

use krs_ir::cell_kind::Multiplicity;
use krs_ir::cell_kind::{CellKind, CellView, Content, DescriptorCell, Order};
use krs_ir::subject::{CellTree, SubjectError, SubjectScope, TreeCell, instance_path, scope};
use krs_ir::{
    Descriptor, DescriptorCellDeclaration, DescriptorCellField, DescriptorCellIdentity,
    DescriptorConfigurationReference, DescriptorIndex, DescriptorPayload, DescriptorSubject,
    DescriptorTerm, ProtocolCellContent, ProtocolHeadRuleExtra, ProvenanceKey, StableItemId,
};
use krs_ir_levels::{
    IrCondition, RuleBodyRef, SemanticModule, SemanticRule, SemanticTerm, SemanticTermKind,
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
                key: CellKind::of(&view).instance_key().map(str::to_owned),
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
///   otherwise (a group the configuration does not hold, or holds in an instance of a Set or a
///   List collection), which the collector refuses before;
/// - [`DescriptorLoweringError::CellOutsideSubject`] for a named cell outside the scope;
/// - [`DescriptorLoweringError::GroupInstance`] for a sentence about one instance that writes the
///   instance's Map key ([`check_instance_sentence`]);
/// - [`DescriptorLoweringError::MainCell`] for a main cell inside a Set collection's instance
///   ([`check_main_cell_holders`]).
pub(super) fn check_subjects(
    descriptors: &[&Descriptor],
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    let mut tree = None;
    // The scope of each subject met so far: most sentences share one.
    let mut scopes = BTreeMap::new();
    for descriptor in descriptors {
        let parts = typed_parts(descriptor);
        for part in &parts {
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
            check_part(descriptor, part, tree, declarations, &mut scopes)
                .map_err(|error| error.within(descriptor.id(), None))?;
        }
        if let (Some(tree), Some(part)) = (&tree, parts.first())
            && let Some(scope) = scopes.get(&part.subject)
        {
            check_instance_sentence(descriptor, part, tree, scope)
                .map_err(|error| error.within(descriptor.id(), None))?;
        }
    }
    check_main_cell_holders(descriptors, declarations, tree.as_ref())
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
        SubjectError::BelowCollection {
            ancestor,
            order: Order::Set,
        } => format!(
            "it sits in an instance of the Set collection cell `{}`, whose instances a local step of one does not keep apart",
            tree.fields[ancestor].1.rust_field
        ),
        SubjectError::BelowCollection {
            ancestor,
            order: Order::List,
        } => format!(
            "it sits in an instance of the List collection cell `{}`, where a step of the instance at any position is not supported yet",
            tree.fields[ancestor].1.rust_field
        ),
        SubjectError::BelowCollection {
            order: Order::Map, ..
        } => unreachable!("a Map collection keeps an instance's identity, its key"),
        // A sentence about a group inside a key would be about an instance's identity.
        SubjectError::InKey { holder, key } => {
            return DescriptorLoweringError::GroupInstance {
                code: krs_diagnostic::codes::analysis::MAP_COLLECTION_KEY,
                reason: krs_ir::subject::key_subject_reason(
                    group.item_name(),
                    unraw(&tree.fields[holder].1.rust_field),
                    unraw(&tree.fields[key].1.rust_field),
                ),
                range,
                item: None,
            };
        }
    };
    DescriptorLoweringError::ParserReferenceDisagreement {
        id: Box::new(group.clone()),
        detail: format!(
            "the sentence is about the group `{}`, which has no position a rule about it applies at in the configuration `{configuration}`: {reason}",
            group.item_name()
        ),
        range,
    }
}

/// The index of the cell `identity` in `tree`, in preorder: the first, where a group held twice
/// gives its cells two positions (the configuration is refused for that as it is).
fn cell_index(tree: &ConfigurationTree<'_>, identity: &DescriptorCellIdentity) -> Option<usize> {
    tree.cells
        .iter()
        .position(|cell| cell.identity == *identity)
}

/// The holders whose one instance a sentence about `subject` is a step of: the `?` and `*` cells
/// on its anchor's path, outermost first ([`instance_path`]); empty for the whole configuration
/// and for a group at a fixed position.
fn subject_path(tree: &ConfigurationTree<'_>, subject: Option<&DescriptorSubject>) -> Vec<usize> {
    match scope(tree, subject) {
        Ok(SubjectScope {
            anchor: Some(anchor),
            ..
        }) => instance_path(tree, anchor),
        _ => Vec::new(),
    }
}

/// What a message calls the holder at `index`: `the optional cell `fpu``, `the Map collection
/// cell `hart``.
fn holder_text(tree: &ConfigurationTree<'_>, index: usize) -> String {
    let kind = match tree.cells[index].multiplicity {
        Multiplicity::Many(Order::Map) => "Map collection",
        Multiplicity::Many(Order::Set) => "Set collection",
        Multiplicity::Many(Order::List) => "List collection",
        Multiplicity::Optional => "optional",
        Multiplicity::One => unreachable!("a holder is a `?` or `*` cell"),
    };
    format!("the {kind} cell `{}`", tree.fields[index].1.rust_field)
}

/// How the group a scope is about sits in its instance `instance`: held by the holder itself, or
/// inside one of its instances.
fn group_in_instance(
    tree: &ConfigurationTree<'_>,
    group: &StableItemId,
    scope: &SubjectScope,
    instance: usize,
) -> String {
    let held = if scope.anchor == Some(instance) {
        "is held by"
    } else {
        "sits in an instance of"
    };
    format!(
        "the cell group `{}` {held} {} of configuration `{}`",
        group.item_name(),
        holder_text(tree, instance),
        tree.configuration.item_name()
    )
}

/// The refusal of a form a sentence about one instance states that is not emitted inside an
/// instance yet.
fn not_emitted(
    tree: &ConfigurationTree<'_>,
    group: &StableItemId,
    scope: &SubjectScope,
    instance: usize,
    what: &str,
    range: Option<krs_ir::SourceRange>,
) -> DescriptorLoweringError {
    DescriptorLoweringError::GroupInstance {
        code: krs_diagnostic::codes::analysis::GROUP_SUBJECT_POSITION,
        reason: format!(
            "{}, so a sentence about `{}` is a local step of one instance; {what} inside an instance is not emitted yet",
            group_in_instance(tree, group, scope, instance),
            group.item_name()
        ),
        range: range.map(Box::new),
        item: None,
    }
}

/// Checks a sentence about one instance of its group (its scope has an instance,
/// [`SubjectScope::instance`]): it writes a Map instance's key only as what it matched.
///
/// A Map collection's key, its instance's first child, is the instance's identity, whole, be it a
/// leaf or a group: a local step writes nothing at or inside it except the subject's own binder
/// for it or the same literal (`krs_syntax::cell_entries::keeps_key`, the predicate the collector
/// applies to the authored entries, here over the terms the descriptor holds).
///
/// Every clause of a rule, a context alias and a `#[k::context]` inside an instance is emitted
/// inside the instance's cell on both emission routes, so each matches in the one instance the
/// sentence is about. A function context is refused later ([`check_instance_contexts`]), once its
/// callers are judged.
fn check_instance_sentence(
    descriptor: &Descriptor,
    part: &TypedPart<'_>,
    tree: &ConfigurationTree<'_>,
    scope: &SubjectScope,
) -> Result<(), DescriptorLoweringError> {
    let (Some(_), Some(DescriptorSubject::Group { declaration: group })) =
        (scope.instance, part.subject)
    else {
        return Ok(());
    };
    if !matches!(
        descriptor.payload(),
        DescriptorPayload::ConfigurationRule(_) | DescriptorPayload::HeadRule(_)
    ) {
        return Ok(());
    }
    check_instance_key(descriptor, tree, group, scope)
}

/// The key of the instance a scope is about, where its anchor is a Map collection: the
/// collection cell, the key cell ([`krs_ir::cell_kind::CellKind::instance_key`]) and every cell
/// at or inside the key, the whole of the instance's identity.
fn instance_key<'t>(
    tree: &'t ConfigurationTree<'_>,
    scope: &SubjectScope,
) -> Option<(usize, usize, Vec<&'t DescriptorCellIdentity>)> {
    let anchor = scope.anchor?;
    let key = krs_ir::subject::key_cell(tree, anchor)?;
    let cells = (0..tree.cells.len())
        .filter(|&index| {
            krs_ir::subject::keys_on_path(tree, index)
                .iter()
                .any(|&(holder, _)| holder == anchor)
        })
        .map(|index| &tree.cells[index].identity)
        .collect();
    Some((anchor, key, cells))
}

/// Refuses a rule about one instance of a Map collection that writes a cell at or inside the
/// instance's key other than as its subject matched it ([`check_instance_sentence`]): the
/// predicate the collector applies to the authored entries, over the descriptor's terms. A
/// written key term is kept only as the matched variable or literal
/// ([`krs_ir::subject::keeps_key_term`]), an in-place rewrite only where its sides are those
/// ([`krs_ir::subject::rewrites_keep`]), and a write of any other state (a whole map, a list, an
/// optional or a collection state, the computation's head) is no provable restatement.
fn check_instance_key(
    descriptor: &Descriptor,
    tree: &ConfigurationTree<'_>,
    group: &StableItemId,
    scope: &SubjectScope,
) -> Result<(), DescriptorLoweringError> {
    let Some((anchor, key, cells)) = instance_key(tree, scope) else {
        return Ok(());
    };
    let inside = |cell: &DescriptorCellIdentity| cells.contains(&cell);
    let refused = match descriptor.payload() {
        DescriptorPayload::ConfigurationRule(rule) => rule_key_write(rule, &inside),
        DescriptorPayload::HeadRule(rule) => head_rule_key_write(rule, &inside),
        _ => None,
    };
    let Some((cell, at)) = refused else {
        return Ok(());
    };
    Err(DescriptorLoweringError::GroupInstance {
        code: krs_diagnostic::codes::analysis::MAP_COLLECTION_KEY,
        reason: krs_ir::subject::key_write_reason(
            group.item_name(),
            unraw(&tree.fields[anchor].1.rust_field),
            unraw(&tree.fields[key].1.rust_field),
            unraw(&cell.field),
        ),
        range: key_range(descriptor, at).map(Box::new),
        item: None,
    })
}

/// The first write of a configuration rule at or inside a key (`inside` says which cells are)
/// that does not keep what the subject matched: an in-place rewrite in the subject, or a result
/// cell; its cell and where it is.
fn rule_key_write<'r>(
    rule: &'r krs_ir::DescriptorConfigurationRule,
    inside: &dyn Fn(&DescriptorCellIdentity) -> bool,
) -> Option<(&'r DescriptorCellIdentity, &'r ProvenanceKey)> {
    fn term(state: &krs_ir::ProtocolRuleStateTerm<DescriptorTerm>) -> Option<&DescriptorTerm> {
        match state {
            krs_ir::ProtocolRuleStateTerm::Term(term) => Some(term),
            _ => None,
        }
    }
    let rewritten = rule
        .subject
        .cells
        .iter()
        .filter(|cell| inside(&cell.field.cell))
        .find(|cell| {
            !cell
                .value
                .terms()
                .into_iter()
                .all(krs_ir::subject::rewrites_keep)
        });
    let written = || {
        rule.result
            .iter()
            .flat_map(|result| &result.cells)
            .filter(|cell| inside(&cell.field.cell))
            .find(|written| {
                let matched = rule
                    .subject
                    .cells
                    .iter()
                    .find(|cell| cell.field.cell == written.field.cell)
                    .and_then(|cell| term(&cell.value));
                !term(&written.value)
                    .is_some_and(|value| krs_ir::subject::keeps_key_term(value, matched))
            })
    };
    rewritten
        .or_else(written)
        .map(|cell| (&cell.field.cell, &cell.field.key))
}

/// The first write of a head rule at or inside a key (`inside` says which cells are) that does
/// not keep what the subject matched: the computation's head, a map update, a cell rewritten to
/// another term, a rewritten optional or collection state, or a rewritten list; its cell and
/// where it is. A read (a map's entries, a cell the result leaves out) keeps it.
fn head_rule_key_write<'r>(
    rule: &'r krs_ir::DescriptorHeadRule,
    inside: &dyn Fn(&DescriptorCellIdentity) -> bool,
) -> Option<(&'r DescriptorCellIdentity, &'r ProvenanceKey)> {
    if let (Some(computation), Some(_)) = (&rule.computation_cell, &rule.head)
        && inside(&computation.cell)
    {
        return Some((
            &computation.cell,
            computation.key.as_ref().unwrap_or(&rule.pattern_key),
        ));
    }
    rule.extras.iter().find_map(|extra| {
        let (cell, kept, at) = match extra {
            ProtocolHeadRuleExtra::HaveMap { cell, .. } => (cell, true, &cell.key),
            ProtocolHeadRuleExtra::UpdateMap { cell, .. } => (cell, false, &cell.key),
            ProtocolHeadRuleExtra::RewriteCell {
                cell,
                before,
                after,
                result_key,
            } => (
                cell,
                after
                    .as_ref()
                    .is_none_or(|after| krs_ir::subject::keeps_key_term(after, Some(before))),
                result_key.as_ref().unwrap_or(&cell.key),
            ),
            ProtocolHeadRuleExtra::RewriteState {
                cell,
                after,
                result_key,
                ..
            } => (
                cell,
                after.is_none(),
                result_key.as_ref().unwrap_or(&cell.key),
            ),
            ProtocolHeadRuleExtra::RewriteList {
                cell,
                after,
                result_key,
                ..
            } => (
                cell,
                after.is_none(),
                result_key.as_ref().unwrap_or(&cell.key),
            ),
        };
        (!kept && inside(&cell.cell)).then_some((&cell.cell, at))
    })
}

/// A field's name without its raw-identifier prefix.
fn unraw(name: &str) -> &str {
    name.strip_prefix("r#").unwrap_or(name)
}

/// Refuses a main cell that is a Map instance's key or lies inside one, and a main cell inside
/// an instance of a Set collection.
///
/// The main cell is where a sentence that names no cell runs (a term rule, a context, a strict
/// production's heating), so each such sentence is a local step of the instance that holds the
/// computation. A Set identifies an instance by its whole content: a step that makes the
/// instance equal to another merges the two, removing an instance the step never touched, so the
/// step is no local step of its instance. The configuration's own refusals of its main cell
/// ([`super::configuration`]) are told where it has none.
fn check_main_cell_holders(
    descriptors: &[&Descriptor],
    declarations: &DescriptorIndex<'_>,
    tree: Option<&ConfigurationTree<'_>>,
) -> Result<(), DescriptorLoweringError> {
    let Some((descriptor, configuration)) =
        descriptors
            .iter()
            .find_map(|descriptor| match descriptor.payload() {
                DescriptorPayload::FixedConfiguration(configuration) => {
                    Some((descriptor, configuration))
                }
                _ => None,
            })
    else {
        return Ok(());
    };
    let Some(main) = configuration.main_cell().cell() else {
        return Ok(());
    };
    let built;
    let tree = match tree {
        Some(tree) if tree.configuration == descriptor.id() => tree,
        _ => match configuration_tree(descriptor.id(), declarations) {
            Ok(tree) => {
                built = tree;
                &built
            }
            // A malformed declaration is the configuration's lowering's error.
            Err(_) => return Ok(()),
        },
    };
    let Some(index) = cell_index(tree, &main.cell) else {
        return Ok(());
    };
    // A Map instance's key is its identity, so a step at a main cell inside it would change the
    // identity of the instance it is a step of.
    if let Some(&(holder, key)) = krs_ir::subject::keys_on_path(tree, index).first() {
        let (owner, field) = tree.fields[key];
        return Err(DescriptorLoweringError::MainCell {
            reason: format!(
                "the computation cell `{}` is the key `{}` of the instances of {} of configuration `{}`, or lies inside it: a sentence that names no cell (a term rule, a context, a strict production's heating) runs at the computation cell, so it would rewrite an instance's key, and the whole key is the instance's identity, which no step of the instance changes; key the instances by another child, declared first",
                unraw(&main.cell.field),
                unraw(&field.rust_field),
                holder_text(tree, holder),
                tree.configuration.item_name()
            ),
            range: key_range(owner, &field.reference.key).map(Box::new),
            item: Some(Box::new(descriptor.id().clone())),
        });
    }
    let Some(set) = instance_path(tree, index)
        .into_iter()
        .find(|&holder| tree.cells[holder].multiplicity == Multiplicity::Many(Order::Set))
    else {
        return Ok(());
    };
    let (owner, field) = tree.fields[set];
    Err(DescriptorLoweringError::MainCell {
        reason: format!(
            "the computation cell `{}` sits in an instance of {} of configuration `{}`: a sentence that names no cell (a term rule, a context, a strict production's heating) runs at the computation cell, so it is a local step of the instance that holds it, and a Set identifies an instance by its whole content, so a step that makes that instance equal to another merges the two, removing an instance the step never touched; hold the instances in a Map collection keyed by an id",
            main.cell.field,
            holder_text(tree, set),
            tree.configuration.item_name()
        ),
        range: key_range(owner, &field.reference.key).map(Box::new),
        item: Some(Box::new(descriptor.id().clone())),
    })
}

/// The holders whose one instance the semantic rule `rule` is a step of, where it is evaluated
/// ([`subject_path`]): its subject's for a sentence typed by a configuration or a group; its own
/// context's for an equation with a function context; none for a claim, which is about the
/// whole transition system; and the main cell's for every other sentence, which runs at the main
/// cell.
fn rule_path(
    rule: &SemanticRule,
    declarations: &DescriptorIndex<'_>,
    tree: &ConfigurationTree<'_>,
    main: &[usize],
) -> Vec<usize> {
    // A claim is about the whole transition system, whatever form it is written in.
    if rule.kind() == krs_ir::SentenceKind::Claim {
        return Vec::new();
    }
    let Some(descriptor) = declarations.get(rule.id()) else {
        return main.to_vec();
    };
    match descriptor.payload() {
        DescriptorPayload::ConfigurationRule(sentence) => {
            subject_path(tree, sentence.subject_configuration.subject.as_ref())
        }
        DescriptorPayload::ContextAlias(alias) => {
            subject_path(tree, alias.configuration.subject.as_ref())
        }
        DescriptorPayload::HeadRule(sentence) if sentence.subject.is_some() => {
            subject_path(tree, sentence.subject.as_ref())
        }
        // A configuration-typed record clause runs where its computation cell is: a cell at a
        // fixed position, or the main cell for a table clause.
        DescriptorPayload::HeadRule(sentence) => sentence
            .computation_cell
            .as_ref()
            .and_then(|computation| cell_index(tree, &computation.cell))
            .map(|index| instance_path(tree, index))
            .unwrap_or_default(),
        DescriptorPayload::StructuredRule(sentence) => match &sentence.function_context {
            Some(context) => subject_path(tree, context.configuration.subject.as_ref()),
            None => main.to_vec(),
        },
        _ => main.to_vec(),
    }
}

/// Every declared application at or below `term`, in preorder.
fn applications<'a>(
    term: &'a SemanticTerm,
    output: &mut Vec<(&'a StableItemId, &'a SemanticTerm)>,
) {
    if let SemanticTermKind::Application {
        application: krs_ir::ApplicationRef::Declared(production),
        ..
    } = term.kind()
    {
        output.push((production, term));
    }
    for child in term.children() {
        applications(child, output);
    }
}

/// The terms a rule evaluates functions in: an equation's or a simplification's right-hand side
/// and requires, since its left-hand side is the pattern it is about, not an application it
/// evaluates; every term of any other sentence.
fn evaluated_terms(rule: &SemanticRule) -> Vec<&SemanticTerm> {
    let pattern_left = matches!(
        rule.kind(),
        krs_ir::SentenceKind::Equation | krs_ir::SentenceKind::Simplification
    );
    let mut terms = match rule.relational_body() {
        RuleBodyRef::Term(body) if pattern_left => vec![body.to()],
        RuleBodyRef::Term(body) => vec![body.from(), body.to()],
        RuleBodyRef::Predicate(body) if pattern_left => body.rhs().terms(),
        RuleBodyRef::Predicate(body) => body
            .lhs()
            .terms()
            .into_iter()
            .chain(body.rhs().terms())
            .collect(),
        RuleBodyRef::Configuration { body, .. } => body
            .parts()
            .iter()
            .flat_map(krs_ir::ClausePart::terms)
            .collect(),
    };
    terms.extend(rule.requires().into_iter().flat_map(IrCondition::terms));
    terms.extend(rule.ensures().into_iter().flat_map(IrCondition::terms));
    terms
}

/// The function an equation defines: the declared head of its left-hand side.
fn defined_function(rule: &SemanticRule) -> Option<&StableItemId> {
    if rule.kind() != krs_ir::SentenceKind::Equation {
        return None;
    }
    let RuleBodyRef::Term(body) = rule.relational_body() else {
        return None;
    };
    match body.from().kind() {
        SemanticTermKind::Application {
            application: krs_ir::ApplicationRef::Declared(function),
            ..
        } => Some(function),
        _ => None,
    }
}

/// Judges every function whose context reads one instance of a group, then refuses those
/// contexts, which are not emitted inside an instance yet.
///
/// A function context typed by a group reads the group's cells in the configuration the
/// function is evaluated in. Where the group sits in an optional cell or a Map collection, that
/// is the one instance of each holder on its path ([`subject_path`]) the evaluation determines,
/// so the function is applied only from a sentence whose own holders extend that path: a sentence
/// about the group or a group inside its instance, or a sentence at a main cell inside that
/// instance. A sentence elsewhere (a rule for the configuration, a configuration-typed function
/// context, a claim) determines no instance, and a function cannot take several values for one
/// argument, so the application is refused (`instance-context-caller`) where the sentence
/// writes it. An equation without a context of its own is evaluated where its caller is, so the
/// functions it applies are judged against its caller's holders, through any number of such
/// equations. A held-once group has no holders, so every caller qualifies.
///
/// # Errors
///
/// - [`DescriptorLoweringError::GroupInstance`] with `instance-context-caller` at the first
///   application whose sentence lies outside the instance a reached context reads;
/// - [`DescriptorLoweringError::GroupInstance`] with `group-subject-position` for a function
///   context inside an instance, whose emission is a later stage.
pub(super) fn check_instance_contexts(
    modules: &[SemanticModule],
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    let rules = modules
        .iter()
        .flat_map(SemanticModule::rules)
        .collect::<Vec<_>>();
    // Each equation with a context typed by a group in an instance, and its descriptor's
    // context: the definition has none unless it holds a group in an optional cell or a Map.
    let contexts = rules
        .iter()
        .filter(|rule| rule.function_context().is_some())
        .filter_map(|rule| {
            let descriptor = declarations.get(rule.id())?;
            let DescriptorPayload::StructuredRule(sentence) = descriptor.payload() else {
                return None;
            };
            let context = sentence.function_context.as_ref()?;
            context.configuration.subject.as_ref()?;
            Some((*rule, descriptor, context))
        })
        .collect::<Vec<_>>();
    let Some((_, _, first)) = contexts.first() else {
        return Ok(());
    };
    let Ok(tree) = configuration_tree(&first.configuration.configuration, declarations) else {
        return Ok(());
    };
    let in_instance = contexts
        .into_iter()
        .filter(|(_, _, context)| {
            !subject_path(&tree, context.configuration.subject.as_ref()).is_empty()
        })
        .collect::<Vec<_>>();
    if in_instance.is_empty() {
        return Ok(());
    }
    let main = declarations
        .configuration(tree.configuration)
        .ok()
        .and_then(|configuration| configuration.main_cell().cell())
        .and_then(|reference| cell_index(&tree, &reference.cell))
        .map(|index| instance_path(&tree, index))
        .unwrap_or_default();
    check_callers(&rules, declarations, &tree, &main)?;
    let (rule, descriptor, context) = in_instance[0];
    let subject = context.configuration.subject.as_ref();
    let scope = scope(&tree, subject).unwrap_or_default();
    let (Some(instance), Some(DescriptorSubject::Group { declaration })) =
        (scope.instance, subject)
    else {
        return Ok(());
    };
    Err(not_emitted(
        &tree,
        declaration,
        &scope,
        instance,
        "a function context",
        key_range(descriptor, &context.configuration.key),
    )
    .within(rule.id(), None))
}

/// The caller rule of [`check_instance_contexts`]: each application in a sentence that determines
/// its own holders (any sentence but an equation without a context of its own) reaches, through
/// equations without contexts, only contexts whose holders its own extend.
fn check_callers(
    rules: &[&SemanticRule],
    declarations: &DescriptorIndex<'_>,
    tree: &ConfigurationTree<'_>,
    main: &[usize],
) -> Result<(), DescriptorLoweringError> {
    let mut equations = BTreeMap::<&StableItemId, Vec<&SemanticRule>>::new();
    for rule in rules {
        if let Some(function) = defined_function(rule) {
            equations.entry(function).or_default().push(rule);
        }
    }
    for rule in rules {
        // An equation without a context of its own is evaluated where its caller is.
        if defined_function(rule).is_some() && rule.function_context().is_none() {
            continue;
        }
        let path = rule_path(rule, declarations, tree, main);
        let mut applied = Vec::new();
        for term in evaluated_terms(rule) {
            applications(term, &mut applied);
        }
        for (applied, application) in applied {
            let mut pending = vec![applied];
            let mut visited = BTreeSet::new();
            while let Some(function) = pending.pop() {
                if !visited.insert(function) {
                    continue;
                }
                for equation in equations.get(function).into_iter().flatten() {
                    if equation.function_context().is_none() {
                        let mut callees = Vec::new();
                        for term in evaluated_terms(equation) {
                            applications(term, &mut callees);
                        }
                        pending.extend(callees.into_iter().map(|(callee, _)| callee));
                        continue;
                    }
                    let needed = rule_path(equation, declarations, tree, main);
                    if path.starts_with(&needed) {
                        continue;
                    }
                    return Err(caller_outside(
                        tree,
                        declarations,
                        rule,
                        (applied, application),
                        (equation, function),
                        (&needed, &path),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// The refusal of the application `application` of `applied` in `rule`, whose holders `path`
/// do not extend `needed`, the holders of the context of `function`'s equation `equation`, which
/// the application reaches.
fn caller_outside(
    tree: &ConfigurationTree<'_>,
    declarations: &DescriptorIndex<'_>,
    rule: &SemanticRule,
    (applied, application): (&StableItemId, &SemanticTerm),
    (equation, function): (&SemanticRule, &StableItemId),
    (needed, path): (&[usize], &[usize]),
) -> DescriptorLoweringError {
    let common = needed
        .iter()
        .zip(path)
        .take_while(|(needed, path)| needed == path)
        .count();
    let holder = holder_text(tree, needed[common.min(needed.len() - 1)]);
    let group = declarations
        .get(equation.id())
        .and_then(|descriptor| match descriptor.payload() {
            DescriptorPayload::StructuredRule(sentence) => sentence.function_context.as_ref(),
            _ => None,
        })
        .and_then(|context| context.configuration.subject.as_ref())
        .map_or_else(String::new, |DescriptorSubject::Group { declaration }| {
            format!(" the cell group `{}`", declaration.item_name())
        });
    let reads = if applied == function {
        format!("`{}` reads", function.item_name())
    } else {
        format!(
            "`{}` applies `{}`, which reads",
            applied.item_name(),
            function.item_name()
        )
    };
    DescriptorLoweringError::GroupInstance {
        code: krs_diagnostic::codes::analysis::INSTANCE_CONTEXT_CALLER,
        reason: format!(
            "{reads}{group} through its function context in one instance of {holder}, the instance it is evaluated in, and this sentence is not inside such an instance, so it determines none: a function has one value for its arguments, so it is applied only from a sentence about one instance of that holder (a rule, a context alias or a function context for the group, or for a group inside its instance)"
        ),
        range: application
            .origin()
            .origin()
            .exact_authored_range()
            .map(Box::new),
        item: Some(Box::new(rule.id().clone())),
    }
}

#[cfg(test)]
mod tests {
    use krs_ir::{DescriptorLiteral, DescriptorTerm, ProvenanceKey, ProvenanceRole};

    use krs_ir::subject::{keeps_key_term, rewrites_keep};

    fn key() -> ProvenanceKey {
        ProvenanceKey::new(ProvenanceRole::RuleLeftLiteral, 0)
    }

    fn variable(name: &str) -> DescriptorTerm {
        DescriptorTerm::Variable {
            key: key(),
            path_key: key(),
            name: name.to_owned(),
        }
    }

    fn int(value: &str) -> DescriptorTerm {
        DescriptorTerm::Literal {
            key: key(),
            literal: DescriptorLiteral::Int(value.to_owned()),
        }
    }

    /// The key predicate over the descriptor's terms, which the compiler and the collector share:
    /// a written key is kept as the subject's binder for it (an alias's binder included) or as
    /// the same literal, and as nothing else.
    #[test]
    fn a_written_key_term_is_kept_only_as_the_matched_binder_or_literal() {
        let alias = DescriptorTerm::As {
            key: key(),
            binding_key: key(),
            name: "me".to_owned(),
            pattern: Box::new(int("0")),
        };
        assert!(keeps_key_term(&variable("me"), Some(&variable("me"))));
        assert!(keeps_key_term(&variable("me"), Some(&alias)));
        assert!(keeps_key_term(&int("0"), Some(&int("0"))));
        assert!(keeps_key_term(&int("0"), Some(&alias)));
        assert!(!keeps_key_term(&variable("me"), Some(&variable("other"))));
        assert!(!keeps_key_term(&int("1"), Some(&int("0"))));
        assert!(!keeps_key_term(&int("0"), Some(&variable("me"))));
        assert!(!keeps_key_term(&variable("me"), None));
        // An in-place rewrite keeps a key only where its sides are the same variable or literal.
        let rewrite = |from: DescriptorTerm, to: Option<DescriptorTerm>| DescriptorTerm::Rewrite {
            key: key(),
            from_key: key(),
            to_key: key(),
            from: Box::new(from),
            to: to.map(Box::new),
        };
        assert!(rewrites_keep(&rewrite(variable("n"), Some(variable("n")))));
        assert!(rewrites_keep(&variable("n")));
        assert!(!rewrites_keep(&rewrite(variable("n"), Some(variable("m")))));
        assert!(!rewrites_keep(&rewrite(int("0"), Some(int("1")))));
        assert!(!rewrites_keep(&rewrite(variable("n"), None)));
        // Below an alias, as below any other node.
        assert!(!rewrites_keep(&DescriptorTerm::As {
            key: key(),
            binding_key: key(),
            name: "me".to_owned(),
            pattern: Box::new(rewrite(int("0"), Some(int("1")))),
        }));
    }
}

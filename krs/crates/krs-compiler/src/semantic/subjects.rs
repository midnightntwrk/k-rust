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
    DescriptorTerm, ProtocolCellContent, ProtocolHeadRuleExtra, ProvenanceKey, SourceRange,
    StableItemId,
};
use krs_ir_levels::{SemanticModule, SemanticRule, SemanticTerm};

use crate::instance_keys::{defined_function, evaluated_applications, term_applications};

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
        // The subjects are judged where the references are, before a readable rule is
        // elaborated: its inference reads the cells it names, so it names them in scope first.
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
/// - [`DescriptorLoweringError::MainCell`] for a main cell inside a Set or a List collection's
///   instance, or at or inside a Map instance's key ([`check_main_cell_holders`]).
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

/// Checks a sentence about one instance of its group (its scope has an instance,
/// [`SubjectScope::instance`]): it writes a Map instance's key only as what it matched.
///
/// A Map collection's key, its instance's first child, is the instance's identity, whole, be it a
/// leaf or a group: a local step writes nothing at or inside it except the subject's own binder
/// for it or the same literal (`krs_syntax::cell_entries::keeps_key`, the predicate the collector
/// applies to the authored entries, here over the terms the descriptor holds).
///
/// Every clause of a rule, a context alias, a `#[k::context]` and a function context inside an
/// instance is emitted inside the instance's cell on both emission routes, so each matches in the
/// one instance the sentence is about; a function context's callers are judged later
/// ([`check_instance_contexts`]).
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
        // The subjects are judged before a readable rule is elaborated ([`typed_parts`]).
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
/// an instance of a Set or a List collection.
///
/// The main cell is where a sentence that names no cell runs (a term rule, a context, a strict
/// production's heating), so each such sentence is a local step of the instance that holds the
/// computation, as a rule for that instance's group is. A Set identifies an instance by its whole
/// content: a step that makes the instance equal to another merges the two, removing an instance
/// the step never touched, so the step is no local step of its instance. A List keeps an
/// instance's position, so the step is about the instance at any position, and matching one
/// instance between others is not supported. The outermost such holder is named. The
/// configuration's own refusals of its main cell ([`super::configuration`]) are told where it has
/// none.
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
    let Some((holder, why)) = instance_path(tree, index).into_iter().find_map(|holder| {
        match tree.cells[holder].multiplicity {
            Multiplicity::Many(Order::Set) => Some((
                holder,
                "and a Set identifies an instance by its whole content, so a step that makes that instance equal to another merges the two, removing an instance the step never touched",
            )),
            Multiplicity::Many(Order::List) => Some((
                holder,
                "which in a List is the instance at any position, and matching one instance between others is not supported yet",
            )),
            _ => None,
        }
    }) else {
        return Ok(());
    };
    let (owner, field) = tree.fields[holder];
    Err(DescriptorLoweringError::MainCell {
        reason: format!(
            "the computation cell `{}` sits in an instance of {} of configuration `{}`: a sentence that names no cell (a term rule, a context, a strict production's heating) runs at the computation cell, so it is a local step of the instance that holds it, {why}; hold the instances in a Map collection keyed by an id",
            main.cell.field,
            holder_text(tree, holder),
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
            if let Some(subject) = &sentence.subject_configuration.subject {
                subject_path(tree, Some(subject))
            } else {
                // A rule typed by the configuration runs where the cells it matches are:
                // completion places each in one instance of each holder on its path, whose key
                // the rule's evaluated applications are passed. The computation cell it matches
                // decides; a rule that matches none is in the instances every cell it matches
                // shares. A holder's own entry (an instance list, an optional cell's state)
                // matches the holder whole, in none of its instances.
                let paths = sentence.subject.cells.iter().filter_map(|cell| {
                    let index = cell_index(tree, &cell.field.cell)?;
                    let mut path = instance_path(tree, index);
                    if path.last() == Some(&index) {
                        path.pop();
                    }
                    Some((cell.wrapper == Some(krs_ir::CellWrapper::KCell), path))
                });
                let mut shared: Option<Vec<usize>> = None;
                for (computation, path) in paths {
                    if computation {
                        return path;
                    }
                    shared = Some(match shared {
                        None => path,
                        Some(shared) => shared
                            .into_iter()
                            .zip(path)
                            .take_while(|(left, right)| left == right)
                            .map(|(left, _)| left)
                            .collect(),
                    });
                }
                shared.unwrap_or_default()
            }
        }
        DescriptorPayload::ContextAlias(alias) => {
            subject_path(tree, alias.configuration.subject.as_ref())
        }
        DescriptorPayload::StructuredRule(sentence) => match &sentence.function_context {
            Some(context) => subject_path(tree, context.configuration.subject.as_ref()),
            None => main.to_vec(),
        },
        _ => main.to_vec(),
    }
}

/// Judges every function whose context reads one instance of a group, and every sentence that
/// passes such a function the keys of its instance.
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
/// equations. The initializer builds the configuration, so it is evaluated in no instance and
/// applies no such function. A held-once group has no holders, so every caller qualifies.
///
/// The function then receives the key of each Map collection on that path as a hidden argument
/// ([`crate::instance_keys`]), and every sentence that applies it passes the keys of its own
/// instance; [`check_instance_keys`] refuses the sentences that cannot.
///
/// # Errors
///
/// - [`DescriptorLoweringError::GroupInstance`] with `instance-context-caller` at the first
///   application whose sentence lies outside the instance a reached context reads, then at the
///   first such application in the initializer;
/// - the first refusal of [`check_instance_keys`].
pub(super) fn check_instance_contexts(
    modules: &[SemanticModule],
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    let rules = modules
        .iter()
        .flat_map(SemanticModule::rules)
        .collect::<Vec<_>>();
    // Each context typed by a group: the definition has none in an instance unless it holds a
    // group in an optional cell or a Map.
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
            Some(context)
        })
        .collect::<Vec<_>>();
    let Some(first) = contexts.first() else {
        return Ok(());
    };
    let Ok(tree) = configuration_tree(&first.configuration.configuration, declarations) else {
        return Ok(());
    };
    if contexts
        .iter()
        .all(|context| subject_path(&tree, context.configuration.subject.as_ref()).is_empty())
    {
        return Ok(());
    }
    let main = declarations
        .configuration(tree.configuration)
        .ok()
        .and_then(|configuration| configuration.main_cell().cell())
        .and_then(|reference| cell_index(&tree, &reference.cell))
        .map(|index| instance_path(&tree, index))
        .unwrap_or_default();
    let equations = context_equations(&rules);
    check_callers(&rules, &equations, declarations, &tree, &main)?;
    check_initializer(modules, &equations, declarations, &tree, &main)?;
    check_instance_keys(modules, &rules, declarations)
}

/// Each function's equations.
fn context_equations<'r>(
    rules: &[&'r SemanticRule],
) -> BTreeMap<&'r StableItemId, Vec<&'r SemanticRule>> {
    let mut equations = BTreeMap::<&StableItemId, Vec<&SemanticRule>>::new();
    for rule in rules {
        if let Some(function) = defined_function(rule) {
            equations.entry(function).or_default().push(rule);
        }
    }
    equations
}

/// Refuses the first sentence that cannot pass the keys a function it applies receives
/// ([`crate::instance_keys::KeyRefusal`]), where it applies the function or writes the key's
/// pattern.
///
/// # Errors
///
/// - [`DescriptorLoweringError::GroupInstance`] with `group-subject-position` for a key that
///   is a group of cells, which KRS does not pass yet, at the first function context that reads
///   such an instance, and for a key cell matched by a pattern that is no variable, literal or
///   wildcard, and for a `#[k::context]` that names no cell, which binds no key cell yet;
/// - [`DescriptorLoweringError::GroupInstance`] with `instance-context-caller` for a sentence
///   that rewrites wherever its left-hand side matches (a simplification, an `anywhere` rule, a
///   desugar), whose left-hand side receives no key its right-hand side or condition passes,
///   for an equation whose pattern applies a function receiving a key the equation does not
///   receive, and for a term rule whose main cell lies in no instance a function it applies is
///   evaluated in.
fn check_instance_keys(
    modules: &[SemanticModule],
    rules: &[&SemanticRule],
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    let keys = crate::instance_keys::InstanceKeys::of(modules);
    if keys.is_empty() {
        return Ok(());
    }
    let holder_of = |cell: &krs_ir::SemanticId| {
        keys.holder(cell)
            .expect("a refused key is a Map collection's")
    };
    // A key that is a group of cells is refused once, at the context that reads its instance,
    // whichever sentence passes it.
    if let Some((cell, reader)) = keys.group_key() {
        return Err(DescriptorLoweringError::GroupInstance {
            code: krs_diagnostic::codes::analysis::GROUP_SUBJECT_POSITION,
            reason: format!(
                "the instances of the Map collection cell `{}` are keyed by `{}`, a group of cells, and a function evaluated in one of them receives that instance's key: passing a key that is a group of cells is not emitted yet; key the instances by a leaf cell, declared first",
                holder_of(cell).name,
                holder_of(cell).key_name,
            ),
            range: declarations
                .get(reader)
                .and_then(|descriptor| match descriptor.payload() {
                    DescriptorPayload::StructuredRule(sentence) => sentence
                        .function_context
                        .as_ref()
                        .and_then(|context| key_range(descriptor, &context.configuration.key)),
                    _ => None,
                })
                .map(Box::new),
            item: Some(Box::new(reader.clone())),
        });
    }
    for rule in rules {
        let Err(refusal) = keys.bindings(rule) else {
            continue;
        };
        let (code, reason, range) = key_refusal(&keys, refusal);
        return Err(DescriptorLoweringError::GroupInstance {
            code,
            reason,
            range,
            item: Some(Box::new(rule.id().clone())),
        });
    }
    Ok(())
}

/// The code, reason and location of the refusal of a sentence that cannot pass the keys a
/// function it applies receives ([`check_instance_keys`]).
fn key_refusal(
    keys: &crate::instance_keys::InstanceKeys,
    refusal: crate::instance_keys::KeyRefusal<'_>,
) -> (krs_diagnostic::Code, String, Option<Box<SourceRange>>) {
    use crate::instance_keys::KeyRefusal;
    let holder_of = |cell: &krs_ir::SemanticId| {
        keys.holder(cell)
            .expect("a refused key is a Map collection's")
    };
    let receives = |function: &StableItemId, cell: &krs_ir::SemanticId| {
        format!(
            "`{}` is evaluated in one instance of the Map collection cell `{}` (its function context reads that instance, or the context of a function it applies does), so it receives that instance's key `{}`",
            function.item_name(),
            holder_of(cell).name,
            holder_of(cell).key_name,
        )
    };
    let at = |term: &SemanticTerm| term.origin().origin().exact_authored_range().map(Box::new);
    match refusal {
        KeyRefusal::Unbound {
            function,
            application,
            holder: cell,
        } => (
            krs_diagnostic::codes::analysis::INSTANCE_CONTEXT_CALLER,
            format!(
                "{}, and this sentence rewrites wherever its left-hand side matches (a simplification, an `anywhere` rule, a desugar), which applies no function receiving that key, so it determines no instance: a function has one value for its arguments, so such a sentence applies it only where its left-hand side applies a function evaluated in the same instance",
                receives(function, &cell)
            ),
            at(application),
        ),
        KeyRefusal::InPattern {
            function,
            application,
            holder: cell,
        } => (
            krs_diagnostic::codes::analysis::INSTANCE_CONTEXT_CALLER,
            format!(
                "{}, and this equation writes it in a pattern, which evaluates nothing, while the equation itself receives no such key, so the pattern determines no instance: a function has one value for its arguments, so it is applied only where the equation is evaluated in that instance",
                receives(function, &cell)
            ),
            at(application),
        ),
        KeyRefusal::Outside {
            function,
            application,
            holder: cell,
        } => (
            krs_diagnostic::codes::analysis::INSTANCE_CONTEXT_CALLER,
            format!(
                "{}, and this term rule runs at the head of the main cell, which lies in no such instance, so it determines none: a function has one value for its arguments, so it is applied only from a sentence about one instance of that holder",
                receives(function, &cell)
            ),
            at(application),
        ),
        KeyRefusal::Context {
            function,
            application,
            holder: cell,
        } => (
            krs_diagnostic::codes::analysis::GROUP_SUBJECT_POSITION,
            format!(
                "{}, and this context names no cell: it runs at the main cell, inside that instance, but it is emitted as K's `context`, which binds no key cell, so passing the instance's key from it is not emitted yet; write it as a context alias typed by the cell group, which names the instance's cells",
                receives(function, &cell)
            ),
            at(application),
        ),
        KeyRefusal::Pattern {
            holder: cell,
            pattern,
        } => (
            krs_diagnostic::codes::analysis::GROUP_SUBJECT_POSITION,
            format!(
                "the sentence matches `{}`, the key of the instances of the Map collection cell `{}`, with a pattern that is no variable, literal or `_`, and passes that key to a function evaluated in its instance, so no one term of the pattern is the key it passes; bind the key to a variable and test it in the condition",
                holder_of(&cell).key_name,
                holder_of(&cell).name,
            ),
            at(pattern),
        ),
        KeyRefusal::GroupKey => {
            unreachable!("a key that is a group of cells is refused above")
        }
    }
}

/// The first context `applied` reaches, through equations without a context of their own,
/// whose holders a sentence with holders `path` does not extend: the equation, its function and
/// the context's holders.
fn reached_outside<'r>(
    applied: &'r StableItemId,
    path: &[usize],
    equations: &BTreeMap<&'r StableItemId, Vec<&'r SemanticRule>>,
    declarations: &DescriptorIndex<'_>,
    tree: &ConfigurationTree<'_>,
    main: &[usize],
) -> Option<(&'r SemanticRule, &'r StableItemId, Vec<usize>)> {
    let mut pending = vec![applied];
    let mut visited = BTreeSet::new();
    while let Some(function) = pending.pop() {
        if !visited.insert(function) {
            continue;
        }
        for equation in equations.get(function).into_iter().flatten() {
            if equation.function_context().is_none() {
                pending.extend(
                    evaluated_applications(equation)
                        .into_iter()
                        .map(|(callee, _)| callee),
                );
                continue;
            }
            let needed = rule_path(equation, declarations, tree, main);
            if !path.starts_with(&needed) {
                return Some((equation, function, needed));
            }
        }
    }
    None
}

/// The caller rule of [`check_instance_contexts`]: each application in a sentence that determines
/// its own holders (any sentence but an equation without a context of its own) reaches, through
/// equations without contexts, only contexts whose holders its own extend.
fn check_callers(
    rules: &[&SemanticRule],
    equations: &BTreeMap<&StableItemId, Vec<&SemanticRule>>,
    declarations: &DescriptorIndex<'_>,
    tree: &ConfigurationTree<'_>,
    main: &[usize],
) -> Result<(), DescriptorLoweringError> {
    for rule in rules {
        // An equation without a context of its own is evaluated where its caller is.
        if defined_function(rule).is_some() && rule.function_context().is_none() {
            continue;
        }
        let path = rule_path(rule, declarations, tree, main);
        for (applied, application) in evaluated_applications(rule) {
            if let Some((equation, function, needed)) =
                reached_outside(applied, &path, equations, declarations, tree, main)
            {
                return Err(caller_outside(
                    tree,
                    declarations,
                    (rule.id(), Caller::Sentence),
                    (applied, application),
                    (equation, function),
                    (&needed, &path),
                ));
            }
        }
    }
    Ok(())
}

/// The initializer's part of the caller rule of [`check_instance_contexts`]: the initializer
/// builds the configuration, so it is evaluated in no instance, and it applies no function that
/// reaches a context in one.
fn check_initializer(
    modules: &[SemanticModule],
    equations: &BTreeMap<&StableItemId, Vec<&SemanticRule>>,
    declarations: &DescriptorIndex<'_>,
    tree: &ConfigurationTree<'_>,
    main: &[usize],
) -> Result<(), DescriptorLoweringError> {
    fn terms<'c>(
        cells: &'c [krs_ir::FixedInitializerCell<krs_ir::SemanticId, SemanticTerm>],
        output: &mut Vec<&'c SemanticTerm>,
    ) {
        for cell in cells {
            match cell.content() {
                krs_ir::FixedInitializerContent::Term { term } => output.push(term),
                krs_ir::FixedInitializerContent::Children { children } => terms(children, output),
            }
        }
    }
    let Some(configuration) = modules.iter().find_map(SemanticModule::configuration) else {
        return Ok(());
    };
    let mut initial = Vec::new();
    terms(configuration.initializer(), &mut initial);
    let mut applied = Vec::new();
    for term in initial {
        term_applications(term, &mut applied);
    }
    for (applied, application) in applied {
        if let Some((equation, function, needed)) =
            reached_outside(applied, &[], equations, declarations, tree, main)
        {
            return Err(caller_outside(
                tree,
                declarations,
                (tree.configuration, Caller::Initializer),
                (applied, application),
                (equation, function),
                (&needed, &[]),
            ));
        }
    }
    Ok(())
}

/// What applies a function [`caller_outside`] refuses.
#[derive(Clone, Copy)]
enum Caller {
    /// A sentence.
    Sentence,
    /// The configuration's initializer.
    Initializer,
}

/// The refusal of the application `application` of `applied` in `item` (a sentence, or the
/// configuration whose initializer writes it), whose holders `path` do not extend `needed`, the
/// holders of the context of `function`'s equation `equation`, which the application reaches.
fn caller_outside(
    tree: &ConfigurationTree<'_>,
    declarations: &DescriptorIndex<'_>,
    (item, caller): (&StableItemId, Caller),
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
    let caller = match caller {
        Caller::Sentence => "this sentence is not inside such an instance, so it determines none",
        Caller::Initializer => {
            "the initializer builds the configuration, so it is evaluated in no instance and determines none"
        }
    };
    DescriptorLoweringError::GroupInstance {
        code: krs_diagnostic::codes::analysis::INSTANCE_CONTEXT_CALLER,
        reason: format!(
            "{reads}{group} through its function context in one instance of {holder}, the instance it is evaluated in, and {caller}: a function has one value for its arguments, so it is applied only from a sentence about one instance of that holder (a rule, a context alias or a function context for the group, or for a group inside its instance)"
        ),
        range: application
            .origin()
            .origin()
            .exact_authored_range()
            .map(Box::new),
        item: Some(Box::new(item.clone())),
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

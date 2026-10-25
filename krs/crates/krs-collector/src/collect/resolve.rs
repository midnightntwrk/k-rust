//! Resolution of host descriptor payloads against the declared items of the selected packages.

use std::any::TypeId;
use std::collections::{HashMap, HashSet};

use krs_ir::{
    DescriptorApplicationRef, DescriptorApplicationReference, DescriptorPayload, DescriptorSortRef,
    DescriptorSortReference, DescriptorStage, HostApplicationIdentity, HostBuiltinRegistry,
    HostDescriptorPayload, HostItemId, HostSortReference, HostStage, HostTypeReference, ItemKind,
    RefMap, StableItemId,
};

use super::PendingDescriptor;
use crate::{CollectionError, CollectionErrorKind};

pub(super) fn declared_type_table(
    pending: &[PendingDescriptor],
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>, CollectionError> {
    let mut declarations = HashMap::new();
    for descriptor in pending {
        let kind = descriptor.id.item_kind();
        let Some(key) = descriptor.host.declared_type else {
            if matches!(
                kind,
                ItemKind::Sort
                    | ItemKind::Constructor
                    | ItemKind::Configuration
                    | ItemKind::Cell
                    | ItemKind::Constant
            ) {
                return Err(CollectionError::new(
                    CollectionErrorKind::MissingTypeDeclaration,
                    format!(
                        "type declaration `{}` exposes no build-local Rust type",
                        descriptor.id
                    ),
                ));
            }
            continue;
        };
        // A named constant's Rust item is a unit struct, which a use names
        // as it names a constructor.
        if !matches!(
            kind,
            ItemKind::Sort
                | ItemKind::Constructor
                | ItemKind::Configuration
                | ItemKind::Cell
                | ItemKind::Constant
        ) {
            return Err(CollectionError::new(
                CollectionErrorKind::ItemKindMismatch,
                format!(
                    "non-type item `{}` exposes a declared Rust type key",
                    descriptor.id
                ),
            ));
        }
        let resolved = key.resolve();
        if kind != ItemKind::Constructor && !matches!(resolved, HostApplicationIdentity::Nominal(_))
        {
            return Err(CollectionError::new(
                CollectionErrorKind::ItemKindMismatch,
                format!(
                    "non-constructor `{}` exposes an enum-variant declaration identity",
                    descriptor.id
                ),
            ));
        }
        if let Some(registry) = builtins
            && let HostApplicationIdentity::Nominal(type_id) = resolved
            && (registry.resolve_sort(type_id).is_some()
                || registry.resolve_operation(type_id).is_some()
                || registry.resolve_map_operation(type_id).is_some()
                || registry.resolve_list_operation(type_id).is_some()
                || registry.resolve_set_operation(type_id).is_some()
                || registry.resolve_ml_connective(type_id).is_some()
                || registry.resolve_operator(type_id).is_some())
        {
            return Err(CollectionError::new(
                CollectionErrorKind::DeclarationBuiltinCollision,
                format!(
                    "authored declaration `{}` reuses a compiler builtin marker type",
                    descriptor.id
                ),
            ));
        }
        if let Some((previous, _)) = declarations.insert(resolved, (descriptor.id.clone(), kind)) {
            return Err(CollectionError::new(
                CollectionErrorKind::DuplicateTypeDeclaration,
                format!(
                    "items `{}` and `{}` expose the same build-local Rust type",
                    previous, descriptor.id
                ),
            ));
        }
    }
    Ok(declarations)
}

type HostCellKey = (TypeId, TypeId);

pub(super) fn declared_cell_field_table(
    pending: &[PendingDescriptor],
) -> Result<HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>, CollectionError> {
    let mut fields = HashMap::new();
    for descriptor in pending {
        let declaration = match &descriptor.host.payload {
            HostDescriptorPayload::FixedConfiguration(configuration) => &configuration.declaration,
            HostDescriptorPayload::Cell(declaration) => declaration.as_ref(),
            HostDescriptorPayload::Sort(_)
            | HostDescriptorPayload::Constructor(_)
            | HostDescriptorPayload::Grammar(_)
            | HostDescriptorPayload::StructuredRule(_)
            | HostDescriptorPayload::ConfigurationRule(_)
            | HostDescriptorPayload::HeadRule(_)
            | HostDescriptorPayload::ContextAlias(_)
            | HostDescriptorPayload::Constant(_) => continue,
        };
        for field in &declaration.fields {
            let key = field.reference.cell.resolve();
            let stable = krs_ir::DescriptorCellIdentity {
                owner: descriptor.id.clone(),
                field: field.rust_field.clone(),
            };
            if fields.insert(key, stable).is_some() {
                return Err(CollectionError::new(
                    CollectionErrorKind::DuplicateTypeDeclaration,
                    format!(
                        "fixed cell field `{}` on `{}` reuses an owner/field marker identity",
                        field.rust_field, descriptor.id
                    ),
                ));
            }
        }
    }
    Ok(fields)
}

#[derive(Clone, Debug)]
struct HeadRuleCellTarget {
    identity: krs_ir::DescriptorCellIdentity,
    names: Vec<String>,
    /// The leaf wrapper; absent for a fixed nested (group) cell, which a
    /// readable record names as a whole (KF-016).
    wrapper: Option<krs_ir::CellWrapper>,
    /// Whether the cell is a `multiplicity = "*"` collection (KF-023).
    collection: bool,
    /// The `#[k::cell]` struct of a nested (group) cell, by its resolved
    /// type: a record in the entry that names the cell stands for the
    /// running configuration's cell of that group (U5).
    group: Option<TypeId>,
}

fn head_rule_cell_target(
    field: &krs_ir::HostCellField,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    wrapper: Option<krs_ir::CellWrapper>,
    group: Option<TypeId>,
) -> Result<HeadRuleCellTarget, CollectionError> {
    let identity = cell_fields
        .get(&field.reference.cell.resolve())
        .cloned()
        .ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::UnresolvedTypeReference,
                format!(
                    "fixed cell `{}` has no stable owner/field identity",
                    field.rust_field
                ),
            )
        })?;
    // A readable record names a cell by its field identifier without `r#`,
    // as Rust names a field.
    let rust_name = field
        .rust_field
        .strip_prefix("r#")
        .unwrap_or(&field.rust_field);
    let mut names = vec![rust_name.to_owned()];
    if let Some(emitted) = &field.emitted_name
        && !names.contains(&emitted.value)
    {
        names.push(emitted.value.clone());
    }
    Ok(HeadRuleCellTarget {
        identity,
        names,
        wrapper,
        collection: field
            .multiplicity
            .as_ref()
            .is_some_and(|multiplicity| multiplicity.value == "*"),
        group,
    })
}

#[derive(Clone, Debug)]
pub(super) struct HeadRuleTarget {
    configuration: StableItemId,
    cells: Vec<HeadRuleCellTarget>,
    /// The children of each nested `#[k::cell]` struct, by its resolved
    /// type: a group record that names fewer leaves some out.
    group_children: HashMap<TypeId, GroupChildren>,
}

/// The children of a nested `#[k::cell]` struct.
#[derive(Clone, Debug, Default)]
pub(super) struct GroupChildren {
    /// How many children the struct declares.
    count: usize,
    /// Its fixed (multiplicity one) group children, by field: the
    /// configuration nests each one's cell inside the struct's (U5).
    fixed: HashMap<String, TypeId>,
}

struct HeadRuleSelection<'a> {
    target: &'a HeadRuleTarget,
    /// The matched computation cell; absent for a cell-record rule that
    /// leaves it out (KF-015).
    computation: Option<&'a HeadRuleCellTarget>,
}

fn collect_head_rule_cells(
    declaration: &krs_ir::HostCellDeclaration,
    declarations: &HashMap<TypeId, &krs_ir::HostCellDeclaration>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    visiting: &mut HashSet<TypeId>,
    cells: &mut Vec<HeadRuleCellTarget>,
    group_children: &mut HashMap<TypeId, GroupChildren>,
) -> Result<(), CollectionError> {
    for field in &declaration.fields {
        match &field.content {
            krs_ir::ProtocolCellContent::Leaf { wrapper, .. } => {
                cells.push(head_rule_cell_target(
                    field,
                    cell_fields,
                    Some(*wrapper),
                    None,
                )?);
            }
            krs_ir::ProtocolCellContent::Nested { declaration } => {
                // A group, an optional group, or a collection is named by a
                // readable record entry; the leaves below a collection stay
                // reachable as its implicit single instance (KF-023).
                let key = declaration.declaration.key.resolve();
                cells.push(head_rule_cell_target(field, cell_fields, None, Some(key))?);
                if !visiting.insert(key) {
                    return Err(CollectionError::new(
                        CollectionErrorKind::InvalidConfiguration,
                        format!(
                            "cyclic nested fixed-cell declaration `{}`",
                            declaration.declaration.authored_path
                        ),
                    ));
                }
                let nested = declarations.get(&key).ok_or_else(|| {
                    CollectionError::new(
                        CollectionErrorKind::UnresolvedTypeReference,
                        format!(
                            "nested fixed-cell declaration `{}` was not collected",
                            declaration.declaration.authored_path
                        ),
                    )
                })?;
                group_children.insert(
                    key,
                    GroupChildren {
                        count: nested.fields.len(),
                        fixed: nested
                            .fields
                            .iter()
                            .filter(|child| child.multiplicity.is_none())
                            .filter_map(|child| match &child.content {
                                krs_ir::ProtocolCellContent::Nested { declaration } => Some((
                                    child.rust_field.clone(),
                                    declaration.declaration.key.resolve(),
                                )),
                                krs_ir::ProtocolCellContent::Leaf { .. } => None,
                            })
                            .collect(),
                    },
                );
                collect_head_rule_cells(
                    nested,
                    declarations,
                    cell_fields,
                    visiting,
                    cells,
                    group_children,
                )?;
                visiting.remove(&key);
            }
        }
    }
    Ok(())
}

pub(super) fn resolve_head_rule_targets(
    pending: &[PendingDescriptor],
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
) -> Result<Vec<HeadRuleTarget>, CollectionError> {
    if !pending
        .iter()
        .any(|descriptor| matches!(descriptor.host.payload, HostDescriptorPayload::HeadRule(_)))
    {
        return Ok(Vec::new());
    }
    let configurations = pending
        .iter()
        .filter_map(|descriptor| match &descriptor.host.payload {
            HostDescriptorPayload::FixedConfiguration(configuration) => {
                Some((descriptor, configuration.as_ref()))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let cell_declarations = pending
        .iter()
        .filter_map(|descriptor| {
            let HostDescriptorPayload::Cell(declaration) = &descriptor.host.payload else {
                return None;
            };
            let Some(krs_ir::HostDeclarationIdentity::Nominal(key)) = descriptor.host.declared_type
            else {
                return None;
            };
            Some((key.resolve(), declaration.as_ref()))
        })
        .collect::<HashMap<_, _>>();
    let targets = configurations
        .into_iter()
        .map(|(descriptor, configuration)| {
            let mut cells = Vec::new();
            let mut group_children = HashMap::new();
            collect_head_rule_cells(
                &configuration.declaration,
                &cell_declarations,
                cell_fields,
                &mut HashSet::new(),
                &mut cells,
                &mut group_children,
            )?;
            Ok(HeadRuleTarget {
                configuration: descriptor.id.clone(),
                cells,
                group_children,
            })
        })
        .collect::<Result<Vec<_>, CollectionError>>()?;
    // Each rule that needs one configuration, or one computation cell, checks it as it is
    // resolved, so the error is located at that rule.
    Ok(targets)
}

/// `a`, `b` and `c` for a message.
fn names<'a>(names: impl Iterator<Item = &'a str>) -> String {
    names
        .map(|name| format!("`{name}`"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The fixed configuration a head rule names, or the only one collected.
fn select_head_rule_target<'a>(
    rule: &krs_ir::HostHeadRule,
    targets: &'a [HeadRuleTarget],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<&'a HeadRuleTarget, CollectionError> {
    Ok(if let Some(configuration) = &rule.configuration {
        let selected = resolve_configuration_reference(configuration, declarations)?;
        targets
            .iter()
            .find(|target| target.configuration == selected.configuration)
            .ok_or_else(|| {
                CollectionError::new(
                    CollectionErrorKind::InvalidConfiguration,
                    "cell-record rule names a fixed configuration that was not collected",
                )
            })?
    } else {
        let [target] = targets else {
            let detail = match targets {
                [] => "this rule rewrites the head of the computation, but the definition has no `#[k::configuration]`: declare one with a `KSequence` cell, which holds the computation, and its `#[k::init]`".to_owned(),
                several => format!(
                    "this rule rewrites the head of the computation, but the definition declares {} configurations, {}; a definition has exactly one",
                    several.len(),
                    names(several.iter().map(|target| target.configuration.item_name())),
                ),
            };
            return Err(CollectionError::new(
                CollectionErrorKind::ConfigurationCount,
                detail,
            ));
        };
        target
    })
}

fn resolve_head_rule_target<'a>(
    rule: &krs_ir::HostHeadRule,
    targets: &'a [HeadRuleTarget],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<HeadRuleSelection<'a>, CollectionError> {
    let target = select_head_rule_target(rule, targets, declarations)?;
    if rule.head.is_none() {
        return Ok(HeadRuleSelection {
            target,
            computation: None,
        });
    }
    let computations = target
        .cells
        .iter()
        .filter(|cell| {
            cell.wrapper == Some(krs_ir::CellWrapper::KCell)
                && rule
                    .computation_cell_name
                    .as_ref()
                    .is_none_or(|name| cell.names.iter().any(|candidate| candidate == name))
        })
        .collect::<Vec<_>>();
    let [computation] = computations.as_slice() else {
        let configuration = target.configuration.item_name();
        let detail = match computations.as_slice() {
            [] => format!(
                "this rule rewrites the head of the computation, but configuration `{configuration}` has no `KSequence` cell to hold the computation"
            ),
            several => format!(
                "this rule rewrites the head of the computation, but configuration `{configuration}` has {} top-level `KSequence` cells, {}, and does not say which holds the computation: write the rule as a `for {configuration}` record, which names its cell",
                several.len(),
                names(
                    several
                        .iter()
                        .filter_map(|cell| cell.names.first().map(String::as_str))
                ),
            ),
        };
        return Err(CollectionError::new(
            CollectionErrorKind::ComputationCell,
            detail,
        ));
    };
    Ok(HeadRuleSelection {
        target,
        computation: Some(computation),
    })
}

struct Resolver<'a> {
    declarations: &'a HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &'a HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    context_aliases: &'a HashMap<HostItemId, StableItemId>,
    builtins: Option<&'a HostBuiltinRegistry>,
    head_targets: &'a [HeadRuleTarget],
    head_selection: Option<HeadRuleSelection<'a>>,
    allow_builtin_application: bool,
    /// The generated marker type of each sort parameter of this payload's
    /// parametric production, by its declared name (KF-027).
    parameters: HashMap<TypeId, String>,
}

impl RefMap<HostStage, DescriptorStage> for Resolver<'_> {
    type Error = CollectionError;

    fn sort(
        &mut self,
        reference: HostSortReference,
    ) -> Result<DescriptorSortReference, Self::Error> {
        if let Some(name) = self.parameters.get(&reference.target.key.resolve()) {
            return Ok(DescriptorSortReference {
                key: reference.key,
                sort: DescriptorSortRef::Parameter(name.clone()),
            });
        }
        resolve_sort_reference(&reference, self.declarations, self.builtins)
            .map_err(|error| error.with_reference_key(reference.key))
    }

    fn application(
        &mut self,
        reference: krs_ir::HostApplicationReference,
    ) -> Result<DescriptorApplicationReference, Self::Error> {
        resolve_application_reference(
            &reference,
            self.declarations,
            self.builtins,
            self.allow_builtin_application,
        )
        .map_err(|error| error.with_reference_key(reference.key))
    }

    fn nominal(&mut self, reference: HostTypeReference) -> Result<StableItemId, Self::Error> {
        resolve_nominal_reference(&reference, ItemKind::Cell, self.declarations)
    }

    fn context_alias(
        &mut self,
        reference: krs_ir::HostContextAliasReference,
    ) -> Result<krs_ir::DescriptorContextAliasReference, Self::Error> {
        Ok(krs_ir::DescriptorContextAliasReference {
            key: reference.key.clone(),
            alias: self
                .item(reference.alias)
                .map_err(|error| error.with_reference_key(reference.key))?,
        })
    }

    fn configuration(
        &mut self,
        reference: krs_ir::HostConfigurationReference,
    ) -> Result<krs_ir::DescriptorConfigurationReference, Self::Error> {
        if let Some(selection) = &self.head_selection {
            return Ok(krs_ir::DescriptorConfigurationReference {
                key: reference.key,
                configuration: selection.target.configuration.clone(),
            });
        }
        resolve_configuration_reference(&reference, self.declarations)
            .map_err(|error| error.with_reference_key(reference.key))
    }

    fn cell(
        &mut self,
        reference: krs_ir::HostCellReference,
    ) -> Result<krs_ir::DescriptorCellReference, Self::Error> {
        resolve_cell_reference(&reference, self.cell_fields)
            .map_err(|error| error.with_reference_key(reference.key))
    }

    fn head_rule_cell(
        &mut self,
        reference: krs_ir::HostHeadRuleCellReference,
    ) -> Result<krs_ir::DescriptorCellReference, Self::Error> {
        let selection = self
            .head_selection
            .as_ref()
            .expect("head-rule cell resolution requires a selected configuration");
        let matches = selection
            .target
            .cells
            .iter()
            .filter(|candidate| candidate.names.iter().any(|name| name == &reference.name))
            .collect::<Vec<_>>();
        let [resolved] = matches.as_slice() else {
            let detail = match matches.len() {
                0 => format!(
                    "readable rule extra names no fixed leaf cell `{}`",
                    reference.name
                ),
                count => format!(
                    "readable rule extra cell name `{}` is ambiguous across {count} fixed leaf cells",
                    reference.name
                ),
            };
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                detail,
            ));
        };
        if selection
            .computation
            .is_some_and(|computation| resolved.identity == computation.identity)
        {
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                format!(
                    "readable rule extra may not mention computation cell `{}`",
                    reference.name
                ),
            ));
        }
        Ok(krs_ir::DescriptorCellReference {
            key: reference.key,
            cell: resolved.identity.clone(),
        })
    }

    fn item(&mut self, reference: HostItemId) -> Result<StableItemId, Self::Error> {
        self.context_aliases
            .get(&reference)
            .cloned()
            .ok_or_else(|| {
                CollectionError::new(
                    CollectionErrorKind::UnresolvedTypeReference,
                    format!("unknown context alias `{}`", reference.item_name()),
                )
            })
    }

    fn cell_declaration(
        &mut self,
        reference: krs_ir::HostCellDeclarationReference,
    ) -> Result<krs_ir::DescriptorCellDeclarationReference, Self::Error> {
        resolve_cell_declaration_reference(&reference, self.declarations)
            .map_err(|error| error.with_reference_key(reference.key))
    }

    fn initializer_owner(
        &mut self,
        reference: krs_ir::HostTypeKey,
    ) -> Result<StableItemId, Self::Error> {
        resolve_declared_identity(
            HostApplicationIdentity::Nominal(reference.resolve()),
            "Self",
            ItemKind::Configuration,
            self.declarations,
        )
    }

    fn parent(&mut self, reference: HostSortReference) -> Result<StableItemId, Self::Error> {
        resolve_nominal_reference(&reference.target, ItemKind::Sort, self.declarations)
            .map_err(|error| error.with_reference_key(reference.key))
    }

    fn constructor_sort(
        &mut self,
        reference: HostSortReference,
    ) -> Result<DescriptorSortRef, Self::Error> {
        Ok(self.sort(reference)?.sort)
    }

    fn constructor_field_sort(
        &mut self,
        reference: HostSortReference,
    ) -> Result<Option<DescriptorSortRef>, Self::Error> {
        if let Some(name) = self.parameters.get(&reference.target.key.resolve()) {
            return Ok(Some(DescriptorSortRef::Parameter(name.clone())));
        }
        resolve_constructor_field_sort(&reference.target, self.declarations, self.builtins)
            .map(Some)
            .map_err(|error| error.with_reference_key(reference.key))
    }

    fn term(&mut self, term: krs_ir::HostTerm) -> Result<krs_ir::HostTerm, Self::Error> {
        Ok(group_record_term(term, self.declarations, |_, _, open| {
            open
        }))
    }
}

/// Reads a readable record in a cell position as the group term it names
/// when rustc resolved its head to a `#[k::cell]` struct (KF-016): `frame:
/// Frame { pc: p, gas: g }` is `k::fragment![crate::Frame { .. }]`. The
/// application's head and field keys become the cell term's, as the
/// `fragment!` spelling numbers them. An alias `saved @ Frame { .. }` names
/// the group it matches, and a result's `Frame { pc: e, ..saved }` updates
/// it (F5).
///
/// `position` is the group whose cell of the running configuration the term
/// stands for: the group the entry names, and below a record there, each
/// fixed group child's own group, since the configuration nests that cell
/// there (U5). A subject record at its own group's position leaves the
/// children it does not name unconstrained, with or without `..`. Anywhere
/// else (a leaf cell's content, a list element, a constructor argument)
/// the record is a value of its cell sort, complete unless it ends in `..`,
/// and the records below a value are read by [`group_record_term`].
fn readable_group_term(
    term: krs_ir::HostTerm,
    subject: bool,
    position: Option<TypeId>,
    groups: &GroupRecords<'_>,
) -> krs_ir::HostTerm {
    use krs_ir::Term;
    if let Term::As {
        key,
        binding_key,
        name,
        pattern,
    } = term
    {
        return Term::As {
            key,
            binding_key,
            name,
            pattern: Box::new(readable_group_term(*pattern, subject, position, groups)),
        };
    }
    let term = group_record_term(
        term,
        groups.declarations,
        |target, fields, authored_open| {
            subject
                && (authored_open
                    || (position == Some(target)
                        && groups
                            .children
                            .get(&target)
                            .is_some_and(|children| fields < children.count)))
        },
    );
    // A record at its group's own position, written bare or as
    // `k::fragment!`, holds its fixed group children at theirs.
    let Term::Cell {
        key,
        declaration,
        fields,
        open,
        update,
    } = term
    else {
        return term;
    };
    let fixed = position
        .filter(|position| *position == declaration.key.resolve())
        .and_then(|position| groups.children.get(&position))
        .map(|children| &children.fixed);
    let fields = fields
        .into_iter()
        .map(|mut field| {
            if let Some(child) = fixed.and_then(|fixed| fixed.get(field.field.as_str())) {
                let value = std::mem::replace(&mut *field.value, placeholder_term());
                *field.value = readable_group_term(value, subject, Some(*child), groups);
            }
            field
        })
        .collect();
    Term::Cell {
        key,
        declaration,
        fields,
        open,
        update,
    }
}

/// Reads a record whose head rustc resolved to a `#[k::cell]` struct as the
/// group's cell term, at any depth of any term (a list element, a
/// constructor argument, an alias target): the group's cell is a value of
/// its generated cell sort like any constructor term, and `CallState { .. }`
/// names it as `k::fragment![CallState { .. }]` does. Outside a
/// configuration cell position the term is a complete value, so a pattern
/// leaves children unconstrained only with `..`; `open` decides from the
/// group's type identity, the number of named children, and the record's
/// own `..`. Any other term is returned unchanged.
fn group_record_term(
    term: krs_ir::HostTerm,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    open: impl FnOnce(TypeId, usize, bool) -> bool,
) -> krs_ir::HostTerm {
    use krs_ir::{Arguments, HostApplicationTarget, Term};
    let Term::Application {
        head_class: krs_ir::DescriptorApplicationHeadClass::Applied,
        reference,
        arguments,
        instance,
        open: authored_open,
        update,
        ..
    } = &term
    else {
        return term;
    };
    let HostApplicationTarget::Nominal(target) = &reference.target else {
        return term;
    };
    // A record, `Frame { pc: p }`, a pattern naming no child, `Frame { .. }`,
    // or an update listing none, `Frame { ..saved }`: the matched group
    // unchanged (N7).
    let record = matches!(arguments, Arguments::Named(_))
        || ((*authored_open || update.is_some()) && arguments.is_empty());
    if !instance.is_empty()
        || !record
        || !matches!(
            declarations.get(&HostApplicationIdentity::Nominal(target.key.resolve())),
            Some((_, ItemKind::Cell))
        )
    {
        return term;
    }
    let authored_open = *authored_open;
    let Term::Application {
        reference,
        arguments,
        update,
        ..
    } = term
    else {
        unreachable!("the record was matched above");
    };
    let HostApplicationTarget::Nominal(declaration) = reference.target else {
        unreachable!("the record head was matched above");
    };
    let fields = Vec::from(arguments)
        .into_iter()
        .filter_map(|argument| match argument {
            krs_ir::TermArgument::Named { key, field, value } => {
                Some(krs_ir::CellTermField { key, field, value })
            }
            krs_ir::TermArgument::Positional { .. } => None,
        })
        .collect::<Vec<_>>();
    Term::Cell {
        key: reference.key,
        open: open(declaration.key.resolve(), fields.len(), authored_open),
        declaration,
        fields,
        update,
    }
}

/// What [`readable_group_term`] reads a record's head and children against.
struct GroupRecords<'a> {
    declarations: &'a HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    children: &'a HashMap<TypeId, GroupChildren>,
    /// The cells of the selected configuration, which give each entry's
    /// group.
    cells: &'a [HeadRuleCellTarget],
}

impl GroupRecords<'_> {
    /// The group whose configuration cell the readable entry `name` names,
    /// if it names exactly one group cell.
    fn position(&self, name: &str) -> Option<TypeId> {
        let mut named = self
            .cells
            .iter()
            .filter(|cell| cell.names.iter().any(|candidate| candidate == name));
        match (named.next(), named.next()) {
            (Some(cell), None) => cell.group,
            _ => None,
        }
    }
}

/// Applies [`readable_group_term`] to the cell values of a readable rule:
/// fixed-cell entries and the inside of `Some(..)`.
fn readable_group_terms(
    mut rule: krs_ir::HostHeadRule,
    groups: &GroupRecords<'_>,
) -> krs_ir::HostHeadRule {
    fn present(
        state: &mut krs_ir::ProtocolRuleStateTerm<krs_ir::HostTerm>,
        subject: bool,
        position: Option<TypeId>,
        groups: &GroupRecords<'_>,
    ) {
        if let krs_ir::ProtocolRuleStateTerm::Present { value } = state
            && let krs_ir::ProtocolRuleStateTerm::Term(term) = value.as_mut()
        {
            let taken = std::mem::replace(term, placeholder_term());
            *term = readable_group_term(taken, subject, position, groups);
        }
    }
    for extra in &mut rule.extras {
        match extra {
            krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                cell,
                before,
                after,
                ..
            } => {
                let position = groups.position(&cell.name);
                let taken = std::mem::replace(before, placeholder_term());
                *before = readable_group_term(taken, true, position, groups);
                if let Some(after) = after {
                    let taken = std::mem::replace(after, placeholder_term());
                    *after = readable_group_term(taken, false, position, groups);
                }
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteState {
                cell,
                before,
                after,
                ..
            } => {
                let position = groups.position(&cell.name);
                present(before, true, position, groups);
                if let Some(after) = after {
                    present(after, false, position, groups);
                }
            }
            krs_ir::ProtocolHeadRuleExtra::HaveMap { .. }
            | krs_ir::ProtocolHeadRuleExtra::UpdateMap { .. }
            | krs_ir::ProtocolHeadRuleExtra::RewriteList { .. } => {}
        }
    }
    rule
}

fn placeholder_term() -> krs_ir::HostTerm {
    krs_ir::Term::Wildcard {
        key: krs_ir::ProvenanceKey::new(krs_ir::ProvenanceRole::RulePattern, 0),
    }
}

/// Keeps the reading of a bracketed cell value that the cell's declared
/// type gives (KF-023). `job: [Job { payload: p }, ..] => job: [..]` reads
/// both as the computation cell's head and as a List collection's front
/// instance, and `job: [.., Job { payload: p }]` both as a list's elements
/// and as a back instance; the macro carries the head or the elements with
/// the List reading beside them, and a `*` collection cell takes the List
/// reading, its instances in place of the head or the elements. Any other
/// cell keeps the reading the macro took, which names the computation cell,
/// a list cell, or is reported as naming neither.
fn readable_bracket_reading(
    mut rule: krs_ir::HostHeadRule,
    targets: &[HeadRuleTarget],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<krs_ir::HostHeadRule, CollectionError> {
    let Some(alternative) = rule.bracket_alternative.take() else {
        return Ok(rule);
    };
    let krs_ir::ProtocolHeadRuleExtra::RewriteState { cell, .. } = &alternative.extra else {
        return Ok(rule);
    };
    let target = select_head_rule_target(&rule, targets, declarations)?;
    let named = target
        .cells
        .iter()
        .filter(|candidate| candidate.names.iter().any(|name| name == &cell.name))
        .collect::<Vec<_>>();
    if let [candidate] = named.as_slice()
        && candidate.collection
    {
        if rule.computation_cell_name.as_ref() == Some(&cell.name) {
            rule.head = None;
            rule.computation_cell_name = None;
        }
        rule.extras.retain(|extra| {
            !matches!(
                extra,
                krs_ir::ProtocolHeadRuleExtra::RewriteList { cell: list, .. }
                    if list.name == cell.name
            )
        });
        rule.bindings = alternative.bindings;
        rule.extras.push(alternative.extra);
    }
    Ok(rule)
}

/// Gives a readable record's sequence values the readings their cells'
/// declared types give (F6). `[a, b, ..] => [c, ..]` reads alike as the
/// computation cell's items and as a list's elements, and only the
/// configuration says which cell is which: the macro reads one such value
/// as the head, a cell named `k` if there is one, and the others as list
/// cells. The computation cell is the configuration's one `KCell` leaf, so a
/// head on an ordinary leaf cell becomes that cell's list, and a list on the
/// computation cell becomes the head. Both readings hold the same terms, so
/// moving one to the other changes no binder. A cell of neither kind keeps
/// its reading and is reported where it is checked.
fn readable_list_reading(
    mut rule: krs_ir::HostHeadRule,
    targets: &[HeadRuleTarget],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<krs_ir::HostHeadRule, CollectionError> {
    let has_list = rule.extras.iter().any(|extra| {
        matches!(extra, krs_ir::ProtocolHeadRuleExtra::RewriteList { .. })
            || empty_brackets(extra).is_some()
    });
    if rule.configuration.is_none() || (rule.computation_cell_name.is_none() && !has_list) {
        return Ok(rule);
    }
    let target = select_head_rule_target(&rule, targets, declarations)?;
    let wrapper = |name: &str| {
        let named = target
            .cells
            .iter()
            .filter(|cell| cell.names.iter().any(|candidate| candidate == name))
            .collect::<Vec<_>>();
        match named.as_slice() {
            [cell] if !cell.collection => cell.wrapper,
            _ => None,
        }
    };
    if let Some(name) = &rule.computation_cell_name
        && rule.head.is_some()
        && wrapper(name) == Some(krs_ir::CellWrapper::Cell)
    {
        let head = rule.head.take().expect("checked above");
        let name = rule.computation_cell_name.take().expect("checked above");
        rule.extras
            .push(head_list(head, name, &rule.pattern_key, &rule.result_key));
    }
    if rule.head.is_none()
        && let Some(index) = rule.extras.iter().position(|extra| {
            matches!(
                extra,
                krs_ir::ProtocolHeadRuleExtra::RewriteList { cell, .. }
                    if wrapper(&cell.name) == Some(krs_ir::CellWrapper::KCell)
            )
        })
    {
        let krs_ir::ProtocolHeadRuleExtra::RewriteList {
            cell,
            result_key,
            before,
            after,
        } = rule.extras.remove(index)
        else {
            unreachable!("the position matched a list cell");
        };
        rule.head = Some(list_head(&cell, result_key.as_ref(), before, after)?);
        rule.computation_cell_name = Some(cell.name);
    }
    // `[]` reads alike as no instances of a List collection and as the
    // empty cons list, and the macro, which cannot see declared types,
    // reads it as instances: on an ordinary leaf cell it is the empty list.
    for extra in &mut rule.extras {
        if let Some(cell) = empty_brackets(extra)
            && wrapper(&cell.name) == Some(krs_ir::CellWrapper::Cell)
        {
            let krs_ir::ProtocolHeadRuleExtra::RewriteState {
                cell, result_key, ..
            } = extra.clone()
            else {
                unreachable!("empty brackets are a state extra");
            };
            let empty = || krs_ir::ProtocolHeadRuleList {
                items: Vec::new(),
                rest: krs_ir::ProtocolHeadRuleListRest::Exact,
                back: Vec::new(),
            };
            *extra = krs_ir::ProtocolHeadRuleExtra::RewriteList {
                cell,
                after: result_key.as_ref().map(|_| empty()),
                result_key,
                before: empty(),
            };
        }
    }
    Ok(rule)
}

/// The cell of a state extra that matches the empty bracketed instance
/// list `[]`, and rewrites it to `[]` again or leaves it out.
fn empty_brackets(extra: &krs_ir::HostHeadRuleExtra) -> Option<&krs_ir::HostHeadRuleCellReference> {
    let is_empty = |state: &krs_ir::ProtocolRuleStateTerm<krs_ir::HostTerm>| {
        matches!(
            state,
            krs_ir::ProtocolRuleStateTerm::Instances(instances)
                if instances.delimiter == krs_ir::InstanceDelimiter::Bracket
                    && instances.front.is_empty()
                    && instances.back.is_empty()
                    && instances.rest == krs_ir::ProtocolRuleFrame::Exact
        )
    };
    match extra {
        krs_ir::ProtocolHeadRuleExtra::RewriteState {
            cell,
            before,
            after,
            ..
        } if is_empty(before) && after.as_ref().is_none_or(is_empty) => Some(cell),
        _ => None,
    }
}

/// The list reading of the head `head` read on the ordinary cell `name`:
/// the same items, with the anonymous `..` as the list's shared rest. The
/// head carries no cell key, so the cell is keyed at the whole pattern and
/// its result at the whole result.
fn head_list(
    head: krs_ir::ProtocolHeadRuleHead<krs_ir::HostTerm>,
    name: String,
    pattern_key: &krs_ir::ProvenanceKey,
    result_key: &krs_ir::ProvenanceKey,
) -> krs_ir::HostHeadRuleExtra {
    let rest = || {
        if head.exact {
            krs_ir::ProtocolHeadRuleListRest::Exact
        } else {
            krs_ir::ProtocolHeadRuleListRest::Shared
        }
    };
    let after = head.result.map(|result| krs_ir::ProtocolHeadRuleList {
        items: match result {
            krs_ir::ProtocolHeadRuleResult::Replace(term) => vec![term],
            krs_ir::ProtocolHeadRuleResult::Splice(terms) => terms,
            krs_ir::ProtocolHeadRuleResult::Erase => Vec::new(),
        },
        rest: rest(),
        back: Vec::new(),
    });
    krs_ir::ProtocolHeadRuleExtra::RewriteList {
        cell: krs_ir::HostHeadRuleCellReference {
            key: pattern_key.clone(),
            name,
        },
        result_key: after.as_ref().map(|_| result_key.clone()),
        before: krs_ir::ProtocolHeadRuleList {
            items: head.items,
            rest: rest(),
            back: Vec::new(),
        },
        after,
    }
}

/// The head reading of a list read on the computation cell `cell`, whose
/// rest is anonymous and last: K's sequence is matched from its front, the
/// next step first, and its rest kept by `..`, never named.
fn list_head(
    cell: &krs_ir::HostHeadRuleCellReference,
    result_key: Option<&krs_ir::ProvenanceKey>,
    before: krs_ir::ProtocolHeadRuleList<krs_ir::HostTerm>,
    after: Option<krs_ir::ProtocolHeadRuleList<krs_ir::HostTerm>>,
) -> Result<krs_ir::ProtocolHeadRuleHead<krs_ir::HostTerm>, CollectionError> {
    let named = || {
        CollectionError::new(
            CollectionErrorKind::InvalidConfiguration,
            format!(
                "`{}` is the computation cell, whose rest is the anonymous `..`; a named rest (`rest @ ..`, `..rest`) belongs to a list cell",
                cell.name
            ),
        )
        .with_reference_key(cell.key.clone())
    };
    // The entry that names an item after the rest is the mistake, the subject's or the result's.
    let back = |key: &krs_ir::ProvenanceKey| {
        CollectionError::new(
            CollectionErrorKind::InvalidConfiguration,
            format!(
                "`..` may only end the computation cell `{}`'s items: it is matched from its front, the next step first, so name the items before the rest",
                cell.name
            ),
        )
        .with_reference_key(key.clone())
    };
    if !before.back.is_empty() {
        return Err(back(&cell.key));
    }
    if after.as_ref().is_some_and(|after| !after.back.is_empty()) {
        return Err(back(result_key.unwrap_or(&cell.key)));
    }
    let exact = match before.rest {
        krs_ir::ProtocolHeadRuleListRest::Exact => true,
        krs_ir::ProtocolHeadRuleListRest::Shared => false,
        krs_ir::ProtocolHeadRuleListRest::Term(_) => return Err(named()),
    };
    let result = match after {
        None => None,
        Some(krs_ir::ProtocolHeadRuleList {
            rest: krs_ir::ProtocolHeadRuleListRest::Term(_),
            ..
        }) => return Err(named()),
        Some(after) => Some(match <[_; 1]>::try_from(after.items) {
            Ok([term]) => krs_ir::ProtocolHeadRuleResult::Replace(term),
            Err(items) if items.is_empty() => krs_ir::ProtocolHeadRuleResult::Erase,
            Err(items) => krs_ir::ProtocolHeadRuleResult::Splice(items),
        }),
    };
    Ok(krs_ir::ProtocolHeadRuleHead {
        items: before.items,
        exact,
        result,
    })
}

fn resolve_head_rule(
    rule: krs_ir::HostHeadRule,
    map: &mut Resolver<'_>,
) -> Result<krs_ir::DescriptorHeadRule, CollectionError> {
    let rule = readable_bracket_reading(rule, map.head_targets, map.declarations)?;
    let rule = readable_list_reading(rule, map.head_targets, map.declarations)?;
    let no_groups = HashMap::new();
    let target = select_head_rule_target(&rule, map.head_targets, map.declarations).ok();
    let rule = readable_group_terms(
        rule,
        &GroupRecords {
            declarations: map.declarations,
            children: target.map_or(&no_groups, |target| &target.group_children),
            cells: target.map_or(&[], |target| &target.cells),
        },
    );
    map.head_selection = Some(resolve_head_rule_target(
        &rule,
        map.head_targets,
        map.declarations,
    )?);
    let rule = rule.try_map_refs(map)?;
    let selection = map
        .head_selection
        .take()
        .expect("head-rule completion requires a selected configuration");
    let computation_cell =
        selection
            .computation
            .map(|computation| krs_ir::DescriptorCellReference {
                key: rule.pattern_key.clone(),
                cell: computation.identity.clone(),
            });
    Ok(krs_ir::DescriptorHeadRule::from_selected(
        rule,
        selection.target.configuration.clone(),
        computation_cell,
    ))
}

pub(super) fn resolve_payload(
    payload: &HostDescriptorPayload,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    context_aliases: &HashMap<HostItemId, StableItemId>,
    builtins: Option<&HostBuiltinRegistry>,
    head_targets: &[HeadRuleTarget],
) -> Result<DescriptorPayload, CollectionError> {
    let mut map = Resolver {
        declarations,
        cell_fields,
        context_aliases,
        builtins,
        head_targets,
        head_selection: None,
        allow_builtin_application: !matches!(payload, HostDescriptorPayload::Grammar(_)),
        parameters: sort_parameters(payload),
    };
    payload
        .clone()
        .try_map_refs(&mut map, &mut resolve_head_rule)
}

/// The sort parameters a parametric production's constructor or grammar
/// payload declares: each is a generated marker type, joined here by its
/// `TypeId` to the parameter's declared name (KF-027).
fn sort_parameters(payload: &HostDescriptorPayload) -> HashMap<TypeId, String> {
    let parameters = match payload {
        HostDescriptorPayload::Constructor(constructor) => constructor.parameters.as_slice(),
        HostDescriptorPayload::Grammar(grammar) => match grammar.as_ref() {
            krs_ir::HostGrammarDescriptor::Production(production) => {
                production.parameters.as_slice()
            }
            _ => &[],
        },
        _ => &[],
    };
    parameters
        .iter()
        .map(|parameter| {
            (
                parameter.target.key.resolve(),
                parameter.target.authored_path.trim().to_owned(),
            )
        })
        .collect()
}

fn resolve_cell_reference(
    reference: &krs_ir::HostCellReference,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
) -> Result<krs_ir::DescriptorCellReference, CollectionError> {
    let key = reference.cell.resolve();
    let cell = cell_fields.get(&key).cloned().ok_or_else(|| {
        CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "cell reference `{}#{}` has no selected owner/field-marker declaration",
                reference.key.role().as_str(),
                reference.key.ordinal()
            ),
        )
    })?;
    Ok(krs_ir::DescriptorCellReference {
        key: reference.key.clone(),
        cell,
    })
}

fn resolve_cell_declaration_reference(
    reference: &krs_ir::HostCellDeclarationReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<krs_ir::DescriptorCellDeclarationReference, CollectionError> {
    Ok(krs_ir::DescriptorCellDeclarationReference {
        key: reference.key.clone(),
        declaration: resolve_nominal_reference(
            &reference.declaration,
            ItemKind::Cell,
            declarations,
        )?,
    })
}

fn resolve_configuration_reference(
    reference: &krs_ir::HostConfigurationReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<krs_ir::DescriptorConfigurationReference, CollectionError> {
    Ok(krs_ir::DescriptorConfigurationReference {
        key: reference.key.clone(),
        configuration: resolve_nominal_reference(
            &reference.configuration,
            ItemKind::Configuration,
            declarations,
        )?,
    })
}

fn resolve_nominal_reference(
    reference: &HostTypeReference,
    expected: ItemKind,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<StableItemId, CollectionError> {
    resolve_declared_identity(
        HostApplicationIdentity::Nominal(reference.key.resolve()),
        &reference.authored_path,
        expected,
        declarations,
    )
}

fn resolve_constructor_field_sort(
    reference: &HostTypeReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<DescriptorSortRef, CollectionError> {
    let type_id = reference.key.resolve();
    if let Some((id, kind)) = declarations.get(&HostApplicationIdentity::Nominal(type_id)) {
        if *kind != ItemKind::Sort {
            return Err(CollectionError::new(
                CollectionErrorKind::ReferenceKindMismatch,
                format!(
                    "Rust path `{}` resolves to `{}`, but a sort is required",
                    reference.authored_path, id
                ),
            ));
        }
        Ok(DescriptorSortRef::Declared(id.clone()))
    } else if let Some(sort) = builtins.and_then(|registry| registry.resolve_sort(type_id)) {
        Ok(DescriptorSortRef::Builtin(sort))
    } else {
        Err(CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "Rust path `{}` resolves to neither a selected sort nor a registered builtin sort",
                reference.authored_path
            ),
        ))
    }
}

fn resolve_declared_identity(
    identity: HostApplicationIdentity,
    authored_path: &str,
    expected: ItemKind,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<StableItemId, CollectionError> {
    let Some((id, kind)) = declarations.get(&identity) else {
        return Err(CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "Rust path `{authored_path}` does not resolve to a selected KRS type declaration"
            ),
        ));
    };
    if *kind != expected {
        return Err(CollectionError::new(
            CollectionErrorKind::ReferenceKindMismatch,
            format!("Rust path `{authored_path}` resolves to `{id}`, but a {expected} is required"),
        ));
    }
    Ok(id.clone())
}

fn resolve_sort_reference(
    reference: &HostSortReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
) -> Result<DescriptorSortReference, CollectionError> {
    let type_id = reference.target.key.resolve();
    let sort = if let Some((id, kind)) =
        declarations.get(&HostApplicationIdentity::Nominal(type_id))
    {
        if *kind == ItemKind::Cell {
            // A whole-group binder is typed by its nested `#[k::cell]`
            // struct, whose K sort is the group's generated cell sort (KF-016).
            return Ok(DescriptorSortReference {
                key: reference.key.clone(),
                sort: DescriptorSortRef::Cell(id.clone()),
            });
        }
        if *kind != ItemKind::Sort {
            return Err(CollectionError::new(
                CollectionErrorKind::ReferenceKindMismatch,
                format!(
                    "Rust path `{}` resolves to `{}`, but a sort is required",
                    reference.target.authored_path, id
                ),
            ));
        }
        DescriptorSortRef::Declared(id.clone())
    } else if let Some(sort) = builtins.and_then(|registry| registry.resolve_sort(type_id)) {
        DescriptorSortRef::Builtin(sort)
    } else {
        return Err(CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "Rust path `{}` resolves to neither a selected sort nor a registered builtin sort",
                reference.target.authored_path
            ),
        ));
    };
    Ok(DescriptorSortReference {
        key: reference.key.clone(),
        sort,
    })
}

fn resolve_application_reference(
    reference: &krs_ir::HostApplicationReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    builtins: Option<&HostBuiltinRegistry>,
    allow_builtin: bool,
) -> Result<DescriptorApplicationReference, CollectionError> {
    let identity = reference.target.resolve();
    let application = if let Some((id, kind)) = declarations.get(&identity) {
        // A use of a named constant stays a reference to it until the
        // compiler substitutes the constant's value.
        if !matches!(kind, ItemKind::Constructor | ItemKind::Constant) {
            return Err(CollectionError::new(
                CollectionErrorKind::ReferenceKindMismatch,
                format!(
                    "Rust path `{}` resolves to `{}`, but a constructor or a constant is required",
                    reference.target.authored_path(),
                    id
                ),
            ));
        }
        DescriptorApplicationRef::Declared(id.clone())
    } else if allow_builtin {
        let HostApplicationIdentity::Nominal(type_id) = identity else {
            return Err(CollectionError::new(
                CollectionErrorKind::UnresolvedTypeReference,
                format!(
                    "enum-variant path `{}` has no selected constructor declaration",
                    reference.target.authored_path()
                ),
            ));
        };
        if let Some(operation) = builtins.and_then(|registry| registry.resolve_operation(type_id)) {
            DescriptorApplicationRef::Builtin(operation)
        } else if let Some(operation) =
            builtins.and_then(|registry| registry.resolve_map_operation(type_id))
        {
            DescriptorApplicationRef::Map(operation)
        } else if let Some(operation) =
            builtins.and_then(|registry| registry.resolve_list_operation(type_id))
        {
            DescriptorApplicationRef::List(operation)
        } else if let Some(operation) =
            builtins.and_then(|registry| registry.resolve_set_operation(type_id))
        {
            DescriptorApplicationRef::Set(operation)
        } else if let Some(connective) =
            builtins.and_then(|registry| registry.resolve_ml_connective(type_id))
        {
            DescriptorApplicationRef::Ml(connective)
        } else if let Some(operator) =
            builtins.and_then(|registry| registry.resolve_operator(type_id))
        {
            DescriptorApplicationRef::Operator(operator)
        } else if let Some(notation) =
            builtins.and_then(|registry| registry.resolve_list_notation(type_id))
        {
            DescriptorApplicationRef::ListNotation(notation)
        } else {
            return Err(CollectionError::new(
                CollectionErrorKind::UnresolvedTypeReference,
                format!(
                    "Rust path `{}` resolves to neither a selected constructor nor a registered term operation",
                    reference.target.authored_path()
                ),
            ));
        }
    } else {
        return Err(CollectionError::new(
            CollectionErrorKind::UnresolvedTypeReference,
            format!(
                "Rust path `{}` does not resolve to a selected constructor declaration",
                reference.target.authored_path()
            ),
        ));
    };
    Ok(DescriptorApplicationReference {
        key: reference.key.clone(),
        application,
    })
}

#[cfg(test)]
mod tests {
    use std::any::TypeId;

    use super::*;
    use krs_ir::{
        BuiltinSort, HostApplicationReference, HostApplicationTarget, HostEnumVariantReference,
        HostTypeKey, ListOperation, PackageId, ProvenanceKey, TermMapOperation,
    };

    struct Boolean;
    struct OtherBoolean;
    struct FalseMarker;
    /// One distinct Rust type per index, standing in for the facade's marker types.
    struct Marker<const N: usize>;

    macro_rules! marker_table {
        ($($index:literal)*) => {
            [$(marker_key::<Marker<$index>> as fn() -> TypeId),*]
        };
    }

    const MARKER_COUNT: usize = 192;

    fn marker_table() -> [fn() -> TypeId; MARKER_COUNT] {
        marker_table!(
            0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
            32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60
            61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89
            90 91 92 93 94 95 96 97 98 99 100 101 102 103 104 105 106 107 108 109 110 111 112 113
            114 115 116 117 118 119 120 121 122 123 124 125 126 127 128 129 130 131 132 133 134 135
            136 137 138 139 140 141 142 143 144 145 146 147 148 149 150 151 152 153 154 155 156 157
            158 159 160 161 162 163 164 165 166 167 168 169 170 171 172 173 174 175 176 177 178 179
            180 181 182 183 184 185 186 187 188 189 190 191
        )
    }

    fn marker_key<T: 'static>() -> TypeId {
        TypeId::of::<T>()
    }

    const SORT_OFFSET: usize = 0;
    const OPERATION_OFFSET: usize = SORT_OFFSET + BuiltinSort::ALL.len();
    const MAP_OFFSET: usize = OPERATION_OFFSET + krs_ir::BuiltinOperation::ALL.len();
    const LIST_OFFSET: usize = MAP_OFFSET + TermMapOperation::ALL.len();
    const SET_OFFSET: usize = LIST_OFFSET + ListOperation::ALL.len();
    const ML_OFFSET: usize = SET_OFFSET + krs_ir::SetOperation::ALL.len();
    const OPERATOR_OFFSET: usize = ML_OFFSET + krs_ir::MlConnective::ALL.len();
    const LIST_NOTATION_OFFSET: usize = OPERATOR_OFFSET + krs_ir::BuiltinOperator::ALL.len();
    const _: () = assert!(LIST_NOTATION_OFFSET + krs_ir::ListNotation::ALL.len() <= MARKER_COUNT);

    fn keys<const N: usize>(offset: usize) -> [HostTypeKey; N] {
        let table = marker_table();
        std::array::from_fn(|index| HostTypeKey(table[offset + index]))
    }

    fn position<T: PartialEq>(all: &[T], value: &T) -> usize {
        all.iter()
            .position(|candidate| candidate == value)
            .expect("catalog member")
    }

    fn sort_key(sort: BuiltinSort) -> HostTypeKey {
        HostTypeKey(marker_table()[SORT_OFFSET + position(&BuiltinSort::ALL, &sort)])
    }

    fn operation_key(operation: krs_ir::BuiltinOperation) -> HostTypeKey {
        HostTypeKey(
            marker_table()[OPERATION_OFFSET + position(&krs_ir::BuiltinOperation::ALL, &operation)],
        )
    }

    fn map_key(operation: TermMapOperation) -> HostTypeKey {
        HostTypeKey(marker_table()[MAP_OFFSET + position(&TermMapOperation::ALL, &operation)])
    }

    fn list_key(operation: ListOperation) -> HostTypeKey {
        HostTypeKey(marker_table()[LIST_OFFSET + position(&ListOperation::ALL, &operation)])
    }

    fn registry() -> HostBuiltinRegistry {
        HostBuiltinRegistry {
            sorts: keys(SORT_OFFSET),
            operations: keys(OPERATION_OFFSET),
            map_operations: keys(MAP_OFFSET),
            list_operations: keys(LIST_OFFSET),
            set_operations: keys(SET_OFFSET),
            ml_connectives: keys(ML_OFFSET),
            operators: keys(OPERATOR_OFFSET),
            list_notation: keys(LIST_NOTATION_OFFSET),
        }
    }

    fn boolean_key() -> TypeId {
        TypeId::of::<Boolean>()
    }

    fn other_boolean_key() -> TypeId {
        TypeId::of::<OtherBoolean>()
    }

    fn false_key() -> TypeId {
        TypeId::of::<FalseMarker>()
    }

    fn test_id(name: &str) -> StableItemId {
        StableItemId::new(
            PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap(),
            ["model"],
            name,
            ItemKind::Constructor,
            "enum:Boolean",
        )
        .unwrap()
    }

    fn unresolved_sort(path: &str) -> HostSortReference {
        HostSortReference {
            key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 0),
            target: HostTypeReference {
                key: HostTypeKey(other_boolean_key),
                authored_path: path.to_owned(),
            },
        }
    }

    fn unresolved_term(path: &str) -> krs_ir::HostTerm {
        krs_ir::HostTerm::Anonymous {
            key: ProvenanceKey::new(krs_ir::ProvenanceRole::RulePattern, 0),
            sort: unresolved_sort(path),
            spelling: "_".to_owned(),
        }
    }

    fn payload_error(
        payload: &HostDescriptorPayload,
        targets: &[HeadRuleTarget],
    ) -> CollectionError {
        resolve_payload(
            payload,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            None,
            targets,
        )
        .unwrap_err()
    }

    fn assert_sort_error(error: &CollectionError, path: &str) {
        assert_eq!(error.kind(), CollectionErrorKind::UnresolvedTypeReference);
        assert_eq!(
            error.detail(),
            format!(
                "Rust path `{path}` resolves to neither a selected sort nor a registered builtin sort"
            )
        );
    }

    #[test]
    fn production_resolves_items_and_attributes_before_result_sort() {
        let registry = registry();
        let owner_sort = HostSortReference {
            key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 0),
            target: HostTypeReference {
                key: sort_key(BuiltinSort::Int),
                authored_path: "Int".to_owned(),
            },
        };
        let mut production = krs_ir::HostProduction {
            parameters: Vec::new(),
            key: owner_sort.key.clone(),
            template_key: None,
            owner: krs_ir::HostProductionOwner::TokenSort { sort: owner_sort },
            result_sort: unresolved_sort("Result"),
            items: vec![krs_ir::HostProductionItem::NonTerminal {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 1),
                field_key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 2),
                declaration_key: None,
                field: krs_ir::ProductionFieldId::new("value").unwrap(),
                sort: Box::new(unresolved_sort("Item")),
            }],
            attributes: vec![krs_ir::HostProductionAttribute::Strictness {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 3),
                kind: krs_ir::StrictnessKind::Strict,
                using: None,
                fields: Vec::new(),
                result_sort: Box::new(unresolved_sort("Attribute")),
            }],
        };
        for path in ["Item", "Attribute", "Result"] {
            let error = resolve_payload(
                &HostDescriptorPayload::Grammar(Box::new(
                    krs_ir::HostGrammarDescriptor::Production(production.clone()),
                )),
                &HashMap::new(),
                &HashMap::new(),
                &HashMap::new(),
                Some(&registry),
                &[],
            )
            .unwrap_err();
            assert_sort_error(&error, path);
            if path == "Item" {
                production.items.clear();
            } else {
                production.attributes.clear();
            }
        }
    }

    #[test]
    fn production_owner_rejects_builtin_term_operations() {
        let registry = registry();
        let production = krs_ir::HostProduction {
            parameters: Vec::new(),
            key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 0),
            template_key: None,
            owner: krs_ir::HostProductionOwner::Constructor {
                constructor: HostApplicationReference {
                    key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 1),
                    target: HostApplicationTarget::Nominal(HostTypeReference {
                        key: operation_key(krs_ir::BuiltinOperation::IntAdd),
                        authored_path: "Add".to_owned(),
                    }),
                },
            },
            result_sort: unresolved_sort("Result"),
            items: Vec::new(),
            attributes: Vec::new(),
        };
        let error = resolve_payload(
            &HostDescriptorPayload::Grammar(Box::new(krs_ir::HostGrammarDescriptor::Production(
                production,
            ))),
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            Some(&registry),
            &[],
        )
        .unwrap_err();
        assert_eq!(error.kind(), CollectionErrorKind::UnresolvedTypeReference);
        assert_eq!(
            error.detail(),
            "Rust path `Add` does not resolve to a selected constructor declaration"
        );
    }

    fn unresolved_cell() -> krs_ir::HostCellReference {
        krs_ir::HostCellReference {
            key: ProvenanceKey::new(krs_ir::ProvenanceRole::ConfigurationField, 0),
            cell: krs_ir::HostCellIdentity {
                owner: HostTypeKey(boolean_key),
                field: HostTypeKey(false_key),
            },
        }
    }

    #[test]
    fn cell_declaration_resolves_content_before_field_identity() {
        let field = krs_ir::HostCellField {
            reference: unresolved_cell(),
            rust_field: "value".to_owned(),
            emitted_name: None,
            color: None,
            multiplicity: None,
            cell_type: None,
            stream: None,
            exit: None,
            initial: None,
            content: krs_ir::ProtocolCellContent::Leaf {
                wrapper_key: ProvenanceKey::new(krs_ir::ProvenanceRole::ConfigurationField, 1),
                wrapper: krs_ir::CellWrapper::Cell,
                sort: unresolved_sort("Content"),
                arguments: Vec::new(),
            },
        };
        let payload = HostDescriptorPayload::Cell(Box::new(krs_ir::HostCellDeclaration {
            key: ProvenanceKey::new(krs_ir::ProvenanceRole::ConfigurationField, 2),
            fields: vec![field],
        }));
        assert_sort_error(&payload_error(&payload, &[]), "Content");
    }

    #[test]
    fn initializer_resolves_content_before_field_identity() {
        let cell = krs_ir::HostInitializerCell {
            key: ProvenanceKey::new(krs_ir::ProvenanceRole::ConfigurationField, 0),
            field: unresolved_cell(),
            content: krs_ir::ProtocolInitializerCellContent::Leaf {
                constructor_key: ProvenanceKey::new(krs_ir::ProvenanceRole::ConfigurationField, 1),
                wrapper: krs_ir::CellWrapper::Cell,
                value: krs_ir::ProtocolInitializerStateTerm::Term(
                    krs_ir::ProtocolInitializerTerm {
                        key: ProvenanceKey::new(krs_ir::ProvenanceRole::ConfigurationField, 2),
                        term: unresolved_term("Content"),
                    },
                ),
            },
        };
        let declarations = HashMap::new();
        let fields = HashMap::new();
        let aliases = HashMap::new();
        let mut map = Resolver {
            parameters: HashMap::new(),
            declarations: &declarations,
            cell_fields: &fields,
            context_aliases: &aliases,
            builtins: None,
            head_targets: &[],
            head_selection: None,
            allow_builtin_application: true,
        };
        let error = cell
            .try_map_refs(
                &mut map,
                &mut |reference, map| map.cell(reference),
                &mut |reference, map| map.cell_declaration(reference),
                &mut |state, map| state.try_map_refs(map, &mut |term, map| term.try_map_refs(map)),
            )
            .unwrap_err();
        assert_sort_error(&error, "Content");
    }

    #[test]
    fn head_rule_resolves_target_extras_and_result_before_header_sort() {
        let key = ProvenanceKey::new(krs_ir::ProvenanceRole::RulePattern, 0);
        let mut rule = krs_ir::HostHeadRule {
            sentence_kind: krs_ir::SentenceKind::Transition,
            label: None,
            priority: None,
            nondet: None,
            pattern_key: key.clone(),
            result_key: key.clone(),
            head_sort: Some(unresolved_sort("Header")),
            configuration: None,
            computation_cell_name: None,
            bindings: Vec::new(),
            head: Some(krs_ir::ProtocolHeadRuleHead {
                items: vec![unresolved_term("Subject")],
                exact: false,
                result: Some(krs_ir::ProtocolHeadRuleResult::Replace(unresolved_term(
                    "Result",
                ))),
            }),
            requires: None,
            extras: vec![krs_ir::ProtocolHeadRuleExtra::HaveMap {
                cell: krs_ir::HostHeadRuleCellReference {
                    key,
                    name: "missing".to_owned(),
                },
                entries: vec![krs_ir::ProtocolHeadRuleMapEntry {
                    key: unresolved_term("Extra"),
                    value_binding: "value".to_owned(),
                }],
            }],
            existentials: Vec::new(),
            ensures: None,
            fresh: Vec::new(),
            evaluation: None,
            bracket_alternative: None,
            claim: None,
        };
        let identity = krs_ir::DescriptorCellIdentity {
            owner: StableItemId::new(
                PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap(),
                ["model"],
                "State",
                ItemKind::Configuration,
                "configuration",
            )
            .unwrap(),
            field: "k".to_owned(),
        };
        let target = HeadRuleTarget {
            configuration: identity.owner.clone(),
            cells: vec![HeadRuleCellTarget {
                identity,
                names: vec!["k".to_owned()],
                wrapper: Some(krs_ir::CellWrapper::KCell),
                collection: false,
                group: None,
            }],
            group_children: HashMap::new(),
        };
        let payload = |rule| HostDescriptorPayload::HeadRule(Box::new(rule));
        let error = payload_error(&payload(rule.clone()), &[]);
        assert_eq!(error.kind(), CollectionErrorKind::ConfigurationCount);
        assert!(
            error
                .detail()
                .contains("but the definition has no `#[k::configuration]`"),
            "{}",
            error.detail()
        );
        let targets = [target];
        let error = payload_error(&payload(rule.clone()), &targets);
        assert_eq!(error.kind(), CollectionErrorKind::InvalidConfiguration);
        assert_eq!(
            error.detail(),
            "readable rule extra names no fixed leaf cell `missing`"
        );
        rule.extras.clear();
        assert_sort_error(&payload_error(&payload(rule.clone()), &targets), "Result");
        let head = rule.head.as_mut().unwrap();
        head.result = Some(krs_ir::ProtocolHeadRuleResult::Erase);
        assert_sort_error(&payload_error(&payload(rule.clone()), &targets), "Subject");
        rule.head.as_mut().unwrap().items = vec![krs_ir::HostTerm::Wildcard {
            key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleLeftWildcard, 0),
        }];
        assert_sort_error(&payload_error(&payload(rule), &targets), "Header");
    }

    #[test]
    fn enum_variant_join_uses_owner_and_marker_identity_not_alias_spelling() {
        let false_id = test_id("False");
        let identity = HostApplicationIdentity::EnumVariant {
            enum_type: boolean_key(),
            variant: false_key(),
        };
        let declarations = HashMap::from([(identity, (false_id.clone(), ItemKind::Constructor))]);
        let target = HostEnumVariantReference::new(
            HostTypeReference {
                key: HostTypeKey(boolean_key),
                authored_path: "Alias".into(),
            },
            HostTypeKey(false_key),
            "Alias::RenamedFalse",
        )
        .unwrap();
        let resolved = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightReference, 0),
                target: HostApplicationTarget::EnumVariant(target),
            },
            &declarations,
            None,
            false,
        )
        .unwrap();
        assert_eq!(
            resolved.application,
            DescriptorApplicationRef::Declared(false_id)
        );

        let wrong_owner = HostEnumVariantReference::new(
            HostTypeReference {
                key: HostTypeKey(other_boolean_key),
                authored_path: "OtherAlias".into(),
            },
            HostTypeKey(false_key),
            "OtherAlias::RenamedFalse",
        )
        .unwrap();
        let error = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightReference, 0),
                target: HostApplicationTarget::EnumVariant(wrong_owner),
            },
            &declarations,
            None,
            false,
        )
        .unwrap_err();
        assert_eq!(error.kind(), CollectionErrorKind::UnresolvedTypeReference);
    }

    #[test]
    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustively verifies sort and operation alias identity."
    )]
    fn complete_builtin_registry_joins_aliases_by_exact_type_identity() {
        let registry = registry();
        registry.validate().unwrap();
        let sort = resolve_sort_reference(
            &HostSortReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 0),
                target: HostTypeReference {
                    key: sort_key(BuiltinSort::Int),
                    authored_path: "RenamedInt".into(),
                },
            },
            &HashMap::new(),
            Some(&registry),
        )
        .unwrap();
        assert_eq!(sort.sort, DescriptorSortRef::Builtin(BuiltinSort::Int));

        let bytes_sort = resolve_sort_reference(
            &HostSortReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 1),
                target: HostTypeReference {
                    key: sort_key(BuiltinSort::Bytes),
                    authored_path: "RenamedBytes".into(),
                },
            },
            &HashMap::new(),
            Some(&registry),
        )
        .unwrap();
        assert_eq!(
            bytes_sort.sort,
            DescriptorSortRef::Builtin(BuiltinSort::Bytes)
        );

        let application = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightApplicationHead, 0),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: operation_key(krs_ir::BuiltinOperation::IntAdd),
                    authored_path: "RenamedAdd".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap();
        assert_eq!(
            application.application,
            DescriptorApplicationRef::Builtin(krs_ir::BuiltinOperation::IntAdd)
        );

        let integer_modulus = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightApplicationHead, 1),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: operation_key(krs_ir::BuiltinOperation::IntMod),
                    authored_path: "RenamedModulus".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap();
        assert_eq!(
            integer_modulus.application,
            DescriptorApplicationRef::Builtin(krs_ir::BuiltinOperation::IntMod)
        );

        let map_update = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightApplicationHead, 0),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: map_key(TermMapOperation::Update),
                    authored_path: "persistent_update".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap();
        assert_eq!(
            map_update.application,
            DescriptorApplicationRef::Map(TermMapOperation::Update)
        );

        let list_get = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightApplicationHead, 1),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: list_key(ListOperation::Get),
                    authored_path: "indexed_lookup".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap();
        assert_eq!(
            list_get.application,
            DescriptorApplicationRef::List(ListOperation::Get)
        );

        let lookalike = resolve_application_reference(
            &HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleRightApplicationHead, 0),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: HostTypeKey(marker_key::<OtherBoolean>),
                    authored_path: "map::update".into(),
                }),
            },
            &HashMap::new(),
            Some(&registry),
            true,
        )
        .unwrap_err();
        assert_eq!(
            lookalike.kind(),
            CollectionErrorKind::UnresolvedTypeReference
        );
    }

    #[test]
    fn constructor_field_sort_preserves_builtin_identity_and_rejects_lookalikes() {
        let registry = registry();
        let builtin = resolve_constructor_field_sort(
            &HostTypeReference {
                key: sort_key(BuiltinSort::Id),
                authored_path: "RenamedId".into(),
            },
            &HashMap::new(),
            Some(&registry),
        )
        .unwrap();
        assert_eq!(builtin, DescriptorSortRef::Builtin(BuiltinSort::Id));

        let error = resolve_constructor_field_sort(
            &HostTypeReference {
                key: HostTypeKey(marker_key::<OtherBoolean>),
                authored_path: "BuiltinLookingButUnregistered".into(),
            },
            &HashMap::new(),
            Some(&registry),
        )
        .unwrap_err();
        assert_eq!(error.kind(), CollectionErrorKind::UnresolvedTypeReference);
        assert!(
            error
                .to_string()
                .contains("neither a selected sort nor a registered builtin sort")
        );
    }

    fn cell_id(name: &str) -> StableItemId {
        StableItemId::new(
            PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap(),
            ["model"],
            name,
            ItemKind::Cell,
            "",
        )
        .unwrap()
    }

    /// `Frame` and `Outer` as `#[k::cell]` structs and `Pair` as a
    /// constructor.
    fn group_declarations() -> HashMap<HostApplicationIdentity, (StableItemId, ItemKind)> {
        HashMap::from([
            (
                HostApplicationIdentity::Nominal(boolean_key()),
                (cell_id("Frame"), ItemKind::Cell),
            ),
            (
                HostApplicationIdentity::Nominal(false_key()),
                (cell_id("Outer"), ItemKind::Cell),
            ),
            (
                HostApplicationIdentity::Nominal(other_boolean_key()),
                (test_id("Pair"), ItemKind::Constructor),
            ),
        ])
    }

    /// `Frame` has two children, and `Outer` two: the group `frame` and a
    /// leaf, so a record naming one leaves the other out.
    fn group_children() -> HashMap<TypeId, GroupChildren> {
        HashMap::from([
            (
                boolean_key(),
                GroupChildren {
                    count: 2,
                    fixed: HashMap::new(),
                },
            ),
            (
                false_key(),
                GroupChildren {
                    count: 2,
                    fixed: HashMap::from([("frame".to_owned(), boolean_key())]),
                },
            ),
        ])
    }

    /// A readable record of the struct `key` naming one field.
    fn one_field_record(
        key: fn() -> TypeId,
        field: &str,
        value: krs_ir::HostTerm,
    ) -> krs_ir::HostTerm {
        krs_ir::HostTerm::Application {
            head_class: krs_ir::DescriptorApplicationHeadClass::Applied,
            reference: HostApplicationReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleLeftApplicationHead, 3),
                target: HostApplicationTarget::Nominal(HostTypeReference {
                    key: HostTypeKey(key),
                    authored_path: "Frame".into(),
                }),
            },
            path_key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleLeftPath, 3),
            arguments: krs_ir::Arguments::named(vec![krs_ir::NamedTermArgument {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleLeftRecordFieldName, 1),
                field: krs_ir::ProductionFieldId::new(field).unwrap(),
                value: Box::new(value),
            }]),
            instance: Vec::new(),
            update: None,
            open: false,
        }
    }

    fn frame_record() -> krs_ir::HostTerm {
        one_field_record(boolean_key, "pc", unresolved_term("p"))
    }

    #[test]
    fn readable_record_naming_a_cell_struct_becomes_a_group_term() {
        let declarations = group_declarations();
        let children = group_children();
        let record = one_field_record;
        let frame = frame_record;
        let groups = GroupRecords {
            declarations: &declarations,
            children: &children,
            cells: &[],
        };
        // At the group's own position, a subject record leaves the child it
        // does not name unconstrained; a result names every child.
        let krs_ir::HostTerm::Cell {
            key,
            declaration,
            fields,
            open,
            update,
        } = readable_group_term(frame(), true, Some(boolean_key()), &groups)
        else {
            panic!("a record naming a cell struct is a group term");
        };
        assert!(open && update.is_none());
        assert!(matches!(
            readable_group_term(frame(), false, Some(boolean_key()), &groups),
            krs_ir::HostTerm::Cell { open: false, .. }
        ));
        assert_eq!(
            key,
            ProvenanceKey::new(krs_ir::ProvenanceRole::RuleLeftApplicationHead, 3)
        );
        assert_eq!(declaration.key.resolve(), boolean_key());
        assert_eq!(fields.len(), 1);
        assert_eq!(
            fields[0].key,
            ProvenanceKey::new(krs_ir::ProvenanceRole::RuleLeftRecordFieldName, 1)
        );
        assert!(matches!(
            readable_group_term(
                record(other_boolean_key, "pc", unresolved_term("p")),
                true,
                Some(boolean_key()),
                &groups
            ),
            krs_ir::HostTerm::Application { .. }
        ));
    }

    #[test]
    fn a_group_record_omits_children_only_at_its_configuration_position() {
        let declarations = group_declarations();
        let children = group_children();
        let record = one_field_record;
        let frame = frame_record;
        let groups = GroupRecords {
            declarations: &declarations,
            children: &children,
            cells: &[],
        };
        // Anywhere else, such as a leaf cell's content, the record is a
        // complete value: closed unless it ends in `..`.
        assert!(matches!(
            readable_group_term(frame(), true, None, &groups),
            krs_ir::HostTerm::Cell { open: false, .. }
        ));
        let mut rest = frame();
        if let krs_ir::HostTerm::Application { open, .. } = &mut rest {
            *open = true;
        }
        assert!(matches!(
            readable_group_term(rest, true, None, &groups),
            krs_ir::HostTerm::Cell { open: true, .. }
        ));
        // A fixed group child of a record at its position is at its own
        // group's position; the child of a value record is left to the
        // strict reading of values.
        let nested = |position| {
            let krs_ir::HostTerm::Cell { fields, .. } =
                readable_group_term(record(false_key, "frame", frame()), true, position, &groups)
            else {
                panic!("the outer record is a group term");
            };
            fields.into_iter().next().unwrap().value
        };
        assert!(matches!(
            *nested(Some(false_key())),
            krs_ir::HostTerm::Cell { open: true, .. }
        ));
        assert!(matches!(
            *nested(None),
            krs_ir::HostTerm::Application { .. }
        ));
        assert!(matches!(
            readable_group_term(
                record(other_boolean_key, "pc", unresolved_term("p")),
                true,
                Some(boolean_key()),
                &groups
            ),
            krs_ir::HostTerm::Application { .. }
        ));
    }
}

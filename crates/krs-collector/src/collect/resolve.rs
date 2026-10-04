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
                ItemKind::Sort | ItemKind::Constructor | ItemKind::Configuration | ItemKind::Cell
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
        if !matches!(
            kind,
            ItemKind::Sort | ItemKind::Constructor | ItemKind::Configuration | ItemKind::Cell
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
                || registry.resolve_set_operation(type_id).is_some())
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
            | HostDescriptorPayload::ContextAlias(_) => continue,
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
    wrapper: krs_ir::CellWrapper,
}

#[derive(Clone, Debug)]
pub(super) struct HeadRuleTarget {
    configuration: StableItemId,
    cells: Vec<HeadRuleCellTarget>,
}

struct HeadRuleSelection<'a> {
    target: &'a HeadRuleTarget,
    computation: &'a HeadRuleCellTarget,
}

fn collect_head_rule_cells(
    declaration: &krs_ir::HostCellDeclaration,
    declarations: &HashMap<TypeId, &krs_ir::HostCellDeclaration>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    visiting: &mut HashSet<TypeId>,
    cells: &mut Vec<HeadRuleCellTarget>,
) -> Result<(), CollectionError> {
    for field in &declaration.fields {
        match &field.content {
            krs_ir::ProtocolCellContent::Leaf { wrapper, .. } => {
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
                let mut names = vec![field.rust_field.clone()];
                if let Some(emitted) = &field.emitted_name
                    && !names.contains(&emitted.value)
                {
                    names.push(emitted.value.clone());
                }
                cells.push(HeadRuleCellTarget {
                    identity,
                    names,
                    wrapper: *wrapper,
                });
            }
            krs_ir::ProtocolCellContent::Nested { declaration } => {
                let key = declaration.declaration.key.resolve();
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
                collect_head_rule_cells(nested, declarations, cell_fields, visiting, cells)?;
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
    let has_implicit_target = pending.iter().any(|descriptor| {
        matches!(
            &descriptor.host.payload,
            HostDescriptorPayload::HeadRule(rule) if rule.configuration.is_none()
        )
    });
    if has_implicit_target && configurations.len() != 1 {
        let detail = match configurations.len() {
            0 => "a `for Sort` rule requires one fixed configuration, but none was collected"
                .to_owned(),
            count => format!(
                "a `for Sort` rule requires one unambiguous fixed configuration, but {count} candidates were collected"
            ),
        };
        return Err(CollectionError::new(
            CollectionErrorKind::InvalidConfiguration,
            detail,
        ));
    }
    let targets = configurations
        .into_iter()
        .map(|(descriptor, configuration)| {
            let mut cells = Vec::new();
            collect_head_rule_cells(
                &configuration.declaration,
                &cell_declarations,
                cell_fields,
                &mut HashSet::new(),
                &mut cells,
            )?;
            Ok(HeadRuleTarget {
                configuration: descriptor.id.clone(),
                cells,
            })
        })
        .collect::<Result<Vec<_>, CollectionError>>()?;
    if has_implicit_target {
        let computations = targets[0]
            .cells
            .iter()
            .filter(|cell| cell.wrapper == krs_ir::CellWrapper::KCell)
            .count();
        if computations != 1 {
            let detail = match computations {
                0 => "selected fixed configuration has no matching top-level KCell<KSequence> computation cell"
                    .to_owned(),
                count => format!(
                    "selected fixed configuration has {count} matching top-level KCell<KSequence> computation cells"
                ),
            };
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                detail,
            ));
        }
    }
    Ok(targets)
}

fn resolve_head_rule_target<'a>(
    rule: &krs_ir::HostHeadRule,
    targets: &'a [HeadRuleTarget],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<HeadRuleSelection<'a>, CollectionError> {
    let target = if let Some(configuration) = &rule.configuration {
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
            let detail = match targets.len() {
                0 => "head-anchored rules require one fixed configuration, but none was collected"
                    .to_owned(),
                count => format!(
                    "a `for Sort` rule requires one unambiguous fixed configuration, but {count} candidates were collected; use a configuration-owned cell-record rule where appropriate"
                ),
            };
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidConfiguration,
                detail,
            ));
        };
        target
    };
    let computations = target
        .cells
        .iter()
        .filter(|cell| {
            cell.wrapper == krs_ir::CellWrapper::KCell
                && rule
                    .computation_cell_name
                    .as_ref()
                    .is_none_or(|name| cell.names.iter().any(|candidate| candidate == name))
        })
        .collect::<Vec<_>>();
    let [computation] = computations.as_slice() else {
        let detail = match computations.len() {
            0 => "selected fixed configuration has no matching top-level KCell<KSequence> computation cell"
                .to_owned(),
            count => format!(
                "selected fixed configuration has {count} matching top-level KCell<KSequence> computation cells"
            ),
        };
        return Err(CollectionError::new(
            CollectionErrorKind::InvalidConfiguration,
            detail,
        ));
    };
    Ok(HeadRuleSelection {
        target,
        computation,
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
    parent_ordinal: u32,
    field_ordinal: u32,
}

impl RefMap<HostStage, DescriptorStage> for Resolver<'_> {
    type Error = CollectionError;

    fn sort(
        &mut self,
        reference: HostSortReference,
    ) -> Result<DescriptorSortReference, Self::Error> {
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
        if resolved.identity == selection.computation.identity {
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

    fn parent(&mut self, reference: HostTypeReference) -> Result<StableItemId, Self::Error> {
        let key = krs_ir::ProvenanceRole::SortParent.key(self.parent_ordinal);
        self.parent_ordinal += 1;
        resolve_nominal_reference(&reference, ItemKind::Sort, self.declarations)
            .map_err(|error| error.with_reference_key(key))
    }

    fn constructor_sort(
        &mut self,
        reference: HostSortReference,
    ) -> Result<DescriptorSortRef, Self::Error> {
        Ok(self.sort(reference)?.sort)
    }

    fn constructor_field_sort(
        &mut self,
        reference: HostTypeReference,
    ) -> Result<Option<DescriptorSortRef>, Self::Error> {
        let key = krs_ir::ProvenanceRole::ConstructorFieldSort.key(self.field_ordinal);
        self.field_ordinal += 1;
        resolve_constructor_field_sort(&reference, self.declarations, self.builtins)
            .map(Some)
            .map_err(|error| error.with_reference_key(key))
    }
}

fn resolve_head_rule(
    rule: krs_ir::HostHeadRule,
    map: &mut Resolver<'_>,
) -> Result<krs_ir::DescriptorHeadRule, CollectionError> {
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
    let computation_cell = krs_ir::DescriptorCellReference {
        key: rule.pattern_key.clone(),
        cell: selection.computation.identity.clone(),
    };
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
        parent_ordinal: 0,
        field_ordinal: 0,
    };
    payload
        .clone()
        .try_map_refs(&mut map, &mut resolve_head_rule)
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
        if *kind != ItemKind::Constructor {
            return Err(CollectionError::new(
                CollectionErrorKind::ReferenceKindMismatch,
                format!(
                    "Rust path `{}` resolves to `{}`, but a constructor is required",
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
    struct SortK;
    struct SortInt;
    struct SortBool;
    struct SortMap;
    struct SortId;
    struct SortBytes;
    struct SortString;
    struct SortList;
    struct SortSet;
    struct Op0;
    struct Op1;
    struct Op2;
    struct Op3;
    struct Op4;
    struct Op5;
    struct Op6;
    struct Op7;
    struct Op8;
    struct Op9;
    struct Op10;
    struct Op11;
    struct Op12;
    struct Op13;
    struct Op14;
    struct Op15;
    struct Op16;
    struct Op17;
    struct Op18;
    struct Op19;
    struct Op20;
    struct Op21;
    struct Op22;
    struct Op23;
    struct Op24;
    struct Op25;
    struct Op26;
    struct Op27;
    struct Op28;
    struct MapUpdateOp;
    struct MapGetOp;
    struct MapInKeysOp;
    struct ListOp0;
    struct ListOp1;
    struct ListOp2;
    struct ListOp3;
    struct ListOp4;
    struct ListOp5;
    struct ListOp6;
    struct ListOp7;
    struct ListOp8;
    struct SetOp0;
    struct SetOp1;
    struct SetOp2;
    struct SetOp3;
    struct SetOp4;

    fn marker_key<T: 'static>() -> TypeId {
        TypeId::of::<T>()
    }

    fn registry() -> HostBuiltinRegistry {
        let sort_keys = [
            HostTypeKey(marker_key::<SortK>),
            HostTypeKey(marker_key::<SortInt>),
            HostTypeKey(marker_key::<SortBool>),
            HostTypeKey(marker_key::<SortMap>),
            HostTypeKey(marker_key::<SortId>),
            HostTypeKey(marker_key::<SortBytes>),
            HostTypeKey(marker_key::<SortString>),
            HostTypeKey(marker_key::<SortList>),
            HostTypeKey(marker_key::<SortSet>),
        ];
        let operation_keys = [
            HostTypeKey(marker_key::<Op0>),
            HostTypeKey(marker_key::<Op1>),
            HostTypeKey(marker_key::<Op2>),
            HostTypeKey(marker_key::<Op3>),
            HostTypeKey(marker_key::<Op4>),
            HostTypeKey(marker_key::<Op5>),
            HostTypeKey(marker_key::<Op6>),
            HostTypeKey(marker_key::<Op7>),
            HostTypeKey(marker_key::<Op8>),
            HostTypeKey(marker_key::<Op9>),
            HostTypeKey(marker_key::<Op10>),
            HostTypeKey(marker_key::<Op11>),
            HostTypeKey(marker_key::<Op12>),
            HostTypeKey(marker_key::<Op13>),
            HostTypeKey(marker_key::<Op14>),
            HostTypeKey(marker_key::<Op15>),
            HostTypeKey(marker_key::<Op16>),
            HostTypeKey(marker_key::<Op17>),
            HostTypeKey(marker_key::<Op18>),
            HostTypeKey(marker_key::<Op19>),
            HostTypeKey(marker_key::<Op20>),
            HostTypeKey(marker_key::<Op21>),
            HostTypeKey(marker_key::<Op22>),
            HostTypeKey(marker_key::<Op23>),
            HostTypeKey(marker_key::<Op24>),
            HostTypeKey(marker_key::<Op25>),
            HostTypeKey(marker_key::<Op26>),
            HostTypeKey(marker_key::<Op27>),
            HostTypeKey(marker_key::<Op28>),
        ];
        HostBuiltinRegistry {
            sorts: sort_keys,
            operations: operation_keys,
            map_operations: [
                HostTypeKey(marker_key::<MapUpdateOp>),
                HostTypeKey(marker_key::<MapGetOp>),
                HostTypeKey(marker_key::<MapInKeysOp>),
            ],
            list_operations: [
                HostTypeKey(marker_key::<ListOp0>),
                HostTypeKey(marker_key::<ListOp1>),
                HostTypeKey(marker_key::<ListOp2>),
                HostTypeKey(marker_key::<ListOp3>),
                HostTypeKey(marker_key::<ListOp4>),
                HostTypeKey(marker_key::<ListOp5>),
                HostTypeKey(marker_key::<ListOp6>),
                HostTypeKey(marker_key::<ListOp7>),
                HostTypeKey(marker_key::<ListOp8>),
            ],
            set_operations: [
                HostTypeKey(marker_key::<SetOp0>),
                HostTypeKey(marker_key::<SetOp1>),
                HostTypeKey(marker_key::<SetOp2>),
                HostTypeKey(marker_key::<SetOp3>),
                HostTypeKey(marker_key::<SetOp4>),
            ],
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
                key: HostTypeKey(marker_key::<SortInt>),
                authored_path: "Int".to_owned(),
            },
        };
        let mut production = krs_ir::HostProduction {
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
            key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 0),
            template_key: None,
            owner: krs_ir::HostProductionOwner::Constructor {
                constructor: HostApplicationReference {
                    key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 1),
                    target: HostApplicationTarget::Nominal(HostTypeReference {
                        key: HostTypeKey(marker_key::<Op0>),
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
            declarations: &declarations,
            cell_fields: &fields,
            context_aliases: &aliases,
            builtins: None,
            head_targets: &[],
            head_selection: None,
            allow_builtin_application: true,
            parent_ordinal: 0,
            field_ordinal: 0,
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
            pattern_key: key.clone(),
            result_key: key.clone(),
            head_sort: Some(unresolved_sort("Header")),
            configuration: None,
            computation_cell_name: None,
            bindings: Vec::new(),
            subject: unresolved_term("Subject"),
            result: krs_ir::ProtocolHeadRuleResult::Replace(unresolved_term("Result")),
            requires: None,
            extras: vec![krs_ir::ProtocolHeadRuleExtra::HaveMap {
                cell: krs_ir::HostHeadRuleCellReference {
                    key,
                    name: "missing".to_owned(),
                },
                key: unresolved_term("Extra"),
                value_binding: "value".to_owned(),
            }],
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
                wrapper: krs_ir::CellWrapper::KCell,
            }],
        };
        let payload = |rule| HostDescriptorPayload::HeadRule(Box::new(rule));
        let error = payload_error(&payload(rule.clone()), &[]);
        assert_eq!(error.kind(), CollectionErrorKind::InvalidConfiguration);
        assert_eq!(
            error.detail(),
            "head-anchored rules require one fixed configuration, but none was collected"
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
        rule.result = krs_ir::ProtocolHeadRuleResult::Erase;
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
    #[allow(clippy::too_many_lines)] // Exhaustively verifies sort and operation alias identity.
    fn complete_builtin_registry_joins_aliases_by_exact_type_identity() {
        let registry = registry();
        registry.validate().unwrap();
        let sort = resolve_sort_reference(
            &HostSortReference {
                key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleType, 0),
                target: HostTypeReference {
                    key: HostTypeKey(marker_key::<SortInt>),
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
                    key: HostTypeKey(marker_key::<SortBytes>),
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
                    key: HostTypeKey(marker_key::<Op0>),
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
                    key: HostTypeKey(marker_key::<Op4>),
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
                    key: HostTypeKey(marker_key::<MapUpdateOp>),
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
                    key: HostTypeKey(marker_key::<ListOp3>),
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
                key: HostTypeKey(marker_key::<SortId>),
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
}

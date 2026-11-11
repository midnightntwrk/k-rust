//! Resolution of host descriptor payloads against the declared items of the selected packages.

use std::any::TypeId;
use std::collections::{BTreeSet, HashMap, HashSet};

use krs_ir::cell_kind::{CellKind, CellView, Content, Layer, Multiplicity, Notation, Order};
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

pub(super) type HostCellKey = (TypeId, TypeId);

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
    /// The cell's K name: its emitted name, else its Rust field's.
    k_name: String,
    /// The cell's own layers, read from its declaration
    /// ([`krs_ir::cell_kind::CellKind::of`] over [`HostCell`]): presence or instances (KF-023),
    /// then a computation, a leaf, or a group, which a readable record names as a whole (KF-016).
    kind: CellKind,
    /// The layers its `?` and `*` ancestors put above it, outermost first
    /// ([`CellKind::path`]): what an entry naming the cell at a record's level is judged against
    /// before its own layers (S1 (b)).
    path: CellKind,
    /// The `#[k::cell]` struct of a nested (group) cell, by its resolved
    /// type: a record in the entry that names the cell stands for the
    /// running configuration's cell of that group (U5).
    group: Option<TypeId>,
    /// Its outermost `?` or `*` ancestor, which an entry naming the cell at a record's level is
    /// refused for: what the refusal's advice writes the entry inside.
    ancestor: Option<MarkedAncestor>,
    /// A leaf's sort as its declaration names it (`Int`), which a refusal's reason names.
    sort: Option<String>,
    /// The index of the enclosing group cell among the configuration's cells, absent for a
    /// top-level cell of the configuration.
    parent: Option<usize>,
    /// The `#[k::cell]` declaration a group cell holds.
    group_id: Option<StableItemId>,
}

/// A cell's outermost `?` or `*` ancestor, as a refusal of an entry naming the cell below it
/// advises writing the entry: inside the ancestor's presence or instance record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct MarkedAncestor {
    /// The ancestor's field name, as a readable record names it.
    pub(super) name: String,
    /// Its mark's layer: `?` or `*` (with its order).
    pub(super) layer: Layer,
    /// Its group's struct name, the head of its record.
    pub(super) group: String,
    /// Whether the cell is a child of the ancestor's own group, which a record of that group
    /// names directly.
    pub(super) direct: bool,
}

fn head_rule_cell_target(
    field: &HostCell<'_>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    group: Option<TypeId>,
    path: &[Layer],
    ancestor: Option<&MarkedAncestor>,
) -> Result<HeadRuleCellTarget, CollectionError> {
    let kind = CellKind::of(field);
    let field = field.field;
    let sort = match &field.content {
        krs_ir::ProtocolCellContent::Leaf { sort, .. } => {
            let path = &sort.target.authored_path;
            Some(path.rsplit("::").next().unwrap_or(path).trim().to_owned())
        }
        krs_ir::ProtocolCellContent::Nested { .. } => None,
    };
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
    let k_name = field
        .emitted_name
        .as_ref()
        .map_or_else(|| field.rust_field.clone(), |name| name.value.clone());
    Ok(HeadRuleCellTarget {
        identity,
        names,
        k_name,
        kind,
        path: CellKind {
            layers: path.to_vec(),
        },
        group,
        ancestor: ancestor.cloned(),
        sort,
        parent: None,
        group_id: None,
    })
}

impl HeadRuleCellTarget {
    /// Whether the cell is a `multiplicity = "*"` collection (KF-023).
    fn is_collection(&self) -> bool {
        matches!(self.kind.multiplicity(), Multiplicity::Many(_))
    }

    /// The wrapper of a cell that is no collection: a computation's `KCell`, a leaf's `Cell`;
    /// none for a group or a collection.
    fn leaf_wrapper(&self) -> Option<krs_ir::CellWrapper> {
        if self.is_collection() {
            return None;
        }
        match self.kind.content() {
            Some(Layer::Computation) => Some(krs_ir::CellWrapper::KCell),
            Some(Layer::Leaf(_)) => Some(krs_ir::CellWrapper::Cell),
            _ => None,
        }
    }
}

/// What a [`HostCell`] reads beside its field: the nested declarations by their resolved type,
/// and which sorts have notation of their own.
pub(super) struct HostCellDeclarations<'a> {
    /// Each nested `#[k::cell]` struct by its resolved type, with its descriptor identity.
    nested: HashMap<TypeId, (&'a StableItemId, &'a krs_ir::HostCellDeclaration)>,
    builtins: Option<&'a HostBuiltinRegistry>,
    /// The resolved types of the declared sorts some production makes a cons list.
    cons_lists: HashSet<TypeId>,
}

impl<'a> HostCellDeclarations<'a> {
    pub(super) fn new(
        pending: &'a [PendingDescriptor],
        builtins: Option<&'a HostBuiltinRegistry>,
    ) -> Self {
        let nested = pending
            .iter()
            .filter_map(|descriptor| {
                let HostDescriptorPayload::Cell(declaration) = &descriptor.host.payload else {
                    return None;
                };
                let Some(krs_ir::HostDeclarationIdentity::Nominal(key)) =
                    descriptor.host.declared_type
                else {
                    return None;
                };
                Some((key.resolve(), (&descriptor.id, declaration.as_ref())))
            })
            .collect();
        let cons_lists = pending
            .iter()
            .filter_map(|descriptor| match &descriptor.host.payload {
                HostDescriptorPayload::Grammar(grammar) => {
                    krs_ir::cell_kind::cons_list_sort(grammar)
                }
                _ => None,
            })
            .map(|sort| sort.target.key.resolve())
            .collect();
        Self {
            nested,
            builtins,
            cons_lists,
        }
    }

    /// The view of `field`.
    pub(super) const fn cell(&'a self, field: &'a krs_ir::HostCellField) -> HostCell<'a> {
        HostCell {
            field,
            declarations: self,
            ancestors: Vec::new(),
        }
    }
}

/// A host cell field read as a [`CellView`]: the collector's declaration of the cell, resolved
/// by Rust types before the descriptors are. A nested group's declaration is the collected
/// `#[k::cell]` struct of its resolved type; a leaf's notation is its sort's (the builtin
/// `List`, `Map` and `Set` by their registered markers, or a declared cons list); the
/// computation is a `KCell`'s content, as [`krs_ir::cell_kind::DescriptorCell`] reads the same
/// field once collected. A missing nested declaration, or one of the cell's own ancestors (a
/// cycle, which collection refuses), reads as a group with no children.
#[derive(Clone)]
pub(super) struct HostCell<'a> {
    field: &'a krs_ir::HostCellField,
    declarations: &'a HostCellDeclarations<'a>,
    ancestors: Vec<TypeId>,
}

impl CellView for HostCell<'_> {
    fn name(&self) -> String {
        let field = &self.field.rust_field;
        field.strip_prefix("r#").unwrap_or(field).to_owned()
    }

    fn multiplicity(&self) -> Multiplicity {
        krs_ir::cell_kind::declared_multiplicity(
            self.field
                .multiplicity
                .as_ref()
                .map(|multiplicity| multiplicity.value.as_str()),
            self.field
                .cell_type
                .as_ref()
                .map(|cell_type| cell_type.value.into()),
        )
    }

    fn content(&self) -> Content<Self> {
        match &self.field.content {
            krs_ir::ProtocolCellContent::Leaf {
                wrapper: krs_ir::CellWrapper::KCell,
                ..
            } => Content::Computation,
            krs_ir::ProtocolCellContent::Leaf { sort, .. } => {
                let target = sort.target.key.resolve();
                Content::Leaf(
                    match self
                        .declarations
                        .builtins
                        .and_then(|builtins| builtins.resolve_sort(target))
                    {
                        Some(builtin) => krs_ir::cell_kind::builtin_notation(builtin),
                        None if self.declarations.cons_lists.contains(&target) => Notation::Cons,
                        None => Notation::Plain,
                    },
                )
            }
            krs_ir::ProtocolCellContent::Nested { declaration } => {
                let key = declaration.declaration.key.resolve();
                let nested = self.declarations.nested.get(&key);
                let children = match nested {
                    Some((_, nested)) if !self.ancestors.contains(&key) => {
                        let mut ancestors = self.ancestors.clone();
                        ancestors.push(key);
                        nested
                            .fields
                            .iter()
                            .map(|field| Self {
                                field,
                                declarations: self.declarations,
                                ancestors: ancestors.clone(),
                            })
                            .collect()
                    }
                    _ => Vec::new(),
                };
                Content::Group {
                    name: nested.map_or_else(
                        || {
                            declaration
                                .declaration
                                .authored_path
                                .rsplit("::")
                                .next()
                                .unwrap_or_default()
                                .to_owned()
                        },
                        |(id, _)| id.item_name().to_owned(),
                    ),
                    children,
                }
            }
        }
    }
}

/// The kind of every cell field each fixed configuration and `#[k::cell]` struct declares, as
/// the collector reads it from the host declaration ([`HostCell`]), by the declaring
/// descriptor's identity and the field's Rust name.
pub(super) type HostCellKinds = Vec<(StableItemId, Vec<(String, CellKind)>)>;

/// The provenance keys a configuration's decision drops: the `main` markers of the candidates
/// its computation does not read, by configuration.
pub(super) type DroppedKeys = HashMap<StableItemId, BTreeSet<krs_ir::ProvenanceKey>>;

/// The entry-admission table's judgement of a configuration's initializer entries
/// ([`admit_initializer`]), given the configuration's index in the descriptors: whether it
/// judged them, or its refusal.
pub(super) type Admission<'a> =
    dyn FnMut(&[PendingDescriptor], usize) -> Result<bool, CollectionError> + 'a;

/// Decides every configuration's kind-neutral initializer leaves by the declared cell's kind,
/// before anything reads a leaf's wrapper (the main cell, the configuration's resolution): a
/// bracketed value is the sequence of its items on a computation cell, and the list of its items
/// on a `List` or cons-list leaf (P2/P3: brackets are the computation's or the list's mark, read
/// by the declared kind).
///
/// Every configuration's entries are the entry-admission table's to judge, against the
/// entries' spellings (`admit`, given the configuration's index in `pending`): an initializer's
/// value is its cell's whole initial content, of the cell's declared kind, and the macro, which
/// does not know that kind, checks none of it. A refusal is the author's answer. A leaf the
/// cell's own kind does not decide (one below a presence or an instances layer, or of a kind
/// brackets do not mark) is decided once the table admits its entry: its brackets are the mark
/// of the content below the presence or the instances (`Some([..])` on an optional list).
/// `admit` answers whether it judged the entries; a configuration it did not judge keeps its
/// leaves neutral.
///
/// Then main: the main configuration variable is the one the computation reads. A candidate
/// marks each variable a neutral leaf reads when nothing else decides main; the rule `k!`
/// follows decides among the candidates the decided computation reads: one is main, two are
/// ambiguous at the second, and the others' markers are dropped.
///
/// # Errors
///
/// [`CollectionErrorKind::AmbiguousMainConfigurationVariable`], with the configuration's index
/// in `pending` and the second candidate's marker key, where the computation reads two; or the
/// refusal `admit` gives, with no key (it is located already).
pub(super) fn decide_neutral_leaves(
    pending: &mut [PendingDescriptor],
    builtins: Option<&HostBuiltinRegistry>,
    admit: &mut Admission<'_>,
) -> Result<DroppedKeys, (usize, Option<krs_ir::ProvenanceKey>, CollectionError)> {
    let kinds = {
        let views = HostCellDeclarations::new(pending, builtins);
        pending
            .iter()
            .filter_map(|descriptor| match &descriptor.host.payload {
                HostDescriptorPayload::Cell(declaration) => Some(declaration.as_ref()),
                HostDescriptorPayload::FixedConfiguration(configuration) => {
                    Some(&configuration.declaration)
                }
                _ => None,
            })
            .flat_map(|declaration| &declaration.fields)
            .map(|field| {
                (
                    field.reference.cell.resolve(),
                    CellKind::of(&views.cell(field)),
                )
            })
            .collect::<HashMap<_, _>>()
    };
    let leaf_wrappers = declared_leaf_wrappers(pending);
    let mut dropped = DroppedKeys::new();
    for index in 0..pending.len() {
        let mut computations = Vec::new();
        let Some(initializer) = configuration_initializer(&mut pending[index]) else {
            continue;
        };
        decide_leaves(&mut initializer.cells, &kinds, &mut computations, false);
        let judged = admit(pending, index).map_err(|error| (index, None, error))?;
        if judged
            && let Some(initializer) = configuration_initializer(&mut pending[index])
            && holds_neutral_leaf(&initializer.cells)
        {
            decide_leaves(&mut initializer.cells, &kinds, &mut computations, true);
        }
        settle_deferred(&mut pending[index], judged, &leaf_wrappers)
            .map_err(|error| (index, None, error))?;
        let descriptor = &mut pending[index];
        let HostDescriptorPayload::FixedConfiguration(configuration) = &mut descriptor.host.payload
        else {
            continue;
        };
        let initializer = &mut configuration.initializer;
        if !initializer
            .variables
            .iter()
            .any(|variable| variable.main_candidate)
        {
            continue;
        }
        let mut read = initializer
            .variables
            .iter_mut()
            .filter(|variable| variable.main_candidate)
            .filter(|variable| {
                computations
                    .iter()
                    .any(|state| krs_ir::initializer_state_reads(state, &variable.binding))
            });
        let main = read.next().map(|variable| variable.binding.clone());
        if let Some(ambiguous) = read.next() {
            let key = ambiguous
                .main_key
                .clone()
                .expect("a main candidate has a marker");
            return Err((
                index,
                Some(key),
                CollectionError::new(
                    CollectionErrorKind::AmbiguousMainConfigurationVariable,
                    format!(
                        "the computation reads two configuration variables, `{}` and `{}`, so \
                         which is main is ambiguous: mark one `#[k::config_var(main)]`",
                        main.as_deref().unwrap_or_default(),
                        ambiguous.binding
                    ),
                ),
            ));
        }
        for variable in &mut initializer.variables {
            if !variable.main_candidate {
                continue;
            }
            variable.main_candidate = false;
            if main.as_ref() != Some(&variable.binding)
                && let Some(key) = variable.main_key.take()
            {
                dropped
                    .entry(descriptor.id.clone())
                    .or_default()
                    .insert(key);
            }
        }
    }
    Ok(dropped)
}

/// Judges, by the entry-admission table, every initializer entry of the configuration
/// `pending[index]` ([`super::cell_entries::judge_initializer`]): each against its declared
/// cell, from the initializer's authored fields. Then, the entries admitted, the sort step for
/// what the wire's shape says of a value ([`initializer_shape`]), then the refusal the reader
/// left until both had answered (a group record update). Answers whether it judged them:
/// an initializer whose source or declaration does not resolve here is left as it is, for the
/// configuration's resolution to report.
///
/// # Errors
///
/// The table's refusal of the first refused entry, located at what it refuses; else the first
/// value whose shape is another cell's than its own; else the reader's deferred refusal.
pub(super) fn admit_initializer(
    pending: &[PendingDescriptor],
    index: usize,
    builtins: Option<&HostBuiltinRegistry>,
    authored: Option<&super::cell_entries::LocatedCells>,
) -> Result<bool, CollectionError> {
    let HostDescriptorPayload::FixedConfiguration(configuration) = &pending[index].host.payload
    else {
        return Ok(false);
    };
    let Some(authored) = authored else {
        return Ok(false);
    };
    let Ok(cell_fields) = declared_cell_field_table(pending) else {
        return Ok(false);
    };
    let views = HostCellDeclarations::new(pending, builtins);
    let Ok(cells) = configuration
        .declaration
        .fields
        .iter()
        .map(|field| head_rule_cell_target(&views.cell(field), &cell_fields, None, &[], None))
        .collect::<Result<Vec<_>, _>>()
    else {
        return Ok(false);
    };
    let entries = configuration
        .initializer
        .cells
        .iter()
        .filter_map(|cell| {
            let identity = cell_fields.get(&cell.field.cell.resolve())?;
            let target = cells.iter().find(|target| &target.identity == identity)?;
            Some((
                &target.identity,
                krs_ir::cell_kind::EntryKind {
                    path: target.path.clone(),
                    own: target.kind.clone(),
                },
                target.sort.as_deref(),
            ))
        })
        .collect::<Vec<_>>();
    super::cell_entries::judge_initializer(&entries, &configuration_groups(&cells), authored)?;
    let declared = pending
        .iter()
        .filter_map(|descriptor| match &descriptor.host.payload {
            HostDescriptorPayload::Cell(declaration) => Some(declaration.as_ref()),
            HostDescriptorPayload::FixedConfiguration(configuration) => {
                Some(&configuration.declaration)
            }
            _ => None,
        })
        .flat_map(|declaration| &declaration.fields)
        .map(|field| (field.reference.cell.resolve(), field))
        .collect::<HashMap<_, _>>();
    if let Some((path, reason)) = initializer_shape(&configuration.initializer.cells, &declared) {
        return Err(super::cell_entries::initializer_content_sort(
            authored, &path, reason,
        ));
    }
    // Every value fits its cell's kind and shape, so a group record update left by the reader
    // is the record update itself, on a group of its own struct or a `*` template of one.
    if let Some(error) = authored.left_after_admission() {
        return Err(error);
    }
    Ok(true)
}

/// The first cell of `cells`, at any depth, whose wire shape is not its declaration's, by the
/// names of the cells down to it and the reason; `None` where every shape is its cell's.
///
/// Once the table has admitted every entry by its marks, a value's shape against its cell is the
/// lattice's step: a term's sort is no group's, a group record's sort is its group's, and a
/// record of one group is not below another's cell. So a term on a group cell, a group record on
/// a leaf and a record of another group are the content-sort mistake, which the wire shows where
/// the macro wrote the shape the value's spelling has. A neutral leaf states no shape, and a cell
/// whose declaration does not resolve here is the configuration's resolution's to report.
fn initializer_shape(
    cells: &[krs_ir::HostInitializerCell],
    declared: &HashMap<(TypeId, TypeId), &krs_ir::HostCellField>,
) -> Option<(Vec<String>, ShapeMismatch)> {
    use krs_ir::{ProtocolCellContent, ProtocolInitializerCellContent};
    for cell in cells {
        let Some(field) = declared.get(&cell.field.cell.resolve()) else {
            continue;
        };
        let name = field.rust_field.clone();
        let mismatch = match (&cell.content, &field.content) {
            (
                ProtocolInitializerCellContent::Leaf { .. },
                ProtocolCellContent::Nested { declaration },
            ) => Some(ShapeMismatch::TermOnGroup {
                group: last_segment(&declaration.declaration.authored_path),
            }),
            (
                ProtocolInitializerCellContent::Nested { declaration, .. },
                ProtocolCellContent::Leaf { .. },
            ) => Some(ShapeMismatch::RecordOnLeaf {
                record: last_segment(&declaration.declaration.authored_path),
            }),
            (
                ProtocolInitializerCellContent::Nested {
                    declaration: written,
                    children,
                },
                ProtocolCellContent::Nested { declaration },
            ) => {
                if written.declaration.key.resolve() != declaration.declaration.key.resolve() {
                    Some(ShapeMismatch::RecordOfAnotherGroup {
                        record: last_segment(&written.declaration.authored_path),
                        group: last_segment(&declaration.declaration.authored_path),
                    })
                } else if let Some((mut path, reason)) = initializer_shape(children, declared) {
                    path.insert(0, name.clone());
                    return Some((path, reason));
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(mismatch) = mismatch {
            return Some((vec![name], mismatch));
        }
    }
    None
}

/// How an initializer value's shape is not its cell's ([`initializer_shape`]).
#[derive(Clone, Debug)]
pub(super) enum ShapeMismatch {
    /// A term on a group cell of this struct.
    TermOnGroup { group: String },
    /// A record of this group struct on a leaf cell.
    RecordOnLeaf { record: String },
    /// A record of the group struct `record` on a group cell of the struct `group`.
    RecordOfAnotherGroup { record: String, group: String },
}

/// The last segment of an authored Rust path.
fn last_segment(path: &str) -> String {
    path.rsplit("::").next().unwrap_or(path).trim().to_owned()
}

/// The initializer of `descriptor`, where it is a fixed configuration.
fn configuration_initializer(
    descriptor: &mut PendingDescriptor,
) -> Option<&mut krs_ir::HostConfigurationInitializer> {
    match &mut descriptor.host.payload {
        HostDescriptorPayload::FixedConfiguration(configuration) => {
            Some(&mut configuration.initializer)
        }
        _ => None,
    }
}

/// The wrapper each declared leaf field of `pending` states, by its resolved identity.
fn declared_leaf_wrappers(
    pending: &[PendingDescriptor],
) -> HashMap<(TypeId, TypeId), krs_ir::CellWrapper> {
    pending
        .iter()
        .filter_map(|descriptor| match &descriptor.host.payload {
            HostDescriptorPayload::Cell(declaration) => Some(declaration.as_ref()),
            HostDescriptorPayload::FixedConfiguration(configuration) => {
                Some(&configuration.declaration)
            }
            _ => None,
        })
        .flat_map(|declaration| &declaration.fields)
        .filter_map(|field| match &field.content {
            krs_ir::ProtocolCellContent::Leaf { wrapper, .. } => {
                Some((field.reference.cell.resolve(), *wrapper))
            }
            krs_ir::ProtocolCellContent::Nested { .. } => None,
        })
        .collect()
}

/// Settles a configuration's kept disagreement with its declaration once its entries are
/// `judged`: a `KSequence` leaf's `k::k![..]` is that leaf's sequence, whose wrapper is the
/// leaf's (`wrappers`), which the macro, reading `k!` as the computation's, did not know; only a
/// disagreement the judged entries leave is the expander's, raised here.
fn settle_deferred(
    descriptor: &mut PendingDescriptor,
    judged: bool,
    wrappers: &HashMap<(TypeId, TypeId), krs_ir::CellWrapper>,
) -> Result<(), CollectionError> {
    if judged && let Some(initializer) = configuration_initializer(descriptor) {
        leaf_sequence_wrappers(&mut initializer.cells, wrappers);
    }
    if descriptor.deferred.is_some() && judged && descriptor.host.validate_state_ownership().is_ok()
    {
        descriptor.deferred = None;
    }
    descriptor.deferred.clone().map_or(Ok(()), Err)
}

/// Gives each leaf of `cells`, at any depth, that holds a `KSequence` state under the
/// computation's wrapper the wrapper its declaration states (`wrappers`): once the table has
/// judged the entries, a sequence on a leaf is that leaf's of sort `KSequence`.
fn leaf_sequence_wrappers(
    cells: &mut [krs_ir::HostInitializerCell],
    wrappers: &HashMap<(TypeId, TypeId), krs_ir::CellWrapper>,
) {
    for cell in cells {
        match &mut cell.content {
            krs_ir::ProtocolInitializerCellContent::Leaf {
                wrapper,
                value: krs_ir::ProtocolInitializerStateTerm::KSequence(_),
                ..
            } => {
                if let Some(declared) = wrappers.get(&cell.field.cell.resolve()) {
                    *wrapper = *declared;
                }
            }
            krs_ir::ProtocolInitializerCellContent::Nested { children, .. } => {
                leaf_sequence_wrappers(children, wrappers);
            }
            _ => {}
        }
    }
}

/// Whether `cells` hold a neutral leaf, at any depth.
fn holds_neutral_leaf(cells: &[krs_ir::HostInitializerCell]) -> bool {
    cells.iter().any(|cell| match &cell.content {
        krs_ir::ProtocolInitializerCellContent::NeutralLeaf { .. } => true,
        krs_ir::ProtocolInitializerCellContent::Nested { children, .. } => {
            holds_neutral_leaf(children)
        }
        krs_ir::ProtocolInitializerCellContent::Leaf { .. } => false,
    })
}

/// Decides the neutral leaves of `cells` by `kinds`, pushing the state of each one decided a
/// computation onto `computations`: by the cell's whole kind, or, once the table has `admitted`
/// the entries, by its content below its presence or instances.
fn decide_leaves(
    cells: &mut [krs_ir::HostInitializerCell],
    kinds: &HashMap<(TypeId, TypeId), CellKind>,
    computations: &mut Vec<krs_ir::HostInitializerStateTerm>,
    admitted: bool,
) {
    for cell in cells {
        match &mut cell.content {
            krs_ir::ProtocolInitializerCellContent::NeutralLeaf {
                constructor_key,
                value,
            } => {
                // Before the admission, a cell of one, neither optional nor a collection: an
                // optional cell's or a collection's brackets are the admission's to judge against
                // its marks, and only an admitted entry's are its content's.
                let kind = kinds.get(&cell.field.cell.resolve());
                let layers = match kind {
                    Some(kind) if admitted => kind.content().map(std::slice::from_ref),
                    Some(kind) => Some(kind.layers.as_slice()),
                    None => None,
                };
                let wrapper = match layers {
                    Some([Layer::Computation]) => krs_ir::CellWrapper::KCell,
                    Some([Layer::Leaf(Notation::List | Notation::Cons)]) => {
                        krs_ir::CellWrapper::Cell
                    }
                    _ => continue,
                };
                if wrapper == krs_ir::CellWrapper::KCell {
                    computations.push(value.clone());
                }
                cell.content = krs_ir::ProtocolInitializerCellContent::Leaf {
                    constructor_key: constructor_key.clone(),
                    wrapper,
                    value: value.clone(),
                };
            }
            krs_ir::ProtocolInitializerCellContent::Nested { children, .. } => {
                decide_leaves(children, kinds, computations, admitted);
            }
            krs_ir::ProtocolInitializerCellContent::Leaf { .. } => {}
        }
    }
}

/// The kinds [`HostCell`] gives every declared cell field of `pending`.
pub(super) fn host_cell_kinds(
    pending: &[PendingDescriptor],
    views: &HostCellDeclarations<'_>,
) -> HostCellKinds {
    pending
        .iter()
        .filter_map(|descriptor| {
            let declaration = match &descriptor.host.payload {
                HostDescriptorPayload::Cell(declaration) => declaration.as_ref(),
                HostDescriptorPayload::FixedConfiguration(configuration) => {
                    &configuration.declaration
                }
                _ => return None,
            };
            let fields = declaration
                .fields
                .iter()
                .map(|field| (field.rust_field.clone(), CellKind::of(&views.cell(field))))
                .collect();
            Some((descriptor.id.clone(), fields))
        })
        .collect()
}

/// Checks that the collector's two readings of each cell give it one kind: the host
/// declaration, which the collector decides with before the descriptors are resolved
/// ([`HostCell`], resolved by Rust types), and the collected declaration, which every
/// compile-path reader after collection asks ([`krs_ir::cell_kind::DescriptorCell`], resolved by
/// stable identities). They read different inputs (nested groups by `TypeId` against the index;
/// builtins by their registered markers against `DescriptorSortRef::Builtin`; cons lists by the
/// grammar's resolved type against its stable identity), so a disagreement is a collector
/// fault, never the author's.
///
/// # Errors
///
/// Returns an internal [`CollectionErrorKind::CellKindDisagreement`] naming the first field the
/// readings disagree on, with both kinds.
pub(super) fn check_cell_kinds(
    bundle: &krs_ir::DescriptorBundle,
    host: &HostCellKinds,
) -> Result<(), CollectionError> {
    let index = krs_ir::DescriptorIndex::new(bundle);
    let disagreement =
        |detail: String| CollectionError::new(CollectionErrorKind::CellKindDisagreement, detail);
    for (owner, fields) in host {
        let declaration = index.cell_owner(owner).map_err(|error| {
            disagreement(format!(
                "the cells `{}` declares have no collected declaration: {error}",
                owner.item_name()
            ))
        })?;
        for (field, host_kind) in fields {
            let collected = declaration
                .fields
                .iter()
                .find(|collected| &collected.rust_field == field)
                .ok_or_else(|| {
                    disagreement(format!(
                        "the cell `{}.{field}` has no collected declaration",
                        owner.item_name()
                    ))
                })?;
            let collected_kind = krs_ir::cell_kind::DescriptorCell::new(collected, &index).kind();
            if *host_kind != collected_kind {
                return Err(disagreement(format!(
                    "the collector reads the cell `{}.{field}` as {host_kind:?} from its host declaration and as {collected_kind:?} from its collected declaration",
                    owner.item_name()
                )));
            }
        }
    }
    Ok(())
}

#[derive(Clone, Debug)]
pub(super) struct HeadRuleTarget {
    configuration: StableItemId,
    cells: Vec<HeadRuleCellTarget>,
    /// The configuration's main cell (`krs_ir::select_main_cell`), the computation a rule that
    /// names no cell rewrites.
    main: krs_ir::MainCell<krs_ir::DescriptorCellIdentity>,
    /// Where the configuration has no main cell, its refusal (`main-cell`), located at its
    /// initializer: the one error a rule that needs the main cell reports
    /// ([`locate_main_cell_refusals`]).
    main_refusal: Option<CollectionError>,
    /// The children of each nested `#[k::cell]` struct, by its resolved
    /// type: a group record that names fewer leaves some out.
    group_children: HashMap<TypeId, GroupChildren>,
    /// The configuration's groups ([`krs_syntax::cell_entries::collect_groups`]), whose records
    /// the entry-admission table reads.
    groups: Vec<krs_ir::cell_kind::GroupKind>,
    /// The cell group this target is scoped to, absent for the whole configuration. A scoped
    /// target's `cells` are the cells its subject lets a sentence name
    /// ([`krs_ir::subject::scope`]): name lookup, the computation cell and the readings of a
    /// readable record stay within them.
    subject: Option<TargetSubject>,
    /// The configuration scoped to each cell group a cell of it holds, by the group's
    /// declaration, or why a sentence about the group has no scope there; empty on a scoped
    /// target.
    subjects: Vec<(StableItemId, Result<HeadRuleTarget, CollectionError>)>,
    /// On the configuration's own target, the key of each Map collection's instance whose cells
    /// its sentences may name directly ([`Self::through_maps`]), as
    /// [`TargetSubject::nested_keys`] holds them; empty on a scoped target.
    configuration_keys: Vec<NestedKey>,
}

/// The cell group a [`HeadRuleTarget`] is scoped to.
#[derive(Clone, Debug)]
struct TargetSubject {
    subject: krs_ir::DescriptorSubject,
    /// The group's name, as a message names it.
    name: String,
    /// The cell of the configuration that holds the group.
    holder: HeadRuleCellTarget,
    /// The configuration's other cells outside the group, which a sentence about the group may
    /// not name.
    outside: Vec<HeadRuleCellTarget>,
    /// Where the group is the instance type of a Map collection, the instance's key cell
    /// ([`krs_ir::cell_kind::CellKind::instance_key`]) and every cell inside it: the whole key is
    /// the instance's identity, which a sentence about the instance reads and never writes
    /// another of ([`krs_syntax::cell_entries::keeps_key`]). Empty for any other subject.
    key: Vec<krs_ir::DescriptorCellIdentity>,
    /// The same of each Map collection inside the group whose instance's cells the sentence
    /// names directly ([`HeadRuleTarget::scoped`]), with the collection's name and its group's.
    nested_keys: Vec<NestedKey>,
}

/// The key of a Map collection's instance whose cells a sentence names directly: the key cell and
/// the cells inside it, the collection cell's name and identity, and the instance group's name.
type NestedKey = (
    Vec<krs_ir::DescriptorCellIdentity>,
    String,
    krs_ir::DescriptorCellIdentity,
    String,
);

/// A Map collection instance's key as [`HeadRuleTarget::instance_key`] and
/// [`HeadRuleTarget::nested_instance_keys`] give it: the key cells, the collection cell's name
/// and identity, and the instance group's name.
pub(super) type TargetKey<'t> = (
    &'t [krs_ir::DescriptorCellIdentity],
    &'t str,
    &'t krs_ir::DescriptorCellIdentity,
    &'t str,
);

/// Where a cell a sentence about a cell group names sits, outside the group.
enum OutsideCell<'a> {
    /// The cell that holds the group.
    Holder,
    /// Another cell of the configuration.
    Other,
    /// A cell of the group `.0`, which no cell of the configuration holds.
    NotHeld(&'a StableItemId),
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

impl HeadRuleTarget {
    /// The configuration the target is.
    pub(super) const fn configuration(&self) -> &StableItemId {
        &self.configuration
    }

    /// The configuration's groups, whose records the entry-admission table reads.
    pub(super) fn groups(&self) -> &[krs_ir::cell_kind::GroupKind] {
        &self.groups
    }

    /// The one cell a readable record entry `name` names, with what the entry is judged
    /// against: the layers of its `?` and `*` ancestors and its own; `None` where no cell, or
    /// more than one, has the name, which the rule's resolution reports.
    pub(super) fn entry(
        &self,
        name: &str,
    ) -> Option<(
        &krs_ir::DescriptorCellIdentity,
        krs_ir::cell_kind::EntryKind,
        Option<&MarkedAncestor>,
        Option<&str>,
    )> {
        let mut named = self
            .cells
            .iter()
            .filter(|cell| cell.names.iter().any(|candidate| candidate == name));
        let (Some(cell), None) = (named.next(), named.next()) else {
            return None;
        };
        Some((
            &cell.identity,
            krs_ir::cell_kind::EntryKind {
                path: cell.path.clone(),
                own: cell.kind.clone(),
            },
            cell.ancestor.as_ref(),
            cell.sort.as_deref(),
        ))
    }

    /// Locates the configuration's main-cell refusal, where it has one, by `locate`.
    pub(super) fn locate_main_refusal(
        &mut self,
        locate: impl FnOnce(CollectionError) -> CollectionError,
    ) {
        self.main_refusal = self.main_refusal.take().map(locate);
        for (_, scoped) in &mut self.subjects {
            if let Ok(scoped) = scoped {
                scoped.main_refusal.clone_from(&self.main_refusal);
            }
        }
    }

    /// The subject a sentence resolved against this target carries.
    fn descriptor_subject(&self) -> Option<krs_ir::DescriptorSubject> {
        self.subject.as_ref().map(|subject| subject.subject.clone())
    }

    /// What a message calls the part of the configuration the target is: the configuration,
    /// or the group it is scoped to.
    fn owner(&self) -> String {
        match &self.subject {
            Some(subject) => format!("the group `{}`", subject.name),
            None => format!("configuration `{}`", self.configuration.item_name()),
        }
    }

    /// The refusal of the name `name`, which no cell the target lets a sentence name has, where a
    /// cell of the configuration outside the target's group has it.
    fn outside(&self, name: &str) -> Option<CollectionError> {
        let subject = self.subject.as_ref()?;
        let named =
            |cell: &HeadRuleCellTarget| cell.names.iter().any(|candidate| candidate == name);
        let place = if named(&subject.holder) {
            OutsideCell::Holder
        } else if subject.outside.iter().any(named) {
            OutsideCell::Other
        } else {
            return None;
        };
        Some(self.outside_refusal(subject, name, &place))
    }

    /// The refusal of the cell `cell`, which a sentence names by its owner (`Group::cell` in
    /// `cells!`), where the target is scoped to a group and the cell is not inside it.
    fn outside_cell(&self, cell: &krs_ir::DescriptorCellIdentity) -> Option<CollectionError> {
        let subject = self.subject.as_ref()?;
        if self
            .cells
            .iter()
            .any(|candidate| candidate.identity == *cell)
        {
            return None;
        }
        let place = if subject.holder.identity == *cell {
            OutsideCell::Holder
        } else if subject
            .outside
            .iter()
            .any(|candidate| candidate.identity == *cell)
        {
            OutsideCell::Other
        } else {
            OutsideCell::NotHeld(&cell.owner)
        };
        let spelled = format!("{}::{}", cell.owner.item_name(), cell.field);
        Some(self.outside_refusal(subject, &spelled, &place))
    }

    /// The refusal of a sentence about the group `subject` that names the cell `spelled`, which
    /// sits at `place`, outside the group.
    fn outside_refusal(
        &self,
        subject: &TargetSubject,
        spelled: &str,
        place: &OutsideCell<'_>,
    ) -> CollectionError {
        let configuration = self.configuration.item_name();
        let why = match place {
            OutsideCell::Holder => format!(
                "`{spelled}` is the cell of configuration `{configuration}` that holds the group; write the sentence for `{configuration}` to name it"
            ),
            OutsideCell::Other => format!(
                "`{spelled}` is another cell of configuration `{configuration}`; write the sentence for `{configuration}` to name it"
            ),
            OutsideCell::NotHeld(owner) => format!(
                "`{spelled}` is a cell of the group `{}`, which configuration `{configuration}` does not hold",
                owner.item_name()
            ),
        };
        CollectionError::new(
            CollectionErrorKind::CellOutsideSubject,
            format!(
                "`{group}` has no cell `{spelled}`: a sentence about the cell group `{group}` names only the cells inside the group, and {why}",
                group = subject.name,
            ),
        )
    }

    /// Scopes the configuration to each cell group one of its cells holds
    /// ([`krs_ir::subject::scope`]), reading its cells as a tree, then judges the configuration's
    /// own cells as a sentence typed by it does ([`Self::through_maps`]).
    fn with_subjects(mut self) -> Self {
        let tree = self.tree();
        let mut groups = Vec::new();
        for group in self.cells.iter().filter_map(|cell| cell.group_id.as_ref()) {
            if !groups.contains(group) {
                groups.push(group.clone());
            }
        }
        self.subjects = groups
            .into_iter()
            .map(|group| {
                let subject = krs_ir::DescriptorSubject::Group {
                    declaration: group.clone(),
                };
                let scoped = match krs_ir::subject::scope(&tree, Some(&subject)) {
                    Ok(krs_ir::SubjectScope {
                        anchor: Some(anchor),
                        nameable,
                        ..
                    }) => {
                        let scoped = self.scoped(subject, anchor, &tree);
                        debug_assert!(
                            scoped
                                .cells
                                .iter()
                                .all(|cell| nameable.contains(&cell.identity))
                                && scoped.cells.len() == nameable.len(),
                            "the cells below the anchor are the scope's nameable cells"
                        );
                        Ok(scoped)
                    }
                    Ok(krs_ir::SubjectScope { anchor: None, .. }) => {
                        unreachable!("a group's scope has the cell that holds the group")
                    }
                    // A configuration that holds one group in several cells is refused whatever
                    // its sentences say (`ambiguous-cell-sort`, at the second field): the fault
                    // is the configuration's, so it is left to that check. Cell identities are
                    // nominal, so the cells below each position have the same identities, and
                    // the first position resolves the sentence's names as any other would.
                    Err(krs_ir::SubjectError::SeveralPositions { positions }) => {
                        Ok(self.scoped(subject, positions[0], &tree))
                    }
                    Err(error) => Err(self.subject_refusal(&group, &error)),
                };
                (group, scoped)
            })
            .collect();
        self.through_maps()
    }

    /// The configuration's cells as a tree.
    fn tree(&self) -> Vec<krs_ir::TreeCell> {
        self.cells
            .iter()
            .map(|cell| krs_ir::TreeCell {
                identity: cell.identity.clone(),
                parent: cell.parent,
                group: cell.group_id.clone(),
                multiplicity: cell.kind.multiplicity(),
                computation: cell.kind.is_computation(),
                key: cell.kind.instance_key().map(str::to_owned),
            })
            .collect()
    }

    /// The configuration's own target judged as a sentence typed by the configuration is: the
    /// Map collections a cell lies in, outermost first up to the first other `?` or `*`, drop
    /// their marks, as below a group's anchor ([`Self::scoped`]). A sentence's cells lie in one
    /// instance of each holder on their deepest chain, so naming a cell of a Map collection's
    /// instance matches one instance of each such collection, the one whose cell matches, as a
    /// rule for the instance's group does, and each such instance's key is written only as
    /// matched ([`Self::nested_instance_keys`]). A cell below an optional cell (whose presence is
    /// stated, never implied), a Set collection (whose steps would merge instances) or a List
    /// collection (whose middle instances are not matched yet) keeps that mark, so it is still
    /// written inside that holder's record. Called once the scoped targets are made
    /// ([`Self::with_subjects`]), since they count the marks from the configuration's level.
    fn through_maps(mut self) -> Self {
        let tree = self.tree();
        let marked = |cell: &HeadRuleCellTarget| {
            matches!(
                cell.kind.layers.first(),
                Some(Layer::Optional | Layer::Instances(_))
            )
        };
        for index in 0..self.cells.len() {
            // The cell's marked holders, outermost first; parents precede their children.
            let mut holders = std::iter::successors(self.cells[index].parent, |&parent| {
                self.cells[parent].parent.filter(|&above| above < parent)
            })
            .filter(|&holder| marked(&self.cells[holder]))
            .collect::<Vec<_>>();
            holders.reverse();
            let nested = holders
                .iter()
                .take_while(|&&holder| self.is_map_collection(holder))
                .count();
            if nested == 0 {
                continue;
            }
            let ancestor = holders.get(nested).and_then(|&holder| {
                let target = &self.cells[holder];
                match target.kind.layers.as_slice() {
                    [
                        layer @ (Layer::Optional | Layer::Instances(_)),
                        Layer::Group(group),
                        ..,
                    ] => Some(MarkedAncestor {
                        name: target.names[0].clone(),
                        layer: layer.clone(),
                        group: group.name.clone(),
                        direct: self.cells[index].parent == Some(holder),
                    }),
                    _ => None,
                }
            });
            let cell = &mut self.cells[index];
            cell.path.layers.drain(..nested.min(cell.path.layers.len()));
            cell.ancestor = ancestor;
        }
        self.configuration_keys = self.nested_map_keys(None, &tree);
        self
    }

    /// The target scoped to `subject`, a group the cell at `anchor` holds: its sentences name
    /// the cells below that cell.
    ///
    /// A sentence about the group is a local step of one instance of each optional cell and
    /// collection on the anchor's path, the anchor included, so its entries are judged from the
    /// instance's level: each cell's `path` and `ancestor` keep only the marks strictly below the
    /// anchor.
    ///
    /// The Map collections a cell lies in inside the instance, outermost first up to the first
    /// other `?` or `*`, drop their marks too: a sentence's cells lie in one instance of each
    /// holder on their deepest chain, so naming a cell of a nested instance matches one instance
    /// of each such collection, the one whose cell matches, as naming a cell of the group matches
    /// one instance of the group. Each such instance's key is written only as matched
    /// ([`Self::nested_instance_keys`]). A cell below a Set or List collection, or an optional
    /// cell, inside the instance keeps that mark, so it is still written inside that inner
    /// holder's record.
    fn scoped(
        &self,
        subject: krs_ir::DescriptorSubject,
        anchor: usize,
        tree: &[krs_ir::TreeCell],
    ) -> Self {
        let krs_ir::DescriptorSubject::Group { declaration } = &subject;
        // Parents precede their children, so the walk up from a cell ends at the top level.
        let above = |index: usize| {
            std::iter::successors(self.cells[index].parent, |&parent| {
                self.cells[parent].parent.filter(|&above| above < parent)
            })
        };
        let below = |index: usize| above(index).any(|ancestor| ancestor == anchor);
        let marked = |index: usize| {
            matches!(
                self.cells[index].kind.layers.first(),
                Some(Layer::Optional | Layer::Instances(_))
            )
        };
        // The marks of the anchor and its ancestors, which the instance's level drops.
        let dropped = std::iter::once(anchor)
            .chain(above(anchor))
            .filter(|&index| marked(index))
            .count();
        let (cells, outside): (Vec<_>, Vec<_>) = self
            .cells
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != anchor)
            .partition(|(index, _)| below(*index));
        let cells = cells
            .into_iter()
            .map(|(index, cell)| {
                let mut cell = cell.clone();
                // The marked holders strictly between the anchor and the cell, outermost first,
                // and how many of them lead as Map collections.
                let between = above(index)
                    .take_while(|&ancestor| ancestor != anchor)
                    .filter(|&ancestor| marked(ancestor))
                    .collect::<Vec<_>>();
                let nested = between
                    .iter()
                    .rev()
                    .take_while(|&&ancestor| self.is_map_collection(ancestor))
                    .count();
                let kept = cell.path.layers.len().saturating_sub(dropped + nested);
                cell.path.layers.drain(..cell.path.layers.len() - kept);
                // The outermost marked group strictly between the anchor and the cell, after
                // those.
                cell.ancestor = between.iter().rev().skip(nested).find_map(|&ancestor| {
                    let holder = &self.cells[ancestor];
                    match holder.kind.layers.as_slice() {
                        [
                            layer @ (Layer::Optional | Layer::Instances(_)),
                            Layer::Group(group),
                            ..,
                        ] => Some(MarkedAncestor {
                            name: holder.names[0].clone(),
                            layer: layer.clone(),
                            group: group.name.clone(),
                            direct: cell.parent == Some(ancestor),
                        }),
                        _ => None,
                    }
                });
                cell
            })
            .collect();
        // The key of the instance the sentence is about, and every cell inside it.
        let key = (0..self.cells.len())
            .filter(|&index| {
                krs_ir::subject::keys_on_path(tree, index)
                    .iter()
                    .any(|&(holder, _)| holder == anchor)
            })
            .map(|index| self.cells[index].identity.clone())
            .collect();
        let nested_keys = self.nested_map_keys(Some(anchor), tree);
        Self {
            configuration: self.configuration.clone(),
            cells,
            main: self.main.clone(),
            main_refusal: self.main_refusal.clone(),
            group_children: self.group_children.clone(),
            groups: self.groups.clone(),
            subject: Some(TargetSubject {
                name: declaration.item_name().to_owned(),
                holder: self.cells[anchor].clone(),
                outside: outside.into_iter().map(|(_, cell)| cell.clone()).collect(),
                key,
                nested_keys,
                subject,
            }),
            subjects: Vec::new(),
            configuration_keys: Vec::new(),
        }
    }

    /// Whether the cell at `index` is a Map collection.
    fn is_map_collection(&self, index: usize) -> bool {
        matches!(
            self.cells[index].kind.layers.first(),
            Some(Layer::Instances(Order::Map))
        )
    }

    /// The key of each Map collection's instance below the cell at `anchor`, or in the whole
    /// configuration where there is none, as [`TargetSubject::nested_keys`] holds them.
    fn nested_map_keys(&self, anchor: Option<usize>, tree: &[krs_ir::TreeCell]) -> Vec<NestedKey> {
        let below = |index: usize| {
            anchor.is_none_or(|anchor| {
                std::iter::successors(self.cells[index].parent, |&parent| {
                    self.cells[parent].parent.filter(|&above| above < parent)
                })
                .any(|ancestor| ancestor == anchor)
            })
        };
        (0..self.cells.len())
            .filter(|&holder| below(holder) && self.is_map_collection(holder))
            .filter_map(|holder| {
                let Some(Layer::Group(group)) = self.cells[holder].kind.layers.get(1) else {
                    return None;
                };
                let cells = (0..self.cells.len())
                    .filter(|&index| {
                        krs_ir::subject::keys_on_path(tree, index)
                            .iter()
                            .any(|&(on, _)| on == holder)
                    })
                    .map(|index| self.cells[index].identity.clone())
                    .collect::<Vec<_>>();
                (!cells.is_empty()).then(|| {
                    (
                        cells,
                        self.cells[holder].names[0].clone(),
                        self.cells[holder].identity.clone(),
                        group.name.clone(),
                    )
                })
            })
            .collect()
    }

    /// The key cells of each Map collection's instance whose cells the target's sentences name
    /// directly: inside the group a scoped target is about ([`Self::scoped`]), or in the whole
    /// configuration ([`Self::through_maps`]), each with the collection cell's name and the
    /// group's: a sentence writes each only as it matched it.
    pub(super) fn nested_instance_keys(&self) -> impl Iterator<Item = TargetKey<'_>> {
        self.subject
            .iter()
            .flat_map(|subject| subject.nested_keys.iter())
            .chain(&self.configuration_keys)
            .map(|(cells, holder, identity, group)| {
                (cells.as_slice(), holder.as_str(), identity, group.as_str())
            })
    }

    /// Where the target is scoped to the instance type of a Map collection, the instance's key
    /// cell and the cells inside it, which a sentence about the instance never writes another
    /// of, with the collection cell's name and the group's.
    pub(super) fn instance_key(&self) -> Option<TargetKey<'_>> {
        let subject = self.subject.as_ref()?;
        (!subject.key.is_empty()).then(|| {
            (
                subject.key.as_slice(),
                subject.holder.names[0].as_str(),
                &subject.holder.identity,
                subject.name.as_str(),
            )
        })
    }

    /// The refusal of a sentence typed by the group `group`, which has no scope in the
    /// configuration for `error`.
    fn subject_refusal(
        &self,
        group_id: &StableItemId,
        error: &krs_ir::SubjectError,
    ) -> CollectionError {
        let group = group_id.item_name();
        let configuration = self.configuration.item_name();
        let name = |index: usize| format!("`{}`", self.cells[index].names[0]);
        // The group's own cell, where it is the marked one, holds it; an ancestor has it below.
        let held = |ancestor: usize| {
            if self.cells[ancestor].group_id.as_ref() == Some(group_id) {
                "is held by"
            } else {
                "sits below"
            }
        };
        let detail = match error {
            krs_ir::SubjectError::NotInConfiguration => {
                return CollectionError::new(
                    CollectionErrorKind::GroupNotInConfiguration,
                    format!(
                        "no cell of configuration `{configuration}` holds the cell group `{group}`, so a rule for `{group}` has no cells to apply to: a group's rules apply at the group's position in the definition's configuration"
                    ),
                );
            }
            krs_ir::SubjectError::SeveralPositions { .. } => {
                unreachable!("a group held by several cells is scoped at the first of them")
            }
            krs_ir::SubjectError::BelowCollection {
                ancestor,
                order: Order::Set,
            } => format!(
                "the cell group `{group}` {} the Set collection cell {} of configuration `{configuration}`: a sentence about `{group}` is about one instance, which a rule rewrites as a local step, and a Set identifies an instance by its whole content, so a step that makes one instance equal to another merges the two, removing an instance the rule never matched; write the sentence for `{configuration}`, or hold the instances in a Map collection keyed by an id",
                held(*ancestor),
                name(*ancestor),
            ),
            krs_ir::SubjectError::BelowCollection {
                ancestor,
                order: Order::List,
            } => format!(
                "the cell group `{group}` {} the List collection cell {} of configuration `{configuration}`: a sentence about `{group}` is about one instance, which in a List is the instance at any position, and matching one instance between others is not supported yet; write the sentence for `{configuration}`, or hold the instances in a Map collection keyed by an id",
                held(*ancestor),
                name(*ancestor),
            ),
            krs_ir::SubjectError::BelowCollection {
                order: Order::Map, ..
            } => unreachable!("a Map collection keeps an instance's identity, its key"),
            krs_ir::SubjectError::InKey { holder, key } => {
                return CollectionError::new(
                    CollectionErrorKind::CellEntry(
                        krs_syntax::cell_entries::Refusal::MapCollectionKey,
                    ),
                    krs_ir::subject::key_subject_reason(
                        group,
                        &self.cells[*holder].names[0],
                        &self.cells[*key].names[0],
                    ),
                );
            }
        };
        CollectionError::new(CollectionErrorKind::GroupSubjectPosition, detail)
    }
}

/// The outermost `?` or `*` ancestor of the cells below `target`, a group, an optional group or
/// a collection whose own outermost `?` or `*` ancestor is `ancestor`: that ancestor, of which
/// they are no direct children, or `target` itself where it is the first marked one, whose
/// group's record names its children directly.
fn below_ancestor(
    ancestor: Option<&MarkedAncestor>,
    target: &HeadRuleCellTarget,
) -> Option<MarkedAncestor> {
    match (ancestor, target.kind.layers.as_slice()) {
        (Some(ancestor), _) => Some(MarkedAncestor {
            direct: false,
            ..ancestor.clone()
        }),
        (
            None,
            [
                layer @ (Layer::Optional | Layer::Instances(_)),
                Layer::Group(group),
                ..,
            ],
        ) => Some(MarkedAncestor {
            name: target.names[0].clone(),
            layer: layer.clone(),
            group: group.name.clone(),
            direct: true,
        }),
        (None, _) => None,
    }
}

fn collect_head_rule_cells(
    declaration: &krs_ir::HostCellDeclaration,
    declarations: &HashMap<TypeId, &krs_ir::HostCellDeclaration>,
    views: &HostCellDeclarations<'_>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    visiting: &mut HashSet<TypeId>,
    (cells, group_children): (
        &mut Vec<HeadRuleCellTarget>,
        &mut HashMap<TypeId, GroupChildren>,
    ),
    (path, ancestor, parent): (&[Layer], Option<&MarkedAncestor>, Option<usize>),
) -> Result<(), CollectionError> {
    for field in &declaration.fields {
        match &field.content {
            krs_ir::ProtocolCellContent::Leaf { .. } => {
                let mut target =
                    head_rule_cell_target(&views.cell(field), cell_fields, None, path, ancestor)?;
                target.parent = parent;
                cells.push(target);
            }
            krs_ir::ProtocolCellContent::Nested { declaration } => {
                // A group, an optional group, or a collection is named by a readable record
                // entry. Its descendants are collected too, so that a name resolving below an
                // optional or collection ancestor is found and then refused at admission with
                // that ancestor's class: an entry names the content of its own level, and below
                // a `*` ancestor the instance is written as an instance record.
                let key = declaration.declaration.key.resolve();
                let mut target = head_rule_cell_target(
                    &views.cell(field),
                    cell_fields,
                    Some(key),
                    path,
                    ancestor,
                )?;
                target.parent = parent;
                target.group_id = views.nested.get(&key).map(|(id, _)| (*id).clone());
                let index = cells.len();
                let below_ancestor = below_ancestor(ancestor, &target);
                let mut below = path.to_vec();
                below.extend(
                    target
                        .kind
                        .layers
                        .first()
                        .filter(|layer| matches!(layer, Layer::Optional | Layer::Instances(_)))
                        .cloned(),
                );
                cells.push(target);
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
                            .filter(|child| {
                                let kind = CellKind::of(&views.cell(child));
                                kind.multiplicity() == Multiplicity::One && kind.group().is_some()
                            })
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
                    views,
                    cell_fields,
                    visiting,
                    (&mut *cells, &mut *group_children),
                    (&below, below_ancestor.as_ref(), Some(index)),
                )?;
                visiting.remove(&key);
            }
        }
    }
    Ok(())
}

/// The fixed configurations as the targets a head rule, or a sentence typed by a cell group, is
/// resolved against: built only where the descriptors hold such a sentence, so a bundle without
/// one is resolved as before.
#[expect(
    clippy::too_many_lines,
    reason = "Each configuration's target is built in one pass: its cells, its main cell and its scoped targets."
)]
pub(super) fn resolve_head_rule_targets(
    pending: &[PendingDescriptor],
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    views: &HostCellDeclarations<'_>,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<Vec<HeadRuleTarget>, CollectionError> {
    if !needs_targets(pending, declarations) {
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
                views,
                cell_fields,
                &mut HashSet::new(),
                (&mut cells, &mut group_children),
                (&[], None, None),
            )?;
            let identity = |cell: &krs_ir::HostCellIdentity| {
                cell_fields.get(&cell.resolve()).cloned().ok_or_else(|| {
                    CollectionError::new(
                        CollectionErrorKind::UnresolvedTypeReference,
                        "a computation cell has no stable owner/field identity",
                    )
                })
            };
            let (main, main_refusal) = match configuration.main_cell() {
                krs_ir::MainCell::Cell(reference) => {
                    (krs_ir::MainCell::Cell(identity(&reference.cell)?), None)
                }
                krs_ir::MainCell::NoComputationCell => (krs_ir::MainCell::NoComputationCell, None),
                krs_ir::MainCell::Ambiguous {
                    cells: initialized,
                    reading,
                } => {
                    // The cells in declaration order, as the configuration's lowering names them.
                    let initialized = initialized
                        .into_iter()
                        .map(|reference| identity(&reference.cell))
                        .collect::<Result<HashSet<_>, _>>()?;
                    let declared = cells
                        .iter()
                        .filter(|cell| initialized.contains(&cell.identity))
                        .collect::<Vec<_>>();
                    let names = declared
                        .iter()
                        .map(|cell| cell.k_name.as_str())
                        .collect::<Vec<_>>();
                    let refusal = CollectionError::new(
                        CollectionErrorKind::MainCell,
                        krs_ir::ambiguous_main_cell_refusal(
                            descriptor.id.item_name(),
                            &names,
                            reading,
                        ),
                    )
                    .with_reference_key(configuration.initializer.key.clone());
                    (
                        krs_ir::MainCell::Ambiguous {
                            cells: declared.iter().map(|cell| cell.identity.clone()).collect(),
                            reading,
                        },
                        Some(refusal),
                    )
                }
            };
            Ok(HeadRuleTarget {
                configuration: descriptor.id.clone(),
                main,
                main_refusal,
                group_children,
                groups: configuration_groups(&cells),
                cells,
                subject: None,
                subjects: Vec::new(),
                configuration_keys: Vec::new(),
            }
            .with_subjects())
        })
        .collect::<Result<Vec<_>, CollectionError>>()?;
    // Each rule that needs one configuration, or one computation cell, checks it as it is
    // resolved, so the error is located at that rule.
    Ok(targets)
}

/// The groups of a configuration whose cells are `cells`, which the entry-admission table reads:
/// those its record-level cells' layers hold, at any depth.
fn configuration_groups(cells: &[HeadRuleCellTarget]) -> Vec<krs_ir::cell_kind::GroupKind> {
    let mut groups = Vec::new();
    for cell in cells.iter().filter(|cell| cell.path.layers.is_empty()) {
        krs_syntax::cell_entries::collect_groups(&cell.kind.layers, &mut groups);
    }
    groups
}

/// `a`, `b` and `c` for a message.
fn names<'a>(names: impl Iterator<Item = &'a str>) -> String {
    names
        .map(|name| format!("`{name}`"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Whether the descriptors hold a head rule or a sentence typed by a cell group, which the
/// configurations' targets resolve.
fn needs_targets(
    pending: &[PendingDescriptor],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> bool {
    pending.iter().any(|descriptor| {
        matches!(descriptor.host.payload, HostDescriptorPayload::HeadRule(_))
            || configuration_references(&descriptor.host.payload)
                .any(|reference| names_group(reference, declarations))
    })
}

/// The configuration references a host payload's sentences are typed by.
fn configuration_references(
    payload: &HostDescriptorPayload,
) -> impl Iterator<Item = &krs_ir::HostConfigurationReference> {
    let references: [Option<&krs_ir::HostConfigurationReference>; 2] = match payload {
        HostDescriptorPayload::ConfigurationRule(rule) => [
            Some(&rule.subject_configuration),
            rule.result_configuration.as_ref(),
        ],
        HostDescriptorPayload::ContextAlias(alias) => [Some(&alias.configuration), None],
        HostDescriptorPayload::StructuredRule(rule) => [
            rule.function_context
                .as_ref()
                .map(|context| &context.configuration),
            None,
        ],
        HostDescriptorPayload::HeadRule(rule) => [rule.configuration.as_ref(), None],
        _ => [None, None],
    };
    references.into_iter().flatten()
}

/// Whether `reference` names a `#[k::cell]` group, as a sentence typed by a group does.
fn names_group(
    reference: &krs_ir::HostConfigurationReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> bool {
    matches!(
        declarations.get(&HostApplicationIdentity::Nominal(
            reference.configuration.key.resolve()
        )),
        Some((_, ItemKind::Cell))
    )
}

/// What a sentence's configuration type names: a configuration, or a cell group.
enum TypedBy {
    Configuration(StableItemId),
    Group(StableItemId),
}

/// Resolves the type of a configuration-typed sentence: a `#[k::configuration]`, or a
/// `#[k::cell]` group, which types a sentence about the group's cells.
fn resolve_typed_by(
    reference: &krs_ir::HostConfigurationReference,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<TypedBy, CollectionError> {
    if let Some((group, ItemKind::Cell)) = declarations.get(&HostApplicationIdentity::Nominal(
        reference.configuration.key.resolve(),
    )) {
        return Ok(TypedBy::Group(group.clone()));
    }
    resolve_nominal_reference(
        &reference.configuration,
        ItemKind::Configuration,
        declarations,
    )
    .map(TypedBy::Configuration)
}

/// The refusal of a claim typed by the cell group `group`.
fn group_claim(group: &StableItemId) -> CollectionError {
    CollectionError::new(
        CollectionErrorKind::GroupClaim,
        format!(
            "a claim is typed by its definition's configuration, not by the cell group `{group}`: a claim states what the definition's transition system does and leaves every cell it does not name unchanged, so the same claim would state something else in each configuration that holds `{group}`; write the claim for the configuration",
            group = group.item_name(),
        ),
    )
}

/// The refusal of a `k::patterns!` block typed by the cell group `group` (FB-49).
fn group_pattern(group: &StableItemId) -> CollectionError {
    CollectionError::new(
        CollectionErrorKind::GroupPattern,
        format!(
            "a pattern typed by the cell group `{group}` is not supported yet: a pattern is about its definition's states, and is written for the configuration, which names the group's cells flat",
            group = group.item_name(),
        ),
    )
}

/// The definition's one configuration scoped to the cell group `group`: a sentence typed by a
/// group is about the group's cells at its one position in that configuration.
fn group_target<'a>(
    group: &StableItemId,
    targets: &'a [HeadRuleTarget],
) -> Result<&'a HeadRuleTarget, CollectionError> {
    let name = group.item_name();
    let [target] = targets else {
        let detail = match targets {
            [] => format!(
                "this rule is for the cell group `{name}`, but the definition has no `#[k::configuration]`: `{name}` is a cell group, not a configuration, and rules for a group are checked through a definition whose configuration holds it"
            ),
            several => format!(
                "this rule is for the cell group `{name}`, but the definition declares {} configurations, {}; a definition has exactly one",
                several.len(),
                names(
                    several
                        .iter()
                        .map(|target| target.configuration.item_name())
                ),
            ),
        };
        return Err(CollectionError::new(
            CollectionErrorKind::ConfigurationCount,
            detail,
        ));
    };
    match target
        .subjects
        .iter()
        .find(|(declaration, _)| declaration == group)
    {
        Some((_, Ok(scoped))) => Ok(scoped),
        Some((_, Err(refusal))) => Err(refusal.clone()),
        None => Err(target.subject_refusal(group, &krs_ir::SubjectError::NotInConfiguration)),
    }
}

/// The fixed configuration a head rule names, or the only one collected; for a rule typed by a
/// cell group, the only one scoped to the group.
pub(super) fn select_head_rule_target<'a>(
    rule: &krs_ir::HostHeadRule,
    targets: &'a [HeadRuleTarget],
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
) -> Result<&'a HeadRuleTarget, CollectionError> {
    Ok(if let Some(configuration) = &rule.configuration {
        match resolve_typed_by(configuration, declarations)? {
            TypedBy::Configuration(selected) => targets
                .iter()
                .find(|target| target.configuration == selected)
                .ok_or_else(|| {
                    CollectionError::new(
                        CollectionErrorKind::InvalidConfiguration,
                        "cell-record rule names a fixed configuration that was not collected",
                    )
                })?,
            TypedBy::Group(group) => if rule
                .claim
                .as_ref()
                .is_some_and(|claim| claim.pattern.is_some())
            {
                Err(group_pattern(&group))
            } else if rule.sentence_kind == krs_ir::SentenceKind::Claim {
                Err(group_claim(&group))
            } else {
                group_target(&group, targets)
            }
            .map_err(|error| error.with_reference_key(configuration.key.clone()))?,
        }
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
    let owner = target.owner();
    let no_computation = || {
        CollectionError::new(
            CollectionErrorKind::ComputationCell,
            format!(
                "this rule rewrites the head of the computation, but {owner} has no `KSequence` cell to hold the computation"
            ),
        )
    };
    // A record names its computation cell; a rule that names none rewrites the configuration's
    // main cell, the computation every sentence that names no cell runs in.
    let computation = if let Some(named) = &rule.computation_cell {
        let computations = target
            .cells
            .iter()
            .filter(|cell| cell.kind.is_computation() && cell.names.contains(&named.name))
            .collect::<Vec<_>>();
        match computations.as_slice() {
            [computation] => *computation,
            [] => {
                let named_cell = target
                    .cells
                    .iter()
                    .any(|cell| cell.names.contains(&named.name));
                if !named_cell && let Some(outside) = target.outside(&named.name) {
                    return Err(outside.with_reference_key(named.key.clone()));
                }
                let holder = if target.subject.is_some() {
                    "group"
                } else {
                    "configuration"
                };
                return Err(CollectionError::new(
                    CollectionErrorKind::ComputationCell,
                    if named_cell {
                        format!(
                            "this rule rewrites the head of the computation in the cell `{}` of {owner}, which is not a `KSequence` cell: name the {holder}'s `KSequence` cell that holds the computation",
                            named.name
                        )
                    } else {
                        format!(
                            "this rule rewrites the head of the computation in the cell `{}`, which {owner} does not have",
                            named.name
                        )
                    },
                ));
            }
            several => {
                return Err(CollectionError::new(
                    CollectionErrorKind::ComputationCell,
                    format!(
                        "this rule rewrites the head of the computation in the cell `{}`, which names {} `KSequence` cells of {owner}, {}: name the cell by a name only it has",
                        named.name,
                        several.len(),
                        names(several.iter().map(|cell| cell.k_name.as_str())),
                    ),
                ));
            }
        }
    } else {
        match &target.main {
            krs_ir::MainCell::Cell(main) => target
                .cells
                .iter()
                .find(|cell| &cell.identity == main)
                .ok_or_else(no_computation)?,
            krs_ir::MainCell::NoComputationCell => return Err(no_computation()),
            // The configuration has no main cell, its own mistake: the rule reports the
            // configuration's refusal, at its initializer, and adds none.
            krs_ir::MainCell::Ambiguous { .. } => {
                return Err(target.main_refusal.clone().unwrap_or_else(|| {
                    CollectionError::new(
                        CollectionErrorKind::InvalidConfiguration,
                        "a configuration without a main cell has no refusal",
                    )
                }));
            }
        }
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
    /// Whether the payload is a claim, which a cell group may not type.
    claim: bool,
    /// The configuration scoped to the cell group the payload's sentence is typed by, absent for
    /// a sentence typed by the configuration: every cell the sentence names is inside the group.
    subject_target: Option<&'a HeadRuleTarget>,
    allow_builtin_application: bool,
    /// The generated marker type of each sort parameter of this payload's
    /// parametric production, by its declared name (KF-027).
    parameters: HashMap<TypeId, String>,
    /// The keys of the nodes only a reading the collector did not keep
    /// denotes, whose anchors the descriptor drops.
    discarded: BTreeSet<krs_ir::ProvenanceKey>,
    /// The applications whose path the host stage read as a set's singleton
    /// ([`krs_ir::names_set_element`]) and which resolve to something else.
    misread_elements: BTreeSet<krs_ir::ProvenanceKey>,
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
        let resolved = resolve_application_reference(
            &reference,
            self.declarations,
            self.builtins,
            self.allow_builtin_application,
        )
        .map_err(|error| error.with_reference_key(reference.key.clone()))?;
        if krs_ir::names_set_element(reference.target.authored_path())
            && resolved.application
                != krs_ir::DescriptorApplicationRef::Set(krs_ir::SetOperation::Item)
        {
            self.misread_elements.insert(reference.key);
        }
        Ok(resolved)
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
                subject: selection.target.descriptor_subject(),
            });
        }
        let resolved = match resolve_typed_by(&reference, self.declarations) {
            Ok(TypedBy::Configuration(configuration)) => Ok((configuration, None)),
            Ok(TypedBy::Group(group)) if self.claim => Err(group_claim(&group)),
            Ok(TypedBy::Group(group)) => group_target(&group, self.head_targets)
                .map(|target| (target.configuration.clone(), target.descriptor_subject())),
            Err(error) => Err(error),
        };
        match resolved {
            Ok((configuration, subject)) => Ok(krs_ir::DescriptorConfigurationReference {
                key: reference.key,
                configuration,
                subject,
            }),
            Err(error) => Err(error.with_reference_key(reference.key)),
        }
    }

    fn cell(
        &mut self,
        reference: krs_ir::HostCellReference,
    ) -> Result<krs_ir::DescriptorCellReference, Self::Error> {
        let resolved = resolve_cell_reference(&reference, self.cell_fields)
            .map_err(|error| error.with_reference_key(reference.key.clone()))?;
        let target = self
            .head_selection
            .as_ref()
            .map(|selection| selection.target)
            .or(self.subject_target);
        match target.and_then(|target| target.outside_cell(&resolved.cell)) {
            Some(outside) => Err(outside.with_reference_key(reference.key)),
            None => Ok(resolved),
        }
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
            if matches.is_empty()
                && let Some(outside) = selection.target.outside(&reference.name)
            {
                return Err(outside.with_reference_key(reference.key));
            }
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

    fn parent(
        &mut self,
        reference: HostSortReference,
    ) -> Result<krs_ir::DescriptorSortParent, Self::Error> {
        match resolve_nominal_reference(&reference.target, ItemKind::Sort, self.declarations) {
            Ok(sort) => Ok(krs_ir::DescriptorSortParent {
                sort,
                key: reference.key,
            }),
            Err(error) => Err(error.with_reference_key(reference.key)),
        }
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
    ) -> Result<DescriptorSortReference, Self::Error> {
        let sort = if let Some(name) = self.parameters.get(&reference.target.key.resolve()) {
            DescriptorSortRef::Parameter(name.clone())
        } else {
            resolve_constructor_field_sort(&reference.target, self.declarations, self.builtins)
                .map_err(|error| error.with_reference_key(reference.key.clone()))?
        };
        Ok(DescriptorSortReference {
            key: reference.key,
            sort,
        })
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
/// application's head, path and field keys become the cell term's, as the
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
/// and the records below a value are read by [`group_record_term`]. A
/// record's authored `..` is kept on either side, as its `k::fragment!` twin
/// keeps it: what it means where it stands (a result's record of a group
/// that is there keeps the children it leaves unnamed) and where it may
/// stand are the entry's admission's to say.
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
            authored_open
                || (subject
                    && position == Some(target)
                    && groups
                        .children
                        .get(&target)
                        .is_some_and(|children| fields < children.count))
        },
    );
    // A record at its group's own position, written bare or as
    // `k::fragment!`, holds its fixed group children at theirs.
    let Term::Cell {
        key,
        path_key,
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
        path_key,
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
        path_key,
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
    // The record's path names the group's declaration, as a fragment's
    // does, and keeps its key.
    Term::Cell {
        key: reference.key,
        path_key,
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
/// a list cell, or is reported as naming neither. An item-less `[..]` is
/// carried as `_` beside its instance list (`read_machine_clause`'s reading):
/// every cell but a `Cell` leaf takes the instance list. Only a cell-record
/// clause
/// carries a List reading: the syntax reads a table clause's (`for Sort;
/// pattern => result`) values one way and gives it no alternative, so it is
/// returned as it is.
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
    // An item-less `[..]` is read as `_` with its instance list beside it.
    // `_` is what it means on a `Cell` leaf. The computation cell has no `_`
    // entry (its entry is its items in brackets) and keeps the instance
    // list, as every other cell does, whose kind's mistake it names.
    let keeps_instances = |candidate: &HeadRuleCellTarget| {
        candidate.is_collection()
            || (item_less_brackets(&alternative.extra).is_some()
                && candidate.leaf_wrapper() != Some(krs_ir::CellWrapper::Cell))
    };
    if let [candidate] = named.as_slice()
        && keeps_instances(candidate)
    {
        if rule
            .computation_cell
            .as_ref()
            .is_some_and(|computation| computation.name == cell.name)
        {
            rule.head = None;
            rule.computation_cell = None;
        }
        rule.extras.retain(|extra| {
            !matches!(
                extra,
                krs_ir::ProtocolHeadRuleExtra::RewriteList { cell: read, .. }
                    | krs_ir::ProtocolHeadRuleExtra::RewriteCell { cell: read, .. }
                    if read.name == cell.name
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
            || item_less_brackets(extra).is_some()
    });
    if rule.configuration.is_none() || (rule.computation_cell.is_none() && !has_list) {
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
            [cell] => cell.leaf_wrapper(),
            _ => None,
        }
    };
    if let Some(computation) = &rule.computation_cell
        && rule.head.is_some()
        && wrapper(&computation.name) == Some(krs_ir::CellWrapper::Cell)
    {
        let head = rule.head.take().expect("checked above");
        let computation = rule.computation_cell.take().expect("checked above");
        rule.extras.push(head_list(head, computation));
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
        rule.computation_cell = Some(krs_ir::HeadRuleComputationCell {
            key: cell.key,
            name: cell.name,
            result_key,
        });
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
    // `[..]` names no item, element or instance, so it matches whatever the
    // cell holds and keeps it. The macro reads the first such value as `_`
    // with its instance list beside it, which a `Cell` leaf keeps
    // ([`readable_bracket_reading`]). The instance list that remains on a
    // leaf (the computation cell's, or a value beside another carried
    // reading) constrains and binds nothing, so the rule is the rule that
    // leaves the cell out.
    rule.extras.retain(|extra| {
        item_less_brackets(extra).is_none_or(|cell| {
            !matches!(
                wrapper(&cell.name),
                Some(krs_ir::CellWrapper::Cell | krs_ir::CellWrapper::KCell)
            )
        })
    });
    Ok(rule)
}

/// The cell of a state extra that matches the bracketed instance list `[..]`,
/// which names nothing but its anonymous rest, and leaves the cell out of the
/// result or writes `[..]` again.
fn item_less_brackets(
    extra: &krs_ir::HostHeadRuleExtra,
) -> Option<&krs_ir::HostHeadRuleCellReference> {
    let is_item_less = |state: &krs_ir::ProtocolRuleStateTerm<krs_ir::HostTerm>| {
        matches!(
            state,
            krs_ir::ProtocolRuleStateTerm::Instances(instances)
                if instances.delimiter == krs_ir::InstanceDelimiter::Bracket
                    && instances.front.is_empty()
                    && instances.back.is_empty()
                    && matches!(instances.rest, krs_ir::ProtocolRuleFrame::Anonymous { .. })
        )
    };
    match extra {
        krs_ir::ProtocolHeadRuleExtra::RewriteState {
            cell,
            before,
            after,
            ..
        } if is_item_less(before) && after.as_ref().is_none_or(is_item_less) => Some(cell),
        _ => None,
    }
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

/// The list reading of the head `head` read on the ordinary cell
/// `computation`: the same items, with the anonymous `..` as the list's
/// shared rest, in the cell the record names.
fn head_list(
    head: krs_ir::ProtocolHeadRuleHead<krs_ir::HostTerm>,
    computation: krs_ir::HeadRuleComputationCell,
) -> krs_ir::HostHeadRuleExtra {
    // The head's `..` is the list's shared rest: the subject defines it,
    // the result names it.
    let rest = || {
        if head.exact {
            krs_ir::ProtocolHeadRuleListRest::Exact
        } else {
            krs_ir::ProtocolHeadRuleListRest::Shared(head.tail_key.clone())
        }
    };
    let after = head.result.map(|result| krs_ir::ProtocolHeadRuleList {
        items: match result {
            krs_ir::ProtocolHeadRuleResult::Replace(term) => vec![term],
            // A list's elements carry no keys: the splice's sequence and
            // items are nodes of the discarded reading.
            krs_ir::ProtocolHeadRuleResult::Splice(splice) => splice.into_terms(),
            krs_ir::ProtocolHeadRuleResult::Erase => Vec::new(),
        },
        rest: rest(),
        back: Vec::new(),
    });
    krs_ir::ProtocolHeadRuleExtra::RewriteList {
        cell: krs_ir::HostHeadRuleCellReference {
            key: computation.key,
            name: computation.name,
        },
        result_key: computation.result_key,
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
    // The list's shared rest is the head's kept tail, the same `..`.
    let (exact, tail_key) = match before.rest {
        krs_ir::ProtocolHeadRuleListRest::Exact => (true, None),
        krs_ir::ProtocolHeadRuleListRest::Shared(key) => (false, key),
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
            // A list's value and elements are no sequence the sentence
            // keyed: the splice carries no keys.
            Err(items) => krs_ir::ProtocolHeadRuleResult::Splice(krs_ir::ProtocolHeadRuleSplice {
                payload_key: None,
                items: items
                    .into_iter()
                    .map(|value| krs_ir::ProtocolHeadRuleSpliceItem { key: None, value })
                    .collect(),
            }),
        }),
    };
    Ok(krs_ir::ProtocolHeadRuleHead {
        items: before.items,
        exact,
        tail_key,
        result,
    })
}

fn resolve_head_rule(
    rule: krs_ir::HostHeadRule,
    map: &mut Resolver<'_>,
) -> Result<krs_ir::DescriptorHeadRule, CollectionError> {
    // A cell-record clause's bracketed and list values read two ways: the
    // nodes only the readings it discards denote go with them. A table
    // clause reads each value one way (its syntax gives it no bracket
    // alternative, and only a cell-record clause's sequence values are read
    // again), so it discards nothing and is not compared.
    let authored = rule
        .configuration
        .as_ref()
        .map(|_| carried_keys(&rule))
        .transpose()?;
    let rule = readable_bracket_reading(rule, map.head_targets, map.declarations)?;
    let rule = readable_list_reading(rule, map.head_targets, map.declarations)?;
    if let Some(authored) = authored {
        let kept = carried_keys(&rule)?;
        map.discarded.extend(authored.difference(&kept).cloned());
    }
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
    // A cell-record clause names its configuration and its computation
    // cell; a table clause names neither.
    let configuration_key = rule
        .configuration
        .as_ref()
        .map(|configuration| configuration.key.clone());
    let named = rule.computation_cell.as_ref();
    let computation_cell =
        selection
            .computation
            .map(|computation| krs_ir::DescriptorComputationCell {
                cell: computation.identity.clone(),
                key: named.map(|named| named.key.clone()),
                result_key: named.and_then(|named| named.result_key.clone()),
            });
    Ok(krs_ir::DescriptorHeadRule::from_selected(
        rule,
        selection.target.configuration.clone(),
        configuration_key,
        selection.target.descriptor_subject(),
        computation_cell,
    ))
}

/// The keys a readable clause's nodes carry; a clause the expander built
/// passed this check already, so a failure is the collector's.
fn carried_keys(
    rule: &krs_ir::HostHeadRule,
) -> Result<BTreeSet<krs_ir::ProvenanceKey>, CollectionError> {
    rule.carried_keys().map_err(|error| {
        let failure = CollectionError::new(
            CollectionErrorKind::ProvenanceMismatch,
            format!("a reading of the readable rule disagrees with its keys: {error}"),
        );
        match error.at() {
            Some(key) => failure.with_reference_key(key.clone()),
            None => failure,
        }
    })
}

/// Resolves a host payload, with the keys of the nodes only a reading it
/// discarded denotes (a readable rule's other reading of a bracketed or
/// list value), whose anchors the descriptor drops.
#[cfg(test)]
pub(super) fn resolve_payload(
    payload: &HostDescriptorPayload,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    context_aliases: &HashMap<HostItemId, StableItemId>,
    builtins: Option<&HostBuiltinRegistry>,
    head_targets: &[HeadRuleTarget],
) -> Result<(DescriptorPayload, BTreeSet<krs_ir::ProvenanceKey>), CollectionError> {
    resolve_payload_reading(
        payload,
        declarations,
        cell_fields,
        context_aliases,
        builtins,
        head_targets,
    )
    .map(|resolved| (resolved.payload, resolved.discarded))
}

/// A descriptor payload resolved, with what its resolution tells beyond the payload.
pub(super) struct ResolvedPayload {
    pub(super) payload: DescriptorPayload,
    /// The anchors the descriptor drops ([`Resolver::discarded`]).
    pub(super) discarded: BTreeSet<krs_ir::ProvenanceKey>,
    /// Whether an application whose path reads as a set's singleton resolves to something else
    /// ([`Resolver::misread_elements`]).
    pub(super) misreads_set_element: bool,
}

/// [`resolve_payload`], also telling whether a path that reads as a set's singleton resolves to
/// something else.
pub(super) fn resolve_payload_reading(
    payload: &HostDescriptorPayload,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    cell_fields: &HashMap<HostCellKey, krs_ir::DescriptorCellIdentity>,
    context_aliases: &HashMap<HostItemId, StableItemId>,
    builtins: Option<&HostBuiltinRegistry>,
    head_targets: &[HeadRuleTarget],
) -> Result<ResolvedPayload, CollectionError> {
    let claim = matches!(
        payload,
        HostDescriptorPayload::ConfigurationRule(rule)
            if rule.sentence_kind == krs_ir::ConfigurationSentenceKind::Claim
    );
    let mut map = Resolver {
        declarations,
        cell_fields,
        context_aliases,
        builtins,
        head_targets,
        head_selection: None,
        claim,
        subject_target: if claim {
            None
        } else {
            group_subject_target(payload, declarations, head_targets)
        },
        allow_builtin_application: !matches!(payload, HostDescriptorPayload::Grammar(_)),
        parameters: sort_parameters(payload),
        discarded: BTreeSet::new(),
        misread_elements: BTreeSet::new(),
    };
    let payload = payload
        .clone()
        .try_map_refs(&mut map, &mut resolve_head_rule)?;
    Ok(ResolvedPayload {
        payload,
        discarded: map.discarded,
        misreads_set_element: !map.misread_elements.is_empty(),
    })
}

/// The configuration scoped to the cell group `payload`'s sentence is typed by, where it is typed
/// by a group that has one; a reference that does not resolve so is refused where it is resolved.
fn group_subject_target<'a>(
    payload: &HostDescriptorPayload,
    declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
    head_targets: &'a [HeadRuleTarget],
) -> Option<&'a HeadRuleTarget> {
    configuration_references(payload).find_map(|reference| {
        match resolve_typed_by(reference, declarations) {
            Ok(TypedBy::Group(group)) => group_target(&group, head_targets).ok(),
            _ => None,
        }
    })
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
        } else if let Some(method) =
            builtins.and_then(|registry| registry.resolve_collection_method(type_id))
        {
            DescriptorApplicationRef::CollectionMethod(method)
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

    const MARKER_COUNT: usize = 224;

    fn marker_table() -> [fn() -> TypeId; MARKER_COUNT] {
        marker_table!(
            0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
            33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61
            62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90
            91 92 93 94 95 96 97 98 99 100 101 102 103 104 105 106 107 108 109 110 111 112 113 114
            115 116 117 118 119 120 121 122 123 124 125 126 127 128 129 130 131 132 133 134 135 136
            137 138 139 140 141 142 143 144 145 146 147 148 149 150 151 152 153 154 155 156 157 158
            159 160 161 162 163 164 165 166 167 168 169 170 171 172 173 174 175 176 177 178 179 180
            181 182 183 184 185 186 187 188 189 190 191 192 193 194 195 196 197 198 199 200 201 202
            203 204 205 206 207 208 209 210 211 212 213 214 215 216 217 218 219 220 221 222 223
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
    const COLLECTION_METHOD_OFFSET: usize = LIST_NOTATION_OFFSET + krs_ir::ListNotation::ALL.len();
    const _: () =
        assert!(COLLECTION_METHOD_OFFSET + krs_ir::CollectionMethod::ALL.len() <= MARKER_COUNT);

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
            collection_methods: keys(COLLECTION_METHOD_OFFSET),
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
            spelling_key: ProvenanceKey::new(krs_ir::ProvenanceRole::ClaimAnonymousSpelling, 0),
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
            unobservable: None,
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
            absent: None,
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
            claim: false,
            subject_target: None,
            allow_builtin_application: true,
            discarded: BTreeSet::new(),
            misread_elements: BTreeSet::new(),
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
            skipped_operand: None,
            pattern_key: key.clone(),
            result_key: key.clone(),
            head_sort: Some(unresolved_sort("Header")),
            configuration: None,
            result_type_key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleResultType, 0),
            computation_cell: None,
            bindings: Vec::new(),
            head: Some(krs_ir::ProtocolHeadRuleHead {
                items: vec![unresolved_term("Subject")],
                exact: false,
                tail_key: None,
                result: Some(krs_ir::ProtocolHeadRuleResult::Replace(unresolved_term(
                    "Result",
                ))),
            }),
            requires: None,
            extras: vec![krs_ir::ProtocolHeadRuleExtra::HaveMap {
                rest_key: None,
                cell: krs_ir::HostHeadRuleCellReference {
                    key,
                    name: "missing".to_owned(),
                },
                entries: vec![krs_ir::ProtocolHeadRuleMapEntry {
                    key_key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleLeftMapKey, 0),
                    key: unresolved_term("Extra"),
                    value_key: ProvenanceKey::new(krs_ir::ProvenanceRole::RuleLeftMapValue, 0),
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
        let main = krs_ir::MainCell::Cell(identity.clone());
        let target = configuration_target(
            identity.owner.clone(),
            vec![HeadRuleCellTarget {
                identity,
                names: vec!["k".to_owned()],
                k_name: "k".to_owned(),
                kind: CellKind {
                    layers: vec![Layer::Computation],
                },
                path: CellKind::default(),
                group: None,
                ancestor: None,
                sort: None,
                parent: None,
                group_id: None,
            }],
            main,
        );
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
            path_key,
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
        assert_eq!(
            path_key,
            ProvenanceKey::new(krs_ir::ProvenanceRole::RuleLeftPath, 3)
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

    /// `for State; name: { stack: [x, ..] } => { stack: [x, x, ..] }` and
    /// its mirror on `k`, with the configuration `State { k: KCell, stack:
    /// Cell }`: the head read on the ordinary cell `stack` becomes its list,
    /// the list read on the computation cell `k` its head.
    fn list_reading_clause(cell: &str, as_head: bool) -> krs_ir::HostHeadRule {
        use krs_ir::ProvenanceRole as Role;
        let key = ProvenanceKey::new;
        let variable = |side: [Role; 2], ordinal| krs_ir::HostTerm::Variable {
            key: key(side[0], ordinal),
            path_key: key(side[1], ordinal),
            name: "x".to_owned(),
        };
        let left = [Role::RuleLeftReference, Role::RuleLeftPath];
        let right = [Role::RuleRightReference, Role::RuleRightPath];
        let mut rule = krs_ir::HostHeadRule {
            sentence_kind: krs_ir::SentenceKind::Transition,
            label: None,
            priority: None,
            nondet: None,
            skipped_operand: None,
            pattern_key: key(Role::RulePattern, 0),
            result_key: key(Role::RuleResult, 0),
            head_sort: None,
            configuration: Some(krs_ir::HostConfigurationReference {
                key: key(Role::RuleType, 0),
                configuration: HostTypeReference {
                    key: HostTypeKey(boolean_key),
                    authored_path: "State".to_owned(),
                },
            }),
            result_type_key: key(Role::RuleResultType, 0),
            computation_cell: None,
            bindings: vec![krs_ir::ProtocolHeadRuleBinding {
                name: "x".to_owned(),
                refinement: None,
            }],
            head: None,
            requires: None,
            extras: Vec::new(),
            existentials: Vec::new(),
            ensures: None,
            fresh: Vec::new(),
            evaluation: None,
            bracket_alternative: None,
            claim: None,
        };
        if as_head {
            rule.computation_cell = Some(krs_ir::HeadRuleComputationCell {
                key: key(Role::RuleLeftCellsField, 0),
                name: cell.to_owned(),
                result_key: Some(key(Role::RuleRightCellsField, 0)),
            });
            rule.head = Some(krs_ir::ProtocolHeadRuleHead {
                items: vec![variable(left, 0)],
                exact: false,
                tail_key: None,
                result: Some(krs_ir::ProtocolHeadRuleResult::Splice(
                    krs_ir::ProtocolHeadRuleSplice {
                        payload_key: Some(key(Role::RuleRightKSequencePayload, 0)),
                        items: (0..2)
                            .map(|ordinal| krs_ir::ProtocolHeadRuleSpliceItem {
                                key: Some(key(Role::RuleRightKSequenceItem, ordinal)),
                                value: variable(right, ordinal),
                            })
                            .collect(),
                    },
                )),
            });
        } else {
            let list = |items| krs_ir::ProtocolHeadRuleList {
                items,
                rest: krs_ir::ProtocolHeadRuleListRest::Shared(None),
                back: Vec::new(),
            };
            rule.extras
                .push(krs_ir::ProtocolHeadRuleExtra::RewriteList {
                    cell: krs_ir::HostHeadRuleCellReference {
                        key: key(Role::RuleLeftCellsField, 0),
                        name: cell.to_owned(),
                    },
                    result_key: Some(key(Role::RuleRightCellsField, 0)),
                    before: list(vec![variable(left, 0)]),
                    after: Some(list(vec![variable(right, 0), variable(right, 1)])),
                });
        }
        rule
    }

    fn state_id() -> StableItemId {
        StableItemId::new(
            PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap(),
            ["model"],
            "State",
            ItemKind::Configuration,
            "",
        )
        .unwrap()
    }

    /// A leaf cell `name` of the configuration `State`.
    fn state_cell(
        name: &str,
        wrapper: Option<krs_ir::CellWrapper>,
        collection: bool,
    ) -> HeadRuleCellTarget {
        HeadRuleCellTarget {
            identity: krs_ir::DescriptorCellIdentity {
                owner: state_id(),
                field: name.to_owned(),
            },
            names: vec![name.to_owned()],
            k_name: name.to_owned(),
            kind: CellKind {
                layers: collection
                    .then_some(Layer::Instances(krs_ir::cell_kind::Order::List))
                    .into_iter()
                    .chain([match wrapper {
                        Some(krs_ir::CellWrapper::KCell) => Layer::Computation,
                        Some(krs_ir::CellWrapper::Cell) => Layer::Leaf(Notation::Plain),
                        None => Layer::Group(krs_ir::cell_kind::GroupKind {
                            name: name.to_owned(),
                            children: Vec::new(),
                        }),
                    }])
                    .collect(),
            },
            path: CellKind::default(),
            group: None,
            ancestor: None,
            sort: None,
            parent: None,
            group_id: None,
        }
    }

    /// Resolves the readable clause `rule` for the configuration `State`
    /// and returns it with the keys of the nodes only the reading it
    /// discarded denotes. The resolved clause is closed over the anchors
    /// that remain: a clause's anchors are the keys it carries, its
    /// declaration's included.
    fn resolve_reading(
        rule: krs_ir::HostHeadRule,
        declarations: &HashMap<HostApplicationIdentity, (StableItemId, ItemKind)>,
        cells: Vec<HeadRuleCellTarget>,
    ) -> (krs_ir::DescriptorHeadRule, BTreeSet<ProvenanceKey>) {
        // The main cell of a configuration whose computation cells the test lists, none of
        // which reads a program.
        let main = krs_ir::select_main_cell(
            cells
                .iter()
                .filter(|cell| cell.kind.is_computation())
                .map(|cell| (cell.identity.clone(), false)),
        );
        let targets = [configuration_target(state_id(), cells, main)];
        let anchors = rule.carried_keys().unwrap();
        let (payload, discarded) = resolve_payload(
            &HostDescriptorPayload::HeadRule(Box::new(rule)),
            declarations,
            &HashMap::new(),
            &HashMap::new(),
            None,
            &targets,
        )
        .unwrap();
        let DescriptorPayload::HeadRule(resolved) = payload else {
            unreachable!("a head rule resolves to a head rule")
        };
        let kept = anchors.difference(&discarded).collect::<Vec<_>>();
        assert_eq!(resolved.validate(ItemKind::Rule), Ok(()));
        assert_eq!(resolved.validate_complete_provenance(kept), Ok(()));
        (*resolved, discarded)
    }

    /// The collector keeps one reading of a sequence value, and the anchors
    /// only the other reading's nodes hold go: a head read as a list drops
    /// its splice's sequence and items, whose elements the list keeps, and
    /// a list read as the head is a splice that carries no key. Either way
    /// the resolved clause is closed over the anchors that remain, its
    /// computation cell or its list keyed at the cell's own names.
    #[test]
    fn a_discarded_sequence_reading_drops_its_own_anchors() {
        let declarations = HashMap::from([(
            HostApplicationIdentity::Nominal(boolean_key()),
            (state_id(), ItemKind::Configuration),
        )]);
        let resolve = |rule| {
            resolve_reading(
                rule,
                &declarations,
                vec![
                    state_cell("k", Some(krs_ir::CellWrapper::KCell), false),
                    state_cell("stack", Some(krs_ir::CellWrapper::Cell), false),
                ],
            )
        };

        let (head_as_list, discarded) = resolve(list_reading_clause("stack", true));
        assert_eq!(
            discarded,
            BTreeSet::from([
                krs_ir::ProvenanceRole::RuleRightKSequencePayload.key(0),
                krs_ir::ProvenanceRole::RuleRightKSequenceItem.key(0),
                krs_ir::ProvenanceRole::RuleRightKSequenceItem.key(1),
            ])
        );
        assert!(head_as_list.computation_cell.is_none());
        assert!(matches!(
            head_as_list.extras.as_slice(),
            [krs_ir::ProtocolHeadRuleExtra::RewriteList { cell, result_key: Some(result), .. }]
                if cell.key == krs_ir::ProvenanceRole::RuleLeftCellsField.key(0)
                    && *result == krs_ir::ProvenanceRole::RuleRightCellsField.key(0)
        ));

        let (list_as_head, discarded) = resolve(list_reading_clause("k", false));
        assert!(discarded.is_empty());
        assert_eq!(
            list_as_head.computation_cell,
            Some(krs_ir::DescriptorComputationCell {
                cell: krs_ir::DescriptorCellIdentity {
                    owner: state_id(),
                    field: "k".to_owned(),
                },
                key: Some(krs_ir::ProvenanceRole::RuleLeftCellsField.key(0)),
                result_key: Some(krs_ir::ProvenanceRole::RuleRightCellsField.key(0)),
            })
        );
        assert!(matches!(
            list_as_head.head.and_then(|head| head.result),
            Some(krs_ir::ProtocolHeadRuleResult::Splice(splice))
                if splice.payload_key.is_none() && splice.items.iter().all(|item| item.key.is_none())
        ));
    }

    struct Job;
    struct JobSort;

    /// `for State; name: { cell: [j @ Job { payload: p }, ..] } => { cell:
    /// [..] } where j: JobSort`, carried in its computation-cell reading,
    /// the head `[j @ Job { .. }, ..]` rewritten to `[..]`, with the List
    /// reading of `cell` beside it: a front instance labelled `j` whose
    /// `payload` child is the record's `p`, then `..`, rewritten to `[..]`.
    /// Each reading keys its own cell names; the List reading's instance
    /// structure is its own, and its child terms are the head's.
    fn bracket_reading_clause(cell: &str) -> krs_ir::HostHeadRule {
        use krs_ir::ProvenanceRole as Role;
        let key = ProvenanceKey::new;
        let job = krs_ir::HostTerm::As {
            key: key(Role::PatternAs, 0),
            binding_key: key(Role::PatternAsBinding, 0),
            name: "j".to_owned(),
            pattern: Box::new(krs_ir::HostTerm::Application {
                head_class: krs_ir::DescriptorApplicationHeadClass::Applied,
                reference: HostApplicationReference {
                    key: key(Role::RuleLeftApplicationHead, 0),
                    target: HostApplicationTarget::Nominal(HostTypeReference {
                        key: HostTypeKey(marker_key::<Job>),
                        authored_path: "Job".to_owned(),
                    }),
                },
                path_key: key(Role::RuleLeftPath, 0),
                arguments: krs_ir::Arguments::named(vec![krs_ir::NamedTermArgument {
                    key: key(Role::RuleLeftRecordFieldName, 0),
                    field: krs_ir::ProductionFieldId::new("payload").unwrap(),
                    value: Box::new(job_payload()),
                }]),
                instance: Vec::new(),
                update: None,
                open: false,
            }),
        };
        krs_ir::HostHeadRule {
            sentence_kind: krs_ir::SentenceKind::Transition,
            label: None,
            priority: None,
            nondet: None,
            skipped_operand: None,
            pattern_key: key(Role::RulePattern, 0),
            result_key: key(Role::RuleResult, 0),
            head_sort: None,
            configuration: Some(krs_ir::HostConfigurationReference {
                key: key(Role::RuleType, 0),
                configuration: HostTypeReference {
                    key: HostTypeKey(boolean_key),
                    authored_path: "State".to_owned(),
                },
            }),
            result_type_key: key(Role::RuleResultType, 0),
            computation_cell: Some(krs_ir::HeadRuleComputationCell {
                key: key(Role::RuleLeftCellsField, 0),
                name: cell.to_owned(),
                result_key: Some(key(Role::RuleRightCellsField, 0)),
            }),
            bindings: vec![
                krs_ir::ProtocolHeadRuleBinding {
                    name: "j".to_owned(),
                    refinement: Some(HostSortReference {
                        key: key(Role::RuleBindingType, 0),
                        target: HostTypeReference {
                            key: HostTypeKey(marker_key::<JobSort>),
                            authored_path: "JobSort".to_owned(),
                        },
                    }),
                },
                krs_ir::ProtocolHeadRuleBinding {
                    name: "p".to_owned(),
                    refinement: None,
                },
            ],
            head: Some(krs_ir::ProtocolHeadRuleHead {
                items: vec![job],
                exact: false,
                tail_key: None,
                result: Some(krs_ir::ProtocolHeadRuleResult::Erase),
            }),
            requires: None,
            extras: Vec::new(),
            existentials: Vec::new(),
            ensures: None,
            fresh: Vec::new(),
            evaluation: None,
            bracket_alternative: Some(job_list_reading(cell)),
            claim: None,
        }
    }

    /// The record's child `p`, which both readings hold.
    fn job_payload() -> krs_ir::HostTerm {
        krs_ir::HostTerm::Variable {
            key: krs_ir::ProvenanceRole::RuleLeftReference.key(0),
            path_key: krs_ir::ProvenanceRole::RuleLeftPath.key(1),
            name: "p".to_owned(),
        }
    }

    /// The List reading of `cell: [j @ Job { payload: p }, ..] => cell:
    /// [..]`, whose instance child is the head record's `p`; the label `j`
    /// is no binding of this reading.
    fn job_list_reading(cell: &str) -> krs_ir::HostHeadRuleBracketAlternative {
        use krs_ir::ProvenanceRole as Role;
        let key = ProvenanceKey::new;
        let instances = |front, rest| {
            krs_ir::ProtocolRuleStateTerm::Instances(krs_ir::ProtocolRuleInstances {
                delimiter: krs_ir::InstanceDelimiter::Bracket,
                front,
                rest: krs_ir::ProtocolRuleFrame::Anonymous { key: rest },
                back: Vec::new(),
            })
        };
        krs_ir::ProtocolHeadRuleBracketAlternative {
            bindings: vec![krs_ir::ProtocolHeadRuleBinding {
                name: "p".to_owned(),
                refinement: None,
            }],
            extra: krs_ir::ProtocolHeadRuleExtra::RewriteState {
                cell: krs_ir::HostHeadRuleCellReference {
                    key: key(Role::RuleLeftCellsField, 1),
                    name: cell.to_owned(),
                },
                result_key: Some(key(Role::RuleRightCellsField, 1)),
                before: instances(
                    vec![krs_ir::ProtocolRuleInstance {
                        key: key(Role::RuleLeftCellsInstance, 0),
                        label: Some("j".to_owned()),
                        head: None,
                        fields: vec![krs_ir::ProtocolRuleInstanceField {
                            key: key(Role::RuleLeftCellsInstanceField, 0),
                            field: "payload".to_owned(),
                            value: krs_ir::ProtocolRuleStateTerm::Term(job_payload()),
                        }],
                        rest: krs_ir::ProtocolInstanceRest::Exact,
                    }],
                    key(Role::RuleLeftCellsInstancesRest, 0),
                ),
                after: Some(instances(
                    Vec::new(),
                    key(Role::RuleRightCellsInstancesRest, 0),
                )),
            },
        }
    }

    fn job_declarations() -> HashMap<HostApplicationIdentity, (StableItemId, ItemKind)> {
        let id = |name, kind| {
            StableItemId::new(
                PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap(),
                ["model"],
                name,
                kind,
                "",
            )
            .unwrap()
        };
        HashMap::from([
            (
                HostApplicationIdentity::Nominal(boolean_key()),
                (state_id(), ItemKind::Configuration),
            ),
            (
                HostApplicationIdentity::Nominal(marker_key::<Job>()),
                (id("Job", ItemKind::Constructor), ItemKind::Constructor),
            ),
            (
                HostApplicationIdentity::Nominal(marker_key::<JobSort>()),
                (id("JobSort", ItemKind::Sort), ItemKind::Sort),
            ),
        ])
    }

    /// On a List collection cell the bracketed value is the collection's
    /// instances: the List reading wins, and the anchors only the head
    /// reading's nodes hold go, the computation cell's names, the record
    /// the instance replaces (its label binder, head, path and field name),
    /// and the refinement of `j`, which the List reading does not bind. The
    /// child `p` is the instance's now.
    #[test]
    fn a_collection_cell_keeps_the_list_reading_and_drops_the_head() {
        use krs_ir::ProvenanceRole as Role;
        let (resolved, discarded) = resolve_reading(
            bracket_reading_clause("jobs"),
            &job_declarations(),
            vec![
                state_cell("k", Some(krs_ir::CellWrapper::KCell), false),
                state_cell("jobs", None, true),
            ],
        );
        assert_eq!(
            discarded,
            BTreeSet::from([
                Role::RuleLeftCellsField.key(0),
                Role::RuleRightCellsField.key(0),
                Role::PatternAs.key(0),
                Role::PatternAsBinding.key(0),
                Role::RuleLeftApplicationHead.key(0),
                Role::RuleLeftPath.key(0),
                Role::RuleLeftRecordFieldName.key(0),
                Role::RuleBindingType.key(0),
            ])
        );
        assert!(resolved.head.is_none() && resolved.computation_cell.is_none());
        assert_eq!(resolved.bindings.len(), 1);
        assert!(matches!(
            resolved.extras.as_slice(),
            [krs_ir::ProtocolHeadRuleExtra::RewriteState { cell, .. }]
                if cell.key == Role::RuleLeftCellsField.key(1)
        ));
    }

    /// On the computation cell the bracketed value is the head: the List
    /// reading goes with the anchors only its nodes hold, its cell names
    /// and its instance structure. Its child terms are the head's, which
    /// keeps them.
    #[test]
    fn a_computation_cell_keeps_the_head_and_drops_the_list_reading() {
        use krs_ir::ProvenanceRole as Role;
        let (resolved, discarded) = resolve_reading(
            bracket_reading_clause("k"),
            &job_declarations(),
            vec![state_cell("k", Some(krs_ir::CellWrapper::KCell), false)],
        );
        assert_eq!(
            discarded,
            BTreeSet::from([
                Role::RuleLeftCellsField.key(1),
                Role::RuleRightCellsField.key(1),
                Role::RuleLeftCellsInstance.key(0),
                Role::RuleLeftCellsInstanceField.key(0),
                Role::RuleLeftCellsInstancesRest.key(0),
                Role::RuleRightCellsInstancesRest.key(0),
            ])
        );
        assert!(resolved.head.is_some() && resolved.extras.is_empty());
        assert_eq!(resolved.bindings.len(), 2);
        assert_eq!(
            resolved
                .computation_cell
                .and_then(|computation| computation.key),
            Some(Role::RuleLeftCellsField.key(0))
        );
    }

    /// A cell of `State`'s tree: `owner` is `State` or a group, `group` the group a group cell
    /// holds, `marked` its `?` or `*` layer.
    fn tree_cell(
        (owner, field): (&str, &str),
        parent: Option<usize>,
        group: Option<&str>,
        marked: Option<Layer>,
    ) -> HeadRuleCellTarget {
        let content = match (group, field) {
            (Some(name), _) => Layer::Group(krs_ir::cell_kind::GroupKind {
                name: name.to_owned(),
                children: Vec::new(),
            }),
            (None, "k") => Layer::Computation,
            (None, _) => Layer::Leaf(Notation::Plain),
        };
        HeadRuleCellTarget {
            identity: krs_ir::DescriptorCellIdentity {
                owner: if owner == "State" {
                    state_id()
                } else {
                    cell_id(owner)
                },
                field: field.to_owned(),
            },
            names: vec![field.to_owned()],
            k_name: field.to_owned(),
            kind: CellKind {
                layers: marked.into_iter().chain([content]).collect(),
            },
            path: CellKind::default(),
            group: None,
            ancestor: None,
            sort: None,
            parent,
            group_id: group.map(cell_id),
        }
    }

    /// `State { core: Core { k, pc }, mem, mark?: Mark { seen }, job*: Job { payload },
    /// left: Twice { x }, right: Twice { x }, obj*: Obj { n } }`, the jobs a List collection and
    /// the objects a Set, scoped to each group it holds.
    fn group_target_state() -> HeadRuleTarget {
        let cells = vec![
            tree_cell(("State", "core"), None, Some("Core"), None),
            tree_cell(("Core", "k"), Some(0), None, None),
            tree_cell(("Core", "pc"), Some(0), None, None),
            tree_cell(("State", "mem"), None, None, None),
            tree_cell(("State", "mark"), None, Some("Mark"), Some(Layer::Optional)),
            tree_cell(("Mark", "seen"), Some(4), None, None),
            tree_cell(
                ("State", "job"),
                None,
                Some("Job"),
                Some(Layer::Instances(krs_ir::cell_kind::Order::List)),
            ),
            tree_cell(("Job", "payload"), Some(6), None, None),
            tree_cell(("State", "left"), None, Some("Twice"), None),
            tree_cell(("Twice", "x"), Some(8), None, None),
            tree_cell(("State", "right"), None, Some("Twice"), None),
            tree_cell(("Twice", "x"), Some(10), None, None),
            tree_cell(
                ("State", "obj"),
                None,
                Some("Obj"),
                Some(Layer::Instances(krs_ir::cell_kind::Order::Set)),
            ),
            tree_cell(("Obj", "n"), Some(12), None, None),
        ];
        let main = krs_ir::MainCell::Cell(cells[1].identity.clone());
        configuration_target(state_id(), cells, main).with_subjects()
    }

    /// `cells` with each cell's `path` and outermost marked `ancestor` from the configuration's
    /// level, as the configuration's walk gives them ([`collect_head_rule_cells`]).
    fn with_marks(mut cells: Vec<HeadRuleCellTarget>) -> Vec<HeadRuleCellTarget> {
        for index in 0..cells.len() {
            let Some(parent) = cells[index].parent else {
                continue;
            };
            let holder = &cells[parent];
            let mut path = holder.path.clone();
            path.layers.extend(
                holder
                    .kind
                    .layers
                    .first()
                    .filter(|layer| matches!(layer, Layer::Optional | Layer::Instances(_)))
                    .cloned(),
            );
            let ancestor = below_ancestor(holder.ancestor.as_ref(), holder);
            cells[index].path = path;
            cells[index].ancestor = ancestor;
        }
        cells
    }

    /// `State { harts: Harts { hart*: Hart { id, k, pc, fpu?: Fpu { f }, jobs*: Job { payload } }
    /// }, mem }`, the harts a Map collection and the jobs a List, scoped to each group it holds.
    fn instance_target_state() -> HeadRuleTarget {
        use krs_ir::cell_kind::Order;
        let cells = with_marks(vec![
            tree_cell(("State", "harts"), None, Some("Harts"), None),
            tree_cell(
                ("Harts", "hart"),
                Some(0),
                Some("Hart"),
                Some(Layer::Instances(Order::Map)),
            ),
            tree_cell(("Hart", "id"), Some(1), None, None),
            tree_cell(("Hart", "k"), Some(1), None, None),
            tree_cell(("Hart", "pc"), Some(1), None, None),
            tree_cell(("Hart", "fpu"), Some(1), Some("Fpu"), Some(Layer::Optional)),
            tree_cell(("Fpu", "f"), Some(5), None, None),
            tree_cell(
                ("Hart", "jobs"),
                Some(1),
                Some("Job"),
                Some(Layer::Instances(Order::List)),
            ),
            tree_cell(("Job", "payload"), Some(7), None, None),
            tree_cell(("State", "mem"), None, None, None),
        ]);
        let main = krs_ir::MainCell::Cell(cells[3].identity.clone());
        configuration_target(state_id(), keyed(cells, 1, "id"), main).with_subjects()
    }

    /// `cells` with the group of the Map collection at `holder` keyed by its child `key`, as
    /// a collected declaration states it ([`krs_ir::cell_kind::GroupKind::key`]).
    fn keyed(
        mut cells: Vec<HeadRuleCellTarget>,
        holder: usize,
        key: &str,
    ) -> Vec<HeadRuleCellTarget> {
        if let Some(Layer::Group(group)) = cells[holder].kind.layers.last_mut() {
            group.children = vec![(
                key.to_owned(),
                CellKind {
                    layers: vec![Layer::Leaf(Notation::Plain)],
                },
            )];
        }
        cells
    }

    /// `State { harts: Harts { hart*: Hart { cpu: Cpu { pc }, k } } }`, the hart keyed by the
    /// group `cpu`.
    fn composite_key_state() -> HeadRuleTarget {
        use krs_ir::cell_kind::Order;
        let cells = with_marks(vec![
            tree_cell(("State", "harts"), None, Some("Harts"), None),
            tree_cell(
                ("Harts", "hart"),
                Some(0),
                Some("Hart"),
                Some(Layer::Instances(Order::Map)),
            ),
            tree_cell(("Hart", "cpu"), Some(1), Some("Cpu"), None),
            tree_cell(("Cpu", "pc"), Some(2), None, None),
            tree_cell(("Hart", "k"), Some(1), None, None),
        ]);
        let main = krs_ir::MainCell::Cell(cells[4].identity.clone());
        configuration_target(state_id(), keyed(cells, 1, "cpu"), main).with_subjects()
    }

    /// A Map instance's key is its whole first child: a composite key holds every cell inside
    /// it, and a group inside the key is no subject (`map-collection-key`).
    #[test]
    fn a_composite_key_is_the_whole_identity_of_its_instance() {
        let state = composite_key_state();
        let targets = std::slice::from_ref(&state);
        let hart = group_target(&cell_id("Hart"), targets).unwrap();
        let (key, holder, _, group) = hart.instance_key().unwrap();
        assert_eq!(
            key.iter()
                .map(|cell| cell.field.as_str())
                .collect::<Vec<_>>(),
            ["cpu", "pc"]
        );
        assert_eq!((holder, group), ("hart", "Hart"));
        let cpu = group_target(&cell_id("Cpu"), targets).unwrap_err();
        assert_eq!(
            cpu.kind(),
            CollectionErrorKind::CellEntry(krs_syntax::cell_entries::Refusal::MapCollectionKey)
        );
        assert!(
            cpu.detail()
                .starts_with("the cell group `Cpu` is the key `cpu` of the instances of the Map collection `hart`"),
            "{}",
            cpu.detail()
        );
    }

    /// Each key of `keys` without the holder's identity, for comparing.
    fn unnamed<'t>(
        keys: impl Iterator<Item = TargetKey<'t>>,
    ) -> Vec<(&'t [krs_ir::DescriptorCellIdentity], &'t str, &'t str)> {
        keys.map(|(key, holder, _, group)| (key, holder, group))
            .collect()
    }

    /// A sentence about the instance type of a collection is a step of one instance, so its
    /// entries are judged from the instance's level: the marks of the anchor and its ancestors
    /// are dropped, and a cell below a further `?` or `*` inside the instance keeps that one,
    /// with that holder as its ancestor. A Map instance's key is its first child.
    #[test]
    fn a_group_subject_in_an_instance_judges_entries_from_the_instance() {
        use krs_ir::cell_kind::Order;
        let state = instance_target_state();
        let targets = std::slice::from_ref(&state);
        let entry = |target: &HeadRuleTarget, name: &str| {
            let (_, kind, ancestor, _) = target.entry(name).unwrap();
            (
                kind.path.layers,
                ancestor.map(|marked| (marked.name.clone(), marked.layer.clone(), marked.direct)),
            )
        };
        // From the configuration's level, a hart's cell is named at the hart's level too (IC-5):
        // a rule for the configuration naming it matches one hart, writing its key only as
        // matched. The hart's optional unit and List collection keep their marks.
        assert_eq!(entry(&state, "pc"), (Vec::new(), None));
        assert_eq!(
            entry(&state, "f"),
            (
                vec![Layer::Optional],
                Some(("fpu".to_owned(), Layer::Optional, true))
            )
        );
        assert_eq!(
            entry(&state, "payload"),
            (
                vec![Layer::Instances(Order::List)],
                Some(("jobs".to_owned(), Layer::Instances(Order::List), true))
            )
        );
        assert_eq!(
            unnamed(state.nested_instance_keys()),
            vec![(
                &[krs_ir::DescriptorCellIdentity {
                    owner: cell_id("Hart"),
                    field: "id".to_owned(),
                }][..],
                "hart",
                "Hart"
            )]
        );
        let hart = group_target(&cell_id("Hart"), targets).unwrap();
        assert_eq!(entry(hart, "pc"), (Vec::new(), None));
        assert_eq!(entry(hart, "id"), (Vec::new(), None));
        assert_eq!(
            entry(hart, "f"),
            (
                vec![Layer::Optional],
                Some(("fpu".to_owned(), Layer::Optional, true))
            )
        );
        assert_eq!(
            entry(hart, "payload"),
            (
                vec![Layer::Instances(Order::List)],
                Some(("jobs".to_owned(), Layer::Instances(Order::List), true))
            )
        );
        assert_eq!(
            hart.instance_key()
                .map(|(key, holder, _, group)| (key, holder, group)),
            Some((
                &[krs_ir::DescriptorCellIdentity {
                    owner: cell_id("Hart"),
                    field: "id".to_owned(),
                }][..],
                "hart",
                "Hart"
            ))
        );
        // An optional group inside the instance is a step of the one present: its cells are at
        // its own level, and it has no key.
        let fpu = group_target(&cell_id("Fpu"), targets).unwrap();
        assert_eq!(entry(fpu, "f"), (Vec::new(), None));
        assert!(fpu.instance_key().is_none());
        // A List collection inside the instance is refused, naming it.
        let job = group_target(&cell_id("Job"), targets).unwrap_err();
        assert_eq!(job.kind(), CollectionErrorKind::GroupSubjectPosition);
        assert!(
            job.detail()
                .starts_with("the cell group `Job` is held by the List collection cell `jobs`"),
            "{}",
            job.detail()
        );
        // The group holding the collection is at a fixed position: a hart's cell names one
        // instance of the Map collection inside the group, so it is at the instance's level, and
        // the sentence writes that instance's key only as matched. The hart's own List
        // collection keeps its mark.
        let harts = group_target(&cell_id("Harts"), targets).unwrap();
        assert_eq!(entry(harts, "pc"), (Vec::new(), None));
        assert_eq!(
            entry(harts, "payload"),
            (
                vec![Layer::Instances(Order::List)],
                Some(("jobs".to_owned(), Layer::Instances(Order::List), true))
            )
        );
        assert!(harts.instance_key().is_none());
        assert_eq!(
            unnamed(harts.nested_instance_keys()),
            vec![(
                &[krs_ir::DescriptorCellIdentity {
                    owner: cell_id("Hart"),
                    field: "id".to_owned(),
                }][..],
                "hart",
                "Hart"
            )]
        );
    }

    /// The target of the configuration `configuration` whose cells are `cells`, with no group
    /// records and no scopes.
    fn configuration_target(
        configuration: StableItemId,
        cells: Vec<HeadRuleCellTarget>,
        main: krs_ir::MainCell<krs_ir::DescriptorCellIdentity>,
    ) -> HeadRuleTarget {
        HeadRuleTarget {
            configuration,
            cells,
            main,
            main_refusal: None,
            group_children: HashMap::new(),
            groups: Vec::new(),
            subject: None,
            subjects: Vec::new(),
            configuration_keys: Vec::new(),
        }
    }

    /// A group at a fixed position scopes the configuration to the cells below it: a sentence
    /// typed by it names those, and is told so when it names the cell holding the group, another
    /// cell of the configuration, or a cell of a group the configuration does not hold; a group
    /// held by several cells is scoped at the first, since that configuration is refused as it is.
    #[test]
    fn a_group_subject_scopes_the_one_configuration_to_the_group_cells() {
        let state = group_target_state();
        let targets = std::slice::from_ref(&state);
        let core = group_target(&cell_id("Core"), targets).unwrap();
        assert_eq!(core.configuration, state_id());
        assert_eq!(
            core.descriptor_subject(),
            Some(krs_ir::DescriptorSubject::Group {
                declaration: cell_id("Core")
            })
        );
        assert_eq!(
            core.cells
                .iter()
                .map(|cell| cell.identity.field.as_str())
                .collect::<Vec<_>>(),
            ["k", "pc"]
        );
        assert_eq!(core.owner(), "the group `Core`");
        assert_eq!(state.owner(), "configuration `State`");
        let outside = core.outside("mem").unwrap();
        assert_eq!(outside.kind(), CollectionErrorKind::CellOutsideSubject);
        assert_eq!(
            outside.detail(),
            "`Core` has no cell `mem`: a sentence about the cell group `Core` names only the cells inside the group, and `mem` is another cell of configuration `State`; write the sentence for `State` to name it"
        );
        assert_eq!(
            core.outside("core").unwrap().detail(),
            "`Core` has no cell `core`: a sentence about the cell group `Core` names only the cells inside the group, and `core` is the cell of configuration `State` that holds the group; write the sentence for `State` to name it"
        );
        assert!(core.outside("pc").is_none() && core.outside("missing").is_none());
        assert!(state.outside("mem").is_none());

        // The same cells named by their owner, as a `cells!` entry names them.
        let identity = |owner: StableItemId, field: &str| krs_ir::DescriptorCellIdentity {
            owner,
            field: field.to_owned(),
        };
        assert!(
            core.outside_cell(&identity(cell_id("Core"), "pc"))
                .is_none()
        );
        assert!(state.outside_cell(&identity(state_id(), "mem")).is_none());
        for (cell, why) in [
            (
                identity(state_id(), "mem"),
                "`State::mem` is another cell of configuration `State`; write the sentence for `State` to name it",
            ),
            (
                identity(state_id(), "core"),
                "`State::core` is the cell of configuration `State` that holds the group; write the sentence for `State` to name it",
            ),
            (
                identity(cell_id("Mark"), "seen"),
                "`Mark::seen` is another cell of configuration `State`; write the sentence for `State` to name it",
            ),
            (
                identity(cell_id("Spare"), "ticks"),
                "`Spare::ticks` is a cell of the group `Spare`, which configuration `State` does not hold",
            ),
        ] {
            let refusal = core.outside_cell(&cell).unwrap();
            assert_eq!(refusal.kind(), CollectionErrorKind::CellOutsideSubject);
            assert!(refusal.detail().ends_with(why), "{}", refusal.detail());
        }

        // `Twice` is held by `left` and `right`: the configuration is refused as
        // `ambiguous-cell-sort`, and a sentence about `Twice` resolves at the first.
        let twice = group_target(&cell_id("Twice"), targets).unwrap();
        assert_eq!(twice.cells.len(), 1);
        assert_eq!(twice.cells[0].identity, identity(cell_id("Twice"), "x"));
        assert_eq!(
            twice.subject.as_ref().unwrap().holder.identity,
            identity(state_id(), "left")
        );

        let none = group_target(&cell_id("Core"), &[]).unwrap_err();
        assert_eq!(none.kind(), CollectionErrorKind::ConfigurationCount);
        assert!(
            none.detail().ends_with(
                "`Core` is a cell group, not a configuration, and rules for a group are checked through a definition whose configuration holds it"
            ),
            "{}",
            none.detail()
        );
    }

    /// A group held by an optional cell is scoped to the one instance present; a group in a
    /// Set or a List collection, or held by no cell, has no scope, and each refusal says why.
    #[test]
    fn a_group_subject_in_an_optional_cell_is_scoped_and_in_a_set_or_a_list_is_refused() {
        let state = group_target_state();
        let targets = std::slice::from_ref(&state);
        let identity = |owner: StableItemId, field: &str| krs_ir::DescriptorCellIdentity {
            owner,
            field: field.to_owned(),
        };
        // `Mark` is held by an optional cell: a sentence about it is a step of the one instance
        // present, and names its cells.
        let mark = group_target(&cell_id("Mark"), targets).unwrap();
        assert_eq!(mark.cells.len(), 1);
        assert_eq!(mark.cells[0].identity, identity(cell_id("Mark"), "seen"));
        assert!(mark.instance_key().is_none());

        let refusal = |group: &str| group_target(&cell_id(group), targets).unwrap_err();
        for (group, kind, reason) in [
            (
                "Job",
                CollectionErrorKind::GroupSubjectPosition,
                "the cell group `Job` is held by the List collection cell `job` of configuration `State`: a sentence about `Job` is about one instance, which in a List is the instance at any position, and matching one instance between others is not supported yet",
            ),
            (
                "Obj",
                CollectionErrorKind::GroupSubjectPosition,
                "the cell group `Obj` is held by the Set collection cell `obj` of configuration `State`: a sentence about `Obj` is about one instance, which a rule rewrites as a local step, and a Set identifies an instance by its whole content, so a step that makes one instance equal to another merges the two",
            ),
            (
                "Spare",
                CollectionErrorKind::GroupNotInConfiguration,
                "no cell of configuration `State` holds the cell group `Spare`",
            ),
        ] {
            let error = refusal(group);
            assert_eq!(error.kind(), kind, "{group}");
            assert!(error.detail().starts_with(reason), "{}", error.detail());
        }
    }

    /// A readable clause typed by a group resolves against the one configuration and carries the
    /// group as its subject; it may not name a cell outside the group, and a claim may not be
    /// typed by a group.
    #[test]
    fn a_clause_typed_by_a_group_carries_its_subject() {
        let declarations = HashMap::from([(
            HostApplicationIdentity::Nominal(boolean_key()),
            (cell_id("Core"), ItemKind::Cell),
        )]);
        let targets = [group_target_state()];
        let resolve = |rule: krs_ir::HostHeadRule| {
            resolve_payload(
                &HostDescriptorPayload::HeadRule(Box::new(rule)),
                &declarations,
                &HashMap::new(),
                &HashMap::new(),
                None,
                &targets,
            )
            .map(|(payload, _)| payload)
        };
        let Ok(DescriptorPayload::HeadRule(resolved)) = resolve(list_reading_clause("k", true))
        else {
            panic!("a clause for `Core` naming its `k` resolves")
        };
        assert_eq!(resolved.configuration, state_id());
        assert_eq!(
            resolved.subject,
            Some(krs_ir::DescriptorSubject::Group {
                declaration: cell_id("Core")
            })
        );
        assert_eq!(
            resolved
                .computation_cell
                .as_ref()
                .map(|computation| &computation.cell.owner),
            Some(&cell_id("Core"))
        );

        let outside = resolve(list_reading_clause("mem", false)).unwrap_err();
        assert_eq!(outside.kind(), CollectionErrorKind::CellOutsideSubject);

        let mut claim = list_reading_clause("k", true);
        claim.sentence_kind = krs_ir::SentenceKind::Claim;
        let refused = resolve(claim).unwrap_err();
        assert_eq!(refused.kind(), CollectionErrorKind::GroupClaim);
    }
}

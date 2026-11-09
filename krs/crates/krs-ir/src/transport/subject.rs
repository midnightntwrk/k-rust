//! The subject of a configuration-typed sentence and the cells it may name.
//!
//! A configuration-typed sentence is lowered against the one configuration of
//! its definition. Its subject is the part of that configuration the sentence
//! is about: the whole configuration, or one nominal `#[k::cell]` group at
//! its one position, in one instance of each optional cell and Map collection
//! that holds it. The subject restricts which cells the sentence may name;
//! it never changes what is framed, since every cell a sentence does not name
//! is framed, wherever its subject sits.
//!
//! [`scope`] is the one resolution of a subject to cell positions. Every
//! stage that judges a sentence's names (collection, semantic analysis) reads
//! a configuration as a [`CellTree`] and asks [`scope`], so a new kind of
//! subject is a new [`DescriptorSubject`] variant and a new arm of [`scope`].

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use super::detail::{StateTermReason, TransportField, TransportItemKind};
use crate::cell_kind::{Multiplicity, Order};
use crate::{DescriptorCellIdentity, DescriptorTerm, ItemKind, StableItemId, StateTransportError};

/// The part of the configuration a sentence is about, when it is not the
/// whole configuration.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum DescriptorSubject {
    /// A nominal `#[k::cell]` group: the sentence names only the group's
    /// cells, at the group's one position in the configuration.
    Group {
        /// The group's `#[k::cell]` declaration.
        declaration: StableItemId,
    },
}

impl DescriptorSubject {
    /// Validates the subject's declaration kind.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError::ItemKind`] when a group subject names
    /// a declaration that is not a `#[k::cell]` group.
    pub fn validate(&self) -> Result<(), StateTransportError> {
        match self {
            Self::Group { declaration } if declaration.item_kind() != ItemKind::Cell => {
                Err(StateTransportError::ItemKind {
                    field: TransportField::RuleSubjectGroup,
                    expected: TransportItemKind::Cell,
                    actual: declaration.item_kind(),
                })
            }
            Self::Group { .. } => Ok(()),
        }
    }
}

/// Checks the owner of a cell a sentence names: the configuration it is
/// lowered against, or a nested group. A sentence about a group names only
/// group cells, since a cell the configuration itself declares is never
/// below a group; which group cells are in its scope is [`scope`]'s
/// question, which needs the whole configuration.
pub(crate) fn validate_cell_owner(
    configuration: &StableItemId,
    subject: Option<&DescriptorSubject>,
    owner: &StableItemId,
) -> Result<(), StateTransportError> {
    if owner.item_kind() == ItemKind::Cell {
        Ok(())
    } else if owner != configuration {
        Err(StateTransportError::CellOwnerMismatch)
    } else if subject.is_some() {
        Err(StateTransportError::InvalidTerm(
            StateTermReason::CellOutsideGroupSubject,
        ))
    } else {
        Ok(())
    }
}

/// One cell of a configuration read as a tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TreeCell {
    /// The cell's nominal identity.
    pub identity: DescriptorCellIdentity,
    /// The index of the enclosing cell in [`CellTree::cells`], absent for a
    /// top-level cell of the configuration.
    pub parent: Option<usize>,
    /// The `#[k::cell]` declaration whose cells this cell holds, absent for
    /// a cell that holds no group.
    pub group: Option<StableItemId>,
    /// The cell's declared multiplicity.
    pub multiplicity: Multiplicity,
    /// Whether the cell holds a computation, a `KSequence`.
    pub computation: bool,
    /// For a collection, the field name of the child that keys each of its instances
    /// ([`crate::cell_kind::CellKind::instance_key`]): a Map collection's first child.
    pub key: Option<String>,
}

/// A configuration's cells in preorder.
///
/// Every cell's parent precedes it, so [`TreeCell::parent`] is smaller than
/// the cell's own index.
pub trait CellTree {
    /// The cells, in preorder.
    fn cells(&self) -> &[TreeCell];
}

impl CellTree for [TreeCell] {
    fn cells(&self) -> &[TreeCell] {
        self
    }
}

impl CellTree for Vec<TreeCell> {
    fn cells(&self) -> &[TreeCell] {
        self
    }
}

/// What a subject lets a sentence name.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SubjectScope {
    /// The index of the cell that holds the subject, absent when the subject
    /// is the whole configuration.
    pub anchor: Option<usize>,
    /// The index of the innermost optional (`?`) or collection (`*`) cell on
    /// the anchor's path, the anchor included: the sentence's cells are
    /// matched in one instance of it. Absent where the subject sits at a
    /// fixed position, and for the whole configuration.
    pub instance: Option<usize>,
    /// The cells the sentence may name: every cell below the anchor, or
    /// every cell of the configuration.
    pub nameable: BTreeSet<DescriptorCellIdentity>,
}

/// Why a subject has no scope in a configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SubjectError {
    /// No cell of the configuration holds the group.
    NotInConfiguration,
    /// Several cells hold the group, so its cells have no one position.
    SeveralPositions {
        /// The indices of the cells that hold the group, in preorder.
        positions: Vec<usize>,
    },
    /// The group's cells sit in an instance of a collection whose order
    /// does not admit a local step of one instance: a Set, whose instance is
    /// its content, so a rewritten instance equal to another merges with it;
    /// or a List, where a step of any one instance is not supported yet.
    BelowCollection {
        /// The index of the nearest such collection cell: the anchor or one
        /// of its ancestors.
        ancestor: usize,
        /// That collection's order.
        order: Order,
    },
    /// The group's cell is the key of a Map collection's instance, or lies inside it. The key is
    /// the instance's identity, which a step of the instance never writes, so no sentence may
    /// be about it.
    InKey {
        /// The index of the Map collection cell.
        holder: usize,
        /// The index of its instance's key cell.
        key: usize,
    },
}

/// Resolves a subject to the cells a sentence about it may name.
///
/// The whole configuration (`None`) lets a sentence name every cell. A group
/// lets it name the cells below the group's one position: the group's own
/// cells and those of the groups nested in it. A rule about the group is a
/// local step of one instance of it, which changes that instance and frames
/// every other cell. Where the group sits in an optional cell or a collection,
/// the step is in one instance of the innermost such cell
/// ([`SubjectScope::instance`]), and every holder on the path must keep the
/// identity of the instance that steps: an optional cell (the one instance
/// present) and a Map collection (its key, which a step never writes) do. A
/// Set collection does not: its instance is its content, so a step that makes
/// one instance equal to another merges the two. A List collection keeps an
/// instance's position, but a step of any one of its instances is not
/// supported yet.
///
/// # Errors
///
/// Returns [`SubjectError`] when no cell or several cells hold the group, or
/// when the group sits in an instance of a Set or a List collection.
pub fn scope<T: CellTree + ?Sized>(
    tree: &T,
    subject: Option<&DescriptorSubject>,
) -> Result<SubjectScope, SubjectError> {
    let cells = tree.cells();
    let Some(subject) = subject else {
        return Ok(SubjectScope {
            anchor: None,
            instance: None,
            nameable: cells.iter().map(|cell| cell.identity.clone()).collect(),
        });
    };
    match subject {
        DescriptorSubject::Group { declaration } => group_scope(cells, declaration),
    }
}

fn group_scope(
    cells: &[TreeCell],
    declaration: &StableItemId,
) -> Result<SubjectScope, SubjectError> {
    let positions = cells
        .iter()
        .enumerate()
        .filter(|(_, cell)| cell.group.as_ref() == Some(declaration))
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let anchor = match positions.as_slice() {
        [] => return Err(SubjectError::NotInConfiguration),
        [anchor] => *anchor,
        _ => return Err(SubjectError::SeveralPositions { positions }),
    };
    let mut instance = None;
    for ancestor in path(cells, anchor) {
        match cells[ancestor].multiplicity {
            Multiplicity::One => continue,
            Multiplicity::Optional | Multiplicity::Many(Order::Map) => {}
            Multiplicity::Many(order @ (Order::Set | Order::List)) => {
                return Err(SubjectError::BelowCollection { ancestor, order });
            }
        }
        instance.get_or_insert(ancestor);
    }
    if let Some(&(holder, key)) = keys_on_path(cells, anchor).first() {
        return Err(SubjectError::InKey { holder, key });
    }
    Ok(SubjectScope {
        anchor: Some(anchor),
        instance,
        nameable: below(cells, anchor),
    })
}

/// The identities of the cells strictly below the cell at `anchor`.
fn below(cells: &[TreeCell], anchor: usize) -> BTreeSet<DescriptorCellIdentity> {
    cells
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != anchor && path(cells, *index).any(|cell| cell == anchor))
        .map(|(_, cell)| cell.identity.clone())
        .collect()
}

/// The optional (`?`) and collection (`*`) cells on the path of the cell at
/// `index`, the cell included, outermost first: the holders whose one
/// instance a step at that cell is in.
#[must_use]
pub fn instance_path<T: CellTree + ?Sized>(tree: &T, index: usize) -> Vec<usize> {
    let cells = tree.cells();
    let mut holders = path(cells, index)
        .filter(|&cell| cells[cell].multiplicity != Multiplicity::One)
        .collect::<Vec<_>>();
    holders.reverse();
    holders
}

/// The key cell of each instance of the collection at `holder`: its child named by
/// [`TreeCell::key`]. `None` for a cell that is no Map collection.
#[must_use]
pub fn key_cell<T: CellTree + ?Sized>(tree: &T, holder: usize) -> Option<usize> {
    let cells = tree.cells();
    let key = cells.get(holder)?.key.as_deref()?;
    let unraw = |name: &str| name.strip_prefix("r#").unwrap_or(name).to_owned();
    cells
        .iter()
        .enumerate()
        .skip(holder + 1)
        .find(|(_, cell)| cell.parent == Some(holder) && unraw(&cell.identity.field) == key)
        .map(|(index, _)| index)
}

/// The Map instance keys the cell at `index` is (the cell itself) or lies inside, innermost
/// first, each as its collection cell and its key cell. A key is an instance's identity, as a
/// whole value, so every cell at or below a key cell is part of that identity.
#[must_use]
pub fn keys_on_path<T: CellTree + ?Sized>(tree: &T, index: usize) -> Vec<(usize, usize)> {
    let cells = tree.cells();
    path(cells, index)
        .filter_map(|cell| {
            let holder = cells[cell].parent.filter(|&parent| parent < cell)?;
            (key_cell(cells, holder) == Some(cell)).then_some((holder, cell))
        })
        .collect()
}

/// Why a rule whose cells lie in one instance of the Map collection cell `holder`, whose instance
/// type is the group `group`, may not write the cell `cell`, which is the instance's key `key` or
/// lies inside it: the one text of every route that judges such a write, whether the rule is for
/// `group`, for a group inside the instance, or for an enclosing group or the configuration that
/// names the instance's cells directly. The text names no rule: each of those is a step of the
/// one instance its cells lie in. An entry of the collection in a rule about an enclosing cell
/// writes the key with another source, refused with [`key_update_reason`].
#[must_use]
pub fn key_write_reason(group: &str, holder: &str, key: &str, cell: &str) -> String {
    let written = if cell == key {
        format!("`{key}`, the key")
    } else {
        format!("`{cell}`, a cell inside the key `{key}`,")
    };
    format!(
        "the rule writes {written} of the `{group}` instance of the Map collection `{holder}` it steps: a rule is a local step of one instance of each Map collection its cells lie in, and the whole key is the instance's identity, so the step writes it only as what its subject matched, the same variable or the same literal; a key that is not a variable or a literal cannot be shown kept, so leave it out of the result, which keeps it, or write it as the subject matched it"
    )
}

/// Why an entry of the Map collection cell `holder` that keeps one instance may not write its key
/// `key` other than as the entry matched it: the key is the instance's identity, so an update of
/// the instance keeps it. The one text of every route that judges a key such an entry writes.
#[must_use]
pub fn key_update_reason(holder: &str, key: &str) -> String {
    format!("an update must not change `{key}`, the key of the Map collection `{holder}`")
}

/// Why no sentence may be about the group `group`, whose cell is the key `key` of the Map
/// collection cell `holder`'s instances or lies inside it ([`SubjectError::InKey`]).
#[must_use]
pub fn key_subject_reason(group: &str, holder: &str, key: &str) -> String {
    format!(
        "the cell group `{group}` is the key `{key}` of the instances of the Map collection `{holder}`, or lies inside it: the whole key is an instance's identity, which no step of the instance changes, so a sentence about `{group}` would be about an identity; match the key from a sentence about the instance or the configuration"
    )
}

/// Whether a written key term keeps the key the subject matched as `matched`: a variable that
/// is the subject's binder for the key (an alias's binder included), or the same literal or
/// token the subject matched. A key is an instance's identity, so a step that writes it writes
/// what is provably the key it matched; a key that is not a variable or a literal cannot be
/// shown kept. The predicate over authored entries is `krs_syntax::cell_entries::keeps_key`.
#[must_use]
pub fn keeps_key_term(written: &DescriptorTerm, matched: Option<&DescriptorTerm>) -> bool {
    fn unaliased(term: &DescriptorTerm) -> &DescriptorTerm {
        match term {
            DescriptorTerm::As { pattern, .. } => pattern,
            other => other,
        }
    }
    match (written, matched) {
        (
            DescriptorTerm::Variable { name, .. },
            Some(DescriptorTerm::Variable { name: bound, .. }),
        )
        | (DescriptorTerm::Variable { name, .. }, Some(DescriptorTerm::As { name: bound, .. })) => {
            name == bound
        }
        (DescriptorTerm::Literal { literal, .. }, Some(matched)) => matches!(
            unaliased(matched),
            DescriptorTerm::Literal { literal: other, .. } if other == literal
        ),
        (DescriptorTerm::BuiltinToken { sort, value, .. }, Some(matched)) => matches!(
            unaliased(matched),
            DescriptorTerm::BuiltinToken { sort: other_sort, value: other, .. }
                if other_sort == sort && other == value
        ),
        _ => false,
    }
}

/// Whether every in-place rewrite (`k::rewrite!(from => to)`) at or below `term` keeps what it
/// matched ([`keeps_key_term`]): in a key, a rewrite whose sides are not the same variable or
/// literal changes the instance's identity.
#[must_use]
pub fn rewrites_keep(term: &DescriptorTerm) -> bool {
    use crate::TermArgumentRef;
    match term {
        DescriptorTerm::Rewrite { from, to, .. } => {
            to.as_deref()
                .is_some_and(|to| keeps_key_term(to, Some(from)))
                && rewrites_keep(from)
        }
        DescriptorTerm::Application {
            arguments, update, ..
        } => {
            arguments.iter().all(|argument| {
                let (TermArgumentRef::Positional { value } | TermArgumentRef::Named { value, .. }) =
                    argument;
                rewrites_keep(value)
            }) && update.as_deref().is_none_or(rewrites_keep)
        }
        DescriptorTerm::Cell { fields, update, .. } => {
            fields.iter().all(|field| rewrites_keep(&field.value))
                && update.as_deref().is_none_or(rewrites_keep)
        }
        DescriptorTerm::OrBool { arguments, .. } => arguments.iter().all(rewrites_keep),
        DescriptorTerm::MapEntries { entries, rest, .. } => {
            entries
                .iter()
                .all(|entry| rewrites_keep(&entry.key) && rewrites_keep(&entry.value))
                && rest.as_deref().is_none_or(rewrites_keep)
        }
        DescriptorTerm::Or { alternatives, .. } => alternatives.iter().all(rewrites_keep),
        DescriptorTerm::SortTest { operand, .. } => rewrites_keep(operand),
        DescriptorTerm::As { pattern, .. } => rewrites_keep(pattern),
        DescriptorTerm::Matches {
            subject, pattern, ..
        } => rewrites_keep(subject) && rewrites_keep(pattern),
        DescriptorTerm::Let {
            pattern,
            value,
            body,
            ..
        } => rewrites_keep(pattern) && rewrites_keep(value) && rewrites_keep(body),
        DescriptorTerm::Closure { body, .. } => rewrites_keep(body),
        DescriptorTerm::Variable { .. }
        | DescriptorTerm::Literal { .. }
        | DescriptorTerm::Wildcard { .. }
        | DescriptorTerm::KeptRest { .. }
        | DescriptorTerm::BuiltinToken { .. }
        | DescriptorTerm::Anonymous { .. }
        | DescriptorTerm::Lexeme { .. } => true,
    }
}

/// The cell at `index`, then each enclosing cell up to the top level.
///
/// The walk follows parents only while they precede their child, as preorder
/// requires, so it ends even on a tree that breaks that requirement.
fn path(cells: &[TreeCell], index: usize) -> impl Iterator<Item = usize> + '_ {
    std::iter::successors(Some(index), |&current| {
        cells[current].parent.filter(|&parent| parent < current)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PackageId;

    fn item(name: &str, kind: ItemKind) -> StableItemId {
        StableItemId::new(
            PackageId::new("ORG-EXAMPLE", "test", "0.1.0", "workspace").unwrap(),
            ["state"],
            name,
            kind,
            "",
        )
        .unwrap()
    }

    fn group(name: &str) -> DescriptorSubject {
        DescriptorSubject::Group {
            declaration: item(name, ItemKind::Cell),
        }
    }

    /// `(owner, field, parent, group, multiplicity)`.
    type Row<'a> = (
        &'a str,
        &'a str,
        Option<usize>,
        Option<&'a str>,
        Multiplicity,
    );

    /// Builds a preorder tree from rows; the owner `Machine` is the
    /// configuration, every other owner a group.
    fn tree(rows: &[Row<'_>]) -> Vec<TreeCell> {
        let mut cells = rows
            .iter()
            .map(|&(owner, field, parent, held, multiplicity)| TreeCell {
                identity: identity(owner, field),
                parent,
                group: held.map(|name| item(name, ItemKind::Cell)),
                multiplicity,
                computation: field == "k",
                key: None,
            })
            .collect::<Vec<_>>();
        // A Map collection's instance is keyed by its first child.
        for index in 0..cells.len() {
            if cells[index].multiplicity == Many(Order::Map) {
                cells[index].key = cells
                    .iter()
                    .find(|cell| cell.parent == Some(index))
                    .map(|cell| cell.identity.field.clone());
            }
        }
        cells
    }

    fn identity(owner: &str, field: &str) -> DescriptorCellIdentity {
        let kind = if owner == "Machine" {
            ItemKind::Configuration
        } else {
            ItemKind::Cell
        };
        DescriptorCellIdentity {
            owner: item(owner, kind),
            field: field.to_owned(),
        }
    }

    fn names(pairs: &[(&str, &str)]) -> BTreeSet<DescriptorCellIdentity> {
        pairs
            .iter()
            .map(|&(owner, field)| identity(owner, field))
            .collect()
    }

    use Multiplicity::{Many, One, Optional};

    /// `Machine { cpu: Cpu { k, regs: Regs { a, f }, pc }, mem }`.
    fn console() -> Vec<TreeCell> {
        tree(&[
            ("Machine", "cpu", None, Some("Cpu"), One),
            ("Cpu", "k", Some(0), None, One),
            ("Cpu", "regs", Some(0), Some("Regs"), One),
            ("Regs", "a", Some(2), None, One),
            ("Regs", "f", Some(2), None, One),
            ("Cpu", "pc", Some(0), None, One),
            ("Machine", "mem", None, None, One),
        ])
    }

    #[test]
    fn the_whole_configuration_names_every_cell() {
        let cells = console();
        let scope = scope(&cells, None).unwrap();
        assert_eq!(scope.anchor, None);
        assert_eq!(
            scope.nameable,
            cells.iter().map(|cell| cell.identity.clone()).collect()
        );
    }

    #[test]
    fn a_fixed_group_names_its_cells_and_its_nested_groups_cells() {
        let scope = scope(&console(), Some(&group("Cpu"))).unwrap();
        assert_eq!(scope.anchor, Some(0));
        assert_eq!(
            scope.nameable,
            names(&[
                ("Cpu", "k"),
                ("Cpu", "regs"),
                ("Regs", "a"),
                ("Regs", "f"),
                ("Cpu", "pc"),
            ])
        );
    }

    #[test]
    fn a_group_inside_a_group_names_only_its_own_cells() {
        let scope = scope(&console(), Some(&group("Regs"))).unwrap();
        assert_eq!(scope.anchor, Some(2));
        assert_eq!(scope.nameable, names(&[("Regs", "a"), ("Regs", "f")]));
    }

    #[test]
    fn a_group_the_configuration_does_not_hold_has_no_scope() {
        assert_eq!(
            scope(&console(), Some(&group("Timer"))),
            Err(SubjectError::NotInConfiguration)
        );
    }

    #[test]
    fn a_group_held_twice_has_no_one_position() {
        let cells = tree(&[
            ("Machine", "left", None, Some("Cpu"), One),
            ("Cpu", "pc", Some(0), None, One),
            ("Machine", "right", None, Some("Cpu"), One),
            ("Cpu", "pc", Some(2), None, One),
        ]);
        assert_eq!(
            scope(&cells, Some(&group("Cpu"))),
            Err(SubjectError::SeveralPositions {
                positions: vec![0, 2]
            })
        );
    }

    /// `Machine { harts: Harts { hart*: Hart { id, k, pc, fpu?: Fpu { f } } }, mem }`, the
    /// collection ordered by `order`.
    fn smp(order: Order) -> Vec<TreeCell> {
        tree(&[
            ("Machine", "harts", None, Some("Harts"), One),
            ("Harts", "hart", Some(0), Some("Hart"), Many(order)),
            ("Hart", "id", Some(1), None, One),
            ("Hart", "k", Some(1), None, One),
            ("Hart", "pc", Some(1), None, One),
            ("Hart", "fpu", Some(1), Some("Fpu"), Optional),
            ("Fpu", "f", Some(5), None, One),
            ("Machine", "mem", None, None, One),
        ])
    }

    #[test]
    fn a_group_in_a_map_collection_is_scoped_to_one_instance() {
        let scope = scope(&smp(Order::Map), Some(&group("Hart"))).unwrap();
        // The collection cell holds the group, so it is both the anchor and the instance.
        assert_eq!((scope.anchor, scope.instance), (Some(1), Some(1)));
        assert_eq!(
            scope.nameable,
            names(&[
                ("Hart", "id"),
                ("Hart", "k"),
                ("Hart", "pc"),
                ("Hart", "fpu"),
                ("Fpu", "f"),
            ])
        );
    }

    #[test]
    fn a_group_in_an_optional_cell_is_scoped_to_the_one_instance() {
        let cells = tree(&[
            ("Machine", "cpu", None, Some("Cpu"), One),
            ("Cpu", "pc", Some(0), None, One),
            ("Machine", "fpu", None, Some("Fpu"), Optional),
            ("Fpu", "f", Some(2), None, One),
        ]);
        let scope = scope(&cells, Some(&group("Fpu"))).unwrap();
        assert_eq!((scope.anchor, scope.instance), (Some(2), Some(2)));
        assert_eq!(scope.nameable, names(&[("Fpu", "f")]));
        // A group at a fixed position has no instance.
        let fixed = super::scope(&cells, Some(&group("Cpu"))).unwrap();
        assert_eq!((fixed.anchor, fixed.instance), (Some(0), None));
    }

    #[test]
    fn a_group_inside_an_instance_is_in_that_instance() {
        // An optional group inside a Map instance: its instance is the inner optional cell.
        let cells = smp(Order::Map);
        let fpu = scope(&cells, Some(&group("Fpu"))).unwrap();
        assert_eq!((fpu.anchor, fpu.instance), (Some(5), Some(5)));
        assert_eq!(instance_path(&cells, 5), vec![1, 5]);
        // A fixed group inside a Map instance: the instance is the collection cell above it.
        let fixed = tree(&[
            ("Machine", "harts", None, Some("Harts"), One),
            ("Harts", "hart", Some(0), Some("Hart"), Many(Order::Map)),
            ("Hart", "id", Some(1), None, One),
            ("Hart", "cpu", Some(1), Some("Cpu"), One),
            ("Cpu", "pc", Some(3), None, One),
        ]);
        let cpu = scope(&fixed, Some(&group("Cpu"))).unwrap();
        assert_eq!((cpu.anchor, cpu.instance), (Some(3), Some(1)));
        assert_eq!(cpu.nameable, names(&[("Cpu", "pc")]));
        assert_eq!(instance_path(&fixed, 3), vec![1]);
        // The group that holds the collection is at a fixed position, and names the
        // collection and everything below it.
        let holder = scope(&fixed, Some(&group("Harts"))).unwrap();
        assert_eq!((holder.anchor, holder.instance), (Some(0), None));
        assert_eq!(
            holder.nameable,
            names(&[
                ("Harts", "hart"),
                ("Hart", "id"),
                ("Hart", "cpu"),
                ("Cpu", "pc"),
            ])
        );
        assert!(instance_path(&fixed, 0).is_empty());
    }

    #[test]
    fn a_map_in_a_map_is_scoped_to_the_inner_instance() {
        let cells = tree(&[
            (
                "Machine",
                "cluster",
                None,
                Some("Cluster"),
                Many(Order::Map),
            ),
            ("Cluster", "id", Some(0), None, One),
            ("Cluster", "hart", Some(0), Some("Hart"), Many(Order::Map)),
            ("Hart", "id", Some(2), None, One),
            ("Hart", "pc", Some(2), None, One),
        ]);
        let hart = scope(&cells, Some(&group("Hart"))).unwrap();
        assert_eq!((hart.anchor, hart.instance), (Some(2), Some(2)));
        assert_eq!(hart.nameable, names(&[("Hart", "id"), ("Hart", "pc")]));
        assert_eq!(instance_path(&cells, 2), vec![0, 2]);
        let cluster = scope(&cells, Some(&group("Cluster"))).unwrap();
        assert_eq!((cluster.anchor, cluster.instance), (Some(0), Some(0)));
    }

    /// `Machine { harts: Harts { hart*: Hart { cpu: Cpu { pc }, k } } }`: the hart's key is the
    /// group `cpu`.
    fn composite_key() -> Vec<TreeCell> {
        tree(&[
            ("Machine", "harts", None, Some("Harts"), One),
            ("Harts", "hart", Some(0), Some("Hart"), Many(Order::Map)),
            ("Hart", "cpu", Some(1), Some("Cpu"), One),
            ("Cpu", "pc", Some(2), None, One),
            ("Hart", "k", Some(1), None, One),
        ])
    }

    #[test]
    fn a_map_key_is_its_instance_identity_at_and_below_the_key_cell() {
        let cells = composite_key();
        assert_eq!(key_cell(&cells, 1), Some(2));
        assert_eq!(key_cell(&cells, 0), None);
        assert_eq!(keys_on_path(&cells, 3), vec![(1, 2)]);
        assert_eq!(keys_on_path(&cells, 2), vec![(1, 2)]);
        assert!(keys_on_path(&cells, 4).is_empty());
        assert!(keys_on_path(&cells, 1).is_empty());
        // A group inside the key is no subject: a rule about it would write the identity.
        assert_eq!(
            scope(&cells, Some(&group("Cpu"))),
            Err(SubjectError::InKey { holder: 1, key: 2 })
        );
        // The instance type itself is a subject.
        let hart = scope(&cells, Some(&group("Hart"))).unwrap();
        assert_eq!((hart.anchor, hart.instance), (Some(1), Some(1)));
    }

    #[test]
    fn a_set_or_a_list_collection_holds_no_local_step() {
        for order in [Order::Set, Order::List] {
            let cells = smp(order);
            assert_eq!(
                scope(&cells, Some(&group("Hart"))),
                Err(SubjectError::BelowCollection { ancestor: 1, order }),
                "{order:?}"
            );
            // A group further inside the instance names the same collection.
            assert_eq!(
                scope(&cells, Some(&group("Fpu"))),
                Err(SubjectError::BelowCollection { ancestor: 1, order }),
                "{order:?}"
            );
        }
    }

    #[test]
    fn a_map_in_an_enclosing_set_or_list_names_the_enclosing_collection() {
        for order in [Order::Set, Order::List] {
            let cells = tree(&[
                ("Machine", "cluster", None, Some("Cluster"), Many(order)),
                ("Cluster", "hart", Some(0), Some("Hart"), Many(Order::Map)),
                ("Hart", "id", Some(1), None, One),
                ("Hart", "pc", Some(1), None, One),
            ]);
            assert_eq!(
                scope(&cells, Some(&group("Hart"))),
                Err(SubjectError::BelowCollection { ancestor: 0, order }),
                "{order:?}"
            );
        }
        // An optional cell inside a List instance is refused for the list.
        let cells = tree(&[
            ("Machine", "board", None, Some("Board"), Many(Order::List)),
            ("Board", "cpu", Some(0), Some("Cpu"), Optional),
            ("Cpu", "pc", Some(1), None, One),
        ]);
        assert_eq!(
            scope(&cells, Some(&group("Cpu"))),
            Err(SubjectError::BelowCollection {
                ancestor: 0,
                order: Order::List
            })
        );
    }

    #[test]
    fn a_group_subject_names_a_cell_group_declaration() {
        assert_eq!(group("Cpu").validate(), Ok(()));
        assert_eq!(
            DescriptorSubject::Group {
                declaration: item("Machine", ItemKind::Configuration),
            }
            .validate(),
            Err(StateTransportError::ItemKind {
                field: TransportField::RuleSubjectGroup,
                expected: TransportItemKind::Cell,
                actual: ItemKind::Configuration,
            })
        );
    }

    #[test]
    fn a_group_subject_is_tagged_on_the_wire() {
        let json = serde_json::to_value(group("Cpu")).unwrap();
        assert_eq!(json["kind"], "group");
        assert_eq!(json["declaration"]["item_name"], "Cpu");
        assert_eq!(
            serde_json::from_value::<DescriptorSubject>(json).unwrap(),
            group("Cpu")
        );
    }
}

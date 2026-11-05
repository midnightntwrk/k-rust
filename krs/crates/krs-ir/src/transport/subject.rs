//! The subject of a configuration-typed sentence and the cells it may name.
//!
//! A configuration-typed sentence is lowered against the one configuration of
//! its definition. Its subject is the part of that configuration the sentence
//! is about: the whole configuration, or one nominal `#[k::cell]` group at
//! its one position. The subject restricts which cells the sentence may name;
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
use crate::cell_kind::Multiplicity;
use crate::{DescriptorCellIdentity, ItemKind, StableItemId, StateTransportError};

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
    /// The group's cells sit below an optional cell, so they exist only in
    /// some states of the configuration.
    BelowOptional {
        /// The index of the nearest optional cell: the anchor or one of its
        /// ancestors.
        ancestor: usize,
    },
    /// The group's cells sit below a collection cell, so each instance holds
    /// its own copy of them.
    BelowCollection {
        /// The index of the nearest collection cell: the anchor or one of
        /// its ancestors.
        ancestor: usize,
    },
}

/// Resolves a subject to the cells a sentence about it may name.
///
/// The whole configuration (`None`) lets a sentence name every cell. A group
/// lets it name the cells below the group's one position: the group's own
/// cells and those of the groups nested in it. That position must be fixed:
/// a group below an optional or a collection cell has no single set of cells
/// a sentence could be about.
///
/// # Errors
///
/// Returns [`SubjectError`] when no cell or several cells hold the group, or
/// when the group's position is below an optional or a collection cell.
pub fn scope<T: CellTree + ?Sized>(
    tree: &T,
    subject: Option<&DescriptorSubject>,
) -> Result<SubjectScope, SubjectError> {
    let cells = tree.cells();
    let Some(subject) = subject else {
        return Ok(SubjectScope {
            anchor: None,
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
    for ancestor in path(cells, anchor) {
        match cells[ancestor].multiplicity {
            Multiplicity::One => {}
            Multiplicity::Optional => return Err(SubjectError::BelowOptional { ancestor }),
            Multiplicity::Many(_) => return Err(SubjectError::BelowCollection { ancestor }),
        }
    }
    let nameable = cells
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != anchor && path(cells, *index).any(|cell| cell == anchor))
        .map(|(_, cell)| cell.identity.clone())
        .collect();
    Ok(SubjectScope {
        anchor: Some(anchor),
        nameable,
    })
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
    use crate::cell_kind::Order;

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
        rows.iter()
            .map(|&(owner, field, parent, held, multiplicity)| TreeCell {
                identity: identity(owner, field),
                parent,
                group: held.map(|name| item(name, ItemKind::Cell)),
                multiplicity,
                computation: field == "k",
            })
            .collect()
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

    #[test]
    fn a_group_below_an_optional_cell_has_no_fixed_position() {
        let cells = tree(&[
            ("Machine", "board", None, Some("Board"), Optional),
            ("Board", "cpu", Some(0), Some("Cpu"), One),
            ("Cpu", "pc", Some(1), None, One),
        ]);
        assert_eq!(
            scope(&cells, Some(&group("Cpu"))),
            Err(SubjectError::BelowOptional { ancestor: 0 })
        );
        // The group's own cell counts: its cells exist only when it does.
        let optional = tree(&[
            ("Machine", "cpu", None, Some("Cpu"), Optional),
            ("Cpu", "pc", Some(0), None, One),
        ]);
        assert_eq!(
            scope(&optional, Some(&group("Cpu"))),
            Err(SubjectError::BelowOptional { ancestor: 0 })
        );
    }

    #[test]
    fn a_group_below_a_collection_cell_has_no_fixed_position() {
        let cells = tree(&[
            ("Machine", "harts", None, Some("Harts"), One),
            ("Harts", "hart", Some(0), Some("Hart"), Many(Order::Map)),
            ("Hart", "id", Some(1), None, One),
            ("Hart", "cpu", Some(1), Some("Cpu"), One),
            ("Cpu", "pc", Some(3), None, One),
        ]);
        assert_eq!(
            scope(&cells, Some(&group("Cpu"))),
            Err(SubjectError::BelowCollection { ancestor: 1 })
        );
        assert_eq!(
            scope(&cells, Some(&group("Hart"))),
            Err(SubjectError::BelowCollection { ancestor: 1 })
        );
        // The group that holds the collection is at a fixed position, and
        // names the collection and everything below it.
        let holder = scope(&cells, Some(&group("Harts"))).unwrap();
        assert_eq!(holder.anchor, Some(0));
        assert_eq!(
            holder.nameable,
            names(&[
                ("Harts", "hart"),
                ("Hart", "id"),
                ("Hart", "cpu"),
                ("Cpu", "pc"),
            ])
        );
    }

    #[test]
    fn the_nearest_unfixed_cell_is_reported() {
        let cells = tree(&[
            ("Machine", "board", None, Some("Board"), Optional),
            ("Board", "harts", Some(0), Some("Cpu"), Many(Order::List)),
            ("Cpu", "pc", Some(1), None, One),
        ]);
        assert_eq!(
            scope(&cells, Some(&group("Cpu"))),
            Err(SubjectError::BelowCollection { ancestor: 1 })
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

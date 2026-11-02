//! A cell's kind as the stack of layers its declaration gives it (design S5, §2.1).
//!
//! A declared cell has at most three layers of its own, outermost first: presence (`?`),
//! instances (`*`, with the collection's order), and one content layer (a computation, a leaf of
//! a sort, or a group of cells). An entry that names a cell is judged against two stacks kept
//! apart ([`EntryKind`]): the layers the ancestors between the record's level and the cell put
//! above it ([`CellKind::path`]), and the cell's own ([`CellKind::of`]). The two are not one
//! stack: an ancestor's mark is written at the ancestor's level, never in the entry, so an entry
//! below a `?` or `*` ancestor is refused for that ancestor whatever it spells (S1 (b)), and only
//! an entry with an empty path is judged against its own layers.
//!
//! Both are read through [`CellView`], which a parsed configuration field and a collected host
//! field can each provide: multiplicity, collection order, and the content (the leaf's notation,
//! or the group's name and children).

/// How a collection orders its instances (`cell_type`).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Order {
    /// `cell_type = "List"`.
    List,
    /// `cell_type = "Set"`.
    Set,
    /// `cell_type = "Map"`.
    Map,
}

/// The notation a leaf's sort has inside its value.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Notation {
    /// A sort without notation of its own (`Int`, a user sort, `KItem`).
    Plain,
    /// The builtin `List`.
    List,
    /// A cons list.
    Cons,
    /// The builtin `Map`.
    Map,
    /// The builtin `Set`.
    Set,
}

/// A group of cells: its struct's name and its children's kinds, in declaration order.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct GroupKind {
    /// The struct's name.
    pub name: String,
    /// Each child's field name and kind.
    pub children: Vec<(String, CellKind)>,
}

impl GroupKind {
    /// The kind of the child named `name`.
    #[must_use]
    pub fn child(&self, name: &str) -> Option<&CellKind> {
        self.children
            .iter()
            .find(|(child, _)| child == name)
            .map(|(_, kind)| kind)
    }
}

/// One layer of a cell's stack.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Layer {
    /// `multiplicity = "?"`: the cell may be absent.
    Optional,
    /// `multiplicity = "*"`: the cell is a collection of instances.
    Instances(Order),
    /// A computation, a `KSequence`.
    Computation,
    /// A leaf of a sort.
    Leaf(Notation),
    /// A group of cells.
    Group(GroupKind),
}

/// A cell's stack of layers, outermost first.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct CellKind {
    /// The layers, outermost first.
    pub layers: Vec<Layer>,
}

/// A declared cell's multiplicity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Multiplicity {
    /// Exactly one cell.
    One,
    /// `?`.
    Optional,
    /// `*`, with the collection's order.
    Many(Order),
}

/// A declared cell's content, as a view gives it.
#[derive(Clone, Debug)]
pub enum Content<F> {
    /// A computation cell.
    Computation,
    /// A leaf whose sort has this notation.
    Leaf(Notation),
    /// A nested group: its struct's name and its fields.
    Group {
        /// The struct's name.
        name: String,
        /// The struct's fields, in declaration order.
        children: Vec<F>,
    },
}

/// What [`CellKind`] reads of a declared cell.
pub trait CellView: Sized {
    /// The field's name, which an entry or a record field names.
    fn name(&self) -> String;
    /// The cell's multiplicity.
    fn multiplicity(&self) -> Multiplicity;
    /// The cell's content.
    fn content(&self) -> Content<Self>;
}

impl CellKind {
    /// The cell's own layers (P1): presence or instances, then its content.
    #[must_use]
    pub fn of<F: CellView>(field: &F) -> Self {
        let mut layers = Vec::with_capacity(2);
        match field.multiplicity() {
            Multiplicity::One => {}
            Multiplicity::Optional => layers.push(Layer::Optional),
            Multiplicity::Many(order) => layers.push(Layer::Instances(order)),
        }
        layers.push(match field.content() {
            Content::Computation => Layer::Computation,
            Content::Leaf(notation) => Layer::Leaf(notation),
            Content::Group { name, children } => Layer::Group(GroupKind {
                name,
                children: children
                    .iter()
                    .map(|child| (child.name(), Self::of(child)))
                    .collect(),
            }),
        });
        Self { layers }
    }

    /// The layers the ancestors between a record's level and a cell put above it, `ancestors`
    /// given outermost first. A plain group adds none: K's configuration abstraction supplies it
    /// and it asks nothing of the entry. A `?` ancestor adds its presence and a `*` ancestor its
    /// instances. An entry whose path is not empty names a cell whose content depends on the
    /// ancestor's presence or on which instance is meant, which the entry cannot say: it is
    /// refused for the outermost such ancestor (S1 (b)), and the author writes the ancestor's
    /// group record inside `Some(..)`, or its instance record.
    #[must_use]
    pub fn path<F: CellView>(ancestors: &[F]) -> Self {
        Self {
            layers: ancestors
                .iter()
                .filter_map(|ancestor| match ancestor.multiplicity() {
                    Multiplicity::One => None,
                    Multiplicity::Optional => Some(Layer::Optional),
                    Multiplicity::Many(order) => Some(Layer::Instances(order)),
                })
                .collect(),
        }
    }

    /// What an entry naming `field` through `ancestors` is judged against: the ancestors'
    /// layers and the cell's own, apart.
    #[must_use]
    pub fn entry<F: CellView>(ancestors: &[F], field: &F) -> EntryKind {
        EntryKind {
            path: Self::path(ancestors),
            own: Self::of(field),
        }
    }
}

/// What an entry naming a cell is judged against: the layers of its marked ancestors and the
/// cell's own layers, kept apart (S1 (b)).
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct EntryKind {
    /// The layers the `?` and `*` ancestors between the record's level and the cell put above
    /// it, outermost first ([`CellKind::path`]); empty for a cell named at its own level or
    /// below plain groups only.
    pub path: CellKind,
    /// The cell's own layers ([`CellKind::of`]).
    pub own: CellKind,
}

#[cfg(test)]
mod tests {
    use super::{CellKind, CellView, Content, GroupKind, Layer, Multiplicity, Notation, Order};

    struct Field {
        name: &'static str,
        multiplicity: Multiplicity,
        content: fn() -> Content<Field>,
    }

    impl CellView for Field {
        fn name(&self) -> String {
            self.name.to_owned()
        }
        fn multiplicity(&self) -> Multiplicity {
            self.multiplicity
        }
        fn content(&self) -> Content<Self> {
            (self.content)()
        }
    }

    fn int() -> Content<Field> {
        Content::Leaf(Notation::Plain)
    }

    fn job() -> Content<Field> {
        Content::Group {
            name: "Job".to_owned(),
            children: vec![Field {
                name: "payload",
                multiplicity: Multiplicity::One,
                content: int,
            }],
        }
    }

    #[test]
    fn a_collection_of_groups_has_its_instances_then_its_group() {
        let job = Field {
            name: "job",
            multiplicity: Multiplicity::Many(Order::List),
            content: job,
        };
        let payload = CellKind {
            layers: vec![Layer::Leaf(Notation::Plain)],
        };
        assert_eq!(
            CellKind::of(&job).layers,
            vec![
                Layer::Instances(Order::List),
                Layer::Group(GroupKind {
                    name: "Job".to_owned(),
                    children: vec![("payload".to_owned(), payload)],
                }),
            ]
        );
    }

    #[test]
    fn only_marked_ancestors_add_layers() {
        let plain = Field {
            name: "queue",
            multiplicity: Multiplicity::One,
            content: job,
        };
        let optional = Field {
            name: "maybe",
            multiplicity: Multiplicity::Optional,
            content: job,
        };
        let many = Field {
            name: "jobs",
            multiplicity: Multiplicity::Many(Order::Map),
            content: job,
        };
        let child = Field {
            name: "payload",
            multiplicity: Multiplicity::One,
            content: int,
        };
        assert_eq!(CellKind::path(&[plain]).layers, vec![]);
        let entry = CellKind::entry(&[optional, many], &child);
        assert_eq!(
            entry.path.layers,
            vec![Layer::Optional, Layer::Instances(Order::Map)]
        );
        assert_eq!(entry.own.layers, vec![Layer::Leaf(Notation::Plain)]);
    }
}

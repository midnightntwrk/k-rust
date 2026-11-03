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

    /// The child that keys an instance of this group in a collection ordered by `order`: a Map
    /// collection's instance is keyed by its first child, its declaration's first field, which
    /// is the instance's identity, so an update that changes the instance in place cannot write
    /// it; a List or Set collection's instance has no key child.
    #[must_use]
    pub fn key(&self, order: Order) -> Option<&str> {
        match order {
            Order::Map => self.children.first().map(|(name, _)| name.as_str()),
            Order::List | Order::Set => None,
        }
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

impl CellKind {
    /// The cell's own multiplicity, read from its outermost layer.
    #[must_use]
    pub fn multiplicity(&self) -> Multiplicity {
        match self.layers.first() {
            Some(Layer::Optional) => Multiplicity::Optional,
            Some(Layer::Instances(order)) => Multiplicity::Many(*order),
            _ => Multiplicity::One,
        }
    }

    /// The cell's content layer, its innermost: a computation, a leaf, or a group.
    #[must_use]
    pub fn content(&self) -> Option<&Layer> {
        self.layers.last()
    }

    /// Whether the cell's content is a computation.
    #[must_use]
    pub fn is_computation(&self) -> bool {
        matches!(self.content(), Some(Layer::Computation))
    }

    /// The notation of the cell's content, when its content is a leaf.
    #[must_use]
    pub fn leaf(&self) -> Option<Notation> {
        match self.content() {
            Some(Layer::Leaf(notation)) => Some(*notation),
            _ => None,
        }
    }

    /// The cell's group, when its content is one.
    #[must_use]
    pub fn group(&self) -> Option<&GroupKind> {
        match self.content() {
            Some(Layer::Group(group)) => Some(group),
            _ => None,
        }
    }
}

/// The sort a production makes a cons list: the result sort of the cons production of a
/// `#[k::syntax_list]` enum or of a `#[k::cons_list]` constructors enum. A cell whose leaf has
/// that sort holds a cons list ([`Notation::Cons`]).
#[must_use]
pub fn cons_list_sort<S: crate::stage::Stage>(
    grammar: &crate::StageGrammarDescriptor<S>,
) -> Option<&S::Sort> {
    let crate::StageGrammarDescriptor::Production(production) = grammar else {
        return None;
    };
    production
        .attributes
        .iter()
        .any(|attribute| {
            matches!(
                attribute,
                crate::TransportProductionAttribute::ListCons { .. }
                    | crate::TransportProductionAttribute::ConsList { .. }
            )
        })
        .then_some(&production.result_sort)
}

impl From<Order> for crate::CellCollectionType {
    fn from(order: Order) -> Self {
        match order {
            Order::List => Self::List,
            Order::Set => Self::Set,
            Order::Map => Self::Map,
        }
    }
}

/// The notation a leaf of the builtin sort `sort` has; [`Notation::Plain`] for the others.
/// `KSequence` is not a leaf's notation: the computation is the content of a `KCell`.
#[must_use]
pub const fn builtin_notation(sort: crate::BuiltinSort) -> Notation {
    match sort {
        crate::BuiltinSort::List => Notation::List,
        crate::BuiltinSort::Map => Notation::Map,
        crate::BuiltinSort::Set => Notation::Set,
        _ => Notation::Plain,
    }
}

/// The multiplicity a declared field's `multiplicity` and `cell_type` give: `"?"` is presence,
/// `"*"` instances in the `cell_type`'s order. Descriptor validation pairs `cell_type` with
/// `"*"` (`validate_cell_metadata`); an unvalidated `"*"` without one reads as a Set, as the
/// parsed view reads it.
#[must_use]
pub fn declared_multiplicity(
    multiplicity: Option<&str>,
    cell_type: Option<crate::CellCollectionType>,
) -> Multiplicity {
    match (multiplicity, cell_type) {
        (Some("?"), _) => Multiplicity::Optional,
        (Some("*"), cell_type) => Multiplicity::Many(match cell_type {
            Some(crate::CellCollectionType::List) => Order::List,
            Some(crate::CellCollectionType::Map) => Order::Map,
            Some(crate::CellCollectionType::Set) | None => Order::Set,
        }),
        _ => Multiplicity::One,
    }
}

/// A collected (descriptor) cell field read as a [`CellView`]: the collector's resolved
/// declaration, as every compile-path reader after collection sees it. A nested group's
/// declaration is looked up in the index; a leaf's notation is its resolved sort's (the builtin
/// `List`, `Map` and `Set`, or a declared cons list). The computation is the content of a
/// `KCell`: a `Cell<KSequence>` is a leaf of sort `K`, which a `Cell(..)` entry reads as one term.
///
/// A nested declaration that is missing, or that is one of the cell's own ancestors (a cycle,
/// which lowering refuses), reads as a group with no children.
#[derive(Clone, Debug)]
pub struct DescriptorCell<'i, 'a> {
    field: &'a crate::DescriptorCellField,
    index: &'i crate::DescriptorIndex<'a>,
    /// The nested declarations from the outermost field down to this one's owner.
    ancestors: Vec<&'a crate::StableItemId>,
}

impl<'i, 'a> DescriptorCell<'i, 'a> {
    /// The view of `field`, whose nested declarations `index` holds.
    #[must_use]
    pub const fn new(
        field: &'a crate::DescriptorCellField,
        index: &'i crate::DescriptorIndex<'a>,
    ) -> Self {
        Self {
            field,
            index,
            ancestors: Vec::new(),
        }
    }

    /// The field.
    #[must_use]
    pub const fn field(&self) -> &'a crate::DescriptorCellField {
        self.field
    }

    /// The cell's own layers ([`CellKind::of`]).
    #[must_use]
    pub fn kind(&self) -> CellKind {
        CellKind::of(self)
    }
}

impl CellView for DescriptorCell<'_, '_> {
    fn name(&self) -> String {
        // An entry names a field by its identifier without `r#`, as Rust names a field.
        let field = &self.field.rust_field;
        field.strip_prefix("r#").unwrap_or(field).to_owned()
    }

    fn multiplicity(&self) -> Multiplicity {
        declared_multiplicity(
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
            crate::ProtocolCellContent::Leaf {
                wrapper: crate::CellWrapper::KCell,
                ..
            } => Content::Computation,
            crate::ProtocolCellContent::Leaf { sort, .. } => Content::Leaf(match &sort.sort {
                crate::DescriptorSortRef::Builtin(builtin) => builtin_notation(*builtin),
                crate::DescriptorSortRef::Declared(id) if self.index.is_cons_list(id) => {
                    Notation::Cons
                }
                _ => Notation::Plain,
            }),
            crate::ProtocolCellContent::Nested { declaration } => {
                let id = &declaration.declaration;
                let children = if self.ancestors.contains(&id) {
                    Vec::new()
                } else {
                    self.index.cell(id).map_or_else(
                        |_| Vec::new(),
                        |nested| {
                            let mut ancestors = self.ancestors.clone();
                            ancestors.push(id);
                            nested
                                .fields
                                .iter()
                                .map(|field| Self {
                                    field,
                                    index: self.index,
                                    ancestors: ancestors.clone(),
                                })
                                .collect()
                        },
                    )
                };
                Content::Group {
                    name: id.item_name().to_owned(),
                    children,
                }
            }
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
    fn a_map_collection_is_keyed_by_its_first_child() {
        let int = || CellKind {
            layers: vec![Layer::Leaf(Notation::Plain)],
        };
        let account = GroupKind {
            name: "Account".to_owned(),
            children: vec![("id".to_owned(), int()), ("balance".to_owned(), int())],
        };
        assert_eq!(account.key(Order::Map), Some("id"));
        assert_eq!(account.key(Order::List), None);
        assert_eq!(account.key(Order::Set), None);
        let empty = GroupKind {
            name: "Empty".to_owned(),
            children: Vec::new(),
        };
        assert_eq!(empty.key(Order::Map), None);
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

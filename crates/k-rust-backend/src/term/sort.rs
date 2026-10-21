//! Backend sorts as hash-consed `Copy` handles: one process-wide interner holds one node per
//! distinct sort, so cloning a sort copies a pointer and equality compares two pointers.
//!
//! ```toml algorithm-representation
//! id = "representation.backend.sort"
//! name = "hash-consed backend sort with a pointer equality and a name-prefix order key"
//! type = "k_rust_backend::term::Sort"
//! sites = ["Sort", "SortNode", "Sorts", "Sort::application", "Sort::simple", "Sort::variable",
//!     "Sort::builtin", "Sort::of_node", "Sorts::new", "Sort::eq", "Sort::cmp", "Sort::hash",
//!     "Sorts::eq", "Sorts::cmp", "order_key"]
//! invariant = """\
//! The interner's initialization interns the builtin sorts first; after it, Sort::of_node is the \
//! only place a Sort is built, and it returns the node the interner holds for the content \
//! (variant, name text, argument handles), leaking a new one only when there is none; Sorts::new \
//! likewise returns the interned slice of the given handles. The arguments of an \
//! interned node are interned handles, so by induction on depth two handles are the same pointer \
//! exactly when their sorts are structurally equal: Eq for Sort is pointer equality, and Eq for \
//! Sorts is pointer equality of nonempty slices (all empty ones are equal). Ord for Sort is the \
//! order of the variants (Application before Variable), then of the names as byte strings, then \
//! of the arguments lexicographically; it decides equal pointers as Equal and otherwise compares \
//! the order key first, the first 16 bytes of the name big-endian and zero-padded, which orders \
//! two names as their bytes do whenever the keys differ, and compares the full names only when \
//! the keys agree. Hash and Debug of Sort and Sorts are those of the node and of the slice, so \
//! they write the same bytes and text as a derived enum Sort { Application { name, arguments: \
//! Vec<Sort> }, Variable(name) }. Nodes are never freed: their number is that of the distinct \
//! sorts the process builds."""
//! tests = ["crates/k-rust-backend/tests/backend/term_order.rs"]
//! ```

use std::{
    borrow::Borrow,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    ops::Deref,
    ptr,
    sync::{Arc, LazyLock, PoisonError, RwLock},
};

use k_rust_kore::names::BuiltinSort;
use rustc_hash::FxHashSet;

use super::Name;

/// A sort of the backend: a `Copy` handle to the one interned node of its content.
#[derive(Clone, Copy)]
pub struct Sort(&'static SortData);

/// The content of a sort, read through [`Sort::node`].
#[derive(Debug, Eq, Hash, PartialEq)]
pub enum SortNode {
    Application { name: Name, arguments: Sorts },
    Variable(Name),
}

/// A `Copy` handle to an interned sequence of sorts, the arguments of a sort application.
#[derive(Clone, Copy)]
pub struct Sorts(&'static [Sort]);

/// An interned node with what is derived once from it.
struct SortData {
    node: SortNode,
    /// [`order_key`] of the node's name.
    key: u128,
    /// The position in `BuiltinSort::ALL` of the builtin this sort is, when it is the nullary
    /// application of a builtin's KORE name.
    builtin: Option<u8>,
    /// True when a sort variable occurs anywhere in the sort.
    has_variable: bool,
}

/// The first 16 bytes of `name`, big-endian, zero-padded. When the keys of two names differ,
/// they order as the names do: at the first byte where the keys differ, either both names have a
/// byte and they first differ there, or one name has ended (a zero of padding) and the other has
/// a nonzero byte, so the ended name is a proper prefix of the other and orders first.
fn order_key(name: &str) -> u128 {
    let bytes = name.as_bytes();
    let mut key = [0; 16];
    let length = bytes.len().min(key.len());
    key[..length].copy_from_slice(&bytes[..length]);
    u128::from_be_bytes(key)
}

// `Sort::builtin` indexes the interned builtins by the variant's discriminant.
const _: () = {
    let mut index = 0;
    while index < BuiltinSort::ALL.len() {
        assert!(BuiltinSort::ALL[index] as usize == index);
        index += 1;
    }
};

/// An interned node in the interner's set, looked up by its content.
struct Entry(&'static SortData);

impl Borrow<SortNode> for Entry {
    fn borrow(&self) -> &SortNode {
        &self.0.node
    }
}

impl PartialEq for Entry {
    fn eq(&self, other: &Self) -> bool {
        self.0.node == other.0.node
    }
}

impl Eq for Entry {}

impl Hash for Entry {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.node.hash(state);
    }
}

struct Interner {
    nodes: RwLock<FxHashSet<Entry>>,
    lists: RwLock<FxHashSet<&'static [Sort]>>,
    /// The nullary applications of the builtins' KORE names, in the order of `BuiltinSort::ALL`,
    /// interned first, with the names of [`super::builtin_names`].
    builtins: [Sort; BuiltinSort::ALL.len()],
}

static INTERNER: LazyLock<Interner> = LazyLock::new(|| {
    let mut nodes = FxHashSet::default();
    let builtins = std::array::from_fn(|index| {
        let node = SortNode::Application {
            name: super::builtin_names()[index].clone(),
            arguments: Sorts::EMPTY,
        };
        let data = leak(node, Some(u8::try_from(index).expect("few builtin sorts")));
        nodes.insert(Entry(data));
        Sort(data)
    });
    Interner {
        nodes: RwLock::new(nodes),
        lists: RwLock::new(FxHashSet::default()),
        builtins,
    }
});

fn leak(node: SortNode, builtin: Option<u8>) -> &'static SortData {
    let (name, has_variable) = match &node {
        SortNode::Application { name, arguments } => (
            name,
            arguments.iter().any(|argument| argument.0.has_variable),
        ),
        SortNode::Variable(name) => (name, true),
    };
    let key = order_key(name);
    Box::leak(Box::new(SortData {
        node,
        key,
        builtin,
        has_variable,
    }))
}

impl Sort {
    /// The interned sort of `node`, which is built only here.
    fn of_node(node: SortNode) -> Self {
        let interner = &*INTERNER;
        if let Some(entry) = interner
            .nodes
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .get(&node)
        {
            return Self(entry.0);
        }
        let mut nodes = interner
            .nodes
            .write()
            .unwrap_or_else(PoisonError::into_inner);
        if let Some(entry) = nodes.get(&node) {
            return Self(entry.0);
        }
        // Every builtin node was interned first, so a node of a builtin's content is found above.
        let data = leak(node, None);
        nodes.insert(Entry(data));
        Self(data)
    }

    pub fn application(name: impl Into<Name>, arguments: Vec<Self>) -> Self {
        Self::application_of(name, Sorts::new(&arguments))
    }

    /// The application of `name` to interned `arguments`.
    pub fn application_of(name: impl Into<Name>, arguments: Sorts) -> Self {
        Self::of_node(SortNode::Application {
            name: name.into(),
            arguments,
        })
    }

    pub fn simple(name: impl Into<Name>) -> Self {
        Self::application_of(name, Sorts::EMPTY)
    }

    pub fn variable(name: impl Into<Name>) -> Self {
        Self::of_node(SortNode::Variable(name.into()))
    }

    /// A builtin sort, the nullary application of its KORE name, read from a table built once.
    #[inline]
    pub fn builtin(sort: BuiltinSort) -> Self {
        INTERNER.builtins[sort as usize]
    }

    /// The content of the sort.
    #[inline]
    #[must_use]
    pub fn node(self) -> &'static SortNode {
        &self.0.node
    }

    /// The name of the application or of the variable.
    #[inline]
    #[must_use]
    pub fn name(self) -> &'static Name {
        match &self.0.node {
            SortNode::Application { name, .. } | SortNode::Variable(name) => name,
        }
    }

    /// The arguments of an application; none for a variable.
    #[inline]
    #[must_use]
    pub fn arguments(self) -> Sorts {
        match &self.0.node {
            SortNode::Application { arguments, .. } => *arguments,
            SortNode::Variable(_) => Sorts::EMPTY,
        }
    }

    /// The name of a sort variable; `None` for an application.
    #[inline]
    #[must_use]
    pub fn as_variable(self) -> Option<&'static Name> {
        match &self.0.node {
            SortNode::Variable(name) => Some(name),
            SortNode::Application { .. } => None,
        }
    }

    /// True for the nullary application of the builtin's KORE name.
    #[inline]
    pub fn is_builtin(&self, sort: BuiltinSort) -> bool {
        *self == Self::builtin(sort)
    }

    /// The position in `BuiltinSort::ALL` of the builtin sort this sort is, when it is the
    /// nullary application of that builtin's KORE name; `None` for any other sort.
    #[inline]
    pub(crate) fn shared_builtin_index(&self) -> Option<usize> {
        self.0.builtin.map(usize::from)
    }

    /// True when a sort variable occurs anywhere in the sort.
    #[inline]
    pub fn has_variable(&self) -> bool {
        self.0.has_variable
    }
}

impl PartialEq for Sort {
    /// Pointer equality, which is structural equality: the interner holds one node per content.
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.0, other.0)
    }
}

impl Eq for Sort {}

impl Hash for Sort {
    /// The node's derived hash, the bytes a derived `Hash` of the enum wrote.
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.node.hash(state);
    }
}

impl fmt::Debug for Sort {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0.node, formatter)
    }
}

impl PartialOrd for Sort {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Sort {
    /// The order of the variants, then of the names, then of the arguments. Equal handles are
    /// equal sorts; otherwise the names' order keys decide whenever they differ.
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        if ptr::eq(self.0, other.0) {
            return Ordering::Equal;
        }
        order_distinct(self.0, other.0)
    }
}

fn order_distinct(left: &SortData, right: &SortData) -> Ordering {
    let names = |name: &Name, other_name: &Name| {
        left.key.cmp(&right.key).then_with(|| {
            if Arc::ptr_eq(name, other_name) {
                Ordering::Equal
            } else {
                name.as_bytes().cmp(other_name.as_bytes())
            }
        })
    };
    match (&left.node, &right.node) {
        (
            SortNode::Application { name, arguments },
            SortNode::Application {
                name: other_name,
                arguments: other_arguments,
            },
        ) => names(name, other_name).then_with(|| arguments.cmp(other_arguments)),
        (SortNode::Variable(name), SortNode::Variable(other_name)) => names(name, other_name),
        (SortNode::Application { .. }, SortNode::Variable(_)) => Ordering::Less,
        (SortNode::Variable(_), SortNode::Application { .. }) => Ordering::Greater,
    }
}

impl Sorts {
    pub const EMPTY: Self = Self(&[]);

    /// The interned sequence of `sorts`.
    pub fn new(sorts: &[Sort]) -> Self {
        if sorts.is_empty() {
            return Self::EMPTY;
        }
        let interner = &*INTERNER;
        if let Some(list) = interner
            .lists
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .get(sorts)
        {
            return Self(list);
        }
        let mut lists = interner
            .lists
            .write()
            .unwrap_or_else(PoisonError::into_inner);
        if let Some(list) = lists.get(sorts) {
            return Self(list);
        }
        let list: &'static [Sort] = Box::leak(sorts.to_vec().into_boxed_slice());
        lists.insert(list);
        Self(list)
    }

    #[inline]
    #[must_use]
    pub fn as_slice(self) -> &'static [Sort] {
        self.0
    }
}

impl AsRef<[Sort]> for Sorts {
    fn as_ref(&self) -> &[Sort] {
        self.0
    }
}

impl Default for Sorts {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl Deref for Sorts {
    type Target = [Sort];

    #[inline]
    fn deref(&self) -> &[Sort] {
        self.0
    }
}

impl From<Vec<Sort>> for Sorts {
    fn from(sorts: Vec<Sort>) -> Self {
        Self::new(&sorts)
    }
}

impl From<&[Sort]> for Sorts {
    fn from(sorts: &[Sort]) -> Self {
        Self::new(sorts)
    }
}

impl FromIterator<Sort> for Sorts {
    fn from_iter<I: IntoIterator<Item = Sort>>(iter: I) -> Self {
        let sorts: Vec<Sort> = iter.into_iter().collect();
        Self::new(&sorts)
    }
}

impl IntoIterator for Sorts {
    type Item = &'static Sort;
    type IntoIter = std::slice::Iter<'static, Sort>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> IntoIterator for &'a Sorts {
    type Item = &'a Sort;
    type IntoIter = std::slice::Iter<'a, Sort>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl PartialEq for Sorts {
    /// Pointer equality of nonempty slices, which is elementwise equality: the interner holds
    /// one slice per sequence of handles.
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len() && (self.0.is_empty() || ptr::eq(self.0, other.0))
    }
}

impl Eq for Sorts {}

impl PartialOrd for Sorts {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Sorts {
    /// The lexicographic order of the sequences.
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            return Ordering::Equal;
        }
        self.0.cmp(other.0)
    }
}

impl Hash for Sorts {
    /// The slice's hash, the bytes the hash of a `Vec<Sort>` of the same sorts writes.
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl fmt::Debug for Sorts {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.0, formatter)
    }
}

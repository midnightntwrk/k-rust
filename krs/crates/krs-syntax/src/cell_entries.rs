//! Cell-entry admission (design S5, §2.3): one judgement of what an entry means, in every form.
//!
//! [`admit`] judges one entry's [`EntrySpelling`] against what its cell's declaration gives it
//! ([`krs_ir::cell_kind::EntryKind`]: the layers of the cell's marked ancestors, its path, and
//! the cell's own layers, kept apart):
//!
//! 1. **form**: what the spelling and its side alone refuse: `_`, `name @ P` and a named rest
//!    `name @ ..` outside a pattern, `None` or an anonymous rest in an initializer's value, an
//!    anonymous rest in a map literal outside a `cells!` pattern;
//! 2. **kind**, against the cell's own layers, outermost first: the outermost layer's mark admits
//!    the entry and its inside is judged against the next layer; a mark no layer of the stack
//!    has gives that mark's refusal; a deeper layer's mark, or a value where the outermost layer
//!    has a mark, gives the missing layer's refusal;
//! 3. **path**: an entry naming a cell below a `?` or `*` ancestor is refused for the outermost
//!    such ancestor, whatever it spells: the ancestor's presence and the instance it means are
//!    written at the ancestor's level (S1 (b)). It comes after the kind, since its advice writes
//!    the entry inside the ancestor's mark, where a spelling the cell's own layers refuse would
//!    be refused again.
//!
//! [`pair`] then judges the entry with its rule: a result's rest against its subject's, at its
//! cell's content root and at each child's of the group and instance records it writes, a Map
//! collection's instance key ([`GroupKind::key`]), which a created instance writes and an
//! update keeps, a
//! result's group record with a bare `..` for a group that exists, a result over a cell the
//! subject does not match (Q1's overwrite, where it means one configuration), an absence test,
//! and the lint of a subject entry that constrains nothing.
//!
//! An admitted entry whose value positions hold a term whose sort the lattice must check is
//! [`Admitted::sorted`]; the compiler judges that sort.
//!
//! The marks per form: presence is `Some`/`None` (and `k::absent!` in an initializer);
//! instances are brackets (a List collection) or braces (Set, Map) in readable, an instance
//! list or set in `cells!`; a computation is brackets, `KCell(..)` or `k::k![..]`; a leaf has no
//! mark but `Cell(..)` in `cells!`, and inside it brackets (a list) or map notation (a map); a
//! group has none, since a record is a value.
//!
//! Where the class matrix states a departure from these principles (`[cell-exception]`), the
//! departure is written here as the table states it, with its reason: a readable computation is
//! matched from its front, a List collection's back instance is not matched in place, an
//! initializer's `k::k![..]` splices no configuration variable's computation (`..pgm`), and a
//! readable record's top-level map read has no result side and reads its value as a fresh
//! binder.

use krs_ir::cell_kind::{GroupKind, Layer, Notation, Order};

pub use krs_ir::cell_kind::EntryKind;

use crate::cell_entry::{
    EntryForm, EntryMap, EntryRecord, EntryRest, EntrySeq, EntrySpelling, RecordTail, RestPlace,
};

/// The side an entry stands on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EntrySide {
    /// A rule's or claim's subject (a pattern).
    Subject,
    /// A rule's or claim's result.
    Result,
    /// An initializer's value.
    Initializer,
}

/// Why an entry is refused; [`Refusal::class`] names it as the class matrix does.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Refusal {
    /// `_` outside a pattern.
    WildcardOutsidePattern,
    /// `name @ P` or a named rest `name @ ..` outside a pattern (a result or an initializer):
    /// it names what a pattern matched. A result writes `..` to keep the subject's anonymous rest
    /// and `..name` to put a named one back; an initializer updates with `..base`.
    AliasOutsidePattern,
    /// `None` in an initializer.
    NoneInInitializer,
    /// A rest in an initializer's value, which is complete.
    InitializerRemainder,
    /// `..` in a map literal outside a `cells!` pattern.
    AnonymousRestInMapLiteral,
    /// Presence on a cell that has no `?` layer.
    PresenceOnPlainCell,
    /// Brackets where no layer reads them.
    BracketReading,
    /// Instances on a cell that has no `*` layer.
    InstancesOnPlainCell,
    /// Instance notation that is no instance of the collection.
    InstanceListShape,
    /// Map notation where no layer is a map.
    MapNotationAtNonMap,
    /// A missing or misplaced leaf or computation wrapper.
    CellWrapper,
    /// A value on a `?` cell without its presence.
    OptionalWithoutPresence,
    /// A value on a `*` cell without its instances.
    CollectionWithoutInstances,
    /// An entry naming a cell below a `?` ancestor, whose presence it would silently require:
    /// the author writes the ancestor's group record inside `Some(..)`,
    /// `Some(G { child: .., .. })` (S1 (b)).
    BelowOptionalAncestor,
    /// An entry naming a cell below a `*` ancestor, where no single cell has the content it
    /// names: the author names the instance with an instance record,
    /// `instances: { G { child: .., .. }, .. }` (S1 (b)).
    BelowCollectionAncestor,
    /// A result writing a `?` cell the subject does not match, whose presence the rule does not
    /// know (Q1, P5).
    UnmatchedOptionalResult,
    /// A group record at a configuration position that names neither every child nor `..`.
    RecordMissingChildren,
    /// A readable rule that drops or captures the continuation.
    ContinuationInReadable,
    /// `None` in a subject whose result does not create the cell.
    AbsenceTestWithoutCreation,
    /// A result rest that is not its subject's.
    RestMismatch,
    /// A result's group record with a bare `..` for a group that exists, matched or overwritten:
    /// a bare `..` in a result is Rust's default fields, which only a created instance has (its
    /// template).
    OpenRecordOutsidePattern,
    /// A readable computation's rest before an item: the computation is matched from its
    /// front (the class matrix's E1).
    ComputationBackItem,
    /// A readable map read at a result entry's head, which has no result side yet: the result
    /// is the frame write `Cell(k::map![k -> v, ..])` (a stated limitation of the readable
    /// record's top-level route).
    MapReadInResult,
    /// A Map collection's instance that does not keep its key, its first child, which is its
    /// identity: a created instance that does not write it (a bare `..` takes the template's
    /// fields, which state no identity), or an instance update (`..me`) that writes it as
    /// anything but the binder the subject matched the key with (a literal, another name, a
    /// computed value, or a key the labelled instance does not name), since an update changes
    /// the instance in place and another key is another entry of the map. Written as the
    /// subject's own key binder, the key is unchanged.
    MapCollectionKey,
    /// A readable map read at a record's top level whose value is not a fresh binder (a stated
    /// limitation of the readable record's top-level route; inside an instance record the value
    /// is matched, P5).
    MapReadValueBinder,
}

impl Refusal {
    /// The class matrix's name of the refusal.
    #[must_use]
    pub const fn class(self) -> &'static str {
        match self {
            Self::WildcardOutsidePattern => "wildcard-outside-pattern",
            Self::AliasOutsidePattern => "alias-outside-pattern",
            Self::NoneInInitializer => "none-in-initializer",
            Self::InitializerRemainder => "initializer-remainder",
            Self::AnonymousRestInMapLiteral => "anonymous-rest-in-map-literal",
            Self::PresenceOnPlainCell => "presence-on-plain-cell",
            Self::BracketReading => "bracket-reading",
            Self::InstancesOnPlainCell => "instances-on-plain-cell",
            Self::InstanceListShape => "instance-list-shape",
            Self::MapNotationAtNonMap => "map-notation-at-non-map",
            Self::CellWrapper => "cell-wrapper",
            Self::OptionalWithoutPresence | Self::BelowOptionalAncestor => {
                "optional-without-presence"
            }
            Self::CollectionWithoutInstances | Self::BelowCollectionAncestor => {
                "collection-without-instances"
            }
            Self::UnmatchedOptionalResult => "unmatched-optional-result",
            Self::RecordMissingChildren => "record-missing-children",
            Self::ContinuationInReadable => "continuation-in-readable",
            Self::AbsenceTestWithoutCreation => "absence-test-without-creation",
            Self::RestMismatch => "rest-mismatch",
            Self::OpenRecordOutsidePattern => "open-record-outside-pattern",
            Self::ComputationBackItem => "computation-back-item",
            Self::MapReadInResult => "map-read-in-result",
            Self::MapCollectionKey => "map-collection-key",
            Self::MapReadValueBinder => "map-read-value-binder",
        }
    }
}

/// The lint an admitted entry owes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Lint {
    /// A subject entry on a cell the result leaves out that matches every content and binds
    /// nothing: it constrains nothing.
    NoEffectEntry,
}

impl Lint {
    /// The class matrix's name of the lint.
    #[must_use]
    pub const fn class(self) -> &'static str {
        match self {
            Self::NoEffectEntry => "no-effect-entry",
        }
    }
}

/// An admitted entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Admitted {
    /// Whether a value position holds a term whose sort the lattice must check: a literal, a
    /// call, a configuration variable, a record that is not its position's group, a bound name,
    /// or any `cells!` name (a typed parameter). A fresh readable name and `_` take their
    /// position's sort.
    pub sorted: bool,
}

/// The mark a spelling carries in a form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mark {
    Presence,
    Sequence,
    InstanceSet,
    InstanceList,
    Map,
    Leaf,
    Computation,
    Value,
}

fn mark(form: EntryForm, spelling: &EntrySpelling) -> Mark {
    let readable = form.is_readable();
    match spelling {
        EntrySpelling::Present(_) | EntrySpelling::Missing | EntrySpelling::Absent(_) => {
            Mark::Presence
        }
        EntrySpelling::Cell(_) => Mark::Leaf,
        EntrySpelling::KCell(_) => Mark::Computation,
        EntrySpelling::InstanceList(_) => Mark::InstanceList,
        EntrySpelling::InstanceSet(_) => Mark::InstanceSet,
        EntrySpelling::KMacro(_) if form == EntryForm::Initializer => Mark::Computation,
        EntrySpelling::Brackets(_) if form != EntryForm::Cells => Mark::Sequence,
        EntrySpelling::Braces(_) if readable => Mark::InstanceSet,
        EntrySpelling::MapRead(_) if readable => Mark::Map,
        EntrySpelling::MapLiteral(_) if form == EntryForm::Initializer => Mark::Map,
        _ => Mark::Value,
    }
}

/// Whether `layer` reads `mark` in `form`.
fn reads(form: EntryForm, layer: &Layer, mark: Mark) -> bool {
    let cells = form == EntryForm::Cells;
    match layer {
        Layer::Optional => mark == Mark::Presence,
        Layer::Instances(Order::List) if cells => mark == Mark::InstanceList,
        Layer::Leaf(_) if cells => mark == Mark::Leaf,
        Layer::Instances(Order::List) | Layer::Leaf(Notation::List | Notation::Cons) => {
            mark == Mark::Sequence
        }
        Layer::Instances(Order::Set | Order::Map) => mark == Mark::InstanceSet,
        Layer::Computation => mark == Mark::Computation || (!cells && mark == Mark::Sequence),
        Layer::Leaf(Notation::Map) => mark == Mark::Map,
        Layer::Leaf(Notation::Plain | Notation::Set) | Layer::Group(_) => false,
    }
}

/// Whether `layer` has a mark of its own in `form`, which a value at its position lacks.
const fn marked(form: EntryForm, layer: &Layer) -> bool {
    match layer {
        Layer::Optional | Layer::Instances(_) | Layer::Computation => true,
        Layer::Leaf(_) => matches!(form, EntryForm::Cells),
        Layer::Group(_) => false,
    }
}

/// The refusal for a missing `layer`.
const fn missing(layer: &Layer) -> Refusal {
    match layer {
        Layer::Optional => Refusal::OptionalWithoutPresence,
        Layer::Instances(_) => Refusal::CollectionWithoutInstances,
        Layer::Computation | Layer::Leaf(_) | Layer::Group(_) => Refusal::CellWrapper,
    }
}

/// The refusal for `mark`, which no layer of `stack` reads.
fn foreign(mark: Mark, stack: &[Layer]) -> Refusal {
    match mark {
        Mark::Presence => Refusal::PresenceOnPlainCell,
        Mark::Sequence => Refusal::BracketReading,
        Mark::InstanceSet | Mark::InstanceList
            if stack
                .iter()
                .any(|layer| matches!(layer, Layer::Instances(_))) =>
        {
            Refusal::InstanceListShape
        }
        Mark::InstanceSet | Mark::InstanceList => Refusal::InstancesOnPlainCell,
        Mark::Map => Refusal::MapNotationAtNonMap,
        Mark::Leaf | Mark::Computation | Mark::Value => Refusal::CellWrapper,
    }
}

fn sequence(spelling: &EntrySpelling) -> Option<&EntrySeq> {
    match spelling {
        EntrySpelling::Brackets(seq)
        | EntrySpelling::Braces(seq)
        | EntrySpelling::KCell(seq)
        | EntrySpelling::InstanceList(seq)
        | EntrySpelling::InstanceSet(seq)
        | EntrySpelling::KMacro(seq) => Some(seq),
        _ => None,
    }
}

fn map_entries(spelling: &EntrySpelling) -> Option<&EntryMap> {
    match spelling {
        EntrySpelling::MapRead(map) | EntrySpelling::MapLiteral(map) => Some(map),
        _ => None,
    }
}

/// A record of `group` at a configuration position, or the fragment it abbreviates, names
/// every child, or writes `..`: records follow Rust.
fn names_every_child(record: &EntryRecord, group: &GroupKind) -> Result<(), Refusal> {
    if matches!(record.tail, RecordTail::Exact) && record.fields.len() != group.children.len() {
        return Err(Refusal::RecordMissingChildren);
    }
    Ok(())
}

/// The spellings directly inside `spelling`.
fn inner(spelling: &EntrySpelling) -> Vec<&EntrySpelling> {
    match spelling {
        EntrySpelling::Present(one)
        | EntrySpelling::Absent(one)
        | EntrySpelling::Cell(one)
        | EntrySpelling::Alias(_, one) => vec![one],
        EntrySpelling::Record(record) | EntrySpelling::Fragment(record) => {
            record.fields.iter().map(|(_, value)| value).collect()
        }
        EntrySpelling::Call(arguments) => arguments.iter().collect(),
        _ => sequence(spelling).map_or_else(
            || {
                map_entries(spelling).map_or_else(Vec::new, |map| {
                    map.entries.iter().flat_map(|(k, v)| [k, v]).collect()
                })
            },
            |seq| seq.items.iter().collect(),
        ),
    }
}

struct Admission<'b> {
    form: EntryForm,
    side: EntrySide,
    bound: &'b dyn Fn(&str) -> bool,
    sorted: bool,
}

impl Admission<'_> {
    /// Step 1, over the whole spelling.
    fn form(&self, spelling: &EntrySpelling) -> Result<(), Refusal> {
        let pattern = self.side == EntrySide::Subject;
        let initializer = self.side == EntrySide::Initializer;
        match spelling {
            EntrySpelling::Wild if !pattern => return Err(Refusal::WildcardOutsidePattern),
            EntrySpelling::Missing if initializer => return Err(Refusal::NoneInInitializer),
            // `name @ P` stands in a pattern only, at any depth, and a rest is no exception: a
            // result keeps the subject's anonymous rest with `..` and puts a named one back with
            // `..name`; the subject drops a rest by naming it `_rest @ ..` and not putting it
            // back. An initializer is a result with no subject: nothing in it is a pattern.
            _ if !pattern
                && (matches!(spelling, EntrySpelling::Alias(..))
                    || matches!(
                        sequence(spelling)
                            .and_then(|seq| seq.rest.as_ref().map(|(rest, _)| rest))
                            .or_else(|| map_entries(spelling).and_then(|map| map.rest.as_ref())),
                        Some(EntryRest::Named(_))
                    )) =>
            {
                return Err(Refusal::AliasOutsidePattern);
            }
            // An initializer's value is the whole initial content: it keeps no unwritten rest
            // (P5). A named base, `[0, ..base]`, is an update and stays.
            EntrySpelling::KMacro(seq) | EntrySpelling::Brackets(seq)
                if initializer && matches!(seq.rest, Some((EntryRest::Anonymous, _))) =>
            {
                return Err(Refusal::InitializerRemainder);
            }
            // Its computation splices no configuration variable's, `k::k![x, ..pgm]`: an
            // item-sorted variable is an item, so `k::k![x, pgm]` says it (E3).
            EntrySpelling::KMacro(seq)
                if initializer && matches!(seq.rest, Some((EntryRest::Splice(_), _))) =>
            {
                return Err(Refusal::InitializerRemainder);
            }
            // `..` names the rest of a map only where a `cells!` pattern frames one.
            EntrySpelling::MapLiteral(map)
                if map.rest == Some(EntryRest::Anonymous)
                    && !(self.form == EntryForm::Cells && pattern) =>
            {
                return Err(Refusal::AnonymousRestInMapLiteral);
            }
            _ => {}
        }
        inner(spelling)
            .into_iter()
            .try_for_each(|one| self.form(one))
    }

    /// Step 2 against `stack`, outermost layer first.
    fn kind(
        &mut self,
        stack: &[Layer],
        spelling: &EntrySpelling,
        head: bool,
    ) -> Result<(), Refusal> {
        if let EntrySpelling::Alias(_, pattern) = spelling {
            return self.kind(stack, pattern, head);
        }
        let Some((outer, below)) = stack.split_first() else {
            self.value(spelling);
            return Ok(());
        };
        // An initializer's value for a collection, at any depth, is one instance's template.
        if self.side == EntrySide::Initializer && matches!(outer, Layer::Instances(_)) {
            return self.kind(below, spelling, head);
        }
        let mark = mark(self.form, spelling);
        if mark == Mark::Value {
            if marked(self.form, outer) {
                return Err(missing(outer));
            }
            if let Layer::Group(group) = outer {
                return self.group(group, spelling);
            }
            self.value(spelling);
            return Ok(());
        }
        if !reads(self.form, outer, mark) {
            return Err(if below.iter().any(|layer| reads(self.form, layer, mark)) {
                missing(outer)
            } else {
                foreign(mark, stack)
            });
        }
        match (outer, spelling) {
            (Layer::Optional, EntrySpelling::Present(content) | EntrySpelling::Absent(content)) => {
                self.kind(below, content, head)
            }
            (Layer::Optional, _) => Ok(()),
            (Layer::Leaf(notation), EntrySpelling::Cell(content)) => self.leaf(*notation, content),
            (Layer::Instances(order), _) => self.instances(*order, below, spelling),
            (Layer::Leaf(_), EntrySpelling::MapRead(map)) => {
                // Both limitations are the readable record's top-level route's; inside an
                // instance record a map read is the child's own entry, lowered by its route.
                if head && self.form.is_readable() && self.side == EntrySide::Result {
                    return Err(Refusal::MapReadInResult);
                }
                if head
                    && map.entries.iter().any(|(_, value)| {
                        !matches!(value, EntrySpelling::Binder(_) | EntrySpelling::Wild)
                    })
                {
                    return Err(Refusal::MapReadValueBinder);
                }
                self.entries(map);
                Ok(())
            }
            (_, EntrySpelling::MapLiteral(map)) => {
                self.entries(map);
                Ok(())
            }
            (Layer::Computation, _) => self.computation(spelling),
            _ => {
                sequence(spelling)
                    .into_iter()
                    .flat_map(|seq| &seq.items)
                    .for_each(|item| self.value(item));
                Ok(())
            }
        }
    }

    /// Inside a leaf's `Cell(..)`: the leaf's own notation, or its value.
    fn leaf(&mut self, notation: Notation, content: &EntrySpelling) -> Result<(), Refusal> {
        match content {
            EntrySpelling::Brackets(seq) => {
                if !matches!(notation, Notation::List | Notation::Cons) {
                    return Err(Refusal::BracketReading);
                }
                seq.items.iter().for_each(|item| self.value(item));
            }
            EntrySpelling::MapLiteral(map) => {
                if notation != Notation::Map {
                    return Err(Refusal::MapNotationAtNonMap);
                }
                self.entries(map);
            }
            other => self.value(other),
        }
        Ok(())
    }

    /// A collection's instances: each item an instance record of the collection's group, or,
    /// in an ordered collection, a value for its front instance.
    fn instances(
        &mut self,
        order: Order,
        below: &[Layer],
        spelling: &EntrySpelling,
    ) -> Result<(), Refusal> {
        let seq = sequence(spelling).expect("an instance mark is a sequence");
        // A List collection's back instance is not matched in place (a stated limitation).
        if order == Order::List && matches!(seq.rest, Some((_, RestPlace::Front))) {
            return Err(Refusal::InstanceListShape);
        }
        for item in &seq.items {
            let item = match item {
                EntrySpelling::Alias(_, pattern) => pattern,
                other => other,
            };
            match (item, below.first()) {
                (
                    EntrySpelling::Record(_) | EntrySpelling::Fragment(_),
                    Some(Layer::Group(group)),
                ) => {
                    self.group(group, item)?;
                }
                // One instance of an ordered collection is its front one.
                _ if order == Order::List => self.value(item),
                // An unordered collection's instance is chosen by a written record.
                _ => return Err(Refusal::InstanceListShape),
            }
        }
        Ok(())
    }

    /// Brackets, `KCell(..)` or `k::k![..]` on a computation.
    fn computation(&mut self, spelling: &EntrySpelling) -> Result<(), Refusal> {
        let seq = sequence(spelling).expect("a computation's mark is a sequence");
        seq.items.iter().for_each(|item| self.value(item));
        if self.form.is_readable() {
            match &seq.rest {
                // A readable rule never drops or captures the continuation.
                Some((EntryRest::Named(_) | EntryRest::Splice(_), _)) => {
                    return Err(Refusal::ContinuationInReadable);
                }
                // The computation is matched from its front (E1).
                Some((_, RestPlace::Front)) => return Err(Refusal::ComputationBackItem),
                _ => {}
            }
        }
        Ok(())
    }

    /// A value at a group's position: a record of the group names its children's entries;
    /// a fragment of the group is a term, which names the children as the record it
    /// abbreviates does; any other value is a term.
    fn group(&mut self, group: &GroupKind, spelling: &EntrySpelling) -> Result<(), Refusal> {
        let record = match spelling {
            EntrySpelling::Record(record) if record.head == group.name => record,
            EntrySpelling::Fragment(record) if record.head == group.name => {
                self.value(spelling);
                return names_every_child(record, group);
            }
            _ => {
                self.value(spelling);
                return Ok(());
            }
        };
        for (name, value) in &record.fields {
            let child = group.child(name).map_or(&[][..], |kind| &kind.layers[..]);
            self.kind(child, value, false)?;
        }
        names_every_child(record, group)
    }

    fn entries(&mut self, map: &EntryMap) {
        for (key, value) in &map.entries {
            self.value(key);
            self.value(value);
        }
    }

    /// A value position: `_` and a fresh readable name take the position's sort.
    fn value(&mut self, spelling: &EntrySpelling) {
        match spelling {
            EntrySpelling::Wild => {}
            EntrySpelling::Binder(name) => {
                self.sorted |= self.form == EntryForm::Cells || (self.bound)(name);
            }
            EntrySpelling::Alias(_, pattern) => self.value(pattern),
            _ => self.sorted = true,
        }
    }
}

/// Steps 1 to 3 for one entry: its form, its kind against `stack`, the cell's own layers,
/// outermost first, then its path (`path`, the layers of the cell's `?` and `*` ancestors,
/// outermost first). An initializer's value of a `*` cell is one instance's template, judged below the
/// instances layer. `bound` tells the names the rule binds outside the entry.
///
/// # Errors
///
/// The refusal of the first step that refuses the entry.
pub fn admit(
    form: EntryForm,
    side: EntrySide,
    path: &[Layer],
    stack: &[Layer],
    spelling: &EntrySpelling,
    bound: &dyn Fn(&str) -> bool,
) -> Result<Admitted, Refusal> {
    let mut admission = Admission {
        form,
        side,
        bound,
        sorted: false,
    };
    admission.form(spelling)?;
    admission.kind(stack, spelling, true)?;
    match path.first() {
        Some(Layer::Optional) => return Err(Refusal::BelowOptionalAncestor),
        Some(_) => return Err(Refusal::BelowCollectionAncestor),
        None => {}
    }
    Ok(Admitted {
        sorted: admission.sorted,
    })
}

/// The rest of an entry's content root, below presence, the leaf wrapper and an alias.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Root<'s> {
    Rest(&'s EntryRest),
    Other,
}

fn root(spelling: &EntrySpelling) -> Root<'_> {
    match spelling {
        EntrySpelling::Present(one) | EntrySpelling::Cell(one) | EntrySpelling::Alias(_, one) => {
            root(one)
        }
        _ => sequence(spelling)
            .and_then(|seq| seq.rest.as_ref().map(|(rest, _)| rest))
            .or_else(|| map_entries(spelling).and_then(|map| map.rest.as_ref()))
            .map_or(Root::Other, Root::Rest),
    }
}

/// Whether `spelling` matches every content `stack` allows: `_`, a name, an alias or `Cell(..)`
/// of one that does, a sequence or map with no item and a rest, or a record of the position's
/// group whose named children all do. Presence, a literal, a call and an item constrain.
fn matches_all(spelling: &EntrySpelling, stack: &[Layer]) -> bool {
    match spelling {
        EntrySpelling::Wild | EntrySpelling::Binder(_) => true,
        EntrySpelling::Alias(_, one) | EntrySpelling::Cell(one) => matches_all(one, stack),
        EntrySpelling::Record(record) | EntrySpelling::Fragment(record) => {
            let Some(Layer::Group(group)) = stack.first() else {
                return false;
            };
            group.name == record.head
                && (record.tail != RecordTail::Exact || record.fields.len() == group.children.len())
                && record.fields.iter().all(|(name, value)| {
                    group
                        .child(name)
                        .is_some_and(|kind| matches_all(value, &kind.layers))
                })
        }
        _ => {
            let open = |rest: Option<&EntryRest>| {
                matches!(rest, Some(EntryRest::Anonymous | EntryRest::Named(_)))
            };
            sequence(spelling).is_some_and(|seq| {
                seq.items.is_empty() && open(seq.rest.as_ref().map(|(rest, _)| rest))
            }) || map_entries(spelling)
                .is_some_and(|map| map.entries.is_empty() && open(map.rest.as_ref()))
        }
    }
}

/// Whether `spelling` binds a name the rule can read; a name starting with `_` reads nothing.
fn binds(spelling: &EntrySpelling) -> bool {
    let reads = |name: &str| !name.starts_with('_');
    match spelling {
        EntrySpelling::Binder(name) => reads(name),
        EntrySpelling::Alias(..) => true,
        _ => {
            let named = sequence(spelling)
                .and_then(|seq| seq.rest.as_ref().map(|(rest, _)| rest))
                .or_else(|| map_entries(spelling).and_then(|map| map.rest.as_ref()));
            matches!(named, Some(EntryRest::Named(name)) if reads(name))
                || inner(spelling).into_iter().any(binds)
        }
    }
}

/// What a result's content is paired with: at the entry's own cell, the subject's entry of the
/// cell, or none where the subject does not match it; at a child of a group or instance record
/// the result writes, the other side of the record's same child.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Other<'s> {
    /// The subject's entry of the same cell.
    Matched(&'s EntrySpelling),
    /// The cell exists and the subject does not match it: the result overwrites it.
    Unmatched,
    /// The result creates the cell, with the instance or the `?` cell that holds it: it had no
    /// content before.
    Created,
}

/// `spelling` below an alias.
fn unaliased(spelling: &EntrySpelling) -> &EntrySpelling {
    match spelling {
        EntrySpelling::Alias(_, pattern) => pattern,
        other => other,
    }
}

/// The record of `group` that `spelling` writes, below an alias: a record, or the group's
/// `k::fragment![..]`, which is the same record in `cells!`.
fn record_of<'s>(spelling: &'s EntrySpelling, group: &GroupKind) -> Option<&'s EntryRecord> {
    match unaliased(spelling) {
        EntrySpelling::Record(record) | EntrySpelling::Fragment(record)
            if record.head == group.name =>
        {
            Some(record)
        }
        _ => None,
    }
}

impl Other<'_> {
    /// The other side of what a result's `Some(..)` holds: what the subject's `Some(..)` holds,
    /// or a cell the result creates where the subject matched `None`.
    fn present(self) -> Self {
        match self {
            Self::Matched(subject) => match unaliased(subject) {
                EntrySpelling::Present(content) => Self::Matched(content),
                EntrySpelling::Missing => Self::Created,
                _ => Self::Unmatched,
            },
            other => other,
        }
    }

    /// The other side of the child `name` of a record of `group` whose other side is `self`:
    /// the subject record's same child; a child the subject's record does not name is unmatched;
    /// a created record's child is created.
    fn child(self, group: &GroupKind, name: &str) -> Self {
        match self {
            Self::Matched(subject) => record_of(subject, group)
                .and_then(|record| record.fields.iter().find(|(field, _)| field == name))
                .map_or(Self::Unmatched, |(_, value)| Self::Matched(value)),
            other => other,
        }
    }

    /// The other side of an instance record a result writes in a collection whose other side is
    /// `self`: an update `..label` changes in place the subject's instance labelled `label`; one
    /// whose label no subject instance has is an instance the subject does not show; any other
    /// instance record creates an instance, whose `..` is its template's.
    fn instance(self, record: &EntryRecord) -> Self {
        let RecordTail::Update(label) = &record.tail else {
            return Self::Created;
        };
        let Self::Matched(subject) = self else {
            return Self::Unmatched;
        };
        sequence(unaliased(subject))
            .and_then(|seq| {
                seq.items.iter().find_map(|item| match item {
                    EntrySpelling::Alias(name, instance) if name == label => {
                        Some(Self::Matched(instance))
                    }
                    _ => None,
                })
            })
            .unwrap_or(Self::Unmatched)
    }
}

/// Whether a result's instance record of `group`, in a collection ordered by `order`, with
/// `other` its other side, keys its instance as its collection does ([`GroupKind::key`]): a Map
/// instance's key is its identity, written at creation and never changed. A created instance
/// writes it, since a bare `..` takes only template fields, which state no identity. An update
/// changes the instance in place, so it writes the key, if at all, as the binder the subject
/// matched the key with, which is the same instance; any other key value, or a key the labelled
/// instance does not name, is a key change.
fn keyed(order: Order, group: &GroupKind, record: &EntryRecord, other: Other<'_>) -> bool {
    fn named<'r>(record: &'r EntryRecord, key: &str) -> Option<&'r EntrySpelling> {
        record
            .fields
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, value)| value)
    }
    let Some(key) = group.key(order) else {
        return true;
    };
    match (&record.tail, named(record, key)) {
        (RecordTail::Update(_), Some(value)) => {
            let Other::Matched(subject) = other else {
                return false;
            };
            matches!(
                (value, record_of(subject, group).and_then(|record| named(record, key))),
                (
                    EntrySpelling::Binder(written),
                    Some(EntrySpelling::Binder(bound) | EntrySpelling::Alias(bound, _)),
                ) if written == bound
            )
        }
        (RecordTail::Update(_), None) => true,
        (RecordTail::Exact | RecordTail::Open, written) => written.is_some(),
    }
}

/// A result's content against its other side, at the entry's cell or at a child's: its rest,
/// then each child of the group and instance records it writes, against the child's own.
fn pair_content(
    form: EntryForm,
    stack: &[Layer],
    spelling: &EntrySpelling,
    other: Other<'_>,
) -> Result<(), Refusal> {
    let anonymous = |root: Root<'_>| root == Root::Rest(&EntryRest::Anonymous);
    match other {
        Other::Unmatched => match stack.first() {
            Some(Layer::Optional) => return Err(Refusal::UnmatchedOptionalResult),
            Some(Layer::Computation) if form.is_readable() => {
                return Err(Refusal::ContinuationInReadable);
            }
            _ if anonymous(root(spelling)) => return Err(Refusal::RestMismatch),
            _ => {}
        },
        Other::Matched(subject) => {
            if *spelling == EntrySpelling::Missing {
                return Ok(());
            }
            if anonymous(root(spelling)) != anonymous(root(subject)) {
                return Err(Refusal::RestMismatch);
            }
        }
        Other::Created => {
            if anonymous(root(spelling)) {
                return Err(Refusal::RestMismatch);
            }
        }
    }
    pair_records(form, stack, spelling, other)
}

/// The group and instance records a result's content writes: a group that exists takes no bare
/// `..`, and each record's children are paired against their own other sides.
fn pair_records(
    form: EntryForm,
    stack: &[Layer],
    spelling: &EntrySpelling,
    other: Other<'_>,
) -> Result<(), Refusal> {
    let fields = |group: &GroupKind, record: &EntryRecord, other: Other<'_>| {
        record.fields.iter().try_for_each(|(name, value)| {
            group.child(name).map_or(Ok(()), |kind| {
                pair_content(form, &kind.layers, value, other.child(group, name))
            })
        })
    };
    match (stack, spelling) {
        ([Layer::Optional, below @ ..], EntrySpelling::Present(content)) => {
            pair_records(form, below, content, other.present())
        }
        ([Layer::Group(group), ..], _) => {
            let Some(record) = record_of(spelling, group) else {
                return Ok(());
            };
            if record.tail == RecordTail::Open && other != Other::Created {
                return Err(Refusal::OpenRecordOutsidePattern);
            }
            fields(group, record, other)
        }
        ([Layer::Instances(order), Layer::Group(group), ..], _) => sequence(spelling)
            .map_or(&[][..], |seq| &seq.items[..])
            .iter()
            .filter_map(|item| record_of(item, group))
            .try_for_each(|record| {
                let other = other.instance(record);
                if !keyed(*order, group, record, other) {
                    return Err(Refusal::MapCollectionKey);
                }
                fields(group, record, other)
            }),
        _ => Ok(()),
    }
}

/// Pairing for an admitted entry with its rule. On a subject, an absence test needs the result
/// to create the cell, and an entry that constrains nothing on a cell the result leaves out
/// (`written` false) owes [`Lint::NoEffectEntry`]. On a result, `other` is the subject's entry
/// of the same cell, `None` where the subject does not match the cell, and the result is
/// paired at every content root it writes: the cell's own, and each child's of the group and
/// instance records it writes, a child being an entry of its own cell. A child's other side is
/// the subject record's same child; in an instance update (`..me`), the same child of the
/// subject instance `me` labels; none where the subject's record does not name the child, and
/// none to keep for a created instance's or `?` cell's child. At each:
///
/// - a group record with a bare `..` for a group that exists (matched or overwritten, the
///   cell's own or one inside a `?` cell the subject matches present) is
///   [`Refusal::OpenRecordOutsidePattern`], since a bare `..` in a result is Rust's default
///   fields, which only a created instance has; the group's fragment is the same record;
/// - over a matched cell, `None` removes the cell with all its content, so it pairs no rest;
///   and its rest is its subject's: a subject's `..` is kept by a result `..` only;
/// - over an unmatched cell, the result is an overwrite, which means one configuration only
///   where the cell's presence is known and no rest is kept: a `?` cell is
///   [`Refusal::UnmatchedOptionalResult`]; a readable computation's continuation, which the
///   subject did not match, is dropped or kept unmatched, [`Refusal::ContinuationInReadable`];
///   and a root `..` keeps a rest the subject never matched, [`Refusal::RestMismatch`];
/// - a created cell had no content, so a root `..` keeps nothing, [`Refusal::RestMismatch`].
///
/// # Errors
///
/// [`Refusal::AbsenceTestWithoutCreation`], [`Refusal::RestMismatch`],
/// [`Refusal::OpenRecordOutsidePattern`], [`Refusal::UnmatchedOptionalResult`] or
/// [`Refusal::ContinuationInReadable`].
pub fn pair(
    form: EntryForm,
    side: EntrySide,
    stack: &[Layer],
    spelling: &EntrySpelling,
    other: Option<&EntrySpelling>,
    written: bool,
) -> Result<Option<Lint>, Refusal> {
    match side {
        EntrySide::Subject if written => Ok(None),
        EntrySide::Subject => {
            if *spelling == EntrySpelling::Missing {
                return Err(Refusal::AbsenceTestWithoutCreation);
            }
            Ok((matches_all(spelling, stack) && !binds(spelling)).then_some(Lint::NoEffectEntry))
        }
        EntrySide::Result => {
            let other = other.map_or(Other::Unmatched, Other::Matched);
            pair_content(form, stack, spelling, other).map(|()| None)
        }
        EntrySide::Initializer => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use krs_ir::cell_kind::{CellKind, GroupKind, Layer, Notation, Order};

    use super::{EntrySide, Lint, Refusal, admit, pair};
    use crate::cell_entry::{EntryForm, EntryReading, EntrySpelling};

    fn read(form: EntryForm, text: &str) -> EntrySpelling {
        EntryReading::new(form, &[])
            .value(text.parse().expect("the entry lexes"))
            .expect("the entry reads")
    }

    fn judge(form: EntryForm, side: EntrySide, stack: &[Layer], text: &str) -> Result<(), Refusal> {
        admit(form, side, &[], stack, &read(form, text), &|_| false).map(|_| ())
    }

    fn below(
        form: EntryForm,
        side: EntrySide,
        path: &[Layer],
        stack: &[Layer],
        text: &str,
    ) -> Result<(), Refusal> {
        admit(form, side, path, stack, &read(form, text), &|_| false).map(|_| ())
    }

    /// An admitted result entry paired with its subject's entry `subject` (`None`: the subject
    /// does not match the cell).
    fn result(
        form: EntryForm,
        stack: &[Layer],
        text: &str,
        subject: Option<&str>,
    ) -> Result<Option<Lint>, Refusal> {
        let spelling = read(form, text);
        admit(form, EntrySide::Result, &[], stack, &spelling, &|_| true)?;
        let subject = subject.map(|text| read(form, text));
        pair(
            form,
            EntrySide::Result,
            stack,
            &spelling,
            subject.as_ref(),
            false,
        )
    }

    fn int() -> CellKind {
        CellKind {
            layers: vec![Layer::Leaf(Notation::Plain)],
        }
    }

    fn frame() -> Layer {
        Layer::Group(GroupKind {
            name: "Frame".to_owned(),
            children: vec![("ret".to_owned(), int()), ("aux".to_owned(), int())],
        })
    }

    #[test]
    fn a_group_record_names_every_child_or_writes_a_rest() {
        let readable = EntryForm::Readable;
        assert_eq!(
            judge(readable, EntrySide::Subject, &[frame()], "Frame { ret: x }"),
            Err(Refusal::RecordMissingChildren)
        );
        assert_eq!(
            judge(
                readable,
                EntrySide::Subject,
                &[frame()],
                "Frame { ret: x, .. }"
            ),
            Ok(())
        );
    }

    #[test]
    fn a_group_fragment_names_every_child_or_writes_a_rest() {
        let cells = EntryForm::Cells;
        let list = [Layer::Instances(Order::List), frame()];
        for side in [EntrySide::Subject, EntrySide::Result] {
            assert_eq!(
                judge(
                    cells,
                    side,
                    &[frame()],
                    "k::fragment![crate::Frame { ret: x }]"
                ),
                Err(Refusal::RecordMissingChildren)
            );
        }
        assert_eq!(
            judge(
                cells,
                EntrySide::Subject,
                &list,
                "[k::fragment![crate::Frame { ret: x }], ..]"
            ),
            Err(Refusal::RecordMissingChildren)
        );
        for text in [
            "k::fragment![crate::Frame { ret: x, .. }]",
            "k::fragment![crate::Frame { ret: x, aux: y }]",
        ] {
            assert_eq!(judge(cells, EntrySide::Subject, &[frame()], text), Ok(()));
        }
    }

    #[test]
    fn an_initializers_collection_child_takes_its_instance_template() {
        let job = CellKind {
            layers: vec![
                Layer::Instances(Order::List),
                Layer::Group(GroupKind {
                    name: "Job".to_owned(),
                    children: vec![("p".to_owned(), int())],
                }),
            ],
        };
        let acct = [
            Layer::Instances(Order::Map),
            Layer::Group(GroupKind {
                name: "Acct".to_owned(),
                children: vec![("id".to_owned(), int()), ("jobs".to_owned(), job)],
            }),
        ];
        let init = EntryForm::Initializer;
        assert_eq!(
            judge(
                init,
                EntrySide::Initializer,
                &acct,
                "Acct { id: 0, jobs: Job { p: 0 } }"
            ),
            Ok(())
        );
        assert_eq!(
            judge(
                init,
                EntrySide::Initializer,
                &acct,
                "Acct { id: 0, jobs: [Job { p: 0 }] }"
            ),
            Err(Refusal::BracketReading)
        );
    }

    #[test]
    fn a_readable_rule_keeps_the_continuation() {
        for text in ["[x, rest @ ..]", "[x, ..rest]"] {
            assert_eq!(
                judge(
                    EntryForm::Readable,
                    EntrySide::Subject,
                    &[Layer::Computation],
                    text
                ),
                Err(Refusal::ContinuationInReadable),
                "{text}"
            );
        }
        assert_eq!(
            judge(
                EntryForm::Cells,
                EntrySide::Subject,
                &[Layer::Computation],
                "k::configuration::KCell(x, rest @ ..)"
            ),
            Ok(())
        );
    }

    #[test]
    fn a_cell_below_a_marked_ancestor_is_refused_for_the_ancestor_whatever_it_spells() {
        let int = [Layer::Leaf(Notation::Plain)];
        let optional = [Layer::Optional];
        let map = [Layer::Instances(Order::Map)];
        let list = [Layer::Instances(Order::List)];
        let (subject, readable, cells) =
            (EntrySide::Subject, EntryForm::Readable, EntryForm::Cells);
        // The review's three probes: an ancestor's mark spelled in the entry admitted it. It is
        // no mark of the cell's own layers, which refuse it first, so the path's advice (the
        // entry inside the ancestor's mark) is never a spelling refused again.
        assert_eq!(
            below(readable, subject, &optional, &int, "Some(x)"),
            Err(Refusal::PresenceOnPlainCell)
        );
        assert_eq!(
            below(readable, subject, &map, &int, "{ .. }"),
            Err(Refusal::InstancesOnPlainCell)
        );
        assert_eq!(
            below(readable, subject, &list, &int, "[x, ..]"),
            Err(Refusal::BracketReading)
        );
        assert_eq!(
            below(cells, subject, &list, &int, "[x, ..]"),
            Err(Refusal::InstancesOnPlainCell)
        );
        // A spelling the cell's own layers admit is refused for its ancestor.
        assert_eq!(
            below(
                readable,
                subject,
                &list,
                &[Layer::Optional, Layer::Leaf(Notation::Plain)],
                "Some(x)"
            ),
            Err(Refusal::BelowCollectionAncestor)
        );
        assert_eq!(
            below(cells, subject, &optional, &int, "k::configuration::Cell(x)"),
            Err(Refusal::BelowOptionalAncestor)
        );
        for (form, x, one) in [
            (readable, "x", "1"),
            (
                cells,
                "k::configuration::Cell(x)",
                "k::configuration::Cell(1)",
            ),
        ] {
            assert_eq!(
                below(form, subject, &map, &int, x),
                Err(Refusal::BelowCollectionAncestor)
            );
            assert_eq!(
                below(form, subject, &optional, &int, x),
                Err(Refusal::BelowOptionalAncestor)
            );
            // The outermost marked ancestor's refusal.
            assert_eq!(
                below(
                    form,
                    EntrySide::Result,
                    &[Layer::Optional, Layer::Instances(Order::List)],
                    &int,
                    one
                ),
                Err(Refusal::BelowOptionalAncestor)
            );
        }
        // A value without the leaf's `cells!` wrapper is the cell's own mistake, first.
        assert_eq!(
            below(cells, subject, &map, &int, "x"),
            Err(Refusal::CellWrapper)
        );
        assert_eq!(
            Refusal::BelowOptionalAncestor.class(),
            "optional-without-presence"
        );
        assert_eq!(
            Refusal::BelowCollectionAncestor.class(),
            "collection-without-instances"
        );
        // The form comes first (P4).
        assert_eq!(
            below(readable, EntrySide::Result, &list, &int, "_"),
            Err(Refusal::WildcardOutsidePattern)
        );
    }

    #[test]
    fn a_result_over_a_cell_the_subject_does_not_match_is_an_overwrite_where_it_means_one_configuration()
     {
        let (readable, cells) = (EntryForm::Readable, EntryForm::Cells);
        let optional = [Layer::Optional, Layer::Leaf(Notation::Plain)];
        let list = [Layer::Leaf(Notation::List)];
        let computation = [Layer::Computation];
        // The review's three probes.
        assert_eq!(
            result(readable, &optional, "Some(1)", None),
            Err(Refusal::UnmatchedOptionalResult)
        );
        assert_eq!(
            result(readable, &list, "[x, ..]", None),
            Err(Refusal::RestMismatch)
        );
        assert_eq!(
            result(readable, &computation, "[x, ..]", None),
            Err(Refusal::ContinuationInReadable)
        );
        // A readable rule drops no continuation it did not match either (Q3); `cells!` may.
        assert_eq!(
            result(readable, &computation, "[x]", None),
            Err(Refusal::ContinuationInReadable)
        );
        assert_eq!(
            result(cells, &computation, "k::configuration::KCell(x)", None),
            Ok(None)
        );
        assert_eq!(
            result(cells, &computation, "k::configuration::KCell(x, ..)", None),
            Err(Refusal::RestMismatch)
        );
        // The overwrite: a plain leaf, an exact list, a group, an exact instance list.
        assert_eq!(
            result(readable, &[Layer::Leaf(Notation::Plain)], "1", None),
            Ok(None)
        );
        assert_eq!(result(readable, &list, "[x]", None), Ok(None));
        assert_eq!(
            result(readable, &[frame()], "Frame { ret: 1, aux: 2 }", None),
            Ok(None)
        );
        assert_eq!(
            result(
                cells,
                &[Layer::Instances(Order::List), frame()],
                "[k::fragment![crate::Frame { ret: 1, aux: 2 }]]",
                None
            ),
            Ok(None)
        );
        assert_eq!(
            result(cells, &optional, "Some(k::configuration::Cell(1))", None),
            Err(Refusal::UnmatchedOptionalResult)
        );
        // Over a matched cell, the rest pairs with the subject's (P6).
        assert_eq!(
            result(readable, &list, "[x, ..]", Some("[y, ..]")),
            Ok(None)
        );
        assert_eq!(
            result(readable, &list, "[x]", Some("[y, ..]")),
            Err(Refusal::RestMismatch)
        );
    }

    #[test]
    fn a_result_none_over_a_matched_optional_cell_removes_it_rest_and_all() {
        let (readable, cells) = (EntryForm::Readable, EntryForm::Cells);
        let list = [Layer::Optional, Layer::Leaf(Notation::List)];
        let map = [Layer::Optional, Layer::Leaf(Notation::Map)];
        assert_eq!(
            result(readable, &list, "None", Some("Some([y, ..])")),
            Ok(None)
        );
        assert_eq!(
            result(readable, &map, "None", Some("Some({ z -> y, .. })")),
            Ok(None)
        );
        assert_eq!(
            result(
                cells,
                &list,
                "None",
                Some("Some(k::configuration::Cell([y, ..]))")
            ),
            Ok(None)
        );
        // A result that writes the content still pairs its rest with the subject's (P6).
        assert_eq!(
            result(readable, &list, "Some([x])", Some("Some([y, ..])")),
            Err(Refusal::RestMismatch)
        );
        // Over an unmatched `?` cell, `None` still does not know the cell's presence.
        assert_eq!(
            result(readable, &list, "None", None),
            Err(Refusal::UnmatchedOptionalResult)
        );
    }

    #[test]
    fn a_named_rest_in_a_result_is_an_alias_outside_a_pattern() {
        let (readable, cells) = (EntryForm::Readable, EntryForm::Cells);
        let refused = Err(Refusal::AliasOutsidePattern);
        for (form, stack, text) in [
            (readable, vec![Layer::Leaf(Notation::List)], "[x, r @ ..]"),
            (readable, vec![Layer::Computation], "[x, r @ ..]"),
            (
                readable,
                vec![Layer::Leaf(Notation::Map)],
                "{ y -> x, r @ .. }",
            ),
            (
                cells,
                vec![Layer::Computation],
                "k::configuration::KCell(x, r @ ..)",
            ),
            (
                cells,
                vec![Layer::Leaf(Notation::List)],
                "k::configuration::Cell([x, r @ ..])",
            ),
            (
                cells,
                vec![Layer::Instances(Order::List), frame()],
                "[k::fragment![crate::Frame { ret: x, .. }], r @ ..]",
            ),
        ] {
            assert_eq!(
                judge(form, EntrySide::Result, &stack, text),
                refused,
                "{text}"
            );
        }
        // Step 1 comes before the path (P4).
        assert_eq!(
            below(
                readable,
                EntrySide::Result,
                &[Layer::Optional],
                &[Layer::Leaf(Notation::List)],
                "[x, r @ ..]"
            ),
            refused
        );
        // A subject names its rest, and a result puts it back with `..r`.
        let list = [Layer::Leaf(Notation::List)];
        assert_eq!(
            judge(readable, EntrySide::Subject, &list, "[x, r @ ..]"),
            Ok(())
        );
        assert_eq!(
            judge(readable, EntrySide::Result, &list, "[x, ..r]"),
            Ok(())
        );
    }

    #[test]
    fn a_result_group_record_with_a_bare_rest_is_refused_over_a_matched_group() {
        let (readable, cells) = (EntryForm::Readable, EntryForm::Cells);
        let refused = Err(Refusal::OpenRecordOutsidePattern);
        let group = [frame()];
        let subject = Some("Frame { ret: y, .. }");
        assert_eq!(
            result(readable, &group, "Frame { ret: x, .. }", subject),
            refused
        );
        assert_eq!(
            result(readable, &group, "Frame { ret: x, aux: 0 }", subject),
            Ok(None)
        );
        // Inside a `?` cell the subject matches present.
        let optional = [Layer::Optional, frame()];
        assert_eq!(
            result(
                readable,
                &optional,
                "Some(Frame { ret: x, .. })",
                Some("Some(Frame { ret: y, .. })")
            ),
            refused
        );
        // A created instance's record has its template's fields.
        let instances = [Layer::Instances(Order::Set), frame()];
        assert_eq!(
            result(
                readable,
                &instances,
                "{ Frame { ret: x, .. }, .. }",
                Some("{ Frame { ret: y, .. }, .. }")
            ),
            Ok(None)
        );
        assert_eq!(
            result(
                cells,
                &[Layer::Instances(Order::List), frame()],
                "[k::fragment![crate::Frame { ret: x, .. }], ..]",
                Some("[k::fragment![crate::Frame { ret: y, .. }], ..]")
            ),
            Ok(None)
        );
        // A subject's record leaves fields unconstrained.
        assert_eq!(
            judge(readable, EntrySide::Subject, &group, "Frame { ret: x, .. }"),
            Ok(())
        );
    }

    #[test]
    fn a_result_group_record_with_a_bare_rest_is_refused_over_an_overwritten_group() {
        let readable = EntryForm::Readable;
        let group = [frame()];
        // Q1's overwrite: the group exists already, so it has no default fields (P6).
        assert_eq!(
            result(readable, &group, "Frame { ret: x, .. }", None),
            Err(Refusal::OpenRecordOutsidePattern)
        );
        assert_eq!(
            result(readable, &group, "Frame { ret: x, aux: 0 }", None),
            Ok(None)
        );
        // A `?` cell the subject does not match is refused for its presence first.
        assert_eq!(
            result(
                readable,
                &[Layer::Optional, frame()],
                "Some(Frame { ret: x, .. })",
                None
            ),
            Err(Refusal::UnmatchedOptionalResult)
        );
        // A created `?` cell, over a subject `None`, takes its template's fields.
        assert_eq!(
            result(
                readable,
                &[Layer::Optional, frame()],
                "Some(Frame { ret: x, .. })",
                Some("None")
            ),
            Ok(None)
        );
        // A created instance's record does too.
        assert_eq!(
            result(
                readable,
                &[Layer::Instances(Order::Set), frame()],
                "{ Frame { ret: x, .. } }",
                None
            ),
            Ok(None)
        );
    }

    #[test]
    fn a_result_group_fragment_with_a_bare_rest_is_refused_over_an_existing_group() {
        let cells = EntryForm::Cells;
        let refused = Err(Refusal::OpenRecordOutsidePattern);
        let group = [frame()];
        let optional = [Layer::Optional, frame()];
        let open = "k::fragment![crate::Frame { ret: x, .. }]";
        // The fragment is the group's record (D-3): matched or overwritten, the group exists.
        assert_eq!(
            result(
                cells,
                &group,
                open,
                Some("k::fragment![crate::Frame { ret: y, .. }]")
            ),
            refused
        );
        assert_eq!(result(cells, &group, open, None), refused);
        assert_eq!(
            result(
                cells,
                &optional,
                "Some(k::fragment![crate::Frame { ret: x, .. }])",
                Some("Some(k::fragment![crate::Frame { ret: y, .. }])")
            ),
            refused
        );
        assert_eq!(
            result(
                cells,
                &group,
                "k::fragment![crate::Frame { ret: x, aux: 0 }]",
                None
            ),
            Ok(None)
        );
        // A `?` cell created over a subject `None`, and a created instance, take the template's.
        assert_eq!(
            result(
                cells,
                &optional,
                "Some(k::fragment![crate::Frame { ret: x, .. }])",
                Some("None")
            ),
            Ok(None)
        );
        assert_eq!(
            result(
                cells,
                &[Layer::Instances(Order::List), frame()],
                "[k::fragment![crate::Frame { ret: x, .. }], ..]",
                Some("[k::fragment![crate::Frame { ret: y, .. }], ..]")
            ),
            Ok(None)
        );
    }

    #[test]
    fn a_result_records_children_pair_their_rests_at_their_own_content_roots() {
        let (readable, cells) = (EntryForm::Readable, EntryForm::Cells);
        let rm = Err(Refusal::RestMismatch);
        let list = CellKind {
            layers: vec![Layer::Leaf(Notation::List)],
        };
        let computation = CellKind {
            layers: vec![Layer::Computation],
        };
        let threads = [
            Layer::Instances(Order::List),
            Layer::Group(GroupKind {
                name: "T".to_owned(),
                children: vec![("k".to_owned(), computation), ("n".to_owned(), int())],
            }),
        ];
        let h = Layer::Group(GroupKind {
            name: "H".to_owned(),
            children: vec![("l".to_owned(), list), ("b".to_owned(), int())],
        });
        let group = [h.clone()];
        // An update's child pairs with the same child of the instance it labels.
        let me = Some("[me @ T { k: [y, ..], .. }, ..]");
        assert_eq!(
            result(readable, &threads, "[T { k: [x], ..me }, ..]", me),
            rm
        );
        assert_eq!(
            result(readable, &threads, "[T { k: [x, ..], ..me }, ..]", me),
            Ok(None)
        );
        // A created instance's child had no content.
        let any = Some("[..]");
        assert_eq!(
            result(readable, &threads, "[T { k: [x, ..], n: 1 }, ..]", any),
            rm
        );
        assert_eq!(
            result(readable, &threads, "[T { k: [x], n: 1 }, ..]", any),
            Ok(None)
        );
        // A matched group's child pairs with the subject record's same child.
        let subject = Some("H { l: [y, ..], .. }");
        assert_eq!(result(readable, &group, "H { l: [x], b: 1 }", subject), rm);
        assert_eq!(
            result(readable, &group, "H { l: [x, ..], b: 1 }", subject),
            Ok(None)
        );
        // A child the subject does not name is overwritten, as an unmatched cell is.
        assert_eq!(result(readable, &group, "H { l: [x, ..], b: 1 }", None), rm);
        assert_eq!(
            result(
                readable,
                &group,
                "H { l: [x], b: 1 }",
                Some("H { b: y, .. }")
            ),
            Ok(None)
        );
        assert_eq!(
            result(
                readable,
                &threads,
                "[T { k: [x], ..me }, ..]",
                Some("[me @ T { n: y, .. }, ..]")
            ),
            Err(Refusal::ContinuationInReadable)
        );
        // A `?` cell created over a subject `None` creates its group's children.
        assert_eq!(
            result(
                readable,
                &[Layer::Optional, h],
                "Some(H { l: [x, ..], b: 1 })",
                Some("None")
            ),
            rm
        );
        // The fragment is the record in `cells!`.
        assert_eq!(
            result(
                cells,
                &threads,
                "[k::fragment![crate::T { k: [x], ..me }], ..]",
                Some("[me @ k::fragment![crate::T { k: [y, ..], .. }], ..]")
            ),
            rm
        );
    }

    #[test]
    fn an_overwritten_records_children_are_unmatched_not_created() {
        let (readable, cells) = (EntryForm::Readable, EntryForm::Cells);
        let group = |name: &str, children: Vec<(&str, Vec<Layer>)>| {
            [Layer::Group(GroupKind {
                name: name.to_owned(),
                children: children
                    .into_iter()
                    .map(|(child, layers)| (child.to_owned(), CellKind { layers }))
                    .collect(),
            })]
        };
        let plain = || vec![Layer::Leaf(Notation::Plain)];
        let c = group("C", vec![("c", vec![Layer::Computation]), ("n", plain())]);
        let o = group(
            "O",
            vec![
                ("o", vec![Layer::Optional, Layer::Leaf(Notation::Plain)]),
                ("n", plain()),
            ],
        );
        let g = Layer::Group(GroupKind {
            name: "G".to_owned(),
            children: vec![("a".to_owned(), int()), ("b".to_owned(), int())],
        });
        let w = group("W", vec![("g", vec![g]), ("n", plain())]);
        let threads = [
            Layer::Instances(Order::List),
            Layer::Group(GroupKind {
                name: "T".to_owned(),
                children: vec![
                    (
                        "k".to_owned(),
                        CellKind {
                            layers: vec![Layer::Computation],
                        },
                    ),
                    ("n".to_owned(), int()),
                ],
            }),
        ];
        let uor = Err(Refusal::UnmatchedOptionalResult);
        let open = Err(Refusal::OpenRecordOutsidePattern);
        // An overwritten group's computation child: a readable rule does not drop the
        // continuation it never matched.
        assert_eq!(
            result(readable, &c, "C { c: [x], n: 0 }", None),
            Err(Refusal::ContinuationInReadable)
        );
        // Its `?` child, whose presence the rule does not know.
        assert_eq!(result(readable, &o, "O { o: Some(1), n: 0 }", None), uor);
        assert_eq!(result(readable, &o, "O { o: None, n: 0 }", None), uor);
        assert_eq!(
            result(
                cells,
                &o,
                "k::fragment![crate::O { o: Some(1), n: 0 }]",
                None
            ),
            uor
        );
        // Its group child exists, so a bare `..` on it is Rust's default fields.
        assert_eq!(
            result(readable, &w, "W { g: G { a: x, .. }, n: 0 }", None),
            open
        );
        assert_eq!(
            result(
                cells,
                &w,
                "k::fragment![crate::W { g: G { a: x, .. }, n: 0 }]",
                None
            ),
            open
        );
        assert_eq!(
            result(
                readable,
                &w,
                "W { g: G { a: x, .. }, n: 0 }",
                Some("W { n: y, .. }")
            ),
            open
        );
        assert_eq!(
            result(readable, &w, "W { g: G { a: x, b: y }, n: 0 }", None),
            Ok(None)
        );
        // An update whose label no subject instance has: its children are unmatched too.
        assert_eq!(
            result(
                readable,
                &threads,
                "[T { k: [x, ..], ..me }, ..]",
                Some("[..]")
            ),
            Err(Refusal::ContinuationInReadable)
        );
    }

    #[test]
    fn an_update_of_a_map_collections_instance_keeps_its_key() {
        let (readable, cells) = (EntryForm::Readable, EntryForm::Cells);
        let account = |order| {
            [
                Layer::Instances(order),
                Layer::Group(GroupKind {
                    name: "A".to_owned(),
                    children: vec![("id".to_owned(), int()), ("bal".to_owned(), int())],
                }),
            ]
        };
        let map = account(Order::Map);
        let refused = Err(Refusal::MapCollectionKey);
        let me = Some("{ me @ A { id: z, .. }, .. }");
        assert_eq!(
            result(readable, &map, "{ A { id: 5, ..me }, .. }", me),
            refused
        );
        // Written back as the binder the subject matched it with, the key is unchanged; another
        // name or a computed value is another key.
        assert_eq!(
            result(readable, &map, "{ A { id: z, ..me }, .. }", me),
            Ok(None)
        );
        assert_eq!(
            result(readable, &map, "{ A { id: y, ..me }, .. }", me),
            refused
        );
        assert_eq!(
            result(readable, &map, "{ A { id: int::add(z, 1), ..me }, .. }", me),
            refused
        );
        // Another instance's key binder is not this instance's.
        assert_eq!(
            result(
                readable,
                &map,
                "{ A { id: z, ..me }, .. }",
                Some("{ me @ A { id: y, .. }, other @ A { id: z, .. }, .. }")
            ),
            refused
        );
        // Unnamed in the pattern, it is still the key.
        assert_eq!(
            result(
                readable,
                &map,
                "{ A { id: 5, ..me }, .. }",
                Some("{ me @ A { bal: y, .. }, .. }")
            ),
            refused
        );
        assert_eq!(
            result(
                cells,
                &map,
                "{ k::fragment![crate::A { id: 5, ..me }], .. }",
                Some("{ me @ k::fragment![crate::A { id: z, .. }], .. }")
            ),
            refused
        );
        assert_eq!(Refusal::MapCollectionKey.class(), "map-collection-key");
        // An unnamed child other than the key is overwritten, and a created instance states
        // its key.
        assert_eq!(
            result(readable, &map, "{ A { bal: 5, ..me }, .. }", me),
            Ok(None)
        );
        assert_eq!(
            result(
                readable,
                &map,
                "{ A { id: 5, bal: 0 }, .. }",
                Some("{ .. }")
            ),
            Ok(None)
        );
        // A Set collection's instance has no key child.
        assert_eq!(
            result(
                readable,
                &account(Order::Set),
                "{ A { id: 5, ..me }, .. }",
                me
            ),
            Ok(None)
        );
        // A subject's record is no update.
        assert_eq!(
            judge(
                readable,
                EntrySide::Subject,
                &map,
                "{ me @ A { id: z, .. }, .. }"
            ),
            Ok(())
        );
    }

    #[test]
    fn a_created_map_collection_instance_writes_its_key() {
        let (readable, cells) = (EntryForm::Readable, EntryForm::Cells);
        let account = |order| {
            [
                Layer::Instances(order),
                Layer::Group(GroupKind {
                    name: "A".to_owned(),
                    children: vec![("id".to_owned(), int()), ("bal".to_owned(), int())],
                }),
            ]
        };
        let map = account(Order::Map);
        let any = Some("{ .. }");
        let refused = Err(Refusal::MapCollectionKey);
        // A bare `..` takes the template's fields, which state no identity.
        assert_eq!(
            result(readable, &map, "{ A { bal: 0, .. }, .. }", any),
            refused
        );
        assert_eq!(
            result(
                cells,
                &map,
                "{ k::fragment![crate::A { bal: 0, .. }], .. }",
                any
            ),
            refused
        );
        // Over a cell the subject does not match, an exact instance set creates its instances.
        assert_eq!(
            result(readable, &map, "{ A { bal: 0, .. } }", None),
            refused
        );
        assert_eq!(
            result(readable, &map, "{ A { id: 5, .. }, .. }", any),
            Ok(None)
        );
        assert_eq!(
            result(readable, &map, "{ A { id: 5, bal: 0 }, .. }", any),
            Ok(None)
        );
        // A Set or List collection has no key.
        assert_eq!(
            result(
                readable,
                &account(Order::Set),
                "{ A { bal: 0, .. }, .. }",
                any
            ),
            Ok(None)
        );
        assert_eq!(
            result(
                readable,
                &account(Order::List),
                "[A { bal: 0, .. }, ..]",
                Some("[..]")
            ),
            Ok(None)
        );
        // An update that leaves the key out keeps it.
        assert_eq!(
            result(
                readable,
                &map,
                "{ A { bal: 0, ..me }, .. }",
                Some("{ me @ A { id: z, .. }, .. }")
            ),
            Ok(None)
        );
    }

    #[test]
    fn an_alias_in_a_result_is_refused_at_the_form_at_any_depth() {
        let (readable, cells) = (EntryForm::Readable, EntryForm::Cells);
        let refused = Err(Refusal::AliasOutsidePattern);
        let int = [Layer::Leaf(Notation::Plain)];
        for (form, stack, text) in [
            (readable, vec![Layer::Leaf(Notation::Plain)], "x @ 1"),
            (readable, vec![Layer::Leaf(Notation::List)], "[x @ 1, ..]"),
            (
                readable,
                vec![Layer::Optional, Layer::Leaf(Notation::Plain)],
                "Some(x @ 1)",
            ),
            (readable, vec![frame()], "Frame { ret: x @ 1, aux: 0 }"),
            (
                cells,
                vec![Layer::Leaf(Notation::Plain)],
                "k::configuration::Cell(x @ 1)",
            ),
            (
                cells,
                vec![Layer::Instances(Order::List), frame()],
                "[f @ k::fragment![crate::Frame { ret: x, aux: 0 }], ..]",
            ),
        ] {
            assert_eq!(
                judge(form, EntrySide::Result, &stack, text),
                refused,
                "{text}"
            );
        }
        // Step 1 comes before the path (P4).
        assert_eq!(
            below(
                readable,
                EntrySide::Result,
                &[Layer::Optional],
                &int,
                "x @ 1"
            ),
            refused
        );
        // A subject names what it matches.
        assert_eq!(judge(readable, EntrySide::Subject, &int, "x @ 1"), Ok(()));
    }

    #[test]
    fn an_alias_or_a_named_rest_in_an_initializer_is_refused_at_the_form() {
        let init = EntryForm::Initializer;
        let side = EntrySide::Initializer;
        let refused = Err(Refusal::AliasOutsidePattern);
        let variables = ["pgm".to_owned()];
        let reading = EntryReading::new(init, &variables);
        let admitted = |stack: &[Layer], text: &str| {
            let spelling = reading.value(text.parse().expect("lexes")).expect("reads");
            admit(init, side, &[], stack, &spelling, &|_| false).map(|_| ())
        };
        let list = [Layer::Leaf(Notation::List)];
        assert_eq!(admitted(&list, "[0, r @ ..]"), refused);
        assert_eq!(
            admitted(&[Layer::Computation], "k::k![Cmd::Go(), r @ ..]"),
            refused
        );
        assert_eq!(
            admitted(&[Layer::Leaf(Notation::Map)], "k::map![0 -> 1, r @ ..]"),
            refused
        );
        assert_eq!(admitted(&[Layer::Leaf(Notation::Plain)], "x @ 0"), refused);
        // `..base` is an initializer's update (P5).
        assert_eq!(admitted(&list, "[0, ..base]"), Ok(()));
    }

    #[test]
    fn an_initializer_refuses_an_anonymous_rest_and_a_spliced_computation_only() {
        let init = EntryForm::Initializer;
        let side = EntrySide::Initializer;
        let list = [Layer::Leaf(Notation::List)];
        assert_eq!(
            judge(init, side, &list, "[0, ..]"),
            Err(Refusal::InitializerRemainder)
        );
        // A named base is an update (P5), as `k::map![.., ..env]` is.
        assert_eq!(judge(init, side, &list, "[0, ..base]"), Ok(()));
        let variables = ["pgm".to_owned()];
        let reading = EntryReading::new(init, &variables);
        let spliced = reading
            .value("k::k![Cmd::Go(), ..pgm]".parse().expect("lexes"))
            .expect("reads");
        assert_eq!(
            admit(init, side, &[], &[Layer::Computation], &spliced, &|_| false).map(|_| ()),
            Err(Refusal::InitializerRemainder)
        );
        let open = reading
            .value("k::k![Cmd::Go(), ..]".parse().expect("lexes"))
            .expect("reads");
        assert_eq!(
            admit(init, side, &[], &[Layer::Computation], &open, &|_| false).map(|_| ()),
            Err(Refusal::InitializerRemainder)
        );
    }

    #[test]
    fn a_map_read_is_refused_in_a_result_at_the_records_top_level_only() {
        let readable = EntryForm::Readable;
        let map = [Layer::Leaf(Notation::Map)];
        assert_eq!(
            judge(readable, EntrySide::Result, &map, "{ y -> x, .. }"),
            Err(Refusal::MapReadInResult)
        );
        let obj = Layer::Group(GroupKind {
            name: "Obj".to_owned(),
            children: vec![
                ("key".to_owned(), int()),
                (
                    "m".to_owned(),
                    CellKind {
                        layers: vec![Layer::Leaf(Notation::Map)],
                    },
                ),
            ],
        });
        assert_eq!(
            judge(
                readable,
                EntrySide::Result,
                &[Layer::Instances(Order::Set), obj],
                "{ Obj { key: 1, m: { 1 -> 2, .. } }, .. }"
            ),
            Ok(())
        );
    }

    #[test]
    fn a_subject_entry_that_constrains_nothing_owes_the_lint() {
        let stack = [frame()];
        let lint = |text: &str, written: bool| {
            pair(
                EntryForm::Readable,
                EntrySide::Subject,
                &stack,
                &read(EntryForm::Readable, text),
                None,
                written,
            )
        };
        assert_eq!(lint("Frame { .. }", false), Ok(Some(Lint::NoEffectEntry)));
        assert_eq!(lint("_", false), Ok(Some(Lint::NoEffectEntry)));
        assert_eq!(lint("_", true), Ok(None));
        assert_eq!(lint("f", false), Ok(None));
        assert_eq!(lint("Frame { ret: 0, .. }", false), Ok(None));
    }

    #[test]
    fn the_shape_rules_refuse_at_reading() {
        let reading = EntryReading::new(EntryForm::Readable, &[]);
        for text in [
            "[x, .., ..]",
            "Some(x, y)",
            "{ x -> a, x -> b, .. }",
            "{ 1 -> a, 1 -> b }",
        ] {
            assert!(
                reading.value(text.parse().expect("lexes")).is_err(),
                "{text} breaks a shape rule"
            );
        }
    }
}

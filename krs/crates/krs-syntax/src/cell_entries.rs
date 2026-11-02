//! Cell-entry admission (design S5, §2.3): one judgement of what an entry means, in every form.
//!
//! [`admit`] judges one entry's [`EntrySpelling`] against its cell's stack
//! ([`krs_ir::cell_kind::CellKind`], the ancestors' layers then the cell's own):
//!
//! 1. **form**: what the spelling and its side alone refuse: `_` outside a pattern, `None` or a
//!    rest in an initializer's value, an anonymous rest in a map literal outside a `cells!`
//!    pattern;
//! 2. **kind**, outermost layer first: the outermost layer's mark admits the entry and its
//!    inside is judged against the next layer; a mark no layer of the stack has gives that
//!    mark's refusal; a deeper layer's mark, or a value where the outermost layer has a mark,
//!    gives the missing layer's refusal.
//!
//! [`pair`] then judges the entry with its rule: a result's rest against its subject's, an
//! absence test, and the lint of a subject entry that constrains nothing.
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
//! initializer's `k::k![..]` holds no rest, and a readable map read has no result side and reads
//! its value as a fresh binder.

use krs_ir::cell_kind::{GroupKind, Layer, Notation, Order};

use crate::cell_entry::{
    EntryForm, EntryMap, EntryRest, EntrySeq, EntrySpelling, RecordTail, RestPlace,
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
    /// A group record at a configuration position that names neither every child nor `..`.
    RecordMissingChildren,
    /// A readable rule that drops or captures the continuation.
    ContinuationInReadable,
    /// `None` in a subject whose result does not create the cell.
    AbsenceTestWithoutCreation,
    /// A result rest that is not its subject's.
    RestMismatch,
    /// A readable computation's rest before an item: the computation is matched from its
    /// front (the class matrix's E1).
    ComputationBackItem,
    /// A readable map read in a result, which has no result side yet: the result is the frame
    /// write `Cell(k::map![k -> v, ..])` (a stated limitation).
    MapReadInResult,
    /// A readable map read at the entry's head whose value is not a fresh binder (a stated
    /// limitation).
    MapReadValueBinder,
}

impl Refusal {
    /// The class matrix's name of the refusal.
    #[must_use]
    pub const fn class(self) -> &'static str {
        match self {
            Self::WildcardOutsidePattern => "wildcard-outside-pattern",
            Self::NoneInInitializer => "none-in-initializer",
            Self::InitializerRemainder => "initializer-remainder",
            Self::AnonymousRestInMapLiteral => "anonymous-rest-in-map-literal",
            Self::PresenceOnPlainCell => "presence-on-plain-cell",
            Self::BracketReading => "bracket-reading",
            Self::InstancesOnPlainCell => "instances-on-plain-cell",
            Self::InstanceListShape => "instance-list-shape",
            Self::MapNotationAtNonMap => "map-notation-at-non-map",
            Self::CellWrapper => "cell-wrapper",
            Self::OptionalWithoutPresence => "optional-without-presence",
            Self::CollectionWithoutInstances => "collection-without-instances",
            Self::RecordMissingChildren => "record-missing-children",
            Self::ContinuationInReadable => "continuation-in-readable",
            Self::AbsenceTestWithoutCreation => "absence-test-without-creation",
            Self::RestMismatch => "rest-mismatch",
            Self::ComputationBackItem => "computation-back-item",
            Self::MapReadInResult => "map-read-in-result",
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
            // An initializer's value is the whole initial content: it has no rest, and its
            // computation does not splice a configuration variable's (E3).
            EntrySpelling::KMacro(seq) | EntrySpelling::Brackets(seq)
                if initializer && seq.rest.is_some() =>
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
                if self.form.is_readable() && self.side == EntrySide::Result {
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
    /// any other value, a fragment included, is a term.
    fn group(&mut self, group: &GroupKind, spelling: &EntrySpelling) -> Result<(), Refusal> {
        let EntrySpelling::Record(record) = spelling else {
            self.value(spelling);
            return Ok(());
        };
        if record.head != group.name {
            self.value(spelling);
            return Ok(());
        }
        for (name, value) in &record.fields {
            let child = group.child(name).map_or(&[][..], |kind| &kind.layers[..]);
            self.kind(child, value, false)?;
        }
        // A group record at a configuration position names every child, or writes `..`.
        if record.tail == RecordTail::Exact && record.fields.len() != group.children.len() {
            return Err(Refusal::RecordMissingChildren);
        }
        Ok(())
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

/// Steps 1 and 2 for one entry: its form, then its kind against `stack` (the ancestors' layers
/// then the cell's own, outermost first). An initializer's value of a `*` cell is one
/// instance's template, judged below the instances layer. `bound` tells the names the rule binds
/// outside the entry.
///
/// # Errors
///
/// The refusal of the first step that refuses the entry.
pub fn admit(
    form: EntryForm,
    side: EntrySide,
    stack: &[Layer],
    spelling: &EntrySpelling,
    bound: &dyn Fn(&str) -> bool,
) -> Result<Admitted, Refusal> {
    let stack = match stack.split_first() {
        Some((Layer::Instances(_), template)) if side == EntrySide::Initializer => template,
        _ => stack,
    };
    let mut admission = Admission {
        form,
        side,
        bound,
        sorted: false,
    };
    admission.form(spelling)?;
    admission.kind(stack, spelling, true)?;
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

/// Step 3 for an admitted entry: on a subject, an absence test needs the result to create the
/// cell, and an entry that constrains nothing on a cell the result leaves out owes
/// [`Lint::NoEffectEntry`]; on a result, its rest is its subject's (`other`): a subject's `..`
/// is kept by a result `..` only.
///
/// # Errors
///
/// [`Refusal::AbsenceTestWithoutCreation`] or [`Refusal::RestMismatch`].
pub fn pair(
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
            let Some(subject) = other else {
                return Ok(None);
            };
            let anonymous = |root: Root<'_>| root == Root::Rest(&EntryRest::Anonymous);
            if anonymous(root(spelling)) != anonymous(root(subject)) {
                return Err(Refusal::RestMismatch);
            }
            Ok(None)
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
        admit(form, side, stack, &read(form, text), &|_| false).map(|_| ())
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
    fn a_cell_below_a_marked_ancestor_meets_the_ancestors_layer_first() {
        let below_collection = [Layer::Instances(Order::Map), Layer::Leaf(Notation::Plain)];
        let below_optional = [Layer::Optional, Layer::Leaf(Notation::Plain)];
        for form in [EntryForm::Readable, EntryForm::Cells] {
            assert_eq!(
                judge(form, EntrySide::Subject, &below_collection, "x"),
                Err(Refusal::CollectionWithoutInstances)
            );
            assert_eq!(
                judge(form, EntrySide::Subject, &below_optional, "x"),
                Err(Refusal::OptionalWithoutPresence)
            );
        }
    }

    #[test]
    fn a_subject_entry_that_constrains_nothing_owes_the_lint() {
        let stack = [frame()];
        let lint = |text: &str, written: bool| {
            pair(
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

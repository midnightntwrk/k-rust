//! Cell-entry admission (design S5, §2.3): one judgement of what an entry means, in every form.
//!
//! [`admit`] judges one entry's [`EntrySpelling`] against what its cell's declaration gives it
//! ([`krs_ir::cell_kind::EntryKind`]: the layers of the cell's marked ancestors, its path, and
//! the cell's own layers, kept apart):
//!
//! 1. **form**: what the spelling and its side alone refuse: `_`, `name @ P` and a named rest
//!    `name @ ..` outside a pattern, `None` or an anonymous rest in an initializer's value, an
//!    anonymous rest in a map literal outside a `cells!` pattern (a `cells!` result's map at a
//!    content root included, `Cell(k::map![.., ..])` or a record field's `k::map![.., ..]` at a
//!    configuration position: the stated M3 limitation);
//! 2. **kind**, against the cell's own layers, outermost first: the outermost layer's mark admits
//!    the entry and its inside is judged against the next layer; a mark no layer of the stack
//!    has gives that mark's refusal (brackets on a Set or Map collection are its instances of the
//!    wrong order; an item after a cons list's rest builds no term); a deeper layer's mark, or a
//!    value where the outermost layer has a mark, gives the missing layer's refusal where the
//!    entry's inside passes against the layers the advice puts it in, and the inside's own
//!    refusal otherwise;
//! 3. **path**: an entry naming a cell below a `?` or `*` ancestor is refused for the outermost
//!    such ancestor, whatever it spells: the ancestor's presence and the instance it means are
//!    written at the ancestor's level (S1 (b)). It comes after the kind, since its advice writes
//!    the entry inside the ancestor's mark, where a spelling the cell's own layers refuse would
//!    be refused again.
//!
//! [`pair`] then judges the entry with its rule: a result's rest against its subject's, at its
//! cell's content root and at each child's of the group and instance records it writes (an
//! update whose label no subject instance has creating its instance from a record of its own
//! constructor bound elsewhere, or having no base), a Map
//! collection's instance key ([`GroupKind::key`]), which a created instance writes and an
//! update keeps, a
//! result's group record with a bare `..` for a group that exists, a result over a cell the
//! subject does not match (Q1's overwrite, where it means one configuration), an absence test
//! at the entry's root and at each `?` child of the records it writes, a List collection's ends
//! (below), and the lint of a subject entry that constrains nothing.
//!
//! [`Sentence::judge`] runs the steps over a whole sentence, each over every entry before the
//! next (the form, then the kind with the path, then the pairing): a later step's question is
//! not well posed while an earlier one is open anywhere in the sentence.
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
//! A computation is read from its front in every form (E1), so `..` ends it.
//!
//! Where the class matrix states a departure from these principles (`[cell-exception]`), the
//! departure is written here as the table states it, with its reason: a List collection's rule
//! changes instances at one end only and keeps no back instance in place (the product creates or
//! removes instances at the back, and reads and updates them at the front: `list_ends`), an
//! initializer's `k::k![..]` splices no configuration variable's computation (`..pgm`), and a
//! readable record's top-level map read has no result side and reads its value as a fresh
//! binder.

use krs_ir::cell_kind::{CellKind, GroupKind, Layer, Notation, Order};

pub use krs_ir::cell_kind::EntryKind;

use crate::cell_entry::{
    EntryForm, EntryMap, EntryRecord, EntryRest, EntrySeq, EntrySpelling, RecordTail,
};

/// What a name the rule binds outside an entry stands for: an update `..base` takes the fields
/// of a record of its own constructor, so whether the name binds a record, and of which
/// constructor, decides whether it can be a base.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Bound {
    /// A record whose head constructor is this struct path's last segment: an alias
    /// `name @ Head { .. }` (or of its fragment).
    Record(String),
    /// Any other value: a list element, a leaf value, a map value.
    Value,
}

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
    /// A rule whose subject and result together change a List collection's instances at both
    /// ends, before its rest and after it (a stated limitation: a rule changes one end).
    ListBothEnds,
    /// A List collection's back instance kept in place: read and kept (the result leaves the
    /// cell out) or updated through its label (a stated limitation: the back is created or
    /// removed, and read and updated at the front).
    ListBackKept,
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
    /// A result's record whose bare `..` leaves a child unnamed, of a group that exists (matched
    /// or overwritten) or in a built term: a bare `..` in a result is Rust's default fields,
    /// which only a created instance has (its template). A `..` after every child defaults
    /// none, and the record is the exact one.
    OpenRecordOutsidePattern,
    /// A computation's rest before an item, in any form (`[.., x]`, `KCell(x, .., y)`): the
    /// computation is read from its front, where the next step is (the class matrix's E1).
    ComputationBackItem,
    /// An item after a cons list's rest (`[.., x]`, `[x, .., y]`, `[..rest, x]`): a cons list is
    /// a constructor term built from its front, so its back is no constructor pattern and, with
    /// no append declared, builds no term.
    ConsListBackItem,
    /// An instance update (`T { .., ..me }`) whose label names no instance the subject matches
    /// and no value the sentence binds: the update has no base.
    RecordUpdateBase,
    /// A `cells!` result's record update that is no in-place update of an instance its subject
    /// labels: a group record's `..base`, or an instance update `..me` whose label names no
    /// subject instance of the cell, so its base is a record matched elsewhere. `cells!` is the
    /// reference notation, which names every field: the one update it has rewrites in place the
    /// instance its subject labels.
    RecordRemainderInCellsTerm,
    /// A readable map read at a result entry's head, which has no result side yet: the result
    /// is the frame write `Cell(k::map![k -> v, ..])` (a stated limitation of the readable
    /// record's top-level route).
    MapReadInResult,
    /// A Map collection's instance that does not keep its key, its first child, which is its
    /// identity: a created instance that does not write it (a bare `..` takes the template's
    /// fields, which state no identity), or an instance update (`..me`) that writes it as
    /// anything but what is provably the key the subject matched (another literal, another
    /// name, a computed value, or a key the labelled instance does not name), since an update
    /// changes the instance in place and another key is another entry of the map. Written as
    /// the subject's own key binder, or as the same literal it matched, the key is unchanged.
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
            Self::InstanceListShape | Self::ListBothEnds | Self::ListBackKept => {
                "instance-list-shape"
            }
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
            Self::ConsListBackItem => "cons-list-back-item",
            Self::RecordUpdateBase => "record-update-base",
            Self::RecordRemainderInCellsTerm => "record-remainder-in-cells-term",
            Self::MapReadInResult => "map-read-in-result",
            Self::MapCollectionKey => "map-collection-key",
            Self::MapReadValueBinder => "map-read-value-binder",
        }
    }
}

impl Refusal {
    /// Whether the refusal is the form step's ([`admit_form`]): what the spelling and its side
    /// alone refuse, judged without the cell's declaration. Whether a record the entry writes
    /// is a group's, and so whether its fields are cells, is the declaration's, so a form
    /// refusal is about the entry's own cell, at the construct it refuses.
    #[must_use]
    pub const fn is_form(self) -> bool {
        matches!(
            self,
            Self::WildcardOutsidePattern
                | Self::AliasOutsidePattern
                | Self::NoneInInitializer
                | Self::InitializerRemainder
                | Self::AnonymousRestInMapLiteral
        )
    }
}

impl Refusal {
    /// The diagnostic code an author meets for the refusal: its class's code.
    #[must_use]
    pub const fn code(self) -> krs_diagnostic::Code {
        use krs_diagnostic::codes::{analysis, collect, syntax};
        match self {
            Self::WildcardOutsidePattern => syntax::UNSUPPORTED_TERM_EXPRESSION,
            Self::AliasOutsidePattern => syntax::INVALID_PATTERN_AS,
            Self::NoneInInitializer | Self::InitializerRemainder => {
                syntax::UNSUPPORTED_INITIALIZER_BODY
            }
            Self::AnonymousRestInMapLiteral => syntax::INVALID_EXPRESSION_NOTATION,
            Self::PresenceOnPlainCell
            | Self::OptionalWithoutPresence
            | Self::BelowOptionalAncestor
            | Self::UnmatchedOptionalResult
            | Self::AbsenceTestWithoutCreation => analysis::OPTIONAL_PRESENCE,
            Self::BracketReading | Self::ConsListBackItem => analysis::INVALID_LIST_NOTATION,
            Self::InstancesOnPlainCell
            | Self::InstanceListShape
            | Self::ListBothEnds
            | Self::ListBackKept
            | Self::CollectionWithoutInstances
            | Self::BelowCollectionAncestor => analysis::COLLECTION_ENTRY,
            Self::MapNotationAtNonMap => analysis::INVALID_TERM,
            Self::CellWrapper => analysis::CELL_WRAPPER,
            Self::RecordMissingChildren => analysis::RECORD_MISSING_CHILDREN,
            Self::ContinuationInReadable => analysis::CONTINUATION_IN_READABLE,
            Self::MapReadInResult | Self::MapReadValueBinder => syntax::RUST_SYNTAX,
            Self::RestMismatch => syntax::INVALID_LIST_NOTATION,
            Self::OpenRecordOutsidePattern => syntax::INVALID_RECORD_UPDATE,
            Self::ComputationBackItem => collect::INVALID_CONFIGURATION,
            Self::RecordUpdateBase | Self::RecordRemainderInCellsTerm => {
                analysis::INVALID_RECORD_UPDATE
            }
            Self::MapCollectionKey => analysis::MAP_COLLECTION_KEY,
        }
    }
}

impl Refusal {
    /// Every refusal, in declaration order (each at its discriminant): the refusals
    /// [`Self::reason`] is checked over.
    pub const ALL: [Self; 30] = [
        Self::WildcardOutsidePattern,
        Self::AliasOutsidePattern,
        Self::NoneInInitializer,
        Self::InitializerRemainder,
        Self::AnonymousRestInMapLiteral,
        Self::PresenceOnPlainCell,
        Self::BracketReading,
        Self::InstancesOnPlainCell,
        Self::InstanceListShape,
        Self::ListBothEnds,
        Self::ListBackKept,
        Self::MapNotationAtNonMap,
        Self::CellWrapper,
        Self::OptionalWithoutPresence,
        Self::CollectionWithoutInstances,
        Self::BelowOptionalAncestor,
        Self::BelowCollectionAncestor,
        Self::UnmatchedOptionalResult,
        Self::RecordMissingChildren,
        Self::ContinuationInReadable,
        Self::AbsenceTestWithoutCreation,
        Self::RestMismatch,
        Self::OpenRecordOutsidePattern,
        Self::ComputationBackItem,
        Self::ConsListBackItem,
        Self::RecordUpdateBase,
        Self::RecordRemainderInCellsTerm,
        Self::MapReadInResult,
        Self::MapCollectionKey,
        Self::MapReadValueBinder,
    ];

    /// Why the entry of the cell `cell`, of the kind `kind` (a leaf of the sort `sort`, where
    /// it is one and its sort is known), written in `form`, is refused: what its spelling means
    /// against its cell, in the terms of the entry and the cell, whichever form wrote it (design
    /// §2.7). It explains; what to write instead depends on the cell's declaration and the
    /// form, and is the advice its reporter adds where the class has one.
    #[must_use]
    #[expect(
        clippy::too_many_lines,
        reason = "One exhaustive match gives every refusal its reason."
    )]
    pub fn reason(
        self,
        form: EntryForm,
        cell: &str,
        kind: &EntryKind,
        sort: Option<&str>,
    ) -> String {
        let own = &kind.own.layers;
        let holds = described(own, sort);
        match self {
            Self::WildcardOutsidePattern => format!(
                "the entry of the cell `{cell}` holds `_`, which only a pattern can: `_` matches any content and gives none, while a result or an initializer gives the cell its content"
            ),
            Self::AliasOutsidePattern => format!(
                "the entry of the cell `{cell}` names a term with `@` outside a pattern, where nothing was matched to name: a result keeps its subject's anonymous rest with `..` and puts a named one back with `..name`, and an initializer updates a record with `..base`"
            ),
            Self::NoneInInitializer => format!(
                "the initial value of the optional cell `{cell}` is `None`, which gives it no template, and K needs one to know what a created cell looks like"
            ),
            Self::InitializerRemainder => format!(
                "the initial value of the cell `{cell}` holds a rest (`..`), but an initializer's value is complete: it has no subject whose rest the `..` could keep, so it lists every item"
            ),
            Self::AnonymousRestInMapLiteral => format!(
                "the entry of the cell `{cell}` holds a map literal with an anonymous `..`, which names no map here: the literal is not the cell's content, so there is no map whose other entries the `..` could stand for"
            ),
            Self::PresenceOnPlainCell => format!(
                "the cell `{cell}` holds {holds} and is not optional (it is declared without `multiplicity = \"?\"`), so it is always there: {} are the presence of an optional cell, which `{cell}` has none of",
                if form == EntryForm::Initializer {
                    "`Some(..)` and `k::absent!(..)`"
                } else {
                    "`Some(..)` and `None`"
                }
            ),
            Self::BracketReading => format!(
                "the cell `{cell}` holds {holds}, which brackets do not denote: a bracketed entry is a computation's items, a List collection's instances, or the elements of a list (the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's){}",
                k_leaf(own, sort).map_or_else(String::new, |leaf| format!("; {leaf}"))
            ),
            Self::InstancesOnPlainCell => format!(
                "the cell `{cell}` holds {holds}, not a collection: an instance list names the instances of a cell declared `#[k::cell(multiplicity = \"*\", cell_type = .., nested)]`; the empty Map or Set a leaf cell holds is `map::empty()` or `set::empty()`, and its empty List is `[]`"
            ),
            Self::InstanceListShape => match own.first() {
                Some(Layer::Instances(Order::List)) => format!(
                    "the cell `{cell}` is a List collection, whose instances are positional: they stand in brackets, at the front before `..` and at the back after it, not in braces"
                ),
                Some(Layer::Instances(order)) => format!(
                    "the cell `{cell}` is a {} collection, whose instances are unordered: they stand in braces, each an instance record naming the instance it matches or writes, not in brackets or as a value",
                    order_name(*order)
                ),
                _ => format!(
                    "the entry of the cell `{cell}` writes instances in a shape its collection does not have"
                ),
            },
            Self::ListBothEnds => format!(
                "this entry names instances at both ends of the List collection `{cell}`; a KRS rule changes either the front (before `..`) or the back (after it), so split it into two rules"
            ),
            Self::ListBackKept => format!(
                "a back instance of the List collection `{cell}` is matched in place; KRS creates or removes instances at the back, and reads and updates them at the front"
            ),
            Self::MapNotationAtNonMap => format!(
                "the cell `{cell}` holds {holds}, not a map: map notation ({}) denotes the entries of a cell whose sort is the builtin `Map`",
                if matches!(form, EntryForm::Cells | EntryForm::Initializer) {
                    "`k::map![..]`"
                } else {
                    "`{ k -> v, .. }`, `map![..]`"
                }
            ),
            Self::CellWrapper => format!(
                "the cell `{cell}` holds {holds}, and the entry's wrapper is not that content's: {}{}",
                match form {
                    EntryForm::Cells => {
                        "`KCell(..)` wraps a computation's items and `Cell(..)` a leaf's value, on the cell that holds one"
                    }
                    // A value on the computation lacks its items' notation; `k::k![..]` on any
                    // other cell writes a computation's items where none stand.
                    EntryForm::Initializer if is_computation(own) => {
                        "a computation's initial value is its items, in `k::k![..]` or in brackets, and a value alone is no computation"
                    }
                    EntryForm::Initializer => match own.last() {
                        Some(Layer::Group(_)) => {
                            "`k::k![..]` lists a computation's items, which only a computation cell holds, and a group's initial value is its record"
                        }
                        _ => {
                            "`k::k![..]` lists a computation's items, which only a computation cell holds, and a leaf's initial value is one term of its sort"
                        }
                    },
                    EntryForm::Readable | EntryForm::Claim => {
                        "a computation's entry is its items in brackets, read from the front, and a value alone is no computation"
                    }
                },
                k_leaf(own, sort).map_or_else(String::new, |leaf| format!("; {leaf}"))
            ),
            Self::OptionalWithoutPresence if form == EntryForm::Initializer => format!(
                "the cell `{cell}` is optional (`multiplicity = \"?\"`), so its initial value states whether it starts there: `Some(..)` holds its content when it does, and `k::absent!(..)` the template of the cell when it does not"
            ),
            Self::OptionalWithoutPresence => format!(
                "the cell `{cell}` is optional (`multiplicity = \"?\"`), so its entry states whether it is there: `Some(..)` holds its content when it is, and `None` stands for its absence"
            ),
            Self::CollectionWithoutInstances => format!(
                "the cell `{cell}` is {holds} (`multiplicity = \"*\"`), so its entry is a list of its instances, each an instance record, not one value: no single cell has the content a value would name"
            ),
            Self::BelowOptionalAncestor => format!(
                "the cell `{cell}` is a cell of an optional (`?`) group, so an entry naming it at the record's level would silently require the group present: an entry names the content of its own level, and the group's presence is written at the group's"
            ),
            Self::BelowCollectionAncestor => format!(
                "the cell `{cell}` is a cell of a collection's (`*`) instance, so no single cell has the content an entry naming it at the record's level would name: there is one `{cell}` per instance, and an entry names the instance through its instance record"
            ),
            Self::UnmatchedOptionalResult => format!(
                "the result writes the optional cell `{cell}`, which the subject does not match, so the rule does not know whether the cell is there: the subject matches it with `Some(..)` or `None` first"
            ),
            Self::RecordMissingChildren => format!(
                "the group record of the cell `{cell}` names some of its children and no `..`: a record without `..` names every child, as a Rust struct literal does, and `..` leaves the others as they are"
            ),
            Self::ContinuationInReadable => format!(
                "the readable entry of the computation cell `{cell}` captures or drops its continuation (with a named rest, a splice, a whole binder, or a result without the subject's `..`): a readable rule keeps the rest of the computation with its anonymous `..`, and a `cells!` rule's `KCell(.., rest @ ..)` is what captures it"
            ),
            Self::AbsenceTestWithoutCreation => format!(
                "the subject tests that the optional cell `{cell}` is absent (`None`), and the result does not create it: K tests a cell's absence only by creating the cell, so a subject's `None` stands where its result creates it with `Some(..)`"
            ),
            Self::RestMismatch => format!(
                "the entry of the cell `{cell}` has a rest (`..`) on one side of the rule only: a result's `..` keeps the rest its subject's `..` matched, and a result without it would keep that rest to K but drop it to a Rust reader"
            ),
            Self::OpenRecordOutsidePattern => format!(
                "the entry of the cell `{cell}` leaves a record open (`..`) outside a pattern, over a group that exists: in a built term `..` stands for Rust's default fields, which only a created instance has (its template), so the record names every child or updates the record its subject matched"
            ),
            Self::ComputationBackItem => format!(
                "the entry of the computation cell `{cell}` has an item after its rest: a computation is read from its front, where its next step is, so `..` ends it"
            ),
            Self::ConsListBackItem => format!(
                "the cell `{cell}` holds a cons list, which is matched and built from its front, so its back is no constructor pattern: `..` only ends its brackets, after the elements before the rest"
            ),
            Self::RecordUpdateBase => format!(
                "the entry of the cell `{cell}` updates a record (`..base`) whose base the sentence does not match: an update takes the fields of a record of its own constructor that the subject names `base @ ..`, such as an instance its subject's instance list labels"
            ),
            Self::RecordRemainderInCellsTerm => format!(
                "the `cells!` entry of the cell `{cell}` takes a record's other children from a base (`..base`) that is no instance its subject labels: `cells!` is the reference notation, which names every child, and its one update rewrites in place the instance of a collection its subject labels; write each other child the record takes, and a group's children as their own entries"
            ),
            Self::MapReadInResult => format!(
                "the entry of the cell `{cell}` reads a map (`{{ k -> v, .. }}`) in a result: a map read is a pattern, and a readable record's result has no map write yet (a stated limitation; a `cells!` result has `Cell(k::map![k -> v, ..])`)"
            ),
            Self::MapCollectionKey => {
                let key = match own.as_slice() {
                    [Layer::Instances(order), Layer::Group(group), ..] => group.key(*order),
                    _ => None,
                };
                format!(
                    "an instance of the Map collection `{cell}` does not keep its key{}, its first child, which is its identity: a created instance states it, and an update keeps the key its subject matched, since another key is another entry of the map",
                    key.map_or_else(String::new, |key| format!(" `{key}`"))
                )
            }
            Self::MapReadValueBinder => format!(
                "the map read of the cell `{cell}` maps a key to a value that is no fresh binder: at a readable record's top level the value names what the entry maps to (a stated limitation; inside an instance record the value is matched)"
            ),
        }
    }
}

/// An entry of a context alias or an equation's function context whose cell's content those
/// sentences' lowerings do not read ([`fixed_cells_only_reason`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnreadEntry {
    /// A `?` cell's `Some(..)` or a collection's instance list: the present cell, or the
    /// instances it names.
    PresentOrInstances,
    /// The entry of a fixed group cell (a binder, `_`, an alias or a record of the group): the
    /// group's cell term, a value of its cell sort.
    Group,
}

/// Why the entry of the cell `cell` in a context alias or an equation's function context, a `?`
/// cell's `Some(..)`, a collection's instance list or a group cell's entry (`entry`), is refused:
/// the limit of those two sentences, whose lowerings read the content of fixed leaf cells only,
/// one leaf's content each. The entry has a meaning, the same as in a rule's subject (the present
/// cell, the instances it names, or the group's cell term, matched and kept), and no lowering
/// there yet. Every site that meets such an entry answers with this one reason, under
/// `krs::expand::cell-collection-placement`: the macro for a collection's named rest, which no
/// context alias binding carries, the collector once the entry's kind admits it, and the
/// compiler's lowerings of the two sentences.
#[must_use]
pub fn fixed_cells_only_reason(cell: &str, entry: UnreadEntry) -> String {
    let (what, advice) = match entry {
        UnreadEntry::PresentOrInstances => (
            "a `?` cell's `Some(..)` or a collection's instance list",
            "",
        ),
        UnreadEntry::Group => (
            "which names the whole group cell",
            "; name the leaf cells inside it, each with an entry of its own",
        ),
    };
    format!(
        "a context alias and an equation's function context read fixed leaf cells only; the entry of `{cell}`, {what}, is not supported there yet{advice}"
    )
}

/// Where `spelling`, an admitted entry of a cell whose own kind is `stack`, names a child of one
/// of its collection's instance records as a `?` cell's `Some(..)` or `None`: the path to the
/// first such child, in reading order, its name, and whether it is `Some(..)`. Inside one
/// instance the child means whether that instance holds the cell, which the table admits and no
/// lowering writes yet, the limit [`crate::INSTANCE_CHILD_MULTIPLICITY`]; it is asked once the
/// sentence's entries are admitted, so a principle the same entry breaks answers first.
#[must_use]
pub fn instance_child_presence<'s>(
    stack: &[Layer],
    spelling: &'s EntrySpelling,
) -> Option<(Vec<usize>, &'s str, bool)> {
    let [Layer::Instances(_), Layer::Group(group), ..] = stack else {
        return None;
    };
    let entry = usize::from(matches!(spelling, EntrySpelling::Alias(..)));
    let seq = sequence(unaliased(spelling))?;
    seq.items.iter().enumerate().find_map(|(step, item)| {
        let record = record_of(item, group)?;
        let labelled = matches!(item, EntrySpelling::Alias(..));
        record
            .fields
            .iter()
            .enumerate()
            .find_map(|(child, (name, value))| {
                let present = match unaliased(value) {
                    EntrySpelling::Present(_) => true,
                    EntrySpelling::Missing => false,
                    _ => return None,
                };
                let path = std::iter::repeat_n(0, entry)
                    .chain([step])
                    .chain(labelled.then_some(0))
                    .chain([child])
                    .collect();
                Some((path, name.as_str(), present))
            })
    })
}

/// The step from a sequence or a map to its rest (`..`, `name @ ..`, `..name`), which is no
/// spelling of its own: [`Located::at`]'s last step where a rest is refused.
pub const REST: usize = usize::MAX;

/// A refusal and where inside the entry's spelling it is raised.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Located {
    /// The refusal.
    pub refusal: Refusal,
    /// The path from the entry's value to the spelling the refusal is raised at, each step the
    /// index of a spelling among those directly inside the one before (a record's fields, a
    /// sequence's items, a map's keys and values in turn, an application's arguments, and the one
    /// spelling inside `Some(..)`, `Cell(..)`, `k::absent!(..)` or `name @ ..`), or [`REST`]:
    /// empty at the entry's value.
    pub at: Vec<usize>,
}

/// A cell whose entry stands inside another entry's spelling: a child of a group record or of an
/// instance record at a configuration position (P1).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NestedCell<'k> {
    /// The child's name.
    pub name: &'k str,
    /// The child's kind.
    pub kind: &'k CellKind,
    /// How many steps of the path lead from the outer entry's value to the child's.
    pub depth: usize,
}

/// The spelling at `at` ([`Located::at`]) inside `spelling`; `None` where the path leads to a
/// rest or to no spelling.
#[must_use]
pub fn spelling_at<'s>(spelling: &'s EntrySpelling, at: &[usize]) -> Option<&'s EntrySpelling> {
    at.iter().try_fold(spelling, |spelling, &step| {
        inner(spelling).get(step).copied()
    })
}

/// The innermost cell whose entry holds the spelling at `at` ([`Located::at`]) inside the entry
/// `spelling` of a cell of the layers `stack`; `None` where that is the entry's own cell. The
/// children of the group and instance records the entry writes are entries of their own cells
/// (P1): a refusal raised inside one is about that cell's content, and names it.
#[must_use]
pub fn nested_cell<'k>(
    stack: &'k [Layer],
    spelling: &EntrySpelling,
    at: &[usize],
) -> Option<NestedCell<'k>> {
    let mut layers = stack;
    let mut spelling = spelling;
    let mut found = None;
    for (depth, &step) in at.iter().enumerate() {
        let Some(&next) = inner(spelling).get(step) else {
            break;
        };
        match (layers, spelling) {
            (_, EntrySpelling::Alias(..)) => {}
            (
                [Layer::Optional, below @ ..],
                EntrySpelling::Present(_) | EntrySpelling::Absent(_),
            ) => layers = below,
            ([Layer::Instances(_), below @ ..], _) if sequence(spelling).is_some() => {
                layers = below;
            }
            (
                [Layer::Group(group), ..],
                EntrySpelling::Record(record) | EntrySpelling::Fragment(record),
            ) if record.head == group.name => {
                let (name, _) = &record.fields[step];
                let Some((name, kind)) = group.children.iter().find(|(child, _)| child == name)
                else {
                    break;
                };
                layers = &kind.layers;
                found = Some(NestedCell {
                    name,
                    kind,
                    depth: depth + 1,
                });
            }
            _ => break,
        }
        spelling = next;
    }
    found
}

/// The content of a cell of the layers `layers`, outermost first, in words with its article (a
/// leaf's with its sort `sort` where it is known): "an optional leaf of sort `Int`", "a List
/// collection of `Job` instances", "a computation".
#[must_use]
pub fn described(layers: &[Layer], sort: Option<&str>) -> String {
    let noun = noun(layers, sort);
    let article = if noun.starts_with(['o', 'a', 'e', 'i', 'u']) {
        "an"
    } else {
        "a"
    };
    format!("{article} {noun}")
}

/// Whether a cell of the layers `layers` holds a computation, inside its presence or its
/// instances.
fn is_computation(layers: &[Layer]) -> bool {
    layers
        .iter()
        .any(|layer| matches!(layer, Layer::Computation))
}

/// What a leaf of sort `KSequence` holds, where `layers` and `sort` are one's: one term of that
/// sort, as a `KSequence` field holds one, and not a computation's items, which only a
/// computation cell holds. Its sort is the computation's, so a refusal of the computation's
/// notation on it says that it is none.
fn k_leaf(layers: &[Layer], sort: Option<&str>) -> Option<&'static str> {
    (matches!(layers.last(), Some(Layer::Leaf(Notation::Plain)))
        && sort == Some(krs_ir::BuiltinSort::KSequence.spec().marker_name))
    .then_some(
        "a leaf of sort `KSequence` is no computation: it holds one term of that sort, as a `KSequence` field does, and no KRS term lists a sequence's items, so a name bound to such a value writes it",
    )
}

/// The content of a cell of the layers `layers`, in words.
fn noun(layers: &[Layer], sort: Option<&str>) -> String {
    match layers.split_first() {
        Some((Layer::Optional, inner)) => format!("optional {}", noun(inner, sort)),
        Some((Layer::Instances(order), inner)) => match inner.first() {
            Some(Layer::Group(group)) => format!(
                "{} collection of `{}` instances",
                order_name(*order),
                group.name
            ),
            _ => format!("{} collection of instances", order_name(*order)),
        },
        Some((Layer::Computation, _)) => "computation".to_owned(),
        Some((Layer::Leaf(notation), _)) => match (notation, sort) {
            (Notation::Plain | Notation::Cons, Some(sort)) => format!("leaf of sort `{sort}`"),
            (Notation::Plain, None) => "leaf".to_owned(),
            (Notation::Cons, None) => "cons-list leaf".to_owned(),
            (Notation::List, _) => "`List` leaf".to_owned(),
            (Notation::Map, _) => "`Map` leaf".to_owned(),
            (Notation::Set, _) => "`Set` leaf".to_owned(),
        },
        Some((Layer::Group(group), _)) => format!("group `{}`", group.name),
        None => "group".to_owned(),
    }
}

/// A collection's order, as its `cell_type` names it.
const fn order_name(order: Order) -> &'static str {
    match order {
        Order::List => "List",
        Order::Set => "Set",
        Order::Map => "Map",
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

    /// The registered code of the warning the lint is reported as.
    #[must_use]
    pub const fn code(self) -> krs_diagnostic::Code {
        match self {
            Self::NoEffectEntry => krs_diagnostic::codes::analysis::NO_EFFECT_ENTRY,
        }
    }

    /// Why the entry of the cell `cell` owes the lint, and what to write instead.
    #[must_use]
    pub fn reason(self, cell: &str) -> String {
        match self {
            Self::NoEffectEntry => format!(
                "the entry of the cell `{cell}` has no effect: it matches every content the cell can hold and binds nothing, and the sentence keeps the cell as it is, so it means the same without the entry; drop the entry, or bind or constrain the content it matches"
            ),
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

/// The marks a spelling is read by: its form's, and whether it stands in a record's or a
/// fragment's child. A child is written as its content, so `cells!`'s marks of a whole entry
/// (the `Cell(..)` and `KCell(..)` wrappers, an instance list's brackets and an instance set's
/// braces at the entry's head) are not a child's: a leaf child is its value, a computation
/// child's brackets or `k::k![..]` are its items (`cc: [y, ..]`), and a collection child's
/// brackets or braces are its instances, as a readable record's child reads them. A `k::k![..]`
/// where the child holds no computation is a term, whose sort the term's own judgement answers.
/// Every other form writes a record's child as it writes a whole entry.
#[derive(Clone, Copy)]
struct Marks {
    form: EntryForm,
    child: bool,
}

impl Marks {
    /// Whether `cells!`'s marks of a whole entry are read.
    fn whole_cells_entry(self) -> bool {
        self.form == EntryForm::Cells && !self.child
    }

    /// The mark `spelling` carries at a cell of `stack`.
    fn of(self, spelling: &EntrySpelling, stack: &[Layer]) -> Mark {
        let readable = self.form.is_readable();
        let cells_child = self.form == EntryForm::Cells && self.child;
        let computation = stack.contains(&Layer::Computation);
        match spelling {
            EntrySpelling::Present(_) | EntrySpelling::Missing | EntrySpelling::Absent(_) => {
                Mark::Presence
            }
            EntrySpelling::Cell(_) => Mark::Leaf,
            EntrySpelling::KCell(_) => Mark::Computation,
            EntrySpelling::InstanceList(_) => Mark::InstanceList,
            EntrySpelling::InstanceSet(_) => Mark::InstanceSet,
            EntrySpelling::KMacro(_)
                if self.form == EntryForm::Initializer || (cells_child && computation) =>
            {
                Mark::Computation
            }
            EntrySpelling::Brackets(_) if !self.whole_cells_entry() => Mark::Sequence,
            EntrySpelling::Braces(_) if readable || cells_child => Mark::InstanceSet,
            EntrySpelling::MapRead(_) if readable => Mark::Map,
            EntrySpelling::MapLiteral(_) if self.form == EntryForm::Initializer => Mark::Map,
            _ => Mark::Value,
        }
    }

    /// Whether `layer` reads `mark`.
    fn read(self, layer: &Layer, mark: Mark) -> bool {
        let cells = self.whole_cells_entry();
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

    /// Whether `layer` has a mark of its own, which a value at its position lacks.
    fn marked(self, layer: &Layer) -> bool {
        match layer {
            Layer::Optional | Layer::Instances(_) | Layer::Computation => true,
            Layer::Leaf(_) => self.whole_cells_entry(),
            Layer::Group(_) => false,
        }
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
        // Brackets are a List collection's instances, so on a Set or Map collection they are
        // its instances of the wrong order, whatever they hold.
        Mark::Sequence | Mark::InstanceSet | Mark::InstanceList
            if stack
                .iter()
                .any(|layer| matches!(layer, Layer::Instances(_))) =>
        {
            Refusal::InstanceListShape
        }
        Mark::Sequence => Refusal::BracketReading,
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
    if matches!(record.tail, RecordTail::Exact) && !names_every_field(record, group) {
        return Err(Refusal::RecordMissingChildren);
    }
    Ok(())
}

/// Whether `record`, a record of `group`, names each of the group's children.
fn names_every_field(record: &EntryRecord, group: &GroupKind) -> bool {
    record.fields.len() == group.children.len()
}

/// Whether `record`, a record of `group`, writes a bare `..` that leaves a child unnamed. A
/// bare `..` in a built record is Rust's default fields; where the record names every child
/// it defaults none, and Rust and K read the same exact record.
fn leaves_open(record: &EntryRecord, group: &GroupKind) -> bool {
    record.tail == RecordTail::Open && !names_every_field(record, group)
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
    bound: &'b dyn Fn(&str) -> Option<Bound>,
    groups: &'b [GroupKind],
    sorted: bool,
    /// Where the spelling being judged stands inside the entry ([`Located::at`]). A step is
    /// pushed before the spelling it leads to is judged and popped once that spelling is
    /// admitted, so a refusal leaves the path at the spelling it is raised at.
    path: Vec<usize>,
    /// Whether the spelling being judged stands in a term: an argument of a call, or inside a
    /// `Cell(..)`, a `KCell(..)`, a computation's or a map's literal. A record's, a fragment's
    /// and `Some(..)`'s children, and what brackets and braces hold, stand where they do.
    in_term: bool,
    /// Whether the spelling being judged stands in a record's or a fragment's child, which is
    /// written as the child's content ([`Marks`]).
    child: bool,
}

impl Admission<'_> {
    fn new<'b>(
        form: EntryForm,
        side: EntrySide,
        bound: &'b dyn Fn(&str) -> Option<Bound>,
        groups: &'b [GroupKind],
    ) -> Admission<'b> {
        Admission {
            form,
            side,
            bound,
            groups,
            sorted: false,
            path: Vec::new(),
            in_term: false,
            child: false,
        }
    }

    /// The marks the spelling being judged is read by.
    const fn marks(&self) -> Marks {
        Marks {
            form: self.form,
            child: self.child,
        }
    }

    /// `judge` over the spelling at the step `step` inside the one being judged.
    fn within<T>(
        &mut self,
        step: usize,
        judge: impl FnOnce(&mut Self) -> Result<T, Refusal>,
    ) -> Result<T, Refusal> {
        self.path.push(step);
        let judged = judge(self)?;
        self.path.pop();
        Ok(judged)
    }

    /// The refusal `refusal`, raised at the spelling the path reaches.
    fn located(&self, refusal: Refusal) -> Located {
        Located {
            refusal,
            at: self.path.clone(),
        }
    }

    /// Step 1, over the whole spelling.
    fn form(&mut self, spelling: &EntrySpelling) -> Result<(), Refusal> {
        let pattern = self.side == EntrySide::Subject;
        let initializer = self.side == EntrySide::Initializer;
        let named_rest = matches!(
            sequence(spelling)
                .and_then(|seq| seq.rest.as_ref().map(|(rest, _)| rest))
                .or_else(|| map_entries(spelling).and_then(|map| map.rest.as_ref())),
            Some(EntryRest::Named(_))
        );
        match spelling {
            EntrySpelling::Wild if !pattern => return Err(Refusal::WildcardOutsidePattern),
            EntrySpelling::Missing if initializer => return Err(Refusal::NoneInInitializer),
            // `name @ P` stands in a pattern only, at any depth, and a rest is no exception: a
            // result keeps the subject's anonymous rest with `..` and puts a named one back with
            // `..name`; the subject drops a rest by naming it `_rest @ ..` and not putting it
            // back. An initializer is a result with no subject: nothing in it is a pattern.
            EntrySpelling::Alias(..) if !pattern => return Err(Refusal::AliasOutsidePattern),
            _ if !pattern && named_rest => {
                self.path.push(REST);
                return Err(Refusal::AliasOutsidePattern);
            }
            // An initializer's value is the whole initial content: it keeps no unwritten rest
            // (P5). A named base, `[0, ..base]`, is an update and stays.
            EntrySpelling::KMacro(seq) | EntrySpelling::Brackets(seq)
                if initializer && matches!(seq.rest, Some((EntryRest::Anonymous, _))) =>
            {
                self.path.push(REST);
                return Err(Refusal::InitializerRemainder);
            }
            // Its computation splices no configuration variable's, `k::k![x, ..pgm]`: an
            // item-sorted variable is an item, so `k::k![x, pgm]` says it (E3).
            EntrySpelling::KMacro(seq)
                if initializer && matches!(seq.rest, Some((EntryRest::Splice(_), _))) =>
            {
                self.path.push(REST);
                return Err(Refusal::InitializerRemainder);
            }
            // `..` names the rest of a map only where a `cells!` pattern frames one, or where a
            // pattern matches a map in a term, below every configuration position: there a map
            // literal is a map pattern, the map's entries and the rest that holds its others
            // (`Load(map![1 -> v, ..])`). A readable record writes a cell's own map with braces,
            // `{ k -> v, .. }`. A `cells!` result's map at a content root
            // (`Cell(k::map![.., ..])`, a record field's `k::map![.., ..]`) keeps its subject's
            // rest, a frame write this route does not lower yet (the stated M3 limitation).
            EntrySpelling::MapLiteral(map)
                if map.rest == Some(EntryRest::Anonymous)
                    && !(pattern && (self.form == EntryForm::Cells || self.in_term)) =>
            {
                self.path.push(REST);
                return Err(Refusal::AnonymousRestInMapLiteral);
            }
            _ => {}
        }
        let in_term = self.in_term;
        self.in_term |= matches!(
            spelling,
            EntrySpelling::Call(_)
                | EntrySpelling::Cell(_)
                | EntrySpelling::KCell(_)
                | EntrySpelling::MapLiteral(_)
                | EntrySpelling::MapRead(_)
                | EntrySpelling::KMacro(_)
        );
        for (step, one) in inner(spelling).into_iter().enumerate() {
            self.within(step, |admission| admission.form(one))?;
        }
        self.in_term = in_term;
        Ok(())
    }

    /// Step 2 against `stack`, outermost layer first.
    fn kind(
        &mut self,
        stack: &[Layer],
        spelling: &EntrySpelling,
        head: bool,
    ) -> Result<(), Refusal> {
        if let EntrySpelling::Alias(_, pattern) = spelling {
            return self.within(0, |admission| admission.kind(stack, pattern, head));
        }
        let Some((outer, below)) = stack.split_first() else {
            return self.value(spelling);
        };
        // An initializer's value for a collection, at any depth, is one instance's template.
        if self.side == EntrySide::Initializer && matches!(outer, Layer::Instances(_)) {
            return self.kind(below, spelling, head);
        }
        let mark = self.marks().of(spelling, stack);
        if self.lacks(outer, below, mark) {
            return self.missing_layer(stack, spelling, head);
        }
        if mark == Mark::Value {
            if let Layer::Group(group) = outer {
                return self.group(group, spelling);
            }
            return self.value(spelling);
        }
        if !self.marks().read(outer, mark) {
            return Err(foreign(mark, stack));
        }
        match (outer, spelling) {
            (Layer::Optional, EntrySpelling::Present(content) | EntrySpelling::Absent(content)) => {
                self.within(0, |admission| admission.kind(below, content, head))
            }
            (Layer::Optional, _) => Ok(()),
            (Layer::Leaf(notation), EntrySpelling::Cell(content)) => {
                self.within(0, |admission| admission.leaf(*notation, content))
            }
            (Layer::Instances(order), _) => self.instances(*order, below, spelling),
            (Layer::Leaf(_), EntrySpelling::MapRead(map)) => {
                // Both limitations are the readable record's top-level route's. A group
                // record's or an instance record's child is a content root its record's route
                // lowers (a field's value is its child's content), so a map read with a rest
                // there has the M3 limitation its `cells!` twin `k::map![k -> v, ..]` has: in a
                // result it would be the frame write `Cell(k::map![k -> v, ..])`, which a
                // readable record has no spelling for yet.
                let child = !head && map.rest.is_some();
                if (head || child) && self.form.is_readable() && self.side == EntrySide::Result {
                    return Err(Refusal::MapReadInResult);
                }
                if head
                    && map.entries.iter().any(|(_, value)| {
                        !matches!(value, EntrySpelling::Binder(_) | EntrySpelling::Wild)
                    })
                {
                    return Err(Refusal::MapReadValueBinder);
                }
                self.entries(map)
            }
            (_, EntrySpelling::MapLiteral(map)) => self.entries(map),
            (Layer::Computation, _) => self.computation(spelling),
            (Layer::Leaf(notation), EntrySpelling::Brackets(seq)) => {
                cons_front(*notation, seq)?;
                self.items(seq)
            }
            _ => sequence(spelling).map_or(Ok(()), |seq| self.items(seq)),
        }
    }

    /// Each item of `seq`, a value.
    fn items(&mut self, seq: &EntrySeq) -> Result<(), Refusal> {
        for (step, item) in seq.items.iter().enumerate() {
            self.within(step, |admission| admission.value(item))?;
        }
        Ok(())
    }

    /// Whether an entry whose head carries `mark` lacks the layer `outer`, above `below`: a value
    /// where `outer` has a mark, or a mark of a layer below it.
    fn lacks(&self, outer: &Layer, below: &[Layer], mark: Mark) -> bool {
        if mark == Mark::Value {
            self.marks().marked(outer)
        } else {
            !self.marks().read(outer, mark)
                && below.iter().any(|layer| self.marks().read(layer, mark))
        }
    }

    /// An entry that lacks `stack`'s outermost layer is refused for it only where its inside
    /// passes against the layers the advice puts it in: below every layer it lacks, each of
    /// which the advice adds. Otherwise the advice would be refused again there, so the inside's
    /// own refusal is the one named.
    fn missing_layer(
        &mut self,
        stack: &[Layer],
        spelling: &EntrySpelling,
        head: bool,
    ) -> Result<(), Refusal> {
        let mark = self.marks().of(spelling, stack);
        let mut inside = &stack[1..];
        while let Some((outer, below)) = inside.split_first()
            && self.lacks(outer, below, mark)
            && !(self.side == EntrySide::Initializer && matches!(outer, Layer::Instances(_)))
        {
            inside = below;
        }
        self.kind(inside, spelling, head)?;
        Err(missing(&stack[0]))
    }

    /// Inside a leaf's `Cell(..)`: the leaf's own notation, or its value.
    fn leaf(&mut self, notation: Notation, content: &EntrySpelling) -> Result<(), Refusal> {
        match content {
            EntrySpelling::Brackets(seq) => {
                if !matches!(notation, Notation::List | Notation::Cons) {
                    return Err(Refusal::BracketReading);
                }
                cons_front(notation, seq)?;
                self.items(seq)
            }
            EntrySpelling::MapLiteral(map) => {
                if notation != Notation::Map {
                    return Err(Refusal::MapNotationAtNonMap);
                }
                self.entries(map)
            }
            other => self.value(other),
        }
    }

    /// A collection's instances: each item an instance record of the collection's group, or a
    /// value for one whole instance: any value in an ordered collection (its front instance),
    /// a name or `_` in an unordered one (any instance it holds).
    fn instances(
        &mut self,
        order: Order,
        below: &[Layer],
        spelling: &EntrySpelling,
    ) -> Result<(), Refusal> {
        let seq = sequence(spelling).expect("an instance mark is a sequence");
        // A List collection's items after its rest are its back instances (P2): which ends a
        // rule changes is the pairing's ([`list_ends`]).
        for (step, item) in seq.items.iter().enumerate() {
            self.within(step, |admission| {
                let (item, aliased) = match item {
                    EntrySpelling::Alias(_, pattern) => (&**pattern, true),
                    other => (other, false),
                };
                if aliased {
                    admission.path.push(0);
                }
                match (item, below.first()) {
                    (
                        EntrySpelling::Record(_) | EntrySpelling::Fragment(_),
                        Some(Layer::Group(group)),
                    ) => {
                        admission.group(group, item)?;
                    }
                    // One instance of an ordered collection is its front one.
                    _ if order == Order::List => admission.value(item)?,
                    // A name or `_` is one whole instance of an unordered collection, any one
                    // it holds, as a record labelled with the name names it.
                    (EntrySpelling::Binder(_) | EntrySpelling::Wild, _) => admission.value(item)?,
                    // Any other value is no instance: an unordered collection's instance is
                    // chosen by its record.
                    _ => return Err(Refusal::InstanceListShape),
                }
                if aliased {
                    admission.path.pop();
                }
                Ok(())
            })?;
        }
        Ok(())
    }

    /// Brackets, `KCell(..)` or `k::k![..]` on a computation.
    fn computation(&mut self, spelling: &EntrySpelling) -> Result<(), Refusal> {
        let seq = sequence(spelling).expect("a computation's mark is a sequence");
        self.items(seq)?;
        // A readable rule never drops or captures the continuation.
        if self.form.is_readable()
            && matches!(
                seq.rest,
                Some((EntryRest::Named(_) | EntryRest::Splice(_), _))
            )
        {
            self.path.push(REST);
            return Err(Refusal::ContinuationInReadable);
        }
        // The computation is read from its front, where the next step is, in every form: `..`
        // ends it and no item follows (E1).
        if !seq.back().is_empty() {
            self.path.push(seq.items.len() - seq.back().len());
            return Err(Refusal::ComputationBackItem);
        }
        Ok(())
    }

    /// A value at a group's position: a record of the group, or the fragment it abbreviates,
    /// names its children's entries, each that child cell's entry read by the child's declared
    /// kind as if the child were its own cell, on both sides, in its content's marks
    /// ([`Marks`]); a fragment is a term besides; any other value is a term.
    fn group(&mut self, group: &GroupKind, spelling: &EntrySpelling) -> Result<(), Refusal> {
        let record = match spelling {
            EntrySpelling::Record(record) if record.head == group.name => record,
            EntrySpelling::Fragment(record) if record.head == group.name => {
                self.sorted = true;
                record
            }
            _ => return self.value(spelling),
        };
        let child = std::mem::replace(&mut self.child, true);
        let children = record
            .fields
            .iter()
            .enumerate()
            .try_for_each(|(step, (name, value))| {
                let child = group.child(name).map_or(&[][..], |kind| &kind.layers[..]);
                self.within(step, |admission| admission.kind(child, value, false))
            });
        self.child = child;
        children?;
        names_every_child(record, group)
    }

    fn entries(&mut self, map: &EntryMap) -> Result<(), Refusal> {
        for (index, (key, value)) in map.entries.iter().enumerate() {
            self.within(2 * index, |admission| admission.value(key))?;
            self.within(2 * index + 1, |admission| admission.value(value))?;
        }
        Ok(())
    }

    /// A value position: `_` and a fresh readable name take the position's sort. In a result
    /// the value is a built term, and a record in it whose bare `..` leaves a field open is
    /// refused, at that record: a bare `..` in a result is Rust's default fields, which only a
    /// created instance has, and a term's record is no instance. A `..` after every field
    /// defaults none.
    fn value(&mut self, spelling: &EntrySpelling) -> Result<(), Refusal> {
        match spelling {
            EntrySpelling::Wild => {}
            EntrySpelling::Binder(name) => {
                self.sorted |= self.form == EntryForm::Cells || (self.bound)(name).is_some();
            }
            EntrySpelling::Alias(_, pattern) => {
                return self.within(0, |admission| admission.value(pattern));
            }
            _ => self.sorted = true,
        }
        if self.side == EntrySide::Result {
            self.term(spelling)?;
        }
        Ok(())
    }

    /// A built term takes no record whose bare `..` leaves a field open: refused at the first
    /// such record ([`open_record`]).
    fn term(&mut self, spelling: &EntrySpelling) -> Result<(), Refusal> {
        if let Some(at) = open_record(spelling, self.groups) {
            self.path.extend(at);
            return Err(Refusal::OpenRecordOutsidePattern);
        }
        Ok(())
    }
}

/// Steps 1 to 3 for one entry: its form, its kind against `stack`, the cell's own layers,
/// outermost first, then its path (`path`, the layers of the cell's `?` and `*` ancestors,
/// outermost first). An initializer's value of a `*` cell is one instance's template, judged below the
/// instances layer. `bound` tells what each name the rule binds outside the entry binds (`None`:
/// the rule binds it nowhere there); `groups` are the
/// configuration's groups, whose children are the fields of a record a term writes by the
/// group's name.
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
    bound: &dyn Fn(&str) -> Option<Bound>,
    groups: &[GroupKind],
) -> Result<Admitted, Refusal> {
    admit_located(form, side, path, stack, spelling, bound, groups)
        .map_err(|located| located.refusal)
}

/// [`admit`], with where inside the spelling the refusal is raised.
///
/// # Errors
///
/// The refusal of the first step that refuses the entry, located.
pub fn admit_located(
    form: EntryForm,
    side: EntrySide,
    path: &[Layer],
    stack: &[Layer],
    spelling: &EntrySpelling,
    bound: &dyn Fn(&str) -> Option<Bound>,
    groups: &[GroupKind],
) -> Result<Admitted, Located> {
    let mut admission = Admission::new(form, side, bound, groups);
    admission
        .form(spelling)
        .map_err(|refusal| admission.located(refusal))?;
    admission
        .kind(stack, spelling, true)
        .map_err(|refusal| admission.located(refusal))?;
    let at = |refusal| Located {
        refusal,
        at: Vec::new(),
    };
    match path.first() {
        Some(Layer::Optional) => return Err(at(Refusal::BelowOptionalAncestor)),
        Some(_) => return Err(at(Refusal::BelowCollectionAncestor)),
        None => {}
    }
    Ok(Admitted {
        sorted: admission.sorted,
    })
}

/// A cons list is built from its front, so its brackets end in their rest: an item after the rest
/// lowers to no term.
fn cons_front(notation: Notation, seq: &EntrySeq) -> Result<(), Refusal> {
    if notation == Notation::Cons && !seq.back().is_empty() {
        return Err(Refusal::ConsListBackItem);
    }
    Ok(())
}

/// Adds to `groups` each group `layers` hold, at any depth (a group's children's included),
/// once by name: the groups [`admit`] reads a term's record by.
pub fn collect_groups(layers: &[Layer], groups: &mut Vec<GroupKind>) {
    for layer in layers {
        if let Layer::Group(group) = layer {
            if !groups.iter().any(|known| known.name == group.name) {
                groups.push(group.clone());
            }
            for (_, child) in &group.children {
                collect_groups(&child.layers, groups);
            }
        }
    }
}

/// The rest of an entry's content root, below presence, the leaf wrapper and an alias.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Root<'s> {
    Rest(&'s EntryRest),
    Other,
}

/// Whether `spelling`'s content root ends in the anonymous rest `..`.
fn keeps_anonymous_rest(spelling: &EntrySpelling) -> bool {
    root(spelling) == Root::Rest(&EntryRest::Anonymous)
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

/// The lint of a subject entry over a cell the sentence keeps as it is, judged against the cell's
/// own layers `stack` (Q1, P5): [`Lint::NoEffectEntry`] where the entry matches every content the
/// cell can hold ([`matches_all`], recursive over the marks) and binds nothing ([`binds`]), so the
/// sentence means the same without it. It is asked only of an entry whose cell the sentence keeps:
/// a subject entry of a cell the result leaves out ([`pair`]), or any entry of a kept pattern
/// ([`pair_kept`]); where the result writes the cell, the entry is what the rewrite starts from.
fn no_effect(spelling: &EntrySpelling, stack: &[Layer]) -> Option<Lint> {
    (matches_all(spelling, stack) && !binds(spelling)).then_some(Lint::NoEffectEntry)
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
                && (record.tail != RecordTail::Exact || names_every_field(record, group))
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

/// Where `spelling`, a term, holds a record (itself included) whose bare `..` leaves a field
/// open ([`leaves_open`]): the path to the first such record, in reading order. A record's
/// fields are those of the group of `groups` its head names; a head that names none has no
/// fields the record is known to name, so its `..` is open.
fn open_record(spelling: &EntrySpelling, groups: &[GroupKind]) -> Option<Vec<usize>> {
    let open = match spelling {
        EntrySpelling::Record(record) | EntrySpelling::Fragment(record) => {
            record.tail == RecordTail::Open
                && groups
                    .iter()
                    .find(|group| group.name == record.head)
                    .is_none_or(|group| leaves_open(record, group))
        }
        _ => false,
    };
    if open {
        return Some(Vec::new());
    }
    inner(spelling)
        .into_iter()
        .enumerate()
        .find_map(|(step, one)| {
            open_record(one, groups).map(|mut at| {
                at.insert(0, step);
                at
            })
        })
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
    /// `self`, `None` where the record has none. An update `..label` changes in place the
    /// subject's instance labelled `label`: only an instance the subject matches is rewritten in
    /// place. An update whose label no subject instance has builds a new instance from the record
    /// the sentence binds `label` to elsewhere, a created instance, where that record is of the
    /// update's own constructor: `..base` takes the fields of a value of the record's own type.
    /// It has no base (`None`) where the sentence binds `label` nowhere, to no record, or to a
    /// record of another constructor. Any other instance record creates an instance, whose `..`
    /// is its template's.
    fn instance(self, record: &EntryRecord, bound: &dyn Fn(&str) -> Option<Bound>) -> Option<Self> {
        let RecordTail::Update(label) = &record.tail else {
            return Some(Self::Created);
        };
        let shown = match self {
            Self::Matched(subject) => sequence(unaliased(subject)).and_then(|seq| {
                seq.items.iter().find_map(|item| match item {
                    EntrySpelling::Alias(name, instance) if name == label => {
                        Some(Self::Matched(instance))
                    }
                    _ => None,
                })
            }),
            Self::Unmatched | Self::Created => None,
        };
        shown.or_else(|| {
            (bound(label) == Some(Bound::Record(record.head.clone()))).then_some(Self::Created)
        })
    }
}

/// Whether a result's instance record of `group`, in a collection ordered by `order`, with
/// `other` its other side, keys its instance as its collection does ([`GroupKind::key`]): a Map
/// instance's key is its identity, written at creation and never changed. A created instance
/// writes it, since a bare `..` takes only template fields, which state no identity. An update
/// changes the instance in place, so it writes the key, if at all, as what is provably the key
/// the subject matched: the key's own binder, or the same literal, which is the same instance;
/// any other key value, or a key the labelled instance does not name, is a key change.
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
            // An update of a value bound elsewhere creates its instance, which writes its key.
            let Other::Matched(subject) = other else {
                return other == Other::Created;
            };
            keeps_key(
                value,
                record_of(subject, group).and_then(|record| named(record, key)),
            )
        }
        (RecordTail::Update(_), None) => true,
        (RecordTail::Exact | RecordTail::Open, written) => written.is_some(),
    }
}

/// Whether a result that writes a Map collection's key as `written` keeps the key `matched`,
/// what its subject matched the same instance's key with (`None` where the subject does not
/// name the key): an instance's key is its identity, so a step that changes the instance in
/// place writes it, if at all, as what is provably the key it matched. That is the subject's own
/// binder for the key (an alias's binder included), or the same literal the subject matched;
/// any other value, or a key the subject does not name, is another instance.
///
/// One predicate serves every place that judges a written key: an instance update inside an
/// instance record ([`Refusal::MapCollectionKey`]), and the flat key entry of a sentence about
/// one instance of a Map collection's group.
#[must_use]
pub fn keeps_key(written: &EntrySpelling, matched: Option<&EntrySpelling>) -> bool {
    match (written, matched) {
        (
            EntrySpelling::Binder(written),
            Some(EntrySpelling::Binder(bound) | EntrySpelling::Alias(bound, _)),
        ) => written == bound,
        (EntrySpelling::Literal(written), Some(matched)) => matches!(
            unaliased(matched),
            EntrySpelling::Literal(literal) if literal == written
        ),
        _ => false,
    }
}

/// A result's content against its other side, at the entry's cell or at a child's: its rest,
/// then each child of the group and instance records it writes, against the child's own.
fn pair_content(
    form: EntryForm,
    stack: &[Layer],
    spelling: &EntrySpelling,
    other: Other<'_>,
    bound: &dyn Fn(&str) -> Option<Bound>,
    path: &mut Vec<usize>,
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
    pair_records(form, stack, spelling, other, bound, path)
}

/// The group and instance records a result's content writes: a group that exists takes no bare
/// `..`, and each record's children are paired against their own other sides.
///
/// In `cells!`, the reference notation, a record names every child: its one update, `..me`,
/// rewrites in place the instance of a collection that its subject labels `me @`, the instance
/// the step matched (R10). A group record's `..base`, and an instance update whose label no
/// subject instance of the cell has (its base a record matched elsewhere), take children from
/// another record, and are refused ([`Refusal::RecordRemainderInCellsTerm`]). The refusal comes
/// after the record's children are paired, each against the instance the update would create: a
/// child is an entry of its own cell, whose content is wrong whatever the record's base.
fn pair_records(
    form: EntryForm,
    stack: &[Layer],
    spelling: &EntrySpelling,
    other: Other<'_>,
    bound: &dyn Fn(&str) -> Option<Bound>,
    path: &mut Vec<usize>,
) -> Result<(), Refusal> {
    let fields =
        |group: &GroupKind, record: &EntryRecord, other: Other<'_>, path: &mut Vec<usize>| {
            for (step, (name, value)) in record.fields.iter().enumerate() {
                if let Some(kind) = group.child(name) {
                    path.push(step);
                    pair_content(
                        form,
                        &kind.layers,
                        value,
                        other.child(group, name),
                        bound,
                        path,
                    )?;
                    path.pop();
                }
            }
            Ok(())
        };
    match (stack, spelling) {
        ([Layer::Optional, below @ ..], EntrySpelling::Present(content)) => {
            path.push(0);
            pair_records(form, below, content, other.present(), bound, path)?;
            path.pop();
            Ok(())
        }
        ([Layer::Group(group), ..], _) => {
            let Some(record) = record_of(spelling, group) else {
                return Ok(());
            };
            let aliased = matches!(spelling, EntrySpelling::Alias(..));
            if aliased {
                path.push(0);
            }
            if leaves_open(record, group) && other != Other::Created {
                return Err(Refusal::OpenRecordOutsidePattern);
            }
            fields(group, record, other, path)?;
            if form == EntryForm::Cells && matches!(record.tail, RecordTail::Update(_)) {
                return Err(Refusal::RecordRemainderInCellsTerm);
            }
            if aliased {
                path.pop();
            }
            Ok(())
        }
        ([Layer::Instances(order), Layer::Group(group), ..], _) => {
            let items = sequence(spelling).map_or(&[][..], |seq| &seq.items[..]);
            for (step, item) in items.iter().enumerate() {
                let Some(record) = record_of(item, group) else {
                    continue;
                };
                path.push(step);
                if matches!(item, EntrySpelling::Alias(..)) {
                    path.push(0);
                }
                let other = other
                    .instance(record, bound)
                    .ok_or(Refusal::RecordUpdateBase)?;
                if !keyed(*order, group, record, other) {
                    return Err(Refusal::MapCollectionKey);
                }
                fields(group, record, other, path)?;
                // An update whose other side is a created instance updates no subject instance.
                if form == EntryForm::Cells
                    && matches!(record.tail, RecordTail::Update(_))
                    && other == Other::Created
                {
                    return Err(Refusal::RecordRemainderInCellsTerm);
                }
                if matches!(item, EntrySpelling::Alias(..)) {
                    path.pop();
                }
                path.pop();
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Where `subject`, a subject's content on `stack`, tests a `?` child absent (`None`, inside a
/// group or instance record it writes) that `result`, the result's content of the same place
/// (`None`: the result does not write it), does not create: the path to the first such `None`.
/// K tests absence only by creating the cell, and a record's child is an entry of its own cell,
/// so the result's same child must be present: the same group's record, the same `?` cell's
/// content, or, in a collection, the result's update `..label` of the instance the subject
/// labels `label`.
fn absence_uncreated(
    stack: &[Layer],
    subject: &EntrySpelling,
    result: Option<&EntrySpelling>,
) -> Option<Vec<usize>> {
    let within = |step: usize, at: Option<Vec<usize>>| {
        at.map(|mut at| {
            at.insert(0, step);
            at
        })
    };
    if let EntrySpelling::Alias(_, pattern) = subject {
        return within(0, absence_uncreated(stack, pattern, result));
    }
    match (stack, subject) {
        // P5 at the entry's own root as at a child: a `None` the result writes the cell over
        // creates it only as `Some(..)`, so a result `None` leaves the absence test without the
        // creation K tests absence by.
        ([Layer::Optional, ..], EntrySpelling::Missing) => result
            .is_some_and(|result| !matches!(unaliased(result), EntrySpelling::Present(_)))
            .then(Vec::new),
        ([Layer::Optional, below @ ..], EntrySpelling::Present(inner)) => {
            let result = result.and_then(|result| match unaliased(result) {
                EntrySpelling::Present(inner) => Some(&**inner),
                _ => None,
            });
            within(0, absence_uncreated(below, inner, result))
        }
        ([Layer::Group(group), ..], _) => record_of(subject, group).and_then(|record| {
            fields_uncreated(group, record, result.and_then(|result| record_of(result, group)))
        }),
        ([Layer::Instances(_), Layer::Group(group), ..], inner) => {
            sequence(inner).and_then(|seq| {
                seq.items.iter().enumerate().find_map(|(step, item)| {
                    let record = record_of(item, group)?;
                    let updated = match item {
                        EntrySpelling::Alias(label, _) => result
                            .and_then(|result| sequence(unaliased(result)))
                            .and_then(|seq| {
                                seq.items
                                    .iter()
                                    .filter_map(|item| record_of(item, group))
                                    .find(|record| {
                                        matches!(&record.tail, RecordTail::Update(base) if base == label)
                                    })
                            }),
                        _ => None,
                    };
                    let at = fields_uncreated(group, record, updated);
                    let at = if matches!(item, EntrySpelling::Alias(..)) {
                        within(0, at)
                    } else {
                        at
                    };
                    within(step, at)
                })
            })
        }
        _ => None,
    }
}

/// [`absence_uncreated`] over each child a subject's `record` of `group` names, with `result`
/// the result's record of the same place.
fn fields_uncreated(
    group: &GroupKind,
    record: &EntryRecord,
    result: Option<&EntryRecord>,
) -> Option<Vec<usize>> {
    record
        .fields
        .iter()
        .enumerate()
        .find_map(|(step, (name, value))| {
            let kind = group.child(name)?;
            let written = result
                .and_then(|result| result.fields.iter().find(|(field, _)| field == name))
                .map(|(_, value)| value);
            let at = if kind.layers.first() == Some(&Layer::Optional)
                && *unaliased(value) == EntrySpelling::Missing
            {
                (!matches!(written.map(unaliased), Some(EntrySpelling::Present(_)))).then(|| {
                    if matches!(value, EntrySpelling::Alias(..)) {
                        vec![0]
                    } else {
                        Vec::new()
                    }
                })
            } else {
                absence_uncreated(&kind.layers, value, written)
            };
            at.map(|mut at| {
                at.insert(0, step);
                at
            })
        })
}

/// Which ends of a List collection an entry's instances name: the front (items before the rest,
/// or every item where the rest is last or there is none), and the back (items after it).
fn ends(spelling: &EntrySpelling) -> (bool, bool) {
    sequence(unaliased(spelling)).map_or((false, false), |seq| {
        (!seq.front().is_empty(), !seq.back().is_empty())
    })
}

/// A List collection's entry (`stack` starts with its instances layer) against its other side
/// (`other`, the other side's entry of the cell; `None` where that side does not name it, or
/// where a subject's result writes the cell, `written`, with an entry the caller does not give).
/// P2 and P6 read each item as the instance at its place, so `outcome` admits every such
/// pairing; the product lowers a List rewrite in place at one end, so two pairings are a stated
/// limitation, each refused where the lowering would refuse it:
///
/// - the subject and the result together name instances at both ends, before the rest and after
///   it ([`Refusal::ListBothEnds`]): at the subject where it names both itself, else at the
///   result, the entry to split;
/// - a subject's back instance kept in place ([`Refusal::ListBackKept`]): the result leaves the
///   cell out (a read keeps every instance it names, a single-body rule included), or updates
///   the instance through its label (`..label` after the result's rest). A back instance the
///   result writes the cell without is removed, and a result's back record that updates nothing
///   is created: both are admitted.
///
/// Moving an instance between the ends (`..label` before the rest for a back instance) and
/// reordering are the lowering's own refusals, not judged here.
fn list_ends(
    side: EntrySide,
    stack: &[Layer],
    spelling: &EntrySpelling,
    other: Option<&EntrySpelling>,
    written: bool,
) -> Result<(), Refusal> {
    if stack.first() != Some(&Layer::Instances(Order::List)) {
        return Ok(());
    }
    let (front, back) = ends(spelling);
    let (other_front, other_back) = other.map_or((false, false), ends);
    let both = (front || other_front) && (back || other_back);
    match side {
        EntrySide::Subject if front && back => Err(Refusal::ListBothEnds),
        // The result names the other end: it is refused there.
        EntrySide::Subject if both => Ok(()),
        EntrySide::Subject => {
            let labels = sequence(unaliased(spelling))
                .into_iter()
                .flat_map(EntrySeq::back)
                .filter_map(|item| match item {
                    EntrySpelling::Alias(label, _) => Some(label.as_str()),
                    _ => None,
                })
                .collect::<Vec<_>>();
            let updated = other
                .and_then(|other| sequence(unaliased(other)))
                .into_iter()
                .flat_map(EntrySeq::back)
                .any(|item| match unaliased(item) {
                    EntrySpelling::Record(record) | EntrySpelling::Fragment(record) => {
                        matches!(&record.tail, RecordTail::Update(label) if labels.contains(&label.as_str()))
                    }
                    _ => false,
                });
            if back && (!written || updated) {
                return Err(Refusal::ListBackKept);
            }
            Ok(())
        }
        EntrySide::Result if both => Err(Refusal::ListBothEnds),
        _ => Ok(()),
    }
}

/// Pairing for an admitted entry with its rule. On a subject, an absence test needs the result
/// to create the cell, at the entry's root (`written`) and at each `?` child of the group and
/// instance records it writes (`other`, the result's entry of the same cell, must write the child
/// present), and an entry that constrains nothing on a cell the result leaves out
/// (`written` false) owes [`Lint::NoEffectEntry`]. On a subject, `other` is the result's entry
/// of the same cell, `None` where the result does not write it. On a result, `other` is the subject's entry
/// of the same cell, `None` where the subject does not match the cell, and the result is
/// paired at every content root it writes: the cell's own, and each child's of the group and
/// instance records it writes, a child being an entry of its own cell. A child's other side is
/// the subject record's same child; in an instance update (`..me`), the same child of the
/// subject instance `me` labels; none where the subject's record does not name the child, and
/// none to keep for a created instance's or `?` cell's child. At each:
///
/// - a group record whose bare `..` leaves a child unnamed, for a group that exists (matched or
///   overwritten, the cell's own or one inside a `?` cell the subject matches present), is
///   [`Refusal::OpenRecordOutsidePattern`], since a bare `..` in a result is Rust's default
///   fields, which only a created instance has; the group's fragment is the same record; a
///   `..` after every child defaults none, so the record is the exact one;
/// - over a matched cell, `None` removes the cell with all its content, so it pairs no rest;
///   and its rest is its subject's: a subject's `..` is kept by a result `..` only;
/// - over an unmatched cell, the result is an overwrite, which means one configuration only
///   where the cell's presence is known and no rest is kept: a `?` cell is
///   [`Refusal::UnmatchedOptionalResult`]; a readable computation's continuation, which the
///   subject did not match, is dropped or kept unmatched, [`Refusal::ContinuationInReadable`];
///   and a root `..` keeps a rest the subject never matched, [`Refusal::RestMismatch`];
/// - a created cell had no content, so a root `..` keeps nothing, [`Refusal::RestMismatch`].
///
/// A List collection's entry is then judged by the ends its rule changes (`list_ends`).
///
/// # Errors
///
/// [`Refusal::AbsenceTestWithoutCreation`], [`Refusal::RestMismatch`],
/// [`Refusal::OpenRecordOutsidePattern`], [`Refusal::UnmatchedOptionalResult`],
/// [`Refusal::ContinuationInReadable`], [`Refusal::ListBothEnds`] or [`Refusal::ListBackKept`].
pub fn pair(
    form: EntryForm,
    side: EntrySide,
    stack: &[Layer],
    spelling: &EntrySpelling,
    other: Option<&EntrySpelling>,
    written: bool,
    bound: &dyn Fn(&str) -> Option<Bound>,
) -> Result<Option<Lint>, Refusal> {
    pair_located(form, side, stack, spelling, other, written, bound)
        .map_err(|located| located.refusal)
}

/// [`pair`], with where inside the spelling the refusal is raised.
///
/// # Errors
///
/// As [`pair`], located.
pub fn pair_located(
    form: EntryForm,
    side: EntrySide,
    stack: &[Layer],
    spelling: &EntrySpelling,
    other: Option<&EntrySpelling>,
    written: bool,
    bound: &dyn Fn(&str) -> Option<Bound>,
) -> Result<Option<Lint>, Located> {
    let root = |refusal| Located {
        refusal,
        at: Vec::new(),
    };
    match side {
        EntrySide::Subject => {
            if let Some(at) = absence_uncreated(stack, spelling, other) {
                return Err(Located {
                    refusal: Refusal::AbsenceTestWithoutCreation,
                    at,
                });
            }
            if !written && *spelling == EntrySpelling::Missing {
                return Err(root(Refusal::AbsenceTestWithoutCreation));
            }
            list_ends(side, stack, spelling, other, written).map_err(root)?;
            Ok((!written).then(|| no_effect(spelling, stack)).flatten())
        }
        EntrySide::Result => {
            let mut path = Vec::new();
            pair_content(
                form,
                stack,
                spelling,
                other.map_or(Other::Unmatched, Other::Matched),
                bound,
                &mut path,
            )
            .map_err(|refusal| Located { refusal, at: path })?;
            list_ends(side, stack, spelling, other, written).map_err(root)?;
            Ok(None)
        }
        EntrySide::Initializer => Ok(None),
    }
}

/// Pairing for an entry of a pattern the sentence keeps as it matched it ([`Rewrite::Kept`]):
/// the pattern changes nothing, so the entry is paired as a rule's subject entry over a cell the
/// result leaves out, which the rule keeps (P0, P5). Its absence test creates nothing, at the
/// cell's root and at each `?` child of the records it writes
/// ([`Refusal::AbsenceTestWithoutCreation`]), and an entry that constrains nothing owes
/// [`Lint::NoEffectEntry`]. A context (`as_rule`) is lowered as a rule's pattern is, so a List
/// collection's back instance it keeps meets the rule lowering's limit (`list_ends`); the
/// other kept patterns are lowered by lowerings of their own, which reach no List lowering, so
/// no such limit refuses them here.
///
/// # Errors
///
/// [`Refusal::AbsenceTestWithoutCreation`], and for a context [`Refusal::ListBothEnds`] or
/// [`Refusal::ListBackKept`].
pub fn pair_kept(
    form: EntryForm,
    stack: &[Layer],
    spelling: &EntrySpelling,
    as_rule: bool,
    bound: &dyn Fn(&str) -> Option<Bound>,
) -> Result<Option<Lint>, Refusal> {
    pair_kept_located(form, stack, spelling, as_rule, bound).map_err(|located| located.refusal)
}

/// [`pair_kept`], with where inside the spelling the refusal is raised.
///
/// # Errors
///
/// As [`pair_kept`], located.
pub fn pair_kept_located(
    form: EntryForm,
    stack: &[Layer],
    spelling: &EntrySpelling,
    as_rule: bool,
    bound: &dyn Fn(&str) -> Option<Bound>,
) -> Result<Option<Lint>, Located> {
    if as_rule {
        return pair_located(
            form,
            EntrySide::Subject,
            stack,
            spelling,
            None,
            false,
            bound,
        );
    }
    let at = if *spelling == EntrySpelling::Missing {
        Some(Vec::new())
    } else {
        absence_uncreated(stack, spelling, None)
    };
    if let Some(at) = at {
        return Err(Located {
            refusal: Refusal::AbsenceTestWithoutCreation,
            at,
        });
    }
    Ok(no_effect(spelling, stack))
}

/// Step 1 alone for one entry: what its spelling and its side refuse, whatever its cell.
///
/// # Errors
///
/// The form's refusal.
pub fn admit_form(
    form: EntryForm,
    side: EntrySide,
    spelling: &EntrySpelling,
) -> Result<(), Refusal> {
    admit_form_located(form, side, spelling).map_err(|located| located.refusal)
}

/// [`admit_form`], with where inside the spelling the refusal is raised: at the construct the
/// form refuses (`_`, `name @ P`, and at [`REST`] a named rest or a map literal's anonymous rest).
///
/// # Errors
///
/// The form's refusal, located.
pub fn admit_form_located(
    form: EntryForm,
    side: EntrySide,
    spelling: &EntrySpelling,
) -> Result<(), Located> {
    let mut admission = Admission::new(form, side, &|_| None, &[]);
    admission
        .form(spelling)
        .map_err(|refusal| admission.located(refusal))
}

/// One entry of a [`Sentence`]: its side, its cell (`C`, which pairs it with the other side's
/// entry of the same cell), its cell's kind, and its spelling where the reader reads one (an
/// entry it does not read, a term with an operator, is judged by no step here).
#[derive(Clone, Debug)]
pub struct SentenceEntry<'s, C> {
    /// The side it stands on.
    pub side: EntrySide,
    /// Its cell.
    pub cell: C,
    /// Its cell's kind.
    pub kind: &'s EntryKind,
    /// Its spelling, where the reader reads one.
    pub spelling: Option<&'s EntrySpelling>,
    /// Where the reader reads no spelling, whether the entry's frame is a `KCell(..)` with the
    /// anonymous rest `..` ([`crate::cell_entry::CellsField::anonymous_rest`]).
    pub anonymous_rest: bool,
}

/// What a sentence does with the cells its entries name, which decides what the pairing step
/// pairs them with.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Rewrite {
    /// A rule or a claim with a result: each entry is paired with the other side's entry of its
    /// cell.
    Result,
    /// A single-body rule: its cells are rewritten in place, so there is no other side, and every
    /// instance it names is kept.
    InPlace,
    /// A pattern the sentence matches and keeps as it matched it, with no rewrite of the cells it
    /// names: a function context, which an equation reads, a context alias, the frame of every
    /// context it makes, and a context's cells around its hole. It changes nothing, so it means
    /// what a rule with that pattern on both sides means (P0): each cell it names is kept as it
    /// matched it, as a rule keeps a cell its result leaves out (P5), and its entries are paired
    /// as such a rule's subject entries are ([`pair_kept`]).
    Kept {
        /// Whether the sentence is lowered as a rule's pattern is (a context), so the rule
        /// lowering's limits on a List collection's ends apply to it (`list_ends`). A function
        /// context and a context alias are lowered by lowerings of their own, which reach none.
        as_rule: bool,
    },
}

/// A whole sentence's entries, in source order (the subject's, then the result's), judged by
/// P4's steps over the sentence ([`Sentence::judge`]).
#[derive(Clone, Copy, Debug)]
pub struct Sentence<'s, C> {
    /// The form.
    pub form: EntryForm,
    /// The entries, in source order.
    pub entries: &'s [SentenceEntry<'s, C>],
    /// What the sentence does with its cells.
    pub rewrite: Rewrite,
    /// The names its parameters bind.
    pub parameters: &'s [String],
    /// The configuration's groups ([`collect_groups`]).
    pub groups: &'s [GroupKind],
}

impl<C: PartialEq> Sentence<'_, C> {
    fn spellings(&self, side: EntrySide) -> impl Iterator<Item = &EntrySpelling> {
        self.entries
            .iter()
            .filter(move |entry| entry.side == side)
            .filter_map(|entry| entry.spelling)
    }

    /// What `name` binds outside an entry: a record where a subject alias labels one of a head,
    /// a value where a parameter or a subject entry binds it.
    #[must_use]
    pub fn bound(&self, name: &str) -> Option<Bound> {
        self.spellings(EntrySide::Subject)
            .find_map(|spelling| record_alias(spelling, name))
            .map(Bound::Record)
            .or_else(|| {
                (self.parameters.iter().any(|parameter| parameter == name)
                    || self
                        .spellings(EntrySide::Subject)
                        .any(|spelling| binds_name(spelling, name)))
                .then_some(Bound::Value)
            })
    }

    /// P4's steps over the whole sentence: each step runs over every entry before the next
    /// starts, since a later step's question is not well posed while an earlier one is open
    /// anywhere in the sentence (a pairing assumes both sides have kinds), and a step that
    /// refuses anything ends the judgement:
    ///
    /// 1. the form, of every entry;
    /// 2. the kind, of every entry, and within an entry its own kind before its path (a path
    ///    refusal needs only the declaration, as the cell's own kind does);
    /// 3. the pairing, of every entry, where the sentence has a result; without one, a
    ///    single-body rule rewrites its cells in place, so only a List collection's ends are
    ///    judged, every instance it names being kept (`list_ends`), and a sentence that keeps
    ///    its pattern as it matched it ([`Rewrite::Kept`]) pairs each entry as a subject entry
    ///    over a cell the sentence keeps ([`pair_kept`]).
    ///
    /// The sorts are the compiler's, after. Within a step the first refusal in source order is
    /// the sentence's: one diagnostic, at one entry.
    ///
    /// An admitted sentence gives the lints its entries owe, each with its entry's index, in
    /// source order: the sentence's warnings, whatever its form.
    ///
    /// # Errors
    ///
    /// The refused entry's index and its refusal.
    pub fn judge(&self) -> Result<Vec<(usize, Lint)>, (usize, Refusal)> {
        self.judge_located()
            .map_err(|(at, located)| (at, located.refusal))
    }

    /// [`Self::judge`], with where inside the refused entry's spelling the refusal is raised.
    ///
    /// # Errors
    ///
    /// The refused entry's index and its located refusal.
    pub fn judge_located(&self) -> Result<Vec<(usize, Lint)>, (usize, Located)> {
        let root = |refusal| Located {
            refusal,
            at: Vec::new(),
        };
        let bound = |name: &str| self.bound(name);
        let entries = || {
            self.entries
                .iter()
                .enumerate()
                .filter_map(|(at, entry)| Some((at, entry, entry.spelling?)))
        };
        for (at, entry, spelling) in entries() {
            admit_form_located(self.form, entry.side, spelling).map_err(|located| (at, located))?;
        }
        for (at, entry, spelling) in entries() {
            admit_located(
                self.form,
                entry.side,
                &entry.kind.path.layers,
                &entry.kind.own.layers,
                spelling,
                &bound,
                self.groups,
            )
            .map_err(|located| (at, located))?;
        }
        let mut lints = Vec::new();
        if let Rewrite::Kept { as_rule } = self.rewrite {
            for (at, entry, spelling) in entries() {
                let lint =
                    pair_kept_located(self.form, &entry.kind.own.layers, spelling, as_rule, &bound)
                        .map_err(|located| (at, located))?;
                lints.extend(lint.map(|lint| (at, lint)));
            }
            return Ok(lints);
        }
        if self.rewrite == Rewrite::InPlace {
            for (at, entry, spelling) in entries() {
                list_ends(entry.side, &entry.kind.own.layers, spelling, None, false)
                    .map_err(|refusal| (at, root(refusal)))?;
            }
            return Ok(lints);
        }
        for (at, entry) in self.entries.iter().enumerate() {
            let other = self.entries.iter().find(|other| {
                other.side != entry.side
                    && matches!(other.side, EntrySide::Subject | EntrySide::Result)
                    && other.cell == entry.cell
            });
            let Some(spelling) = entry.spelling else {
                // An entry whose items the reader does not read is paired by its frame alone:
                // a result's `..` keeps the subject's unnamed rest of the cell (P6), which an
                // exact subject does not have, a named one that the result does not put back
                // drops (D2), and an unmatched cell never had.
                if entry.side == EntrySide::Result
                    && entry.anonymous_rest
                    && !other.is_some_and(|other| {
                        other
                            .spelling
                            .map_or(other.anonymous_rest, keeps_anonymous_rest)
                    })
                {
                    return Err((at, root(Refusal::RestMismatch)));
                }
                continue;
            };
            if other.is_some_and(|other| other.spelling.is_none()) {
                continue;
            }
            let lint = pair_located(
                self.form,
                entry.side,
                &entry.kind.own.layers,
                spelling,
                other.and_then(|other| other.spelling),
                entry.side == EntrySide::Subject && other.is_some(),
                &bound,
            )
            .map_err(|located| (at, located))?;
            lints.extend(lint.map(|lint| (at, lint)));
        }
        Ok(lints)
    }
}

/// The head of the record `name` labels in `spelling`, `name @ Head { .. }` or its fragment.
fn record_alias(spelling: &EntrySpelling, name: &str) -> Option<String> {
    match spelling {
        EntrySpelling::Alias(alias, pattern) if alias == name => match &**pattern {
            EntrySpelling::Record(record) | EntrySpelling::Fragment(record) => {
                Some(record.head.clone())
            }
            _ => None,
        },
        _ => inner(spelling)
            .into_iter()
            .find_map(|one| record_alias(one, name)),
    }
}

/// Whether `spelling` binds `name`: as a binder, an alias's name, or a named rest.
fn binds_name(spelling: &EntrySpelling, name: &str) -> bool {
    match spelling {
        EntrySpelling::Binder(binder) => binder == name,
        EntrySpelling::Alias(alias, _) if alias == name => true,
        _ => {
            let rest = sequence(spelling)
                .and_then(|seq| seq.rest.as_ref().map(|(rest, _)| rest))
                .or_else(|| map_entries(spelling).and_then(|map| map.rest.as_ref()));
            matches!(rest, Some(EntryRest::Named(rest)) if rest == name)
                || inner(spelling).into_iter().any(|one| binds_name(one, name))
        }
    }
}

#[cfg(test)]
mod tests {
    use krs_ir::cell_kind::{CellKind, GroupKind, Layer, Notation, Order};

    use super::{
        Bound, EntrySide, Lint, Refusal, Rewrite, Sentence, SentenceEntry, admit, collect_groups,
        inner, keeps_key, pair,
    };
    use crate::cell_entry::{EntryForm, EntryReading, EntrySpelling, RecordTail};

    /// Every refusal explains itself (design §2.7): its reason names the entry's cell and says
    /// more than its class's name, in every form, and no two refusals of the same class read
    /// alike unless they mean the same. [`Refusal::ALL`] lists every refusal at its
    /// discriminant, so a refusal added without a place there fails here, and `reason` matches
    /// every refusal, so one added without a reason does not compile.
    #[test]
    fn every_refusal_says_why_in_terms_of_its_entry() {
        for (at, refusal) in Refusal::ALL.iter().enumerate() {
            assert_eq!(
                *refusal as usize, at,
                "{refusal:?} stands at its discriminant"
            );
        }
        assert_eq!(
            Refusal::ALL.len(),
            Refusal::MapReadValueBinder as usize + 1,
            "the last refusal ends the list"
        );
        let group = GroupKind {
            name: "Job".to_owned(),
            children: vec![(
                "id".to_owned(),
                CellKind {
                    layers: vec![Layer::Leaf(Notation::Plain)],
                },
            )],
        };
        let kinds = [
            vec![Layer::Leaf(Notation::Plain)],
            vec![Layer::Computation],
            vec![Layer::Optional, Layer::Leaf(Notation::Plain)],
            vec![Layer::Instances(Order::List), Layer::Group(group.clone())],
            vec![Layer::Instances(Order::Map), Layer::Group(group)],
        ];
        for refusal in Refusal::ALL {
            for form in [
                EntryForm::Readable,
                EntryForm::Claim,
                EntryForm::Cells,
                EntryForm::Initializer,
            ] {
                for layers in &kinds {
                    let kind = super::EntryKind {
                        path: CellKind::default(),
                        own: CellKind {
                            layers: layers.clone(),
                        },
                    };
                    let reason = refusal.reason(form, "qcell", &kind, Some("Int"));
                    assert!(
                        reason.contains("`qcell`"),
                        "{refusal:?} names its cell: {reason}"
                    );
                    assert!(
                        !reason.contains(refusal.class()) && !reason.contains("is refused"),
                        "{refusal:?} says why, not its class: {reason}"
                    );
                    assert!(
                        reason.split_whitespace().count() >= 12,
                        "{refusal:?} explains itself: {reason}"
                    );
                }
            }
        }
    }

    /// A leaf of sort `KSequence` holds one term of that sort, so the computation's notations on
    /// it, `k::k![..]` in an initializer, `KCell(..)` in `cells!` and brackets in every form, are
    /// refused for what the leaf holds, not with the computation's own reason; a leaf of another
    /// sort is told it is no computation without the K clause, and a value on the computation
    /// keeps the computation's reason.
    #[test]
    fn the_computation_s_notation_on_a_leaf_of_sort_k_is_refused_for_what_the_leaf_holds() {
        let kind = |layers: Vec<Layer>| super::EntryKind {
            path: CellKind::default(),
            own: CellKind { layers },
        };
        let leaf = kind(vec![Layer::Leaf(Notation::Plain)]);
        let clause = "a leaf of sort `KSequence` is no computation: it holds one term of that sort";
        for (refusal, form) in [
            (Refusal::CellWrapper, EntryForm::Initializer),
            (Refusal::CellWrapper, EntryForm::Cells),
            (Refusal::BracketReading, EntryForm::Initializer),
            (Refusal::BracketReading, EntryForm::Readable),
            (Refusal::BracketReading, EntryForm::Claim),
            (Refusal::BracketReading, EntryForm::Cells),
        ] {
            let k = refusal.reason(form, "saved", &leaf, Some("KSequence"));
            assert!(k.contains(clause), "{refusal:?} in {form:?}: {k}");
            assert!(!k.contains("a value alone"), "{refusal:?} in {form:?}: {k}");
            let int = refusal.reason(form, "pc", &leaf, Some("Int"));
            assert!(
                !int.contains("is no computation:"),
                "{refusal:?} in {form:?}: {int}"
            );
        }
        let int = Refusal::CellWrapper.reason(EntryForm::Initializer, "pc", &leaf, Some("Int"));
        assert!(
            int.contains("which only a computation cell holds, and a leaf's initial value is one term of its sort")
                && !int.contains("a value alone"),
            "{int}"
        );
        let computation = Refusal::CellWrapper.reason(
            EntryForm::Initializer,
            "k",
            &kind(vec![Layer::Computation]),
            None,
        );
        assert!(
            computation.contains("a value alone is no computation"),
            "{computation}"
        );
    }

    /// The groups a test's configuration declares: those of the stack, and `Frame`.
    fn groups(stack: &[Layer]) -> Vec<GroupKind> {
        let mut groups = Vec::new();
        collect_groups(stack, &mut groups);
        collect_groups(&[frame()], &mut groups);
        groups
    }

    fn read(form: EntryForm, text: &str) -> EntrySpelling {
        EntryReading::new(form, &[])
            .value(text.parse().expect("the entry lexes"))
            .expect("the entry reads")
    }

    /// The bases `spelling`'s updates name, each with its update's head: the reading of a base
    /// the subject does not show as a record of the update's own constructor matched elsewhere.
    fn update_bases(spelling: &EntrySpelling, out: &mut Vec<(String, String)>) {
        if let EntrySpelling::Record(record) | EntrySpelling::Fragment(record) = spelling
            && let RecordTail::Update(base) = &record.tail
        {
            out.push((base.clone(), record.head.clone()));
        }
        for one in inner(spelling) {
            update_bases(one, out);
        }
    }

    fn judge(form: EntryForm, side: EntrySide, stack: &[Layer], text: &str) -> Result<(), Refusal> {
        admit(
            form,
            side,
            &[],
            stack,
            &read(form, text),
            &|_| None,
            &groups(stack),
        )
        .map(|_| ())
    }

    fn below(
        form: EntryForm,
        side: EntrySide,
        path: &[Layer],
        stack: &[Layer],
        text: &str,
    ) -> Result<(), Refusal> {
        admit(
            form,
            side,
            path,
            stack,
            &read(form, text),
            &|_| None,
            &groups(stack),
        )
        .map(|_| ())
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
        let mut bases = Vec::new();
        update_bases(&spelling, &mut bases);
        let bound = |name: &str| {
            Some(
                bases
                    .iter()
                    .find(|(base, _)| base == name)
                    .map_or(Bound::Value, |(_, head)| Bound::Record(head.clone())),
            )
        };
        admit(
            form,
            EntrySide::Result,
            &[],
            stack,
            &spelling,
            &bound,
            &groups(stack),
        )?;
        let subject = subject.map(|text| read(form, text));
        pair(
            form,
            EntrySide::Result,
            stack,
            &spelling,
            subject.as_ref(),
            false,
            &bound,
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
    fn a_bare_rest_in_a_built_record_is_refused_where_it_leaves_a_field_open() {
        let readable = EntryForm::Readable;
        let open = Err(Refusal::OpenRecordOutsidePattern);
        let set = [Layer::Leaf(Notation::Set)];
        let job = [Layer::Group(GroupKind {
            name: "Job".to_owned(),
            children: vec![("payload".to_owned(), int())],
        })];
        // The record of a group that exists.
        let over = Some("Frame { ret: y, .. }");
        assert_eq!(
            result(readable, &[frame()], "Frame { ret: x, .. }", over),
            open
        );
        assert_eq!(
            result(readable, &[frame()], "Frame { ret: x, aux: y, .. }", over),
            Ok(None)
        );
        assert_eq!(
            result(
                EntryForm::Cells,
                &[frame()],
                "k::fragment![crate::Frame { ret: x, aux: y, .. }]",
                Some("k::fragment![crate::Frame { ret: y, .. }]"),
            ),
            Ok(None)
        );
        assert_eq!(
            result(readable, &job, "Job { payload: x, .. }", None),
            Ok(None)
        );
        // A term, on a leaf and where the missing layer's advice makes it one.
        assert_eq!(
            result(readable, &set, "Frame { ret: x, .. }", Some("old")),
            open
        );
        assert_eq!(
            result(readable, &set, "Frame { ret: x, aux: y, .. }", Some("old")),
            Ok(None)
        );
        let code = [Layer::Computation];
        assert_eq!(result(readable, &code, "Frame { ret: x, .. }", None), open);
        assert_eq!(
            result(readable, &code, "Frame { ret: x, aux: y, .. }", None),
            Err(Refusal::CellWrapper)
        );
        // A head no group names.
        assert_eq!(result(readable, &set, "Q { a: x, .. }", Some("old")), open);
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
    }

    #[test]
    fn an_update_whose_label_the_subject_does_not_show_is_created_or_has_no_base() {
        let readable = EntryForm::Readable;
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
        // An update whose label no subject instance has is no in-place rewrite: of a value the
        // sentence binds elsewhere, it creates an instance, whose `..` keeps nothing; of a label
        // bound nowhere, it has no base.
        assert_eq!(
            result(
                readable,
                &threads,
                "[T { k: [x, ..], ..me }, ..]",
                Some("[..]")
            ),
            Err(Refusal::RestMismatch)
        );
        assert_eq!(
            result(readable, &threads, "[T { k: [x], ..me }, ..]", Some("[..]")),
            Ok(None)
        );
        let spelling = read(readable, "[T { k: [x], ..me }, ..]");
        let subject = read(readable, "[..]");
        assert_eq!(
            pair(
                readable,
                EntrySide::Result,
                &threads,
                &spelling,
                Some(&subject),
                false,
                &|name| (name != "me").then_some(Bound::Value),
            ),
            Err(Refusal::RecordUpdateBase)
        );
        // `..me` takes the fields of a record of the update's own constructor: a base bound
        // elsewhere to no record (a list element), or to a record of another constructor, is
        // none.
        for bound in [Bound::Value, Bound::Record("Job".to_owned())] {
            assert_eq!(
                pair(
                    readable,
                    EntrySide::Result,
                    &threads,
                    &spelling,
                    Some(&subject),
                    false,
                    &|_| Some(bound.clone()),
                ),
                Err(Refusal::RecordUpdateBase)
            );
        }
        assert_eq!(
            pair(
                readable,
                EntrySide::Result,
                &threads,
                &spelling,
                Some(&subject),
                false,
                &|_| Some(Bound::Record("T".to_owned())),
            ),
            Ok(None)
        );
    }

    #[test]
    fn a_cells_update_rewrites_in_place_only_an_instance_its_subject_labels() {
        let cells = EntryForm::Cells;
        let remainder = Err(Refusal::RecordRemainderInCellsTerm);
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
        // `..me` of the subject instance `me @` labels is the update `cells!` has, in place.
        assert_eq!(
            result(
                cells,
                &threads,
                "[k::fragment![crate::T { n: x, ..me }], ..]",
                Some("[me @ k::fragment![crate::T { n: y, .. }], ..]")
            ),
            Ok(None)
        );
        // A label no subject instance of the cell has takes the record's other children from a
        // record matched elsewhere, which the reference notation names instead.
        assert_eq!(
            result(
                cells,
                &threads,
                "[k::fragment![crate::T { n: x, ..me }], ..]",
                Some("[..]")
            ),
            remainder
        );
        assert_eq!(
            result(
                cells,
                &threads,
                "[k::fragment![crate::T { n: x, ..me }]]",
                None
            ),
            remainder
        );
        // The record's children are paired first, against the instance it would create; a base
        // that is no record of the update's constructor is none at all.
        assert_eq!(
            result(
                cells,
                &threads,
                "[k::fragment![crate::T { k: [x, ..], ..me }], ..]",
                Some("[..]")
            ),
            Err(Refusal::RestMismatch)
        );
        let spelling = read(cells, "[k::fragment![crate::T { n: x, ..me }], ..]");
        let subject = read(cells, "[..]");
        assert_eq!(
            pair(
                cells,
                EntrySide::Result,
                &threads,
                &spelling,
                Some(&subject),
                false,
                &|_| Some(Bound::Value),
            ),
            Err(Refusal::RecordUpdateBase)
        );
        // A group record's `..base` takes its other children from another record, wherever the
        // base is matched.
        let g = [Layer::Group(GroupKind {
            name: "G".to_owned(),
            children: vec![("a".to_owned(), int()), ("b".to_owned(), int())],
        })];
        for subject in [
            None,
            Some("_"),
            Some("saved @ k::fragment![crate::G { a: y, .. }]"),
        ] {
            assert_eq!(
                result(
                    cells,
                    &g,
                    "k::fragment![crate::G { a: x, ..saved }]",
                    subject
                ),
                remainder
            );
        }
        // Readable keeps both: they are readable-record notation.
        let readable = EntryForm::Readable;
        assert_eq!(
            result(readable, &threads, "[T { n: x, ..me }, ..]", Some("[..]")),
            Ok(None)
        );
        assert_eq!(
            result(readable, &g, "G { a: x, ..saved }", Some("_")),
            Ok(None)
        );
    }

    /// A subject's `None` on a `?` child of a group or instance record tests the child absent,
    /// which K does only by creating it: the result's same child must be present.
    #[test]
    fn a_child_absence_test_needs_the_result_to_create_the_child() {
        let readable = EntryForm::Readable;
        let optional = CellKind {
            layers: vec![Layer::Optional, Layer::Leaf(Notation::Plain)],
        };
        let group = GroupKind {
            name: "O".to_owned(),
            children: vec![("o".to_owned(), optional), ("n".to_owned(), int())],
        };
        let accounts = [Layer::Instances(Order::Map), Layer::Group(group.clone())];
        let one = [Layer::Group(group)];
        let subject = |stack: &[Layer], text: &str, result: Option<&str>| {
            let result = result.map(|text| read(readable, text));
            pair(
                readable,
                EntrySide::Subject,
                stack,
                &read(readable, text),
                result.as_ref(),
                result.is_some(),
                &|_| None,
            )
        };
        let absent = Err(Refusal::AbsenceTestWithoutCreation);
        assert_eq!(subject(&one, "O { o: None, n: x }", None), absent);
        assert_eq!(
            subject(&one, "O { o: None, n: x }", Some("O { o: None, n: x }")),
            absent
        );
        assert_eq!(
            subject(&one, "O { o: None, n: x }", Some("O { o: Some(1), n: x }")),
            Ok(None)
        );
        assert_eq!(
            subject(&accounts, "{ O { n: x, o: None }, .. }", None),
            absent
        );
        // An unlabelled instance is rewritten by no result record.
        assert_eq!(
            subject(
                &accounts,
                "{ O { n: x, o: None }, .. }",
                Some("{ O { n: x, o: Some(1) }, .. }")
            ),
            absent
        );
        assert_eq!(
            subject(
                &accounts,
                "{ me @ O { n: x, o: None }, .. }",
                Some("{ O { o: Some(1), ..me }, .. }")
            ),
            Ok(None)
        );
        assert_eq!(
            subject(
                &accounts,
                "{ me @ O { n: x, o: None }, .. }",
                Some("{ O { n: 1, ..me }, .. }")
            ),
            absent
        );
        // At the cell's own root as at a child: a result `None` over a subject `None` creates
        // nothing.
        let root = [Layer::Optional, Layer::Leaf(Notation::Plain)];
        assert_eq!(subject(&root, "None", Some("None")), absent);
        assert_eq!(subject(&root, "None", Some("Some(1)")), Ok(None));
    }
    #[test]
    fn a_written_key_is_kept_only_as_the_matched_binder_or_literal() {
        let binder = |name: &str| EntrySpelling::Binder(name.to_owned());
        let literal = |text: &str| EntrySpelling::Literal(text.to_owned());
        let alias = EntrySpelling::Alias("me".to_owned(), Box::new(literal("0")));
        assert!(keeps_key(&binder("me"), Some(&binder("me"))));
        assert!(keeps_key(&binder("me"), Some(&alias)));
        assert!(keeps_key(&literal("0"), Some(&literal("0"))));
        assert!(keeps_key(&literal("0"), Some(&alias)));
        assert!(!keeps_key(&binder("me"), Some(&binder("other"))));
        assert!(!keeps_key(&literal("1"), Some(&literal("0"))));
        assert!(!keeps_key(&literal("0"), Some(&binder("me"))));
        assert!(!keeps_key(
            &EntrySpelling::Call(vec![binder("me")]),
            Some(&binder("me"))
        ));
        // A key the subject does not name is no key it matched.
        assert!(!keeps_key(&binder("me"), None));
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
    fn an_update_writing_the_literal_its_subject_matched_keeps_the_key() {
        let (readable, cells) = (EntryForm::Readable, EntryForm::Cells);
        let map = [
            Layer::Instances(Order::Map),
            Layer::Group(GroupKind {
                name: "A".to_owned(),
                children: vec![("id".to_owned(), int()), ("bal".to_owned(), int())],
            }),
        ];
        let refused = Err(Refusal::MapCollectionKey);
        // The same literal the subject matched is provably the same key; another literal is
        // another key.
        let five = Some("{ me @ A { id: 5, .. }, .. }");
        assert_eq!(
            result(readable, &map, "{ A { id: 5, ..me }, .. }", five),
            Ok(None)
        );
        assert_eq!(
            result(
                readable,
                &map,
                "{ A { id: 5, ..me }, .. }",
                Some("{ me @ A { id: k @ 5, .. }, .. }")
            ),
            Ok(None)
        );
        assert_eq!(
            result(
                cells,
                &map,
                "{ k::fragment![crate::A { id: 5, ..me }], .. }",
                Some("{ me @ k::fragment![crate::A { id: 5, .. }], .. }")
            ),
            Ok(None)
        );
        assert_eq!(
            result(readable, &map, "{ A { id: 6, ..me }, .. }", five),
            refused
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
            admit(init, side, &[], stack, &spelling, &|_| None, &[]).map(|_| ())
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
            admit(
                init,
                side,
                &[],
                &[Layer::Computation],
                &spliced,
                &|_| None,
                &[]
            )
            .map(|_| ()),
            Err(Refusal::InitializerRemainder)
        );
        let open = reading
            .value("k::k![Cmd::Go(), ..]".parse().expect("lexes"))
            .expect("reads");
        assert_eq!(
            admit(
                init,
                side,
                &[],
                &[Layer::Computation],
                &open,
                &|_| None,
                &[]
            )
            .map(|_| ()),
            Err(Refusal::InitializerRemainder)
        );
    }

    #[test]
    fn a_map_read_with_a_rest_is_refused_in_a_result_at_every_content_root() {
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
                &[Layer::Instances(Order::Set), obj.clone()],
                "{ Obj { key: 1, m: { 1 -> 2, .. } }, .. }"
            ),
            Err(Refusal::MapReadInResult)
        );
        // An instance record's child without a rest is the exact map, which a result builds.
        assert_eq!(
            judge(
                readable,
                EntrySide::Result,
                &[Layer::Instances(Order::Set), obj],
                "{ Obj { key: 1, m: { 1 -> 2 } }, .. }"
            ),
            Ok(())
        );
        // A group record's child is lowered by the record's own route, which has no map read
        // on a result's side either (the field's value is the child's content root).
        let m = Layer::Group(GroupKind {
            name: "M".to_owned(),
            children: vec![
                (
                    "mm".to_owned(),
                    CellKind {
                        layers: vec![Layer::Leaf(Notation::Map)],
                    },
                ),
                ("mn".to_owned(), int()),
            ],
        });
        assert_eq!(
            judge(
                readable,
                EntrySide::Result,
                &[m],
                "M { mm: { y -> x, .. }, mn: 0 }"
            ),
            Err(Refusal::MapReadInResult)
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
                &|_| None,
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

    #[test]
    fn an_item_after_a_cons_lists_rest_is_refused_inside_its_mark() {
        let (readable, cells) = (EntryForm::Readable, EntryForm::Cells);
        let cons = [Layer::Leaf(Notation::Cons)];
        let list = [Layer::Leaf(Notation::List)];
        for text in ["[.., x]", "[x, .., y]"] {
            assert_eq!(
                judge(readable, EntrySide::Subject, &cons, text),
                Err(Refusal::ConsListBackItem)
            );
            assert_eq!(judge(readable, EntrySide::Subject, &list, text), Ok(()));
        }
        assert_eq!(
            judge(
                cells,
                EntrySide::Subject,
                &cons,
                "k::configuration::Cell([.., x])"
            ),
            Err(Refusal::ConsListBackItem)
        );
        assert_eq!(
            below(
                readable,
                EntrySide::Subject,
                &[Layer::Optional],
                &cons,
                "[.., x]"
            ),
            Err(Refusal::ConsListBackItem)
        );
        assert_eq!(
            judge(readable, EntrySide::Subject, &cons, "[x, ..]"),
            Ok(())
        );
    }

    #[test]
    fn an_item_after_the_computations_rest_is_refused_in_every_form() {
        let computation = [Layer::Computation];
        for (form, text) in [
            (EntryForm::Readable, "[.., x]"),
            (EntryForm::Readable, "[x, .., y]"),
            (EntryForm::Claim, "[.., x]"),
            (EntryForm::Cells, "k::configuration::KCell(.., x)"),
            (EntryForm::Cells, "k::configuration::KCell(x, .., y)"),
        ] {
            for side in [EntrySide::Subject, EntrySide::Result] {
                assert_eq!(
                    judge(form, side, &computation, text),
                    Err(Refusal::ComputationBackItem),
                    "{form:?} {side:?} {text}"
                );
            }
        }
        assert_eq!(
            judge(
                EntryForm::Cells,
                EntrySide::Subject,
                &computation,
                "k::configuration::KCell(x, ..)"
            ),
            Ok(())
        );
        assert_eq!(
            below(
                EntryForm::Cells,
                EntrySide::Subject,
                &[Layer::Optional],
                &computation,
                "k::configuration::KCell(.., x)"
            ),
            Err(Refusal::ComputationBackItem)
        );
    }

    /// A name or `_` alone in an instance list is one whole instance, in every collection kind:
    /// the front or back one of a List, any one of a Set or Map, as a record labelled with the
    /// name names it. The table admits it; any other value names no instance of an unordered
    /// collection, whose instance its record chooses.
    #[test]
    fn a_name_or_wildcard_item_is_one_whole_instance_of_any_collection() {
        let readable = EntryForm::Readable;
        for order in [Order::Set, Order::Map] {
            let stack = [Layer::Instances(order), frame()];
            for text in ["{ x, .. }", "{ _, .. }", "{ x }"] {
                assert_eq!(judge(readable, EntrySide::Subject, &stack, text), Ok(()));
            }
            assert_eq!(
                judge(readable, EntrySide::Subject, &stack, "{ 0, .. }"),
                Err(Refusal::InstanceListShape)
            );
        }
        let list = [Layer::Instances(Order::List), frame()];
        for text in ["[x, ..]", "[_, ..]", "[x]", "[.., x]"] {
            assert_eq!(judge(readable, EntrySide::Subject, &list, text), Ok(()));
        }
    }

    #[test]
    fn brackets_on_an_unordered_collection_are_its_instances_of_the_wrong_order() {
        let readable = EntryForm::Readable;
        for order in [Order::Set, Order::Map] {
            let stack = [Layer::Instances(order), frame()];
            for text in ["[x, ..]", "[..]", "[Frame { ret: x, .. }, ..]"] {
                assert_eq!(
                    judge(readable, EntrySide::Subject, &stack, text),
                    Err(Refusal::InstanceListShape)
                );
            }
        }
        assert_eq!(
            judge(readable, EntrySide::Subject, &[frame()], "[x, ..]"),
            Err(Refusal::BracketReading)
        );
    }

    #[test]
    fn a_missing_layer_is_named_only_where_its_inside_passes() {
        let (readable, cells) = (EntryForm::Readable, EntryForm::Cells);
        let optional_int = [Layer::Optional, Layer::Leaf(Notation::Plain)];
        let optional_frame = [Layer::Optional, frame()];
        let set = [Layer::Instances(Order::Set), frame()];
        assert_eq!(
            judge(
                cells,
                EntrySide::Subject,
                &optional_int,
                "k::configuration::Cell([x, ..])"
            ),
            Err(Refusal::BracketReading)
        );
        assert_eq!(
            judge(
                cells,
                EntrySide::Subject,
                &optional_int,
                "k::configuration::Cell(x)"
            ),
            Err(Refusal::OptionalWithoutPresence)
        );
        assert_eq!(
            judge(cells, EntrySide::Subject, &optional_int, "x"),
            Err(Refusal::OptionalWithoutPresence)
        );
        assert_eq!(
            judge(
                readable,
                EntrySide::Subject,
                &optional_frame,
                "Frame { ret: x }"
            ),
            Err(Refusal::RecordMissingChildren)
        );
        assert_eq!(
            judge(readable, EntrySide::Subject, &set, "Frame { ret: x }"),
            Err(Refusal::RecordMissingChildren)
        );
        assert_eq!(
            judge(readable, EntrySide::Subject, &set, "x"),
            Err(Refusal::CollectionWithoutInstances)
        );
    }

    /// P4 over a sentence: each step runs over every entry before the next, and within a step
    /// the first refusal in source order is the sentence's. A path refusal is the kind step's.
    #[test]
    fn a_sentence_is_judged_step_by_step_over_every_entry() {
        let form = EntryForm::Cells;
        let leaf = |path: Vec<Layer>| super::EntryKind {
            path: CellKind { layers: path },
            own: int(),
        };
        let optional = super::EntryKind {
            path: CellKind { layers: vec![] },
            own: CellKind {
                layers: vec![Layer::Optional, Layer::Leaf(Notation::Plain)],
            },
        };
        let (plain, below) = (leaf(vec![]), leaf(vec![Layer::Optional]));
        let judge = |written: &[(EntrySide, &str, &super::EntryKind, &str)]| {
            let spellings = written
                .iter()
                .map(|(.., text)| read(form, text))
                .collect::<Vec<_>>();
            let entries = written
                .iter()
                .zip(&spellings)
                .map(|((side, cell, kind, _), spelling)| SentenceEntry {
                    side: *side,
                    cell: *cell,
                    kind,
                    spelling: Some(spelling),
                    anonymous_rest: false,
                })
                .collect::<Vec<_>>();
            Sentence {
                form,
                entries: &entries,
                rewrite: if written.iter().any(|(side, ..)| *side == EntrySide::Result) {
                    Rewrite::Result
                } else {
                    Rewrite::InPlace
                },
                parameters: &["x".to_owned()],
                groups: &groups(&[]),
            }
            .judge()
            .map(|_| ())
        };
        let (s, r) = (EntrySide::Subject, EntrySide::Result);
        // The pairing's absence test waits for the path refusal, met later in source order.
        assert_eq!(
            judge(&[
                (s, "c", &optional, "None"),
                (s, "p", &below, "k::configuration::Cell(x)"),
            ]),
            Err((1, Refusal::BelowOptionalAncestor))
        );
        // A path refusal and a cell's own kind are one step: the first in source order.
        assert_eq!(
            judge(&[
                (s, "p", &below, "k::configuration::Cell(x)"),
                (r, "q", &plain, "x"),
            ]),
            Err((0, Refusal::BelowOptionalAncestor))
        );
        assert_eq!(
            judge(&[
                (s, "q", &plain, "x"),
                (s, "p", &below, "k::configuration::Cell(x)"),
            ]),
            Err((0, Refusal::CellWrapper))
        );
        // The form of every entry comes before any kind.
        assert_eq!(
            judge(&[
                (s, "p", &below, "k::configuration::Cell(x)"),
                (r, "q", &plain, "_"),
            ]),
            Err((1, Refusal::WildcardOutsidePattern))
        );
        // Every entry's form and kind admitted: the pairing runs (a `?` result over a cell the
        // subject does not match).
        assert_eq!(
            judge(&[
                (s, "q", &plain, "k::configuration::Cell(_)"),
                (r, "c", &optional, "Some(k::configuration::Cell(x))")
            ]),
            Err((1, Refusal::UnmatchedOptionalResult))
        );
    }

    /// A kept pattern's sentence ([`Rewrite::Kept`]) over the leaf `pc`, the leaf `apc` below a
    /// Map collection, the `?` leaf `counter`, the Map collection `account` of `Acct { id, note }`
    /// (`note` a `?` leaf) and the List collection `job`, judged step by step.
    fn kept_sentence(
        as_rule: bool,
        written: &[(&str, &str)],
    ) -> Result<Vec<(usize, Lint)>, (usize, Refusal)> {
        let form = EntryForm::Cells;
        let kind = |path: Vec<Layer>, own: Vec<Layer>| super::EntryKind {
            path: CellKind { layers: path },
            own: CellKind { layers: own },
        };
        let optional = || vec![Layer::Optional, Layer::Leaf(Notation::Plain)];
        let acct = Layer::Group(GroupKind {
            name: "Acct".to_owned(),
            children: vec![
                ("id".to_owned(), int()),
                ("note".to_owned(), CellKind { layers: optional() }),
            ],
        });
        let job = Layer::Group(GroupKind {
            name: "Job".to_owned(),
            children: vec![("payload".to_owned(), int())],
        });
        let all = groups(&[acct.clone(), job.clone()]);
        let kinds = [
            ("pc", kind(vec![], int().layers)),
            (
                "apc",
                kind(vec![Layer::Instances(Order::Map)], int().layers),
            ),
            ("counter", kind(vec![], optional())),
            (
                "account",
                kind(vec![], vec![Layer::Instances(Order::Map), acct]),
            ),
            (
                "job",
                kind(vec![], vec![Layer::Instances(Order::List), job]),
            ),
        ];
        let spellings = written
            .iter()
            .map(|(_, text)| read(form, text))
            .collect::<Vec<_>>();
        let entries = written
            .iter()
            .zip(&spellings)
            .map(|((cell, _), spelling)| SentenceEntry {
                side: EntrySide::Subject,
                cell: *cell,
                kind: &kinds
                    .iter()
                    .find(|(name, _)| name == cell)
                    .expect("a declared cell")
                    .1,
                spelling: Some(spelling),
                anonymous_rest: false,
            })
            .collect::<Vec<_>>();
        Sentence {
            form,
            entries: &entries,
            rewrite: Rewrite::Kept { as_rule },
            parameters: &["x".to_owned()],
            groups: &all,
        }
        .judge()
    }

    /// A pattern a sentence keeps as it matched it (a function context, a context alias, a
    /// context) is judged by form and kind with the path, then paired as a rule with that
    /// pattern on both sides: S1 (b) refuses an entry below a `*` ancestor there as in a rule; a
    /// `None` creates nothing, at the cell's root and below it (P5); an entry that constrains
    /// nothing owes the lint; a List collection's back instance kept in place meets the rule
    /// lowering's limit in a context only, the one kept pattern lowered as a rule's.
    #[test]
    fn a_kept_pattern_is_paired_as_a_rule_with_that_pattern_on_both_sides() {
        let absent = Refusal::AbsenceTestWithoutCreation;
        for as_rule in [false, true] {
            let judge = |written: &[(&str, &str)]| kept_sentence(as_rule, written);
            assert_eq!(
                judge(&[
                    ("pc", "k::configuration::Cell(x)"),
                    ("apc", "k::configuration::Cell(x)"),
                ]),
                Err((1, Refusal::BelowCollectionAncestor))
            );
            assert_eq!(
                judge(&[("pc", "k::configuration::Cell(_)")]),
                Ok(vec![(0, Lint::NoEffectEntry)])
            );
            assert_eq!(
                judge(&[("counter", "Some(k::configuration::Cell(x))")]),
                Ok(Vec::new())
            );
            assert_eq!(judge(&[("counter", "None")]), Err((0, absent)));
            assert_eq!(
                judge(&[(
                    "account",
                    "{ k::fragment![crate::Acct { id: x, note: None }], .. }"
                )]),
                Err((0, absent))
            );
            assert_eq!(
                judge(&[("job", "[k::fragment![crate::Job { payload: x }], ..]")]),
                Ok(Vec::new())
            );
        }
        let back = [("job", "[.., k::fragment![crate::Job { payload: x }]]")];
        assert_eq!(kept_sentence(false, &back), Ok(Vec::new()));
        assert_eq!(kept_sentence(true, &back), Err((0, Refusal::ListBackKept)));
    }

    /// A sentence over the List collection `job` (instances of `Job { payload }`) and the leaf
    /// `pc`, judged step by step.
    fn list_sentence(
        form: EntryForm,
        written: &[(EntrySide, &str, &str)],
    ) -> Result<(), (usize, Refusal)> {
        let job = super::EntryKind {
            path: CellKind { layers: vec![] },
            own: CellKind {
                layers: vec![
                    Layer::Instances(Order::List),
                    Layer::Group(GroupKind {
                        name: "Job".to_owned(),
                        children: vec![("payload".to_owned(), int())],
                    }),
                ],
            },
        };
        let plain = super::EntryKind {
            path: CellKind { layers: vec![] },
            own: int(),
        };
        let spellings = written
            .iter()
            .map(|(.., text)| read(form, text))
            .collect::<Vec<_>>();
        let entries = written
            .iter()
            .zip(&spellings)
            .map(|((side, cell, _), spelling)| SentenceEntry {
                side: *side,
                cell: *cell,
                kind: if *cell == "job" { &job } else { &plain },
                spelling: Some(spelling),
                anonymous_rest: false,
            })
            .collect::<Vec<_>>();
        Sentence {
            form,
            entries: &entries,
            rewrite: if written.iter().any(|(side, ..)| *side == EntrySide::Result) {
                Rewrite::Result
            } else {
                Rewrite::InPlace
            },
            parameters: &["v".to_owned(), "x".to_owned()],
            groups: &groups(&job.own.layers),
        }
        .judge()
        .map(|_| ())
    }

    /// A List collection's back instance is created or removed, and never kept in place: the
    /// subject's and the result's items after the rest are judged together at the pairing, where
    /// the lowering refuses a kept back instance (at the subject's entry).
    #[test]
    fn a_list_collections_back_instance_is_created_or_removed_never_kept_in_place() {
        let (s, r) = (EntrySide::Subject, EntrySide::Result);
        let readable = EntryForm::Readable;
        // Created at the back (`enqueue`), removed from it (`pop`): one end, nothing kept.
        assert_eq!(
            list_sentence(
                readable,
                &[
                    (s, "job", "[..]"),
                    (r, "job", "[.., Job { payload: v, .. }]")
                ]
            ),
            Ok(())
        );
        assert_eq!(
            list_sentence(
                readable,
                &[
                    (s, "job", "[.., last @ Job { payload: p, .. }]"),
                    (r, "job", "[..]")
                ]
            ),
            Ok(())
        );
        assert_eq!(
            list_sentence(readable, &[(s, "job", "[.., x]"), (r, "job", "[..]")]),
            Ok(())
        );
        // Kept in place: the result leaves the cell out, or updates the instance by its label.
        assert_eq!(
            list_sentence(
                readable,
                &[(s, "job", "[.., Job { payload: p, .. }]"), (r, "pc", "x")]
            ),
            Err((0, Refusal::ListBackKept))
        );
        assert_eq!(
            list_sentence(readable, &[(s, "job", "[.., x]"), (r, "pc", "x")]),
            Err((0, Refusal::ListBackKept))
        );
        assert_eq!(
            list_sentence(
                readable,
                &[
                    (s, "job", "[.., last @ Job { payload: p, .. }]"),
                    (r, "job", "[.., Job { payload: 1, ..last }]")
                ]
            ),
            Err((0, Refusal::ListBackKept))
        );
        // A single-body rule keeps every instance it names.
        assert_eq!(
            list_sentence(readable, &[(s, "job", "[.., Job { payload: p, .. }]")]),
            Err((0, Refusal::ListBackKept))
        );
        assert_eq!(
            list_sentence(readable, &[(s, "job", "[Job { payload: p, .. }, ..]")]),
            Ok(())
        );
    }

    /// A List collection's rule changes one end: the subject's and the result's items before
    /// the rest and after it are judged together at the pairing, refused at the entry to split.
    #[test]
    fn a_list_collections_rule_changes_one_end() {
        let (s, r) = (EntrySide::Subject, EntrySide::Result);
        let readable = EntryForm::Readable;
        // Both ends: at the subject where it names both, else at the result.
        assert_eq!(
            list_sentence(
                readable,
                &[
                    (s, "job", "[Job { payload: p, .. }, ..]"),
                    (r, "job", "[.., Job { payload: 0, .. }]")
                ]
            ),
            Err((1, Refusal::ListBothEnds))
        );
        assert_eq!(
            list_sentence(
                readable,
                &[
                    (
                        s,
                        "job",
                        "[Job { payload: p, .. }, .., Job { payload: q, .. }]"
                    ),
                    (r, "job", "[..]")
                ]
            ),
            Err((0, Refusal::ListBothEnds))
        );
        // The `cells!` spellings queue's expansion prints.
        let cells = EntryForm::Cells;
        assert_eq!(
            list_sentence(
                cells,
                &[
                    (s, "job", "[instances0 @ ..]"),
                    (
                        r,
                        "job",
                        "[..instances0, k::fragment![crate::Job { payload: v, .. }]]"
                    )
                ]
            ),
            Ok(())
        );
        assert_eq!(
            list_sentence(
                cells,
                &[
                    (
                        s,
                        "job",
                        "[instances0 @ .., last @ k::fragment![crate::Job { payload: p, .. }]]"
                    ),
                    (r, "job", "[..instances0]")
                ]
            ),
            Ok(())
        );
    }
}

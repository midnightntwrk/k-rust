//! The twin relation as a generated check (TWINORACLE): each spelling of a child, generated
//! beside its *twin*, the same spelling at a top-level cell of the same kind and sort, in the
//! same form and on the same side ([`Family::ChildTwins`], [`Base::ChildTwins`]).
//!
//! An instance's child, and a group record's child, is a cell (`docs-site/src/pages/reference/
//! language.mdx`, "Each child of a record there is that child cell's entry, read by the child's
//! declared kind exactly as if the child were written as its own cell", and "An instance child
//! is a cell, so its content is read as that cell's would be outside every instance"): so a
//! child's spelling means what the same spelling means at a cell of the child's kind and sort
//! outside every instance and group. The twin is that cell's case, and the relation is the
//! oracle: a child case is expected what its twin is ([`twin_of`], [`super::table`]), accepted
//! where the twin is, with the twin's K read through the child's place ([`projection`]), and
//! refused where the twin is, with its class. It states agreement, not a verdict: the twin's
//! own outcome is the table's, stated from what the spelling denotes at a top-level cell, and a
//! child that disagrees with it is a red that the triage decides by meaning.
//!
//! **Places.** A child of an instance of a List collection (`queue.job` of `J`), of a Map
//! collection (`bank.acct` of `A`, keyed by `aid`), of a fixed group (`gg` of `Gg`) and of a
//! present `?` group (`og` of `Og`); each holds a child of every kind ([`Kind`]), and so does the
//! top level, whose cells are the twins (`tk`, `tl`, `tm`, `te`, `tn`). A cell's name is its
//! place's letter and its kind's: `jl` is the List child of a List collection's instance.
//!
//! **Forms.** A readable rule, a `cells!` rule and a `cells!` claim. A child of a readable record
//! is written as its twin is (`jl: [y, ..]` and `tl: [y, ..]`), a `cells!` record's child bare
//! where its twin wraps the content (`jl: [y, ..]` and `tl: k::configuration::Cell([y, ..])`, a
//! computation's items in `KCell(..)`: `jk: [Cmd::Go(), ..]` and `jk: k::k![Cmd::Go(), ..]` are
//! both `tk: k::configuration::KCell(Cmd::Go(), ..)`).
//!
//! **Sides.** A row writes the child's subject, its result, or both; the record around it is
//! the same on each side and matches the instance or group with `..`, so the row's spelling is
//! the case's one point of interest. A result over a subject that leaves the child in the
//! record's `..` is twinned with a result over a top-level cell the subject does not name.
//!
//! **TWINWIDE.** The family also writes `_`, a bare binder and an alias at each kind; each kind's
//! representative rows ([`Reach::Core`]) at a `?` leaf's present content (`Some(..)`), a Set
//! collection's instance child and a group child inside a List instance's child
//! ([`Place::widened`]); and the sentences [`Form::writes`] places: a readable claim, a context, a
//! context alias and a function context (at the top and a fixed group's child named through its
//! struct, [`Place::GroupPath`]), and a single-body rule's rewrite of a cell's whole content.
//!
//! **Stated differences** ([`stated`]): where the child genuinely cannot mean what its twin
//! means, by a limit the documentation or a refusal states, the relation does not apply, and the
//! child case has an entry of its own. Each is a predicate with its reason.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::sync::LazyLock;

use super::k7::{K7, SkipKind};
use super::{Base, BaseText, Case, CaseSpec, Command, Family, ItemBuilder, Packaging, Side};

/// A child's kind, by its declaration: the computation (`KSequence`), leaves of the builtin
/// `List`, `Map`, `Set` and `Int`, and a leaf of sort `KSequence`
/// (`k::configuration::Cell<KSequence>`), where a remainder is saved whole (`Cell(tail)`). A
/// declaration holding that leaf writes every leaf with its wrapper, so the base does
/// ([`base`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kind {
    /// A computation cell.
    Computation,
    /// A builtin `List` leaf.
    List,
    /// A builtin `Map` leaf.
    Map,
    /// A builtin `Set` leaf.
    Set,
    /// An `Int` leaf.
    Int,
    /// A leaf of sort `KSequence`, which holds one term of that sort.
    SequenceLeaf,
}

impl Kind {
    /// Every kind, in declaration order.
    pub const ALL: [Self; 6] = [
        Self::Computation,
        Self::List,
        Self::Map,
        Self::Set,
        Self::Int,
        Self::SequenceLeaf,
    ];

    /// The kind's ID segment.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Computation => "k",
            Self::List => "list",
            Self::Map => "map",
            Self::Set => "set",
            Self::Int => "int",
            Self::SequenceLeaf => "k-leaf",
        }
    }

    /// The kind's letter in its cells' names.
    const fn letter(self) -> &'static str {
        match self {
            Self::Computation => "k",
            Self::List => "l",
            Self::Map => "m",
            Self::Set => "e",
            Self::Int => "n",
            Self::SequenceLeaf => "q",
        }
    }

    /// The child's declared type, with its wrapper: a declaration holding a leaf of sort
    /// `KSequence` writes every leaf so.
    const fn type_name(self) -> &'static str {
        match self {
            Self::Computation => "k::configuration::KCell<KSequence>",
            Self::List => "k::configuration::Cell<List>",
            Self::Map => "k::configuration::Cell<Map>",
            Self::Set => "k::configuration::Cell<Set>",
            Self::Int => "k::configuration::Cell<Int>",
            Self::SequenceLeaf => "k::configuration::Cell<KSequence>",
        }
    }

    /// The base initializer's value of a cell of the kind.
    const fn default(self) -> &'static str {
        match self {
            Self::List => "list::empty()",
            Self::Map => "k::map![]",
            Self::Set => "set::empty()",
            Self::Int => "0",
            Self::Computation | Self::SequenceLeaf => "k::k![]",
        }
    }
}

/// Where a child stands: the top level (the twins), or a child of a List collection's instance,
/// a Map collection's instance, a fixed group or a present `?` group.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Place {
    /// A top-level cell: the twin.
    Top,
    /// A child of `queue.job`'s instances (`J`).
    ListChild,
    /// A child of `bank.acct`'s instances (`A`, keyed by `aid`).
    MapChild,
    /// A child of the fixed group `gg` (`Gg`).
    GroupChild,
    /// A child of the `?` group `og` (`Og`), present on the side that writes it.
    OptChild,
    /// The present content of a top-level `?` leaf (`pl`), `Some(..)` around the spelling
    /// (TWINWIDE): "`Some(..)` holds the present cell's content as a record's entry does".
    OptLeaf,
    /// A child of `club.memb`'s instances (`E`, a Set collection) (TWINWIDE).
    SetChild,
    /// A child of the fixed group `jh` (`Hh`) inside a List collection's instance (TWINWIDE).
    NestedChild,
    /// A child of the fixed group `gg` named through the group's struct, `crate::Gg::gl:`, as
    /// a context alias and a function context read it (TWINWIDE).
    GroupPath,
}

impl Place {
    /// Every place, the twins' first.
    pub const ALL: [Self; 9] = [
        Self::Top,
        Self::ListChild,
        Self::MapChild,
        Self::GroupChild,
        Self::OptChild,
        Self::OptLeaf,
        Self::SetChild,
        Self::NestedChild,
        Self::GroupPath,
    ];

    /// Whether the place is one TWINWIDE added, where only the rows of [`Reach::Core`] are
    /// written, in a readable and a `cells!` rule.
    const fn widened(self) -> bool {
        matches!(self, Self::OptLeaf | Self::SetChild | Self::NestedChild)
    }

    /// The place's ID segment.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Top => "top",
            Self::ListChild => "list-child",
            Self::MapChild => "map-child",
            Self::GroupChild => "group-child",
            Self::OptChild => "opt-child",
            Self::OptLeaf => "opt-leaf",
            Self::SetChild => "set-child",
            Self::NestedChild => "nested-child",
            Self::GroupPath => "group-path",
        }
    }

    /// The place's letter in its cells' names.
    const fn letter(self) -> &'static str {
        match self {
            Self::Top => "t",
            Self::ListChild => "j",
            Self::MapChild => "a",
            Self::GroupChild | Self::GroupPath => "g",
            Self::OptChild => "o",
            Self::OptLeaf => "p",
            Self::SetChild => "s",
            Self::NestedChild => "h",
        }
    }

    /// The group whose children the place's cells are.
    const fn group(self) -> &'static str {
        match self {
            Self::Top | Self::OptLeaf => "Machine",
            Self::ListChild => "J",
            Self::MapChild => "A",
            Self::GroupChild | Self::GroupPath => "Gg",
            Self::OptChild => "Og",
            Self::SetChild => "E",
            Self::NestedChild => "Hh",
        }
    }
}

/// The cell of `kind` at `place`.
#[must_use]
pub fn cell(place: Place, kind: Kind) -> String {
    format!("{}{}", place.letter(), kind.letter())
}

/// A sentence form of the family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Form {
    /// A readable rule of `k::rules!`.
    Readable,
    /// A `#[k::rule]` fn over `k::cells!` records.
    Cells,
    /// A `#[k::claim]` fn over `k::cells!` records.
    CellsClaim,
    /// A readable claim of `k::claims!` (TWINWIDE).
    ReadableClaim,
    /// A `#[k::context]` fn over a `k::cells!` pattern, which keeps every cell it names.
    Context,
    /// A `#[k::context_alias]` fn over a `k::cells!` pattern.
    ContextAlias,
    /// An `#[k::equation]` whose function context is a `k::cells!` pattern.
    FunctionContext,
    /// A single-body `#[k::rule]` fn: one `k::cells!` subject whose `k::rewrite!` marks the change.
    SingleBody,
}

impl Form {
    /// Every form.
    pub const ALL: [Self; 8] = [
        Self::Readable,
        Self::Cells,
        Self::CellsClaim,
        Self::ReadableClaim,
        Self::Context,
        Self::ContextAlias,
        Self::FunctionContext,
        Self::SingleBody,
    ];

    /// The form's ID segment.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Readable => "readable",
            Self::Cells => "cells",
            Self::CellsClaim => "cells-claim",
            Self::ReadableClaim => "readable-claim",
            Self::Context => "context",
            Self::ContextAlias => "context-alias",
            Self::FunctionContext => "function-context",
            Self::SingleBody => "single-body",
        }
    }

    /// Whether the form is readable: its children are written as their twins are.
    const fn readable(self) -> bool {
        matches!(self, Self::Readable | Self::ReadableClaim)
    }

    /// Whether the form is a kept sentence, whose pattern keeps every cell it names: a
    /// context, a context alias or a function context.
    const fn kept(self) -> bool {
        matches!(
            self,
            Self::Context | Self::ContextAlias | Self::FunctionContext
        )
    }

    /// Whether the form writes a child at `place` (TWINWIDE): a readable claim at the places
    /// TWINORACLE wrote; a context at those too, which matches as a rule's subject does; a
    /// context alias and a function context only where they read a fixed leaf, at the top and
    /// a fixed group's child named through the group's struct (`language.mdx`: they "read fixed
    /// leaf cells only", and a group cell's entry, a `?` cell's `Some(..)` or a collection's
    /// instance list there "is not supported yet"); a single-body rule where a rewrite is a
    /// cell's whole content ("a leaf of any sort, inside a group .. too, an optional cell's
    /// present content .. and a matched collection instance's child"), and at a `?` group's
    /// child, the stated limit [`SINGLE_BODY_OPTIONAL_GROUP`]; the rule forms everywhere but the
    /// group path.
    const fn writes(self, place: Place) -> bool {
        match self {
            Self::ReadableClaim | Self::Context => matches!(
                place,
                Place::Top
                    | Place::ListChild
                    | Place::MapChild
                    | Place::GroupChild
                    | Place::OptChild
            ),
            Self::ContextAlias | Self::FunctionContext => {
                matches!(place, Place::Top | Place::GroupPath)
            }
            Self::SingleBody => matches!(
                place,
                Place::Top
                    | Place::ListChild
                    | Place::MapChild
                    | Place::GroupChild
                    | Place::OptChild
                    | Place::OptLeaf
            ),
            Self::Readable | Self::Cells | Self::CellsClaim => !matches!(place, Place::GroupPath),
        }
    }
}

/// One spelling of a child: its kind, its subject and result texts in a readable record and in a
/// `cells!` record (`-` where a side does not write the child, both `-` where the form does not
/// write the row), the `cells!` parameters its binders need, the names its command binds, and
/// whether its rule moves the computation's remainder `tail` (`cells!` only: `k`'s result is then
/// `KCell()`).
#[derive(Clone, Copy, Debug)]
pub struct Row {
    /// The child's kind.
    pub kind: Kind,
    /// The readable subject and result.
    pub readable: [&'static str; 2],
    /// The `cells!` subject and result.
    pub cells: [&'static str; 2],
    /// The `cells!` rule's parameters besides the command's.
    pub params: &'static [(&'static str, &'static str)],
    /// The command's arguments, each an `Int`.
    pub args: &'static [&'static str],
    /// Whether the rule moves `k`'s remainder `tail` into the child.
    pub moves_rest: bool,
    /// Whether the spelling is the whole entry rather than a content (`_`, a binder), so its twin
    /// writes it as written, in the child's own form, unwrapped: on the computation, which spells
    /// its content as items, a bare `_` or binder is the entry's own mistake at the top as in a
    /// record (`cell-wrapper`: "a value where the computation's .. wrapper is missing").
    pub bare: bool,
    /// The readable rule's binder declarations (`where b: KSequence`), empty for none.
    pub declares: &'static str,
    /// Where the row is written ([`Reach`]).
    pub reach: Reach,
}

/// Where a row is written.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reach {
    /// At TWINORACLE's places, in a readable rule, a `cells!` rule and a `cells!` claim.
    Standard,
    /// There, and as one of each kind's representative spellings (a subject, a result, both
    /// sides, `_`) at the places and in the sentences TWINWIDE added.
    Core,
    /// A single-body rule's rewrite (its `cells!` subject a `k::rewrite!`), in that form only.
    SingleBody,
}

const NONE: [&str; 2] = ["-", "-"];
const ITEM: &str = "k::KItem";
const LIST: &str = "k::Term<k::builtin::List>";
const INT: &str = "k::Term<k::builtin::Int>";
const MAP: &str = "k::Term<k::builtin::Map>";
const SET: &str = "k::Term<k::builtin::Set>";
const SEQUENCE: &str = "k::builtin::KSequence";

const fn row(kind: Kind, readable: [&'static str; 2], cells: [&'static str; 2]) -> Row {
    Row {
        kind,
        readable,
        cells,
        params: &[],
        args: &[],
        moves_rest: false,
        bare: false,
        declares: "",
        reach: Reach::Standard,
    }
}

const fn single(cells: &'static str) -> Row {
    let mut row = row(Kind::Int, NONE, [cells, "-"]);
    row.reach = Reach::SingleBody;
    row
}

const fn of(mut row: Row, kind: Kind) -> Row {
    row.kind = kind;
    row
}

const fn core(mut row: Row) -> Row {
    row.reach = Reach::Core;
    row
}

const fn bare(mut row: Row) -> Row {
    row.bare = true;
    row
}

const fn declaring(mut row: Row, declares: &'static str) -> Row {
    row.declares = declares;
    row
}

const fn bound(mut row: Row, params: &'static [(&'static str, &'static str)]) -> Row {
    row.params = params;
    row
}

const fn taking(mut row: Row, args: &'static [&'static str]) -> Row {
    row.args = args;
    row
}

const fn moving(mut row: Row) -> Row {
    row.moves_rest = true;
    row
}

/// The family's rows: for each kind, the spellings the CHILDSEQ, CHILDKIND and CHILDLEFT lanes
/// probed by hand (brackets with `..` at either end and `[..]`, named rests, map braces with
/// `..` and a named rest, `k::k![..]` and `k::map![..]`, a constant after `..`, a remainder written
/// into another kind, a remainder saved whole into a leaf of sort `KSequence`), and the brackets a
/// kind refuses.
pub const ROWS: &[Row] = &[
    // The computation.
    core(row(
        Kind::Computation,
        ["[Go(), ..]", "[Hold(), ..]"],
        ["[Cmd::Go(), ..]", "[Cmd::Hold(), ..]"],
    )),
    row(Kind::Computation, ["[..]", "-"], ["[..]", "-"]),
    row(
        Kind::Computation,
        ["[..]", "[Hold(), ..]"],
        ["[..]", "[Cmd::Hold(), ..]"],
    ),
    row(
        Kind::Computation,
        ["[Go(), ..]", "[]"],
        ["[Cmd::Go(), ..]", "[]"],
    ),
    taking(
        row(
            Kind::Computation,
            ["[_, ..]", "[x, ..]"],
            ["[_, ..]", "[x, ..]"],
        ),
        &["x"],
    ),
    row(Kind::Computation, ["[Go()]", "-"], ["[Cmd::Go()]", "-"]),
    row(
        Kind::Computation,
        NONE,
        ["k::k![Cmd::Go(), ..]", "k::k![Cmd::Hold(), ..]"],
    ),
    core(row(
        Kind::Computation,
        NONE,
        ["[Cmd::Go(), rest @ ..]", "[Cmd::Hold(), ..rest]"],
    )),
    row(Kind::Computation, NONE, ["-", "[Cmd::Hold(), ..zz]"]),
    moving(row(Kind::Computation, NONE, ["-", "[..tail]"])),
    // The builtin `List`.
    core(bound(
        row(Kind::List, ["[y, ..]", "-"], ["[y, ..]", "-"]),
        &[("y", ITEM)],
    )),
    core(taking(
        row(Kind::List, ["[_, ..]", "[x, ..]"], ["[_, ..]", "[x, ..]"]),
        &["x"],
    )),
    row(Kind::List, ["[..]", "-"], ["[..]", "-"]),
    row(Kind::List, ["[..]", "[1, ..]"], ["[..]", "[1, ..]"]),
    bound(
        row(Kind::List, ["[.., y]", "-"], ["[.., y]", "-"]),
        &[("y", ITEM)],
    ),
    taking(
        row(Kind::List, ["[_, ..]", "[.., x]"], ["[_, ..]", "[.., x]"]),
        &["x"],
    ),
    bound(
        row(
            Kind::List,
            ["[y, rest @ ..]", "[..rest, y]"],
            ["[y, rest @ ..]", "[..rest, y]"],
        ),
        &[("y", ITEM), ("rest", LIST)],
    ),
    core(taking(row(Kind::List, ["-", "[x]"], ["-", "[x]"]), &["x"])),
    bound(
        row(Kind::List, ["[y, ..]", "[]"], ["[y, ..]", "[]"]),
        &[("y", ITEM)],
    ),
    taking(
        row(Kind::List, ["-", "[x, ..ELS]"], ["-", "[x, ..ELS]"]),
        &["x"],
    ),
    moving(row(Kind::List, NONE, ["-", "[1, ..tail]"])),
    // The builtin `Map`.
    core(bound(
        row(
            Kind::Map,
            ["{ 0 -> v, .. }", "-"],
            ["k::map![0 -> v, ..]", "-"],
        ),
        &[("v", ITEM)],
    )),
    bound(
        row(Kind::Map, ["{ 0 -> v }", "-"], ["k::map![0 -> v]", "-"]),
        &[("v", ITEM)],
    ),
    core(taking(
        row(Kind::Map, ["-", "{ 0 -> x }"], ["-", "k::map![0 -> x]"]),
        &["x"],
    )),
    taking(
        bound(
            row(
                Kind::Map,
                ["{ 0 -> v, rest @ .. }", "{ 0 -> x, ..rest }"],
                ["k::map![0 -> v, rest @ ..]", "k::map![0 -> x, ..rest]"],
            ),
            &[("v", ITEM)],
        ),
        &["x"],
    ),
    bound(
        row(Kind::Map, ["map![0 -> v, ..]", "-"], NONE),
        &[("v", ITEM)],
    ),
    row(Kind::Map, NONE, ["k::map![..]", "-"]),
    row(Kind::Map, ["[..]", "-"], ["[..]", "-"]),
    moving(row(Kind::Map, NONE, ["-", "k::map![0 -> 1, ..tail]"])),
    // The builtin `Set`.
    bound(
        row(Kind::Set, ["{ y, .. }", "-"], ["k::set![y, ..]", "-"]),
        &[("y", ITEM)],
    ),
    core(taking(row(Kind::Set, NONE, ["-", "k::set![x]"]), &["x"])),
    row(Kind::Set, ["[..]", "-"], ["[..]", "-"]),
    // An `Int` leaf.
    core(bound(row(Kind::Int, ["y", "-"], ["y", "-"]), &[("y", INT)])),
    core(taking(row(Kind::Int, ["-", "x"], ["-", "x"]), &["x"])),
    row(Kind::Int, ["[..]", "-"], ["[..]", "-"]),
    // A leaf of sort `KSequence`: the computation's remainder saved into it whole (A1).
    core(moving(row(Kind::SequenceLeaf, NONE, ["-", "tail"]))),
    // TWINWIDE step 1: the whole content `_`, a bare binder and an alias at each kind
    // (`language.mdx`: a record's child is "a binder, `_`, a term of its sort, .." read "exactly
    // as if the child were written as its own cell"). On the computation, `_` and a binder are
    // the entry, twinned with the same bare entry at the top ([`Row::bare`]).
    core(bare(row(Kind::Computation, ["_", "-"], ["_", "-"]))),
    bare(bound(
        row(Kind::Computation, ["b", "-"], ["b", "-"]),
        &[("b", SEQUENCE)],
    )),
    core(row(Kind::List, ["_", "-"], ["_", "-"])),
    bound(row(Kind::List, ["b", "-"], ["b", "-"]), &[("b", LIST)]),
    bound(
        row(Kind::List, ["b @ [y, ..]", "-"], ["b @ [y, ..]", "-"]),
        &[("b", LIST), ("y", ITEM)],
    ),
    core(row(Kind::Map, ["_", "-"], ["_", "-"])),
    bound(row(Kind::Map, ["b", "-"], ["b", "-"]), &[("b", MAP)]),
    bound(
        row(
            Kind::Map,
            ["b @ { 0 -> v, .. }", "-"],
            ["b @ k::map![0 -> v, ..]", "-"],
        ),
        &[("b", MAP), ("v", ITEM)],
    ),
    core(row(Kind::Set, ["_", "-"], ["_", "-"])),
    bound(row(Kind::Set, ["b", "-"], ["b", "-"]), &[("b", SET)]),
    core(row(Kind::Int, ["_", "-"], ["_", "-"])),
    bound(
        row(Kind::Int, ["b @ 0", "-"], ["b @ 0", "-"]),
        &[("b", INT)],
    ),
    core(row(Kind::SequenceLeaf, ["_", "-"], ["_", "-"])),
    bound(
        row(Kind::SequenceLeaf, ["b", "-"], ["b", "-"]),
        &[("b", SEQUENCE)],
    ),
    // TWINWIDE step 3: a single-body rule's rewrite of a cell's whole content, at each kind
    // whose content one rewrite writes ("A rewrite that is a cell's whole content .. changes the
    // content from what its left side matches to what its right side writes").
    taking(bound(single("k::rewrite!(y => x)"), &[("y", INT)]), &["x"]),
    taking(of(single("k::rewrite!(_ => [x])"), Kind::List), &["x"]),
    taking(
        of(single("k::rewrite!(_ => k::map![0 -> x])"), Kind::Map),
        &["x"],
    ),
    taking(
        of(single("k::rewrite!(_ => k::set![x])"), Kind::Set),
        &["x"],
    ),
    of(single("k::rewrite!(_ => ())"), Kind::SequenceLeaf),
    // TWINWIDE step 4 (after KSEQSPLITS): a matched computation whose parts are binders of sort
    // `K`. `b, ..` and `b, c, ..` have two parts of unknown length, so a computation splits
    // between them in more than one way; `Keep { body: b }, b, ..` has one, since `keep(b)`
    // fixes `b`. Their twins are the `KCell(..)` spellings.
    declaring(
        bound(
            row(Kind::Computation, ["[b, ..]", "-"], ["[b, ..]", "-"]),
            &[("b", SEQUENCE)],
        ),
        "b: KSequence",
    ),
    declaring(
        bound(
            row(Kind::Computation, ["[b, c, ..]", "-"], ["[b, c, ..]", "-"]),
            &[("b", SEQUENCE), ("c", SEQUENCE)],
        ),
        "b: KSequence, c: KSequence",
    ),
    // The refusal's advice: a binder declared at an item sort has a known length, so `i, ..`
    // splits one way.
    declaring(
        bound(
            row(Kind::Computation, ["[i, ..]", "-"], ["[i, ..]", "-"]),
            &[("i", ITEM)],
        ),
        "i: k::KItem",
    ),
    declaring(
        bound(
            row(
                Kind::Computation,
                ["[Keep { body: b }, b, ..]", "-"],
                ["[Cmd::Keep { body: b }, b, ..]", "-"],
            ),
            &[("b", SEQUENCE)],
        ),
        "b: KSequence",
    ),
];

impl Row {
    /// The row's subject and result in `form`, `None` where a side does not write the child;
    /// `None` where the form does not write the row.
    fn texts(&self, form: Form) -> Option<[Option<&'static str>; 2]> {
        let texts = if form.readable() {
            self.readable
        } else {
            self.cells
        };
        let side = |text: &'static str| (text != "-").then_some(text);
        let texts = [side(texts[0]), side(texts[1])];
        let written = match form {
            Form::SingleBody => self.reach == Reach::SingleBody,
            _ if self.reach == Reach::SingleBody => false,
            Form::ReadableClaim => self.reach == Reach::Core,
            // A kept sentence has no result: it writes a core row's subject.
            Form::Context | Form::ContextAlias | Form::FunctionContext => {
                self.reach == Reach::Core && texts[1].is_none() && !self.moves_rest
            }
            Form::Readable | Form::Cells | Form::CellsClaim => true,
        };
        (written && texts != [None, None]).then_some(texts)
    }
}

/// The ID segment of a row's side: `subject`, `result` or `both`.
const fn side_name(texts: [Option<&str>; 2]) -> &'static str {
    match texts {
        [Some(_), None] => "subject",
        [None, Some(_)] => "result",
        _ => "both",
    }
}

/// The construct of a row's case: its subject, its result, or both joined by ` => `.
fn construct(texts: [Option<&str>; 2]) -> String {
    match texts {
        [Some(subject), Some(result)] => format!("{subject} => {result}"),
        [Some(text), None] | [None, Some(text)] => text.to_owned(),
        [None, None] => unreachable!("a row writes one side at least"),
    }
}

/// A child's `cells!` text as its twin, a top-level cell, writes it: a computation's items, in
/// brackets or in `k::k![..]`, as `KCell(..)`'s, any other computation term as `KCell`'s one
/// part, and any other kind's content in `Cell(..)`.
#[must_use]
pub fn cells_twin(kind: Kind, text: &str) -> String {
    if kind == Kind::Computation {
        let items = text
            .strip_prefix("k::k![")
            .or_else(|| text.strip_prefix('['))
            .and_then(|inner| inner.strip_suffix(']'))
            .unwrap_or(text);
        format!("k::configuration::KCell({items})")
    } else {
        format!("k::configuration::Cell({text})")
    }
}

/// The twin's form of a child case of `form` and `kind`: its own, but a readable computation
/// child's, whose twin is the `cells!` cell. A readable record reads one computation cell by its
/// brackets in a rule, so a second top-level computation cell bracketed beside `k` is not
/// supported yet (`language.mdx`, "A record that brackets two computation cells .. is not
/// supported yet"), while "a group record's computation child is no second cell of the record
/// but an entry of the group's record, so its brackets are its items beside `k`'s" (the same
/// paragraph), as an instance's are: the cell whose items the child's brackets are is the
/// `cells!` cell `KCell(..)`, which writes them. A bare entry ([`Row::bare`]) brackets nothing,
/// and is twinned in its own form.
#[must_use]
pub const fn twin_form(form: Form, row: &Row) -> Form {
    match (form, row.kind, row.bare) {
        (Form::Readable, Kind::Computation, false) => Form::Cells,
        (Form::ReadableClaim, Kind::Computation, false) => Form::CellsClaim,
        _ => form,
    }
}

/// Why a child case at `place`, writing `texts`, is no twin's: a stated difference,
/// where the child cannot mean what its twin means, by a limit the documentation or a refusal
/// states. `None` where the relation holds.
#[must_use]
pub fn stated(
    form: Form,
    place: Place,
    row: &Row,
    texts: [Option<&str>; 2],
) -> Option<&'static str> {
    let kind = row.kind;
    let group_record = matches!(
        place,
        Place::GroupChild | Place::OptChild | Place::NestedChild
    );
    let result_keeps_rest = texts[1].is_some_and(|result| {
        let brackets = result.starts_with('[') || result.starts_with("k::k![");
        brackets && (result.contains(", ..]") || result == "[..]" || result.starts_with("[..,"))
    });
    // A bare entry on the computation is the entry's own mistake, told before any limit of the
    // place, as its twin's is.
    if place == Place::OptChild && kind == Kind::Computation && !row.bare {
        return Some(OPTIONAL_GROUP_COMPUTATION);
    }
    if group_record && result_keeps_rest && matches!(kind, Kind::Computation | Kind::List) {
        return Some(GROUP_CHILD_RESULT_REST);
    }
    if place == Place::NestedChild && kind == Kind::Computation && !row.bare {
        return Some(INSTANCE_GROUP_COMPUTATION);
    }
    if place == Place::OptLeaf && form.readable() && result_keeps_rest {
        return Some(OPTIONAL_LEAF_RESULT_REST);
    }
    if place == Place::OptChild && form == Form::SingleBody {
        return Some(SINGLE_BODY_OPTIONAL_GROUP);
    }
    None
}

/// A `?` group's computation child is not supported yet in a rule, with or without a rest: the
/// present group's record is read as one term of the group (`krs-syntax`
/// `list_notation::GROUP_CHILD_ANONYMOUS_REST`: "a `?` group's computation child (`Some(G { c:
/// [x, ..], .. })`) is not supported yet in a rule, with or without a rest"), and a term holds no
/// computation's items. A top-level computation cell has no such limit.
pub const OPTIONAL_GROUP_COMPUTATION: &str = "a `?` group's computation child is not supported yet in a rule, with or without a rest (list_notation.rs GROUP_CHILD_ANONYMOUS_REST)";

/// A group record's child keeps no rest in a result: the record is read as one term of the group,
/// which writes each child's whole content (`language.mdx`, "below it elsewhere, in a group's
/// child (`H { hl: [x, ..], hb: 0 }`) or inside `Some([..])` .., a result's `..` is not supported
/// yet"; `list_notation::GROUP_CHILD_ANONYMOUS_REST`). A top-level cell's brackets keep the rest.
pub const GROUP_CHILD_RESULT_REST: &str = "a group record's child keeps no rest in a result: a result's `..` there is not supported yet (language.mdx, an anonymous `..` keeps a rest only in a cell of the record itself and in an instance's child; list_notation.rs GROUP_CHILD_ANONYMOUS_REST)";

/// A computation child of a group inside an instance record is not supported yet in a rule: an
/// instance record's group child is "the group's term", and "a record whose child's entry is a
/// computation's items is lowered as its children's own cells, and is not supported yet where the
/// group must be one term" (`language.mdx`; CHILDKIND's C6: a named computation rest one level
/// down). A top-level computation cell has no such limit.
pub const INSTANCE_GROUP_COMPUTATION: &str = "a computation child of a group inside an instance record is not supported yet in a rule: the record is the group's term, which holds no computation's items (language.mdx, a record whose child's entry is a computation's items is not supported yet where the group must be one term; CHILDKIND C6)";

/// A readable `?` leaf's `Some([..])` keeps no rest in a result: "inside `Some([..])` .. a
/// result's `..` is not supported yet" (`language.mdx`, the paragraph on where an anonymous `..`
/// keeps a rest), but over the subject's own `Some([..])`. A top-level list cell's brackets keep
/// the rest, and so does the `cells!` `Some(Cell([..]))`, whose brackets are the cell's own.
pub const OPTIONAL_LEAF_RESULT_REST: &str = "a readable `?` leaf's `Some([..])` keeps no rest in a result: a result's `..` inside `Some([..])` is not supported yet (language.mdx, an anonymous `..` keeps a rest only in a cell of the record itself and in an instance's child)";

/// A single-body rule's rewrite of a `?` group's child is a rewrite below the root of the
/// optional cell's present content, which "has no lowering yet (`krs::analysis::optional-presence`
/// ..): rewrite that content whole, or write the rule with a result" (`language.mdx`, local
/// rewrites). A top-level cell's whole content, and a `?` leaf's present content, are rewritten.
pub const SINGLE_BODY_OPTIONAL_GROUP: &str = "a single-body rule's rewrite of a `?` group's child stands below the root of the optional cell's present content, which has no lowering yet (language.mdx, local rewrites: krs::analysis::optional-presence)";

/// One case of the family, and what it is judged by.
#[derive(Clone, Debug)]
pub struct Generated {
    /// The case.
    pub case: Case,
    /// For a child case, its twin's ID, where the relation holds.
    pub twin: Option<String>,
    /// For a child case where the relation does not hold, why ([`stated`]).
    pub stated: Option<&'static str>,
    /// The child's cell, and its twin's (`jl` and `tl`); `None` for a twin.
    pub cells: Option<(String, String)>,
    /// Where the case's cell stands.
    pub place: Place,
}

/// The ID of the case of `form`, `place`, `kind` and `texts` (each in the form's own spelling).
fn id(form: Form, place: Place, kind: Kind, texts: [Option<&str>; 2]) -> String {
    format!(
        "{}/{}/{}/{}/{}/{}",
        Family::ChildTwins.name(),
        form.name(),
        side_name(texts),
        place.name(),
        kind.name(),
        construct(texts)
    )
}

/// The texts a twin of `form` writes for a row's child texts of `form` (its own form's): a
/// readable child's as written, a `cells!` child's wrapped ([`cells_twin`]).
fn twin_texts(form: Form, row: &Row) -> Option<[Option<String>; 2]> {
    let texts = row.texts(form)?;
    Some(texts.map(|text| {
        text.map(|text| {
            if form.readable() || row.bare {
                text.to_owned()
            } else {
                cells_twin(row.kind, text)
            }
        })
    }))
}

/// A child's texts as its place writes them: a `?` leaf's present content in `Some(..)`, as
/// its twin's content (a `cells!` leaf's in `Cell(..)`: "`omap: Some(k::configuration::Cell(map![k
/// -> v, ..]))`"); a group path's wrapped as its twin's, but a bare entry ([`Row::bare`]); every
/// other place's as the row writes them.
fn place_texts(
    form: Form,
    place: Place,
    row: &Row,
    texts: [Option<&str>; 2],
) -> [Option<String>; 2] {
    texts.map(|text| {
        text.map(|text| match place {
            Place::OptLeaf if form.readable() => format!("Some({text})"),
            Place::OptLeaf => format!("Some({})", cells_twin(row.kind, text)),
            Place::GroupPath if !row.bare => cells_twin(row.kind, text),
            _ => text.to_owned(),
        })
    })
}

/// Every case of the family, in generation order.
pub static GENERATED: LazyLock<Vec<Generated>> = LazyLock::new(|| {
    let mut out = Vec::new();
    // Two rows whose children differ may share a twin (`[Cmd::Go(), ..]` and `k::k![Cmd::Go(), ..]`
    // are both `KCell(Cmd::Go(), ..)`): the twin is generated once.
    let mut twins = std::collections::BTreeSet::new();
    for row in ROWS {
        for form in Form::ALL {
            let Some(texts) = row.texts(form) else {
                continue;
            };
            let twin_form = twin_form(form, row);
            for place in Place::ALL {
                if !form.writes(place)
                    || (place.widened()
                        && matches!(form, Form::Readable | Form::Cells | Form::CellsClaim)
                        && (row.reach != Reach::Core || form == Form::CellsClaim))
                    || (place == Place::OptLeaf && row.kind == Kind::Computation)
                {
                    continue;
                }
                if place == Place::Top {
                    if twin_form != form {
                        continue;
                    }
                    let twin = twin_texts(form, row).expect("the row writes the form");
                    let texts = [twin[0].as_deref(), twin[1].as_deref()];
                    if !twins.insert(id(form, place, row.kind, texts)) {
                        continue;
                    }
                    out.push(Generated {
                        case: render(form, place, row, texts),
                        twin: None,
                        stated: None,
                        cells: None,
                        place,
                    });
                    continue;
                }
                let stated = stated(form, place, row, texts);
                let twin = if stated.is_some() {
                    None
                } else {
                    twin_texts(twin_form, row).map(|twin| {
                        id(
                            twin_form,
                            Place::Top,
                            row.kind,
                            [twin[0].as_deref(), twin[1].as_deref()],
                        )
                    })
                };
                let shown = place_texts(form, place, row, texts);
                out.push(Generated {
                    case: render(form, place, row, [shown[0].as_deref(), shown[1].as_deref()]),
                    twin,
                    stated,
                    cells: Some((cell(place, row.kind), cell(Place::Top, row.kind))),
                    place,
                });
            }
        }
    }
    out
});

static TWINS: LazyLock<BTreeMap<&'static str, &'static Generated>> = LazyLock::new(|| {
    GENERATED
        .iter()
        .map(|generated| (generated.case.id.as_str(), generated))
        .collect()
});

/// The family's cases.
pub(super) fn cases(cases: &mut Vec<Case>) {
    cases.extend(GENERATED.iter().map(|generated| generated.case.clone()));
}

/// The ID of the twin of the child case `id`, where the relation holds: the case is expected
/// what its twin is ([`super::table`]). `None` for a twin, a child of a stated difference, and a
/// case of another family.
#[must_use]
pub fn twin_of(id: &str) -> Option<&'static str> {
    TWINS.get(id)?.twin.as_deref()
}

/// Whether the child case `id` owes the lint its twin's entry owes. A lint of a twin's entry
/// (`no-effect-entry`: it matches whatever its cell holds and binds nothing, so the sentence is
/// the same without it) is the whole entry's, so it is the child's only where the record around
/// the child adds nothing of its own: a fixed group's, which is always there. An instance record
/// requires an instance and a `?` group's `Some(..)` the group's presence, so their entries
/// constrain the configuration whatever the child's spelling. `true` for every other case.
#[must_use]
pub fn owes_twin_lint(id: &str) -> bool {
    TWINS.get(id).is_none_or(|generated| {
        generated.twin.is_none() || matches!(generated.place, Place::GroupChild | Place::GroupPath)
    })
}

/// The generated case `id` of the family, with what it is judged by.
#[must_use]
pub fn generated(id: &str) -> Option<&'static Generated> {
    TWINS.get(id).copied()
}

/// A child case's K sentences read at its twin's place ([`Generated::cells`]); `None` where a
/// sentence writes the child otherwise than these rules read, whose K then differs from the
/// twin's (K2 says so). In the sentence that writes the child's cell:
///
/// - a rewrite of a whole holder, `(<og> .. <ol> A </ol> .. </og> => <og> .. <ol> B </ol> ..
///   </og>)`, whose other cells are written alike on both sides, is the rewrite of the child,
///   `<ol> A => B </ol>`: the other cells are kept, as the holder's frame keeps them (a group the
///   rule writes as one term, a `?` group's, is printed so);
/// - the cells that hold the child (its instance or group, and a collection's own cell around the
///   instance) are taken away where they hold nothing else but frames, `...`, and cells whose
///   content is `_`, which match whatever their cell holds as a frame does;
/// - the child's cell is renamed its twin's.
///
/// What the holders add is the child's place, not its spelling: an instance or a present group
/// to hold it, which the twin's top-level cell always has.
#[must_use]
pub fn projection(additions: &[String], child: &str, twin: &str) -> Option<Vec<String>> {
    let open = format!("<{child}>");
    let mut out = Vec::with_capacity(additions.len());
    let mut found = false;
    for sentence in additions {
        if !sentence.contains(&open) {
            out.push(sentence.clone());
            continue;
        }
        found = true;
        let sentence = holder_rewrite(sentence, child).unwrap_or_else(|| sentence.clone());
        out.push(unwrapped(&sentence, child, twin)?);
    }
    found.then_some(out)
}

/// One cell element of a sentence: `<name>` .. `</name>` at a byte range.
#[derive(Clone, Debug)]
struct Element {
    name: String,
    start: usize,
    end: usize,
    /// The content's range, between the tags.
    inner: std::ops::Range<usize>,
}

/// The cell elements of `text`, outermost first in order of their opening tags.
fn elements(text: &str) -> Vec<Element> {
    let mut stack = Vec::<(String, usize, usize)>::new();
    let mut found = Vec::new();
    let mut at = 0;
    while let Some(offset) = text[at..].find('<') {
        let start = at + offset;
        let rest = &text[start + 1..];
        let closing = rest.starts_with('/');
        let name_start = start + 1 + usize::from(closing);
        let name_len = text[name_start..]
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '-'))
            .unwrap_or(text.len() - name_start);
        let after = name_start + name_len;
        if name_len == 0 || !text[after..].starts_with('>') {
            at = start + 1;
            continue;
        }
        let name = text[name_start..after].to_owned();
        let tag_end = after + 1;
        if closing {
            if let Some(index) = stack.iter().rposition(|(open, ..)| *open == name) {
                let (name, open_start, inner_start) = stack.remove(index);
                stack.truncate(index);
                found.push(Element {
                    name,
                    start: open_start,
                    end: tag_end,
                    inner: inner_start..start,
                });
            }
        } else {
            stack.push((name, start, tag_end));
        }
        at = tag_end;
    }
    found.sort_by_key(|element| element.start);
    found
}

/// The innermost element of `all` that strictly holds `held`.
fn parent<'a>(all: &'a [Element], held: &Element) -> Option<&'a Element> {
    all.iter()
        .filter(|element| element.start < held.start && held.end <= element.end)
        .max_by_key(|element| element.start)
}

/// `sentence` with a rewrite of a whole holder of `child` read as the child's rewrite
/// ([`projection`]'s first rule); `None` where the sentence holds none.
fn holder_rewrite(sentence: &str, child: &str) -> Option<String> {
    let all = elements(sentence);
    let children = all
        .iter()
        .filter(|element| element.name == child)
        .collect::<Vec<_>>();
    let [left, right] = children.as_slice() else {
        return None;
    };
    let (left_holder, right_holder) = (parent(&all, left)?, parent(&all, right)?);
    if left_holder.name != right_holder.name
        || !sentence[..left_holder.start].ends_with('(')
        || sentence[left_holder.end..right_holder.start] != *" => "
        || !sentence[right_holder.end..].starts_with(')')
    {
        return None;
    }
    let others = |holder: &Element, held: &Element| {
        format!(
            "{}{}",
            &sentence[holder.inner.start..held.start],
            &sentence[held.end..holder.inner.end]
        )
    };
    if others(left_holder, left) != others(right_holder, right) {
        return None;
    }
    let content = |element: &Element| sentence[element.inner.clone()].trim().to_owned();
    let mut text = String::with_capacity(sentence.len());
    text.push_str(&sentence[..left_holder.start - 1]);
    let _ = write!(
        text,
        "<{child}> {} => {} </{child}>",
        content(left),
        content(right)
    );
    text.push_str(&sentence[right_holder.end + 1..]);
    Some(text)
}

/// `sentence` with the cells around `child`'s element taken away and `child` renamed `twin`
/// ([`projection`]).
fn unwrapped(sentence: &str, child: &str, twin: &str) -> Option<String> {
    let all = elements(sentence);
    let target = all.iter().find(|element| element.name == child)?;
    if all.iter().filter(|element| element.name == child).count() != 1 {
        return None;
    }
    // The child's ancestors, outermost first, below the sentence's top level.
    let ancestors = all
        .iter()
        .filter(|element| element.start < target.start && target.end <= element.end)
        .collect::<Vec<_>>();
    let Some(outer) = ancestors.first() else {
        return Some(renamed_element(sentence, target, twin));
    };
    // Every ancestor holds the next one (or the child) and frames only.
    let mut holders = ancestors.clone();
    holders.push(target);
    for pair in holders.windows(2) {
        let (holder, held) = (pair[0], pair[1]);
        let siblings = all
            .iter()
            .filter(|element| {
                holder.inner.start <= element.start
                    && element.end <= holder.inner.end
                    && parent(&all, element).is_some_and(|parent| parent.start == holder.start)
                    && element.start != held.start
            })
            .collect::<Vec<_>>();
        if siblings
            .iter()
            .any(|sibling| sentence[sibling.inner.clone()].trim() != "_")
        {
            return None;
        }
        let mut rest = String::new();
        let mut at = holder.inner.start;
        let mut cuts = siblings.clone();
        cuts.push(held);
        cuts.sort_by_key(|element| element.start);
        for cut in cuts {
            rest.push_str(&sentence[at..cut.start]);
            rest.push(' ');
            at = cut.end;
        }
        rest.push_str(&sentence[at..holder.inner.end]);
        if !frames_only(&rest) {
            return None;
        }
    }
    let child_text = renamed_element(
        &sentence[target.start..target.end],
        &Element {
            name: target.name.clone(),
            start: 0,
            end: target.end - target.start,
            inner: target.inner.start - target.start..target.inner.end - target.start,
        },
        twin,
    );
    let mut text = String::with_capacity(sentence.len());
    text.push_str(&sentence[..outer.start]);
    text.push_str(&child_text);
    text.push_str(&sentence[outer.end..]);
    Some(text)
}

/// Whether `text`, between a holder's tags and the cells it holds, holds nothing but frames:
/// whitespace and K's `...`.
fn frames_only(text: &str) -> bool {
    text.split_whitespace().all(|word| word == "...")
}

/// `text` with `element`'s tags renamed `name`.
fn renamed_element(text: &str, element: &Element, name: &str) -> String {
    let mut out = String::with_capacity(text.len() + 8);
    out.push_str(&text[..element.start]);
    let _ = write!(out, "<{name}>");
    out.push_str(&text[element.inner.clone()]);
    let _ = write!(out, "</{name}>");
    out.push_str(&text[element.end..]);
    out
}

/// The family's base: the computation `k`, the twins at the top level, and a child of every kind
/// in a List collection's instance, a Map collection's instance, a fixed group and a `?` group.
/// Every leaf is declared with its wrapper, as a declaration holding a leaf of sort `KSequence`
/// must write them.
pub(super) fn base() -> BaseText {
    BaseText {
        before_commands: BEFORE_COMMANDS,
        after_commands: AFTER_COMMANDS.as_str(),
        initializer: INITIALIZER.as_str(),
        after_initializer: "",
    }
}

const BEFORE_COMMANDS: &str = r#"use k::KResult;
use k::builtin::{Int, KSequence, List, Map, Set, list, set};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

/// A constant of the builtin `List`, written after a list's `..`.
#[k::constant]
const ELS: List = list::item(5);

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("hold")] Hold(),
    #[k::syntax("keep({body})")] Keep { body: KSequence },
"#;

/// The children of `place`'s group (a Map collection's instance's key `aid` first, a List
/// collection's instance's group `jh` last).
fn children(place: Place) -> String {
    let mut out = String::new();
    if place == Place::MapChild {
        out.push_str("    #[k::cell]\n    pub aid: k::configuration::Cell<Int>,\n");
    }
    for kind in Kind::ALL {
        let _ = write!(
            out,
            "    #[k::cell]\n    pub {}: {},\n",
            cell(place, kind),
            kind.type_name()
        );
    }
    if place == Place::ListChild {
        out.push_str("    #[k::cell(nested)]\n    pub jh: Hh,\n");
    }
    out
}

/// The kinds of the top-level `?` leaves: every kind but the computation.
const OPTIONAL_LEAVES: [Kind; 5] = [
    Kind::List,
    Kind::Map,
    Kind::Set,
    Kind::Int,
    Kind::SequenceLeaf,
];

/// The record of `place`'s group with every child at its base value.
fn default_record(place: Place) -> String {
    let mut fields = Vec::new();
    if place == Place::MapChild {
        fields.push("aid: 0".to_owned());
    }
    for kind in Kind::ALL {
        fields.push(format!("{}: {}", cell(place, kind), kind.default()));
    }
    if place == Place::ListChild {
        fields.push(format!("jh: {}", default_record(Place::NestedChild)));
    }
    format!("{} {{ {} }}", place.group(), fields.join(", "))
}

static AFTER_COMMANDS: LazyLock<String> = LazyLock::new(|| {
    let mut out = String::from("}\n\n");
    for place in [
        Place::ListChild,
        Place::MapChild,
        Place::GroupChild,
        Place::OptChild,
        Place::SetChild,
        Place::NestedChild,
    ] {
        let _ = write!(
            out,
            "#[k::cell]\npub struct {} {{\n{}}}\n\n",
            place.group(),
            children(place)
        );
    }
    out.push_str(
        "#[k::cell]\npub struct Queue {\n    #[k::cell(multiplicity = \"*\", cell_type = \"List\", \
         nested)]\n    pub job: J,\n}\n\n#[k::cell]\npub struct Bank {\n    \
         #[k::cell(multiplicity = \"*\", cell_type = \"Map\", nested)]\n    pub acct: A,\n}\n\n#[k::cell]\npub struct Club {\n    \
         #[k::cell(multiplicity = \"*\", cell_type = \"Set\", nested)]\n    pub memb: E,\n}\n\n",
    );
    out.push_str(
        "#[k::configuration]\npub struct Machine {\n    #[k::cell]\n    pub k: k::configuration::KCell<KSequence>,\n",
    );
    out.push_str(&children(Place::Top));
    for kind in OPTIONAL_LEAVES {
        let _ = write!(
            out,
            "    #[k::cell(multiplicity = \"?\")]\n    pub {}: Option<{}>,\n",
            cell(Place::OptLeaf, kind),
            kind.type_name()
        );
    }
    out.push_str("    #[k::cell(nested)]\n    pub club: Club,\n");
    out.push_str(
        "    #[k::cell(nested)]\n    pub queue: Queue,\n    #[k::cell(nested)]\n    pub bank: Bank,\n    \
         #[k::cell(nested)]\n    pub gg: Gg,\n    #[k::cell(multiplicity = \"?\", nested)]\n    \
         pub og: Option<Og>,\n}\n\n",
    );
    out
});

static INITIALIZER: LazyLock<String> = LazyLock::new(|| {
    let mut out = String::from(
        "impl Machine {\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {\n        Self {\n            k: k::k![pgm],\n",
    );
    for kind in Kind::ALL {
        let _ = writeln!(
            out,
            "            {}: {},",
            cell(Place::Top, kind),
            kind.default()
        );
    }
    for kind in OPTIONAL_LEAVES {
        let _ = writeln!(
            out,
            "            {}: k::absent!({}),",
            cell(Place::OptLeaf, kind),
            kind.default()
        );
    }
    let _ = writeln!(
        out,
        "            queue: Queue {{ job: {} }},\n            bank: Bank {{ acct: {} }},\n            gg: {},\n            og: k::absent!({}),\n            club: Club {{ memb: {} }},",
        default_record(Place::ListChild),
        default_record(Place::MapChild),
        default_record(Place::GroupChild),
        default_record(Place::OptChild),
        default_record(Place::SetChild),
    );
    out.push_str("        }\n    }\n}\n");
    out
});

/// The text of a cell's entry at `place` in `form` on the side `subject` (`true`) or the result,
/// split around the child's text `content` where it writes the child, and `labelled` where the
/// subject labels the instance its result updates; `None` for a top-level cell the side does not
/// write.
fn entry(
    form: Form,
    place: Place,
    kind: Kind,
    content: Option<&str>,
    subject: bool,
    labelled: bool,
) -> Option<(String, String)> {
    let cells = !form.readable();
    let name = cell(place, kind);
    let field = content.map_or_else(String::new, |_| format!("{name}: {{}}, "));
    let fragment = |record: String| {
        if cells {
            format!("k::fragment![crate::{record}]")
        } else {
            record
        }
    };
    let whole = match place {
        Place::Top => {
            content?;
            return Some((format!("{name}: "), String::new()));
        }
        Place::OptLeaf => match (content, cells) {
            (Some(_), _) => format!("{name}: {{}}"),
            (None, false) => format!("{name}: Some(_)"),
            (None, true) => format!("{name}: Some(k::configuration::Cell(_))"),
        },
        Place::ListChild | Place::MapChild | Place::SetChild | Place::NestedChild => {
            let (key, open, close) = match (place, cells) {
                (Place::ListChild | Place::NestedChild, false) => ("job", "[", ", ..]"),
                (Place::ListChild | Place::NestedChild, true) => {
                    ("crate::Queue::job", "[", ", ..]")
                }
                (Place::MapChild, false) => ("acct", "{ ", ", .. }"),
                (Place::MapChild, true) => ("crate::Bank::acct", "{ ", ", .. }"),
                (_, false) => ("memb", "{ ", ", .. }"),
                (_, true) => ("crate::Club::memb", "{ ", ", .. }"),
            };
            let (group, field) = if place == Place::NestedChild {
                let holder = if cells { "crate::Hh" } else { "Hh" };
                let field = content.map_or_else(String::new, |_| {
                    format!("jh: {holder} {{ {name}: {{}}, .. }}, ")
                });
                (Place::ListChild.group(), field)
            } else {
                (place.group(), field)
            };
            let label = if subject && labelled { "me @ " } else { "" };
            let rest = if subject { ".." } else { "..me" };
            let record = fragment(format!("{group} {{ {field}{rest} }}"));
            format!("{key}: {open}{label}{record}{close}")
        }
        Place::GroupChild => format!("gg: {}", fragment(format!("Gg {{ {field}.. }}"))),
        Place::GroupPath => format!("crate::Gg::{name}: {{}}"),
        Place::OptChild => format!("og: Some({})", fragment(format!("Og {{ {field}.. }}"))),
    };
    Some(whole.split_once("{}").map_or_else(
        || (whole.clone(), String::new()),
        |(before, after)| (before.to_owned(), after.to_owned()),
    ))
}

/// Push an entry's text around `content`, returning the range of the entry and of the child's
/// text in the item.
fn push_entry(
    item: &mut ItemBuilder,
    (before, after): (String, String),
    content: Option<&str>,
) -> (std::ops::Range<usize>, std::ops::Range<usize>) {
    let start = item.text.len();
    item.push(&before);
    let child_start = item.text.len();
    if let Some(content) = content {
        item.push(content);
    }
    let child_end = item.text.len();
    item.push(&after);
    (start..item.text.len(), child_start..child_end)
}

/// Push a `cells!` fn's parameters: the command's arguments and the row's binders.
fn push_parameters(item: &mut ItemBuilder, row: &Row) {
    for arg in row.args {
        item.push(&format!("    {arg}: {INT},\n"));
    }
    for (name, ty) in row.params {
        item.push(&format!("    {name}: {ty},\n"));
    }
}

/// Push the head of a kept sentence's or a single-body rule's fn, up to its `k::cells!`
/// pattern's entries: a context whose hole is the command's own `Int` argument, so it heats
/// nothing a program runs and is judged for its pattern alone; a context alias framing `here`;
/// an equation of a function of its own, so that its function context makes no other function of
/// the base one of the configuration; a single-body rule rewriting the command away.
fn kept_head(item: &mut ItemBuilder, form: Form, row: &Row, tag: &str, command: &str, args: &str) {
    match form {
        Form::Context => {
            item.push(&format!(
                "#[k::context(hole = h)]\nfn case_{tag}(\n    h: k::Term<k::builtin::Int>,\n"
            ));
            push_parameters(item, row);
            item.push(&format!(
                "    k::cells! {{ k: k::configuration::KCell(crate::Cmd::{command} {{ a: h }}, ..)"
            ));
        }
        Form::ContextAlias => {
            item.push(&format!(
                "#[k::context_alias(name = case_{tag}, here = site)]\nfn case_{tag}(\n"
            ));
            push_parameters(item, row);
            item.push("    k::cells! { k: k::configuration::KCell(site, tail @ ..)");
        }
        Form::FunctionContext => {
            item.push(&format!(
                "#[k::function(partial, sort = Int, syntax = \"probe{tag}({{a}})\")]\n\
                 pub struct Probe{tag} {{\n    pub a: k::Term<k::KItem>,\n}}\n\n\
                 #[k::equation]\nfn case_{tag}(\n    a: k::Term<k::KItem>,\n"
            ));
            push_parameters(item, row);
            item.push(&format!(
                "    k::term![Probe{tag}(a)]: k::Term<k::builtin::Int>,\n    k::cells! {{ "
            ));
        }
        _ => {
            item.push(&format!(
                "#[k::rule(label = \"case-{tag}\")]\npub fn case_{tag}(\n"
            ));
            push_parameters(item, row);
            item.push(&format!(
                "    k::cells! {{ k: k::configuration::KCell(k::rewrite!(crate::Cmd::{command}({args}) \
                 => ()), ..)"
            ));
        }
    }
}

/// The end of a kept sentence's or a single-body rule's fn, after its pattern's entries.
const fn kept_tail(form: Form) -> &'static str {
    match form {
        Form::ContextAlias => ", state @ .. }: crate::Machine,\n) {\n}\n",
        Form::FunctionContext => {
            ", .. }: crate::Machine,\n) -> k::Term<k::builtin::Int> {\n    0\n}\n"
        }
        Form::Context => ", .. }: crate::Machine,\n) {\n}\n",
        _ => ", .. }: crate::Machine,\n) {}\n",
    }
}

/// A case's written entries, each with its child's text where it writes the child.
type Ranges = Vec<(std::ops::Range<usize>, Option<std::ops::Range<usize>>)>;

/// The ranges of a case's entry and spelling: the entry runs over the cell's entries on both
/// sides; the spelling is the child's text, or, where both sides write it, from the subject's
/// child to the result's.
fn entry_and_spelling(ranges: &Ranges) -> (std::ops::Range<usize>, std::ops::Range<usize>) {
    let entry = ranges
        .first()
        .map(|first| first.0.start)
        .unwrap_or_default()
        ..ranges.last().map(|last| last.0.end).unwrap_or_default();
    let children = ranges
        .iter()
        .filter_map(|(_, child)| child.clone())
        .collect::<Vec<_>>();
    let spelling = match children.as_slice() {
        [child] => child.clone(),
        [first, .., last] => first.start..last.end,
        [] => entry.clone(),
    };
    (entry, spelling)
}

/// The case of `row` at `place` in `form`, whose child texts are `texts` (a twin's wrapped).
fn render(form: Form, place: Place, row: &Row, texts: [Option<&str>; 2]) -> Case {
    let spec = CaseSpec {
        family: Family::ChildTwins,
        base: Base::ChildTwins,
        side: if texts[1].is_some() {
            Side::Result
        } else {
            Side::Subject
        },
        kind: None,
        slot: vec![
            form.name().to_owned(),
            side_name(texts).to_owned(),
            place.name().to_owned(),
            row.kind.name().to_owned(),
        ],
        construct: construct(texts),
    };
    let arity = if form == Form::Context {
        1
    } else {
        row.args.len()
    };
    let command = Command::for_case(&spec.id(), arity);
    let args = row.args.join(", ");
    let labelled = texts[1].is_some();
    // The subject writes the cell where it writes the child, or where a child's result updates
    // the instance or group it matches; a top-level cell the subject does not write is left out.
    let subject = entry(form, place, row.kind, texts[0], true, labelled)
        .filter(|_| texts[0].is_some() || place != Place::Top);
    let result =
        texts[1].and_then(|text| entry(form, place, row.kind, Some(text), false, labelled));
    let mut item = ItemBuilder::new();
    let mut ranges = Ranges::new();
    let mut write =
        |item: &mut ItemBuilder, entry: Option<(String, String)>, text: Option<&str>| {
            if let Some(entry) = entry {
                if !item.text.ends_with("{ ") {
                    item.push(", ");
                }
                let (entry, child) = push_entry(item, entry, text);
                ranges.push((entry, text.map(|_| child)));
            }
        };
    let tag = spec.tag();
    if form.kept() || form == Form::SingleBody {
        kept_head(&mut item, form, row, &tag, &command.name, &args);
        write(&mut item, subject, texts[0]);
        item.push(kept_tail(form));
    } else if form.readable() {
        let (block, attribute) = if form == Form::ReadableClaim {
            ("k::claims!", "#[k::claim(all_paths)]\n    ")
        } else {
            ("k::rules!", "")
        };
        item.push(&format!(
            "{block} {{\n    for Machine;\n    use Cmd::*;\n\n    {attribute}case_{tag}: {{ k: [{}({args}), ..]",
            command.name
        ));
        write(&mut item, subject, texts[0]);
        item.push(" } => { k: [..]");
        write(&mut item, result, texts[1]);
        item.push(" }");
        if !row.declares.is_empty() {
            item.push(&format!(" where {}", row.declares));
        }
        item.push(";\n}\n");
    } else {
        let marker = if form == Form::CellsClaim {
            format!("#[k::claim(all_paths, label = \"case-{tag}\")]")
        } else {
            format!("#[k::rule(label = \"case-{tag}\")]")
        };
        item.push(&format!("{marker}\npub fn case_{tag}(\n"));
        push_parameters(&mut item, row);
        item.push(&format!(
            "    k::cells! {{ k: k::configuration::KCell(crate::Cmd::{}({args}), tail @ ..)",
            command.name
        ));
        write(&mut item, subject, texts[0]);
        item.push(", state @ .. }: crate::Machine,\n) -> crate::Machine {\n    k::cells! { k: ");
        item.push(if row.moves_rest {
            "k::configuration::KCell()"
        } else {
            "k::configuration::KCell(..tail)"
        });
        write(&mut item, result, texts[1]);
        item.push(", ..state }\n}\n");
    }
    let (entry, spelling) = entry_and_spelling(&ranges);
    item.entry = Some(entry);
    item.spelling = Some(spelling);
    let mut case = spec.finish(Packaging::Shared(command), &item);
    case.k7 = K7::skip(
        SkipKind::Form,
        "the twin family's base has no driver commands to set its cells up, and a claim needs a \
         prover; the relation compares a child's K with its twin's instead",
    );
    case
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_child_case_has_a_twin_or_a_stated_difference() {
        for generated in GENERATED.iter() {
            if generated.cells.is_none() {
                assert!(generated.twin.is_none() && generated.stated.is_none());
                continue;
            }
            assert!(
                generated.twin.is_some() != generated.stated.is_some(),
                "{}",
                generated.case.id
            );
            if let Some(twin) = &generated.twin {
                let twin = generated_twin(twin);
                assert!(twin.cells.is_none(), "{} twins a child", generated.case.id);
            }
        }
    }

    fn generated_twin(id: &str) -> &'static Generated {
        generated(id).unwrap_or_else(|| panic!("the twin {id} is generated"))
    }

    #[test]
    fn a_child_s_k_reads_at_its_twin_s_place() {
        let child = [
            "rule [case-TAG]:\n<k> cTAG => .K ... </k>\n<queue>\n<job>\n<jl> ListItem(V0:KItem) ... </jl>\n...\n</job>\n...\n</queue>".to_owned(),
            "syntax Stmt ::= \"cTAG\" [symbol(cmdCTAG), format(%1)]".to_owned(),
        ];
        assert_eq!(
            projection(&child, "jl", "tl"),
            Some(vec![
                "rule [case-TAG]:\n<k> cTAG => .K ... </k>\n<tl> ListItem(V0:KItem) ... </tl>"
                    .to_owned(),
                child[1].clone(),
            ])
        );
        // A holder that matches another cell than the child is no frame; one whose other cells
        // hold `_` is.
        let held = ["rule [case-TAG]:\n<k> cTAG => .K ... </k>\n<gg> <gl> L:List </gl> <gn> 0 </gn> ... </gg>".to_owned()];
        assert_eq!(projection(&held, "gl", "tl"), None);
        let open =
            ["<k> c </k>\n<gg> <gk> _ </gk> <gl> L:List </gl> <gn> _ </gn> </gg>".to_owned()];
        assert_eq!(
            projection(&open, "gl", "tl"),
            Some(vec!["<k> c </k>\n<tl> L:List </tl>".to_owned()])
        );
        // A rewrite of the whole holder that keeps its other cells is the child's rewrite.
        let whole = ["<k> c </k>\n(<og> <ok> V1:K </ok> <ol> _ </ol> </og> => <og> <ok> V1:K </ok> <ol> ListItem(V0:Int) </ol> </og>)".to_owned()];
        assert_eq!(
            projection(&whole, "ol", "tl"),
            Some(vec![
                "<k> c </k>\n<tl> _ => ListItem(V0:Int) </tl>".to_owned()
            ])
        );
    }
}

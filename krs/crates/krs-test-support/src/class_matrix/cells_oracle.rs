//! The oracle of the cell-entry families (design S5, §3): what a cell entry means, from the
//! principles of cell content (`S5-principles.md`, P0–P7) with the decisions in force, and
//! nothing else.
//!
//! A cell-entry case carries its entry as data ([`EntryCase`]): the form it is written in, its
//! side, the layers its cell's declaration gives it ([`Layer`], outermost first) as two stacks
//! kept apart, the path (the layers of the cell's `?` and `*` ancestors between the record's
//! level and the cell) and the cell's own, the entry's [`Spelling`], which holds marks and names
//! and no source text, and its rule ([`Template`]). The generator declares each spelling as a
//! value, so nothing here can branch on how a spelling is written.
//!
//! [`outcome`] answers steps 1–3 of the design's §2.3 for one entry:
//!
//! 1. **form**: what the spelling and its side alone refuse (`_`, `name @ P` and a named rest
//!    `name @ ..` in a result or an initializer, `None` or an anonymous rest in an initializer, an
//!    anonymous rest in a map literal that is lexically no content root: outside a `cells!`
//!    pattern, other than a cell entry's content in a `cells!` result, the direct argument of
//!    `Cell(..)` or the direct value of a field of a record at a configuration position);
//! 2. **kind**: P3 against the cell's own layers, outermost first: (a) the outermost layer's mark
//!    admits the entry and its inside is judged against the next layer; (b) a mark of a layer the
//!    stack has nowhere gives that mark's class; (c) a deeper layer's mark, or a value where the
//!    outermost layer has a mark, gives the missing layer's class, but only where the entry's
//!    inside passes form and kind against the deeper layers, and otherwise the inside's own
//!    refusal (P3's reason at every depth, S5.0g pattern review P-R5); a cons list's back item is
//!    refused inside the leaf's mark (P2, P-R1), the computation's inside its own (E1, in every
//!    form), and brackets on a Set or Map collection are its instance mark of the wrong order
//!    (P-R4); then the path (S1 (b)): an
//!    entry naming a cell below a `?` or `*` ancestor is refused for the outermost such ancestor,
//!    whatever it spells, since the ancestor's presence and the instance meant are written at the
//!    ancestor's level, never in the entry (a mark in the entry is the cell's own, P2). The
//!    cell's own refusal comes first for P3's reason: the path's advice writes the entry inside
//!    the ancestor's mark, so a spelling its own stack refuses would be refused again there;
//! 3. **pairing**: rests (P6), absence (P5), Q1's lint and overwrite (a result over a cell the
//!    subject does not match, [`Context::other`] `None`), Q3, and a bare `..` in a result's group
//!    record for a group that exists, matched or overwritten (P6: Rust's default fields, which
//!    only a created instance has). A result is paired at every content root it writes: its
//!    cell's, and each child's of the group and instance records it writes (P1: a child is an
//!    entry of its own cell), against the child's own other side: the subject record's same
//!    child, the same child of the subject instance an update `..me` labels (R10), an unmatched
//!    child where the subject does not name it, and none for a created instance's or `?`
//!    cell's child. An update whose label no subject instance has creates an instance where the
//!    sentence binds the label elsewhere, and has no base (`record-update-base`) where it binds
//!    it nowhere (P0, P-R3). A Map collection's instance is keyed by its first child: a created instance
//!    writes it (P5), and an update writes it, if at all, as the binder its subject matched it
//!    with (P0); otherwise `map-collection-key` (§2.3, §7).
//!
//! It answers [`Outcome::After`] where steps 1–3 admit and a value position holds a term whose
//! sort the lattice must check (step 4, the compiler's). [`rule_outcome`] answers step 5, the
//! rule-level classes, from the whole sentence, with the [`Template`] as its input.
//!
//! E1 (the computation is read from its front) is here, in every form (`computation_front`):
//! it is stated of the computation, and P3 is one judgement in every form. The other stated
//! exceptions (E3 and the stated limitations) are not here: they are `[cell-exception."GLOB"]`
//! entries of `expected.toml`, which check 1 (`tests/cells_oracle.rs`) reads, so an exception
//! that names no disagreement any more is found stale.
//!
//! **Names.** P1 makes a cell's name play no part in its entries' judgement, and steps 1–3 compare
//! names only as data: a record's head with the position's group, a binder with the names the
//! rule binds. Two branches read a name for what it says, each from its own principle:
//!
//! - `main-cell-not-k` ([`rule_outcome`], step 5) compares a computation cell's name with `k`.
//!   That is the class's own meaning, not an entry's: K takes the cell named `k` as the
//!   computation cell, so a program placed in another computation cell beside `k` is not the one
//!   K runs. It judges the whole initializer, after its entries are admitted, where P1 does not
//!   reach;
//! - a binder whose name starts with `_` binds nothing the rule can read ([`binds`]), Rust's
//!   convention for a name kept unused. Q1/S2's lint asks whether an entry binds anything; `pc:
//!   _x` binds nothing a rule reads, as `pc: _` does, so it owes the lint as `_` does.

use super::Side;

/// The form an entry is written in.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Form {
    /// A readable record (`k::rules!` with `for Machine`).
    Readable,
    /// A readable claim.
    Claim,
    /// A `cells!` rule.
    Cells,
    /// An initializer's field.
    Init,
}

/// A rest at a content root (P6).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Rest {
    /// `..`.
    Anon,
    /// `name @ ..`.
    Named(String),
    /// `..name`.
    Splice(String),
}

/// Where a sequence's rest stands: last (`[x, ..]`) or before an item (`[.., x]`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RestAt {
    /// After every item.
    Back,
    /// Before an item.
    Front,
}

/// A sequence of items with an optional rest: brackets, `KCell(..)`, `k::k![..]`, instance lists.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Seq {
    /// The items in order.
    pub items: Vec<Spelling>,
    /// The rest and where it stands; `None` for an exact sequence.
    pub rest: Option<(Rest, RestAt)>,
}

/// Map entries with an optional rest: a readable map read or a map literal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entries {
    /// The `key -> value` entries.
    pub entries: Vec<(Spelling, Spelling)>,
    /// The rest; `None` for an exact map.
    pub rest: Option<Rest>,
}

/// A record's tail.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RecordRest {
    /// No `..`: every field is named.
    Exact,
    /// `..`.
    Open,
    /// `..base`.
    Update(String),
}

/// A record `Head { field: value, .. }`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Record {
    /// The struct's name, its path's last segment.
    pub head: String,
    /// The fields in order.
    pub fields: Vec<(String, Spelling)>,
    /// The tail.
    pub rest: RecordRest,
}

/// A cell entry's spelling as data: its marks, its names, and the values it holds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Spelling {
    /// `_`.
    Wild,
    /// A binder, `x`; whether it is fresh is the rule's ([`Context::bound`]).
    Binder(String),
    /// A literal, `0`, with its text where it is declared (two literals are provably equal only
    /// when both texts are known and the same).
    Literal(Option<String>),
    /// A function application or a constructor term, with its arguments.
    Call(Vec<Self>),
    /// A configuration variable in an initializer, `pgm`.
    ConfigVar(String),
    /// `Some(..)`.
    Present(Box<Self>),
    /// `None`.
    Missing,
    /// `k::absent!(..)` in an initializer.
    Absent(Box<Self>),
    /// Readable brackets, `[x, ..]` (also inside `Cell(..)` and in an initializer).
    Brackets(Seq),
    /// Readable instance braces, `{ Obj { .. }, .. }`.
    Braces(Seq),
    /// A readable map read, `{ k -> v, .. }`.
    MapRead(Entries),
    /// A record, `Frame { ret: x }`.
    Record(Record),
    /// `name @ pattern`.
    Alias(String, Box<Self>),
    /// `k::configuration::Cell(..)`.
    Cell(Box<Self>),
    /// `k::configuration::KCell(..)`.
    KCell(Seq),
    /// `k::fragment![crate::G { .. }]`.
    Fragment(Record),
    /// A `cells!` List instance list, `[k::fragment![..], rest @ ..]`.
    InstList(Seq),
    /// A `cells!` Set or Map instance set, `{ k::fragment![..], rest @ .. }`.
    InstSet(Seq),
    /// A map literal, `k::map![..]` or readable `map![..]`.
    MapLit(Entries),
    /// `k::k![..]`.
    KMacro(Seq),
}

/// How a collection orders its instances.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Order {
    /// `cell_type = "List"`.
    List,
    /// `cell_type = "Set"`.
    Set,
    /// `cell_type = "Map"`.
    Map,
}

/// What notation the content of a leaf has inside its value (P2's "inside a leaf").
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Notation {
    /// A sort with no notation of its own (`Int`, a user sort, `KItem`).
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

/// A group: its struct's name and its children's stacks, in declaration order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Group {
    /// The struct's name.
    pub name: String,
    /// Each child's name and stack.
    pub children: Vec<(String, Vec<Layer>)>,
}

/// One layer of a cell's declared stack (P1).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Layer {
    /// `multiplicity = "?"`.
    Optional,
    /// `multiplicity = "*"`.
    Instances(Order),
    /// A computation, a `KSequence`.
    Computation,
    /// A leaf of a sort.
    Leaf(Notation),
    /// A group of cells.
    Group(Group),
}

/// What a sentence is, for its rule-level checks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Sentence {
    /// A rule (readable or `cells!`).
    Rule,
    /// A claim.
    Claim,
    /// An initializer.
    Initializer,
    /// A one-sided `cells!` pattern the sentence keeps as it matched it: an equation's function
    /// context, which the equation reads, a context alias, the frame of every context it makes,
    /// and a context's cells around its hole. It changes nothing, so it means what a rule with
    /// that pattern on both sides means (P0): its entries are subject entries over cells the
    /// sentence keeps, as a rule keeps a cell its result leaves out (P5), so each is paired with
    /// no other side and the result not writing its cell ([`Context::other`] `None`,
    /// [`Context::written`] false). No rule-level class but an overlap of its entries is about
    /// it.
    Context,
}

/// One entry of a sentence: its cell, its side, its stacks and its spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entry {
    /// The cell's name.
    pub cell: String,
    /// The side it stands on.
    pub side: Side,
    /// The layers of the cell's `?` and `*` ancestors between the record's level and the cell,
    /// outermost first (a plain group adds none); empty for a cell named at its own level.
    pub path: Vec<Layer>,
    /// The cell's own stack.
    pub stack: Vec<Layer>,
    /// The entry.
    pub spelling: Spelling,
}

/// The rule a case's entry stands in: its other entries, its guard, and the configuration
/// variables an initializer declares.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Template {
    /// What the sentence is.
    pub sentence: Sentence,
    /// Every entry but the case's own.
    pub entries: Vec<Entry>,
    /// Whether the sentence has a condition.
    pub guard: bool,
    /// An initializer's configuration variables, each with whether it is the main one (the
    /// program's).
    pub variables: Vec<(String, bool)>,
}

/// What a case's entry is judged with besides its stack: the names the rule binds elsewhere,
/// the other side's entry of the same cell, and whether the result writes the cell.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Context {
    /// Names the rule binds outside the entry (a result's binders are bound).
    pub bound: Vec<String>,
    /// What the names of [`Self::bound`] bind, where it is a record: each name an alias binds to
    /// a record (`me @ Acct { .. }`, or its fragment), with the record's head constructor. A
    /// bound name not listed binds no record: a list element, a leaf value, a map value (P6: an
    /// update `..me` takes the fields of a record of its own constructor).
    pub records: Vec<(String, String)>,
    /// For a result, the subject's entry of the same cell: whether the subject matches the cell
    /// at all, and if so what it spells. `None` on a result is an unmatched cell, which the
    /// result overwrites (Q1). For a subject, the result's entry of the same cell, where the
    /// result writes it and the case states it (`None`: no result entry is known), which says
    /// whether the result creates a `?` child the subject tests absent (P5).
    pub other: Option<Spelling>,
    /// For a subject entry, whether the result writes the cell.
    pub written: bool,
    /// The configuration's groups ([`collect_groups`]): a record a term writes by a group's
    /// name has that group's children as its fields (P6).
    pub groups: Vec<Group>,
}

/// A cell-entry case as the oracle reads it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EntryCase {
    /// The form.
    pub form: Form,
    /// The case's own entry.
    pub entry: Entry,
    /// Its context.
    pub context: Context,
    /// The sentence it stands in.
    pub template: Template,
}

/// What steps 1–3 answer for one entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Outcome {
    /// Admitted, with the lint it owes (Q1's `no-effect-entry`).
    Admit {
        /// The lint class, if any.
        lint: Option<&'static str>,
    },
    /// Admitted by steps 1–3; a value's sort is the lattice's to judge (step 4).
    After,
    /// Refused with this class.
    Refuse(&'static str),
}

impl Outcome {
    /// Whether steps 1–3 admit the entry.
    #[must_use]
    pub const fn admits(self) -> bool {
        !matches!(self, Self::Refuse(_))
    }
}

/// Which step of the kind judgement refused (P3), or another step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Step {
    /// Step 1, the form.
    Form,
    /// P3 (b): a mark of a layer the stack has nowhere.
    MarkElsewhere,
    /// P3 (c): a deeper layer's mark, or a value where the outermost layer has a mark.
    MissingLayer,
    /// S1 (b): the entry names a cell below a `?` or `*` ancestor (after the cell's own kind).
    Path,
    /// Inside a layer's mark (a leaf's notation, an instance's shape, Q3).
    Inside,
    /// Step 3, pairing.
    Pairing,
}

/// A refusal with where it was met: the step, and the depth of the refused node below the
/// entry's head (0 for the head).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Refusal {
    /// The class.
    pub class: &'static str,
    /// The step that refused.
    pub step: Step,
    /// The refused node's depth below the head.
    pub depth: usize,
}

/// The lint a subject entry that constrains nothing owes (Q1).
pub const NO_EFFECT_ENTRY: &str = "no-effect-entry";

/// The classes [`outcome`] answers with.
pub const ENTRY_CLASSES: [&str; 23] = [
    "absence-test-without-creation",
    "alias-outside-pattern",
    "anonymous-rest-in-map-literal",
    "bracket-reading",
    "cell-wrapper",
    "collection-without-instances",
    "computation-back-item",
    "cons-list-back-item",
    "continuation-in-readable",
    "initializer-remainder",
    "instance-list-shape",
    "instances-on-plain-cell",
    "map-collection-key",
    "map-notation-at-non-map",
    "none-in-initializer",
    "open-record-outside-pattern",
    "optional-without-presence",
    "presence-on-plain-cell",
    "record-missing-children",
    "record-update-base",
    "rest-mismatch",
    "unmatched-optional-result",
    "wildcard-outside-pattern",
];

/// The classes [`rule_outcome`] answers with: they judge the whole sentence.
pub const RULE_CLASSES: [&str; 5] = [
    "always-enabled-rule",
    "group-and-descendant",
    "main-cell-not-k",
    "rule-changes-no-cell",
    "unused-configuration-variable",
];

/// The lint classes [`outcome`] answers with.
pub const LINT_CLASSES: [&str; 1] = [NO_EFFECT_ENTRY];

/// The code each class of [`ENTRY_CLASSES`], [`RULE_CLASSES`] and [`LINT_CLASSES`] answers with,
/// which `expected.toml` must declare alike (check 0).
pub const CODES: [(&str, &str); 29] = [
    (
        "absence-test-without-creation",
        "krs::analysis::optional-presence",
    ),
    ("alias-outside-pattern", "krs::syntax::invalid-pattern-as"),
    ("always-enabled-rule", "krs::analysis::always-enabled-rule"),
    (
        "anonymous-rest-in-map-literal",
        "krs::syntax::invalid-expression-notation",
    ),
    ("bracket-reading", "krs::analysis::invalid-list-notation"),
    ("cell-wrapper", "krs::analysis::cell-wrapper"),
    (
        "collection-without-instances",
        "krs::analysis::collection-entry",
    ),
    (
        "computation-back-item",
        "krs::collect::invalid-configuration",
    ),
    (
        "cons-list-back-item",
        "krs::analysis::invalid-list-notation",
    ),
    (
        "continuation-in-readable",
        "krs::analysis::continuation-in-readable",
    ),
    (
        "group-and-descendant",
        "krs::analysis::group-and-descendant",
    ),
    (
        "initializer-remainder",
        "krs::syntax::unsupported-initializer-body",
    ),
    ("instance-list-shape", "krs::analysis::collection-entry"),
    ("instances-on-plain-cell", "krs::analysis::collection-entry"),
    ("main-cell-not-k", "krs::analysis::main-cell"),
    ("map-collection-key", "krs::analysis::map-collection-key"),
    ("map-notation-at-non-map", "krs::analysis::invalid-term"),
    (NO_EFFECT_ENTRY, "krs::analysis::no-effect-entry"),
    (
        "none-in-initializer",
        "krs::syntax::unsupported-initializer-body",
    ),
    (
        "open-record-outside-pattern",
        "krs::syntax::invalid-record-update",
    ),
    (
        "optional-without-presence",
        "krs::analysis::optional-presence",
    ),
    ("presence-on-plain-cell", "krs::analysis::optional-presence"),
    (
        "record-missing-children",
        "krs::analysis::record-missing-children",
    ),
    ("record-update-base", "krs::analysis::invalid-record-update"),
    ("rest-mismatch", "krs::syntax::invalid-list-notation"),
    (
        "rule-changes-no-cell",
        "krs::analysis::rule-changes-no-cell",
    ),
    (
        "unmatched-optional-result",
        "krs::analysis::optional-presence",
    ),
    (
        "unused-configuration-variable",
        "krs::analysis::unused-configuration-variable",
    ),
    (
        "wildcard-outside-pattern",
        "krs::syntax::unsupported-term-expression",
    ),
];

/// The sort classes: the lattice's (step 4), which [`Outcome::After`] leaves to the compiler.
pub const SORT_CLASSES: [&str; 5] = [
    "binder-sort",
    "collection-element-sort",
    "configuration-variable-sort",
    "content-sort",
    "list-notation-sort",
];

/// The readable refusals whose `cells!` abbreviation may be admitted (check 3 (ii)): Q3 (a
/// `cells!`-only spelling, which P7 allows), and a map literal's `..`, which readable writes with
/// its own mark, `{ k -> v, .. }` (P2).
pub const READABLE_ONLY: [&str; 2] = ["anonymous-rest-in-map-literal", "continuation-in-readable"];

/// The marks of P2, per form.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Mark {
    /// `Some`/`None`/`k::absent!`.
    Presence,
    /// Brackets (readable and initializer; a sequence inside `Cell(..)`).
    Seq,
    /// Instance braces.
    SetInst,
    /// A `cells!` instance list.
    ListInst,
    /// Map notation.
    Map,
    /// `Cell(..)`.
    Leaf,
    /// `KCell(..)`, `k::k![..]`.
    Comp,
    /// No mark: a value.
    Value,
}

/// The mark `spelling` carries in `form`; `inside_leaf` reads it inside `Cell(..)`.
#[must_use]
pub const fn mark(form: Form, spelling: &Spelling, inside_leaf: bool) -> Mark {
    match spelling {
        Spelling::Present(_) | Spelling::Missing | Spelling::Absent(_) => Mark::Presence,
        _ if inside_leaf => match spelling {
            Spelling::Brackets(_) => Mark::Seq,
            Spelling::MapLit(_) => Mark::Map,
            _ => Mark::Value,
        },
        Spelling::Cell(_) if matches!(form, Form::Cells) => Mark::Leaf,
        Spelling::KCell(_) if matches!(form, Form::Cells) => Mark::Comp,
        Spelling::InstList(_) if matches!(form, Form::Cells) => Mark::ListInst,
        Spelling::InstSet(_) if matches!(form, Form::Cells) => Mark::SetInst,
        Spelling::KMacro(_) if matches!(form, Form::Init) => Mark::Comp,
        Spelling::Brackets(_) if !matches!(form, Form::Cells) => Mark::Seq,
        Spelling::MapLit(_) if matches!(form, Form::Init) => Mark::Map,
        Spelling::Braces(_) if matches!(form, Form::Readable | Form::Claim) => Mark::SetInst,
        Spelling::MapRead(_) if matches!(form, Form::Readable | Form::Claim) => Mark::Map,
        _ => Mark::Value,
    }
}

/// Whether `layer`'s mark in `form` is `mark` (P2).
#[must_use]
pub const fn admits(form: Form, layer: &Layer, mark: Mark) -> bool {
    match layer {
        Layer::Optional => matches!(mark, Mark::Presence),
        Layer::Instances(Order::Set | Order::Map) => matches!(mark, Mark::SetInst),
        Layer::Instances(Order::List) => match form {
            Form::Cells => matches!(mark, Mark::ListInst),
            _ => matches!(mark, Mark::Seq),
        },
        Layer::Computation => {
            matches!(mark, Mark::Comp)
                || (matches!(mark, Mark::Seq) && !matches!(form, Form::Cells))
        }
        Layer::Leaf(notation) => match form {
            Form::Cells => matches!(mark, Mark::Leaf),
            _ => {
                (matches!(mark, Mark::Seq) && matches!(notation, Notation::List | Notation::Cons))
                    || (matches!(mark, Mark::Map) && matches!(notation, Notation::Map))
            }
        },
        Layer::Group(_) => false,
    }
}

/// Whether `layer` has a mark of its own in `form`: a group never, a leaf only in `cells!`.
#[must_use]
pub const fn has_mark(form: Form, layer: &Layer) -> bool {
    match layer {
        Layer::Optional | Layer::Instances(_) | Layer::Computation => true,
        Layer::Leaf(_) => matches!(form, Form::Cells),
        Layer::Group(_) => false,
    }
}

/// The class of a missing layer (P3 c).
#[must_use]
pub const fn missing(layer: &Layer) -> &'static str {
    match layer {
        Layer::Optional => "optional-without-presence",
        Layer::Instances(_) => "collection-without-instances",
        Layer::Computation | Layer::Leaf(_) | Layer::Group(_) => "cell-wrapper",
    }
}

/// The class of a mark no layer of `stack` has (P3 b).
fn mark_elsewhere(mark: Mark, stack: &[Layer]) -> &'static str {
    match mark {
        Mark::Presence => "presence-on-plain-cell",
        // P2, P3b: brackets are a List collection's instance mark, so on a cell whose instance
        // layer is a Set or a Map they are its instance mark of the wrong order (S5.0g pattern
        // review P-R4), whatever they hold; on a cell with no instance layer they denote nothing.
        Mark::Seq
            if stack
                .iter()
                .any(|layer| matches!(layer, Layer::Instances(_))) =>
        {
            "instance-list-shape"
        }
        Mark::Seq => "bracket-reading",
        Mark::SetInst | Mark::ListInst => {
            if stack
                .iter()
                .any(|layer| matches!(layer, Layer::Instances(_)))
            {
                "instance-list-shape"
            } else {
                "instances-on-plain-cell"
            }
        }
        Mark::Map => "map-notation-at-non-map",
        Mark::Leaf | Mark::Comp | Mark::Value => "cell-wrapper",
    }
}

/// The spellings directly inside `spelling`.
#[must_use]
pub fn children(spelling: &Spelling) -> Vec<&Spelling> {
    match spelling {
        Spelling::Present(inner) | Spelling::Absent(inner) | Spelling::Cell(inner) => {
            vec![inner]
        }
        Spelling::Alias(_, inner) => vec![inner],
        Spelling::Brackets(seq)
        | Spelling::Braces(seq)
        | Spelling::KCell(seq)
        | Spelling::InstList(seq)
        | Spelling::InstSet(seq)
        | Spelling::KMacro(seq) => seq.items.iter().collect(),
        Spelling::MapRead(entries) | Spelling::MapLit(entries) => entries
            .entries
            .iter()
            .flat_map(|(key, value)| [key, value])
            .collect(),
        Spelling::Record(record) | Spelling::Fragment(record) => {
            record.fields.iter().map(|(_, value)| value).collect()
        }
        Spelling::Call(arguments) => arguments.iter().collect(),
        Spelling::Wild
        | Spelling::Binder(_)
        | Spelling::Literal(_)
        | Spelling::ConfigVar(_)
        | Spelling::Missing => Vec::new(),
    }
}

/// A content root's rest, as P6 pairs it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Root {
    /// A sequence or map without a rest.
    Exact,
    /// A rest.
    Rest(Rest),
    /// A binder for the whole content.
    Whole,
    /// Any other value.
    Value,
}

/// The rest of `spelling`'s content root, below presence and the leaf wrapper.
#[must_use]
pub fn root(spelling: &Spelling) -> Root {
    match spelling {
        Spelling::Present(inner) | Spelling::Cell(inner) | Spelling::Alias(_, inner) => root(inner),
        Spelling::Brackets(seq)
        | Spelling::Braces(seq)
        | Spelling::KCell(seq)
        | Spelling::InstList(seq)
        | Spelling::InstSet(seq)
        | Spelling::KMacro(seq) => seq
            .rest
            .as_ref()
            .map_or(Root::Exact, |(rest, _)| Root::Rest(rest.clone())),
        Spelling::MapRead(entries) | Spelling::MapLit(entries) => entries
            .rest
            .as_ref()
            .map_or(Root::Exact, |rest| Root::Rest(rest.clone())),
        Spelling::Binder(_) => Root::Whole,
        _ => Root::Value,
    }
}

fn sequence(spelling: &Spelling) -> Option<(usize, Option<&Rest>)> {
    match spelling {
        Spelling::Brackets(seq)
        | Spelling::Braces(seq)
        | Spelling::KCell(seq)
        | Spelling::InstList(seq)
        | Spelling::InstSet(seq)
        | Spelling::KMacro(seq) => Some((seq.items.len(), seq.rest.as_ref().map(|(rest, _)| rest))),
        Spelling::MapRead(entries) | Spelling::MapLit(entries) => {
            Some((entries.entries.len(), entries.rest.as_ref()))
        }
        _ => None,
    }
}

/// Whether `spelling` matches every content `stack` allows (Q1, R9), from its marks: `_` and a
/// binder; `x @ p` as `p`; `Cell(p)` as `p`; a sequence, map or instance list with no item and a
/// rest; a group record or fragment of the position's group whose named children all do. A
/// presence mark, a literal, a call and any item constrain; so does a constructor pattern, even
/// of a sort with one constructor, since telling that needs the lattice.
#[must_use]
pub fn total(spelling: &Spelling, stack: &[Layer]) -> bool {
    match spelling {
        Spelling::Wild | Spelling::Binder(_) => true,
        Spelling::Alias(_, inner) | Spelling::Cell(inner) => total(inner, stack),
        Spelling::Record(record) | Spelling::Fragment(record) => {
            let Some(Layer::Group(group)) = stack.first() else {
                return false;
            };
            if group.name != record.head {
                return false;
            }
            if record.rest == RecordRest::Exact && !names_every_field(record, group) {
                return false;
            }
            record.fields.iter().all(|(name, value)| {
                child(group, name).is_some_and(|child_stack| total(value, child_stack))
            })
        }
        _ => sequence(spelling).is_some_and(|(items, rest)| {
            items == 0 && matches!(rest, Some(Rest::Anon | Rest::Named(_)))
        }),
    }
}

/// Whether `spelling` binds a name the rule can read (a name starting with `_` reads nothing).
#[must_use]
pub fn binds(spelling: &Spelling) -> bool {
    match spelling {
        Spelling::Binder(name) => !name.starts_with('_'),
        Spelling::Alias(..) => true,
        _ => {
            matches!(sequence(spelling), Some((_, Some(Rest::Named(name)))) if !name.starts_with('_'))
                || children(spelling).into_iter().any(binds)
        }
    }
}

/// Whether `spelling` names the configuration variable `name`: as a value, or as the base a
/// value is built on (P5, D2 #8): a computation's, list's, map's or instance sequence's `..name`
/// and a record update's `..name` use the variable exactly as an item `name` would.
#[must_use]
pub fn mentions(spelling: &Spelling, name: &str) -> bool {
    let base = match spelling {
        Spelling::ConfigVar(variable) => return variable == name,
        Spelling::Brackets(seq)
        | Spelling::Braces(seq)
        | Spelling::KCell(seq)
        | Spelling::InstList(seq)
        | Spelling::InstSet(seq)
        | Spelling::KMacro(seq) => match &seq.rest {
            Some((Rest::Splice(variable), _)) => Some(variable),
            _ => None,
        },
        Spelling::MapRead(entries) | Spelling::MapLit(entries) => match &entries.rest {
            Some(Rest::Splice(variable)) => Some(variable),
            _ => None,
        },
        Spelling::Record(record) | Spelling::Fragment(record) => match &record.rest {
            RecordRest::Update(variable) => Some(variable),
            _ => None,
        },
        _ => None,
    };
    base.is_some_and(|variable| variable == name)
        || children(spelling)
            .into_iter()
            .any(|inner| mentions(inner, name))
}

/// The child that keys an instance of `group` in a collection ordered by `order`: a Map
/// collection's instance is keyed by its first child, its declaration's first field (the
/// instance's identity); a List or Set collection's instance has none.
fn key(order: Order, group: &Group) -> Option<&str> {
    match order {
        Order::Map => group.children.first().map(|(name, _)| name.as_str()),
        Order::List | Order::Set => None,
    }
}

fn child<'g>(group: &'g Group, name: &str) -> Option<&'g Vec<Layer>> {
    group
        .children
        .iter()
        .find(|(child, _)| child == name)
        .map(|(_, stack)| stack)
}

/// L4 (P6: records follow Rust): a record of `group` at a configuration position, or the
/// fragment it abbreviates (P7), names every child, or writes `..`.
fn names_every_child(record: &Record, group: &Group, depth: usize) -> Result<(), Refusal> {
    if record.rest == RecordRest::Exact && !names_every_field(record, group) {
        return refuse("record-missing-children", Step::Inside, depth);
    }
    Ok(())
}

/// Whether `record`, a record of `group`, names each of the group's children.
fn names_every_field(record: &Record, group: &Group) -> bool {
    record.fields.len() == group.children.len()
}

/// Whether `record`, a record of `group`, writes a bare `..` that leaves a child unnamed (P6:
/// a bare `..` in a built record is Rust's default fields). A `..` after every child defaults
/// none: Rust and K then read the same exact record, so P0 refuses nothing.
fn leaves_open(record: &Record, group: &Group) -> bool {
    record.rest == RecordRest::Open && !names_every_field(record, group)
}

/// Adds to `groups` each group `layers` hold, at any depth (a group's children's included),
/// once by name: a configuration's groups, as [`Context::groups`] holds them.
pub fn collect_groups(layers: &[Layer], groups: &mut Vec<Group>) {
    for layer in layers {
        if let Layer::Group(group) = layer {
            if !groups.iter().any(|known| known.name == group.name) {
                groups.push(group.clone());
            }
            for (_, child) in &group.children {
                collect_groups(child, groups);
            }
        }
    }
}

/// Where a spelling stands, read lexically (P1, P6): whether at a configuration position, and
/// whether as a cell entry's content there, its content root.
///
/// The entry's head stands at a position. A record or fragment at a position is the record of
/// its group or instance, so each field's direct value is its child cell's entry (P1), which no
/// wrapper marks: that value, below `Some(..)` and an alias, is the child's content, at a
/// position. An instance list's or set's items at a position are instance records, at a
/// position. `Cell(..)`'s argument is its leaf's content. Anywhere else, a list's element, a
/// map's entry, a constructor's or a call's argument, a spelling is a term's part (P6: below a
/// root, notation is a term's).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Place {
    /// At a configuration position.
    position: bool,
    /// A cell entry's content: a content root (P6).
    root: bool,
}

impl Place {
    /// The entry's head: at a position, and its content is inside its own mark.
    const HEAD: Self = Self {
        position: true,
        root: false,
    };

    /// Where the spellings directly inside `spelling`, standing here, stand.
    const fn inside(self, spelling: &Spelling) -> Self {
        match spelling {
            Spelling::Cell(_) => Self {
                position: false,
                root: true,
            },
            Spelling::Present(_) | Spelling::Absent(_) | Spelling::Alias(..) => self,
            Spelling::Record(_) | Spelling::Fragment(_) if self.position => Self {
                position: true,
                root: true,
            },
            Spelling::InstList(_) | Spelling::InstSet(_) if self.position => Self {
                position: true,
                root: false,
            },
            _ => Self {
                position: false,
                root: false,
            },
        }
    }
}

/// One entry's judgement: what refused it, and whether a value's sort is the lattice's.
struct Judge<'c> {
    form: Form,
    side: Side,
    context: &'c Context,
    sort: bool,
}

const fn refuse(class: &'static str, step: Step, depth: usize) -> Result<(), Refusal> {
    Err(Refusal { class, step, depth })
}

impl Judge<'_> {
    /// Step 1: what the spelling and its side alone refuse, read lexically (P4): `place` tells
    /// where `spelling` stands ([`Place`]).
    fn form_step(&self, spelling: &Spelling, depth: usize, place: Place) -> Result<(), Refusal> {
        let initializer = self.side == Side::Initializer;
        match spelling {
            Spelling::Wild if matches!(self.side, Side::Result | Side::Initializer) => {
                return refuse("wildcard-outside-pattern", Step::Form, depth);
            }
            Spelling::Missing if initializer => {
                return refuse("none-in-initializer", Step::Form, depth);
            }
            // §2.3 step 1: `name @ P` names what a pattern matched, so it stands in a pattern
            // only, at any depth, and a rest is no exception. A result keeps the subject's
            // anonymous rest with `..` and puts a named one back with `..name` (P6); the subject
            // drops a rest by naming it `_rest @ ..` and not putting it back. An initializer is a
            // result with no subject (P5): nothing in it is a pattern, and `..base` updates.
            _ if matches!(self.side, Side::Result | Side::Initializer)
                && (matches!(spelling, Spelling::Alias(..))
                    || matches!(sequence(spelling), Some((_, Some(Rest::Named(_)))))) =>
            {
                return refuse("alias-outside-pattern", Step::Form, depth);
            }
            // P5: an initializer's value is complete.
            Spelling::KMacro(seq) | Spelling::Brackets(seq)
                if initializer && matches!(seq.rest, Some((Rest::Anon, _))) =>
            {
                return refuse("initializer-remainder", Step::Form, depth);
            }
            // P6: `..` is K's `...` at a content root only; below a root, notation is a term's,
            // and a term's `..` names no map. A `cells!` map literal is lexically a content root
            // where it is a cell entry's content ([`Place::root`]), in a subject (where every map
            // a pattern writes is matched) and in a result alike: whether its `..` keeps a rest
            // is pairing's (P4: it needs the declaration and the other side; S5.0g pattern review
            // P-R2, and the fixes review's F-1 for a record's child). A readable `map![..]` is a
            // literal everywhere: readable writes a map's root as `{ k -> v, .. }` (P2).
            Spelling::MapLit(entries)
                if entries.rest == Some(Rest::Anon)
                    && !(self.form == Form::Cells
                        && (self.side == Side::Subject
                            || (self.side == Side::Result && place.root))) =>
            {
                return refuse("anonymous-rest-in-map-literal", Step::Form, depth);
            }
            _ => {}
        }
        let inner = place.inside(spelling);
        for one in children(spelling) {
            self.form_step(one, depth + 1, inner)?;
        }
        Ok(())
    }

    /// Step 2: P3 against `stack`, recursively.
    fn judge(&mut self, stack: &[Layer], spelling: &Spelling, depth: usize) -> Result<(), Refusal> {
        if let Spelling::Alias(_, inner) = spelling {
            return self.judge(stack, inner, depth + 1);
        }
        let Some(outer) = stack.first() else {
            return self.value(spelling, depth);
        };
        // P5: an initializer's value for a `*` cell, at any depth (a collection child of a
        // template included), is one instance's template.
        if self.side == Side::Initializer && matches!(outer, Layer::Instances(_)) {
            return self.judge(&stack[1..], spelling, depth);
        }
        let mark = mark(self.form, spelling, false);
        if mark != Mark::Value {
            if admits(self.form, outer, mark) {
                return self.inside(stack, spelling, depth);
            }
            if stack[1..]
                .iter()
                .any(|layer| admits(self.form, layer, mark))
            {
                return self.missing_layer(stack, spelling, depth);
            }
            return refuse(mark_elsewhere(mark, stack), Step::MarkElsewhere, depth);
        }
        if has_mark(self.form, outer) {
            return self.missing_layer(stack, spelling, depth);
        }
        if let Layer::Group(group) = outer {
            return self.group_value(group, spelling, depth);
        }
        self.value(spelling, depth)
    }

    /// P3 (c), with P3's reason at every depth (S5.0g pattern review P-R5): `stack`'s outermost
    /// layer is missing from the entry, which is refused for it only where its inside passes
    /// form and kind against the deeper layers, `stack[1..]`, every other layer the advice must
    /// add included; otherwise the advice would be refused again there, so the inside's own
    /// refusal is named. An inside missing only further layers passes: the advice adds them
    /// too.
    fn missing_layer(
        &mut self,
        stack: &[Layer],
        spelling: &Spelling,
        depth: usize,
    ) -> Result<(), Refusal> {
        match self.judge(&stack[1..], spelling, depth) {
            Err(inside) if !(inside.step == Step::MissingLayer && inside.depth == depth) => {
                Err(inside)
            }
            _ => refuse(missing(&stack[0]), Step::MissingLayer, depth),
        }
    }

    /// A value at a group's position: a record of the group names its children's entries (P1);
    /// a fragment of the group is a term the lattice judges, which names the children as the
    /// record it abbreviates does (P7), its own `..` and its children's records paired as the
    /// record's are; any other value is a term.
    fn group_value(
        &mut self,
        group: &Group,
        spelling: &Spelling,
        depth: usize,
    ) -> Result<(), Refusal> {
        let record = match spelling {
            Spelling::Record(record) if record.head == group.name => record,
            Spelling::Fragment(record) if record.head == group.name => {
                self.sort = true;
                self.fragment_terms(group, record, depth)?;
                return names_every_child(record, group, depth);
            }
            _ => return self.value(spelling, depth),
        };
        for (name, value) in &record.fields {
            let stack = child(group, name).unwrap_or_else(|| {
                panic!("the record of `{}` names its child `{name}`", group.name)
            });
            self.judge(stack, value, depth + 1)?;
        }
        names_every_child(record, group, depth)
    }

    /// Inside the outermost layer's mark.
    fn inside(
        &mut self,
        stack: &[Layer],
        spelling: &Spelling,
        depth: usize,
    ) -> Result<(), Refusal> {
        let rest = &stack[1..];
        match spelling {
            Spelling::Present(inner) | Spelling::Absent(inner) => {
                return self.judge(rest, inner, depth + 1);
            }
            Spelling::Missing => return Ok(()),
            Spelling::Cell(inner) => {
                let Layer::Leaf(notation) = stack[0] else {
                    unreachable!("only a leaf's mark is `Cell`")
                };
                match (mark(self.form, inner, true), &**inner) {
                    (Mark::Seq, Spelling::Brackets(seq)) => {
                        if !matches!(notation, Notation::List | Notation::Cons) {
                            return refuse("bracket-reading", Step::Inside, depth + 1);
                        }
                        cons_front(notation, seq, depth + 1)?;
                        for item in &seq.items {
                            self.value(item, depth + 2)?;
                        }
                    }
                    (Mark::Map, Spelling::MapLit(entries)) => {
                        if notation != Notation::Map {
                            return refuse("map-notation-at-non-map", Step::Inside, depth + 1);
                        }
                        for (key, value) in &entries.entries {
                            self.value(key, depth + 2)?;
                            self.value(value, depth + 2)?;
                        }
                    }
                    _ => self.value(inner, depth + 1)?,
                }
                return Ok(());
            }
            _ => {}
        }
        if let Layer::Instances(order) = stack[0] {
            let Some((items, _)) = seq_of(spelling) else {
                unreachable!("an instance layer's mark is a sequence")
            };
            for item in items {
                let base = match item {
                    Spelling::Alias(_, inner) => inner,
                    other => other,
                };
                match (base, &rest[0]) {
                    (Spelling::Record(_) | Spelling::Fragment(_), Layer::Group(group)) => {
                        self.group_value(group, base, depth + 2)?;
                    }
                    // Q2: one instance of an ordered collection is a value (its front one).
                    _ if order == Order::List => self.value(base, depth + 1)?,
                    // Q2: an unordered collection's instance is chosen by a written record.
                    _ => return refuse("instance-list-shape", Step::Inside, depth + 1),
                }
            }
            return Ok(());
        }
        match spelling {
            Spelling::MapRead(entries) | Spelling::MapLit(entries) => {
                for (key, value) in &entries.entries {
                    self.value(key, depth + 1)?;
                    self.value(value, depth + 1)?;
                }
            }
            _ => {
                if let (Layer::Leaf(notation), Spelling::Brackets(seq)) = (&stack[0], spelling) {
                    cons_front(*notation, seq, depth)?;
                }
                if let Some((items, seq_rest)) = seq_of(spelling) {
                    for item in items {
                        self.value(item, depth + 1)?;
                    }
                    // Q3: a readable rule never drops or captures the continuation.
                    if stack[0] == Layer::Computation
                        && matches!(self.form, Form::Readable | Form::Claim)
                        && matches!(seq_rest, Some(Rest::Named(_) | Rest::Splice(_)))
                    {
                        return refuse("continuation-in-readable", Step::Inside, depth);
                    }
                }
                computation_front(&stack[0], spelling, depth)?;
            }
        }
        Ok(())
    }

    /// A value at a value position: a fresh readable binder and `_` take the position's sort;
    /// everything else, a bound binder and every `cells!` binder (whose parameter is typed)
    /// included, is the lattice's (step 4). In a result, a value is a built term, and a record
    /// in it whose bare `..` leaves a field open is refused: Rust's default fields, which only
    /// a created instance has (its template), and a term's record is no instance (P6). A `..`
    /// after every field defaults none (P0). That is the record's shape, known from the
    /// declaration, so it comes before the sort (P4).
    fn value(&mut self, spelling: &Spelling, depth: usize) -> Result<(), Refusal> {
        match spelling {
            Spelling::Wild => {}
            Spelling::Binder(name) => {
                if self.form == Form::Cells || self.context.bound.contains(name) {
                    self.sort = true;
                }
            }
            Spelling::Alias(_, inner) => return self.value(inner, depth + 1),
            _ => self.sort = true,
        }
        if self.side == Side::Result && open_record(spelling, &self.context.groups) {
            return refuse("open-record-outside-pattern", Step::Inside, depth);
        }
        Ok(())
    }

    /// The terms inside a result's fragment of `group`, whose children are terms the lattice
    /// judges (P7): a child's own group record (or fragment), a `?` child's `Some(..)` and a
    /// collection child's instance records are its cell's records, whose `..` pairing judges;
    /// every other value is a term ([`Self::value`]'s open record).
    fn fragment_terms(&self, group: &Group, record: &Record, depth: usize) -> Result<(), Refusal> {
        if self.side != Side::Result {
            return Ok(());
        }
        for (name, value) in &record.fields {
            if let Some(stack) = child(group, name) {
                self.cell_terms(stack, value, depth + 1)?;
            }
        }
        Ok(())
    }

    fn cell_terms(
        &self,
        stack: &[Layer],
        spelling: &Spelling,
        depth: usize,
    ) -> Result<(), Refusal> {
        let spelling = unaliased(spelling);
        match (stack, spelling) {
            ([Layer::Group(group), ..], _) if record_of(spelling, group).is_some() => {
                let record = record_of(spelling, group).expect("a record of the group");
                self.fragment_terms(group, record, depth)
            }
            ([Layer::Optional, below @ ..], Spelling::Present(inner)) => {
                self.cell_terms(below, inner, depth + 1)
            }
            ([Layer::Instances(_), Layer::Group(group), ..], _) if seq_of(spelling).is_some() => {
                let (items, _) = seq_of(spelling).expect("an instance sequence");
                for item in items {
                    match record_of(item, group) {
                        Some(record) => self.fragment_terms(group, record, depth + 1)?,
                        None if open_record(item, &self.context.groups) => {
                            return refuse("open-record-outside-pattern", Step::Inside, depth + 1);
                        }
                        None => {}
                    }
                }
                Ok(())
            }
            _ if open_record(spelling, &self.context.groups) => {
                refuse("open-record-outside-pattern", Step::Inside, depth)
            }
            _ => Ok(()),
        }
    }

    /// Step 3: pairing the entry with its rule (P5, P6, Q1).
    fn pair(&self, stack: &[Layer], spelling: &Spelling) -> Result<Option<&'static str>, Refusal> {
        match self.side {
            Side::Subject => {
                // P5 at every depth (P1: a record's child is an entry of its own cell, S5.0g
                // item 3b ruling 2): a `?` child the subject tests absent needs the result to
                // create it.
                if absence_uncreated(stack, spelling, self.context.other.as_ref()) {
                    refuse("absence-test-without-creation", Step::Pairing, 0)?;
                }
                if self.context.written {
                    return Ok(None);
                }
                if *spelling == Spelling::Missing {
                    // P5: K tests absence only by creating the cell.
                    refuse("absence-test-without-creation", Step::Pairing, 0)?;
                }
                // Q1, S2: an entry that matches every content and binds nothing, on a cell the
                // result leaves out, constrains nothing.
                Ok((total(spelling, stack) && !binds(spelling)).then_some(NO_EFFECT_ENTRY))
            }
            Side::Result => {
                let other = self
                    .context
                    .other
                    .as_ref()
                    .map_or(Other::Unmatched, Other::Matched);
                self.pair_result(stack, spelling, other).map(|()| None)
            }
            Side::Guard | Side::Initializer => Ok(None),
        }
    }

    /// Step 3 for a result's content, at the entry's cell or at a child's (P1: a group or
    /// instance record's children are entries of their own cells): its content root against
    /// its other side (P6), then each child the group or instance records it writes name,
    /// against the child's own other side.
    fn pair_result(
        &self,
        stack: &[Layer],
        spelling: &Spelling,
        other: Other<'_>,
    ) -> Result<(), Refusal> {
        let anon = Root::Rest(Rest::Anon);
        match other {
            Other::Unmatched => {
                // Q1: a result over a cell the subject does not match overwrites it, which
                // means one configuration only where the cell's presence is known (P5) and no
                // rest the subject never matched is kept (P6); a readable rule neither drops nor
                // keeps unmatched the continuation (Q3).
                let readable = matches!(self.form, Form::Readable | Form::Claim);
                match stack.first() {
                    Some(Layer::Optional) => {
                        return refuse("unmatched-optional-result", Step::Pairing, 0);
                    }
                    Some(Layer::Computation) if readable => {
                        return refuse("continuation-in-readable", Step::Pairing, 0);
                    }
                    _ if root(spelling) == anon => {
                        return refuse("rest-mismatch", Step::Pairing, 0);
                    }
                    _ => {}
                }
            }
            Other::Matched(subject) => {
                // P5: `None` removes the cell, and with it all its content, its rest included;
                // it writes no content root, so P6 has no rest to pair.
                if *spelling == Spelling::Missing {
                    return Ok(());
                }
                // P6: a result rest is the subject's rest of the same cell, and a subject's
                // anonymous rest is kept only by a result `..` (D2).
                if (root(spelling) == anon) != (root(subject) == anon) {
                    return refuse("rest-mismatch", Step::Pairing, 0);
                }
            }
            // P6: a created cell had no content, so a `..` keeps no rest the subject wrote.
            Other::Created => {
                if root(spelling) == anon {
                    return refuse("rest-mismatch", Step::Pairing, 0);
                }
            }
        }
        self.pair_children(stack, spelling, other)
    }

    /// The children of the group or instance records a result's content writes, each against
    /// its own other side ([`Other`]).
    fn pair_children(
        &self,
        stack: &[Layer],
        spelling: &Spelling,
        other: Other<'_>,
    ) -> Result<(), Refusal> {
        match (stack, spelling) {
            ([Layer::Optional, below @ ..], Spelling::Present(inner)) => {
                self.pair_children(below, inner, other.present())
            }
            ([Layer::Group(group), ..], _) => {
                let Some(record) = record_of(spelling, group) else {
                    return Ok(());
                };
                // P6: a bare `..` in a result is Rust's default fields, which only a created
                // instance has (its template); a group that exists, matched or overwritten,
                // has none. A `..` after every child defaults none: the exact record (P0). A
                // fragment of the group is its record (P7: readable `G { a: x, .. }`
                // abbreviates `k::fragment![crate::G { a: x, .. }]`), as Q1's lint reads it
                // ([`total`]).
                if leaves_open(record, group) && other != Other::Created {
                    return refuse("open-record-outside-pattern", Step::Pairing, 0);
                }
                self.pair_fields(group, record, other)
            }
            ([Layer::Instances(order), Layer::Group(group), ..], _) => {
                for item in seq_of(spelling).map_or(&[][..], |(items, _)| items) {
                    if let Some(record) = record_of(item, group) {
                        let Some(other) = other.instance(record, self.context) else {
                            return refuse("record-update-base", Step::Pairing, 0);
                        };
                        if !keyed(*order, group, record, other) {
                            return refuse("map-collection-key", Step::Pairing, 0);
                        }
                        self.pair_fields(group, record, other)?;
                    }
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Each field of `record`, a record of `group`, against the same child of `other`.
    fn pair_fields(&self, group: &Group, record: &Record, other: Other<'_>) -> Result<(), Refusal> {
        for (name, value) in &record.fields {
            if let Some(stack) = child(group, name) {
                self.pair_result(stack, value, other.child(group, name))?;
            }
        }
        Ok(())
    }
}

/// What a result's content is paired with (P6): at the entry's own cell, the subject's entry
/// of the cell, or none where the subject does not match it (Q1's overwrite); at a child of a
/// group or instance record (P1), the other side of its record's same child (R10).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Other<'s> {
    /// The subject's entry of the same cell.
    Matched(&'s Spelling),
    /// The cell exists and the subject does not match it: the result overwrites it (Q1).
    Unmatched,
    /// The cell is created, with the instance or the `?` cell that holds it: it had no content.
    Created,
}

impl Other<'_> {
    /// The other side of what a result `Some(..)` holds: the subject's `Some(..)`'s, or a cell
    /// the result creates over a subject `None` (P5).
    fn present(self) -> Self {
        match self {
            Self::Matched(subject) => match unaliased(subject) {
                Spelling::Present(inner) => Self::Matched(inner),
                Spelling::Missing => Self::Created,
                _ => Self::Unmatched,
            },
            other => other,
        }
    }

    /// The other side of `group`'s child `name` in a record whose other side is `self`: the
    /// subject's record's same child, or an unmatched child where the subject's record does not
    /// name it (or is no record of the group); a created record's child is created.
    fn child(self, group: &Group, name: &str) -> Self {
        match self {
            Self::Matched(subject) => record_of(subject, group)
                .and_then(|record| record.fields.iter().find(|(field, _)| field == name))
                .map_or(Self::Unmatched, |(_, value)| Self::Matched(value)),
            other => other,
        }
    }

    /// The other side of an instance record a result writes in a collection whose other side is
    /// `self`, `None` where it has none (P0, S5.0g pattern review P-R3). An update `..label`
    /// changes in place the subject's instance labelled `label` (R10), which the update matched:
    /// K rewrites in place only an instance the left side matched. Where no subject instance has
    /// the label, the update is no in-place rewrite: if the sentence binds `label` elsewhere to a
    /// record of the update's own constructor (a record matched in another cell), the record is
    /// a new term with that record's fields, a created instance. If it binds `label` nowhere, or
    /// to no record (a list element, a leaf value), or to a record of another constructor, the
    /// update has no base (`record-update-base`), `None`: `..base` takes the fields of a value
    /// of the record's own type (P6, as Rust's update syntax; S5.0g item 3b ruling 1). Any other
    /// instance record creates an instance (P6: its `..` is its template's).
    fn instance(self, record: &Record, context: &Context) -> Option<Self> {
        let RecordRest::Update(label) = &record.rest else {
            return Some(Self::Created);
        };
        let shown = match self {
            Self::Matched(subject) => seq_of(unaliased(subject)).and_then(|(items, _)| {
                items.iter().find_map(|item| match item {
                    Spelling::Alias(name, inner) if name == label => Some(Self::Matched(inner)),
                    _ => None,
                })
            }),
            Self::Unmatched | Self::Created => None,
        };
        shown.or_else(|| {
            context
                .records
                .iter()
                .any(|(name, head)| name == label && *head == record.head)
                .then_some(Self::Created)
        })
    }
}

/// P5 at every depth (P1, S5.0g item 3b ruling 2): whether `subject`, a subject's content on
/// `stack`, tests a `?` child absent (`None`, inside a group or instance record it writes) that
/// `result`, the result's content of the same place (`None`: the result does not write it),
/// does not create. K tests absence only by creating the cell, and a record's child is an entry
/// of its own cell, so the test needs the result's same child to be present (`Some(..)`): the
/// same record of a group, the same `?` cell's content, or, in a collection, the result's
/// update `..label` of the instance the subject labels `label` (an unlabelled subject instance
/// is rewritten by no result record). At the entry's own root, a `None` the result writes the
/// cell over is created only by a result `Some(..)`: a result `None` creates nothing (P5, as
/// at a child); where the result does not write the cell, [`Judge::pair`]'s `written` decides.
fn absence_uncreated(stack: &[Layer], subject: &Spelling, result: Option<&Spelling>) -> bool {
    match (stack, unaliased(subject)) {
        ([Layer::Optional, ..], Spelling::Missing) => {
            result.is_some_and(|result| !matches!(unaliased(result), Spelling::Present(_)))
        }
        ([Layer::Optional, below @ ..], Spelling::Present(inner)) => {
            let result = result.and_then(|result| match unaliased(result) {
                Spelling::Present(inner) => Some(&**inner),
                _ => None,
            });
            absence_uncreated(below, inner, result)
        }
        ([Layer::Group(group), ..], _) => record_of(subject, group).is_some_and(|record| {
            fields_uncreated(group, record, result.and_then(|result| record_of(result, group)))
        }),
        ([Layer::Instances(_), Layer::Group(group), ..], inner) => {
            seq_of(inner).is_some_and(|(items, _)| {
                items.iter().any(|item| {
                    let Some(record) = record_of(item, group) else {
                        return false;
                    };
                    let updated = match item {
                        Spelling::Alias(label, _) => result
                            .and_then(|result| seq_of(unaliased(result)))
                            .and_then(|(items, _)| {
                                items.iter().filter_map(|item| record_of(item, group)).find(
                                    |record| {
                                        matches!(&record.rest, RecordRest::Update(base) if base == label)
                                    },
                                )
                            }),
                        _ => None,
                    };
                    fields_uncreated(group, record, updated)
                })
            })
        }
        _ => false,
    }
}

/// [`absence_uncreated`] over each child `record`, a subject's record of `group`, names, with
/// `result` the result's record of the same place.
fn fields_uncreated(group: &Group, record: &Record, result: Option<&Record>) -> bool {
    record.fields.iter().any(|(name, value)| {
        let Some(stack) = child(group, name) else {
            return false;
        };
        let written = result
            .and_then(|result| result.fields.iter().find(|(field, _)| field == name))
            .map(|(_, value)| value);
        if stack.first() == Some(&Layer::Optional) && *unaliased(value) == Spelling::Missing {
            return !matches!(written.map(unaliased), Some(Spelling::Present(_)));
        }
        absence_uncreated(stack, value, written)
    })
}

/// P2 with P0 (S5.0g pattern review P-R1): a cons list is a constructor term built from its
/// front, `x : rest`, so its brackets end in their rest. An item after the rest (`[.., x]`,
/// `[x, .., y]`, a result's `[..rest, x]`) is no constructor pattern and, with no append
/// declared, builds no term: it lowers to no K, on either side. It is the leaf mark's own shape,
/// known from the declaration, so it is a kind refusal inside the mark (it stands under a path,
/// and comes before pairing).
fn cons_front(notation: Notation, seq: &Seq, depth: usize) -> Result<(), Refusal> {
    if notation == Notation::Cons && matches!(seq.rest, Some((_, RestAt::Front))) {
        return refuse("cons-list-back-item", Step::Inside, depth);
    }
    Ok(())
}

/// E1: the computation is read from its front, where the next step is, so `..` ends it and no
/// item follows it (`[.., x]`, `KCell(x, .., y)`). E1 is stated of the computation, not of a
/// form: P3 is one judgement in every form, so it holds in readable, claims and `cells!` alike
/// (S5.0g fixes review F-6, ruled). It is the computation mark's own shape, known from the
/// declaration, so it is a kind refusal inside the mark (it stands under a path, and comes
/// before pairing).
fn computation_front(layer: &Layer, spelling: &Spelling, depth: usize) -> Result<(), Refusal> {
    let (Spelling::Brackets(seq) | Spelling::KCell(seq) | Spelling::KMacro(seq)) = spelling else {
        return Ok(());
    };
    if *layer == Layer::Computation && matches!(seq.rest, Some((_, RestAt::Front))) {
        return refuse("computation-back-item", Step::Inside, depth);
    }
    Ok(())
}

/// The record of `group` that `spelling` writes, below an alias: a record, or its fragment.
fn record_of<'s>(spelling: &'s Spelling, group: &Group) -> Option<&'s Record> {
    match unaliased(spelling) {
        Spelling::Record(record) | Spelling::Fragment(record) if record.head == group.name => {
            Some(record)
        }
        _ => None,
    }
}

/// Whether a result's instance record of `group`, in a collection ordered by `order`, with
/// `other` its other side ([`Other::instance`]), keys its instance as its collection does
/// (§2.3, §7). A Map collection's instance is keyed by its first child, its identity: written at
/// creation and never changed by an update. A created instance writes it (P5: a bare `..` gives
/// the template's fields, and the template states no identity). An update (`..me`) changes the
/// instance in place: it writes the key, if at all, as what is provably the key its subject
/// matched, the key's own binder or the same literal, which means the same instance (P0); any
/// other key value, or a key the labelled instance does not name, is a key change. A List or
/// Set collection has no key.
fn keyed(order: Order, group: &Group, record: &Record, other: Other<'_>) -> bool {
    fn named<'r>(record: &'r Record, key: &str) -> Option<&'r Spelling> {
        record
            .fields
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, value)| value)
    }
    let Some(key) = key(order, group) else {
        return true;
    };
    match (&record.rest, named(record, key)) {
        (RecordRest::Update(_), Some(value)) => {
            // A created instance (an update of a value matched elsewhere) writes its key, as
            // any created instance does (P5).
            let Other::Matched(subject) = other else {
                return other == Other::Created;
            };
            let matched = record_of(subject, group).and_then(|record| named(record, key));
            match (value, matched) {
                (
                    Spelling::Binder(written),
                    Some(Spelling::Binder(bound) | Spelling::Alias(bound, _)),
                ) => written == bound,
                (Spelling::Literal(Some(written)), Some(matched)) => matches!(
                    unaliased(matched),
                    Spelling::Literal(Some(literal)) if literal == written
                ),
                _ => false,
            }
        }
        (RecordRest::Update(_), None) => true,
        (RecordRest::Exact | RecordRest::Open, written) => written.is_some(),
    }
}

/// Whether `spelling`, a term, holds a record (itself included) whose bare `..` leaves a field
/// open ([`leaves_open`]). A record's fields are those of the group of `groups` its head names;
/// a head that names none has no fields the record is known to name, so its `..` is open.
fn open_record(spelling: &Spelling, groups: &[Group]) -> bool {
    let open = match spelling {
        Spelling::Record(record) | Spelling::Fragment(record) => {
            record.rest == RecordRest::Open
                && groups
                    .iter()
                    .find(|group| group.name == record.head)
                    .is_none_or(|group| leaves_open(record, group))
        }
        _ => false,
    };
    open || children(spelling)
        .into_iter()
        .any(|one| open_record(one, groups))
}

/// `spelling` below an alias.
fn unaliased(spelling: &Spelling) -> &Spelling {
    match spelling {
        Spelling::Alias(_, inner) => inner,
        other => other,
    }
}

fn seq_of(spelling: &Spelling) -> Option<(&[Spelling], Option<&Rest>)> {
    match spelling {
        Spelling::Brackets(seq)
        | Spelling::Braces(seq)
        | Spelling::KCell(seq)
        | Spelling::InstList(seq)
        | Spelling::InstSet(seq)
        | Spelling::KMacro(seq) => Some((&seq.items, seq.rest.as_ref().map(|(rest, _)| rest))),
        _ => None,
    }
}

/// Steps 1–3 for one entry, with the refusal's step and depth: `path` is the layers of the
/// cell's `?` and `*` ancestors, `stack` the cell's own.
///
/// # Errors
///
/// The refusal, where steps 1–3 refuse the entry.
pub fn judge(
    form: Form,
    side: Side,
    path: &[Layer],
    stack: &[Layer],
    spelling: &Spelling,
    context: &Context,
) -> Result<Outcome, Refusal> {
    let mut judge = Judge {
        form,
        side,
        context,
        sort: false,
    };
    judge.form_step(spelling, 0, Place::HEAD)?;
    judge.judge(stack, spelling, 0)?;
    // S1 (b): below a marked ancestor, the entry is refused for the outermost one, after the
    // cell's own kind (P3's reason): the advice writes the entry inside the ancestor's mark, so
    // a spelling the cell's own stack refuses would be refused again there.
    if let Some(ancestor) = path.first() {
        refuse(missing(ancestor), Step::Path, 0)?;
    }
    let lint = judge.pair(stack, spelling)?;
    Ok(if judge.sort && lint.is_none() {
        Outcome::After
    } else {
        Outcome::Admit { lint }
    })
}

/// Steps 1–3 for one entry (design §3, `outcome`): `path` is the layers of the cell's `?` and
/// `*` ancestors, `stack` the cell's own.
#[must_use]
pub fn outcome(
    form: Form,
    side: Side,
    path: &[Layer],
    stack: &[Layer],
    spelling: &Spelling,
    context: &Context,
) -> Outcome {
    judge(form, side, path, stack, spelling, context)
        .unwrap_or_else(|refusal| Outcome::Refuse(refusal.class))
}

/// Which step of P4's order over a sentence a refusal belongs to: the form (0), the kind (1),
/// the pairing (2). A path refusal is the kind's: it needs only the declaration, as the cell's
/// own kind does, and the cell's own kind comes before it within the entry (R3).
const fn sentence_step(step: Step) -> u8 {
    match step {
        Step::Form => 0,
        Step::MarkElsewhere | Step::MissingLayer | Step::Path | Step::Inside => 1,
        Step::Pairing => 2,
    }
}

/// Steps 1–3 over a whole sentence (P4 over a sentence): each step runs over every entry
/// before the next starts, since a later step's question is not well posed while an earlier
/// one is open anywhere in the sentence (a pairing assumes both sides have kinds), and a step
/// that refuses anything ends the judgement. `entries` is the sentence's entries in source
/// order, each with its own context; `own` the index of the entry whose admission is asked.
///
/// Answers the index of the entry the answer is about and the answer: the first refusal of the
/// first step that refuses, in source order, or, where every entry is admitted, `own`'s
/// outcome (its lint and its sort are its own).
#[must_use]
pub fn sentence_outcome(form: Form, entries: &[(Entry, Context)], own: usize) -> (usize, Outcome) {
    let judged = entries
        .iter()
        .map(|(entry, context)| {
            judge(
                form,
                entry.side,
                &entry.path,
                &entry.stack,
                &entry.spelling,
                context,
            )
        })
        .collect::<Vec<_>>();
    let first = judged
        .iter()
        .enumerate()
        .filter_map(|(at, judged)| {
            judged
                .as_ref()
                .err()
                .map(|refusal| (sentence_step(refusal.step), at, refusal.class))
        })
        .min();
    match first {
        Some((_, at, class)) => (at, Outcome::Refuse(class)),
        None => (
            own,
            judged[own]
                .as_ref()
                .copied()
                .unwrap_or_else(|refusal| Outcome::Refuse(refusal.class)),
        ),
    }
}

/// The names `spelling` binds: its binders, its aliases' names and its named rests.
fn bound_names(spelling: &Spelling, out: &mut Vec<String>) {
    let mut push = |name: &str| {
        if !out.iter().any(|known| known == name) {
            out.push(name.to_owned());
        }
    };
    match spelling {
        Spelling::Binder(name) | Spelling::Alias(name, _) => push(name),
        _ => {}
    }
    let rest = match spelling {
        Spelling::MapRead(entries) | Spelling::MapLit(entries) => entries.rest.as_ref(),
        _ => sequence(spelling).and_then(|(_, rest)| rest),
    };
    if let Some(Rest::Named(name)) = rest {
        push(name);
    }
    for inner in children(spelling) {
        bound_names(inner, out);
    }
}

/// The record each alias of `spelling` labels, with its head (`me @ Acct { .. }`: `me`, `Acct`).
fn record_aliases(spelling: &Spelling, out: &mut Vec<(String, String)>) {
    if let Spelling::Alias(name, inner) = spelling
        && let Spelling::Record(record) | Spelling::Fragment(record) = &**inner
        && !out.iter().any(|(known, _)| known == name)
    {
        out.push((name.clone(), record.head.clone()));
    }
    for inner in children(spelling) {
        record_aliases(inner, out);
    }
}

impl EntryCase {
    /// The case's whole sentence, its own entry first, then the template's, each with the
    /// context it is judged in. The own entry keeps the case's context. Another entry's is read
    /// from the sentence as the case's is: the names every other subject entry binds (an
    /// initializer's: its configuration variables), the records their aliases label, the other
    /// side's entry of the same cell, and, for a subject, whether the result writes the cell.
    #[must_use]
    pub fn sentence(&self) -> Vec<(Entry, Context)> {
        let all = std::iter::once(&self.entry)
            .chain(&self.template.entries)
            .collect::<Vec<_>>();
        let mut out = vec![(self.entry.clone(), self.context.clone())];
        for (at, entry) in all.iter().enumerate().skip(1) {
            let mut context = Context {
                groups: self.context.groups.clone(),
                ..Context::default()
            };
            if self.template.sentence == Sentence::Initializer {
                context.bound.clone_from(&self.context.bound);
            }
            for (_, other) in all
                .iter()
                .enumerate()
                .filter(|(other, subject)| *other != at && subject.side == Side::Subject)
            {
                bound_names(&other.spelling, &mut context.bound);
                record_aliases(&other.spelling, &mut context.records);
            }
            let across = |side: Side| {
                all.iter()
                    .find(|other| other.side == side && other.cell == entry.cell)
                    .map(|other| other.spelling.clone())
            };
            match entry.side {
                Side::Subject => {
                    context.other = across(Side::Result);
                    context.written = context.other.is_some();
                }
                Side::Result => context.other = across(Side::Subject),
                _ => {}
            }
            out.push(((*entry).clone(), context));
        }
        out
    }

    /// The case's [`outcome`].
    #[must_use]
    pub fn outcome(&self) -> Outcome {
        outcome(
            self.form,
            self.entry.side,
            &self.entry.path,
            &self.entry.stack,
            &self.entry.spelling,
            &self.context,
        )
    }

    /// The case's [`rule_outcome`], given its entry's outcome.
    #[must_use]
    pub fn rule_outcome(&self, entry: Outcome) -> Option<&'static str> {
        rule_outcome(&self.template, &self.entry, entry)
    }
}

/// Step 5, the rule-level rows, judged after the entries are admitted, from the whole sentence:
/// `entry` is the case's own entry, `template` the rest of its sentence.
///
/// - `group-and-descendant`: two entries of a rule or claim, on either side, name a cell and a
///   cell below it (P1: an entry denotes the content of one cell, so the first already names
///   the second, and the two denote overlapping content). Judged first: the rule's other
///   classes judge what the rule matches and writes, which overlapping entries do not state
///   once;
/// - `always-enabled-rule`: every subject entry of a rule constrains nothing (Q1's [`total`])
///   and there is no guard, so the rule matches every configuration;
/// - `rule-changes-no-cell`: a rule writes no cell;
/// - `unused-configuration-variable`: no initializer value names a configuration variable;
/// - `main-cell-not-k`: the program is placed in a computation cell, and not in the one named
///   `k`, which K takes as the computation cell by its name, whatever order the entries come in.
#[must_use]
pub fn rule_outcome(template: &Template, entry: &Entry, outcome: Outcome) -> Option<&'static str> {
    if !outcome.admits() {
        return None;
    }
    let entries = || template.entries.iter().chain([entry]);
    if template.sentence != Sentence::Initializer
        && entries().any(|outer| entries().any(|inner| holds(&outer.stack, &inner.cell)))
    {
        return Some("group-and-descendant");
    }
    match template.sentence {
        Sentence::Rule => {
            if !template.guard
                && entries()
                    .filter(|entry| entry.side == Side::Subject)
                    .all(|entry| total(&entry.spelling, &entry.stack))
            {
                return Some("always-enabled-rule");
            }
            if !entries().any(|entry| entry.side == Side::Result) {
                return Some("rule-changes-no-cell");
            }
            None
        }
        Sentence::Claim | Sentence::Context => None,
        Sentence::Initializer => {
            let computation = |entry: &Entry| entry.stack.last() == Some(&Layer::Computation);
            let k = |entry: &Entry| entry.cell == "k" && computation(entry);
            for (variable, main) in &template.variables {
                let holders = || entries().filter(|entry| mentions(&entry.spelling, variable));
                if holders().next().is_none() {
                    return Some("unused-configuration-variable");
                }
                // Which entries hold the program is a set: their order states nothing.
                if *main && holders().any(computation) && !holders().any(k) && entries().any(k) {
                    return Some("main-cell-not-k");
                }
            }
            None
        }
    }
}

/// Whether a group of `stack` holds a cell named `cell` at any depth below it, through its
/// children's own layers (a `?` or `*` child's included).
fn holds(stack: &[Layer], cell: &str) -> bool {
    stack.iter().any(|layer| match layer {
        Layer::Group(group) => group
            .children
            .iter()
            .any(|(name, child)| name == cell || holds(child, cell)),
        _ => false,
    })
}

fn wrap_seq(items: Vec<Spelling>, rest: Option<(Rest, RestAt)>) -> Seq {
    Seq { items, rest }
}

/// The `cells!` entry a readable `spelling` on `stack` abbreviates (P7), defined for every
/// spelling on every stack, refused ones included:
///
/// - `x @ p` → `x @ abbreviate(p)`; `Some(e)` → `Some(abbreviate(e))` below presence; `None`;
/// - brackets go to the first layer that reads brackets in readable: a computation's
///   `KCell(..)`, a List collection's instance list (each record item a fragment), otherwise
///   `Cell([..])`;
/// - instance braces → `{ fragments, rest }`; a map read → `Cell(k::map![..])`;
/// - a value: a record of the position's group → its fragment; on a stack whose content is a
///   leaf with no instance or group layer, `Cell(value)`; otherwise the value itself.
///
/// Rests stay as written: `..` is the reading `krs expand` prints.
#[must_use]
pub fn abbreviate(stack: &[Layer], spelling: &Spelling) -> Spelling {
    let fragment = |item: &Spelling| match item {
        Spelling::Record(record) => Spelling::Fragment(record.clone()),
        other => other.clone(),
    };
    match spelling {
        Spelling::Alias(name, inner) => {
            Spelling::Alias(name.clone(), Box::new(abbreviate(stack, inner)))
        }
        Spelling::Present(inner) => {
            let below = stack
                .iter()
                .filter(|layer| **layer != Layer::Optional)
                .cloned()
                .collect::<Vec<_>>();
            Spelling::Present(Box::new(abbreviate(&below, inner)))
        }
        Spelling::Missing => Spelling::Missing,
        Spelling::Brackets(seq) => {
            match stack
                .iter()
                .find(|layer| admits(Form::Readable, layer, Mark::Seq))
            {
                Some(Layer::Computation) => {
                    Spelling::KCell(wrap_seq(seq.items.clone(), seq.rest.clone()))
                }
                Some(Layer::Instances(_)) => Spelling::InstList(wrap_seq(
                    seq.items.iter().map(fragment).collect(),
                    seq.rest.clone(),
                )),
                _ => Spelling::Cell(Box::new(spelling.clone())),
            }
        }
        Spelling::Braces(seq) => Spelling::InstSet(wrap_seq(
            seq.items.iter().map(fragment).collect(),
            seq.rest.clone(),
        )),
        Spelling::MapRead(entries) => Spelling::Cell(Box::new(Spelling::MapLit(entries.clone()))),
        _ => {
            let content = stack
                .iter()
                .filter(|layer| **layer != Layer::Optional)
                .collect::<Vec<_>>();
            if let (Some(Layer::Group(group)), Spelling::Record(record)) =
                (content.first(), spelling)
                && group.name == record.head
            {
                return Spelling::Fragment(record.clone());
            }
            let leaf = matches!(content.last(), Some(Layer::Leaf(_)))
                && !content
                    .iter()
                    .any(|layer| matches!(layer, Layer::Instances(_) | Layer::Group(_)));
            if leaf {
                Spelling::Cell(Box::new(spelling.clone()))
            } else {
                spelling.clone()
            }
        }
    }
}

/// The spelling the advice of a P3 (c) refusal of `spelling` at its head writes: every layer of
/// `stack` above the author's head whose mark is missing, added outermost first, with the
/// number of layers added. A rest the advice writes follows the side: `..` in a subject, the
/// other side's root rest (`..` when it is anonymous) in a result, none in an initializer.
/// `None` where the author's head needs no layer or no advice adds one.
#[must_use]
pub fn advise(
    form: Form,
    side: Side,
    stack: &[Layer],
    spelling: &Spelling,
    other: Option<&Spelling>,
) -> Option<(Spelling, usize)> {
    let rest = match side {
        Side::Subject => Some((Rest::Anon, RestAt::Back)),
        Side::Result if other.is_some_and(|other| root(other) == Root::Rest(Rest::Anon)) => {
            Some((Rest::Anon, RestAt::Back))
        }
        _ => None,
    };
    let complete = complete(form, stack, spelling, rest.as_ref())?;
    (complete.1 > 0).then_some(complete)
}

fn complete(
    form: Form,
    stack: &[Layer],
    spelling: &Spelling,
    rest: Option<&(Rest, RestAt)>,
) -> Option<(Spelling, usize)> {
    let Some(outer) = stack.first() else {
        return Some((spelling.clone(), 0));
    };
    let mark = mark(form, spelling, false);
    let needs = if mark == Mark::Value {
        has_mark(form, outer)
    } else {
        !admits(form, outer, mark)
    };
    if !needs {
        return Some((spelling.clone(), 0));
    }
    let one = |item: Spelling| wrap_seq(vec![item], rest.cloned());
    match outer {
        Layer::Optional => {
            let (inner, added) = complete(form, &stack[1..], spelling, rest)?;
            Some((Spelling::Present(Box::new(inner)), added + 1))
        }
        Layer::Instances(order) => {
            let item = spelling.clone();
            Some((
                match (form, order) {
                    (Form::Cells, Order::List) => Spelling::InstList(one(item)),
                    (Form::Cells, _) => Spelling::InstSet(one(item)),
                    (_, Order::List) => Spelling::Brackets(one(item)),
                    (_, _) => Spelling::Braces(one(item)),
                },
                1,
            ))
        }
        Layer::Computation if mark == Mark::Value => Some((
            match form {
                Form::Cells => Spelling::KCell(one(spelling.clone())),
                Form::Init => Spelling::KMacro(wrap_seq(vec![spelling.clone()], None)),
                Form::Readable | Form::Claim => Spelling::Brackets(one(spelling.clone())),
            },
            1,
        )),
        Layer::Leaf(_) if mark == Mark::Value => {
            Some((Spelling::Cell(Box::new(spelling.clone())), 1))
        }
        _ => None,
    }
}

/// Builders for spelling declarations.
pub mod build {
    use super::{Entries, Record, RecordRest, Rest, RestAt, Seq, Spelling};

    /// `_`.
    #[must_use]
    pub const fn wild() -> Spelling {
        Spelling::Wild
    }
    /// A binder.
    #[must_use]
    pub fn bind(name: &str) -> Spelling {
        Spelling::Binder(name.to_owned())
    }
    /// A literal, its text unstated.
    #[must_use]
    pub const fn lit() -> Spelling {
        Spelling::Literal(None)
    }
    /// An application.
    #[must_use]
    pub const fn call(arguments: Vec<Spelling>) -> Spelling {
        Spelling::Call(arguments)
    }
    /// A configuration variable.
    #[must_use]
    pub fn var(name: &str) -> Spelling {
        Spelling::ConfigVar(name.to_owned())
    }
    /// `Some(inner)`.
    #[must_use]
    pub fn some(inner: Spelling) -> Spelling {
        Spelling::Present(Box::new(inner))
    }
    /// `k::absent!(inner)`.
    #[must_use]
    pub fn absent(inner: Spelling) -> Spelling {
        Spelling::Absent(Box::new(inner))
    }
    /// `name @ inner`.
    #[must_use]
    pub fn alias(name: &str, inner: Spelling) -> Spelling {
        Spelling::Alias(name.to_owned(), Box::new(inner))
    }
    /// `Cell(inner)`.
    #[must_use]
    pub fn cell(inner: Spelling) -> Spelling {
        Spelling::Cell(Box::new(inner))
    }
    /// No rest.
    #[must_use]
    pub const fn exact() -> Option<(Rest, RestAt)> {
        None
    }
    /// `..` last.
    #[must_use]
    pub const fn open() -> Option<(Rest, RestAt)> {
        Some((Rest::Anon, RestAt::Back))
    }
    /// `..` before the items.
    #[must_use]
    pub const fn open_front() -> Option<(Rest, RestAt)> {
        Some((Rest::Anon, RestAt::Front))
    }
    /// `name @ ..` last.
    #[must_use]
    pub fn named(name: &str) -> Option<(Rest, RestAt)> {
        Some((Rest::Named(name.to_owned()), RestAt::Back))
    }
    /// `..name` last.
    #[must_use]
    pub fn splice(name: &str) -> Option<(Rest, RestAt)> {
        Some((Rest::Splice(name.to_owned()), RestAt::Back))
    }
    /// A sequence.
    #[must_use]
    pub const fn seq(items: Vec<Spelling>, rest: Option<(Rest, RestAt)>) -> Seq {
        Seq { items, rest }
    }
    /// Map entries; the rest's position is always last.
    #[must_use]
    pub fn entries(entries: Vec<(Spelling, Spelling)>, rest: Option<(Rest, RestAt)>) -> Entries {
        Entries {
            entries,
            rest: rest.map(|(rest, _)| rest),
        }
    }
    /// A record.
    #[must_use]
    pub fn record(head: &str, fields: Vec<(&str, Spelling)>, rest: RecordRest) -> Record {
        Record {
            head: head.to_owned(),
            fields: fields
                .into_iter()
                .map(|(name, value)| (name.to_owned(), value))
                .collect(),
            rest,
        }
    }
}

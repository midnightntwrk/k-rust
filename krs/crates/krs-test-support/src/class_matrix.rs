//! Class-test cases: one construct in one slot of an otherwise accepted base.
//!
//! A *case* is one source with exactly one point of interest: one construct (a spelling, a term
//! shape, an initializer value) in one *slot* (a form and a position in it, written as a
//! template with a hole), on top of a fixed *base* that declares the configuration and the
//! constructors every case of its family needs. Each slot lists the constructs that can stand
//! there syntactically, so the generator is a union of slot products, not a blind Cartesian
//! product.
//!
//! The families ([`Family`]) and their slots:
//! - readable records and readable claims: 7 cell kinds × 13 entry spellings × {subject,
//!   result}, `readable/result/pc/Some(x)`;
//! - `cells!` rules: 7 cell kinds × 13 subject and 11 result spellings of the reference form,
//!   `cells/subject/stack/k::configuration::Cell(x)`;
//! - initializers: 7 cell kinds × 16 values, `init/k/k::k![]`, a remainder after a computation
//!   item, `init/k/k::k![Cmd::Go(), ..pgm]`, three field orders, `init/order/reversed`, and a
//!   two-child group's children in reverse order, `init/order/nested-reversed`;
//! - the strict-subsort axis (`Int ≤ Value ≤ Stmt ≤ KItem`): an `Int` literal, a `Value` and a
//!   `Stmt` constructor and an `Int` binder in the `Value`, `Stmt` and `KItem` leaves, a typed
//!   `List` element and `Map` value, a group child, an optional cell and a collection instance,
//!   in readable records, claims and initializers, `readable/result/typed/list/Go()`;
//! - term positions: every construct of the oracle's catalog (every `TermTree` shape, every
//!   literal kind, every construct of the product's position table, every notation form of
//!   `krs_syntax::notation`, the builtin and declared function applications and the collection
//!   forms) at every position of the 17 sentence forms: their argument positions, their slots'
//!   roots (a fn's, an equation's, a simplification's, a context's and a static clause's whole
//!   subject, a `for KItem` clause's bare and wrapped, a result's, a value's and a computation
//!   item's), and the positions the constructs open (depth 2: a `let` pattern and body, a
//!   `k::matches!` pattern, a rewrite's sides, an `A | B` branch, an `@` body, a function's
//!   argument, a set's element, a record update's field, a closure's body), each at one host per
//!   kind,
//!   `terms/equation/guard/k::is!(Int, x)`, `terms/rule/subject-root/_`,
//!   `terms/sort-rule/result/let-body/Size(x)`;
//! - the import axis: two bare variants at every position of depth 1 under a module-level
//!   `use Cmd::*;`, `import/table/subject/Go()`;
//! - the attribute axis ([`attributes`]): every attribute an author writes on a sentence (a key of
//!   its marker, a helper beside it) on every sentence form, on the form's term slot template,
//!   judged by the attribute oracle, `attrs/rule/owise`, `attrs/alias/#[k::requires(..)]`;
//! - the run families: the readable records and the `cells!` rules again on the run base
//!   ([`Base::Run`]), whose driver commands let K7 run them, each a twin of a machine-base case
//!   judged by the same table entries ([`table::twin`]), `readable-run/subject/pc/0`, and 4 subject
//!   and 4 result spellings of a Set collection whose instances hold a map cell, which only the run
//!   base declares, `cells-run/subject/bag/{ k::fragment![crate::Obj { .. }], instances0 @ .. }`.
//!
//! A case's ID is spelled from its axes, as above, so the expected-outcome table ([`table`])
//! can match IDs with globs and an ID stays stable when other cases are added. A construct
//! never contains `/`.
//!
//! **The oracle.** A term case also carries its position and its construct's nodes as data
//! ([`Case::term`], [`positions`]): each slot template declares where its hole stands, and each
//! spelling the constructs it holds and where each stands relative to the hole. The oracle
//! ([`oracle`]) derives from them whether the case is accepted and the class of its mistake,
//! stated per construct from what it means at a position. The table reads the oracle first for
//! the term families ([`table`]'s precedence), so their refusal rules name only a term's sort and
//! names.
//!
//! Every case records three byte ranges: the *spelling* (the construct itself), the *entry*
//! (the smallest unit of the slot that holds the construct, `pc: Some(x)` for a cell entry, the
//! spelling itself for a term position, and the outer construct's text, `{ let y = x; HOLE }`,
//! for a construct inside another's opening) and the *item* (the whole sentence or initializer
//! the case adds). The ranges are relative to the item's text; [`render`] places them in a
//! package source.
//!
//! **Packaging.** A rule-level case gets its own command constructor, declared in its base's
//! command family, and its subject starts the computation cell with it, so the cases of one
//! base can share a package without two of them matching one configuration
//! ([`Packaging::Shared`]). A case that cannot be kept apart that way needs a package of its
//! own ([`Packaging::Own`]): an initializer, because a definition has exactly one, and a case
//! whose construct fills the computation cell's subject entry, because no command item is left
//! there to tell it from the other cases. A case whose construct is a rule's whole subject, or
//! the computation item before its command, keeps its command but is rendered alone
//! ([`Packaging::Alone`]): its construct can match what another case's subject matches (`_`,
//! `x`), which the overlap check refuses when the two are printed together.
//!
//! **Count.** [`cases`] asserts at most [`FRONT_CASE_CAP`] cases, whose documentation argues the
//! budget: the fast tier runs every case in-process, and the cap, not a timed assertion, keeps it
//! inside its budget.

pub mod advice;
pub mod attributes;
mod cells;
mod config_drivers;
pub use config_drivers::{Extent, Part, Reading};
pub mod entry_points;
pub mod invariants;
pub mod k7;
mod machine;
pub mod oracle;
pub mod pending;
pub mod positions;
pub mod table;
mod terms;

use std::fmt::Write as _;
use std::ops::Range;

/// The most cases one shard of the fast tier ([`FRONT_SHARDS`]) may hold. The fast tier runs every
/// case in-process: measured with NT-2's term positions, 5,518 cases take 41.0 s on one CPU
/// (7.4 ms a case, the term family's roots and depth-2 cases being larger items than S0's) and
/// 3.0 s on 32 threads. 6,000 cases are 45 s single-threaded, the budget of a test a developer
/// runs after each change; past it the term family is split into shards rather than the cap
/// raised, as NT-5's collection notation is ([`Family::Notation`]).
pub const FRONT_CASE_CAP: usize = 6_000;

/// The shards of the fast tier, each the families one of its tests runs, and each within
/// [`FRONT_CASE_CAP`]: the collection notation's term cases are a shard of their own, and so,
/// since NT-12's static productions took the first shard past the cap, are the term family's.
pub const FRONT_SHARDS: [&[Family]; 3] = [
    &[
        Family::Readable,
        Family::Claim,
        Family::Cells,
        Family::Init,
        Family::Import,
        Family::Attributes,
        Family::ReadableRun,
        Family::CellsRun,
    ],
    &[Family::Notation],
    &[Family::Terms],
];

/// The family a case belongs to: its form, which fixes its base and its templates.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Family {
    /// A readable `for Machine` record of `k::rules!`.
    Readable,
    /// A readable claim of `k::claims!`.
    Claim,
    /// A `#[k::rule]` fn whose subject and result are `k::cells!` records.
    Cells,
    /// A `#[k::init]` initializer.
    Init,
    /// A construct at a term position of a sentence form.
    Terms,
    /// A bare constructor at a term position, with the constructors imported once at module
    /// level and no block of its own importing them (the import axis).
    Import,
    /// An index read or a collection method (`m[k]`, `s.contains(x)`), or the call it denotes,
    /// at a term position: the term family's positions, templates and oracle, kept apart so that
    /// each shard of the fast tier stays within its budget ([`FRONT_SHARDS`]).
    Notation,
    /// An attribute on a sentence form ([`attributes`]), written on the form's term slot
    /// template.
    Attributes,
    /// The readable family's records on the run base ([`Base::Run`]), which K7 runs: each case a
    /// twin of a readable record of the machine base, judged by the same table entries, and the
    /// Set collection's instances, which the machine base does not have.
    ReadableRun,
    /// The `cells!` family's rules on the run base, as [`Family::ReadableRun`] is the readable
    /// family's.
    CellsRun,
}

impl Family {
    /// Every family, in ID order.
    pub const ALL: [Self; 10] = [
        Self::Readable,
        Self::Claim,
        Self::Cells,
        Self::Init,
        Self::Terms,
        Self::Import,
        Self::Notation,
        Self::Attributes,
        Self::ReadableRun,
        Self::CellsRun,
    ];

    /// The first segment of the IDs of this family's cases.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Readable => "readable",
            Self::Claim => "claim",
            Self::Cells => "cells",
            Self::Init => "init",
            Self::Terms => "terms",
            Self::Import => "import",
            Self::Notation => "notation",
            Self::Attributes => "attrs",
            Self::ReadableRun => "readable-run",
            Self::CellsRun => "cells-run",
        }
    }

    /// The family a run family's cases are twins of: the same slot templates and spellings on
    /// [`Base::Machine`], which the run family instantiates on [`Base::Run`].
    #[must_use]
    pub const fn twin(self) -> Option<Self> {
        match self {
            Self::ReadableRun => Some(Self::Readable),
            Self::CellsRun => Some(Self::Cells),
            _ => None,
        }
    }
}

/// The base a case is rendered on.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Base {
    /// The seven cell kinds over one constructor family (readable records, claims, `cells!`
    /// rules and initializers).
    Machine,
    /// Leaf cells, typed collections, a group, an optional cell and a collection whose content
    /// sort is `Value`, below `Stmt` and above `Int` (the strict-subsort axis).
    Typed,
    /// Sorts, constructors and functions whose fields admit every term shape, for the term
    /// positions of every sentence form.
    Terms,
    /// The term base with its constructors imported at module level.
    Imported,
    /// The machine base with a two-child group, `Frame { ret, aux }`, for the order of a nested
    /// initializer's children: its only case is an initializer.
    Nested,
    /// The machine base with its optional cell declared `initial`, for an initializer that
    /// writes it present (`counter: Some(0)`, which `none-in-initializer` advises): its only case
    /// is that initializer.
    Initial,
    /// The machine base's cells, with the same names and declarations, a Set collection whose
    /// instances hold a map cell (`shelf.bag` of `Obj { key, m }`), and K7's driver commands, which
    /// set each cell up in one step: the readable and `cells!` families' templates instantiated
    /// again ([`Family::ReadableRun`], [`Family::CellsRun`]), so that K7 runs them while the machine
    /// base's cases, and the K they record, stay as they are.
    Run,
}

impl Base {
    /// Every base.
    pub const ALL: [Self; 7] = [
        Self::Machine,
        Self::Typed,
        Self::Terms,
        Self::Imported,
        Self::Nested,
        Self::Initial,
        Self::Run,
    ];

    /// The base's own source, with no case: its default initializer and no command.
    #[must_use]
    pub fn preamble(self) -> String {
        self.text().assemble(&[], None)
    }

    fn text(self) -> BaseText {
        match self {
            Self::Machine => machine::machine_base(),
            Self::Typed => machine::typed_base(),
            Self::Terms => terms::base(false),
            Self::Imported => terms::base(true),
            Self::Nested => machine::nested_base(),
            Self::Initial => machine::initial_base(),
            Self::Run => machine::run_base(),
        }
    }
}

/// A base split where cases add to it.
struct BaseText {
    /// Everything before the command family's case variants.
    before_commands: &'static str,
    /// From the end of the command family to the initializer.
    after_commands: &'static str,
    /// The base's own initializer, which an initializer case replaces.
    initializer: &'static str,
    /// Declarations after the initializer.
    after_initializer: &'static str,
}

impl BaseText {
    /// The base with `commands` declared and `initializer` in place of the base's own.
    fn assemble(&self, commands: &[&Command], initializer: Option<&str>) -> String {
        let mut text = self.up_to_initializer(commands);
        text.push_str(initializer.unwrap_or(self.initializer));
        text.push_str(self.after_initializer);
        text
    }

    /// The base up to its initializer, with `commands` declared.
    fn up_to_initializer(&self, commands: &[&Command]) -> String {
        self.declaring(commands).0
    }

    /// The base up to its initializer, with `commands` declared, and the range of each
    /// command's declaration in it.
    fn declaring(&self, commands: &[&Command]) -> (String, Vec<Range<usize>>) {
        let mut text = String::from(self.before_commands);
        let mut declarations = Vec::with_capacity(commands.len());
        for command in commands {
            let start = text.len();
            command.declare(&mut text);
            declarations.push(start..text.len());
        }
        text.push_str(self.after_commands);
        (text, declarations)
    }
}

/// The side of a sentence a construct stands on.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Side {
    /// The matched side: a rule's or claim's left side, a function's arguments.
    Subject,
    /// The written side: a rule's or claim's right side, an equation's value.
    Result,
    /// A `#[k::requires]` condition.
    Guard,
    /// An initializer value.
    Initializer,
}

impl Side {
    /// The side's ID segment.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Subject => "subject",
            Self::Result => "result",
            Self::Guard => "guard",
            Self::Initializer => "initializer",
        }
    }
}

/// The kind of a configuration cell, the context axis of every cell-entry slot.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CellKind {
    /// The computation cell, `KSequence`.
    KSequence,
    /// An ordinary leaf cell.
    Leaf,
    /// A leaf cell of the builtin `List`.
    List,
    /// A leaf cell of the builtin `Map`.
    Map,
    /// A nested group of cells.
    Group,
    /// A `multiplicity = "?"` cell.
    Optional,
    /// A `multiplicity = "*"` collection (`cell_type = "List"`).
    Collection,
    /// A `multiplicity = "*"` collection with `cell_type = "Set"`, whose instances hold a map
    /// cell: only on the run base ([`Base::Run`]), outside [`CellKind::ALL`].
    SetCollection,
}

impl CellKind {
    /// Every kind of the machine base, which the configuration families cross with their
    /// spellings.
    pub const ALL: [Self; 7] = [
        Self::KSequence,
        Self::Leaf,
        Self::List,
        Self::Map,
        Self::Group,
        Self::Optional,
        Self::Collection,
    ];
}

/// A case's command constructor: a variant of its base's command family, used only by that
/// case, so that no two cases of one package match one configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Command {
    /// The variant name, `C` and eight hexadecimal digits of the case ID's hash.
    pub name: String,
    /// The number of fields, `a`, `b`, ...: none for a case whose command binds nothing, two
    /// for a case whose command binds `x` and `y`.
    pub arity: usize,
    /// The sort of every field.
    pub field_sort: &'static str,
    /// The attribute that marks the variant a static clause's production (`#[k::desugar]`,
    /// `#[k::alias]`), for a case whose clause expands it.
    pub marker: Option<&'static str>,
}

impl Command {
    /// The command of the case `id`, with `arity` `Int` fields.
    fn for_case(id: &str, arity: usize) -> Self {
        Self::with_fields(id, arity, "Int")
    }

    /// The command of the case `id`, with `arity` fields of `field_sort`.
    fn with_fields(id: &str, arity: usize, field_sort: &'static str) -> Self {
        Self {
            name: format!("C{:08x}", fnv1a(id)),
            arity,
            field_sort,
            marker: None,
        }
    }

    /// The command, its variant marked by `marker`.
    fn marked(self, marker: Option<&'static str>) -> Self {
        Self { marker, ..self }
    }

    /// The variant's K terminal: its name with a lowercase first letter.
    #[must_use]
    pub fn terminal(&self) -> String {
        self.name.to_lowercase()
    }

    fn declare(&self, text: &mut String) {
        let terminal = self.terminal();
        let marker = self
            .marker
            .map_or_else(String::new, |marker| format!(" {marker}"));
        match self.arity {
            0 => writeln!(
                text,
                "    #[k::syntax(\"{terminal}\")]{marker} {}(),",
                self.name
            ),
            arity => {
                let fields = (0..arity).map(field_name).collect::<Vec<_>>();
                // Parenthesized, so that no production ends at a field: a `KItem` field there
                // would make the family need a precedence chain.
                let template = fields
                    .iter()
                    .map(|field| format!("{{{field}}}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let declared = fields
                    .iter()
                    .map(|field| format!("{field}: {}", self.field_sort))
                    .collect::<Vec<_>>()
                    .join(", ");
                writeln!(
                    text,
                    "    #[k::syntax(\"{terminal}({template})\")]{marker} {} {{ {declared} }},",
                    self.name
                )
            }
        }
        .expect("writing to a String cannot fail");
    }
}

fn field_name(index: usize) -> char {
    char::from(b"abcdefgh"[index])
}

/// The 32-bit FNV-1a hash, which names a case's command and labels after its ID.
fn fnv1a(text: &str) -> u32 {
    text.bytes().fold(0x811c_9dc5, |hash, byte| {
        (hash ^ u32::from(byte)).wrapping_mul(0x0100_0193)
    })
}

/// Why a case needs a package of its own.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OwnReason {
    /// The case is an initializer and replaces its base's: a definition has exactly one.
    Initializer,
    /// The construct fills the computation cell's subject entry, so no command item is left to
    /// keep the case apart from the others of its base.
    ComputationSubject,
}

/// Whether a case shares a package with the other cases of its base.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Packaging {
    /// A rule-level case with its own command constructor.
    Shared(Command),
    /// A case rendered alone on its base.
    Own(OwnReason),
    /// A case with its own command constructor, rendered alone on its base: its construct is a
    /// rule's whole subject, or the computation item before its command, so a construct that
    /// matches what another case's subject matches (`_`, `x`) makes the two rules' heads overlap,
    /// which the overlap check refuses when they are printed together.
    Alone(Command),
}

/// One generated case.
#[derive(Clone, Debug)]
pub struct Case {
    /// The stable ID spelled from the case's axes.
    pub id: String,
    /// The case's family.
    pub family: Family,
    /// The base the case is rendered on.
    pub base: Base,
    /// The side the construct stands on.
    pub side: Side,
    /// The cell kind of a cell-entry slot.
    pub kind: Option<CellKind>,
    /// The construct as written, the last ID segment; for a field-order case, the order's
    /// name, while its spelling is the whole field list.
    pub construct: String,
    /// Whether the case shares its base's package.
    pub packaging: Packaging,
    /// Whether rustc parses the construct's position as Rust before any KRS macro reads it: a
    /// fn body an attribute macro takes (a `#[k::rule]`, `#[k::equation]` or
    /// `#[k::simplification]` result, a `#[k::function]` shorthand) or a `#[k::constant]`
    /// value. A construct rustc's parser refuses there (`y @ P`) is reported by rustc whatever
    /// KRS does, which K2 admits ([`invariants::without_rustc_parse_error`]).
    pub rustc_parses: bool,
    /// A term case's position and its construct's nodes, which the oracle reads
    /// ([`Case::oracle`]); `None` outside the term families.
    pub term: Option<positions::TermCase>,
    /// What K7 runs the case on, and what the run must show ([`k7`]); a case of a family K7 has
    /// no drivers for says so.
    pub k7: k7::K7,
    /// The runs of the case's program on counter-witnesses of its construct, ground terms the
    /// construct must not match (another value, and for an exact collection one with an item
    /// more), each of which must not apply the case's sentence; empty where the construct has
    /// none or its slot reads no witness.
    pub k7_counters: Vec<k7::Run>,
    /// Whether the case's sentence holds no command of its own: a subject's root, which can take
    /// what another case's program holds, so K7 runs it, and the cases beside it, on definitions
    /// apart.
    pub unkeyed: bool,
    /// An attribute case's form and attribute, which the attribute axis's oracle reads
    /// ([`Case::oracle`]); `None` outside the attribute family.
    pub attribute: Option<attributes::Pair>,
    item: String,
    spelling: Range<usize>,
    entry: Range<usize>,
}

impl Case {
    /// The text the case adds to its base: a sentence block, or an initializer `impl`.
    #[must_use]
    pub fn item(&self) -> &str {
        &self.item
    }

    /// The text the case writes of its own, which K8 reads for the form an advice proposes
    /// (`advice::followed_in`): its command's declaration, its item, and, on a base that changes
    /// the machine base's declarations for its case ([`Base::Initial`]), the declarations after
    /// its commands.
    #[must_use]
    pub fn own_source(&self) -> String {
        let mut text = String::new();
        if let Some(command) = self.command() {
            command.declare(&mut text);
        }
        text.push_str(&self.item);
        if self.base == Base::Initial {
            text.push_str(self.base.text().after_commands);
        }
        text
    }

    /// The eight hexadecimal digits of the case ID's hash, which name the case's command
    /// (`C` and the digits), its labels, and its other items.
    #[must_use]
    pub fn tag(&self) -> String {
        format!("{:08x}", fnv1a(&self.id))
    }

    /// The case's command constructor, for a shared case.
    #[must_use]
    pub const fn command(&self) -> Option<&Command> {
        match &self.packaging {
            Packaging::Shared(command) | Packaging::Alone(command) => Some(command),
            Packaging::Own(_) => None,
        }
    }

    /// The oracle's outcome for a term case or an attribute case, `None` for a case of another
    /// family.
    #[must_use]
    pub fn oracle(&self) -> Option<oracle::Outcome> {
        self.term
            .as_ref()
            .map(|term| oracle::expected(term.position, &term.nodes))
            .or_else(|| self.attribute.map(attributes::Pair::expected))
    }

    /// Whether the case replaces its base's initializer.
    #[must_use]
    pub const fn replaces_initializer(&self) -> bool {
        matches!(self.packaging, Packaging::Own(OwnReason::Initializer))
    }

    /// The case rendered alone on its base.
    #[must_use]
    pub fn render(&self) -> Rendered<'_> {
        render(&[self])
    }
}

/// A package source and where each case's ranges lie in it.
#[derive(Clone, Debug)]
pub struct Rendered<'a> {
    /// The complete `src/lib.rs`.
    pub source: String,
    /// The rendered cases, in the order given.
    pub cases: Vec<Placed<'a>>,
}

/// One case's ranges in a rendered source.
#[derive(Clone, Debug)]
pub struct Placed<'a> {
    /// The case.
    pub case: &'a Case,
    /// The case's whole item.
    pub item: Range<usize>,
    /// The construct.
    pub spelling: Range<usize>,
    /// The slot's unit that holds the construct.
    pub entry: Range<usize>,
    /// The declaration of the case's command constructor in its base's command family, for a
    /// shared case.
    pub command: Option<Range<usize>>,
}

impl Placed<'_> {
    /// The narrowest of the case's ranges that contains `range`: `spelling`, `entry`, or
    /// `item`, then `command` for the declaration of its command constructor; `outside` when
    /// none does.
    #[must_use]
    pub fn region(&self, range: &Range<usize>) -> &'static str {
        let contains = |outer: &Range<usize>| outer.start <= range.start && range.end <= outer.end;
        if contains(&self.spelling) {
            "spelling"
        } else if contains(&self.entry) {
            "entry"
        } else if contains(&self.item) {
            "item"
        } else if self.command.as_ref().is_some_and(contains) {
            "command"
        } else {
            "outside"
        }
    }

    /// Whether `range` lies in what the case adds to its base: its item, or its command's
    /// declaration.
    #[must_use]
    pub fn owns(&self, range: &Range<usize>) -> bool {
        self.region(range) != "outside"
    }
}

/// Render cases on their base: the base with every case's command declared, followed by every
/// case's item, or with an initializer case's item in place of the base's initializer.
///
/// # Panics
///
/// Panics if the cases are empty, have different bases, or an own-package case is rendered
/// with another case.
#[must_use]
pub fn render<'a>(cases: &[&'a Case]) -> Rendered<'a> {
    let first = cases.first().expect("at least one case is rendered");
    assert!(
        cases.iter().all(|case| case.base == first.base),
        "cases of one package share a base"
    );
    assert!(
        cases.len() == 1
            || cases
                .iter()
                .all(|case| matches!(case.packaging, Packaging::Shared(_))),
        "a case that is not shared is rendered alone"
    );
    let base = first.base.text();
    let commands = cases
        .iter()
        .filter_map(|case| case.command())
        .collect::<Vec<_>>();
    let (mut source, declarations) = base.declaring(&commands);
    let mut declarations = declarations.into_iter();
    if first.replaces_initializer() {
        let start = source.len();
        source.push_str(&first.item);
        source.push_str(base.after_initializer);
        return Rendered {
            source,
            cases: vec![place(first, start, None)],
        };
    }
    source.push_str(base.initializer);
    source.push_str(base.after_initializer);
    let mut placed = Vec::with_capacity(cases.len());
    for case in cases {
        source.push('\n');
        let command = case.command().and_then(|_| declarations.next());
        placed.push(place(case, source.len(), command));
        source.push_str(&case.item);
    }
    Rendered {
        source,
        cases: placed,
    }
}

fn place(case: &Case, start: usize, command: Option<Range<usize>>) -> Placed<'_> {
    let shift = |range: &Range<usize>| start + range.start..start + range.end;
    Placed {
        case,
        item: start..start + case.item.len(),
        spelling: shift(&case.spelling),
        entry: shift(&case.entry),
        command,
    }
}

/// Every case of every family, in ID order.
///
/// # Panics
///
/// Panics if a shard of the fast tier ([`FRONT_SHARDS`]) holds more than [`FRONT_CASE_CAP`]
/// cases, or if two cases share one ID.
#[must_use]
pub fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    machine::readable(&mut cases);
    machine::claims(&mut cases);
    machine::initializers(&mut cases);
    machine::typed(&mut cases);
    cells::cases(&mut cases);
    machine::readable_runs(&mut cases);
    cells::runs(&mut cases);
    terms::cases(&mut cases);
    cases.sort_by(|left, right| left.id.cmp(&right.id));
    for shard in FRONT_SHARDS {
        let count = cases
            .iter()
            .filter(|case| shard.contains(&case.family))
            .count();
        assert!(
            count <= FRONT_CASE_CAP,
            "{count} class-test cases of the shard {shard:?} exceed the cap of {FRONT_CASE_CAP}"
        );
    }
    if let Some(pair) = cases.windows(2).find(|pair| pair[0].id == pair[1].id) {
        panic!("two class-test cases share the ID {}", pair[0].id);
    }
    cases
}

/// Why K7 runs no counter-witness of a run family's case ([`Family::twin`]), `None` for a case that
/// runs one or a case of another family ([`config_drivers`]).
#[must_use]
pub fn run_counterless(case: &Case) -> Option<&'static str> {
    let kind = case.kind?;
    let plans = match case.family {
        Family::ReadableRun => {
            config_drivers::readable(kind, case.side, &case.construct, case.command())
        }
        Family::CellsRun => config_drivers::cells(kind, case.side, &case.construct, case.command()),
        _ => return None,
    };
    plans.counters.err()
}

/// The collections a run family's subject case reads (`Obj { key: 1, m: map![1 -> 2] }` reads the
/// Set collection's instances, open, and the instance's map, exact), each with the items its
/// witness and its counter-witnesses write there, or why it reads none; `None` for a case of
/// another family, a result case, or a case K7 does not run ([`config_drivers`]).
#[must_use]
pub fn run_readings(case: &Case) -> Option<Result<Vec<Reading>, &'static str>> {
    let kind = case.kind?;
    let readable = match case.family {
        Family::ReadableRun => true,
        Family::CellsRun => false,
        _ => return None,
    };
    config_drivers::readings(readable, kind, case.side, &case.construct)
}

/// What a spelling of the term families matches and denotes, as K7 reads it ([`k7`]).
#[derive(Clone, Debug)]
pub struct SpellingMeaning {
    /// The spelling's family.
    pub family: Family,
    /// The spelling, as reference code writes it.
    pub text: &'static str,
    /// A ground term it matches where a pattern reads it, or why none is.
    pub witness: Result<k7::Ground, &'static str>,
    /// What it denotes where it is built.
    pub value: k7::Meaning,
    /// Ground terms it must not match where a pattern reads it, or why none is stated.
    pub counter: Result<Vec<k7::Ground>, &'static str>,
}

/// What every spelling of the term families matches and denotes, `x` being 1.
#[must_use]
pub fn spelling_meanings() -> Vec<SpellingMeaning> {
    terms::meanings()
}

/// An item under construction: its text and the ranges recorded in it.
struct ItemBuilder {
    text: String,
    spelling: Option<Range<usize>>,
    entry: Option<Range<usize>>,
}

impl ItemBuilder {
    const fn new() -> Self {
        Self {
            text: String::new(),
            spelling: None,
            entry: None,
        }
    }

    fn push(&mut self, text: &str) -> &mut Self {
        self.text.push_str(text);
        self
    }

    /// Push the construct, recording its range as the spelling.
    fn spelling(&mut self, construct: &str) -> &mut Self {
        let start = self.text.len();
        self.text.push_str(construct);
        self.spelling = Some(start..self.text.len());
        self
    }

    /// Push `key: construct`, recording the whole as the entry and the construct as the
    /// spelling.
    fn entry(&mut self, key: &str, construct: &str) -> &mut Self {
        let start = self.text.len();
        self.push(key).push(": ").spelling(construct);
        self.entry = Some(start..self.text.len());
        self
    }

    /// Push the construct as both spelling and entry, for a term position.
    fn term(&mut self, construct: &str) -> &mut Self {
        self.spelling(construct);
        self.entry = self.spelling.clone();
        self
    }

    /// Push `before`, the construct and `after`, recording the whole as the entry and the
    /// construct as the spelling: a construct inside the text of the construct whose opening it
    /// stands in.
    fn inside(&mut self, before: &str, construct: &str, after: &str) -> &mut Self {
        let start = self.text.len();
        self.push(before).spelling(construct).push(after);
        self.entry = Some(start..self.text.len());
        self
    }
}

/// The parts of a case before its ranges are known.
struct CaseSpec {
    family: Family,
    base: Base,
    side: Side,
    kind: Option<CellKind>,
    /// The ID segments between the family and the construct.
    slot: Vec<String>,
    construct: String,
}

impl CaseSpec {
    fn id(&self) -> String {
        let mut id = self.family.name().to_owned();
        for segment in &self.slot {
            id.push('/');
            id.push_str(segment);
        }
        id.push('/');
        id.push_str(&self.construct);
        id
    }

    /// The case's label suffix: eight hexadecimal digits of its ID's hash.
    fn tag(&self) -> String {
        format!("{:08x}", fnv1a(&self.id()))
    }

    fn finish(self, packaging: Packaging, item: &ItemBuilder) -> Case {
        let spelling = item
            .spelling
            .clone()
            .expect("every case records its construct");
        let entry = item.entry.clone().unwrap_or_else(|| spelling.clone());
        Case {
            id: self.id(),
            family: self.family,
            base: self.base,
            side: self.side,
            kind: self.kind,
            construct: self.construct,
            packaging,
            rustc_parses: false,
            term: None,
            k7: k7::K7::skip(
                k7::SkipKind::Form,
                "the readable, claim and `cells!` families read cells the machine and typed bases \
                 start at fixed values, and those bases have no driver commands to set them up \
                 (a claim needs a prover besides)",
            ),
            k7_counters: Vec::new(),
            unkeyed: false,
            attribute: None,
            item: item.text.clone(),
            spelling,
            entry,
        }
    }
}

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
//! - initializers: 7 cell kinds × 16 values, `init/k/k::k![]`, and three field orders,
//!   `init/order/reversed`;
//! - the strict-subsort axis (`Int ≤ Value ≤ Stmt ≤ KItem`): an `Int` literal, a `Value` and a
//!   `Stmt` constructor and an `Int` binder in the `Value`, `Stmt` and `KItem` leaves, a typed
//!   `List` element and `Map` value, a group child, an optional cell and a collection instance,
//!   in readable records, claims and initializers, `readable/result/typed/list/Go()`;
//! - term positions: every `TermTree` shape and literal kind at 29 positions of 11 forms (rule
//!   and local-rule fns, equation fns and tables, the fn shorthand, simplifications, `for Stmt`
//!   rules, readable records and claims, initializers and constants), nesting depth 2 at one
//!   subject position per form that has one, `terms/equation/guard/k::is!(Int, x)`;
//! - the import axis: two bare variants at the same 29 positions under a module-level
//!   `use Cmd::*;`, `import/table/subject/Go()`.
//!
//! A case's ID is spelled from its axes, as above, so the expected-outcome table ([`table`])
//! can match IDs with globs and an ID stays stable when other cases are added. A construct
//! never contains `/`.
//!
//! Every case records three byte ranges: the *spelling* (the construct itself), the *entry*
//! (the smallest unit of the slot that holds the construct, `pc: Some(x)` for a cell entry and
//! the spelling itself for a term position) and the *item* (the whole sentence or initializer
//! the case adds). The ranges are relative to the item's text; [`render`] places them in a
//! package source.
//!
//! **Packaging.** A rule-level case gets its own command constructor, declared in its base's
//! command family, and its subject starts the computation cell with it, so the cases of one
//! base can share a package without two of them matching one configuration
//! ([`Packaging::Shared`]). A case that cannot be kept apart that way needs a package of its
//! own ([`Packaging::Own`]): an initializer, because a definition has exactly one, and a case
//! whose construct fills the computation cell's subject entry, because no command item is left
//! there to tell it from the other cases.
//!
//! **Count.** [`cases`] asserts at most [`FRONT_CASE_CAP`] cases: the fast tier runs every case
//! in-process at about 5.6 ms each, and the cap, not a timed assertion, keeps it inside its
//! budget.

mod cells;
pub mod invariants;
mod machine;
pub mod pending;
pub mod table;
mod terms;

use std::fmt::Write as _;
use std::ops::Range;

/// The most cases [`cases`] may generate: at about 5.6 ms per case in-process, 4,000 cases fit
/// the fast tier's budget single-threaded.
pub const FRONT_CASE_CAP: usize = 4_000;

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
}

impl Family {
    /// Every family, in ID order.
    pub const ALL: [Self; 6] = [
        Self::Readable,
        Self::Claim,
        Self::Cells,
        Self::Init,
        Self::Terms,
        Self::Import,
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
}

impl Base {
    /// Every base.
    pub const ALL: [Self; 4] = [Self::Machine, Self::Typed, Self::Terms, Self::Imported];

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
        let mut text = String::from(self.before_commands);
        for command in commands {
            command.declare(&mut text);
        }
        text.push_str(self.after_commands);
        text
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
}

impl CellKind {
    /// Every kind.
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
        }
    }

    /// The variant's K terminal: its name with a lowercase first letter.
    #[must_use]
    pub fn terminal(&self) -> String {
        self.name.to_lowercase()
    }

    fn declare(&self, text: &mut String) {
        let terminal = self.terminal();
        match self.arity {
            0 => writeln!(text, "    #[k::syntax(\"{terminal}\")] {}(),", self.name),
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
                    "    #[k::syntax(\"{terminal}({template})\")] {} {{ {declared} }},",
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

    /// The case's command constructor, for a shared case.
    #[must_use]
    pub const fn command(&self) -> Option<&Command> {
        match &self.packaging {
            Packaging::Shared(command) => Some(command),
            Packaging::Own(_) => None,
        }
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
}

impl Placed<'_> {
    /// The narrowest of the case's ranges that contains `range`: `spelling`, `entry`, or
    /// `item`; `outside` when none does.
    #[must_use]
    pub fn region(&self, range: &Range<usize>) -> &'static str {
        let contains = |outer: &Range<usize>| outer.start <= range.start && range.end <= outer.end;
        if contains(&self.spelling) {
            "spelling"
        } else if contains(&self.entry) {
            "entry"
        } else if contains(&self.item) {
            "item"
        } else {
            "outside"
        }
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
        cases.len() == 1 || cases.iter().all(|case| case.command().is_some()),
        "a case without a command is rendered alone"
    );
    let base = first.base.text();
    let commands = cases
        .iter()
        .filter_map(|case| case.command())
        .collect::<Vec<_>>();
    if first.replaces_initializer() {
        let start = base.up_to_initializer(&commands).len();
        return Rendered {
            source: base.assemble(&commands, Some(&first.item)),
            cases: vec![place(first, start)],
        };
    }
    let mut source = base.assemble(&commands, None);
    let mut placed = Vec::with_capacity(cases.len());
    for case in cases {
        source.push('\n');
        placed.push(place(case, source.len()));
        source.push_str(&case.item);
    }
    Rendered {
        source,
        cases: placed,
    }
}

fn place(case: &Case, start: usize) -> Placed<'_> {
    let shift = |range: &Range<usize>| start + range.start..start + range.end;
    Placed {
        case,
        item: start..start + case.item.len(),
        spelling: shift(&case.spelling),
        entry: shift(&case.entry),
    }
}

/// Every case of every family, in ID order.
///
/// # Panics
///
/// Panics if the generator produces more than [`FRONT_CASE_CAP`] cases, or two cases with one
/// ID.
#[must_use]
pub fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    machine::readable(&mut cases);
    machine::claims(&mut cases);
    machine::initializers(&mut cases);
    machine::typed(&mut cases);
    cells::cases(&mut cases);
    terms::cases(&mut cases);
    cases.sort_by(|left, right| left.id.cmp(&right.id));
    assert!(
        cases.len() <= FRONT_CASE_CAP,
        "{} class-test cases exceed the cap of {FRONT_CASE_CAP}",
        cases.len()
    );
    if let Some(pair) = cases.windows(2).find(|pair| pair[0].id == pair[1].id) {
        panic!("two class-test cases share the ID {}", pair[0].id);
    }
    cases
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
            item: item.text.clone(),
            spelling,
            entry,
        }
    }
}

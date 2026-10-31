//! The configuration families: readable records, readable claims, initializers, and the
//! strict-subsort axis over typed cells; and the readable records again on the run base
//! ([`Base::Run`]), which K7 runs ([`super::config_drivers`]).
//!
//! The readable records are one slot list instantiated twice, on the machine base and on the run
//! base, rather than copied: the run base declares the machine base's cells under the same names, so
//! each template writes the same item on both, and a spelling added to the family reaches its run
//! twin by construction, while the machine base's items, and the K they record, stay as they are.

use std::sync::LazyLock;

use super::config_drivers;
use super::k7::{Ground, K7, Run, SkipKind, Status};
use super::{
    Base, BaseText, Case, CaseSpec, CellKind, Command, Family, ItemBuilder, OwnReason, Packaging,
    Side,
};

/// The seven cell kinds, each in one cell, over the command family `Cmd`.
///
/// `Int ≤ Value ≤ Stmt`, so a command (`Stmt`) is a computation item. The group `frame` has
/// one child, so a record naming it is complete; the collection `job` is its parent `queue`'s
/// only child, as K requires.
const MACHINE_BEFORE_COMMANDS: &str = r#"use k::KResult;
use k::builtin::{Int, KSequence, List, Map, list};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
"#;

const MACHINE_AFTER_COMMANDS: &str = r#"}

/// A nested group with one child.
#[k::cell]
pub struct Frame {
    #[k::cell]
    pub ret: Int,
}

/// The parent of the `job` collection.
#[k::cell]
pub struct Queue {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub job: Job,
}

/// One instance of the `job` collection.
#[k::cell]
pub struct Job {
    #[k::cell]
    pub payload: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub stack: List,
    #[k::cell]
    pub env: Map,
    #[k::cell(nested)]
    pub frame: Frame,
    #[k::cell(multiplicity = "?")]
    pub counter: Option<Int>,
    #[k::cell(nested)]
    pub queue: Queue,
}

"#;

/// The machine's initializer, field by field: `(cell, value)`, in declaration order. A
/// collection's value is its parent's, which holds the template of one instance.
const MACHINE_FIELDS: [(&str, &str); 7] = [
    ("k", "k::k![pgm]"),
    ("pc", "0"),
    ("stack", "list::empty()"),
    ("env", "k::map![]"),
    ("frame", "Frame { ret: 0 }"),
    ("counter", "Some(0)"),
    ("queue", "Queue { job: Job { payload: 0 } }"),
];

const MACHINE_INITIALIZER: &str = r#"impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            pc: 0,
            stack: list::empty(),
            env: k::map![],
            frame: Frame { ret: 0 },
            counter: Some(0),
            queue: Queue { job: Job { payload: 0 } },
        }
    }
}
"#;

pub(super) fn machine_base() -> BaseText {
    debug_assert_eq!(
        base_initializer(MACHINE_HEADER, &MACHINE_FIELDS),
        MACHINE_INITIALIZER,
        "the machine's initializer lists its fields"
    );
    BaseText {
        before_commands: MACHINE_BEFORE_COMMANDS,
        after_commands: MACHINE_AFTER_COMMANDS,
        initializer: MACHINE_INITIALIZER,
        after_initializer: "",
    }
}

/// The machine's one-child group, which the nested base replaces.
const MACHINE_FRAME: &str = "/// A nested group with one child.
#[k::cell]
pub struct Frame {
    #[k::cell]
    pub ret: Int,
}
";

/// The nested base's group: two children, `ret` declared first.
const NESTED_FRAME: &str = "/// A nested group with two children.
#[k::cell]
pub struct Frame {
    #[k::cell]
    pub ret: Int,
    #[k::cell]
    pub aux: Int,
}
";

/// The nested base's initializer, field by field: the machine's, with both children of `frame`
/// in declaration order and distinct values, so that a K which swaps them shows it.
const NESTED_FIELDS: [(&str, &str); 7] = [
    ("k", "k::k![pgm]"),
    ("pc", "0"),
    ("stack", "list::empty()"),
    ("env", "k::map![]"),
    ("frame", "Frame { ret: 0, aux: 1 }"),
    ("counter", "Some(0)"),
    ("queue", "Queue { job: Job { payload: 0 } }"),
];

/// The machine base with [`NESTED_FRAME`] in place of its group.
static NESTED_AFTER_COMMANDS: LazyLock<String> = LazyLock::new(|| {
    assert!(
        MACHINE_AFTER_COMMANDS.contains(MACHINE_FRAME),
        "the machine base declares its group"
    );
    MACHINE_AFTER_COMMANDS.replacen(MACHINE_FRAME, NESTED_FRAME, 1)
});

static NESTED_INITIALIZER: LazyLock<String> =
    LazyLock::new(|| base_initializer(MACHINE_HEADER, &NESTED_FIELDS));

/// The machine base's optional cell, and the initial base's, which starts present.
const MACHINE_OPTIONAL: &str = "#[k::cell(multiplicity = \"?\")]\n    pub counter";
const INITIAL_OPTIONAL: &str = "#[k::cell(multiplicity = \"?\", initial)]\n    pub counter";

/// The machine base with its optional cell declared `initial`.
static INITIAL_AFTER_COMMANDS: LazyLock<String> = LazyLock::new(|| {
    assert!(
        MACHINE_AFTER_COMMANDS.contains(MACHINE_OPTIONAL),
        "the machine base declares its optional cell"
    );
    MACHINE_AFTER_COMMANDS.replacen(MACHINE_OPTIONAL, INITIAL_OPTIONAL, 1)
});

pub(super) fn initial_base() -> BaseText {
    BaseText {
        before_commands: MACHINE_BEFORE_COMMANDS,
        after_commands: INITIAL_AFTER_COMMANDS.as_str(),
        initializer: MACHINE_INITIALIZER,
        after_initializer: "",
    }
}

pub(super) fn nested_base() -> BaseText {
    BaseText {
        before_commands: MACHINE_BEFORE_COMMANDS,
        after_commands: NESTED_AFTER_COMMANDS.as_str(),
        initializer: NESTED_INITIALIZER.as_str(),
        after_initializer: "",
    }
}

/// The main-cell bases: a computation cell `prog`, not named `k`, and a second one, `code`, in
/// the group `frame`, with the cell-free sentence `step` (a `#[k::rule]` fn, `go => done`),
/// which K runs in the configuration's main cell (`k_surface::main_cell`): the `KSequence` cell
/// that holds the program. Its cases are initializers that place the program in one cell or the
/// other, and the run shows which cell is the main cell.
const MAIN_BEFORE_COMMANDS: &str = r#"use k::builtin::{Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("done")] Done(),
"#;

const MAIN_AFTER_COMMANDS: &str = r"}

/// A cell-free sentence, which K runs in the main cell.
#[k::rule]
fn step(k::term![Cmd::Go()]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Done()
}

/// A group whose one child is a second computation cell.
#[k::cell]
pub struct Frame {
    #[k::cell]
    pub code: KSequence,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub prog: KSequence,
    #[k::cell(nested)]
    pub frame: Frame,
}

";

/// The main-cell base's top-level computation cell, and the `k` base's, named `k`.
const MAIN_TOP: &str = "pub prog: KSequence";
const MAIN_K_TOP: &str = "pub k: KSequence";

/// The main-cell base with its top-level computation cell named `k`, which K takes as the main
/// cell by its name.
static MAIN_K_AFTER_COMMANDS: LazyLock<String> = LazyLock::new(|| {
    assert!(
        MAIN_AFTER_COMMANDS.contains(MAIN_TOP),
        "the main-cell base declares its top-level computation cell"
    );
    MAIN_AFTER_COMMANDS.replacen(MAIN_TOP, MAIN_K_TOP, 1)
});

/// The main-cell base's initializer, field by field: the program in the top-level cell.
const MAIN_FIELDS: [(&str, &str); 2] =
    [("prog", "k::k![pgm]"), ("frame", "Frame { code: k::k![] }")];
const MAIN_K_FIELDS: [(&str, &str); 2] =
    [("k", "k::k![pgm]"), ("frame", "Frame { code: k::k![] }")];

static MAIN_INITIALIZER: LazyLock<String> =
    LazyLock::new(|| base_initializer(MACHINE_HEADER, &MAIN_FIELDS));
static MAIN_K_INITIALIZER: LazyLock<String> =
    LazyLock::new(|| base_initializer(MACHINE_HEADER, &MAIN_K_FIELDS));

pub(super) fn main_base() -> BaseText {
    BaseText {
        before_commands: MAIN_BEFORE_COMMANDS,
        after_commands: MAIN_AFTER_COMMANDS,
        initializer: MAIN_INITIALIZER.as_str(),
        after_initializer: "",
    }
}

pub(super) fn main_k_base() -> BaseText {
    BaseText {
        before_commands: MAIN_BEFORE_COMMANDS,
        after_commands: MAIN_K_AFTER_COMMANDS.as_str(),
        initializer: MAIN_K_INITIALIZER.as_str(),
        after_initializer: "",
    }
}

/// Why K7 does not run a case the table refuses at K2: no definition is emitted, so nothing runs.
pub(super) const REFUSED_AT_K2: &str = "refused at K2, so no definition is emitted to run";

/// The main-cell shapes: the program in the top-level computation cell `prog` (not named `k`),
/// in the computation cell `code` inside the group `frame`, and on the `k` base in `k` and in
/// `code`, beside `k`. Each case's run takes one step, the cell-free `go => done`, which applies
/// in the main cell, the cell that holds the program; `code` beside `k` is refused
/// (`main-cell`), since K would take `k` as the computation cell by its name.
fn main_cells(cases: &mut Vec<Case>) {
    for (base, top, in_code, refused) in [
        (Base::MainCell, "prog", false, false),
        (Base::MainCell, "prog", true, false),
        (Base::MainK, "k", false, false),
        (Base::MainK, "k", true, true),
    ] {
        let main = if in_code { "code" } else { top };
        let spec = CaseSpec {
            family: Family::Init,
            base,
            side: Side::Initializer,
            kind: None,
            slot: vec![
                if base == Base::MainK {
                    "main-k"
                } else {
                    "main"
                }
                .to_owned(),
                main.to_owned(),
            ],
            construct: "k::k![pgm]".to_owned(),
        };
        let mut item = ItemBuilder::new();
        let fields = if base == Base::MainK {
            &MAIN_K_FIELDS
        } else {
            &MAIN_FIELDS
        };
        initializer(
            &mut item,
            MACHINE_HEADER,
            fields,
            |item, cell, value| match (cell == top, in_code) {
                (true, false) => {
                    item.entry(cell, "k::k![pgm]");
                }
                (true, true) => {
                    item.push(cell).push(": k::k![]");
                }
                (false, false) => {
                    item.push(cell).push(": ").push(value);
                }
                (false, true) => {
                    item.push("frame: Frame { ")
                        .entry("code", "k::k![pgm]")
                        .push(" }");
                }
            },
        );
        let mut case = spec.finish(Packaging::Own(OwnReason::Initializer), &item);
        let done = || Ground::Seq(vec![Ground::ctor("Cmd::Done", Vec::new())]);
        let (top_value, code_value) = if in_code {
            (Ground::Seq(Vec::new()), done())
        } else {
            (done(), Ground::Seq(Vec::new()))
        };
        case.k7 = if refused {
            K7::skip(SkipKind::Value, REFUSED_AT_K2)
        } else {
            K7::Run(Run {
                program: "go".to_owned(),
                variables: Vec::new(),
                depth: 1,
                steps: 1,
                cells: vec![
                    (top.to_owned(), top_value),
                    ("frame.code".to_owned(), code_value),
                ],
                status: Status::Value,
            })
        };
        cases.push(case);
    }
}

/// The run base up to its case commands: the machine base's sorts and `go`, and K7's driver
/// commands, each of which sets one cell up ([`RUN_DRIVERS`]).
const RUN_BEFORE_COMMANDS: &str = r#"use k::builtin::{Int, KSequence, List, Map, list};
use k::{KItem, KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

/// `go`, K7's driver commands, then one command per case.
#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("then({a}, {b})")] Then { a: KItem, b: KItem },
    #[k::syntax("skip")] Skip(),
    #[k::syntax("setpc({a})")] SetPc { a: Int },
    #[k::syntax("setstack({a})")] SetStack { a: KItem },
    #[k::syntax("setenv({a})")] SetEnv { a: KItem },
    #[k::syntax("setret({a})")] SetRet { a: Int },
    #[k::syntax("setcounter({a})")] SetCounter { a: Int },
    #[k::syntax("dropcounter")] DropCounter(),
    #[k::syntax("addjob({a})")] AddJob { a: Int },
    #[k::syntax("addobj({a}, {b})")] AddObj { a: Int, b: KItem },
    #[k::syntax("pushjob({a})")] PushJob { a: Int },
"#;

/// The run base's Set collection: its parent and one instance, which holds a map cell.
const RUN_SHELF: &str = "/// The parent of the Set collection `bag`.
#[k::cell]
pub struct Shelf {
    #[k::cell(multiplicity = \"*\", cell_type = \"Set\", nested)]
    pub bag: Obj,
}

/// One instance of the `bag` collection: a key and a map.
#[k::cell]
pub struct Obj {
    #[k::cell]
    pub key: Int,
    #[k::cell]
    pub m: Map,
}

";

/// The machine base's configuration declaration, which the run base extends with its shelf.
const MACHINE_CONFIGURATION: &str = "#[k::configuration]
pub struct Machine {";
const MACHINE_LAST_CELL: &str = "    #[k::cell(nested)]
    pub queue: Queue,
}";
const RUN_LAST_CELLS: &str = "    #[k::cell(nested)]
    pub queue: Queue,
    #[k::cell(nested)]
    pub shelf: Shelf,
}";

/// The machine base's declarations, with the shelf declared before the configuration and held
/// last by it.
static RUN_AFTER_COMMANDS: LazyLock<String> = LazyLock::new(|| {
    assert!(
        MACHINE_AFTER_COMMANDS.contains(MACHINE_CONFIGURATION)
            && MACHINE_AFTER_COMMANDS.contains(MACHINE_LAST_CELL),
        "the machine base declares its configuration, the queue last"
    );
    MACHINE_AFTER_COMMANDS
        .replacen(
            MACHINE_CONFIGURATION,
            &format!("{RUN_SHELF}{MACHINE_CONFIGURATION}"),
            1,
        )
        .replacen(MACHINE_LAST_CELL, RUN_LAST_CELLS, 1)
});

/// The run base's initializer, field by field: the machine's, and the shelf's instance template.
const RUN_FIELDS: [(&str, &str); 8] = [
    ("k", "k::k![pgm]"),
    ("pc", "0"),
    ("stack", "list::empty()"),
    ("env", "k::map![]"),
    ("frame", "Frame { ret: 0 }"),
    ("counter", "Some(0)"),
    ("queue", "Queue { job: Job { payload: 0 } }"),
    ("shelf", "Shelf { bag: Obj { key: 0, m: k::map![] } }"),
];

static RUN_INITIALIZER: LazyLock<String> =
    LazyLock::new(|| base_initializer(MACHINE_HEADER, &RUN_FIELDS));

/// K7's driver rules and the makers of the values the program grammar has no syntax for, as the
/// terms base has them: a program is one `Stmt`, written in the definition's program grammar,
/// which has user productions and literals only, so
///
/// - `then(a, b)` puts `a` before `b` in the computation cell, and `skip` leaves it, which
///   empties it when nothing follows;
/// - `setpc(a)`, `setstack(l)`, `setenv(m)`, `setret(a)` and `setcounter(a)` replace a cell's
///   content (`setcounter` creates the optional cell where the state does not hold it), and
///   `dropcounter` removes it; `addjob(a)` puts an instance at the front of the List collection
///   `job`, and `addobj(a, m)` adds one to the Set collection `bag`; `pushjob(a)` puts a `Job`
///   cell record in its own place at the front of the computation, as a readable result writes a
///   cell record as a computation item;
/// - `memp` and `mput(m, k, v)` build a map, `lemp`, `lone(a)` and `lcat(a, b)` a list, each
///   exactly the value it names.
///
/// None of them is a case's: each case's K is what it adds to this base. The driver rules have
/// priority 10 (11 for the rule that creates the optional cell, which applies only where the cell
/// is absent), ahead of every case's, so that none overlaps a case's rule whose computation cell
/// takes any item (`[x, ..]`): a driver rule applies first where both could, and a case's rule
/// never meets a driver's command but as its witness.
const RUN_DRIVERS: &str = r#"
k::rules! {
    for Machine;

    #[k::rule(priority = 10)]
    then: { k: [Cmd::Then(a, b), ..] } => { k: [a, b, ..] };
    #[k::rule(priority = 10)]
    skip: { k: [Cmd::Skip(), ..] } => { k: [..] };
    #[k::rule(priority = 10)]
    set_pc: { k: [Cmd::SetPc(a), ..], pc: _ } => { k: [..], pc: a };
    #[k::rule(priority = 10)]
    set_stack: { k: [Cmd::SetStack(l), ..], stack: _ } => { k: [..], stack: k::project!(List, l) };
    #[k::rule(priority = 10)]
    set_env: { k: [Cmd::SetEnv(m), ..], env: _ } => { k: [..], env: k::project!(Map, m) };
    #[k::rule(priority = 10)]
    set_ret: { k: [Cmd::SetRet(a), ..], frame: Frame { ret: _ } } => { k: [..], frame: Frame { ret: a } };
    #[k::rule(priority = 10)]
    set_counter: { k: [Cmd::SetCounter(a), ..], counter: Some(_) } => { k: [..], counter: Some(a) };
    #[k::rule(priority = 11)]
    make_counter: { k: [Cmd::SetCounter(a), ..], counter: None } => { k: [..], counter: Some(a) };
    #[k::rule(priority = 10)]
    drop_counter: { k: [Cmd::DropCounter(), ..], counter: Some(_) } => { k: [..], counter: None };
    #[k::rule(priority = 10)]
    add_job: { k: [Cmd::AddJob(a), ..], job: [..] } => { k: [..], job: [Job { payload: a }, ..] };
    #[k::rule(priority = 10)]
    add_obj: { k: [Cmd::AddObj(a, m), ..], bag: { .. } } => { k: [..], bag: { Obj { key: a, m: k::project!(Map, m) }, .. } };
    #[k::rule(priority = 10)]
    push_job: { k: [Cmd::PushJob(a), ..] } => { k: [Job { payload: a, .. }, ..] };
}

#[k::function(partial, syntax = "memp")]
pub fn Memp() -> Term<KItem> {
    k::builtin::map::empty()
}

#[k::function(partial, syntax = "mput({m}, {a}, {b})")]
pub fn Mput(m: Term<KItem>, a: Term<KItem>, b: Term<KItem>) -> Term<KItem> {
    k::builtin::map::update(k::project!(Map, m), a, b)
}

#[k::function(partial, syntax = "lemp")]
pub fn Lemp() -> Term<KItem> {
    k::builtin::list::empty()
}

#[k::function(partial, syntax = "lone({a})")]
pub fn Lone(a: Term<KItem>) -> Term<KItem> {
    k::builtin::list::item(a)
}

#[k::function(partial, syntax = "lcat({a}, {b})")]
pub fn Lcat(a: Term<KItem>, b: Term<KItem>) -> Term<KItem> {
    k::builtin::list::concat(k::project!(List, a), k::project!(List, b))
}
"#;

pub(super) fn run_base() -> BaseText {
    BaseText {
        before_commands: RUN_BEFORE_COMMANDS,
        after_commands: RUN_AFTER_COMMANDS.as_str(),
        initializer: RUN_INITIALIZER.as_str(),
        after_initializer: RUN_DRIVERS,
    }
}

/// The cell of each kind in the machine base.
const fn machine_cell(kind: CellKind) -> &'static str {
    match kind {
        CellKind::KSequence => "k",
        CellKind::Leaf => "pc",
        CellKind::List => "stack",
        CellKind::Map => "env",
        CellKind::Group => "frame",
        CellKind::Optional => "counter",
        CellKind::Collection => "job",
        CellKind::SetCollection => "bag",
    }
}

/// The readable entry spellings: a binder, a wildcard, the four bracket and brace shapes, a
/// literal, the two optional spellings, a group record, and a List collection's front and back
/// instance. `x` and `y` are the binders a result case's command binds.
const READABLE_SPELLINGS: [&str; 13] = [
    "x",
    "_",
    "[..]",
    "[]",
    "[x, ..]",
    "{ .. }",
    "{ y -> x, .. }",
    "0",
    "Some(x)",
    "None",
    "Frame { ret: x }",
    "[Job { payload: x, .. }, ..]",
    "[.., Job { payload: 0, .. }]",
];

/// A readable record or claim clause with `construct` in `kind`'s entry on `side`.
///
/// - Subject: `{ k: [C(), ..], CELL: S } => { k: [..] }`, which only reads the cell.
/// - Result: `{ k: [C(x, y), ..], CELL: OLD } => { k: [..], CELL: S }`; the subject matches the
///   cell because a result cannot introduce a cell the subject does not match, and the command
///   binds `x` and `y` for the spelling. `OLD` ([`result_subject`]) is the binder `old` for a
///   cell that holds one value, and the spelling the cell's kind requires otherwise, so that the
///   subject is no case of its own.
/// - The computation cell's subject: `{ k: S, pc: _ } => { pc: 1 }`, which reads the
///   computation and writes another cell, so the rule changes a cell whatever `S` is.
/// - The computation cell's result: `{ k: [C(x, y), ..] } => { k: S }`.
fn record_clause(
    item: &mut ItemBuilder,
    label: &str,
    command: Option<&Command>,
    kind: CellKind,
    side: Side,
    construct: &str,
) {
    let cell = machine_cell(kind);
    item.push(label).push(": { ");
    match (kind, side, command) {
        (CellKind::KSequence, Side::Subject, _) => {
            item.entry(cell, construct).push(", pc: _ } => { pc: 1 }");
        }
        (CellKind::KSequence, _, Some(command)) => {
            item.push(&format!("k: [{}(x, y), ..] }} => {{ ", command.name))
                .entry(cell, construct)
                .push(" }");
        }
        (_, Side::Subject, Some(command)) => {
            item.push(&format!("k: [{}(), ..], ", command.name))
                .entry(cell, construct)
                .push(" } => { k: [..] }");
        }
        (_, _, Some(command)) => {
            item.push(&format!(
                "k: [{}(x, y), ..], {cell}: {} }} => {{ k: [..], ",
                command.name,
                result_subject(kind)
            ))
            .entry(cell, construct)
            .push(" }");
        }
        (_, _, None) => unreachable!("only the computation cell's subject has no command"),
    }
    item.push(";\n");
}

/// What a result case's subject matches in the cell it rewrites: the binder `old`, and for the
/// optional cell and the collection, whose entries `Some`/`None` and an instance list are the
/// only spellings their kinds admit, a present cell and a front instance.
const fn result_subject(kind: CellKind) -> &'static str {
    match kind {
        CellKind::Optional => "Some(old)",
        CellKind::Collection => "[Job { payload: _, .. }, ..]",
        CellKind::SetCollection => "{ .. }",
        _ => "old",
    }
}

/// The Set collection's subject spellings on the run base, the shape NT-10's review M1 needs: an
/// instance whose map cell is exact (`map![1 -> 2]`), one whose key is computed, two whose exact
/// map computes its value or its key, each looked up as the set's element (decision D1a: every
/// cell written, nothing that selects), one whose map reads an entry and leaves the others open
/// (`{ 1 -> 2, .. }`), and an instance record with `..` (`Obj { key: 1, .. }`), which select; and
/// that map written as a literal with an anonymous rest (`map![1 -> 2, ..]`), which names no map
/// in a readable record.
const READABLE_BAG_SUBJECTS: [&str; 7] = [
    "{ Obj { key: 1, m: map![1 -> 2] }, .. }",
    "{ Obj { key: k::builtin::int::add(0, 1), m: map![1 -> 2] }, .. }",
    "{ Obj { key: 1, m: map![1 -> k::builtin::int::add(1, 1)] }, .. }",
    "{ Obj { key: 1, m: map![k::builtin::int::add(0, 1) -> 2] }, .. }",
    "{ Obj { key: 1, m: { 1 -> 2, .. } }, .. }",
    "{ Obj { key: 1, .. }, .. }",
    "{ Obj { key: 1, m: map![1 -> 2, ..] }, .. }",
];

/// The Set collection's result spellings on the run base, over the command's binders `x` and `y`:
/// a new instance whose map cell is exact, one whose key is computed, two whose map computes its
/// value or its key, and one whose map writes `..`.
const READABLE_BAG_RESULTS: [&str; 5] = [
    "{ Obj { key: x, m: map![x -> y] }, .. }",
    "{ Obj { key: k::builtin::int::add(x, 1), m: map![x -> y] }, .. }",
    "{ Obj { key: x, m: map![x -> k::builtin::int::add(y, 1)] }, .. }",
    "{ Obj { key: x, m: map![k::builtin::int::add(x, 1) -> y] }, .. }",
    "{ Obj { key: x, m: map![x -> y, ..] }, .. }",
];

/// Readable records: 7 kinds × 13 spellings × {subject, result}.
pub(super) fn readable(cases: &mut Vec<Case>) {
    record_family(cases, Family::Readable, Base::Machine);
}

/// Readable claims over the same matrix as readable records.
pub(super) fn claims(cases: &mut Vec<Case>) {
    record_family(cases, Family::Claim, Base::Machine);
}

/// The readable records again on the run base, each with K7's plan
/// ([`config_drivers::readable`]), and the Set collection's spellings, which only the run base
/// declares a cell for.
pub(super) fn readable_runs(cases: &mut Vec<Case>) {
    record_family(cases, Family::ReadableRun, Base::Run);
    for (side, spellings) in [
        (Side::Subject, &READABLE_BAG_SUBJECTS[..]),
        (Side::Result, &READABLE_BAG_RESULTS[..]),
    ] {
        for construct in spellings {
            cases.push(record_spelling(
                Family::ReadableRun,
                Base::Run,
                CellKind::SetCollection,
                side,
                construct,
            ));
        }
    }
}

fn record_family(cases: &mut Vec<Case>, family: Family, base: Base) {
    for kind in CellKind::ALL {
        for side in [Side::Subject, Side::Result] {
            for construct in READABLE_SPELLINGS {
                cases.push(record_spelling(family, base, kind, side, construct));
            }
        }
    }
}

/// The record case of `family` on `base` writing `construct` into `kind`'s cell on `side`, with
/// K7's plan where the base has drivers.
fn record_spelling(
    family: Family,
    base: Base,
    kind: CellKind,
    side: Side,
    construct: &str,
) -> Case {
    let spec = CaseSpec {
        family,
        base,
        side,
        kind: Some(kind),
        slot: vec![side.name().to_owned(), machine_cell(kind).to_owned()],
        construct: construct.to_owned(),
    };
    let mut case = record_case(spec, kind, side);
    if base == Base::Run {
        let plans = config_drivers::readable(kind, side, construct, case.command());
        case.k7 = plans.k7;
        case.k7_counters = plans.counters.unwrap_or_default();
    }
    case
}

fn record_case(spec: CaseSpec, kind: CellKind, side: Side) -> Case {
    let packaging = if kind == CellKind::KSequence && side == Side::Subject {
        Packaging::Own(OwnReason::ComputationSubject)
    } else {
        Packaging::Shared(Command::for_case(
            &spec.id(),
            if side == Side::Subject { 0 } else { 2 },
        ))
    };
    let label = format!("case_{}", spec.tag());
    let mut item = ItemBuilder::new();
    let (block, attribute) = match spec.family {
        Family::Claim => ("k::claims!", "    #[k::claim(all_paths)]\n"),
        _ => ("k::rules!", ""),
    };
    item.push(block)
        .push(" {\n    for Machine;\n    use Cmd::*;\n\n")
        .push(attribute)
        .push("    ");
    let command = match &packaging {
        Packaging::Shared(command) | Packaging::Alone(command) => Some(command),
        Packaging::Own(_) => None,
    };
    record_clause(&mut item, &label, command, kind, side, &spec.construct);
    item.push("}\n");
    spec.finish(packaging, &item)
}

/// The initializer values: a literal, the configuration variable, the computation-cell
/// spellings, bracket lists, the builtin empty-collection operations, `map!` spellings (one
/// entry, emitted as K's join, and two whose keys may be equal, emitted as the calls) and the
/// calls the second denotes, the optional spellings, and a group record and a collection
/// instance.
const INITIALIZER_VALUES: [&str; 18] = [
    "0",
    "pgm",
    "k::k![]",
    "k::k![pgm]",
    "k::k![0]",
    "[]",
    "[0]",
    "[pgm]",
    "list::empty()",
    "k::map![]",
    "k::map![0 -> 1]",
    "k::map![pgm -> 1, 0 -> 2]",
    "k::builtin::map::update(k::builtin::map::update(k::builtin::map::empty(), pgm, 1), 0, 2)",
    "k::builtin::map::empty()",
    "Some(0)",
    "None",
    "Frame { ret: 0 }",
    "Job { payload: 0 }",
];

/// A computation cell's value with a remainder: a command item, then the configuration
/// variable's sequence after it, `Go ~> $PGM`. Only a `k!` takes a remainder, so the value
/// stands in the computation cell alone.
const COMPUTATION_REMAINDER: &str = "k::k![Cmd::Go(), ..pgm]";

/// Initializers: 7 kinds × 18 values, each value in place of the base's value of that kind's
/// cell (for the collection, in place of its parent's instance template), the computation
/// cell's remainder, and the field-order axis: the base's initializer with its fields
/// reordered.
pub(super) fn initializers(cases: &mut Vec<Case>) {
    for kind in CellKind::ALL {
        for value in INITIALIZER_VALUES {
            cases.push(cell_value(kind, value));
        }
    }
    cases.push(cell_value(CellKind::KSequence, COMPUTATION_REMAINDER));
    field_order(cases);
    main_cells(cases);
}

/// The machine's initializer with `value` as the value of `kind`'s cell.
fn cell_value(kind: CellKind, value: &str) -> Case {
    let spec = CaseSpec {
        family: Family::Init,
        base: Base::Machine,
        side: Side::Initializer,
        kind: Some(kind),
        slot: vec![machine_cell(kind).to_owned()],
        construct: value.to_owned(),
    };
    let mut item = ItemBuilder::new();
    initializer(
        &mut item,
        MACHINE_HEADER,
        &MACHINE_FIELDS,
        |item, cell, base_value| {
            if cell == machine_cell(kind) {
                item.entry(cell, value);
            } else if kind == CellKind::Collection && cell == "queue" {
                item.push("queue: Queue { ").entry("job", value).push(" }");
            } else {
                item.push(cell).push(": ").push(base_value);
            }
        },
    );
    let mut case = spec.finish(Packaging::Own(OwnReason::Initializer), &item);
    case.k7 = if kind == CellKind::Optional && !matches!(value, "Some(0)" | "None") {
        // An optional cell's value is `Some(..)` or `None`; the table refuses any other.
        K7::skip(SkipKind::Value, REFUSED_AT_K2)
    } else {
        machine_start(&[(machine_cell(kind), machine_value(kind, value))], &[])
    };
    if kind == CellKind::Collection {
        unread_template(&mut case.k7);
    }
    case
}

/// Why an initializer case's run reads nothing of its spelling, for each case K7 runs as
/// liveness only for that reason ([`super::initializer_unread`]).
pub(super) const TEMPLATE_UNREAD: &str = "a collection's initializer writes one instance's template, and the collection starts with no instance: no driver command of the machine or the typed base creates one, so no run reads the template";

/// A collection case's plan reads the configuration's other cells and nothing of the case's
/// spelling, the template of an instance the run never creates ([`TEMPLATE_UNREAD`]).
fn unread_template(plan: &mut K7) {
    if let K7::Run(run) = plan {
        run.status = Status::Liveness;
    }
}

/// The program every initializer case starts with, `go`, which `pgm` is.
fn go() -> Ground {
    Ground::ctor("Cmd::Go", Vec::new())
}

/// What the machine base's cells hold when the run starts, by cell path: every cell of the
/// configuration, with the values the base's own initializer denotes and the program `go`. The
/// optional `counter` written `Some(0)` holds 0 (decision NT-12-6), and the collection `job`,
/// whose initializer writes an instance's template, starts with no instance.
fn machine_cells() -> Vec<(&'static str, Ground)> {
    vec![
        ("k", Ground::Seq(vec![go()])),
        ("pc", Ground::Int(0)),
        ("stack", Ground::List(Vec::new())),
        ("env", Ground::map(Vec::new())),
        ("frame.ret", Ground::Int(0)),
        ("counter", Ground::Int(0)),
        ("queue.job[payload]", Ground::List(Vec::new())),
    ]
}

/// What `value` gives the cell of `kind` when the run starts with the program `go`, or `None`
/// where the generator states nothing: a value of another kind's notation (refused) and a
/// collection's instance template (the collection starts empty). An optional cell written
/// `Some(v)` starts present with `v` and one written `None` starts absent (decision NT-12-6); any
/// other spelling of it is refused, and [`cell_value`] runs none.
fn machine_value(kind: CellKind, value: &str) -> Option<Ground> {
    let items = |items: Vec<Ground>| match kind {
        CellKind::KSequence => Some(Ground::Seq(items)),
        CellKind::List => Some(Ground::List(items)),
        _ => None,
    };
    match (kind, value) {
        (CellKind::KSequence, "pgm" | "k::k![pgm]")
        | (CellKind::KSequence | CellKind::List, "[pgm]") => items(vec![go()]),
        (CellKind::KSequence, "k::k![]") | (CellKind::KSequence | CellKind::List, "[]") => {
            items(Vec::new())
        }
        (CellKind::KSequence, "k::k![0]" | "0") | (CellKind::KSequence | CellKind::List, "[0]") => {
            items(vec![Ground::Int(0)])
        }
        (CellKind::KSequence, "k::k![Cmd::Go(), ..pgm]") => items(vec![go(), go()]),
        (CellKind::List, "list::empty()") => items(Vec::new()),
        (CellKind::Leaf, "0")
        | (CellKind::Optional, "Some(0)")
        | (CellKind::Group, "Frame { ret: 0 }") => Some(Ground::Int(0)),
        (CellKind::Optional, "None") => Some(Ground::Absent),
        (CellKind::Map, "k::map![]" | "k::builtin::map::empty()") => Some(Ground::map(Vec::new())),
        (CellKind::Map, "k::map![0 -> 1]") => {
            Some(Ground::map(vec![(Ground::Int(0), Ground::Int(1))]))
        }
        // Two entries whose keys are `pgm` (`go`) and 0, each written over the map before it.
        (
            CellKind::Map,
            "k::map![pgm -> 1, 0 -> 2]"
            | "k::builtin::map::update(k::builtin::map::update(k::builtin::map::empty(), pgm, 1), 0, 2)",
        ) => Some(Ground::map(vec![
            (go(), Ground::Int(1)),
            (Ground::Int(0), Ground::Int(2)),
        ])),
        _ => None,
    }
}

/// K7's plan for an initializer case: the run starts with the program `go` and the
/// configuration variables `variables`, takes no step, and the cells hold the machine base's
/// values (`machine_cells`) with `changed` in place of theirs: a changed cell's value where
/// the generator states it, the cell left unread where it does not.
fn machine_start(changed: &[(&str, Option<Ground>)], variables: &[(&str, &str)]) -> K7 {
    start_with(machine_cells(), changed, variables)
}

fn start_with(
    cells: Vec<(&'static str, Ground)>,
    changed: &[(&str, Option<Ground>)],
    variables: &[(&str, &str)],
) -> K7 {
    let mut status = Status::Value;
    let mut read = Vec::new();
    let mut cells = cells;
    // A changed cell the base's list does not read (an optional cell) is read where its value is
    // stated.
    for (changed, value) in changed {
        if value.is_some()
            && !cells
                .iter()
                .any(|(cell, _)| cell == changed || cell.starts_with(&format!("{changed}.")))
        {
            cells.push((changed, Ground::Any));
        }
    }
    for (cell, value) in cells {
        // A group cell's child is read by its path below the group: `frame.ret` for `frame`.
        let changed_value = changed
            .iter()
            .find(|(changed, _)| *changed == cell || cell.starts_with(&format!("{changed}.")));
        match changed_value {
            Some((_, Some(value))) => read.push((cell.to_owned(), value.clone())),
            Some((_, None)) => status = Status::Liveness,
            None => read.push((cell.to_owned(), value)),
        }
    }
    K7::Run(Run {
        program: "go".to_owned(),
        variables: variables
            .iter()
            .map(|(name, text)| ((*name).to_owned(), (*text).to_owned()))
            .collect(),
        depth: 0,
        steps: 0,
        cells: read,
        status,
    })
}

/// The field-order axis: a Rust struct literal's field order has no meaning, so every
/// order is the base's initializer. The construct is the whole field list; for the nested
/// group's order, on the nested base, it is the group's field list.
fn field_order(cases: &mut Vec<Case>) {
    let mut reversed = MACHINE_FIELDS;
    reversed.reverse();
    let mut swapped = MACHINE_FIELDS;
    swapped.swap(0, 1);
    let mut last_first = MACHINE_FIELDS;
    last_first.rotate_right(1);
    for (name, fields) in [
        ("reversed", reversed),
        ("pc-first", swapped),
        ("queue-first", last_first),
    ] {
        let spec = CaseSpec {
            family: Family::Init,
            base: Base::Machine,
            side: Side::Initializer,
            kind: None,
            slot: vec!["order".to_owned()],
            construct: name.to_owned(),
        };
        let mut item = ItemBuilder::new();
        let mut start = None;
        let mut end = 0;
        initializer(&mut item, MACHINE_HEADER, &fields, |item, cell, value| {
            start.get_or_insert(item.text.len());
            item.push(cell).push(": ").push(value);
            end = item.text.len();
        });
        let range = start.expect("the base has fields")..end;
        item.spelling = Some(range.clone());
        item.entry = Some(range);
        let mut case = spec.finish(Packaging::Own(OwnReason::Initializer), &item);
        case.k7 = machine_start(&[], &[]);
        cases.push(case);
    }
    cases.push(nested_reversed());
    cases.push(initial_present());
}

/// The initial base's initializer, its optional cell declared `initial`, writing that cell
/// present: the form `none-in-initializer` advises. The run starts with the cell holding `0`.
fn initial_present() -> Case {
    let spec = CaseSpec {
        family: Family::Init,
        base: Base::Initial,
        side: Side::Initializer,
        kind: Some(CellKind::Optional),
        slot: vec!["initial".to_owned()],
        construct: "Some(0)".to_owned(),
    };
    let mut item = ItemBuilder::new();
    initializer(
        &mut item,
        MACHINE_HEADER,
        &MACHINE_FIELDS,
        |item, cell, value| {
            if cell == "counter" {
                item.entry(cell, "Some(0)");
            } else {
                item.push(cell).push(": ").push(value);
            }
        },
    );
    let mut case = spec.finish(Packaging::Own(OwnReason::Initializer), &item);
    case.k7 = start_with(machine_cells(), &[], &[]);
    case
}

/// The nested base's initializer with its group's two children in the reverse of their
/// declaration order. The spelling is the group's field list, the entry the group's cell entry.
fn nested_reversed() -> Case {
    let spec = CaseSpec {
        family: Family::Init,
        base: Base::Nested,
        side: Side::Initializer,
        kind: None,
        slot: vec!["order".to_owned()],
        construct: "nested-reversed".to_owned(),
    };
    let mut item = ItemBuilder::new();
    initializer(
        &mut item,
        MACHINE_HEADER,
        &NESTED_FIELDS,
        |item, cell, value| {
            if cell == "frame" {
                let start = item.text.len();
                item.push("frame: Frame { ")
                    .spelling("aux: 1, ret: 0")
                    .push(" }");
                item.entry = Some(start..item.text.len());
            } else {
                item.push(cell).push(": ").push(value);
            }
        },
    );
    let mut case = spec.finish(Packaging::Own(OwnReason::Initializer), &item);
    let mut cells = machine_cells();
    cells.push(("frame.aux", Ground::Int(1)));
    case.k7 = start_with(cells, &[], &[]);
    case
}

/// The machine's initializer up to its first field.
const MACHINE_HEADER: &str = "impl Machine {\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {\n        Self {\n";

/// An initializer `impl` from `header` and `fields`, each written by `field`.
fn initializer(
    item: &mut ItemBuilder,
    header: &str,
    fields: &[(&str, &str)],
    mut field: impl FnMut(&mut ItemBuilder, &str, &str),
) {
    item.push(header);
    for (cell, value) in fields {
        item.push("            ");
        field(item, cell, value);
        item.push(",\n");
    }
    item.push("        }\n    }\n}\n");
}

/// A base's own initializer: `header` and `fields` as listed.
fn base_initializer(header: &str, fields: &[(&str, &str)]) -> String {
    let mut item = ItemBuilder::new();
    initializer(&mut item, header, fields, |item, cell, value| {
        item.push(cell).push(": ").push(value);
    });
    item.text
}

/// The typed base: cells whose content sort is `Value`, strictly between `Int` and `Stmt`, of
/// every kind but the computation cell, and leaves of `Stmt` and `KItem`.
const TYPED_BEFORE_COMMANDS: &str = r#"use k::{KItem, KResult};
use k::builtin::{Int, KSequence, List, Map, list};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Value, result = KResult)]
#[rustfmt::skip]
pub enum Val {
    #[k::syntax("unit")] Unit(),
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("setstmt")] SetStmt(),
"#;

const TYPED_AFTER_COMMANDS: &str = r#"}

/// A nested group with one `Value` child.
#[k::cell]
pub struct Boxed {
    #[k::cell]
    pub inner: Value,
}

/// The parent of the `slot` collection.
#[k::cell]
pub struct Slots {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub slot: Slot,
}

/// One instance of the `slot` collection.
#[k::cell]
pub struct Slot {
    #[k::cell]
    pub item: Value,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub leaf: Value,
    #[k::cell]
    pub stmt: Stmt,
    #[k::cell]
    pub any: KItem,
    #[k::cell]
    pub list: List<Value>,
    #[k::cell]
    pub map: Map<Int, Value>,
    #[k::cell(nested)]
    pub boxed: Boxed,
    #[k::cell(multiplicity = "?")]
    pub opt: Option<Value>,
    #[k::cell(nested)]
    pub slots: Slots,
}

// K7's one driver command on the typed base: it writes a `Stmt` into `stmt`, whose declared sort
// is `Stmt` whatever its initial value's sort (`Val::Unit()`, a `Value`).
k::rules! {
    for Machine;
    use Cmd::*;

    set_stmt: { k: [SetStmt(), ..], stmt: _ } => { k: [..], stmt: Go() };
}

"#;

/// The typed initializer, field by field: each leaf starts from a value of the cell's own sort
/// (the cases write a strict subsort's, decision NT-16), and the `KItem` leaf from a
/// configuration variable of that type, since no constructor has the sort `KItem`.
const TYPED_FIELDS: [(&str, &str); 9] = [
    ("k", "k::k![pgm]"),
    ("leaf", "Val::Unit()"),
    ("stmt", "Cmd::Go()"),
    ("any", "any"),
    ("list", "list::empty()"),
    ("map", "k::map![]"),
    ("boxed", "Boxed { inner: Val::Unit() }"),
    ("opt", "Some(Val::Unit())"),
    ("slots", "Slots { slot: Slot { item: Val::Unit() } }"),
];

/// The typed initializer up to its first field.
const TYPED_HEADER: &str = "impl Machine {\n    #[k::init]\n    pub fn init(\n        #[k::config_var(name = \"PGM\", main)] pgm: Stmt,\n        #[k::config_var(name = \"ANY\")] any: KItem,\n    ) -> Self {\n        Self {\n";

const TYPED_INITIALIZER: &str = r#"impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "ANY")] any: KItem,
    ) -> Self {
        Self {
            k: k::k![pgm],
            leaf: Val::Unit(),
            stmt: Cmd::Go(),
            any: any,
            list: list::empty(),
            map: k::map![],
            boxed: Boxed { inner: Val::Unit() },
            opt: Some(Val::Unit()),
            slots: Slots { slot: Slot { item: Val::Unit() } },
        }
    }
}
"#;

pub(super) fn typed_base() -> BaseText {
    debug_assert_eq!(
        base_initializer(TYPED_HEADER, &TYPED_FIELDS),
        TYPED_INITIALIZER,
        "the typed initializer lists its fields"
    );
    BaseText {
        before_commands: TYPED_BEFORE_COMMANDS,
        after_commands: TYPED_AFTER_COMMANDS,
        initializer: TYPED_INITIALIZER,
        after_initializer: "",
    }
}

/// The contents of the strict-subsort axis: an `Int` literal (strictly below `Value`), a
/// `Value` constructor, a `Stmt` constructor (strictly above `Value`), and a binder that the
/// command's `Int` field sorts.
const TYPED_CONTENTS: [&str; 4] = ["1", "Unit()", "Go()", "x"];

/// One typed position: the cell, how a subject and a result write a content `C` there, and
/// what a result case's subject matches in the cell.
struct TypedSlot {
    cell: &'static str,
    /// `(before, after)` around the content, in the entry.
    wrap: (&'static str, &'static str),
    /// The subject entry of a result case.
    result_subject: &'static str,
    /// The result entry's wrapping, when it differs from `wrap`.
    result_wrap: Option<(&'static str, &'static str)>,
}

const TYPED_SLOTS: [TypedSlot; 8] = [
    TypedSlot {
        cell: "leaf",
        wrap: ("", ""),
        result_subject: "leaf: _",
        result_wrap: None,
    },
    TypedSlot {
        cell: "stmt",
        wrap: ("", ""),
        result_subject: "stmt: _",
        result_wrap: None,
    },
    TypedSlot {
        cell: "any",
        wrap: ("", ""),
        result_subject: "any: _",
        result_wrap: None,
    },
    TypedSlot {
        cell: "list",
        wrap: ("[", ", ..]"),
        result_subject: "list: [_, ..]",
        result_wrap: None,
    },
    TypedSlot {
        cell: "map",
        wrap: ("{ 0 -> ", ", .. }"),
        result_subject: "map: m",
        result_wrap: Some(("k::builtin::map::update(m, 0, ", ")")),
    },
    TypedSlot {
        cell: "boxed",
        wrap: ("Boxed { inner: ", " }"),
        result_subject: "boxed: _",
        result_wrap: None,
    },
    TypedSlot {
        cell: "opt",
        wrap: ("Some(", ")"),
        result_subject: "opt: Some(_)",
        result_wrap: None,
    },
    TypedSlot {
        cell: "slot",
        wrap: ("[Slot { item: ", ", .. }, ..]"),
        result_subject: "slot: [s @ Slot { item: _, .. }, ..]",
        result_wrap: Some(("[Slot { item: ", ", ..s }, ..]")),
    },
];

/// The strict-subsort axis: readable records, readable claims and initializers that write
/// each content of [`TYPED_CONTENTS`] into each typed position.
///
/// The ID is `family/side/typed/CELL/C`, the construct the content alone, whose range is the
/// content; the entry is the whole cell entry.
pub(super) fn typed(cases: &mut Vec<Case>) {
    for family in [Family::Readable, Family::Claim] {
        for slot in &TYPED_SLOTS {
            for side in [Side::Subject, Side::Result] {
                for content in TYPED_CONTENTS {
                    cases.push(typed_record(family, slot, side, content));
                }
            }
        }
    }
    for slot in &TYPED_SLOTS {
        for content in TYPED_INITIAL_CONTENTS {
            cases.push(typed_initializer(slot.cell, content));
        }
    }
    cases.push(typed_written());
}

/// The typed initializer whose `stmt` starts as `Val::Unit()`, a `Value`, run on `setstmt`,
/// which writes `Cmd::Go()`, a `Stmt` and no `Value`: the cell's sort is its declared `Stmt`,
/// not its initial value's, so the run writes it (decision NT-7-2: K reads a leaf cell's sort
/// from its initial value, and KRS states the declared sort where the value's is narrower).
fn typed_written() -> Case {
    let mut case = typed_initializer_named("stmt-written", "stmt", "Val::Unit()");
    if let K7::Run(run) = &mut case.k7 {
        "setstmt".clone_into(&mut run.program);
        run.depth = 1;
        run.steps = 1;
        for (cell, value) in &mut run.cells {
            match cell.as_str() {
                "k" => *value = Ground::Seq(Vec::new()),
                "stmt" => *value = go(),
                _ => {}
            }
        }
    }
    case
}

fn typed_record(family: Family, slot: &TypedSlot, side: Side, content: &str) -> Case {
    let spec = CaseSpec {
        family,
        base: Base::Typed,
        side,
        kind: None,
        slot: vec![
            side.name().to_owned(),
            "typed".to_owned(),
            slot.cell.to_owned(),
        ],
        construct: content.to_owned(),
    };
    let command = Command::for_case(&spec.id(), if side == Side::Subject { 0 } else { 2 });
    let label = format!("case_{}", spec.tag());
    let (block, attribute) = match family {
        Family::Claim => ("k::claims!", "    #[k::claim(all_paths)]\n"),
        _ => ("k::rules!", ""),
    };
    let mut item = ItemBuilder::new();
    item.push(block)
        .push(" {\n    for Machine;\n    use Cmd::*;\n    use Val::*;\n\n")
        .push(attribute)
        .push("    ")
        .push(&label)
        .push(": { ");
    let (before, after) = if side == Side::Subject {
        item.push(&format!("k: [{}(), ..], ", command.name));
        slot.wrap
    } else {
        item.push(&format!(
            "k: [{}(x, y), ..], {} }} => {{ k: [..], ",
            command.name, slot.result_subject
        ));
        slot.result_wrap.unwrap_or(slot.wrap)
    };
    let entry_start = item.text.len();
    item.push(slot.cell)
        .push(": ")
        .push(before)
        .spelling(content)
        .push(after);
    item.entry = Some(entry_start..item.text.len());
    item.push(if side == Side::Subject {
        " } => { k: [..] };\n}\n"
    } else {
        " };\n}\n"
    });
    spec.finish(Packaging::Shared(command), &item)
}

/// The strict-subsort axis's contents as an initializer writes them: no block imports a
/// constructor, and the binder is the configuration variable `any`.
const TYPED_INITIAL_CONTENTS: [&str; 4] = ["1", "Val::Unit()", "Cmd::Go()", "any"];

/// A typed initializer with `content` as the value of `cell`, inside its group, option, or
/// instance template where the cell has one. The collection `slot` is written in its parent
/// `slots`.
fn typed_initializer(cell: &str, content: &str) -> Case {
    typed_initializer_named(cell, cell, content)
}

/// [`typed_initializer`] under the slot name `slot`.
fn typed_initializer_named(slot: &str, cell: &str, content: &str) -> Case {
    let spec = CaseSpec {
        family: Family::Init,
        base: Base::Typed,
        side: Side::Initializer,
        kind: None,
        slot: vec!["typed".to_owned(), slot.to_owned()],
        construct: content.to_owned(),
    };
    let field_of_cell = if cell == "slot" { "slots" } else { cell };
    // A case that replaces the content of the `any` cell would leave the configuration variable
    // `any` unread, a second mistake; the computation cell reads it instead.
    let any_moved = cell == "any" && content != "any";
    let mut item = ItemBuilder::new();
    initializer(
        &mut item,
        TYPED_HEADER,
        &TYPED_FIELDS,
        |item, field, value| {
            if field == "k" && any_moved {
                item.push(field).push(": k::k![pgm, any]");
                return;
            }
            if field != field_of_cell {
                item.push(field).push(": ").push(value);
                return;
            }
            let (before, after) = match field {
                "list" => ("k::builtin::list::item(", ")"),
                "map" => ("k::map![0 -> ", "]"),
                "boxed" => ("Boxed { inner: ", " }"),
                "opt" => ("Some(", ")"),
                "slots" => ("Slots { slot: Slot { item: ", " } }"),
                _ => ("", ""),
            };
            let start = item.text.len();
            item.push(field)
                .push(": ")
                .push(before)
                .spelling(content)
                .push(after);
            item.entry = Some(start..item.text.len());
        },
    );
    let mut case = spec.finish(Packaging::Own(OwnReason::Initializer), &item);
    case.k7 = typed_start(cell, content);
    case
}

/// K7's plan for a typed initializer case: the run starts with the program `go` and `ANY` bound
/// to 1, takes no step, and every cell holds the typed base's value with `content`'s in `cell`:
/// the optional `opt` written `Some(Val::Unit())` holds the unit (decision NT-12-6), and the
/// collection `slot`, whose initializer writes an instance's template, starts with no instance.
fn typed_start(cell: &str, content: &str) -> K7 {
    let unit = || Ground::ctor("Val::Unit", Vec::new());
    let value = match content {
        "1" | "any" => Ground::Int(1),
        "Val::Unit()" => unit(),
        _ => go(),
    };
    let any_moved = cell == "any" && content != "any";
    let k = if any_moved {
        vec![go(), Ground::Int(1)]
    } else {
        vec![go()]
    };
    let cells = vec![
        ("k", Ground::Seq(k)),
        ("leaf", unit()),
        ("stmt", go()),
        ("any", Ground::Int(1)),
        ("list", Ground::List(Vec::new())),
        ("map", Ground::map(Vec::new())),
        ("boxed.inner", unit()),
        ("opt", unit()),
        ("slots.slot[item]", Ground::List(Vec::new())),
    ];
    let changed = match cell {
        "list" => Some(Ground::List(vec![value])),
        "map" => Some(Ground::map(vec![(Ground::Int(0), value)])),
        "slot" => {
            let mut plan = start_with(cells, &[], &[("ANY", "1")]);
            unread_template(&mut plan);
            return plan;
        }
        _ => Some(value),
    };
    start_with(cells, &[(cell, changed)], &[("ANY", "1")])
}

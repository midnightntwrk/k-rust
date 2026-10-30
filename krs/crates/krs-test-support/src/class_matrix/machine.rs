//! The configuration families: readable records, readable claims, initializers, and the
//! strict-subsort axis over typed cells.

use std::sync::LazyLock;

use super::k7::{Ground, K7, Run, Status};
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

/// The machine base's optional cell, and the nested base's, which starts present.
const MACHINE_OPTIONAL: &str = "#[k::cell(multiplicity = \"?\")]\n    pub counter";
const INITIAL_OPTIONAL: &str = "#[k::cell(multiplicity = \"?\", initial)]\n    pub counter";

/// The machine base with [`NESTED_FRAME`] in place of its group, and its optional cell declared
/// `initial`.
static NESTED_AFTER_COMMANDS: LazyLock<String> = LazyLock::new(|| {
    assert!(
        MACHINE_AFTER_COMMANDS.contains(MACHINE_FRAME)
            && MACHINE_AFTER_COMMANDS.contains(MACHINE_OPTIONAL),
        "the machine base declares its group and its optional cell"
    );
    MACHINE_AFTER_COMMANDS
        .replacen(MACHINE_FRAME, NESTED_FRAME, 1)
        .replacen(MACHINE_OPTIONAL, INITIAL_OPTIONAL, 1)
});

static NESTED_INITIALIZER: LazyLock<String> =
    LazyLock::new(|| base_initializer(MACHINE_HEADER, &NESTED_FIELDS));

pub(super) fn nested_base() -> BaseText {
    BaseText {
        before_commands: MACHINE_BEFORE_COMMANDS,
        after_commands: NESTED_AFTER_COMMANDS.as_str(),
        initializer: NESTED_INITIALIZER.as_str(),
        after_initializer: "",
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
        _ => "old",
    }
}

/// Readable records: 7 kinds × 13 spellings × {subject, result}.
pub(super) fn readable(cases: &mut Vec<Case>) {
    record_family(cases, Family::Readable);
}

/// Readable claims over the same matrix as readable records.
pub(super) fn claims(cases: &mut Vec<Case>) {
    record_family(cases, Family::Claim);
}

fn record_family(cases: &mut Vec<Case>, family: Family) {
    for kind in CellKind::ALL {
        for side in [Side::Subject, Side::Result] {
            for construct in READABLE_SPELLINGS {
                let spec = CaseSpec {
                    family,
                    base: Base::Machine,
                    side,
                    kind: Some(kind),
                    slot: vec![side.name().to_owned(), machine_cell(kind).to_owned()],
                    construct: construct.to_owned(),
                };
                cases.push(record_case(spec, kind, side));
            }
        }
    }
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
    case.k7 = machine_start(&[(machine_cell(kind), machine_value(kind, value))], &[]);
    case
}

/// The program every initializer case starts with, `go`, which `pgm` is.
fn go() -> Ground {
    Ground::ctor("Cmd::Go", Vec::new())
}

/// What the machine base's cells hold when the run starts, by cell path: the base's own
/// initializer's values with the program `go`. The collection `job` starts with no instance and
/// is not read; the optional `counter` is read only by the case that writes it, so that one
/// finding about optional cells (NT-12-6) stays with that case.
fn machine_cells() -> Vec<(&'static str, Ground)> {
    vec![
        ("k", Ground::Seq(vec![go()])),
        ("pc", Ground::Int(0)),
        ("stack", Ground::List(Vec::new())),
        ("env", Ground::map(Vec::new())),
        ("frame.ret", Ground::Int(0)),
    ]
}

/// What `value` gives the cell of `kind` when the run starts with the program `go`, or `None`
/// where the generator states nothing: a value of another kind's notation (refused), the absent
/// optional cell (no value to read), and a collection's instance template (the collection starts
/// empty).
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
        (CellKind::Leaf | CellKind::Optional, "0" | "Some(0)")
        | (CellKind::Group, "Frame { ret: 0 }") => Some(Ground::Int(0)),
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

/// The nested base's initializer, whose optional cell is declared `initial`, writing that cell
/// present: the form `none-in-initializer` advises. The run starts with the cell holding `0`.
fn initial_present() -> Case {
    let spec = CaseSpec {
        family: Family::Init,
        base: Base::Nested,
        side: Side::Initializer,
        kind: Some(CellKind::Optional),
        slot: vec!["initial".to_owned()],
        construct: "Some(0)".to_owned(),
    };
    let mut item = ItemBuilder::new();
    initializer(
        &mut item,
        MACHINE_HEADER,
        &NESTED_FIELDS,
        |item, cell, value| {
            if cell == "counter" {
                item.entry(cell, "Some(0)");
            } else {
                item.push(cell).push(": ").push(value);
            }
        },
    );
    let mut case = spec.finish(Packaging::Own(OwnReason::Initializer), &item);
    let mut cells = machine_cells();
    cells.push(("frame.aux", Ground::Int(1)));
    cells.push(("counter", Ground::Int(0)));
    case.k7 = start_with(cells, &[], &[]);
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

"#;

/// The typed initializer, field by field. A leaf's initial value has exactly the cell's sort,
/// so the `KItem` leaf starts from a configuration variable of that type.
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
    let spec = CaseSpec {
        family: Family::Init,
        base: Base::Typed,
        side: Side::Initializer,
        kind: None,
        slot: vec!["typed".to_owned(), cell.to_owned()],
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
/// to 1, takes no step, and the typed cells hold the typed base's values with `content`'s in
/// `cell` (the collection `slot` starts empty and is not read).
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
    ];
    let changed = match cell {
        "list" => Some(Ground::List(vec![value])),
        "map" => Some(Ground::map(vec![(Ground::Int(0), value)])),
        "slot" => return start_with(cells, &[], &[("ANY", "1")]),
        _ => Some(value),
    };
    start_with(cells, &[(cell, changed)], &[("ANY", "1")])
}

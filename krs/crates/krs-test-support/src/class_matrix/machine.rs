//! The configuration families: readable records, readable claims, initializers, and the
//! strict-subsort axis over typed cells.

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
/// - Result: `{ k: [C(x, y), ..], CELL: old } => { k: [..], CELL: S }`; the subject binds the
///   cell because a result cannot introduce a cell the subject does not match, and the command
///   binds `x` and `y` for the spelling.
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
                "k: [{}(x, y), ..], {cell}: old }} => {{ k: [..], ",
                command.name
            ))
            .entry(cell, construct)
            .push(" }");
        }
        (_, _, None) => unreachable!("only the computation cell's subject has no command"),
    }
    item.push(";\n");
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
        Packaging::Shared(command) => Some(command),
        Packaging::Own(_) => None,
    };
    record_clause(&mut item, &label, command, kind, side, &spec.construct);
    item.push("}\n");
    spec.finish(packaging, &item)
}

/// The initializer values: a literal, the configuration variable, the computation-cell
/// spellings, bracket lists, the builtin empty-collection operations, `map!` spellings, the
/// optional spellings, and a group record and a collection instance.
const INITIALIZER_VALUES: [&str; 16] = [
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
    "k::builtin::map::empty()",
    "Some(0)",
    "None",
    "Frame { ret: 0 }",
    "Job { payload: 0 }",
];

/// Initializers: 7 kinds × 16 values, each value in place of the base's value of that kind's
/// cell (for the collection, in place of its parent's instance template), and the field-order
/// axis: the base's initializer with its fields reordered.
pub(super) fn initializers(cases: &mut Vec<Case>) {
    for kind in CellKind::ALL {
        for value in INITIALIZER_VALUES {
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
            cases.push(spec.finish(Packaging::Own(OwnReason::Initializer), &item));
        }
    }
    field_order(cases);
}

/// The field-order axis: a Rust struct literal's field order has no meaning, so every
/// order is the base's initializer. The construct is the whole field list.
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
        cases.push(spec.finish(Packaging::Own(OwnReason::Initializer), &item));
    }
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
    let mut item = ItemBuilder::new();
    initializer(
        &mut item,
        TYPED_HEADER,
        &TYPED_FIELDS,
        |item, field, value| {
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
    spec.finish(Packaging::Own(OwnReason::Initializer), &item)
}

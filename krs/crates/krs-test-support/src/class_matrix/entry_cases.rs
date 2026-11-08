//! The cell-entry cases as the cells oracle reads them ([`super::cells_oracle`]): each family's
//! spellings declared as [`Spelling`] values, each base's cells as [`Layer`] stacks, and each
//! case's rule ([`Template`]) and context, as the readable, `cells!`, initializer and typed
//! templates write them (`machine.rs` `record_clause`, `typed_record`, `cell_value`;
//! `cells.rs` `case`).
//!
//! [`declared`] is the declaration table: every construct the cell-entry families write, with its
//! spelling as data. The oracle reads the data only, never the text.

use super::cells_oracle::build::{
    alias, bind, call, cell, entries, exact, lit, named, open, open_front, record, seq, some,
    splice, var, wild,
};
use super::cells_oracle::{
    Context, Entry, EntryCase, Form, Group, Layer, Notation, Order, RecordRest, Rest, RestAt,
    Sentence, Spelling, Template, collect_groups,
};
use super::{Base, Case, Family, Side};

fn brackets(items: Vec<Spelling>, rest: Option<(Rest, RestAt)>) -> Spelling {
    Spelling::Brackets(seq(items, rest))
}

fn rec(head: &str, fields: Vec<(&str, Spelling)>, rest: RecordRest) -> Spelling {
    Spelling::Record(record(head, fields, rest))
}

fn frag(head: &str, fields: Vec<(&str, Spelling)>, rest: RecordRest) -> Spelling {
    Spelling::Fragment(record(head, fields, rest))
}

fn map(pairs: Vec<(Spelling, Spelling)>, rest: Option<(Rest, RestAt)>) -> Spelling {
    Spelling::MapLit(entries(pairs, rest))
}

fn kcell(items: Vec<Spelling>, rest: Option<(Rest, RestAt)>) -> Spelling {
    Spelling::KCell(seq(items, rest))
}

fn kmac(items: Vec<Spelling>, rest: Option<(Rest, RestAt)>) -> Spelling {
    Spelling::KMacro(seq(items, rest))
}

/// `k::builtin::int::add(a, b)` and the other two-argument applications.
fn add(a: Spelling, b: Spelling) -> Spelling {
    call(vec![a, b])
}

/// The spelling of every construct the cell-entry families write, and of the other sides their
/// templates write; `None` for a construct of no cell-entry family.
#[must_use]
#[expect(clippy::too_many_lines, reason = "one declaration per construct")]
pub fn declared(construct: &str) -> Option<Spelling> {
    let (x, y) = (|| bind("x"), || bind("y"));
    let obj =
        |key: Spelling, m: Spelling| rec("Obj", vec![("key", key), ("m", m)], RecordRest::Exact);
    let fobj =
        |key: Spelling, m: Spelling| frag("Obj", vec![("key", key), ("m", m)], RecordRest::Exact);
    let braces = |item: Spelling| Spelling::Braces(seq(vec![item], open()));
    let instset = |item: Spelling, rest| Spelling::InstSet(seq(vec![item], rest));
    let update = |a, b, c| call(vec![a, b, c]);
    let two_updates = |key: Spelling| update(update(call(vec![]), key, lit()), y(), lit());
    Some(match construct {
        // Readable entries (`machine::READABLE_SPELLINGS`).
        "x" => x(),
        "_" => wild(),
        "[..]" => brackets(vec![], open()),
        "[]" => brackets(vec![], exact()),
        "[x, ..]" => brackets(vec![x()], open()),
        "{ .. }" => Spelling::Braces(seq(vec![], open())),
        "{ y -> x, .. }" => Spelling::MapRead(entries(vec![(y(), x())], open())),
        "0" | "1" => lit(),
        "Some(x)" => some(x()),
        "None" => Spelling::Missing,
        "Frame { ret: x }" => rec("Frame", vec![("ret", x())], RecordRest::Exact),
        "[Job { payload: x, .. }, ..]" => brackets(
            vec![rec("Job", vec![("payload", x())], RecordRest::Open)],
            open(),
        ),
        "[.., Job { payload: 0, .. }]" => brackets(
            vec![rec("Job", vec![("payload", lit())], RecordRest::Open)],
            open_front(),
        ),
        // `cells!` subject entries (`cells::SUBJECT_SPELLINGS`).
        "k::configuration::Cell(x)" => cell(x()),
        "k::configuration::Cell(_)" => cell(wild()),
        "k::configuration::Cell(0)" => cell(lit()),
        "k::configuration::KCell(x, ..)" => kcell(vec![x()], open()),
        "k::configuration::KCell()" => kcell(vec![], exact()),
        "Some(k::configuration::Cell(x))" => some(cell(x())),
        "k::fragment![crate::Frame { ret: x }]" => {
            frag("Frame", vec![("ret", x())], RecordRest::Exact)
        }
        // A bare `..` after the one child (`cells::cases`): the exact record.
        "k::fragment![crate::Frame { ret: x, .. }]" => {
            frag("Frame", vec![("ret", x())], RecordRest::Open)
        }
        "[k::fragment![crate::Job { payload: x, .. }], instances0 @ ..]" => {
            Spelling::InstList(seq(
                vec![frag("Job", vec![("payload", x())], RecordRest::Open)],
                named("instances0"),
            ))
        }
        "k::configuration::Cell(k::map![y -> x, ..])" => cell(map(vec![(y(), x())], open())),
        "k::configuration::Cell([x, ..])" => cell(brackets(vec![x()], open())),
        // `cells!` result entries (`cells::RESULT_SPELLINGS`).
        "k::configuration::KCell(x)" => kcell(vec![x()], exact()),
        // The computation cell's results over a subject with a rest
        // (`cells::KEPT_COMPUTATION_RESULTS`).
        "k::configuration::KCell(..)" => kcell(vec![], open()),
        "k::configuration::KCell(x, ..r)" => kcell(vec![x()], splice("r")),
        "k::configuration::KCell(..r)" => kcell(vec![], splice("r")),
        "[k::fragment![crate::Job { payload: x, ..old }], ..instances0]" => {
            Spelling::InstList(seq(
                vec![frag(
                    "Job",
                    vec![("payload", x())],
                    RecordRest::Update("old".to_owned()),
                )],
                splice("instances0"),
            ))
        }
        "k::configuration::Cell(k::map![x -> y])" => cell(map(vec![(x(), y())], exact())),
        "k::configuration::Cell(k::map![x -> 1, y -> 2])" => {
            cell(map(vec![(x(), lit()), (y(), lit())], exact()))
        }
        "k::configuration::Cell(k::builtin::map::update(k::builtin::map::update(k::builtin::map::empty(), x, 1), y, 2))" => {
            cell(two_updates(x()))
        }
        "k::configuration::Cell([x, y])" => cell(brackets(vec![x(), y()], exact())),
        // Initializer values (`machine::INITIALIZER_VALUES`, `COMPUTATION_REMAINDER`).
        "pgm" => var("pgm"),
        "k::k![]" => kmac(vec![], exact()),
        "k::k![pgm]" => kmac(vec![var("pgm")], exact()),
        "k::k![0]" => kmac(vec![lit()], exact()),
        "[0]" => brackets(vec![lit()], exact()),
        "[pgm]" => brackets(vec![var("pgm")], exact()),
        "list::empty()"
        | "k::builtin::map::empty()"
        | "Unit()"
        | "Go()"
        | "Val::Unit()"
        | "Cmd::Go()" => call(vec![]),
        "k::map![]" => map(vec![], exact()),
        "k::map![0 -> 1]" => map(vec![(lit(), lit())], exact()),
        "k::map![pgm -> 1, 0 -> 2]" => map(vec![(var("pgm"), lit()), (lit(), lit())], exact()),
        "k::builtin::map::update(k::builtin::map::update(k::builtin::map::empty(), pgm, 1), 0, 2)" => {
            update(update(call(vec![]), var("pgm"), lit()), lit(), lit())
        }
        "Some(0)" => some(lit()),
        "k::absent!(0)" => Spelling::Absent(Box::new(lit())),
        "Frame { ret: 0 }" => rec("Frame", vec![("ret", lit())], RecordRest::Exact),
        "Job { payload: 0 }" => rec("Job", vec![("payload", lit())], RecordRest::Exact),
        "k::k![Cmd::Go(), ..pgm]" => kmac(vec![call(vec![])], splice("pgm")),
        // The typed axis's initializer binder.
        "any" => var("any"),
        // The Set collection's readable entries (`machine::READABLE_BAG_*`).
        "{ Obj { key: 1, m: map![1 -> 2] }, .. }" => {
            braces(obj(lit(), map(vec![(lit(), lit())], exact())))
        }
        "{ Obj { key: k::builtin::int::add(0, 1), m: map![1 -> 2] }, .. }" => {
            braces(obj(add(lit(), lit()), map(vec![(lit(), lit())], exact())))
        }
        "{ Obj { key: 1, m: map![1 -> k::builtin::int::add(1, 1)] }, .. }" => {
            braces(obj(lit(), map(vec![(lit(), add(lit(), lit()))], exact())))
        }
        "{ Obj { key: 1, m: map![k::builtin::int::add(0, 1) -> 2] }, .. }" => {
            braces(obj(lit(), map(vec![(add(lit(), lit()), lit())], exact())))
        }
        "{ Obj { key: 1, m: { 1 -> 2, .. } }, .. }" => braces(obj(
            lit(),
            Spelling::MapRead(entries(vec![(lit(), lit())], open())),
        )),
        "{ Obj { key: 1, .. }, .. }" => braces(rec("Obj", vec![("key", lit())], RecordRest::Open)),
        "{ Obj { key: 1, m: map![1 -> 2, ..] }, .. }" => {
            braces(obj(lit(), map(vec![(lit(), lit())], open())))
        }
        "{ Obj { key: x, m: map![x -> y] }, .. }" => {
            braces(obj(x(), map(vec![(x(), y())], exact())))
        }
        "{ Obj { key: k::builtin::int::add(x, 1), m: map![x -> y] }, .. }" => {
            braces(obj(add(x(), lit()), map(vec![(x(), y())], exact())))
        }
        "{ Obj { key: x, m: map![x -> k::builtin::int::add(y, 1)] }, .. }" => {
            braces(obj(x(), map(vec![(x(), add(y(), lit()))], exact())))
        }
        "{ Obj { key: x, m: map![k::builtin::int::add(x, 1) -> y] }, .. }" => {
            braces(obj(x(), map(vec![(add(x(), lit()), y())], exact())))
        }
        "{ Obj { key: x, m: map![x -> y, ..] }, .. }" => {
            braces(obj(x(), map(vec![(x(), y())], open())))
        }
        // The Set collection's `cells!` entries (`cells::BAG_*`).
        "{ k::fragment![crate::Obj { key: 1, m: k::map![1 -> 2] }], instances0 @ .. }" => instset(
            fobj(lit(), map(vec![(lit(), lit())], exact())),
            named("instances0"),
        ),
        "{ k::fragment![crate::Obj { key: k::builtin::int::add(0, 1), m: k::map![1 -> 2] }], instances0 @ .. }" => {
            instset(
                fobj(add(lit(), lit()), map(vec![(lit(), lit())], exact())),
                named("instances0"),
            )
        }
        "{ k::fragment![crate::Obj { key: 1, m: k::map![1 -> k::builtin::int::add(1, 1)] }], instances0 @ .. }" => {
            instset(
                fobj(lit(), map(vec![(lit(), add(lit(), lit()))], exact())),
                named("instances0"),
            )
        }
        "{ k::fragment![crate::Obj { key: 1, m: k::map![k::builtin::int::add(0, 1) -> 2] }], instances0 @ .. }" => {
            instset(
                fobj(lit(), map(vec![(add(lit(), lit()), lit())], exact())),
                named("instances0"),
            )
        }
        "{ k::fragment![crate::Obj { key: 1, m: k::map![1 -> 2, ..] }], instances0 @ .. }" => {
            instset(
                fobj(lit(), map(vec![(lit(), lit())], open())),
                named("instances0"),
            )
        }
        "{ k::fragment![crate::Obj { key: 1, .. }], instances0 @ .. }" => instset(
            frag("Obj", vec![("key", lit())], RecordRest::Open),
            named("instances0"),
        ),
        "{ k::fragment![crate::Obj { key: x, m: k::map![x -> y] }], ..instances0 }" => instset(
            fobj(x(), map(vec![(x(), y())], exact())),
            splice("instances0"),
        ),
        "{ k::fragment![crate::Obj { key: k::builtin::int::add(x, 1), m: k::map![x -> y] }], ..instances0 }" => {
            instset(
                fobj(add(x(), lit()), map(vec![(x(), y())], exact())),
                splice("instances0"),
            )
        }
        "{ k::fragment![crate::Obj { key: x, m: k::map![x -> k::builtin::int::add(y, 1)] }], ..instances0 }" => {
            instset(
                fobj(x(), map(vec![(x(), add(y(), lit()))], exact())),
                splice("instances0"),
            )
        }
        "{ k::fragment![crate::Obj { key: x, m: k::map![k::builtin::int::add(x, 1) -> y] }], ..instances0 }" => {
            instset(
                fobj(x(), map(vec![(add(x(), lit()), y())], exact())),
                splice("instances0"),
            )
        }
        "{ k::fragment![crate::Obj { key: x, m: k::map![x -> y, ..] }], ..instances0 }" => instset(
            fobj(x(), map(vec![(x(), y())], open())),
            splice("instances0"),
        ),
        // The framed map results and their subjects (`cells::FRAMED_MAP_RESULTS`).
        "k::configuration::Cell(k::map![5 -> old, rest @ ..])" => {
            cell(map(vec![(lit(), bind("old"))], named("rest")))
        }
        "k::configuration::Cell(k::map![5 -> old, ..])" => {
            cell(map(vec![(lit(), bind("old"))], open()))
        }
        "k::configuration::Cell(k::map![x -> y, ..rest])" => {
            cell(map(vec![(x(), y())], splice("rest")))
        }
        "k::configuration::Cell(k::map![x -> 3, y -> 4, ..rest])" => {
            cell(map(vec![(x(), lit()), (y(), lit())], splice("rest")))
        }
        "k::configuration::Cell(k::map![5 -> old, x -> y, ..rest])" => {
            cell(map(vec![(lit(), bind("old")), (x(), y())], splice("rest")))
        }
        "k::configuration::Cell(k::map![5 -> 9, k::builtin::int::add(x, 4) -> y, ..rest])" => cell(
            map(vec![(lit(), lit()), (add(x(), lit()), y())], splice("rest")),
        ),
        "k::configuration::Cell(k::map![0x5 -> y, ..rest])" => {
            cell(map(vec![(lit(), y())], splice("rest")))
        }
        "k::configuration::Cell(k::builtin::map::update(rest, x, y))" => {
            cell(update(bind("rest"), x(), y()))
        }
        "k::configuration::Cell(k::map![y -> k::builtin::map::size(rest)])" => {
            cell(map(vec![(y(), call(vec![bind("rest")]))], exact()))
        }
        "k::configuration::Cell(k::map![5 -> old, x -> y])" => {
            cell(map(vec![(lit(), bind("old")), (x(), y())], exact()))
        }
        // The other sides the templates write.
        "old" => bind("old"),
        "Some(old)" => some(bind("old")),
        "[Job { payload: _, .. }, ..]" => brackets(
            vec![rec("Job", vec![("payload", wild())], RecordRest::Open)],
            open(),
        ),
        "k::configuration::Cell(old)" => cell(bind("old")),
        "Some(k::configuration::Cell(old))" => some(cell(bind("old"))),
        "[old @ k::fragment![crate::Job { payload: _, .. }], instances0 @ ..]" => {
            Spelling::InstList(seq(
                vec![alias(
                    "old",
                    frag("Job", vec![("payload", wild())], RecordRest::Open),
                )],
                named("instances0"),
            ))
        }
        "{ instances0 @ .. }" => Spelling::InstSet(seq(vec![], named("instances0"))),
        _ => return None,
    })
}

fn declare(construct: &str) -> Spelling {
    declared(construct)
        .unwrap_or_else(|| panic!("the cell-entry spelling `{construct}` is declared"))
}

const fn leaf(notation: Notation) -> Layer {
    Layer::Leaf(notation)
}

fn group(name: &str, children: Vec<(&str, Vec<Layer>)>) -> Layer {
    Layer::Group(Group {
        name: name.to_owned(),
        children: children
            .into_iter()
            .map(|(child, stack)| (child.to_owned(), stack))
            .collect(),
    })
}

/// The stack of the machine and run bases' cell `cell` (P1): its own layers, under its plain
/// groups (a plain group above a cell adds no layer to its entry, §2.3).
///
/// # Panics
///
/// Panics if the bases declare no cell `cell`.
#[must_use]
pub fn machine_stack(cell: &str) -> Vec<Layer> {
    machine_stack_of(cell).unwrap_or_else(|| panic!("the machine base has no cell `{cell}`"))
}

fn machine_stack_of(cell: &str) -> Option<Vec<Layer>> {
    let int = || vec![leaf(Notation::Plain)];
    Some(match cell {
        "k" | "prog" | "code" => vec![Layer::Computation],
        "pc" => int(),
        "stack" => vec![leaf(Notation::List)],
        "env" => vec![leaf(Notation::Map)],
        "frame" => vec![group("Frame", vec![("ret", int())])],
        "counter" => vec![Layer::Optional, leaf(Notation::Plain)],
        "job" => vec![
            Layer::Instances(Order::List),
            group("Job", vec![("payload", int())]),
        ],
        "bag" => vec![
            Layer::Instances(Order::Set),
            group(
                "Obj",
                vec![("key", int()), ("m", vec![leaf(Notation::Map)])],
            ),
        ],
        _ => return None,
    })
}

/// The stack of the typed base's cell `cell`.
///
/// # Panics
///
/// Panics if the typed base declares no cell `cell`.
#[must_use]
pub fn typed_stack(cell: &str) -> Vec<Layer> {
    typed_stack_of(cell).unwrap_or_else(|| panic!("the typed base has no cell `{cell}`"))
}

fn typed_stack_of(cell: &str) -> Option<Vec<Layer>> {
    let plain = || vec![leaf(Notation::Plain)];
    Some(match cell {
        "leaf" | "stmt" | "any" => plain(),
        "list" => vec![leaf(Notation::List)],
        "map" => vec![leaf(Notation::Map)],
        "boxed" => vec![group("Boxed", vec![("inner", plain())])],
        "opt" => vec![Layer::Optional, leaf(Notation::Plain)],
        "slot" => vec![
            Layer::Instances(Order::List),
            group("Slot", vec![("item", plain())]),
        ],
        _ => return None,
    })
}

/// P5: a `*` cell's initializer value is one instance's template.
fn initializer_stack(mut stack: Vec<Layer>) -> Vec<Layer> {
    if matches!(stack.first(), Some(Layer::Instances(_))) {
        stack.remove(0);
    }
    stack
}

fn entry(cell: &str, side: Side, stack: Vec<Layer>, spelling: Spelling) -> Entry {
    Entry {
        cell: cell.to_owned(),
        side,
        path: Vec::new(),
        stack,
        spelling,
    }
}

/// The names a result case's subject and command bind (`record_clause`, `cells.rs` `old`).
const BOUND: [&str; 6] = ["x", "y", "old", "instances0", "rest", "tail"];

/// The cell-entry case of `case`, or `None` for a case of no cell-entry slot (a term case, an
/// initializer's field order, the `initial` declaration).
#[must_use]
pub fn entry_case(case: &Case) -> Option<EntryCase> {
    let mut entry = base_entry_case(case)?;
    entry.context.groups = base_groups(case.base);
    Some(entry)
}

/// The groups of `base`'s configuration ([`Context::groups`]), as [`declared_stack`] reads its
/// cells.
fn base_groups(base: Base) -> Vec<Group> {
    if base == Base::Kinds {
        return super::kinds::groups();
    }
    if base == Base::Sweep {
        return super::sweep::groups();
    }
    if base == Base::SweepPaths {
        return super::sweep::paths::groups();
    }
    let stacks = if base == Base::Typed {
        ["leaf", "stmt", "any", "list", "map", "boxed", "opt", "slot"]
            .map(typed_stack)
            .to_vec()
    } else {
        [
            "k", "prog", "code", "pc", "stack", "env", "frame", "counter", "job", "bag",
        ]
        .map(machine_stack)
        .to_vec()
    };
    let mut groups = Vec::new();
    for stack in &stacks {
        collect_groups(stack, &mut groups);
    }
    groups
}

fn base_entry_case(case: &Case) -> Option<EntryCase> {
    if case.base == Base::Kinds {
        return Some(super::kinds::entry_case(case));
    }
    if case.base == Base::Sweep {
        return Some(super::sweep::entry_case(case));
    }
    if case.base == Base::SweepPaths {
        return Some(super::sweep::paths::entry_case(case));
    }
    let segments = case.id.split('/').collect::<Vec<_>>();
    match case.family {
        Family::Readable | Family::Claim | Family::ReadableRun if segments[2] == "typed" => {
            Some(typed_record(case, segments[3]))
        }
        Family::Readable | Family::Claim | Family::ReadableRun => {
            Some(readable_record(case, segments[2]))
        }
        Family::Cells | Family::CellsRun => Some(cells_rule(case, segments[2])),
        Family::Init => match (case.base, segments[1]) {
            (Base::Machine, "order" | "initial") | (Base::Nested | Base::Initial, _) => None,
            (Base::Machine, cell) => Some(machine_initializer(case, cell)),
            (Base::Typed, "typed") => Some(typed_initializer(case, segments[2])),
            (Base::MainCell | Base::MainK, _) => Some(main_initializer(case)),
            _ => None,
        },
        _ => None,
    }
}

fn readable_form(family: Family) -> (Form, Sentence) {
    if family == Family::Claim {
        (Form::Claim, Sentence::Claim)
    } else {
        (Form::Readable, Sentence::Rule)
    }
}

/// A readable record or claim (`record_clause`).
fn readable_record(case: &Case, cell: &str) -> EntryCase {
    let (form, sentence) = readable_form(case.family);
    let stack = machine_stack(cell);
    let spelling = declare(&case.construct);
    let command = |arguments| brackets(vec![call(arguments)], open());
    let (entries, context) = match (cell, case.side) {
        ("k", Side::Subject) => (
            vec![
                entry("pc", Side::Subject, machine_stack("pc"), wild()),
                entry("pc", Side::Result, machine_stack("pc"), lit()),
            ],
            Context::default(),
        ),
        ("k", _) => {
            let other = command(vec![bind("x"), bind("y")]);
            (
                vec![entry("k", Side::Subject, stack.clone(), other.clone())],
                result_context(other),
            )
        }
        (_, Side::Subject) => (
            vec![
                entry("k", Side::Subject, machine_stack("k"), command(vec![])),
                entry(
                    "k",
                    Side::Result,
                    machine_stack("k"),
                    brackets(vec![], open()),
                ),
            ],
            Context::default(),
        ),
        _ => {
            let other = declare(match cell {
                "counter" => "Some(old)",
                "job" => "[Job { payload: _, .. }, ..]",
                "bag" => "{ .. }",
                _ => "old",
            });
            (
                vec![
                    entry(
                        "k",
                        Side::Subject,
                        machine_stack("k"),
                        command(vec![bind("x"), bind("y")]),
                    ),
                    entry(cell, Side::Subject, stack.clone(), other.clone()),
                    entry(
                        "k",
                        Side::Result,
                        machine_stack("k"),
                        brackets(vec![], open()),
                    ),
                ],
                result_context(other),
            )
        }
    };
    EntryCase {
        form,
        entry: entry(cell, case.side, stack, spelling),
        context,
        template: Template {
            sentence,
            entries,
            guard: false,
            variables: Vec::new(),
        },
    }
}

/// A result's context over `other`, the subject's entry of its cell: what the subject's aliases
/// bind are its records.
fn result_context(other: Spelling) -> Context {
    Context {
        bound: BOUND.map(str::to_owned).to_vec(),
        records: super::sweep::records_by(&other),
        other: Some(other),
        written: false,
        groups: Vec::new(),
        fixed_cells: false,
    }
}

/// A `cells!` rule (`cells.rs` `case`).
fn cells_rule(case: &Case, cell: &str) -> EntryCase {
    let stack = machine_stack(cell);
    let spelling = declare(&case.construct);
    let command = |arguments, rest| kcell(vec![call(arguments)], rest);
    let k = || machine_stack("k");
    let (entries, context) = match (cell, case.side) {
        ("k", Side::Subject) => (
            vec![
                entry("pc", Side::Subject, machine_stack("pc"), cell_of(wild())),
                entry("pc", Side::Result, machine_stack("pc"), cell_of(lit())),
            ],
            Context::default(),
        ),
        ("k", _) => {
            // The subject's rest after the command, by the slot's segment after the cell.
            let slot = case
                .id
                .strip_suffix(case.construct.as_str())
                .unwrap_or_default();
            let rest = match slot.rsplit('/').nth(1) {
                Some("rest") => open(),
                Some("named") => named("r"),
                _ => exact(),
            };
            let other = command(vec![bind("x"), bind("y")], rest);
            (
                vec![entry("k", Side::Subject, k(), other.clone())],
                result_context(other),
            )
        }
        (_, Side::Subject) => (
            vec![
                entry("k", Side::Subject, k(), command(vec![], named("tail"))),
                entry("k", Side::Result, k(), kcell(vec![], splice("tail"))),
            ],
            Context::default(),
        ),
        _ => {
            let framed = super::cells::FRAMED_MAP_RESULTS
                .iter()
                .find(|(_, result)| *result == case.construct)
                .filter(|_| cell == "env")
                .map(|(subject, _)| *subject);
            let other = declare(framed.unwrap_or(match cell {
                "pc" | "stack" | "env" => "k::configuration::Cell(old)",
                "counter" => "Some(k::configuration::Cell(old))",
                "job" => "[old @ k::fragment![crate::Job { payload: _, .. }], instances0 @ ..]",
                "bag" => "{ instances0 @ .. }",
                _ => "old",
            }));
            (
                vec![
                    entry(
                        "k",
                        Side::Subject,
                        k(),
                        command(vec![bind("x"), bind("y")], named("tail")),
                    ),
                    entry(cell, Side::Subject, stack.clone(), other.clone()),
                    entry("k", Side::Result, k(), kcell(vec![], splice("tail"))),
                ],
                result_context(other),
            )
        }
    };
    EntryCase {
        form: Form::Cells,
        entry: entry(cell, case.side, stack, spelling),
        context,
        template: Template {
            sentence: Sentence::Rule,
            entries,
            guard: false,
            variables: Vec::new(),
        },
    }
}

fn cell_of(inner: Spelling) -> Spelling {
    cell(inner)
}

/// The machine base's initializer fields as its own initializer writes them, by cell; the
/// collection's value is its instance's template.
fn machine_fields() -> Vec<(&'static str, Spelling)> {
    vec![
        ("k", declare("k::k![pgm]")),
        ("pc", lit()),
        ("stack", call(vec![])),
        ("env", declare("k::map![]")),
        ("frame", declare("Frame { ret: 0 }")),
        ("counter", declare("k::absent!(0)")),
        ("job", declare("Job { payload: 0 }")),
    ]
}

/// The machine's initializer with the case's value in its cell (`cell_value`).
fn machine_initializer(case: &Case, cell: &str) -> EntryCase {
    let entries = machine_fields()
        .into_iter()
        .filter(|(field, _)| *field != cell)
        .map(|(field, value)| {
            entry(
                field,
                Side::Initializer,
                initializer_stack(machine_stack(field)),
                value,
            )
        })
        .collect();
    initializer_case(
        entry(
            cell,
            Side::Initializer,
            initializer_stack(machine_stack(cell)),
            declare(&case.construct),
        ),
        entries,
        vec![("pgm".to_owned(), true)],
    )
}

fn initializer_case(own: Entry, entries: Vec<Entry>, variables: Vec<(String, bool)>) -> EntryCase {
    EntryCase {
        form: Form::Init,
        entry: own,
        context: Context {
            bound: variables.iter().map(|(name, _)| name.clone()).collect(),
            records: Vec::new(),
            other: None,
            written: false,
            groups: Vec::new(),
            fixed_cells: false,
        },
        template: Template {
            sentence: Sentence::Initializer,
            entries,
            guard: false,
            variables,
        },
    }
}

/// The main-cell bases' initializers (`main_cells`): the program in the top-level computation
/// cell (`prog`, or `k`) or in `code`, inside the plain group `frame`.
fn main_initializer(case: &Case) -> EntryCase {
    let segments = case.id.split('/').collect::<Vec<_>>();
    let top = if case.base == Base::MainK {
        "k"
    } else {
        "prog"
    };
    let own = segments[2];
    let other = if own == "code" { top } else { "code" };
    initializer_case(
        entry(
            own,
            Side::Initializer,
            machine_stack(own),
            declare(&case.construct),
        ),
        vec![entry(
            other,
            Side::Initializer,
            machine_stack(other),
            declare("k::k![]"),
        )],
        vec![("pgm".to_owned(), true)],
    )
}

/// A typed position's entry around `content` (`TYPED_SLOTS`): the subject's or the result's
/// wrapping.
fn typed_wrap(cell: &str, side: Side, content: Spelling) -> Spelling {
    match (cell, side) {
        ("list", _) => brackets(vec![content], open()),
        ("map", Side::Subject) => Spelling::MapRead(entries(vec![(lit(), content)], open())),
        ("map", _) => call(vec![bind("m"), lit(), content]),
        ("boxed", _) => rec("Boxed", vec![("inner", content)], RecordRest::Exact),
        ("opt", _) => some(content),
        ("slot", Side::Subject) => brackets(
            vec![rec("Slot", vec![("item", content)], RecordRest::Open)],
            open(),
        ),
        ("slot", _) => brackets(
            vec![rec(
                "Slot",
                vec![("item", content)],
                RecordRest::Update("s".to_owned()),
            )],
            open(),
        ),
        _ => content,
    }
}

/// What a typed result case's subject matches in its cell (`TYPED_SLOTS`' `result_subject`).
fn typed_result_subject(cell: &str) -> Spelling {
    match cell {
        "list" => brackets(vec![wild()], open()),
        "map" => bind("m"),
        "opt" => some(wild()),
        "slot" => brackets(
            vec![alias(
                "s",
                rec("Slot", vec![("item", wild())], RecordRest::Open),
            )],
            open(),
        ),
        _ => wild(),
    }
}

/// A typed readable record or claim (`typed_record`).
fn typed_record(case: &Case, cell: &str) -> EntryCase {
    let (form, sentence) = readable_form(case.family);
    let stack = typed_stack(cell);
    let spelling = typed_wrap(cell, case.side, declare(&case.construct));
    let k = || machine_stack("k");
    let command = |arguments| brackets(vec![call(arguments)], open());
    let (entries, context) = if case.side == Side::Subject {
        (
            vec![
                entry("k", Side::Subject, k(), command(vec![])),
                entry("k", Side::Result, k(), brackets(vec![], open())),
            ],
            Context::default(),
        )
    } else {
        let other = typed_result_subject(cell);
        let mut context = result_context(other.clone());
        context.bound.extend(["m".to_owned(), "s".to_owned()]);
        (
            vec![
                entry("k", Side::Subject, k(), command(vec![bind("x"), bind("y")])),
                entry(cell, Side::Subject, stack.clone(), other),
                entry("k", Side::Result, k(), brackets(vec![], open())),
            ],
            context,
        )
    };
    EntryCase {
        form,
        entry: entry(cell, case.side, stack, spelling),
        context,
        template: Template {
            sentence,
            entries,
            guard: false,
            variables: Vec::new(),
        },
    }
}

/// A typed initializer value around `content` (`typed_initializer_named`).
fn typed_initial(cell: &str, content: Spelling) -> Spelling {
    match cell {
        "list" => call(vec![content]),
        "map" => map(vec![(lit(), content)], exact()),
        "boxed" => rec("Boxed", vec![("inner", content)], RecordRest::Exact),
        "opt" => some(content),
        "slot" => rec("Slot", vec![("item", content)], RecordRest::Exact),
        _ => content,
    }
}

/// The typed initializer with the case's content in its cell (`typed_initializer_named`): the
/// `stmt-written` case writes `stmt`.
fn typed_initializer(case: &Case, slot: &str) -> EntryCase {
    let cell = if slot == "stmt-written" { "stmt" } else { slot };
    let content = declare(&case.construct);
    let any_moved = cell == "any" && content != var("any");
    let unit = || call(vec![]);
    let fields: [(&str, Spelling); 9] = [
        (
            "k",
            kmac(
                if any_moved {
                    vec![var("pgm"), var("any")]
                } else {
                    vec![var("pgm")]
                },
                exact(),
            ),
        ),
        ("leaf", unit()),
        ("stmt", unit()),
        ("any", var("any")),
        ("list", call(vec![])),
        ("map", map(vec![], exact())),
        ("boxed", typed_initial("boxed", unit())),
        ("opt", Spelling::Absent(Box::new(unit()))),
        ("slot", typed_initial("slot", unit())),
    ];
    let stack_of = |field: &str| {
        if field == "k" {
            machine_stack("k")
        } else {
            initializer_stack(typed_stack(field))
        }
    };
    let entries = fields
        .into_iter()
        .filter(|(field, _)| *field != cell)
        .map(|(field, value)| entry(field, Side::Initializer, stack_of(field), value))
        .collect();
    initializer_case(
        entry(
            cell,
            Side::Initializer,
            stack_of(cell),
            typed_initial(cell, content),
        ),
        entries,
        vec![("pgm".to_owned(), true), ("any".to_owned(), false)],
    )
}

/// Whether the test side declares `case`'s base's cell `cell` as a stack of its own: every cell
/// an entry of the base's templates names. A plain group the base's sentences name only on the
/// way to its children (`queue`, `shelf`, the typed base's `slots`, the main bases' `frame`) is
/// not one: its record is read as its children's entries.
#[must_use]
pub fn declares(case: &Case, cell: &str) -> bool {
    match case.base {
        Base::Typed => cell == "k" || typed_stack_of(cell).is_some(),
        Base::MainCell | Base::MainK => matches!(cell, "prog" | "k" | "code"),
        Base::Kinds => cell == "k" || super::kinds::declares(cell),
        Base::Sweep => super::sweep::declares(cell),
        Base::SweepPaths => super::sweep::paths::declares(cell),
        _ => machine_stack_of(cell).is_some(),
    }
}

/// The declared stack of `case`'s cell `cell`, before an initializer reads a collection's
/// template (P5).
#[must_use]
pub fn declared_stack(case: &Case, cell: &str) -> Vec<Layer> {
    if case.base == Base::Kinds {
        super::kinds::stack(cell)
    } else if case.base == Base::Sweep {
        super::sweep::stack(cell)
    } else if case.base == Base::SweepPaths {
        super::sweep::paths::stack(cell)
    } else if case.base == Base::Typed && cell != "k" {
        typed_stack(cell)
    } else {
        machine_stack(cell)
    }
}

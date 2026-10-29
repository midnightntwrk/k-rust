//! `cells!` rules: the reference spelling of a configuration rule, over the machine base.
//!
//! A `cells!` rule declares every subject binder, in first-occurrence order, as a parameter
//! before the subject, so each spelling carries its binders, typed by the position they fill.

use super::{
    Base, Case, CaseSpec, CellKind, Command, Family, ItemBuilder, OwnReason, Packaging, Side,
};

/// How a spelling's binders are declared, by the cell kind it is written into.
#[derive(Clone, Copy)]
enum Binders {
    /// No binder.
    None,
    /// `x`, the whole content of the cell: the kind's content type.
    Whole,
    /// `x`, one computation item or list element: `KItem`.
    Item,
    /// `x`, an `Int` (an optional cell's or a group child's content).
    Int,
    /// `y` and `x`, a map entry's key and value: `KItem`.
    Entry,
}

/// The subject spellings: the leaf and computation wrappers with a binder, a wildcard and a
/// literal, the optional spellings, a bare binder and wildcard (a group's or a collection
/// instance's), a group fragment, a List collection's front instance, a map read, and a list
/// pattern.
const SUBJECT_SPELLINGS: [(&str, Binders); 13] = [
    ("k::configuration::Cell(x)", Binders::Whole),
    ("k::configuration::Cell(_)", Binders::None),
    ("k::configuration::Cell(0)", Binders::None),
    ("k::configuration::KCell(x, ..)", Binders::Item),
    ("k::configuration::KCell()", Binders::None),
    ("Some(k::configuration::Cell(x))", Binders::Int),
    ("None", Binders::None),
    ("x", Binders::Whole),
    ("_", Binders::None),
    ("k::fragment![crate::Frame { ret: x }]", Binders::Int),
    (
        "[k::fragment![crate::Job { payload: x, .. }], instances0 @ ..]",
        Binders::Int,
    ),
    (
        "k::configuration::Cell(k::map![y -> x, ..])",
        Binders::Entry,
    ),
    ("k::configuration::Cell([x, ..])", Binders::Item),
];

/// The result spellings, over the command's `Int` binders `x` and `y`: the wrappers, the
/// optional spellings, a bare binder, a group fragment, a List collection instance that keeps
/// the subject's other instances, a one-entry map (K's join), a two-entry map whose keys may
/// be equal (the calls) and the calls it denotes, and a two-element list.
const RESULT_SPELLINGS: [&str; 13] = [
    "k::configuration::Cell(x)",
    "k::configuration::Cell(0)",
    "k::configuration::KCell(x)",
    "k::configuration::KCell()",
    "Some(k::configuration::Cell(x))",
    "None",
    "x",
    "k::fragment![crate::Frame { ret: x }]",
    "[k::fragment![crate::Job { payload: x, ..old }], ..instances0]",
    "k::configuration::Cell(k::map![x -> y])",
    "k::configuration::Cell(k::map![x -> 1, y -> 2])",
    "k::configuration::Cell(k::builtin::map::update(k::builtin::map::update(k::builtin::map::empty(), x, 1), y, 2))",
    "k::configuration::Cell([x, y])",
];

/// The `cells!` key of each kind's cell: a collection is named through its parent.
const fn key(kind: CellKind) -> &'static str {
    match kind {
        CellKind::KSequence => "k",
        CellKind::Leaf => "pc",
        CellKind::List => "stack",
        CellKind::Map => "env",
        CellKind::Group => "frame",
        CellKind::Optional => "counter",
        CellKind::Collection => "crate::Queue::job",
    }
}

/// The ID segment of each kind's cell, as in the readable family.
const fn cell(kind: CellKind) -> &'static str {
    match kind {
        CellKind::Collection => "job",
        other => key(other),
    }
}

/// The type of a binder that is a cell's whole content.
const fn whole(kind: CellKind) -> &'static str {
    match kind {
        CellKind::KSequence => "k::KItem",
        CellKind::Leaf | CellKind::Optional => "k::Term<k::builtin::Int>",
        CellKind::List => "k::Term<k::builtin::List>",
        CellKind::Map => "k::Term<k::builtin::Map>",
        CellKind::Group => "crate::Frame",
        CellKind::Collection => "crate::Job",
    }
}

fn declare(binders: Binders, kind: CellKind) -> Vec<(&'static str, &'static str)> {
    const INT: &str = "k::Term<k::builtin::Int>";
    match binders {
        Binders::None => Vec::new(),
        Binders::Whole => vec![("x", whole(kind))],
        Binders::Item => vec![("x", "k::KItem")],
        Binders::Int => vec![("x", INT)],
        Binders::Entry => vec![("y", "k::KItem"), ("x", "k::KItem")],
    }
}

/// How a result case's subject binds the cell it rewrites, and the binders that declares: the
/// reference spelling of the readable `CELL: old`, and for the collection its front instance,
/// labelled `old`, with the others as `instances0`.
fn old(kind: CellKind) -> (&'static str, Vec<(&'static str, &'static str)>) {
    match kind {
        CellKind::KSequence => {
            unreachable!("the computation cell's result case binds the command")
        }
        CellKind::Leaf | CellKind::List | CellKind::Map => {
            ("k::configuration::Cell(old)", vec![("old", whole(kind))])
        }
        CellKind::Group => ("old", vec![("old", whole(kind))]),
        CellKind::Optional => (
            "Some(k::configuration::Cell(old))",
            vec![("old", whole(kind))],
        ),
        CellKind::Collection => (
            "[old @ k::fragment![crate::Job { payload: _, .. }], instances0 @ ..]",
            Vec::new(),
        ),
    }
}

/// `cells!` rules: 7 kinds × (13 subject spellings + 13 result spellings).
///
/// - Subject: `CELL: S` after the command, `KCell(C(), tail @ ..)`; the result restores the
///   computation and leaves the cell unchanged.
/// - Result: the subject binds the cell (see [`old`]) after `KCell(C(x, y), tail @ ..)`, and
///   the result writes `CELL: S`.
/// - The computation cell's subject: `k: S, pc: Cell(_)`, and the result writes `pc` only.
/// - The computation cell's result: `k: KCell(C(x, y))`, the whole cell, and the result is
///   `k: S`.
pub(super) fn cases(cases: &mut Vec<Case>) {
    for kind in CellKind::ALL {
        for (construct, binders) in SUBJECT_SPELLINGS {
            cases.push(case(
                kind,
                Side::Subject,
                construct,
                &declare(binders, kind),
            ));
        }
        for construct in RESULT_SPELLINGS {
            cases.push(case(kind, Side::Result, construct, &[]));
        }
    }
}

fn case(kind: CellKind, side: Side, construct: &str, binders: &[(&str, &str)]) -> Case {
    let spec = CaseSpec {
        family: Family::Cells,
        base: Base::Machine,
        side,
        kind: Some(kind),
        slot: vec![side.name().to_owned(), cell(kind).to_owned()],
        construct: construct.to_owned(),
    };
    let tag = spec.tag();
    let packaging = if kind == CellKind::KSequence && side == Side::Subject {
        Packaging::Own(OwnReason::ComputationSubject)
    } else {
        Packaging::Shared(Command::for_case(
            &spec.id(),
            if side == Side::Subject { 0 } else { 2 },
        ))
    };
    let command = match &packaging {
        Packaging::Shared(command) | Packaging::Alone(command) => command.name.clone(),
        Packaging::Own(_) => String::new(),
    };
    let mut parameters = Vec::new();
    if side == Side::Result {
        parameters.push(("x", "k::Term<k::builtin::Int>"));
        parameters.push(("y", "k::Term<k::builtin::Int>"));
    }
    parameters.extend_from_slice(binders);
    let mut item = ItemBuilder::new();
    item.push(&format!(
        "#[k::rule(label = \"case-{tag}\")]\npub fn case_{tag}(\n"
    ));
    let push_parameters = |item: &mut ItemBuilder, parameters: &[(&str, &str)]| {
        for (name, ty) in parameters {
            item.push(&format!("    {name}: {ty},\n"));
        }
    };
    match (kind, side) {
        (CellKind::KSequence, Side::Subject) => {
            push_parameters(&mut item, &parameters);
            item.push("    k::cells! { ")
                .entry(key(kind), construct)
                .push(concat!(
                    ", pc: k::configuration::Cell(_), state @ .. }: crate::Machine,\n",
                    ") -> crate::Machine {\n",
                    "    k::cells! { pc: k::configuration::Cell(1), ..state }\n",
                    "}\n",
                ));
        }
        (CellKind::KSequence, _) => {
            push_parameters(&mut item, &parameters);
            item.push(&format!(
                "    k::cells! {{ k: k::configuration::KCell(crate::Cmd::{command}(x, y)), state @ .. }}: crate::Machine,\n) -> crate::Machine {{\n    k::cells! {{ "
            ))
            .entry(key(kind), construct)
            .push(", ..state }\n}\n");
        }
        (_, Side::Subject) => {
            push_parameters(&mut item, &parameters);
            item.push(&format!(
                "    k::cells! {{ k: k::configuration::KCell(crate::Cmd::{command}(), tail @ ..), "
            ))
            .entry(key(kind), construct)
            .push(concat!(
                ", state @ .. }: crate::Machine,\n",
                ") -> crate::Machine {\n",
                "    k::cells! { k: k::configuration::KCell(..tail), ..state }\n",
                "}\n",
            ));
        }
        (_, _) => {
            let (bound, old_binders) = old(kind);
            parameters.extend(old_binders);
            push_parameters(&mut item, &parameters);
            item.push(&format!(
                "    k::cells! {{ k: k::configuration::KCell(crate::Cmd::{command}(x, y), tail @ ..), {}: {bound}, state @ .. }}: crate::Machine,\n) -> crate::Machine {{\n    k::cells! {{ k: k::configuration::KCell(..tail), ",
                key(kind)
            ))
            .entry(key(kind), construct)
            .push(", ..state }\n}\n");
        }
    }
    spec.finish(packaging, &item)
}

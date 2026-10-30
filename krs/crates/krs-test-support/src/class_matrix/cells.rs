//! `cells!` rules: the reference spelling of a configuration rule, over the machine base, and again
//! over the run base ([`Base::Run`]), which K7 runs (one slot list instantiated twice, as the
//! readable family's).
//!
//! A `cells!` rule declares every subject binder, in first-occurrence order, as a parameter
//! before the subject, so each spelling carries its binders, typed by the position they fill.

use super::config_drivers;
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

/// The Set collection's subject spellings on the run base, as the readable family's
/// (`machine::READABLE_BAG_SUBJECTS`): an instance whose map cell is exact, one whose key is
/// computed, two whose exact map computes its value or its key, and one whose map writes `..`,
/// which selects.
const BAG_SUBJECTS: [&str; 5] = [
    "{ k::fragment![crate::Obj { key: 1, m: k::map![1 -> 2] }], instances0 @ .. }",
    "{ k::fragment![crate::Obj { key: k::builtin::int::add(0, 1), m: k::map![1 -> 2] }], instances0 @ .. }",
    "{ k::fragment![crate::Obj { key: 1, m: k::map![1 -> k::builtin::int::add(1, 1)] }], instances0 @ .. }",
    "{ k::fragment![crate::Obj { key: 1, m: k::map![k::builtin::int::add(0, 1) -> 2] }], instances0 @ .. }",
    "{ k::fragment![crate::Obj { key: 1, m: k::map![1 -> 2, ..] }], instances0 @ .. }",
];

/// The Set collection's result spellings on the run base, over the command's binders: a new
/// instance beside the subject's others (`..instances0`), whose map cell is exact, whose key is
/// computed, whose map computes its value or its key, or whose map writes `..`.
const BAG_RESULTS: [&str; 5] = [
    "{ k::fragment![crate::Obj { key: x, m: k::map![x -> y] }], ..instances0 }",
    "{ k::fragment![crate::Obj { key: k::builtin::int::add(x, 1), m: k::map![x -> y] }], ..instances0 }",
    "{ k::fragment![crate::Obj { key: x, m: k::map![x -> k::builtin::int::add(y, 1)] }], ..instances0 }",
    "{ k::fragment![crate::Obj { key: x, m: k::map![k::builtin::int::add(x, 1) -> y] }], ..instances0 }",
    "{ k::fragment![crate::Obj { key: x, m: k::map![x -> y, ..] }], ..instances0 }",
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
        CellKind::SetCollection => "crate::Shelf::bag",
    }
}

/// The ID segment of each kind's cell, as in the readable family.
const fn cell(kind: CellKind) -> &'static str {
    match kind {
        CellKind::Collection => "job",
        CellKind::SetCollection => "bag",
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
        CellKind::SetCollection => "crate::Obj",
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
        CellKind::SetCollection => ("{ instances0 @ .. }", Vec::new()),
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
    family(cases, Family::Cells, Base::Machine);
}

/// The `cells!` rules again on the run base, each with K7's plan ([`config_drivers::cells`]), and
/// the Set collection's spellings, which only the run base declares a cell for.
pub(super) fn runs(cases: &mut Vec<Case>) {
    family(cases, Family::CellsRun, Base::Run);
    let at = Placement {
        family: Family::CellsRun,
        base: Base::Run,
        kind: CellKind::SetCollection,
    };
    for construct in BAG_SUBJECTS {
        cases.push(at.case(Side::Subject, construct, &[]));
    }
    for construct in BAG_RESULTS {
        cases.push(at.case(Side::Result, construct, &[]));
    }
}

fn family(cases: &mut Vec<Case>, family: Family, base: Base) {
    for kind in CellKind::ALL {
        let at = Placement { family, base, kind };
        for (construct, binders) in SUBJECT_SPELLINGS {
            cases.push(at.case(Side::Subject, construct, &declare(binders, kind)));
        }
        for construct in RESULT_SPELLINGS {
            cases.push(at.case(Side::Result, construct, &[]));
        }
    }
}

/// Where a case's construct stands: its family, base and cell kind.
struct Placement {
    family: Family,
    base: Base,
    kind: CellKind,
}

impl Placement {
    /// The case writing `construct` on `side`, its subject binders `binders`, with K7's plan where
    /// the base has drivers.
    fn case(&self, side: Side, construct: &str, binders: &[(&str, &str)]) -> Case {
        let mut case = case(self.family, self.base, self.kind, side, construct, binders);
        if self.base == Base::Run {
            let plans = config_drivers::cells(self.kind, side, construct, case.command());
            case.k7 = plans.k7;
            case.k7_counter = plans.counter.ok();
        }
        case
    }
}

fn case(
    family: Family,
    base: Base,
    kind: CellKind,
    side: Side,
    construct: &str,
    binders: &[(&str, &str)],
) -> Case {
    let spec = CaseSpec {
        family,
        base,
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

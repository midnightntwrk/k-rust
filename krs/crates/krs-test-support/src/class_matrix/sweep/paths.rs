//! The path sweep (S5.3 part 5): one generated case of [`Family::SweepPaths`] for each rule-form
//! cell of the sweep's main tables below a `?` ancestor and below a `*` ancestor (the rows at the
//! paths `?` and `*` of `cells-outcome-sweep.tsv`), rendered on [`Base::SweepPaths`], whose
//! `krs-class` shard `sweep-paths` makes the compiler a witness of `outcome` there, through the
//! macro, the collector, the lowering and the recorded K, as the root sweep's shard is at the
//! record's level.
//!
//! The base holds the optional group `qopt` (`Q`) and the List collection `line` (`L`), each with
//! one child per stack the main tables name ([`stacks`]), named and renamed per path as
//! `sweep::SLOTS` names the root's: a group is the content of one cell only and a cell's name is
//! its own in the whole configuration. The collection's instance also holds `lid`, an `Int` of
//! its own that the matched results' subject names; no sweep stack is a key, as a List collection
//! has none. A `*` child stands in a plain group of its own, as at the record's level: a `*`
//! cell is its parent's only child (`krs::analysis::collection-siblings`).

use std::collections::BTreeMap;
use std::sync::LazyLock;

use super::super::cells_oracle::{EntryCase, Form, Group, Layer, Notation, Order};
use super::super::kinds::{self, Content, Decl, group, leaf, many, one, opt};
use super::super::{Base, BaseText, Case, Family, Side};
use super::{Built, Cell, Key, Layout, RESULT_BOUND, Slot, build, main_tables, stacks, subject};

/// The path base's cell of each sweep stack below the optional group `qopt`.
const BELOW_OPTIONAL_SLOTS: [Slot; 14] = [
    ("computation", "qprog", &[]),
    ("leaf Int", "qpc", &[]),
    ("leaf List", "qstack", &[]),
    ("leaf Cons", "qseq", &[]),
    ("leaf Map", "qenv", &[]),
    ("leaf Set", "qset", &[]),
    (
        "group G",
        "qframe",
        &[("G", "Qg"), ("a", "qa"), ("b", "qb")],
    ),
    ("? leaf Int", "qcounter", &[]),
    ("? leaf List", "qolist", &[]),
    ("? leaf Map", "qomap", &[]),
    (
        "? group G",
        "qogroup",
        &[("G", "Qgp"), ("a", "qpa"), ("b", "qpb")],
    ),
    (
        "* List of G",
        "qjob",
        &[("G", "Qgl"), ("a", "qla"), ("b", "qlb")],
    ),
    (
        "* Set of G",
        "qbag",
        &[("G", "Qgs"), ("a", "qsa"), ("b", "qsb")],
    ),
    (
        "* Map of G",
        "qacct",
        &[("G", "Qgm"), ("a", "qma"), ("b", "qmb")],
    ),
];

/// The path base's cell of each sweep stack in the List collection `line`'s instance.
const BELOW_INSTANCES_SLOTS: [Slot; 14] = [
    ("computation", "lprog", &[]),
    ("leaf Int", "lpc", &[]),
    ("leaf List", "lstack", &[]),
    ("leaf Cons", "lseq", &[]),
    ("leaf Map", "lenv", &[]),
    ("leaf Set", "lset", &[]),
    (
        "group G",
        "lframe",
        &[("G", "Lg"), ("a", "la"), ("b", "lb")],
    ),
    ("? leaf Int", "lcounter", &[]),
    ("? leaf List", "lolist", &[]),
    ("? leaf Map", "lomap", &[]),
    (
        "? group G",
        "logroup",
        &[("G", "Lgp"), ("a", "lpa"), ("b", "lpb")],
    ),
    (
        "* List of G",
        "ljob",
        &[("G", "Lgl"), ("a", "lla"), ("b", "llb")],
    ),
    (
        "* Set of G",
        "lbag",
        &[("G", "Lgs"), ("a", "lsa"), ("b", "lsb")],
    ),
    (
        "* Map of G",
        "lacct",
        &[("G", "Lgm"), ("a", "lma"), ("b", "lmb")],
    ),
];

/// One cell of each slot's stack, named and renamed as the slot says; a `*` cell in a plain group
/// of its own (`qqueue`, `Qqueue`).
fn children(slots: &[Slot]) -> Vec<Decl> {
    let int = || leaf(Notation::Plain);
    slots
        .iter()
        .map(|(stack, cell, renames)| {
            let to = |name: &str| {
                renames
                    .iter()
                    .find(|(from, _)| *from == name)
                    .map_or_else(|| panic!("{cell} renames no `{name}`"), |(_, to)| *to)
            };
            let g = || group(to("G"), vec![one(to("a"), int()), one(to("b"), int())]);
            let notation = |name: &str| match name {
                "Int" => Notation::Plain,
                "List" => Notation::List,
                "Cons" => Notation::Cons,
                "Map" => Notation::Map,
                "Set" => Notation::Set,
                other => panic!("no leaf {other}"),
            };
            let collection = |order: Order, wrapper: &str| {
                let mut head = cell[..1].to_uppercase();
                head.push_str(wrapper);
                one(
                    &format!("{}{wrapper}", &cell[..1]),
                    group(&head, vec![many(cell, order, g())]),
                )
            };
            match *stack {
                "computation" => one(cell, Content::Comp),
                "group G" => one(cell, g()),
                "? group G" => opt(cell, g()),
                "* List of G" => collection(Order::List, "queue"),
                "* Set of G" => collection(Order::Set, "shelf"),
                "* Map of G" => collection(Order::Map, "bank"),
                other => match other.strip_prefix("? leaf ") {
                    Some(name) => opt(cell, leaf(notation(name))),
                    None => one(
                        cell,
                        leaf(notation(
                            other
                                .strip_prefix("leaf ")
                                .unwrap_or_else(|| panic!("no sweep stack {other}")),
                        )),
                    ),
                },
            }
        })
        .collect()
}

/// The path base's configuration: the main computation `k`, whose command each case matches; the
/// group `G` (`frame`) that a leaf's record spelling names, as at the record's level; the optional
/// group `qopt`; and the List collection `line`.
fn configuration() -> Vec<Decl> {
    let int = || leaf(Notation::Plain);
    let mut instance = vec![one("lid", int())];
    instance.extend(children(&BELOW_INSTANCES_SLOTS));
    vec![
        one("k", Content::Comp),
        one("frame", group("G", vec![one("a", int()), one("b", int())])),
        opt("qopt", group("Q", children(&BELOW_OPTIONAL_SLOTS))),
        one(
            "lines",
            group(
                "Linequeue",
                vec![many("line", Order::List, group("L", instance))],
            ),
        ),
    ]
}

static CONFIGURATION: LazyLock<Vec<Decl>> = LazyLock::new(configuration);

/// Why no K7 plan runs a path sweep case.
const UNRUN: &str = "the path sweep's cases witness the compiler's verdict on each sweep cell \
                     below a marked ancestor; the path base has no driver commands to set its \
                     cells up";

/// The cells below the optional group `qopt`, which a matched result's subject matches whole.
pub(in super::super) static BELOW_OPTIONAL: Layout = Layout {
    configuration: &CONFIGURATION,
    slots: &BELOW_OPTIONAL_SLOTS,
    family: Family::SweepPaths,
    base: Base::SweepPaths,
    ancestor: Some(("qopt", ["Some(old)", "Some(old)"])),
    unrun: UNRUN,
};

/// The cells in the List collection `line`'s instance, which a matched result's subject matches
/// by its front instance.
pub(in super::super) static BELOW_INSTANCES: Layout = Layout {
    configuration: &CONFIGURATION,
    slots: &BELOW_INSTANCES_SLOTS,
    family: Family::SweepPaths,
    base: Base::SweepPaths,
    ancestor: Some((
        "line",
        [
            "[L { lid: old, .. }, ..]",
            "[k::fragment![crate::L { lid: old, .. }], ..]",
        ],
    )),
    unrun: UNRUN,
};

/// Every rule-form cell of the sweep's main tables below a marked ancestor, in the sweep's
/// order: each table's rows by side, path (`?`, then `*`) and stack, then by column.
#[must_use]
pub fn cells() -> Vec<Cell> {
    let mut out = Vec::new();
    let sides: [(&str, Side, bool, bool); 4] = [
        ("subject", Side::Subject, false, false),
        ("subject, written", Side::Subject, true, false),
        ("result, matched", Side::Result, false, true),
        ("result, unmatched", Side::Result, false, false),
    ];
    for (table, form, spellings) in main_tables() {
        if form == Form::Init {
            continue;
        }
        for (side_name, side, written, matched) in sides {
            for path in ["?", "*"] {
                for (stack, layers) in stacks() {
                    for text in spellings {
                        out.push(Cell {
                            key: (
                                table.clone(),
                                side_name.to_owned(),
                                stack.to_owned(),
                                (*text).to_owned(),
                            ),
                            form,
                            side,
                            written,
                            stack,
                            path,
                            text,
                            other: matched.then(|| subject(form, &layers)),
                            bound: if side == Side::Result {
                                RESULT_BOUND
                            } else {
                                &[]
                            },
                            row: None,
                        });
                    }
                }
            }
        }
    }
    out
}

/// Every path cell with its case or its reason, in the sweep's order.
static BUILT: LazyLock<Vec<(Cell, Built)>> = LazyLock::new(|| {
    cells()
        .into_iter()
        .map(|cell| {
            let built = build(&cell);
            (cell, built)
        })
        .collect()
});

static GENERATED: LazyLock<BTreeMap<String, EntryCase>> = LazyLock::new(|| {
    BUILT
        .iter()
        .filter_map(|(_, built)| match built {
            Built::Case(generated) => Some((generated.case.id.clone(), generated.entry.clone())),
            Built::Unbuilt(_) => None,
        })
        .collect()
});

/// The path sweep's cases.
pub(in super::super) fn cases(cases: &mut Vec<Case>) {
    for (_, built) in BUILT.iter() {
        if let Built::Case(generated) = built {
            cases.push(generated.case.clone());
        }
    }
}

/// The reading of a path sweep case.
///
/// # Panics
///
/// Panics if `case` is no case of the path sweep.
#[must_use]
pub fn entry_case(case: &Case) -> EntryCase {
    GENERATED
        .get(&case.id)
        .unwrap_or_else(|| panic!("{} is no path sweep case", case.id))
        .clone()
}

/// The path cells no case can be compiled for, by path and key, with the reason.
#[must_use]
pub fn unbuilt() -> BTreeMap<(&'static str, Key), &'static str> {
    BUILT
        .iter()
        .filter_map(|(cell, built)| match built {
            Built::Unbuilt(reason) => Some(((cell.path, cell.key.clone()), *reason)),
            Built::Case(_) => None,
        })
        .collect()
}

static AFTER_COMMANDS: LazyLock<String> = LazyLock::new(|| BELOW_OPTIONAL.after_commands());

static INITIALIZER: LazyLock<String> = LazyLock::new(|| BELOW_OPTIONAL.initializer());

pub(in super::super) fn base() -> BaseText {
    BaseText {
        before_commands: kinds::BEFORE_COMMANDS,
        after_commands: AFTER_COMMANDS.as_str(),
        initializer: INITIALIZER.as_str(),
        after_initializer: "",
    }
}

/// Whether the path base declares `cell` as a cell of its own.
#[must_use]
pub fn declares(cell: &str) -> bool {
    BELOW_OPTIONAL.declares(cell)
}

/// The path base's cell `cell`'s own layers.
///
/// # Panics
///
/// Panics if the base declares no cell `cell`.
#[must_use]
pub fn stack(cell: &str) -> Vec<Layer> {
    kinds::own(BELOW_OPTIONAL.find(cell).0)
}

/// The path base's groups, at any depth.
#[must_use]
pub fn groups() -> Vec<Group> {
    BELOW_OPTIONAL.groups()
}

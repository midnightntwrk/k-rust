//! The sweep of the cells oracle's `outcome` (S5.0g): the stacks, the sides' other entries and
//! the spellings `tests/cells_oracle.rs` prints as `cells-outcome-sweep.tsv`, and the compiled
//! sweep (S5.0g part (b), item 3a): one generated case of [`Family::Sweep`] for each sweep cell
//! named at its record's level (path `-`), rendered on [`Base::Sweep`], whose `krs-class` shard
//! `sweep` makes the compiler a witness of `outcome` on every such cell.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::sync::LazyLock;

use super::cells_oracle::build::{bind, named, open, seq, splice};
use super::cells_oracle::{
    Context, Entries, Entry, EntryCase, Form, Group, Layer, Notation, Order, Outcome, Record,
    RecordRest, Rest, RestAt, Sentence as TemplateSentence, Seq, Spelling, Template,
    collect_groups, outcome,
};
use super::kinds::{self, Content, Decl, Generated, group as decl_group, leaf, many, one, opt};
use super::{
    Base, BaseText, Case, CaseSpec, Command, Family, ItemBuilder, OwnReason, Packaging, Side,
};

/// The name of a declared stack as the sweep and check 5 name it.
#[must_use]
pub fn stack_name(cell: &str, stack: &[Layer]) -> String {
    let leaf = |notation: &Notation| match notation {
        Notation::Plain => "leaf Int",
        Notation::List => "leaf List",
        Notation::Cons => "leaf Cons",
        Notation::Map => "leaf Map",
        Notation::Set => "leaf Set",
    };
    match stack {
        [Layer::Computation] if cell.ends_with("code") => "second computation".to_owned(),
        [Layer::Computation] => "computation".to_owned(),
        [Layer::Leaf(notation)] => leaf(notation).to_owned(),
        [Layer::Group(_)] => "group".to_owned(),
        [Layer::Optional, Layer::Leaf(notation)] => format!("? {}", leaf(notation)),
        [Layer::Optional, Layer::Group(_)] => "? group".to_owned(),
        [Layer::Instances(order), ..] => format!(
            "* {}",
            match order {
                Order::List => "List",
                Order::Set => "Set",
                Order::Map => "Map",
            }
        ),
        other => format!("{other:?}"),
    }
}

/// The form's name, the first segment of its IDs.
#[must_use]
pub const fn form_name(form: Form) -> &'static str {
    match form {
        Form::Readable => "readable",
        Form::Claim => "claim",
        Form::Cells => "cells",
        Form::Init => "init",
    }
}

/// The sweep's group `G`, two `Int` children (so a record naming one is not complete).
#[must_use]
pub fn group_g() -> Layer {
    Layer::Group(Group {
        name: "G".to_owned(),
        children: vec![
            ("a".to_owned(), vec![Layer::Leaf(Notation::Plain)]),
            ("b".to_owned(), vec![Layer::Leaf(Notation::Plain)]),
        ],
    })
}

/// The sweep's own stacks: every kind the domain has (check 5's, but the second computation,
/// which differs from the first by its name only, P1), with `G` as the group and the
/// collections' instance group.
#[must_use]
pub fn stacks() -> Vec<(&'static str, Vec<Layer>)> {
    let leaf = |notation| vec![Layer::Leaf(notation)];
    let optional = |mut stack: Vec<Layer>| {
        stack.insert(0, Layer::Optional);
        stack
    };
    let many = |order| vec![Layer::Instances(order), group_g()];
    vec![
        ("computation", vec![Layer::Computation]),
        ("leaf Int", leaf(Notation::Plain)),
        ("leaf List", leaf(Notation::List)),
        ("leaf Cons", leaf(Notation::Cons)),
        ("leaf Map", leaf(Notation::Map)),
        ("leaf Set", leaf(Notation::Set)),
        ("group G", vec![group_g()]),
        ("? leaf Int", optional(leaf(Notation::Plain))),
        ("? leaf List", optional(leaf(Notation::List))),
        ("? leaf Map", optional(leaf(Notation::Map))),
        ("? group G", optional(vec![group_g()])),
        ("* List of G", many(Order::List)),
        ("* Set of G", many(Order::Set)),
        ("* Map of G", many(Order::Map)),
    ]
}

/// The entry a matched result's subject writes in its cell: the cell's content with an
/// anonymous rest at its content root where it has one, else a binder.
///
/// # Panics
///
/// Panics if the sweep has no subject entry for `stack`.
#[must_use]
pub fn subject(form: Form, stack: &[Layer]) -> String {
    let cells = form == Form::Cells;
    let inner = |text: &str| {
        if cells {
            format!("k::configuration::Cell({text})")
        } else {
            text.to_owned()
        }
    };
    match stack {
        [Layer::Optional, rest @ ..] => format!("Some({})", subject(form, rest)),
        [Layer::Computation] if cells => "k::configuration::KCell(y, ..)".to_owned(),
        [Layer::Computation] => "[y, ..]".to_owned(),
        [Layer::Leaf(Notation::List | Notation::Cons)] => inner("[y, ..]"),
        [Layer::Leaf(Notation::Map)] if cells => inner("k::map![z -> y, ..]"),
        [Layer::Leaf(Notation::Map)] => "{ z -> y, .. }".to_owned(),
        [Layer::Leaf(_)] => inner("old"),
        [Layer::Group(_)] if cells => "k::fragment![crate::G { a: y, .. }]".to_owned(),
        [Layer::Group(_)] => "G { a: y, .. }".to_owned(),
        [Layer::Instances(Order::List), ..] if cells => {
            "[k::fragment![crate::G { a: y, .. }], ..]".to_owned()
        }
        [Layer::Instances(_), ..] if cells => {
            "{ k::fragment![crate::G { a: y, .. }], .. }".to_owned()
        }
        [Layer::Instances(Order::List), ..] => "[G { a: y, .. }, ..]".to_owned(),
        [Layer::Instances(_), ..] => "{ G { a: y, .. }, .. }".to_owned(),
        other => panic!("no sweep subject for {other:?}"),
    }
}

/// The spellings the sweep writes in each form, one per column: each mark of the form, and the
/// rests and records that pairing and L4 read.
#[must_use]
pub const fn spellings(form: Form) -> &'static [&'static str] {
    match form {
        Form::Readable | Form::Claim => &[
            "Some(x)",
            "None",
            "[x, ..]",
            "[x]",
            "[..]",
            "[.., x]",
            "[x, r @ ..]",
            "{ G { a: x, .. }, .. }",
            "{ y -> x, .. }",
            "x",
            "_",
            "0",
            "G { a: x, .. }",
            "G { a: x, b: y, .. }",
            "G { a: x }",
        ],
        Form::Cells => &[
            "Some(k::configuration::Cell(x))",
            "None",
            "k::configuration::Cell(x)",
            "k::configuration::Cell([x, ..])",
            "k::configuration::Cell(k::map![y -> x, ..])",
            "k::configuration::KCell(x, ..)",
            "k::configuration::KCell(x)",
            "[k::fragment![crate::G { a: x, .. }], ..]",
            "{ k::fragment![crate::G { a: x, .. }], .. }",
            "x",
            "_",
            "k::fragment![crate::G { a: x, .. }]",
            "k::fragment![crate::G { a: x, b: y, .. }]",
            "k::fragment![crate::G { a: x }]",
        ],
        Form::Init => &[
            "Some(0)",
            "k::absent!(0)",
            "None",
            "k::k![pgm]",
            "k::k![Cmd::Go(), ..]",
            "[0]",
            "[0, ..]",
            "k::map![0 -> 1]",
            "0",
            "G { a: 0, b: 0 }",
            "G { a: 0 }",
            "Cmd::Go()",
            "pgm",
        ],
    }
}

/// The sweep's second table of each form: single-entry spellings the first does not print (the
/// S5.0g pattern review's gaps G7, G8 and G9), each a column of its own table so that the first
/// table's patterns stand as reviewed.
#[must_use]
pub const fn more_spellings(form: Form) -> &'static [&'static str] {
    match form {
        // G8: a bracketed instance record (P-R4), a value item in unordered braces (Q2), the
        // readable map literal (`READABLE_ONLY`), `_` inside `Some` (a result's placement),
        // `Some` of an open record and of a sequence, an exact instance set (Q1's exact
        // overwrite of a collection), and an instance record that does not name a Map
        // collection's key.
        Form::Readable | Form::Claim => &[
            "[G { a: x, .. }, ..]",
            "{ x, .. }",
            "map![y -> x, ..]",
            "Some(_)",
            "Some(G { .. })",
            "Some([..])",
            "{ G { a: x, b: y } }",
            "{ G { b: x, .. }, .. }",
        ],
        // G9: back items (E1, the List back instance, P-R1) and `Cell(_)` (Q1's lint).
        Form::Cells => &[
            "k::configuration::Cell([.., x])",
            "k::configuration::KCell(.., x)",
            "k::configuration::Cell(_)",
        ],
        // G7: a record update, E3's splice of the program, D2 #8's map base.
        Form::Init => &[
            "G { a: 0, ..base }",
            "k::k![Cmd::Go(), ..pgm]",
            "k::map![0 -> 1, ..env]",
        ],
    }
}

/// The sweep's third table of each form that has one: the computation's back items in `cells!`
/// (E1 holds in every form, the S5.0g fixes review's F-6), a table of its own so that the
/// second table's patterns stand as reviewed.
#[must_use]
pub const fn back_spellings(form: Form) -> &'static [&'static str] {
    match form {
        Form::Cells => &["k::configuration::KCell(x, .., y)"],
        Form::Readable | Form::Claim | Form::Init => &[],
    }
}

/// The sweep's main tables: each form's, then its second table ([`more_spellings`]), then
/// its third where it has one ([`back_spellings`]).
#[must_use]
pub fn main_tables() -> Vec<(String, Form, &'static [&'static str])> {
    let forms = [Form::Readable, Form::Claim, Form::Cells, Form::Init];
    let first = forms
        .iter()
        .map(|form| (form_name(*form).to_owned(), *form, spellings(*form)));
    let second = forms.iter().map(|form| {
        (
            format!("{} more", form_name(*form)),
            *form,
            more_spellings(*form),
        )
    });
    let third = forms
        .iter()
        .filter(|form| !back_spellings(**form).is_empty())
        .map(|form| {
            (
                format!("{} back", form_name(*form)),
                *form,
                back_spellings(*form),
            )
        });
    first.chain(second).chain(third).collect()
}

/// A group of the children sweep: its name and its children's own layers, in declaration
/// order (a Map collection's key is its first child).
#[must_use]
pub fn group_of(name: &str, children: &[(&str, Layer)]) -> Layer {
    Layer::Group(Group {
        name: name.to_owned(),
        children: children
            .iter()
            .map(|(child, layer)| ((*child).to_owned(), vec![layer.clone()]))
            .collect(),
    })
}

/// The children sweep's stacks, by name.
///
/// # Panics
///
/// Panics if the children sweep names no stack `name`.
#[must_use]
pub fn children_stack(name: &str) -> Vec<Layer> {
    let list = Layer::Leaf(Notation::List);
    let int = Layer::Leaf(Notation::Plain);
    let h = || group_of("H", &[("l", list.clone()), ("b", int.clone())]);
    match name {
        "group H" => vec![h()],
        "? group H" => vec![Layer::Optional, h()],
        "* List of T" => vec![
            Layer::Instances(Order::List),
            group_of("T", &[("k", Layer::Computation), ("n", int.clone())]),
        ],
        "* Map of A" => vec![
            Layer::Instances(Order::Map),
            group_of("A", &[("id", int.clone()), ("l", list.clone())]),
        ],
        "group C" => vec![group_of(
            "C",
            &[("c", Layer::Computation), ("n", int.clone())],
        )],
        "group O" => vec![Layer::Group(Group {
            name: "O".to_owned(),
            children: vec![
                ("o".to_owned(), vec![Layer::Optional, int.clone()]),
                ("n".to_owned(), vec![int.clone()]),
            ],
        })],
        "group W" => vec![group_of("W", &[("g", group_g()), ("n", int.clone())])],
        "group M" => vec![group_of(
            "M",
            &[("m", Layer::Leaf(Notation::Map)), ("n", int.clone())],
        )],
        "? group G" => vec![Layer::Optional, group_g()],
        "? leaf List" => vec![Layer::Optional, list.clone()],
        other => panic!("no children-sweep stack {other}"),
    }
}

/// The children sweep's rows: a stack, the subject's entry of the cell (`-`: the subject does
/// not match it), and a result, each written in readable (claim alike) and in `cells!`.
pub const CHILDREN: [(&str, [&str; 2], [&str; 2]); 39] = [
    (
        "group H",
        [
            "H { l: [y, ..], .. }",
            "k::fragment![crate::H { l: [y, ..], .. }]",
        ],
        [
            "H { l: [x], b: 0 }",
            "k::fragment![crate::H { l: [x], b: 0 }]",
        ],
    ),
    (
        "group H",
        [
            "H { l: [y, ..], .. }",
            "k::fragment![crate::H { l: [y, ..], .. }]",
        ],
        [
            "H { l: [x, ..], b: 0 }",
            "k::fragment![crate::H { l: [x, ..], b: 0 }]",
        ],
    ),
    (
        "group H",
        ["H { b: y, .. }", "k::fragment![crate::H { b: y, .. }]"],
        [
            "H { l: [x, ..], b: 0 }",
            "k::fragment![crate::H { l: [x, ..], b: 0 }]",
        ],
    ),
    (
        "group H",
        ["H { b: y, .. }", "k::fragment![crate::H { b: y, .. }]"],
        [
            "H { l: [x], b: 0 }",
            "k::fragment![crate::H { l: [x], b: 0 }]",
        ],
    ),
    (
        "group H",
        ["-", "-"],
        [
            "H { l: [x, ..], b: 0 }",
            "k::fragment![crate::H { l: [x, ..], b: 0 }]",
        ],
    ),
    (
        "group H",
        ["-", "-"],
        [
            "H { l: [x], b: 0 }",
            "k::fragment![crate::H { l: [x], b: 0 }]",
        ],
    ),
    (
        "? group H",
        [
            "Some(H { l: [y, ..], .. })",
            "Some(k::fragment![crate::H { l: [y, ..], .. }])",
        ],
        [
            "Some(H { l: [x], b: 0 })",
            "Some(k::fragment![crate::H { l: [x], b: 0 }])",
        ],
    ),
    (
        "? group H",
        ["None", "None"],
        [
            "Some(H { l: [x, ..], b: 0 })",
            "Some(k::fragment![crate::H { l: [x, ..], b: 0 }])",
        ],
    ),
    (
        "? group H",
        ["None", "None"],
        [
            "Some(H { l: [x], b: 0 })",
            "Some(k::fragment![crate::H { l: [x], b: 0 }])",
        ],
    ),
    (
        "* List of T",
        [
            "[me @ T { k: [y, ..], .. }, ..]",
            "[me @ k::fragment![crate::T { k: [y, ..], .. }], ..]",
        ],
        [
            "[T { k: [x], ..me }, ..]",
            "[k::fragment![crate::T { k: [x], ..me }], ..]",
        ],
    ),
    (
        "* List of T",
        [
            "[me @ T { k: [y, ..], .. }, ..]",
            "[me @ k::fragment![crate::T { k: [y, ..], .. }], ..]",
        ],
        [
            "[T { k: [x, ..], ..me }, ..]",
            "[k::fragment![crate::T { k: [x, ..], ..me }], ..]",
        ],
    ),
    (
        "* List of T",
        [
            "[me @ T { n: y, .. }, ..]",
            "[me @ k::fragment![crate::T { n: y, .. }], ..]",
        ],
        [
            "[T { n: 0, ..me }, ..]",
            "[k::fragment![crate::T { n: 0, ..me }], ..]",
        ],
    ),
    (
        "* List of T",
        ["[..]", "[..]"],
        [
            "[T { k: [x], n: 0 }, ..]",
            "[k::fragment![crate::T { k: [x], n: 0 }], ..]",
        ],
    ),
    (
        "* List of T",
        ["[..]", "[..]"],
        [
            "[T { k: [x, ..], n: 0 }, ..]",
            "[k::fragment![crate::T { k: [x, ..], n: 0 }], ..]",
        ],
    ),
    (
        "* Map of A",
        [
            "{ me @ A { id: z, .. }, .. }",
            "{ me @ k::fragment![crate::A { id: z, .. }], .. }",
        ],
        [
            "{ A { id: 5, ..me }, .. }",
            "{ k::fragment![crate::A { id: 5, ..me }], .. }",
        ],
    ),
    (
        "* Map of A",
        [
            "{ me @ A { id: z, .. }, .. }",
            "{ me @ k::fragment![crate::A { id: z, .. }], .. }",
        ],
        [
            "{ A { id: z, ..me }, .. }",
            "{ k::fragment![crate::A { id: z, ..me }], .. }",
        ],
    ),
    (
        "* Map of A",
        [
            "{ me @ A { l: [y, ..], .. }, .. }",
            "{ me @ k::fragment![crate::A { l: [y, ..], .. }], .. }",
        ],
        [
            "{ A { id: 5, ..me }, .. }",
            "{ k::fragment![crate::A { id: 5, ..me }], .. }",
        ],
    ),
    (
        "* Map of A",
        [
            "{ me @ A { id: z, .. }, .. }",
            "{ me @ k::fragment![crate::A { id: z, .. }], .. }",
        ],
        [
            "{ A { l: [x], ..me }, .. }",
            "{ k::fragment![crate::A { l: [x], ..me }], .. }",
        ],
    ),
    (
        "* Map of A",
        [
            "{ me @ A { id: z, l: [y, ..] }, .. }",
            "{ me @ k::fragment![crate::A { id: z, l: [y, ..] }], .. }",
        ],
        [
            "{ A { l: [x], ..me }, .. }",
            "{ k::fragment![crate::A { l: [x], ..me }], .. }",
        ],
    ),
    (
        "* Map of A",
        [
            "{ me @ A { id: z, l: [y, ..] }, .. }",
            "{ me @ k::fragment![crate::A { id: z, l: [y, ..] }], .. }",
        ],
        [
            "{ A { l: [x, ..], ..me }, .. }",
            "{ k::fragment![crate::A { l: [x, ..], ..me }], .. }",
        ],
    ),
    (
        "* Map of A",
        ["{ .. }", "{ .. }"],
        [
            "{ A { id: 5, l: [x] }, .. }",
            "{ k::fragment![crate::A { id: 5, l: [x] }], .. }",
        ],
    ),
    (
        "* Map of A",
        [
            "{ me @ A { id: z, .. }, .. }",
            "{ me @ k::fragment![crate::A { id: z, .. }], .. }",
        ],
        [
            "{ A { id: y, ..me }, .. }",
            "{ k::fragment![crate::A { id: y, ..me }], .. }",
        ],
    ),
    (
        "* Map of A",
        ["{ .. }", "{ .. }"],
        [
            "{ A { l: [x], .. }, .. }",
            "{ k::fragment![crate::A { l: [x], .. }], .. }",
        ],
    ),
    (
        "* Map of A",
        ["{ .. }", "{ .. }"],
        [
            "{ A { id: 5, .. }, .. }",
            "{ k::fragment![crate::A { id: 5, .. }], .. }",
        ],
    ),
    (
        "* List of T",
        ["[..]", "[..]"],
        [
            "[T { n: 0, .. }, ..]",
            "[k::fragment![crate::T { n: 0, .. }], ..]",
        ],
    ),
    // R1 (S5.0g review): an overwritten group's children are unmatched, not created (Q1): its
    // computation child (Q3), its `?` child (P5) and its group child (P6) each pair as an
    // overwrite.
    (
        "group C",
        ["-", "-"],
        [
            "C { c: [x], n: 0 }",
            "k::fragment![crate::C { c: [x], n: 0 }]",
        ],
    ),
    (
        "group O",
        ["-", "-"],
        [
            "O { o: Some(1), n: 0 }",
            "k::fragment![crate::O { o: Some(1), n: 0 }]",
        ],
    ),
    (
        "group O",
        ["-", "-"],
        [
            "O { o: None, n: 0 }",
            "k::fragment![crate::O { o: None, n: 0 }]",
        ],
    ),
    (
        "group W",
        ["-", "-"],
        [
            "W { g: G { a: x, .. }, n: 0 }",
            "k::fragment![crate::W { g: G { a: x, .. }, n: 0 }]",
        ],
    ),
    (
        "group W",
        ["-", "-"],
        [
            "W { g: G { a: x, b: y }, n: 0 }",
            "k::fragment![crate::W { g: G { a: x, b: y }, n: 0 }]",
        ],
    ),
    // A bare `..` that names every child leaves no field open: the exact record (P6, P0).
    (
        "group W",
        ["-", "-"],
        [
            "W { g: G { a: x, b: y, .. }, n: 0 }",
            "k::fragment![crate::W { g: G { a: x, b: y, .. }, n: 0 }]",
        ],
    ),
    // P-R3 (S5.0g pattern review): an update whose label no subject instance has, of a value
    // the sentence matches elsewhere (`me` is bound), creates an instance.
    (
        "* List of T",
        ["[..]", "[..]"],
        [
            "[T { k: [x, ..], ..me }, ..]",
            "[k::fragment![crate::T { k: [x, ..], ..me }], ..]",
        ],
    ),
    (
        "* List of T",
        ["[..]", "[..]"],
        [
            "[T { k: [x], ..me }, ..]",
            "[k::fragment![crate::T { k: [x], ..me }], ..]",
        ],
    ),
    (
        "* Map of A",
        ["{ .. }", "{ .. }"],
        [
            "{ A { l: [x, ..], ..me }, .. }",
            "{ k::fragment![crate::A { l: [x, ..], ..me }], .. }",
        ],
    ),
    // R9 (P0): an update writing the key as the same literal its subject matched keeps it.
    (
        "* Map of A",
        [
            "{ me @ A { id: 5, .. }, .. }",
            "{ me @ k::fragment![crate::A { id: 5, .. }], .. }",
        ],
        [
            "{ A { id: 5, ..me }, .. }",
            "{ k::fragment![crate::A { id: 5, ..me }], .. }",
        ],
    ),
    (
        "* Map of A",
        [
            "{ me @ A { id: 5, .. }, .. }",
            "{ me @ k::fragment![crate::A { id: 5, .. }], .. }",
        ],
        [
            "{ A { id: 6, ..me }, .. }",
            "{ k::fragment![crate::A { id: 6, ..me }], .. }",
        ],
    ),
    // G2 (S5.0g pattern review): a `?` cell whose subject is `None`, which the result creates at
    // the entry's root (P5, P6).
    (
        "? group G",
        ["None", "None"],
        [
            "Some(G { a: x, .. })",
            "Some(k::fragment![crate::G { a: x, .. }])",
        ],
    ),
    (
        "? leaf List",
        ["None", "None"],
        ["Some([x, ..])", "Some(k::configuration::Cell([x, ..]))"],
    ),
    (
        "? group G",
        ["None", "None"],
        ["Some(G { a: x })", "Some(k::fragment![crate::G { a: x }])"],
    ),
];

/// The children sweep's updates whose label the sentence matches nowhere (S5.0g pattern review
/// P-R3): the subject shows no instance labelled `me`, and nothing else binds it.
pub const CHILDREN_UNBASED: [(&str, [&str; 2], [&str; 2]); 3] = [
    (
        "* List of T",
        ["[..]", "[..]"],
        [
            "[T { k: [x], ..me }, ..]",
            "[k::fragment![crate::T { k: [x], ..me }], ..]",
        ],
    ),
    (
        "* List of T",
        ["[..]", "[..]"],
        [
            "[T { k: [x, ..], ..me }, ..]",
            "[k::fragment![crate::T { k: [x, ..], ..me }], ..]",
        ],
    ),
    (
        "* Map of A",
        ["{ .. }", "{ .. }"],
        [
            "{ A { l: [x, ..], ..me }, .. }",
            "{ k::fragment![crate::A { l: [x, ..], ..me }], .. }",
        ],
    ),
];

/// The fragment-child sweep's rows (the S5.0g fixes review's F-1, ruled): a group record whose
/// child holds a Map, a List or a computation, in a subject and in a result, the child framed or
/// exact, and in a result over a subject child framed, exact or not named. Each is a side, a
/// stack, the subject's entry of the cell (`-`: none; a subject's own row has none) and the
/// entry, each written in readable (claim alike) and in `cells!`, whose fragment writes the
/// child's content bare (P1: the field's value is the child's entry, its content root, P6).
pub const FRAGMENT_CHILD: [(&str, &str, [&str; 2], [&str; 2]); 21] = [
    (
        "subject",
        "group M",
        ["-", "-"],
        [
            "M { m: { y -> x, .. }, .. }",
            "k::fragment![crate::M { m: k::map![y -> x, ..], .. }]",
        ],
    ),
    (
        "subject",
        "group M",
        ["-", "-"],
        [
            "M { m: { y -> x }, .. }",
            "k::fragment![crate::M { m: k::map![y -> x], .. }]",
        ],
    ),
    (
        "result",
        "group M",
        [
            "M { m: { z -> y, .. }, .. }",
            "k::fragment![crate::M { m: k::map![z -> y, ..], .. }]",
        ],
        [
            "M { m: { y -> x, .. }, n: 0 }",
            "k::fragment![crate::M { m: k::map![y -> x, ..], n: 0 }]",
        ],
    ),
    (
        "result",
        "group M",
        [
            "M { m: { z -> y }, .. }",
            "k::fragment![crate::M { m: k::map![z -> y], .. }]",
        ],
        [
            "M { m: { y -> x, .. }, n: 0 }",
            "k::fragment![crate::M { m: k::map![y -> x, ..], n: 0 }]",
        ],
    ),
    (
        "result",
        "group M",
        [
            "M { m: { z -> y, .. }, .. }",
            "k::fragment![crate::M { m: k::map![z -> y, ..], .. }]",
        ],
        [
            "M { m: { y -> x }, n: 0 }",
            "k::fragment![crate::M { m: k::map![y -> x], n: 0 }]",
        ],
    ),
    (
        "result",
        "group M",
        [
            "M { m: { z -> y }, .. }",
            "k::fragment![crate::M { m: k::map![z -> y], .. }]",
        ],
        [
            "M { m: { y -> x }, n: 0 }",
            "k::fragment![crate::M { m: k::map![y -> x], n: 0 }]",
        ],
    ),
    (
        "result",
        "group M",
        ["M { n: z, .. }", "k::fragment![crate::M { n: z, .. }]"],
        [
            "M { m: { y -> x, .. }, n: 0 }",
            "k::fragment![crate::M { m: k::map![y -> x, ..], n: 0 }]",
        ],
    ),
    (
        "subject",
        "group H",
        ["-", "-"],
        [
            "H { l: [y, ..], .. }",
            "k::fragment![crate::H { l: [y, ..], .. }]",
        ],
    ),
    (
        "subject",
        "group H",
        ["-", "-"],
        ["H { l: [y], .. }", "k::fragment![crate::H { l: [y], .. }]"],
    ),
    (
        "result",
        "group H",
        [
            "H { l: [z, ..], .. }",
            "k::fragment![crate::H { l: [z, ..], .. }]",
        ],
        [
            "H { l: [x, ..], b: 0 }",
            "k::fragment![crate::H { l: [x, ..], b: 0 }]",
        ],
    ),
    (
        "result",
        "group H",
        ["H { l: [z], .. }", "k::fragment![crate::H { l: [z], .. }]"],
        [
            "H { l: [x, ..], b: 0 }",
            "k::fragment![crate::H { l: [x, ..], b: 0 }]",
        ],
    ),
    (
        "result",
        "group H",
        [
            "H { l: [z, ..], .. }",
            "k::fragment![crate::H { l: [z, ..], .. }]",
        ],
        [
            "H { l: [x], b: 0 }",
            "k::fragment![crate::H { l: [x], b: 0 }]",
        ],
    ),
    (
        "result",
        "group H",
        ["H { l: [z], .. }", "k::fragment![crate::H { l: [z], .. }]"],
        [
            "H { l: [x], b: 0 }",
            "k::fragment![crate::H { l: [x], b: 0 }]",
        ],
    ),
    (
        "result",
        "group H",
        ["H { b: z, .. }", "k::fragment![crate::H { b: z, .. }]"],
        [
            "H { l: [x, ..], b: 0 }",
            "k::fragment![crate::H { l: [x, ..], b: 0 }]",
        ],
    ),
    (
        "subject",
        "group C",
        ["-", "-"],
        [
            "C { c: [y, ..], .. }",
            "k::fragment![crate::C { c: [y, ..], .. }]",
        ],
    ),
    (
        "subject",
        "group C",
        ["-", "-"],
        ["C { c: [y], .. }", "k::fragment![crate::C { c: [y], .. }]"],
    ),
    (
        "result",
        "group C",
        [
            "C { c: [z, ..], .. }",
            "k::fragment![crate::C { c: [z, ..], .. }]",
        ],
        [
            "C { c: [x, ..], n: 0 }",
            "k::fragment![crate::C { c: [x, ..], n: 0 }]",
        ],
    ),
    (
        "result",
        "group C",
        ["C { c: [z], .. }", "k::fragment![crate::C { c: [z], .. }]"],
        [
            "C { c: [x, ..], n: 0 }",
            "k::fragment![crate::C { c: [x, ..], n: 0 }]",
        ],
    ),
    (
        "result",
        "group C",
        [
            "C { c: [z, ..], .. }",
            "k::fragment![crate::C { c: [z, ..], .. }]",
        ],
        [
            "C { c: [x], n: 0 }",
            "k::fragment![crate::C { c: [x], n: 0 }]",
        ],
    ),
    (
        "result",
        "group C",
        ["C { c: [z], .. }", "k::fragment![crate::C { c: [z], .. }]"],
        [
            "C { c: [x], n: 0 }",
            "k::fragment![crate::C { c: [x], n: 0 }]",
        ],
    ),
    (
        "result",
        "group C",
        ["C { n: z, .. }", "k::fragment![crate::C { n: z, .. }]"],
        [
            "C { c: [x, ..], n: 0 }",
            "k::fragment![crate::C { c: [x, ..], n: 0 }]",
        ],
    ),
];

/// D-5's stacks: a Map collection of `Q { id: Int, js: * List of J { p: Int } }`, and a plain
/// group `P { js: * List of J }`, each with a collection child.
///
/// # Panics
///
/// Panics if the initializer children sweep names no stack `name`.
#[must_use]
pub fn nested_collection_stack(name: &str) -> Vec<Layer> {
    let int = Layer::Leaf(Notation::Plain);
    let js = vec![
        Layer::Instances(Order::List),
        group_of("J", &[("p", int.clone())]),
    ];
    let group = |head: &str, mut children: Vec<(String, Vec<Layer>)>| {
        children.push(("js".to_owned(), js.clone()));
        Layer::Group(Group {
            name: head.to_owned(),
            children,
        })
    };
    match name {
        "* Map of Q" => vec![
            Layer::Instances(Order::Map),
            group("Q", vec![("id".to_owned(), vec![int.clone()])]),
        ],
        "group P" => vec![group("P", Vec::new())],
        // G7: a template with a `?` child, and a Map collection's template.
        "group O" => vec![Layer::Group(Group {
            name: "O".to_owned(),
            children: vec![
                ("o".to_owned(), vec![Layer::Optional, int.clone()]),
                ("n".to_owned(), vec![int]),
            ],
        })],
        "* Map of A" => vec![
            Layer::Instances(Order::Map),
            group_of("A", &[("id", int), ("l", Layer::Leaf(Notation::List))]),
        ],
        other => panic!("no nested-collection stack {other}"),
    }
}

/// The initializer rows of the children sweep (D-5, P5): a template record whose child is a
/// collection, valued by that collection's own instance template, or otherwise.
pub const INITIALIZER_CHILDREN: [(&str, &str); 11] = [
    ("* Map of Q", "Q { id: 0, js: J { p: 0 } }"),
    ("* Map of Q", "Q { id: 0, js: [J { p: 0 }] }"),
    ("* Map of Q", "Q { id: 0, js: 0 }"),
    ("group P", "P { js: J { p: 0 } }"),
    ("group P", "P { js: Some(J { p: 0 }) }"),
    ("group P", "P { js: 0 }"),
    // G7 (S5.0g pattern review): `k::absent!` in a template's `?` child, and a Map collection's
    // template, which names its key or omits it.
    ("group O", "O { o: k::absent!(0), n: 0 }"),
    ("group O", "O { o: Some(0), n: 0 }"),
    ("group O", "O { o: 0, n: 0 }"),
    ("* Map of A", "A { id: 0, l: [0] }"),
    ("* Map of A", "A { l: [0] }"),
];

// The compiled sweep (S5.0g part (b), item 3a).

/// A cell of the sweep named at its record's level, keyed as the witness test keys it:
/// `(table, side, stack, column)`. A main table's side is its row's; a children row's is its form
/// and side, with the subject's entry it stands over (`readable result over [..]`); an
/// initializer's is `init`.
pub type Key = (String, String, String, String);

/// One root cell of the sweep: its key, and the entry its probe judges.
#[derive(Clone, Debug)]
pub struct Cell {
    /// The witness key.
    pub key: Key,
    /// The form the entry is written in.
    pub form: Form,
    /// The entry's side.
    pub side: Side,
    /// For a subject, whether the result writes the cell.
    pub written: bool,
    /// The stack's name, as [`stacks`], [`children_stack`] or [`nested_collection_stack`] name it.
    pub stack: &'static str,
    /// The entry, as the sweep writes it.
    pub text: &'static str,
    /// For a result, the subject's entry of the cell, as the sweep writes it.
    pub other: Option<String>,
    /// The names the sentence binds outside the entry.
    pub bound: &'static [&'static str],
    /// The children tables' row tag, `None` in a main table: it tells rows of one stack and entry
    /// apart in the case's ID.
    pub row: Option<String>,
}

const RESULT_BOUND: &[&str] = &["x", "y", "z", "old"];
const CHILDREN_BOUND: &[&str] = &["x", "y", "z", "me"];
const UNBASED_BOUND: &[&str] = &["x", "y", "z"];

/// The layers of a stack the sweep names.
///
/// # Panics
///
/// Panics if the sweep names no such stack.
#[must_use]
pub fn named_stack(name: &str) -> Vec<Layer> {
    if let Some((_, stack)) = stacks().into_iter().find(|(stack, _)| *stack == name) {
        return stack;
    }
    match name {
        "* Map of Q" | "group P" => nested_collection_stack(name),
        _ => children_stack(name),
    }
}

/// Every root cell of the sweep, in the sweep's order: each main table's rows at path `-` by
/// column, then the children tables' rows.
#[must_use]
#[expect(clippy::too_many_lines, reason = "one loop per sweep table")]
pub fn cells() -> Vec<Cell> {
    let mut out = Vec::new();
    for (table, form, spellings) in main_tables() {
        let sides: &[(&str, Side, bool, bool)] = if form == Form::Init {
            &[("init", Side::Initializer, false, false)]
        } else {
            &[
                ("subject", Side::Subject, false, false),
                ("subject, written", Side::Subject, true, false),
                ("result, matched", Side::Result, false, true),
                ("result, unmatched", Side::Result, false, false),
            ]
        };
        for (side_name, side, written, matched) in sides {
            for (stack, layers) in stacks() {
                for text in spellings {
                    out.push(Cell {
                        key: (
                            table.clone(),
                            (*side_name).to_owned(),
                            stack.to_owned(),
                            (*text).to_owned(),
                        ),
                        form,
                        side: *side,
                        written: *written,
                        stack,
                        text,
                        other: matched.then(|| subject(form, &layers)),
                        bound: match side {
                            Side::Result => RESULT_BOUND,
                            Side::Initializer => &["pgm"],
                            _ => &[],
                        },
                        row: None,
                    });
                }
            }
        }
    }
    let rule_forms = [Form::Readable, Form::Claim, Form::Cells];
    for (table, tag, rows, bound) in [
        ("children", "c", &CHILDREN[..], CHILDREN_BOUND),
        (
            "children, base matched nowhere",
            "u",
            &CHILDREN_UNBASED[..],
            UNBASED_BOUND,
        ),
    ] {
        for form in rule_forms {
            let spelled = usize::from(form == Form::Cells);
            for (at, (stack, other, result)) in rows.iter().enumerate() {
                let other = (other[spelled] != "-").then(|| other[spelled].to_owned());
                let side = other.as_ref().map_or_else(
                    || format!("{} result", form_name(form)),
                    |other| format!("{} result over {other}", form_name(form)),
                );
                out.push(Cell {
                    key: (
                        table.to_owned(),
                        side,
                        (*stack).to_owned(),
                        result[spelled].to_owned(),
                    ),
                    form,
                    side: Side::Result,
                    written: false,
                    stack,
                    text: result[spelled],
                    other,
                    bound,
                    row: Some(format!("{tag}{at:02}")),
                });
            }
        }
    }
    for form in rule_forms {
        let spelled = usize::from(form == Form::Cells);
        for (at, (side_name, stack, other, entry)) in FRAGMENT_CHILD.iter().enumerate() {
            let other = (other[spelled] != "-").then(|| other[spelled].to_owned());
            let subject = *side_name == "subject";
            let side = other.as_ref().map_or_else(
                || format!("{} {side_name}", form_name(form)),
                |other| format!("{} {side_name} over {other}", form_name(form)),
            );
            out.push(Cell {
                key: (
                    "children, fragment child".to_owned(),
                    side,
                    (*stack).to_owned(),
                    entry[spelled].to_owned(),
                ),
                form,
                side: if subject { Side::Subject } else { Side::Result },
                written: false,
                stack,
                text: entry[spelled],
                other,
                bound: if subject { &[] } else { UNBASED_BOUND },
                row: Some(format!("f{at:02}")),
            });
        }
    }
    for (at, (stack, text)) in INITIALIZER_CHILDREN.iter().enumerate() {
        out.push(Cell {
            key: (
                "children, init".to_owned(),
                "init".to_owned(),
                (*stack).to_owned(),
                (*text).to_owned(),
            ),
            form: Form::Init,
            side: Side::Initializer,
            written: false,
            stack,
            text,
            other: None,
            bound: &["pgm"],
            row: Some(format!("i{at:02}")),
        });
    }
    out
}

/// A token of a spelling's text.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Ident(String),
    Literal(String),
    Punct(&'static str),
}

fn tokens(text: &str) -> Vec<Token> {
    const PUNCTS: [&str; 15] = [
        "..", "::", "->", "[", "]", "{", "}", "(", ")", ",", ":", "@", "!", "-", "=",
    ];
    let mut out = Vec::new();
    let mut rest = text;
    while let Some(c) = rest.chars().next() {
        if c.is_whitespace() {
            rest = &rest[c.len_utf8()..];
        } else if c.is_ascii_alphabetic() || c == '_' {
            let end = rest
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(rest.len());
            out.push(Token::Ident(rest[..end].to_owned()));
            rest = &rest[end..];
        } else if c.is_ascii_digit() {
            let end = rest
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(rest.len());
            out.push(Token::Literal(rest[..end].to_owned()));
            rest = &rest[end..];
        } else {
            let punct = PUNCTS
                .iter()
                .find(|punct| rest.starts_with(**punct))
                .unwrap_or_else(|| panic!("`{text}`: no sweep token at `{rest}`"));
            out.push(Token::Punct(punct));
            rest = &rest[punct.len()..];
        }
    }
    out
}

/// A reader of the sweep's spellings into the oracle's data, as the product reads an entry
/// (`krs_syntax::cell_entry`): `cells!` reads brackets and braces at the entry's head (below
/// presence and aliases) as instances, readable braces holding `->` as a map read, and an
/// initializer's `pgm`, `env` and `base` as configuration variables. Literals keep their text.
struct Reader {
    form: Form,
    tokens: Vec<Token>,
    at: usize,
}

impl Reader {
    fn peek(&self, ahead: usize) -> Option<&Token> {
        self.tokens.get(self.at + ahead)
    }

    fn is(&self, ahead: usize, punct: &str) -> bool {
        matches!(self.peek(ahead), Some(Token::Punct(found)) if *found == punct)
    }

    fn eat(&mut self, punct: &str) -> bool {
        let found = self.is(0, punct);
        if found {
            self.at += 1;
        }
        found
    }

    fn expect(&mut self, punct: &str) {
        assert!(self.eat(punct), "expected `{punct}` at {:?}", self.peek(0));
    }

    fn ident(&mut self) -> String {
        match self.tokens.get(self.at) {
            Some(Token::Ident(name)) => {
                self.at += 1;
                name.clone()
            }
            other => panic!("expected a name, found {other:?}"),
        }
    }

    /// Where the delimited group opened just before ends (the index of its closing token).
    fn closing(&self) -> usize {
        let mut depth = 0usize;
        for (at, token) in self.tokens.iter().enumerate().skip(self.at) {
            match token {
                Token::Punct("[" | "{" | "(") => depth += 1,
                Token::Punct("]" | "}" | ")") if depth == 0 => return at,
                Token::Punct("]" | "}" | ")") => depth -= 1,
                _ => {}
            }
        }
        panic!("an unclosed group")
    }

    fn end(&self) -> bool {
        matches!(self.peek(0), None | Some(Token::Punct("]" | "}" | ")")))
    }

    fn parse(&mut self, head: bool) -> Spelling {
        if matches!(self.peek(0), Some(Token::Ident(name)) if name == "_") {
            self.at += 1;
            return Spelling::Wild;
        }
        if matches!(self.peek(0), Some(Token::Ident(_))) && self.is(1, "@") && !self.is(2, "..") {
            let name = self.ident();
            self.expect("@");
            return Spelling::Alias(name, Box::new(self.parse(head)));
        }
        if self.eat("[") {
            let seq = self.seq("]");
            return if head && self.form == Form::Cells {
                Spelling::InstList(seq)
            } else {
                Spelling::Brackets(seq)
            };
        }
        if self.eat("{") {
            return self.braces(head);
        }
        if let Some(Token::Literal(text)) = self.peek(0) {
            let text = text.clone();
            self.at += 1;
            return Spelling::Literal(Some(text));
        }
        let mut last = self.ident();
        while self.eat("::") {
            last = self.ident();
        }
        if self.eat("!") {
            return self.macro_call(&last);
        }
        if self.eat("(") {
            return self.call(&last, head);
        }
        if self.eat("{") {
            let record = self.record(last);
            return Spelling::Record(record);
        }
        match last.as_str() {
            "None" => Spelling::Missing,
            name if self.form == Form::Init && ["pgm", "env", "base"].contains(&name) => {
                Spelling::ConfigVar(last)
            }
            _ => Spelling::Binder(last),
        }
    }

    fn call(&mut self, name: &str, head: bool) -> Spelling {
        let spelling = match name {
            "Some" => Spelling::Present(Box::new(self.parse(head))),
            "Cell" if self.form == Form::Cells => {
                let inner = self.parse(false);
                self.eat(",");
                Spelling::Cell(Box::new(inner))
            }
            "KCell" if self.form == Form::Cells => return Spelling::KCell(self.seq(")")),
            _ => {
                let mut arguments = Vec::new();
                while !self.end() {
                    arguments.push(self.parse(false));
                    if !self.eat(",") {
                        break;
                    }
                }
                Spelling::Call(arguments)
            }
        };
        self.expect(")");
        spelling
    }

    fn macro_call(&mut self, name: &str) -> Spelling {
        let close = if self.eat("[") {
            "]"
        } else if self.eat("(") {
            ")"
        } else {
            self.expect("{");
            "}"
        };
        let spelling = match name {
            "k" => return Spelling::KMacro(self.seq(close)),
            "map" => return Spelling::MapLit(self.map(close)),
            "fragment" => {
                let mut head = self.ident();
                while self.eat("::") {
                    head = self.ident();
                }
                self.expect("{");
                Spelling::Fragment(self.record(head))
            }
            "absent" => Spelling::Absent(Box::new(self.parse(false))),
            other => panic!("no sweep macro `{other}!`"),
        };
        self.expect(close);
        spelling
    }

    /// A rest at the reader, if one starts there: `..`, `name @ ..` or `..name`.
    fn rest(&mut self) -> Option<Rest> {
        if self.eat("..") {
            if let Some(Token::Ident(name)) = self.peek(0) {
                let name = name.clone();
                self.at += 1;
                return Some(Rest::Splice(name));
            }
            return Some(Rest::Anon);
        }
        if matches!(self.peek(0), Some(Token::Ident(_))) && self.is(1, "@") && self.is(2, "..") {
            let name = self.ident();
            self.at += 2;
            return Some(Rest::Named(name));
        }
        None
    }

    fn seq(&mut self, close: &str) -> Seq {
        let mut items = Vec::new();
        let mut rest = None;
        while !self.is(0, close) {
            if let Some(found) = self.rest() {
                let back = self.is(0, close) || self.is(0, ",") && self.is(1, close);
                rest = Some((found, if back { RestAt::Back } else { RestAt::Front }));
            } else {
                items.push(self.parse(false));
            }
            if !self.eat(",") {
                break;
            }
        }
        self.expect(close);
        Seq { items, rest }
    }

    fn map(&mut self, close: &str) -> Entries {
        let mut entries = Vec::new();
        let mut rest = None;
        while !self.is(0, close) {
            if let Some(found) = self.rest() {
                rest = Some(found);
            } else {
                let key = self.parse(false);
                self.expect("->");
                entries.push((key, self.parse(false)));
            }
            if !self.eat(",") {
                break;
            }
        }
        self.expect(close);
        Entries { entries, rest }
    }

    fn braces(&mut self, head: bool) -> Spelling {
        let close = self.closing();
        let mut depth = 0usize;
        let mut map_read = false;
        for token in &self.tokens[self.at..close] {
            match token {
                Token::Punct("[" | "{" | "(") => depth += 1,
                Token::Punct("]" | "}" | ")") => depth -= 1,
                Token::Punct("->") if depth == 0 => map_read = true,
                _ => {}
            }
        }
        if map_read && self.form != Form::Cells {
            return Spelling::MapRead(self.map("}"));
        }
        let seq = self.seq("}");
        if head && self.form == Form::Cells {
            Spelling::InstSet(seq)
        } else {
            Spelling::Braces(seq)
        }
    }

    fn record(&mut self, head: String) -> Record {
        let mut fields = Vec::new();
        let mut rest = RecordRest::Exact;
        while !self.is(0, "}") {
            if self.eat("..") {
                rest = if let Some(Token::Ident(base)) = self.peek(0) {
                    let base = base.clone();
                    self.at += 1;
                    RecordRest::Update(base)
                } else {
                    RecordRest::Open
                };
                self.eat(",");
                break;
            }
            let name = self.ident();
            let value = if self.eat(":") {
                self.parse(false)
            } else {
                Spelling::Binder(name.clone())
            };
            fields.push((name, value));
            if !self.eat(",") {
                break;
            }
        }
        self.expect("}");
        Record { head, fields, rest }
    }
}

/// The oracle's reading of the sweep spelling `text` in `form`, literals with their text (as a
/// probe reads it).
///
/// # Panics
///
/// Panics if `text` is no spelling the sweep writes.
#[must_use]
pub fn read(form: Form, text: &str) -> Spelling {
    let mut reader = Reader {
        form,
        tokens: tokens(text),
        at: 0,
    };
    let spelling = reader.parse(true);
    assert!(
        reader.at == reader.tokens.len(),
        "`{text}` reads past its end"
    );
    spelling
}

/// `text` with each name `renames` maps replaced, a path segment only after `crate::`.
fn renamed(text: &str, renames: &[(&str, &str)]) -> String {
    let mut out = String::with_capacity(text.len() + 8);
    let mut rest = text;
    while let Some(c) = rest.chars().next() {
        if c.is_ascii_alphabetic() || c == '_' {
            let end = rest
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(rest.len());
            let name = &rest[..end];
            let path_segment =
                rest[end..].starts_with("::") || out.ends_with("::") && !out.ends_with("crate::");
            match renames.iter().find(|(from, _)| *from == name) {
                Some((_, to)) if !path_segment => out.push_str(to),
                _ => out.push_str(name),
            }
            rest = &rest[end..];
        } else {
            out.push(c);
            rest = &rest[c.len_utf8()..];
        }
    }
    out
}

/// The sweep base's cell of each stack the sweep names, and the names its spellings take there:
/// a group is the content of one cell only (one struct per nested cell), and a cell's name is its
/// own in the whole configuration, so each group stack's group and children are renamed
/// (`G { a: x, .. }` on `? group G` is `Gp { pa: x, .. }`; no group is named as a command, which a readable rule's `use Cmd::*` brings into scope). A renaming changes no answer: the
/// cell's name plays no part (P1), and the spelling names the cell's own group as before. A
/// leaf's record spelling (`G { a: x, .. }` on `leaf Int`) names `frame`'s `G`, as the sweep's.
/// A stack's name, its cell, and the names its spellings take there.
type Slot = (
    &'static str,
    &'static str,
    &'static [(&'static str, &'static str)],
);

const SLOTS: [Slot; 23] = [
    ("computation", "prog", &[]),
    ("leaf Int", "pc", &[]),
    ("leaf List", "stack", &[]),
    ("leaf Cons", "seq", &[]),
    ("leaf Map", "env", &[]),
    ("leaf Set", "set", &[]),
    ("group G", "frame", &[]),
    ("? leaf Int", "counter", &[]),
    ("? leaf List", "olist", &[]),
    ("? leaf Map", "omap", &[]),
    (
        "? group G",
        "ogroup",
        &[("G", "Gp"), ("a", "pa"), ("b", "pb")],
    ),
    (
        "* List of G",
        "job",
        &[("G", "Gl"), ("a", "la"), ("b", "lb")],
    ),
    (
        "* Set of G",
        "bag",
        &[("G", "Gs"), ("a", "sa"), ("b", "sb")],
    ),
    (
        "* Map of G",
        "acct",
        &[("G", "Gm"), ("a", "ma"), ("b", "mb")],
    ),
    ("group H", "hcell", &[("l", "hl"), ("b", "hb")]),
    (
        "? group H",
        "ohcell",
        &[("H", "Ho"), ("l", "ohl"), ("b", "ohb")],
    ),
    ("* List of T", "tjob", &[("k", "tk"), ("n", "tn")]),
    ("* Map of A", "acc", &[("id", "aid"), ("l", "al")]),
    ("group C", "ccell", &[("c", "cc"), ("n", "cn")]),
    ("group O", "ocell", &[("o", "oo"), ("n", "on")]),
    (
        "group W",
        "wcell",
        &[
            ("g", "wg"),
            ("n", "wn"),
            ("G", "Gw"),
            ("a", "wa"),
            ("b", "wb"),
        ],
    ),
    ("group M", "mcell", &[("m", "mm"), ("n", "mn")]),
    (
        "group P",
        "pcell",
        &[("js", "pjs"), ("J", "Jp"), ("p", "pp")],
    ),
];

fn slot(stack: &str) -> (&'static str, &'static [(&'static str, &'static str)]) {
    SLOTS.iter().find(|(name, ..)| *name == stack).map_or_else(
        || panic!("the sweep base has no cell of the stack {stack}"),
        |(_, cell, renames)| (*cell, *renames),
    )
}

/// The sweep base's configuration: a cell of every stack the sweep names ([`SLOTS`]), and the
/// main computation `k`, whose command each rule case matches.
fn configuration() -> Vec<Decl> {
    let int = || leaf(Notation::Plain);
    let two = |head: &str, a: &str, b: &str| decl_group(head, vec![one(a, int()), one(b, int())]);
    let wrap = |name: &str, head: &str, child: Decl| one(name, decl_group(head, vec![child]));
    vec![
        one("k", Content::Comp),
        one("prog", Content::Comp),
        one("pc", int()),
        one("stack", leaf(Notation::List)),
        one("seq", leaf(Notation::Cons)),
        one("env", leaf(Notation::Map)),
        one("set", leaf(Notation::Set)),
        one("frame", two("G", "a", "b")),
        opt("counter", int()),
        opt("olist", leaf(Notation::List)),
        opt("omap", leaf(Notation::Map)),
        opt("ogroup", two("Gp", "pa", "pb")),
        wrap(
            "queue",
            "Queue",
            many("job", Order::List, two("Gl", "la", "lb")),
        ),
        wrap(
            "shelf",
            "Shelf",
            many("bag", Order::Set, two("Gs", "sa", "sb")),
        ),
        wrap(
            "bank",
            "Bank",
            many("acct", Order::Map, two("Gm", "ma", "mb")),
        ),
        one(
            "hcell",
            decl_group("H", vec![one("hl", leaf(Notation::List)), one("hb", int())]),
        ),
        opt(
            "ohcell",
            decl_group(
                "Ho",
                vec![one("ohl", leaf(Notation::List)), one("ohb", int())],
            ),
        ),
        wrap(
            "tqueue",
            "Tqueue",
            many(
                "tjob",
                Order::List,
                decl_group("T", vec![one("tk", Content::Comp), one("tn", int())]),
            ),
        ),
        wrap(
            "abank",
            "Abank",
            many(
                "acc",
                Order::Map,
                decl_group(
                    "A",
                    vec![one("aid", int()), one("al", leaf(Notation::List))],
                ),
            ),
        ),
        one(
            "ccell",
            decl_group("C", vec![one("cc", Content::Comp), one("cn", int())]),
        ),
        one(
            "ocell",
            decl_group("O", vec![opt("oo", int()), one("on", int())]),
        ),
        one(
            "wcell",
            decl_group(
                "W",
                vec![one("wg", two("Gw", "wa", "wb")), one("wn", int())],
            ),
        ),
        one(
            "mcell",
            decl_group("M", vec![one("mm", leaf(Notation::Map)), one("mn", int())]),
        ),
        one(
            "pcell",
            decl_group(
                "P",
                vec![many(
                    "pjs",
                    Order::List,
                    decl_group("Jp", vec![one("pp", int())]),
                )],
            ),
        ),
    ]
}

static CONFIGURATION: LazyLock<Vec<Decl>> = LazyLock::new(configuration);

fn find(cell: &str) -> (&'static Decl, Vec<Layer>, Option<&'static str>) {
    kinds::find_in(&CONFIGURATION, cell)
        .unwrap_or_else(|| panic!("the sweep base has no cell `{cell}`"))
}

/// Whether the sweep base declares `cell` as a cell of its own.
#[must_use]
pub fn declares(cell: &str) -> bool {
    kinds::find_in(&CONFIGURATION, cell).is_some_and(|(decl, ..)| !kinds::wrapper(decl))
}

/// The sweep base's cell `cell`'s own layers.
///
/// # Panics
///
/// Panics if the base declares no cell `cell`.
#[must_use]
pub fn stack(cell: &str) -> Vec<Layer> {
    kinds::own(find(cell).0)
}

/// The sweep base's groups, at any depth.
#[must_use]
pub fn groups() -> Vec<Group> {
    let mut groups = Vec::new();
    for decl in CONFIGURATION.iter() {
        collect_groups(&kinds::own(decl), &mut groups);
    }
    groups
}

static AFTER_COMMANDS: LazyLock<String> = LazyLock::new(|| {
    let mut out = String::from("}\n\n");
    kinds::structs(&CONFIGURATION, &mut out);
    out.push_str("#[k::configuration]\npub struct Machine {\n");
    for decl in CONFIGURATION.iter() {
        let _ = write!(
            out,
            "    {}\n    pub {}: {},\n",
            kinds::attribute(decl),
            decl.name,
            kinds::type_name(decl)
        );
    }
    out.push_str("}\n\n");
    out
});

static INITIALIZER: LazyLock<String> = LazyLock::new(|| {
    let mut item = ItemBuilder::new();
    item.push(kinds::HEADER);
    kinds::initializer_fields_in(&CONFIGURATION, None, &mut item);
    item.push(kinds::FOOTER);
    item.text
});

pub(super) fn base() -> BaseText {
    BaseText {
        before_commands: kinds::BEFORE_COMMANDS,
        after_commands: AFTER_COMMANDS.as_str(),
        initializer: INITIALIZER.as_str(),
        after_initializer: "",
    }
}

/// Why no K7 plan runs a sweep case.
const UNRUN: &str = "the compiled sweep's cases witness the compiler's verdict on each root sweep \
                     cell; the sweep base has no driver commands to set its cells up";

/// The names `spelling` binds or reads (binders, aliases, named rests and record bases).
fn names(spelling: &Spelling, out: &mut BTreeSet<String>) {
    let rest = |rest: &Rest, out: &mut BTreeSet<String>| {
        if let Rest::Named(name) | Rest::Splice(name) = rest {
            out.insert(name.clone());
        }
    };
    let seq = |seq: &Seq, out: &mut BTreeSet<String>| {
        for item in &seq.items {
            names(item, out);
        }
        if let Some((found, _)) = &seq.rest {
            rest(found, out);
        }
    };
    let record = |record: &Record, out: &mut BTreeSet<String>| {
        for (_, value) in &record.fields {
            names(value, out);
        }
        if let RecordRest::Update(base) = &record.rest {
            out.insert(base.clone());
        }
    };
    match spelling {
        Spelling::Binder(name) => {
            out.insert(name.clone());
        }
        Spelling::Alias(name, inner) => {
            out.insert(name.clone());
            names(inner, out);
        }
        Spelling::Present(inner) | Spelling::Absent(inner) | Spelling::Cell(inner) => {
            names(inner, out);
        }
        Spelling::Call(arguments) => arguments.iter().for_each(|argument| names(argument, out)),
        Spelling::Brackets(items)
        | Spelling::Braces(items)
        | Spelling::KCell(items)
        | Spelling::InstList(items)
        | Spelling::InstSet(items)
        | Spelling::KMacro(items) => seq(items, out),
        Spelling::MapRead(map) | Spelling::MapLit(map) => {
            for (key, value) in &map.entries {
                names(key, out);
                names(value, out);
            }
            if let Some(found) = &map.rest {
                rest(found, out);
            }
        }
        Spelling::Record(fields) | Spelling::Fragment(fields) => record(fields, out),
        Spelling::Wild | Spelling::Literal(_) | Spelling::ConfigVar(_) | Spelling::Missing => {}
    }
}

/// The names a subject entry binds: its binders and aliases (a named rest is no parameter).
pub(super) fn bound_by(spelling: &Spelling) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    names(spelling, &mut out);
    out
}

/// The names `spelling`'s aliases bind to a record, each with the record's head constructor
/// (`me @ Acct { .. }` or its fragment: `me`, `Acct`), in first-occurrence order.
#[must_use]
pub fn records_by(spelling: &Spelling) -> Vec<(String, String)> {
    fn walk(spelling: &Spelling, out: &mut Vec<(String, String)>) {
        if let Spelling::Alias(name, inner) = spelling
            && let Spelling::Record(record) | Spelling::Fragment(record) = &**inner
            && !out.iter().any(|(known, _)| known == name)
        {
            out.push((name.clone(), record.head.clone()));
        }
        for inner in super::cells_oracle::children(spelling) {
            walk(inner, out);
        }
    }
    let mut out = Vec::new();
    walk(spelling, &mut out);
    out
}

/// The children sweep's reading of a base its subject does not show (`CHILDREN_BOUND`'s `me`):
/// each name of `bound` an update `..name` in `spelling` names binds a record of that update's
/// own constructor, matched elsewhere in the sentence (S5.0g item 3b ruling 1: `..base` takes
/// the fields of a record of its own constructor), in first-occurrence order.
#[must_use]
pub fn update_records(bound: &[&str], spelling: &Spelling) -> Vec<(String, String)> {
    fn walk(bound: &[&str], spelling: &Spelling, out: &mut Vec<(String, String)>) {
        if let Spelling::Record(record) | Spelling::Fragment(record) = spelling
            && let RecordRest::Update(base) = &record.rest
            && bound.contains(&base.as_str())
            && !out.iter().any(|(known, _)| known == base)
        {
            out.push((base.clone(), record.head.clone()));
        }
        for inner in super::cells_oracle::children(spelling) {
            walk(bound, inner, out);
        }
    }
    let mut out = Vec::new();
    walk(bound, spelling, &mut out);
    out
}

/// The Rust type of a `cells!` binder at a position whose content is `stack` (the layers below
/// the position), or `KItem` where the entry is not of the stack's kind there.
fn position_type(stack: &[Layer]) -> String {
    match stack {
        [Layer::Leaf(Notation::Plain)] => kinds::INT.to_owned(),
        [Layer::Leaf(Notation::List)] => "k::Term<k::builtin::List>".to_owned(),
        [Layer::Leaf(Notation::Map)] => "k::Term<k::builtin::Map>".to_owned(),
        [Layer::Leaf(Notation::Set)] => "k::Term<k::builtin::Set>".to_owned(),
        // A cons leaf's whole content is a term of the cons list's sort (S5.0g item 3a review
        // F-3 (a)); its items, read through `items_at`, are `Int`s.
        [Layer::Leaf(Notation::Cons)] => "k::Term<crate::Ints>".to_owned(),
        [Layer::Group(group)] | [Layer::Instances(_), Layer::Group(group)] => {
            format!("crate::{}", group.name)
        }
        [Layer::Optional, inner @ ..] => position_type(inner),
        _ => kinds::ITEM.to_owned(),
    }
}

/// The `cells!` parameters `spelling`'s binders need, each typed by its position on `stack`.
pub(super) fn binder_types(spelling: &Spelling, stack: &[Layer], out: &mut Vec<(String, String)>) {
    let mut add = |name: &str, ty: String| {
        if !out.iter().any(|(known, _)| known == name) {
            out.push((name.to_owned(), ty));
        }
    };
    let items_at = |stack: &[Layer]| -> Vec<Layer> {
        match stack {
            [Layer::Leaf(Notation::Cons)] => vec![Layer::Leaf(Notation::Plain)],
            [Layer::Instances(_), group] => vec![group.clone()],
            _ => Vec::new(),
        }
    };
    match (spelling, stack) {
        (Spelling::Binder(name), _) => add(name, position_type(stack)),
        // An alias names the instance it matches; `cells!` binds it there, as no parameter.
        (Spelling::Alias(_, inner), _) => binder_types(inner, stack, out),
        (Spelling::Present(inner), [Layer::Optional, rest @ ..]) => binder_types(inner, rest, out),
        (Spelling::Cell(inner) | Spelling::Present(inner) | Spelling::Absent(inner), _) => {
            binder_types(inner, stack, out);
        }
        (
            Spelling::Brackets(items)
            | Spelling::Braces(items)
            | Spelling::KCell(items)
            | Spelling::InstList(items)
            | Spelling::InstSet(items)
            | Spelling::KMacro(items),
            _,
        ) => {
            let at = items_at(stack);
            for item in &items.items {
                binder_types(item, &at, out);
            }
        }
        (Spelling::MapRead(map) | Spelling::MapLit(map), _) => {
            for (key, value) in &map.entries {
                binder_types(key, &[], out);
                binder_types(value, &[], out);
            }
        }
        (Spelling::Record(record) | Spelling::Fragment(record), _) => {
            let group = match stack {
                [Layer::Group(group)] | [Layer::Instances(_), Layer::Group(group)] => Some(group),
                _ => None,
            };
            for (field, value) in &record.fields {
                let child = group
                    .and_then(|group| group.children.iter().find(|(name, _)| name == field))
                    .map_or(&[][..], |(_, layers)| &layers[..]);
                binder_types(value, child, out);
            }
        }
        (Spelling::Call(arguments), _) => {
            for argument in arguments {
                binder_types(argument, &[], out);
            }
        }
        _ => {}
    }
}

/// The result entries a written subject's rule may write in its cell, in the sweep's names, in
/// order of preference: one that keeps the subject's rest and one that writes the content anew.
fn written_candidates(form: Form, stack: &str) -> &'static [&'static str] {
    if form == Form::Cells {
        match stack {
            "computation" => &["k::configuration::KCell(..)", "k::configuration::KCell()"],
            "leaf Int" => &["k::configuration::Cell(1)"],
            "leaf List" | "leaf Cons" => {
                &["k::configuration::Cell([..])", "k::configuration::Cell([])"]
            }
            "leaf Map" => &["k::configuration::Cell(k::map![])"],
            "leaf Set" => &["k::configuration::Cell(set::empty())"],
            "group G" => &["k::fragment![crate::G { a: 1, b: 1 }]"],
            "? leaf Int" => &["Some(k::configuration::Cell(1))", "None"],
            "? leaf List" => &[
                "Some(k::configuration::Cell([..]))",
                "Some(k::configuration::Cell([]))",
                "None",
            ],
            "? leaf Map" => &["Some(k::configuration::Cell(k::map![]))", "None"],
            "? group G" => &["Some(k::fragment![crate::G { a: 1, b: 1 }])", "None"],
            "* List of G" => &["[..]", "[]"],
            _ => &["{ .. }", "{ }"],
        }
    } else {
        match stack {
            "computation" | "leaf List" | "leaf Cons" | "* List of G" => &["[..]", "[]"],
            "leaf Int" => &["1"],
            "leaf Map" => &["map![]"],
            "leaf Set" => &["set::empty()"],
            "group G" => &["G { a: 1, b: 1 }"],
            "? leaf Int" => &["Some(1)", "None"],
            "? leaf List" => &["Some([..])", "Some([])", "None"],
            "? leaf Map" => &["Some(map![])", "None"],
            "? group G" => &["Some(G { a: 1, b: 1 })", "None"],
            _ => &["{ .. }", "{ }"],
        }
    }
}

/// A root cell's case, or why it has none.
pub(super) enum Built {
    /// The case and its reading.
    Case(Box<Generated>),
    /// No case can be compiled for the cell, for this reason.
    Unbuilt(&'static str),
}

/// Why a written subject has no case: no result entry in the form pairs with it.
pub const NO_WRITTEN_RESULT: &str = "unbuilt: no result entry of the form writes this cell beside the subject's entry and is admitted (`outcome` admits none of the written candidates over it): the case would refuse its result, not its subject";

/// Why a cell of the stack `* Map of Q` (D-5's: an instance `Q { id, js }` whose `js` is a List
/// collection beside `id`) has no case: the stack cannot be declared. The rule is K's, not P1's:
/// a `*` cell's instances are its parent's whole content, one collection term, so the `*` cell
/// is its parent's only child (`krs::analysis::collection-siblings`). P1's stack admits the
/// configuration (a group's child has a stack of its own), so these rows are about a
/// configuration P1 describes and K cannot declare.
pub const UNDECLARABLE: &str = "unbuilt: the stack cannot be declared, by K's declaration rule (not P1's stack, which admits it): a `*` cell's instances are its parent's whole content, one collection term, so the `*` cell is its parent's only child (`krs::analysis::collection-siblings`), and `js` stands beside `id`; no case of this stack compiles";

/// Why a children row whose update `..me` reads a value the sentence matches elsewhere has no
/// case of its own here.
pub const ME_ELSEWHERE: &str = "unbuilt: the update's base `me` is bound by another entry of the sentence than the cell's subject, a case of two entries (S5.0g item 3b's G1 and F-7)";

const fn side_segment(cell: &Cell) -> &'static str {
    match (cell.side, cell.written, cell.other.is_some()) {
        (Side::Subject, false, _) => "subject",
        (Side::Subject, true, _) => "written",
        (Side::Result, _, true) => "result",
        (Side::Result, _, false) => "overwrite",
        _ => "init",
    }
}

/// The case of `cell` on the sweep base.
#[expect(clippy::too_many_lines, reason = "one sentence per side and form")]
pub(super) fn build(cell: &Cell) -> Built {
    if cell.stack == "* Map of Q" {
        return Built::Unbuilt(UNDECLARABLE);
    }
    let (name, renames) = slot(cell.stack);
    let text = renamed(cell.text, renames);
    let spelling = read(cell.form, &text);
    let other = cell.other.as_deref().map(|other| renamed(other, renames));
    let other_spelling = other.as_deref().map(|other| read(cell.form, other));
    let held = bound_by(&spelling);
    if cell.side == Side::Result
        && held.contains("me")
        && cell.bound.contains(&"me")
        && !other_spelling
            .as_ref()
            .is_some_and(|other| bound_by(other).contains("me"))
    {
        return Built::Unbuilt(ME_ELSEWHERE);
    }
    let (decl, path, _) = find(name);
    let stack = kinds::own(decl);
    // What the names bound outside the entry bind: the subject's entry of the cell's aliases,
    // and, for the children sweep's `me` its subject does not show, a record of its update's
    // constructor (a case of that reading is `ME_ELSEWHERE`, unbuilt).
    let mut records = other_spelling.as_ref().map(records_by).unwrap_or_default();
    for found in update_records(cell.bound, &spelling) {
        if !records.iter().any(|(known, _)| *known == found.0) {
            records.push(found);
        }
    }
    let context = Context {
        bound: cell.bound.iter().map(|name| (*name).to_owned()).collect(),
        records,
        other: other_spelling.clone(),
        written: cell.written,
        groups: groups(),
    };
    let written = if cell.written {
        let admitted = |candidate: &&str, other: Option<Spelling>| {
            let text = renamed(candidate, renames);
            let result = read(cell.form, &text);
            let context = Context {
                bound: held.iter().cloned().collect(),
                records: records_by(&spelling),
                other,
                written: false,
                groups: groups(),
            };
            matches!(
                outcome(cell.form, Side::Result, &path, &stack, &result, &context),
                Outcome::Admit { lint: None } | Outcome::After
            )
            .then_some((text, result))
        };
        let candidates = written_candidates(cell.form, cell.stack);
        // A subject refused by its own kind has no rest a result can pair with: its result is
        // the first candidate admitted on its own (as an overwrite), so the subject's refusal
        // stays the case's one mistake.
        let refused =
            !outcome(cell.form, Side::Subject, &path, &stack, &spelling, &context).admits();
        let found = candidates
            .iter()
            .find_map(|candidate| admitted(candidate, Some(spelling.clone())))
            .or_else(|| {
                refused
                    .then(|| {
                        candidates
                            .iter()
                            .find_map(|candidate| admitted(candidate, None))
                    })
                    .flatten()
            });
        match found {
            Some(found) => Some(found),
            None => return Built::Unbuilt(NO_WRITTEN_RESULT),
        }
    } else {
        None
    };
    let family_form = form_name(cell.form);
    let mut slot = vec![family_form.to_owned(), side_segment(cell).to_owned()];
    slot.push(match &cell.row {
        Some(row) => format!("{row}-{name}"),
        None => name.to_owned(),
    });
    let spec = CaseSpec {
        family: Family::Sweep,
        base: Base::Sweep,
        side: cell.side,
        kind: None,
        slot,
        construct: text.clone(),
    };
    let entry = |cell: &str, side: Side, spelling: Spelling| {
        let (decl, path, _) = find(cell);
        Entry {
            cell: cell.to_owned(),
            side,
            path,
            stack: kinds::own(decl),
            spelling,
        }
    };
    let mut generated = if cell.form == Form::Init {
        init_case(spec, name, &text, spelling.clone())
    } else {
        let mut sentence = Sentence {
            spec,
            cell: name,
            text: &text,
            other: other.as_deref(),
            other_spelling: other_spelling.clone(),
            written: written.as_ref().map(|(text, _)| text.as_str()),
            held: &held,
            stack: &stack,
            spelling: &spelling,
            entries: Vec::new(),
        };
        // A template's other entries are declared spellings (no literal texts), as the
        // product's reading of the rendered sentence is compared with them.
        if let Some((_, result)) = &written {
            sentence
                .entries
                .push(entry(name, Side::Result, untexted(result)));
        }
        if let Some(other) = &other_spelling {
            sentence
                .entries
                .push(entry(name, Side::Subject, untexted(other)));
        }
        if cell.form == Form::Cells {
            sentence.cells()
        } else {
            sentence.readable(cell.form)
        }
    };
    generated.entry.context = context;
    generated.entry.entry = entry(name, cell.side, spelling);
    if cell.form == Form::Init {
        generated.entry.context.groups = Vec::new();
        generated.entry.entry.stack = init_stack(name);
    }
    generated.case.k7 = super::k7::K7::skip(super::k7::SkipKind::Form, UNRUN);
    Built::Case(Box::new(generated))
}

/// An initializer's stack of `cell`: a collection's top layer stripped (its value is one
/// instance's template, P5).
fn init_stack(cell: &str) -> Vec<Layer> {
    let mut stack = stack(cell);
    if matches!(stack.first(), Some(Layer::Instances(_))) {
        stack.remove(0);
    }
    stack
}

/// A rule case's parts.
struct Sentence<'s> {
    spec: CaseSpec,
    cell: &'static str,
    text: &'s str,
    other: Option<&'s str>,
    other_spelling: Option<Spelling>,
    written: Option<&'s str>,
    held: &'s BTreeSet<String>,
    stack: &'s [Layer],
    spelling: &'s Spelling,
    /// The template's entries of the cell besides the case's own.
    entries: Vec<Entry>,
}

impl Sentence<'_> {
    /// The names the command binds: on a result, those the entry holds and the subject's entry
    /// of the cell does not bind, of `x`, `y`, `z`.
    fn arguments(&self) -> Vec<&'static str> {
        if self.spec.side != Side::Result {
            return Vec::new();
        }
        let other = self
            .other_spelling
            .as_ref()
            .map(bound_by)
            .unwrap_or_default();
        ["x", "y", "z"]
            .into_iter()
            .filter(|name| self.held.contains(*name) && !other.contains(*name))
            .collect()
    }

    fn k_entries(form: Form, arguments: &[&str]) -> [Entry; 2] {
        let call =
            super::cells_oracle::build::call(arguments.iter().map(|name| bind(name)).collect());
        let entry = |side, spelling| {
            let (decl, path, _) = find("k");
            Entry {
                cell: "k".to_owned(),
                side,
                path,
                stack: kinds::own(decl),
                spelling,
            }
        };
        if form == Form::Cells {
            [
                entry(
                    Side::Subject,
                    Spelling::KCell(seq(vec![call], named("tail"))),
                ),
                entry(Side::Result, Spelling::KCell(seq(vec![], splice("tail")))),
            ]
        } else {
            [
                entry(Side::Subject, Spelling::Brackets(seq(vec![call], open()))),
                entry(Side::Result, Spelling::Brackets(seq(vec![], open()))),
            ]
        }
    }

    fn readable(self, form: Form) -> Generated {
        let arguments = self.arguments();
        let command = Command::for_case(&self.spec.id(), arguments.len());
        let label = format!("case_{}", self.spec.tag());
        let (block, attribute, sentence) = if form == Form::Claim {
            (
                "k::claims!",
                "    #[k::claim(all_paths)]\n",
                TemplateSentence::Claim,
            )
        } else {
            ("k::rules!", "", TemplateSentence::Rule)
        };
        let mut item = ItemBuilder::new();
        item.push(block)
            .push(" {\n    for Machine;\n    use Cmd::*;\n\n")
            .push(attribute)
            .push("    ")
            .push(&label)
            .push(&format!(
                ": {{ k: [{}({}), ..], ",
                command.name,
                arguments.join(", ")
            ));
        let cell = self.cell;
        if self.spec.side == Side::Subject {
            item.entry(cell, self.text).push(" } => { k: [..]");
            if let Some(written) = self.written {
                item.push(&format!(", {cell}: {written}"));
            }
            item.push(" };\n}\n");
        } else {
            if let Some(other) = self.other {
                item.push(&format!("{cell}: {other} "));
            }
            item.push("} => { k: [..], ")
                .entry(cell, self.text)
                .push(" };\n}\n");
        }
        let mut entries = Self::k_entries(form, &arguments).to_vec();
        entries.extend(self.entries.iter().cloned());
        self.finish(sentence, Packaging::Shared(command), &item, entries, form)
    }

    fn cells(self) -> Generated {
        let arguments = self.arguments();
        let command = Command::for_case(&self.spec.id(), arguments.len());
        let tag = self.spec.tag();
        let mut parameters = arguments
            .iter()
            .map(|name| ((*name).to_owned(), kinds::INT.to_owned()))
            .collect::<Vec<_>>();
        if self.spec.side == Side::Subject {
            binder_types(self.spelling, self.stack, &mut parameters);
        }
        if let Some(other) = &self.other_spelling {
            binder_types(other, self.stack, &mut parameters);
        }
        let mut item = ItemBuilder::new();
        item.push(&format!(
            "#[k::rule(label = \"case-{tag}\")]\npub fn case_{tag}(\n"
        ));
        for (name, ty) in &parameters {
            item.push(&format!("    {name}: {ty},\n"));
        }
        let key = cells_key(self.cell);
        item.push(&format!(
            "    k::cells! {{ k: k::configuration::KCell(crate::Cmd::{}({}), tail @ ..), ",
            command.name,
            arguments.join(", ")
        ));
        let result = "state @ .. }: crate::Machine,\n) -> crate::Machine {\n    k::cells! { k: k::configuration::KCell(..tail), ";
        if self.spec.side == Side::Subject {
            item.entry(&key, self.text).push(", ").push(result);
            if let Some(written) = self.written {
                item.push(&format!("{key}: {written}, "));
            }
            item.push("..state }\n}\n");
        } else {
            if let Some(other) = self.other {
                item.push(&format!("{key}: {other}, "));
            }
            item.push(result)
                .entry(&key, self.text)
                .push(", ..state }\n}\n");
        }
        let mut entries = Self::k_entries(Form::Cells, &arguments).to_vec();
        entries.extend(self.entries.iter().cloned());
        self.finish(
            TemplateSentence::Rule,
            Packaging::Shared(command),
            &item,
            entries,
            Form::Cells,
        )
    }

    fn finish(
        self,
        sentence: TemplateSentence,
        packaging: Packaging,
        item: &ItemBuilder,
        entries: Vec<Entry>,
        form: Form,
    ) -> Generated {
        let case = self.spec.finish(packaging, item);
        Generated {
            case,
            entry: EntryCase {
                form,
                entry: entries[0].clone(),
                context: Context::default(),
                template: Template {
                    sentence,
                    entries,
                    guard: false,
                    variables: Vec::new(),
                },
            },
        }
    }
}

/// The `cells!` key of `cell`: a top-level cell by its name, a nested one through its parent's
/// type.
fn cells_key(cell: &str) -> String {
    match find(cell) {
        (_, _, Some(parent)) => format!("crate::{parent}::{cell}"),
        _ => cell.to_owned(),
    }
}

/// The configuration variables besides `pgm` an initializer value reads, each with its type: a
/// record update's base takes the record's group, a map literal's splice the builtin `Map`.
fn variables_of(spelling: &Spelling, out: &mut Vec<(String, String)>) {
    let mut add = |name: &str, ty: String| {
        if name != "pgm" && !out.iter().any(|(known, _)| known == name) {
            out.push((name.to_owned(), ty));
        }
    };
    match spelling {
        Spelling::Record(record) | Spelling::Fragment(record) => {
            if let RecordRest::Update(base) = &record.rest {
                add(base, format!("crate::{}", record.head));
            }
            for (_, value) in &record.fields {
                variables_of(value, out);
            }
        }
        Spelling::MapLit(map) => {
            if let Some(Rest::Splice(base)) = &map.rest {
                add(base, "Map".to_owned());
            }
        }
        Spelling::Present(inner) | Spelling::Absent(inner) => variables_of(inner, out),
        _ => {}
    }
}

fn init_case(spec: CaseSpec, cell: &str, text: &str, spelling: Spelling) -> Generated {
    let mut variables = Vec::new();
    variables_of(&spelling, &mut variables);
    let mut item = ItemBuilder::new();
    if variables.is_empty() {
        item.push(kinds::HEADER);
    } else {
        item.push(
            "impl Machine {\n    #[k::init]\n    pub fn init(\n        #[k::config_var(name = \"PGM\", main)] pgm: Stmt,\n",
        );
        for (name, ty) in &variables {
            item.push(&format!(
                "        #[k::config_var(name = \"{}\")] {name}: {ty},\n",
                name.to_uppercase()
            ));
        }
        item.push("    ) -> Self {\n        Self {\n");
    }
    kinds::initializer_fields_in(&CONFIGURATION, Some((cell, text)), &mut item);
    item.push(kinds::FOOTER);
    let case = spec.finish(Packaging::Own(OwnReason::Initializer), &item);
    let mut entries = Vec::new();
    for decl in CONFIGURATION.iter() {
        let field = match &decl.content {
            Content::Group(_, children) if kinds::wrapper(decl) => &children[0],
            _ => decl,
        };
        if field.name == cell {
            continue;
        }
        let top = std::ptr::eq(field, decl);
        entries.push(Entry {
            cell: field.name.clone(),
            side: Side::Initializer,
            path: Vec::new(),
            stack: init_stack(&field.name),
            spelling: kinds::default(field, top).1,
        });
    }
    Generated {
        case,
        entry: EntryCase {
            form: Form::Init,
            entry: Entry {
                cell: cell.to_owned(),
                side: Side::Initializer,
                path: Vec::new(),
                stack: init_stack(cell),
                spelling,
            },
            context: Context::default(),
            template: Template {
                sentence: TemplateSentence::Initializer,
                entries,
                guard: false,
                variables: std::iter::once(("pgm".to_owned(), true))
                    .chain(variables.into_iter().map(|(name, _)| (name, false)))
                    .collect(),
            },
        },
    }
}

/// Every root cell with its case or its reason, in the sweep's order.
pub(super) static BUILT: LazyLock<Vec<(Cell, Built)>> = LazyLock::new(|| {
    cells()
        .into_iter()
        .map(|cell| {
            let built = build(&cell);
            (cell, built)
        })
        .collect()
});

static GENERATED: LazyLock<BTreeMap<String, (Key, EntryCase)>> = LazyLock::new(|| {
    BUILT
        .iter()
        .filter_map(|(cell, built)| match built {
            Built::Case(generated) => Some((
                generated.case.id.clone(),
                (cell.key.clone(), generated.entry.clone()),
            )),
            Built::Unbuilt(_) => None,
        })
        .collect()
});

/// The sweep's cases, but those of a cell another family's case already writes in the same form,
/// side, stack and spelling (`existing`, by [`row_key`]): that case is the cell's witness.
pub(super) fn cases(existing: &BTreeSet<(String, String, String, String)>, cases: &mut Vec<Case>) {
    for (cell, built) in BUILT.iter() {
        if let Built::Case(generated) = built
            && !existing.contains(&main_key(cell))
        {
            cases.push(generated.case.clone());
        }
    }
}

/// A main-table cell's key as [`row_key`] spells a case's: `(form, side, stack, spelling)`, the
/// spelling the sweep writes, read without literal texts, a matched result's side naming the
/// subject's entry it stands over; children rows have none (`-`).
#[must_use]
pub fn main_key(cell: &Cell) -> (String, String, String, String) {
    if cell.row.is_some() {
        return (
            "-".to_owned(),
            "-".to_owned(),
            "-".to_owned(),
            "-".to_owned(),
        );
    }
    let side = match &cell.other {
        Some(other) => format!(
            "{} over {:?}",
            cell.key.1,
            untexted(&read(cell.form, other))
        ),
        None => cell.key.1.clone(),
    };
    (
        form_name(cell.form).to_owned(),
        side,
        cell.key.2.clone(),
        format!("{:?}", untexted(&read(cell.form, cell.text))),
    )
}

/// A case's row in the sweep's terms: its form, its side (a subject the result leaves or writes,
/// a result over a matched or an unmatched cell), its stack, and its spelling without literal
/// texts.
#[must_use]
pub fn row_key(cell_stack: &[Layer], entry: &EntryCase) -> (String, String, String, String) {
    let side = match entry.entry.side {
        Side::Subject if entry.context.written => "subject, written",
        Side::Subject => "subject",
        Side::Result if entry.context.other.is_some() => "result, matched",
        Side::Result => "result, unmatched",
        _ => "init",
    };
    let stack = match stack_name(&entry.entry.cell, cell_stack).as_str() {
        "second computation" => "computation".to_owned(),
        "group" => "group G".to_owned(),
        "? group" => "? group G".to_owned(),
        list if list.starts_with("* ") => format!("{list} of G"),
        other => other.to_owned(),
    };
    let side = match &entry.context.other {
        Some(other) if entry.entry.side == Side::Result => {
            format!("{side} over {:?}", untexted(other))
        }
        _ => side.to_owned(),
    };
    (
        form_name(entry.form).to_owned(),
        side,
        stack,
        format!("{:?}", untexted(&entry.entry.spelling)),
    )
}

/// `spelling` with its literals' texts dropped, as a generator declares spellings.
#[must_use]
pub fn untexted(spelling: &Spelling) -> Spelling {
    let seq = |seq: &Seq| Seq {
        items: seq.items.iter().map(untexted).collect(),
        rest: seq.rest.clone(),
    };
    let map = |map: &Entries| Entries {
        entries: map
            .entries
            .iter()
            .map(|(key, value)| (untexted(key), untexted(value)))
            .collect(),
        rest: map.rest.clone(),
    };
    let record = |record: &Record| Record {
        head: record.head.clone(),
        fields: record
            .fields
            .iter()
            .map(|(name, value)| (name.clone(), untexted(value)))
            .collect(),
        rest: record.rest.clone(),
    };
    let boxed = |inner: &Spelling| Box::new(untexted(inner));
    match spelling {
        Spelling::Literal(_) => Spelling::Literal(None),
        Spelling::Call(arguments) => Spelling::Call(arguments.iter().map(untexted).collect()),
        Spelling::Present(inner) => Spelling::Present(boxed(inner)),
        Spelling::Absent(inner) => Spelling::Absent(boxed(inner)),
        Spelling::Cell(inner) => Spelling::Cell(boxed(inner)),
        Spelling::Alias(name, inner) => Spelling::Alias(name.clone(), boxed(inner)),
        Spelling::Brackets(items) => Spelling::Brackets(seq(items)),
        Spelling::Braces(items) => Spelling::Braces(seq(items)),
        Spelling::KCell(items) => Spelling::KCell(seq(items)),
        Spelling::InstList(items) => Spelling::InstList(seq(items)),
        Spelling::InstSet(items) => Spelling::InstSet(seq(items)),
        Spelling::KMacro(items) => Spelling::KMacro(seq(items)),
        Spelling::MapRead(entries) => Spelling::MapRead(map(entries)),
        Spelling::MapLit(entries) => Spelling::MapLit(map(entries)),
        Spelling::Record(fields) => Spelling::Record(record(fields)),
        Spelling::Fragment(fields) => Spelling::Fragment(record(fields)),
        other => other.clone(),
    }
}

/// The reading of a sweep case, and the root cell it witnesses.
///
/// # Panics
///
/// Panics if `case` is no case of the sweep.
#[must_use]
pub fn entry_case(case: &Case) -> EntryCase {
    GENERATED
        .get(&case.id)
        .unwrap_or_else(|| panic!("{} is no sweep case", case.id))
        .1
        .clone()
}

/// The root cell a sweep case was generated for, `None` for another case.
#[must_use]
pub fn key_of(id: &str) -> Option<&'static Key> {
    GENERATED.get(id).map(|(key, _)| key)
}

/// The cells no case can be compiled for, with the reason.
#[must_use]
pub fn unbuilt() -> BTreeMap<Key, &'static str> {
    BUILT
        .iter()
        .filter_map(|(cell, built)| match built {
            Built::Unbuilt(reason) => Some((cell.key.clone(), *reason)),
            Built::Case(_) => None,
        })
        .collect()
}

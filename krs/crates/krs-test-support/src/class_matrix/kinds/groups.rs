//! S5.0g part (b), item 3b: the kinds base's case groups of more than one entry, and the listed
//! single-entry groups the compiled sweep does not reach at its root (paths, a key two levels
//! deep, the field shorthand, the no-effect lints of R9, an alias in a result).
//!
//! Each group is one sentence written in readable (claims alike) and in `cells!`: its subject's
//! and its result's entries besides the command's, and the entries whose cases it has. A case is
//! the sentence with one entry as its own: the template holds the others, the context the names
//! the other subject entries bind, the subject's entry of the cell for a result, and whether the
//! result writes the cell for a subject. Every spelling is read from its text by the sweep's
//! reader ([`super::super::sweep::read`]), which reads as the product's `cell_entry` does (check 2
//! compares them), so a group is written once, as text.

use std::collections::BTreeSet;

use super::super::cells_oracle::build::{bind, call, named, open, seq, splice};
use super::super::cells_oracle::{
    Context, EntryCase, Form, Sentence as TemplateSentence, Spelling, Template,
};
use super::super::sweep::{binder_types, bound_by, read, records_by, untexted};
use super::super::{Base, CaseSpec, Command, Family, ItemBuilder, Packaging, Side};
use super::{Generated, INT, entry, groups, key, stack};

/// An entry of a group's sentence: its cell, and its text in readable and in `cells!` (empty:
/// the form has no such sentence).
type Written = (&'static str, [&'static str; 2]);

/// One sentence of a group.
pub(super) struct Group {
    /// The ID's side segment: the group's name, and a letter per sentence.
    pub(super) tag: &'static str,
    /// The command's arguments, `Int` binders the result reads.
    pub(super) arguments: &'static [&'static str],
    /// The subject's entries besides `k`'s.
    pub(super) subject: &'static [Written],
    /// The result's entries besides `k`'s.
    pub(super) result: &'static [Written],
    /// The entries that are a case's own, by side and cell.
    pub(super) cases: &'static [(Side, &'static str)],
    /// The `cells!` parameters after the command's arguments, in the order their binders first
    /// occur (as `cells!` requires), where their positions do not give them: a binder inside a
    /// list element or a map, whose position is a term's; an alias inside a term (of a List
    /// leaf's element, of a nested collection's instance in a fragment field), a term binder
    /// that is no instance label (only a cell collection's own instance alias is one); and a
    /// named rest inside a term (`rest @ ..` in a List leaf's brackets), a term binder that is no
    /// frame (only a cell collection's, a computation's and a map cell's own rests are). These are
    /// the product's rule-signature rules (`krs_syntax::cells_pattern_term_binders`). Empty: each
    /// binder typed by its position.
    pub(super) typed: &'static [(&'static str, &'static str)],
}

const S: Side = Side::Subject;
const RS: Side = Side::Result;

/// The groups, in the ticket's order (`tickets/S5-0g-b3b-listed-groups.md`).
pub(super) const GROUPS: &[Group] = &[
    // Listed: a cell named below a List and a Set collection's instance, and the Map
    // collection's key named through its path (S1 (b)). Each sentence tests one entry, so its
    // other entries are ones admitted alone (P4 over a sentence: a second refused entry would be
    // the sentence's answer as well): a result's subject matches the cell through its
    // collection's instance, since an entry naming the cell is refused whatever it spells.
    Group {
        tag: "path-a",
        arguments: &[],
        subject: &[("payload", ["x", "k::configuration::Cell(x)"])],
        result: &[],
        cases: &[(S, "payload")],
        typed: &[],
    },
    Group {
        tag: "path-a",
        arguments: &[],
        subject: &[("key", ["x", "k::configuration::Cell(x)"])],
        result: &[],
        cases: &[(S, "key")],
        typed: &[],
    },
    Group {
        tag: "path-b",
        arguments: &["x"],
        subject: &[(
            "job",
            [
                "[Job { payload: _, .. }, ..]",
                "[k::fragment![crate::Job { payload: _, .. }], ..]",
            ],
        )],
        result: &[("payload", ["x", "k::configuration::Cell(x)"])],
        cases: &[(RS, "payload")],
        typed: &[],
    },
    Group {
        tag: "path-c",
        arguments: &["x"],
        subject: &[(
            "bag",
            [
                "{ Obj { key: _, .. }, .. }",
                "{ k::fragment![crate::Obj { key: _, .. }], .. }",
            ],
        )],
        result: &[("key", ["x", "k::configuration::Cell(x)"])],
        cases: &[(RS, "key")],
        typed: &[],
    },
    Group {
        tag: "path-d",
        arguments: &[],
        subject: &[("id", ["x", "k::configuration::Cell(x)"])],
        result: &[],
        cases: &[(S, "id")],
        typed: &[],
    },
    Group {
        tag: "path-e",
        arguments: &["x"],
        subject: &[(
            "account",
            [
                "{ Acct { id: _, .. }, .. }",
                "{ k::fragment![crate::Acct { id: _, .. }], .. }",
            ],
        )],
        result: &[("id", ["x", "k::configuration::Cell(x)"])],
        cases: &[(RS, "id")],
        typed: &[],
    },
    // Listed: a key two levels deep (`crate::Ag::aa`, below the Map collection; `crate::Hjob::hpay`,
    // below a `?` and a List collection), one entry per sentence.
    Group {
        tag: "deep-a",
        arguments: &[],
        subject: &[("aa", ["x", "k::configuration::Cell(x)"])],
        result: &[],
        cases: &[(S, "aa")],
        typed: &[],
    },
    Group {
        tag: "deep-a",
        arguments: &[],
        subject: &[("hpay", ["y", "k::configuration::Cell(y)"])],
        result: &[],
        cases: &[(S, "hpay")],
        typed: &[],
    },
    Group {
        tag: "deep-b",
        arguments: &["x"],
        subject: &[],
        result: &[("aa", ["x", "k::configuration::Cell(x)"])],
        cases: &[(RS, "aa")],
        typed: &[],
    },
    Group {
        tag: "deep-b",
        arguments: &["x"],
        subject: &[],
        result: &[("hpay", ["x", "k::configuration::Cell(x)"])],
        cases: &[(RS, "hpay")],
        typed: &[],
    },
    // Listed: the field shorthand in an instance record (S5.K).
    Group {
        tag: "shorthand",
        arguments: &[],
        subject: &[(
            "job",
            [
                "[Job { payload, .. }, ..]",
                "[k::fragment![crate::Job { payload, .. }], ..]",
            ],
        )],
        result: &[],
        cases: &[(S, "job")],
        typed: &[],
    },
    Group {
        tag: "shorthand",
        arguments: &[],
        subject: &[(
            "bag",
            [
                "{ Obj { key, .. }, .. }",
                "{ k::fragment![crate::Obj { key, .. }], .. }",
            ],
        )],
        result: &[],
        cases: &[(S, "bag")],
        typed: &[],
    },
    Group {
        tag: "shorthand",
        arguments: &[],
        subject: &[(
            "account",
            [
                "{ Acct { id, .. }, .. }",
                "{ k::fragment![crate::Acct { id, .. }], .. }",
            ],
        )],
        result: &[],
        cases: &[(S, "account")],
        typed: &[],
    },
    // Listed: R9's no-effect spellings, linted (a record or wrapper that constrains nothing) and
    // not (an instance pattern, which matches one instance; an empty list, which constrains).
    Group {
        tag: "lint",
        arguments: &[],
        subject: &[("frame", ["G { .. }", "k::fragment![crate::G { .. }]"])],
        result: &[],
        cases: &[(S, "frame")],
        typed: &[],
    },
    Group {
        tag: "lint",
        arguments: &[],
        subject: &[("env", ["", "k::configuration::Cell(k::map![..])"])],
        result: &[],
        cases: &[(S, "env")],
        typed: &[],
    },
    Group {
        tag: "lint",
        arguments: &[],
        subject: &[("prog", ["", "k::configuration::KCell(..)"])],
        result: &[],
        cases: &[(S, "prog")],
        typed: &[],
    },
    Group {
        tag: "lint",
        arguments: &[],
        subject: &[(
            "bag",
            [
                "{ Obj { .. }, .. }",
                "{ k::fragment![crate::Obj { .. }], .. }",
            ],
        )],
        result: &[],
        cases: &[(S, "bag")],
        typed: &[],
    },
    Group {
        tag: "lint",
        arguments: &[],
        subject: &[(
            "account",
            [
                "{ Acct { .. }, .. }",
                "{ k::fragment![crate::Acct { .. }], .. }",
            ],
        )],
        result: &[],
        cases: &[(S, "account")],
        typed: &[],
    },
    Group {
        tag: "lint",
        arguments: &[],
        subject: &[("job", ["[]", "[]"])],
        result: &[],
        cases: &[(S, "job")],
        typed: &[],
    },
    // Listed: S5.0's ruling 3, an alias in a result, at a group and at a leaf, one per sentence.
    Group {
        tag: "alias",
        arguments: &["x", "y"],
        subject: &[(
            "frame",
            ["G { a: z, .. }", "k::fragment![crate::G { a: z, .. }]"],
        )],
        result: &[(
            "frame",
            [
                "f @ G { a: x, b: y }",
                "f @ k::fragment![crate::G { a: x, b: y }]",
            ],
        )],
        cases: &[(RS, "frame")],
        typed: &[],
    },
    Group {
        tag: "alias",
        arguments: &["x"],
        subject: &[("pc", ["w", "k::configuration::Cell(w)"])],
        result: &[("pc", ["p @ x", "k::configuration::Cell(p @ x)"])],
        cases: &[(RS, "pc")],
        typed: &[],
    },
    // G1 and F-7: an instance updated from a record of its constructor the sentence matches in
    // another cell (a List leaf's element), with a `?`, group, computation (exact and with a
    // rest) and Map child; and the base bound to a non-record (`g1-f`, `record-update-base`:
    // S5.0g item 3b ruling 1).
    Group {
        tag: "g1-a",
        arguments: &["x"],
        subject: &[
            (
                "stack",
                [
                    "[me @ Acct { id: z, .. }, ..]",
                    "k::configuration::Cell([me @ k::fragment![crate::Acct { id: z, .. }], rest @ ..])",
                ],
            ),
            ("account", ["{ .. }", "{ instances0 @ .. }"]),
        ],
        result: &[
            ("stack", ["[..]", "k::configuration::Cell(rest)"]),
            (
                "account",
                [
                    "{ Acct { acounter: Some(x), ..me }, .. }",
                    "{ k::fragment![crate::Acct { acounter: Some(x), ..me }], ..instances0 }",
                ],
            ),
        ],
        cases: &[(RS, "account"), (S, "stack")],
        typed: &[
            ("me", "crate::Acct"),
            ("z", INT),
            ("rest", "k::Term<k::builtin::List>"),
        ],
    },
    Group {
        tag: "g1-b",
        arguments: &["x"],
        subject: &[
            (
                "stack",
                [
                    "[me @ Acct { id: z, .. }, ..]",
                    "k::configuration::Cell([me @ k::fragment![crate::Acct { id: z, .. }], rest @ ..])",
                ],
            ),
            ("account", ["{ .. }", "{ instances0 @ .. }"]),
        ],
        result: &[
            ("stack", ["[..]", "k::configuration::Cell(rest)"]),
            (
                "account",
                [
                    "{ Acct { aframe: Ag { aa: x }, ..me }, .. }",
                    "{ k::fragment![crate::Acct { aframe: Ag { aa: x }, ..me }], ..instances0 }",
                ],
            ),
        ],
        cases: &[(RS, "account")],
        typed: &[
            ("me", "crate::Acct"),
            ("z", INT),
            ("rest", "k::Term<k::builtin::List>"),
        ],
    },
    Group {
        tag: "g1-c",
        arguments: &["x"],
        subject: &[
            (
                "stack",
                [
                    "[me @ Acct { id: z, .. }, ..]",
                    "k::configuration::Cell([me @ k::fragment![crate::Acct { id: z, .. }], rest @ ..])",
                ],
            ),
            ("account", ["{ .. }", "{ instances0 @ .. }"]),
        ],
        result: &[
            ("stack", ["[..]", "k::configuration::Cell(rest)"]),
            (
                "account",
                [
                    "{ Acct { aprog: [x], ..me }, .. }",
                    "{ k::fragment![crate::Acct { aprog: [x], ..me }], ..instances0 }",
                ],
            ),
        ],
        cases: &[(RS, "account")],
        typed: &[
            ("me", "crate::Acct"),
            ("z", INT),
            ("rest", "k::Term<k::builtin::List>"),
        ],
    },
    Group {
        tag: "g1-d",
        arguments: &["x"],
        subject: &[
            (
                "stack",
                [
                    "[me @ Acct { id: z, .. }, ..]",
                    "k::configuration::Cell([me @ k::fragment![crate::Acct { id: z, .. }], rest @ ..])",
                ],
            ),
            ("account", ["{ .. }", "{ instances0 @ .. }"]),
        ],
        result: &[
            ("stack", ["[..]", "k::configuration::Cell(rest)"]),
            (
                "account",
                [
                    "{ Acct { aprog: [x, ..], ..me }, .. }",
                    "{ k::fragment![crate::Acct { aprog: [x, ..], ..me }], ..instances0 }",
                ],
            ),
        ],
        cases: &[(RS, "account")],
        typed: &[
            ("me", "crate::Acct"),
            ("z", INT),
            ("rest", "k::Term<k::builtin::List>"),
        ],
    },
    Group {
        tag: "g1-e",
        arguments: &["x"],
        subject: &[
            (
                "stack",
                [
                    "[me @ Acct { id: z, .. }, ..]",
                    "k::configuration::Cell([me @ k::fragment![crate::Acct { id: z, .. }], rest @ ..])",
                ],
            ),
            ("account", ["{ .. }", "{ instances0 @ .. }"]),
        ],
        result: &[
            ("stack", ["[..]", "k::configuration::Cell(rest)"]),
            (
                "account",
                [
                    "{ Acct { aenv: { x -> 1 }, ..me }, .. }",
                    "{ k::fragment![crate::Acct { aenv: k::map![x -> 1], ..me }], ..instances0 }",
                ],
            ),
        ],
        cases: &[(RS, "account")],
        typed: &[
            ("me", "crate::Acct"),
            ("z", INT),
            ("rest", "k::Term<k::builtin::List>"),
        ],
    },
    Group {
        tag: "g1-f",
        arguments: &["x"],
        subject: &[
            (
                "stack",
                ["[me, ..]", "k::configuration::Cell([me, rest @ ..])"],
            ),
            ("account", ["{ .. }", "{ instances0 @ .. }"]),
        ],
        result: &[
            ("stack", ["[..]", "k::configuration::Cell(rest)"]),
            (
                "account",
                [
                    "{ Acct { acounter: Some(x), ..me }, .. }",
                    "{ k::fragment![crate::Acct { acounter: Some(x), ..me }], ..instances0 }",
                ],
            ),
        ],
        cases: &[(RS, "account")],
        typed: &[("me", "k::KItem"), ("rest", "k::Term<k::builtin::List>")],
    },
    // G1: KEVM's restore shape, a group saved in a List leaf's element written back over the
    // group's cell.
    Group {
        tag: "g1-restore",
        arguments: &["x"],
        subject: &[
            (
                "stack",
                [
                    "[saved @ G { a: z, .. }, ..]",
                    "k::configuration::Cell([saved @ k::fragment![crate::G { a: z, .. }], rest @ ..])",
                ],
            ),
            ("frame", ["_", "_"]),
        ],
        result: &[
            ("stack", ["[..]", "k::configuration::Cell(rest)"]),
            (
                "frame",
                [
                    "G { a: x, ..saved }",
                    "k::fragment![crate::G { a: x, ..saved }]",
                ],
            ),
        ],
        cases: &[(RS, "frame"), (S, "stack")],
        typed: &[
            ("saved", "crate::G"),
            ("z", INT),
            ("rest", "k::Term<k::builtin::List>"),
        ],
    },
    // G3: an instance record naming a `?` child and a `*` child, and a subject `None` on its `?`
    // child the result does not create (`g3-b`, `absence-test-without-creation`: P5 at every
    // depth, S5.0g item 3b ruling 2).
    Group {
        tag: "g3-a",
        arguments: &[],
        subject: &[(
            "account",
            [
                "{ Acct { id: z, acounter: Some(y), .. }, .. }",
                "{ k::fragment![crate::Acct { id: z, acounter: Some(y), .. }], .. }",
            ],
        )],
        result: &[],
        cases: &[(S, "account")],
        typed: &[("z", INT), ("y", INT)],
    },
    Group {
        tag: "g3-b",
        arguments: &[],
        subject: &[(
            "account",
            [
                "{ Acct { id: z, acounter: None, .. }, .. }",
                "{ k::fragment![crate::Acct { id: z, acounter: None, .. }], .. }",
            ],
        )],
        result: &[],
        cases: &[(S, "account")],
        typed: &[("z", INT)],
    },
    Group {
        tag: "g3-c",
        arguments: &["x"],
        subject: &[(
            "account",
            [
                "{ me @ Acct { id: z, acounter: Some(y), .. }, .. }",
                "{ me @ k::fragment![crate::Acct { id: z, acounter: Some(y), .. }], instances0 @ .. }",
            ],
        )],
        result: &[(
            "account",
            [
                "{ Acct { acounter: Some(x), ..me }, .. }",
                "{ k::fragment![crate::Acct { acounter: Some(x), ..me }], ..instances0 }",
            ],
        )],
        cases: &[(RS, "account")],
        typed: &[("z", INT), ("y", INT)],
    },
    Group {
        tag: "g3-d",
        arguments: &[],
        subject: &[(
            "account",
            [
                "{ Acct { id: z, aqueue: Aqueue { ajob: [Ajob { apay: y }, ..] }, .. }, .. }",
                "{ k::fragment![crate::Acct { id: z, aqueue: Aqueue { ajob: [Ajob { apay: y }, ..] }, .. }], .. }",
            ],
        )],
        result: &[],
        cases: &[(S, "account")],
        typed: &[("z", INT), ("y", INT)],
    },
    // G4: records two levels deep in results: a group in a created and in an updated instance,
    // a collection child with labels at two levels, a Map leaf child (M3 at depth).
    Group {
        tag: "g4-a",
        arguments: &["x"],
        subject: &[("account", ["{ .. }", "{ instances0 @ .. }"])],
        result: &[(
            "account",
            [
                "{ Acct { id: x, aframe: Ag { aa: x }, .. }, .. }",
                "{ k::fragment![crate::Acct { id: x, aframe: Ag { aa: x }, .. }], ..instances0 }",
            ],
        )],
        cases: &[(RS, "account")],
        typed: &[],
    },
    Group {
        tag: "g4-b",
        arguments: &["x"],
        subject: &[(
            "account",
            [
                "{ me @ Acct { id: z, aframe: Ag { aa: y }, .. }, .. }",
                "{ me @ k::fragment![crate::Acct { id: z, aframe: Ag { aa: y }, .. }], instances0 @ .. }",
            ],
        )],
        result: &[(
            "account",
            [
                "{ Acct { aframe: Ag { aa: x }, ..me }, .. }",
                "{ k::fragment![crate::Acct { aframe: Ag { aa: x }, ..me }], ..instances0 }",
            ],
        )],
        cases: &[(RS, "account")],
        typed: &[("z", INT), ("y", INT)],
    },
    Group {
        tag: "g4-c",
        arguments: &["x"],
        subject: &[(
            "account",
            [
                "{ me @ Acct { id: z, aqueue: Aqueue { ajob: [j @ Ajob { apay: y }, ..] }, .. }, .. }",
                "{ me @ k::fragment![crate::Acct { id: z, aqueue: Aqueue { ajob: [j @ Ajob { apay: y }, jobs @ ..] }, .. }], instances0 @ .. }",
            ],
        )],
        result: &[(
            "account",
            [
                "{ Acct { aqueue: Aqueue { ajob: [Ajob { apay: x, ..j }, ..] }, ..me }, .. }",
                "{ k::fragment![crate::Acct { aqueue: Aqueue { ajob: [Ajob { apay: x, ..j }, ..jobs] }, ..me }], ..instances0 }",
            ],
        )],
        cases: &[(RS, "account")],
        typed: &[
            ("z", INT),
            ("j", "crate::Ajob"),
            ("y", INT),
            ("jobs", "k::KItem"),
        ],
    },
    Group {
        tag: "g4-d",
        arguments: &["x"],
        subject: &[(
            "account",
            [
                "{ me @ Acct { id: z, aenv: { v -> y, .. }, .. }, .. }",
                "{ me @ k::fragment![crate::Acct { id: z, aenv: k::map![v -> y, ..], .. }], instances0 @ .. }",
            ],
        )],
        result: &[(
            "account",
            [
                "{ Acct { aenv: { v -> x, .. }, ..me }, .. }",
                "{ k::fragment![crate::Acct { aenv: k::map![v -> x, ..], ..me }], ..instances0 }",
            ],
        )],
        cases: &[(RS, "account")],
        typed: &[("z", INT), ("v", "k::KItem"), ("y", "k::KItem")],
    },
    // G5: entries across cells: a named rest moved to another cell, `group-and-descendant` beside
    // a path entry, a subject `None` on a `?` ancestor with a path entry below it, and a label
    // used by another collection (`g5-b`: an update whose base is a record of another
    // constructor, `record-update-base`, S5.0g item 3b ruling 1).
    Group {
        tag: "g5-a",
        arguments: &[],
        subject: &[
            (
                "stack",
                ["[x, r @ ..]", "k::configuration::Cell([x, r @ ..])"],
            ),
            ("olist", ["Some(old)", "Some(k::configuration::Cell(old))"]),
        ],
        result: &[
            ("stack", ["[x]", "k::configuration::Cell([x])"]),
            (
                "olist",
                ["Some([..r])", "Some(k::configuration::Cell([..r]))"],
            ),
        ],
        cases: &[(RS, "olist")],
        typed: &[
            ("x", "k::KItem"),
            ("r", "k::Term<k::builtin::List>"),
            ("old", "k::Term<k::builtin::List>"),
        ],
    },
    Group {
        tag: "g5-b",
        arguments: &[],
        subject: &[
            (
                "job",
                [
                    "[me @ Job { payload: z }, ..]",
                    "[me @ k::fragment![crate::Job { payload: z }], ..]",
                ],
            ),
            ("bag", ["{ .. }", "{ instances0 @ .. }"]),
        ],
        result: &[(
            "bag",
            [
                "{ Obj { key: 1, ..me }, .. }",
                "{ k::fragment![crate::Obj { key: 1, ..me }], ..instances0 }",
            ],
        )],
        cases: &[(RS, "bag")],
        typed: &[],
    },
    Group {
        tag: "g5-c",
        arguments: &[],
        subject: &[
            (
                "opt",
                [
                    "Some(H { hpc: y, .. })",
                    "Some(k::fragment![crate::H { hpc: y, .. }])",
                ],
            ),
            ("hstack", ["[z, ..]", "k::configuration::Cell([z, ..])"]),
        ],
        result: &[],
        cases: &[(S, "opt"), (S, "hstack")],
        typed: &[("y", INT), ("z", "k::KItem")],
    },
    Group {
        tag: "g5-d",
        arguments: &[],
        subject: &[
            ("opt", ["None", "None"]),
            ("hpc", ["z", "k::configuration::Cell(z)"]),
        ],
        result: &[],
        cases: &[(S, "opt"), (S, "hpc")],
        typed: &[],
    },
];

/// The case of `group` whose own entry is `own`, in `family`, if the form writes the sentence.
#[expect(
    clippy::too_many_lines,
    reason = "one sentence per form, as `sweep::build`"
)]
fn case(group: &Group, family: Family, own: (Side, &str)) -> Option<Generated> {
    let (form, at) = match family {
        Family::Readable => (Form::Readable, 0),
        Family::Claim => (Form::Claim, 0),
        _ => (Form::Cells, 1),
    };
    let written = |entries: &[Written]| -> Option<Vec<(&'static str, &'static str)>> {
        entries
            .iter()
            .map(|(cell, texts)| (!texts[at].is_empty()).then_some((*cell, texts[at])))
            .collect()
    };
    // A form writes the sentence only where it writes every entry of it.
    let subject = written(group.subject)?;
    let result = written(group.result)?;
    let side_entries = if own.0 == Side::Subject {
        &subject
    } else {
        &result
    };
    let &(_, text) = side_entries.iter().find(|(cell, _)| *cell == own.1)?;
    let spec = CaseSpec {
        family,
        base: Base::Kinds,
        side: own.0,
        kind: None,
        slot: vec![group.tag.to_owned(), "kinds".to_owned(), own.1.to_owned()],
        construct: text.to_owned(),
    };
    let command = Command::for_case(&spec.id(), group.arguments.len());
    let arguments = group.arguments.join(", ");
    let read = |text: &str| read(form, text);
    let cells = form == Form::Cells;
    // The template: `k`'s entries, then every entry but the case's own, without literal texts.
    let k = |side, spelling| entry("k", side, spelling);
    let call = call(group.arguments.iter().map(|name| bind(name)).collect());
    let mut entries = if cells {
        vec![
            k(
                Side::Subject,
                Spelling::KCell(seq(vec![call], named("tail"))),
            ),
            k(Side::Result, Spelling::KCell(seq(vec![], splice("tail")))),
        ]
    } else {
        vec![
            k(Side::Subject, Spelling::Brackets(seq(vec![call], open()))),
            k(Side::Result, Spelling::Brackets(seq(vec![], open()))),
        ]
    };
    let is_own = |side: Side, cell: &str| side == own.0 && cell == own.1;
    for (side, list) in [(Side::Subject, &subject), (Side::Result, &result)] {
        for (cell, text) in list {
            if !is_own(side, cell) {
                entries.push(entry(cell, side, untexted(&read(text))));
            }
        }
    }
    // The context: the names bound outside the entry (the command's arguments, every other
    // subject entry's) and what each binds where it is a record, the subject's entry of a
    // result's cell, the result's entry of a subject's cell and whether the result writes it.
    let mut bound = group
        .arguments
        .iter()
        .map(|name| (*name).to_owned())
        .collect::<BTreeSet<_>>();
    if cells {
        bound.insert("tail".to_owned());
    }
    let mut records = Vec::new();
    for (cell, text) in &subject {
        if !is_own(Side::Subject, cell) {
            bound.extend(bound_by(&read(text)));
            records.extend(records_by(&read(text)));
        }
    }
    let other_side = if own.0 == Side::Result {
        &subject
    } else {
        &result
    };
    let context = Context {
        bound: bound.into_iter().collect(),
        records,
        other: other_side
            .iter()
            .find(|(cell, _)| *cell == own.1)
            .map(|(_, text)| read(text)),
        written: own.0 == Side::Subject && result.iter().any(|(cell, _)| *cell == own.1),
        groups: groups(),
    };
    let mut item = ItemBuilder::new();
    let fields = |item: &mut ItemBuilder, side: Side, list: &[(&str, &str)]| {
        for (cell, text) in list {
            let name = if cells { key(cell) } else { (*cell).to_owned() };
            item.push(", ");
            if is_own(side, cell) {
                item.entry(&name, text);
            } else {
                item.push(&format!("{name}: {text}"));
            }
        }
    };
    let sentence = if cells {
        let mut parameters = group
            .arguments
            .iter()
            .map(|name| ((*name).to_owned(), INT.to_owned()))
            .collect::<Vec<_>>();
        if group.typed.is_empty() {
            for (cell, text) in &subject {
                binder_types(&read(text), &stack(cell), &mut parameters);
            }
        } else {
            parameters.extend(
                group
                    .typed
                    .iter()
                    .map(|(name, ty)| ((*name).to_owned(), (*ty).to_owned())),
            );
        }
        let tag = spec.tag();
        item.push(&format!(
            "#[k::rule(label = \"case-{tag}\")]\npub fn case_{tag}(\n"
        ));
        for (name, ty) in &parameters {
            item.push(&format!("    {name}: {ty},\n"));
        }
        item.push(&format!(
            "    k::cells! {{ k: k::configuration::KCell(crate::Cmd::{}({arguments}), tail @ ..)",
            command.name
        ));
        fields(&mut item, Side::Subject, &subject);
        item.push(concat!(
            ", state @ .. }: crate::Machine,\n",
            ") -> crate::Machine {\n",
            "    k::cells! { k: k::configuration::KCell(..tail)",
        ));
        fields(&mut item, Side::Result, &result);
        item.push(", ..state }\n}\n");
        TemplateSentence::Rule
    } else {
        let (block, attribute, sentence) = if form == Form::Claim {
            (
                "k::claims!",
                "    #[k::claim(all_paths)]\n",
                TemplateSentence::Claim,
            )
        } else {
            ("k::rules!", "", TemplateSentence::Rule)
        };
        item.push(block)
            .push(" {\n    for Machine;\n    use Cmd::*;\n\n")
            .push(attribute)
            .push(&format!(
                "    case_{}: {{ k: [{}({arguments}), ..]",
                spec.tag(),
                command.name
            ));
        fields(&mut item, Side::Subject, &subject);
        item.push(" } => { k: [..]");
        fields(&mut item, Side::Result, &result);
        item.push(" };\n}\n");
        sentence
    };
    let case = spec.finish(Packaging::Shared(command), &item);
    Some(Generated {
        case,
        entry: EntryCase {
            form,
            entry: entry(own.1, own.0, read(text)),
            context,
            template: Template {
                sentence,
                entries,
                guard: false,
                variables: Vec::new(),
            },
        },
    })
}

/// Every case of the groups: each own entry in readable, claim and `cells!`, where the form
/// writes the sentence.
pub(super) fn cases() -> Vec<Generated> {
    let mut out = Vec::new();
    for group in GROUPS {
        for &own in group.cases {
            for family in [Family::Readable, Family::Claim, Family::Cells] {
                out.extend(case(group, family, own));
            }
        }
    }
    out
}

/// The listed initializer cases: S5.0's ruling 4, a named rest or an alias in an initializer's
/// value (nothing in an initializer is a pattern).
pub(super) const INITIALIZERS: [(&str, &str); 4] = [
    ("stack", "[0, r @ ..]"),
    ("env", "k::map![0 -> 1, r @ ..]"),
    ("frame", "f @ G { a: 0, b: 0 }"),
    ("prog", "k::k![Cmd::Go(), r @ ..]"),
];

/// G6: the sentences that keep a `cells!` pattern as they matched it, an equation's function
/// context, a context alias and a context, each written once per own entry (`cells!` only: none
/// has a readable form). A kept pattern changes nothing, so it means what a rule with that
/// pattern on both sides means (P0): each entry is a subject entry over a cell the sentence
/// keeps, as a rule's result leaving the cell out keeps it.
///
/// The own entries are the S1 (b) path under a `*` ancestor (a Map collection's instance child,
/// a List collection's instance child), which is refused for the ancestor whatever it spells; a
/// plain leaf and a List leaf beside them, admitted, which witness that the sentence's other
/// entries are ones admitted alone; and what a kept pattern's pairing asks (S5.3 part 3,
/// ruling B): a `?` cell's `Some(..)`; its `None`, at the cell's root and below one (an
/// instance record's `?` child), which creates nothing (P5); an entry that matches every content
/// (S5.2's lint); a collection's instance record (a Set's, with an anonymous and a named rest,
/// and a List's front one); and a List
/// collection's back instance. A `?` child's `None` inside a `?` group's fragment is not one of
/// them: the macro reads a group's fragment as a term, where `None` is a binder.
pub(super) const CONTEXTS: &[(&str, &str)] = &[
    ("apc", "k::configuration::Cell(x)"),
    ("payload", "k::configuration::Cell(x)"),
    ("pc", "k::configuration::Cell(x)"),
    ("stack", "k::configuration::Cell([x, ..])"),
    ("counter", "Some(k::configuration::Cell(x))"),
    ("counter", "None"),
    (
        "account",
        "{ k::fragment![crate::Acct { id: z, acounter: None, .. }], .. }",
    ),
    ("pc", "k::configuration::Cell(_)"),
    ("bag", "{ k::fragment![crate::Obj { key: x }], .. }"),
    (
        "bag",
        "{ k::fragment![crate::Obj { key: x }], instances0 @ .. }",
    ),
    ("job", "[k::fragment![crate::Job { payload: x }], ..]"),
    ("job", "[.., k::fragment![crate::Job { payload: x }]]"),
];

/// The sentence a G6 case stands in.
#[derive(Clone, Copy)]
enum Kept {
    /// An `#[k::equation]` whose last parameter is a function context.
    FunctionContext,
    /// A `#[k::context_alias]`, whose pattern frames the computation's `here`.
    ContextAlias,
    /// A `#[k::context]` over a `cells!` pattern, whose hole is the case's command's argument.
    Context,
}

/// The G6 case of `cell`'s entry `text` in the sentence `kept`.
fn context_case(kept: Kept, cell: &str, text: &str) -> Generated {
    let tag = match kept {
        Kept::FunctionContext => "g6-function-context",
        Kept::ContextAlias => "g6-context-alias",
        Kept::Context => "g6-context",
    };
    let spec = CaseSpec {
        family: Family::Cells,
        base: Base::Kinds,
        side: Side::Subject,
        kind: None,
        slot: vec![tag.to_owned(), "kinds".to_owned(), cell.to_owned()],
        construct: text.to_owned(),
    };
    let spelling = read(Form::Cells, text);
    let mut parameters = Vec::new();
    binder_types(&spelling, &stack(cell), &mut parameters);
    let case_tag = spec.tag();
    let command = Command::for_case(&spec.id(), usize::from(matches!(kept, Kept::Context)));
    let mut item = ItemBuilder::new();
    let mut bound = parameters
        .iter()
        .map(|(name, _)| name.clone())
        .collect::<BTreeSet<_>>();
    let mut entries = Vec::new();
    match kept {
        Kept::FunctionContext => {
            // The equation defines a function of its own, so the function context makes no
            // other function of the base one of the configuration.
            item.push(&format!(
                "#[k::function(partial, sort = Int, syntax = \"g6probe{case_tag}({{a}})\")]\n\
                 pub struct G6Probe{case_tag} {{\n    pub a: k::Term<k::KItem>,\n}}\n\n\
                 #[k::equation]\nfn case_{case_tag}(\n    a: k::Term<k::KItem>,\n"
            ));
            for (name, ty) in &parameters {
                item.push(&format!("    {name}: {ty},\n"));
            }
            item.push(&format!(
                "    k::term![G6Probe{case_tag}(a)]: k::Term<k::builtin::Int>,\n    k::cells! {{ "
            ));
            item.entry(&key(cell), text);
            item.push(", .. }: crate::Machine,\n) -> k::Term<k::builtin::Int> {\n    0\n}\n");
            bound.insert("a".to_owned());
        }
        Kept::ContextAlias => {
            item.push(&format!(
                "#[k::context_alias(name = case_{case_tag}, here = site)]\nfn case_{case_tag}(\n"
            ));
            for (name, ty) in &parameters {
                item.push(&format!("    {name}: {ty},\n"));
            }
            item.push("    k::cells! { k: k::configuration::KCell(site, tail @ ..), ");
            item.entry(&key(cell), text);
            item.push(", state @ .. }: crate::Machine,\n) {\n}\n");
            bound.extend(["site".to_owned(), "tail".to_owned()]);
            entries.push(entry(
                "k",
                Side::Subject,
                Spelling::KCell(seq(vec![bind("site")], named("tail"))),
            ));
        }
        Kept::Context => {
            // The hole is the command's own `Int` argument, a result, so the context heats
            // nothing a program runs: it is judged for its pattern alone.
            item.push(&format!(
                "#[k::context(hole = h)]\nfn case_{case_tag}(\n    h: k::Term<k::builtin::Int>,\n"
            ));
            for (name, ty) in &parameters {
                item.push(&format!("    {name}: {ty},\n"));
            }
            let k = format!(
                "k::configuration::KCell(Cmd::{} {{ a: h }}, ..)",
                command.name
            );
            item.push(&format!("    k::cells! {{ k: {k}, "));
            item.entry(&key(cell), text);
            item.push(", .. }: crate::Machine,\n) {\n}\n");
            bound.insert("h".to_owned());
            entries.push(entry("k", Side::Subject, read(Form::Cells, &k)));
        }
    }
    let case = spec.finish(Packaging::Alone(command), &item);
    Generated {
        case,
        entry: EntryCase {
            form: Form::Cells,
            entry: entry(cell, Side::Subject, spelling),
            context: Context {
                bound: bound.into_iter().collect(),
                records: Vec::new(),
                other: None,
                written: false,
                groups: groups(),
            },
            template: Template {
                sentence: TemplateSentence::Context,
                entries,
                guard: false,
                variables: Vec::new(),
            },
        },
    }
}

/// Every G6 case: each own entry in a function context, in a context alias and in a context.
pub(super) fn context_cases() -> Vec<Generated> {
    CONTEXTS
        .iter()
        .flat_map(|(cell, text)| {
            [Kept::FunctionContext, Kept::ContextAlias, Kept::Context]
                .map(|kept| context_case(kept, cell, text))
        })
        .collect()
}

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
use super::super::sweep::{binder_types, bound_by, read, untexted};
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
    /// list element or a map, whose position is a term's, and an alias of a list element, a term
    /// binder that is no instance label. Empty: each binder typed by its position.
    pub(super) typed: &'static [(&'static str, &'static str)],
}

const S: Side = Side::Subject;
const RS: Side = Side::Result;

/// The groups, in the ticket's order (`tickets/S5-0g-b3b-listed-groups.md`).
pub(super) const GROUPS: &[Group] = &[
    // Listed: a cell named below a List and a Set collection's instance, and the Map
    // collection's key named through its path (S1 (b)).
    Group {
        tag: "path-a",
        arguments: &[],
        subject: &[
            ("payload", ["x", "k::configuration::Cell(x)"]),
            ("key", ["x", "k::configuration::Cell(x)"]),
        ],
        result: &[],
        cases: &[(S, "payload"), (S, "key")],
        typed: &[],
    },
    Group {
        tag: "path-b",
        arguments: &["x"],
        subject: &[("payload", ["y", "k::configuration::Cell(y)"])],
        result: &[("payload", ["x", "k::configuration::Cell(x)"])],
        cases: &[(RS, "payload")],
        typed: &[],
    },
    Group {
        tag: "path-c",
        arguments: &["x"],
        subject: &[("key", ["y", "k::configuration::Cell(y)"])],
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
        subject: &[("id", ["y", "k::configuration::Cell(y)"])],
        result: &[("id", ["x", "k::configuration::Cell(x)"])],
        cases: &[(RS, "id")],
        typed: &[],
    },
    // Listed: a key two levels deep (`crate::Ag::aa`, below the Map collection; `crate::Hjob::hpay`,
    // below a `?` and a List collection).
    Group {
        tag: "deep-a",
        arguments: &[],
        subject: &[
            ("aa", ["x", "k::configuration::Cell(x)"]),
            ("hpay", ["y", "k::configuration::Cell(y)"]),
        ],
        result: &[],
        cases: &[(S, "aa"), (S, "hpay")],
        typed: &[],
    },
    Group {
        tag: "deep-b",
        arguments: &["x"],
        subject: &[],
        result: &[
            ("aa", ["x", "k::configuration::Cell(x)"]),
            ("hpay", ["x", "k::configuration::Cell(x)"]),
        ],
        cases: &[(RS, "aa"), (RS, "hpay")],
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
    // Listed: S5.0's ruling 3, an alias in a result, at a group and at a leaf.
    Group {
        tag: "alias",
        arguments: &["x", "y"],
        subject: &[
            (
                "frame",
                ["G { a: z, .. }", "k::fragment![crate::G { a: z, .. }]"],
            ),
            ("pc", ["w", "k::configuration::Cell(w)"]),
        ],
        result: &[
            (
                "frame",
                [
                    "f @ G { a: x, b: y }",
                    "f @ k::fragment![crate::G { a: x, b: y }]",
                ],
            ),
            ("pc", ["p @ x", "k::configuration::Cell(p @ x)"]),
        ],
        cases: &[(RS, "frame"), (RS, "pc")],
        typed: &[],
    },
    // G1 and F-7 (readable and claims; `cells!` owed: its parameters for an alias of a list element are
    // not found yet, item 3b's remaining plan): an instance updated from a record the sentence matches in another cell (a List
    // leaf's element), with a `?`, group, computation (exact and with a rest) and Map child (the
    // base bound to a non-record is item 3b's stop, not generated: `outcome` admits it).
    Group {
        tag: "g1-a",
        arguments: &["x"],
        subject: &[
            ("stack", ["[me @ Acct { id: z, .. }, ..]", ""]),
            ("account", ["{ .. }", ""]),
        ],
        result: &[
            ("stack", ["[..]", ""]),
            ("account", ["{ Acct { acounter: Some(x), ..me }, .. }", ""]),
        ],
        cases: &[(RS, "account"), (S, "stack")],
        typed: &[("me", "crate::Acct"), ("z", INT)],
    },
    Group {
        tag: "g1-b",
        arguments: &["x"],
        subject: &[
            ("stack", ["[me @ Acct { id: z, .. }, ..]", ""]),
            ("account", ["{ .. }", ""]),
        ],
        result: &[
            ("stack", ["[..]", ""]),
            (
                "account",
                ["{ Acct { aframe: Ag { aa: x }, ..me }, .. }", ""],
            ),
        ],
        cases: &[(RS, "account")],
        typed: &[("me", "crate::Acct"), ("z", INT)],
    },
    Group {
        tag: "g1-c",
        arguments: &["x"],
        subject: &[
            ("stack", ["[me @ Acct { id: z, .. }, ..]", ""]),
            ("account", ["{ .. }", ""]),
        ],
        result: &[
            ("stack", ["[..]", ""]),
            ("account", ["{ Acct { aprog: [x], ..me }, .. }", ""]),
        ],
        cases: &[(RS, "account")],
        typed: &[("me", "crate::Acct"), ("z", INT)],
    },
    Group {
        tag: "g1-d",
        arguments: &["x"],
        subject: &[
            ("stack", ["[me @ Acct { id: z, .. }, ..]", ""]),
            ("account", ["{ .. }", ""]),
        ],
        result: &[
            ("stack", ["[..]", ""]),
            ("account", ["{ Acct { aprog: [x, ..], ..me }, .. }", ""]),
        ],
        cases: &[(RS, "account")],
        typed: &[("me", "crate::Acct"), ("z", INT)],
    },
    Group {
        tag: "g1-e",
        arguments: &["x"],
        subject: &[
            ("stack", ["[me @ Acct { id: z, .. }, ..]", ""]),
            ("account", ["{ .. }", ""]),
        ],
        result: &[
            ("stack", ["[..]", ""]),
            ("account", ["{ Acct { aenv: { x -> 1 }, ..me }, .. }", ""]),
        ],
        cases: &[(RS, "account")],
        typed: &[("me", "crate::Acct"), ("z", INT)],
    },
    // G1: KEVM's restore shape, a group saved in a List leaf's element written back over the
    // group's cell.
    Group {
        tag: "g1-restore",
        arguments: &["x"],
        subject: &[
            ("stack", ["[saved @ G { a: z, .. }, ..]", ""]),
            ("frame", ["_", ""]),
        ],
        result: &[
            ("stack", ["[..]", ""]),
            ("frame", ["G { a: x, ..saved }", ""]),
        ],
        cases: &[(RS, "frame"), (S, "stack")],
        typed: &[("saved", "crate::G"), ("z", INT)],
    },
    // G3: an instance record naming a `?` child and a `*` child (its `None` subject child is
    // item 3b's stop, not generated: `outcome` admits it where P5 refuses it).
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
                "",
            ],
        )],
        result: &[(
            "account",
            [
                "{ Acct { aqueue: Aqueue { ajob: [Ajob { apay: x, ..j }, ..] }, ..me }, .. }",
                "",
            ],
        )],
        cases: &[(RS, "account")],
        typed: &[("z", INT), ("j", "crate::Ajob"), ("y", INT)],
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
    // a path entry, a subject `None` on a `?` ancestor with a path entry below it (a label used by
    // another collection is item 3b's stop, not generated: `outcome` admits an update whose base
    // is a record of another constructor).
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
        typed: &[("x", "k::KItem"), ("old", "k::Term<k::builtin::List>")],
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
#[expect(clippy::too_many_lines, reason = "one sentence per form, as `sweep::build`")]
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
    // subject entry's), the subject's entry of a result's cell, whether the result writes a
    // subject's cell.
    let mut bound = group
        .arguments
        .iter()
        .map(|name| (*name).to_owned())
        .collect::<BTreeSet<_>>();
    if cells {
        bound.insert("tail".to_owned());
    }
    for (cell, text) in &subject {
        if !is_own(Side::Subject, cell) {
            bound.extend(bound_by(&read(text)));
        }
    }
    let context = Context {
        bound: bound.into_iter().collect(),
        other: (own.0 == Side::Result)
            .then(|| {
                subject
                    .iter()
                    .find(|(cell, _)| *cell == own.1)
                    .map(|(_, text)| read(text))
            })
            .flatten(),
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

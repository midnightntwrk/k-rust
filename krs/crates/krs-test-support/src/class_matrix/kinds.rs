//! The `kinds` base (S5.0g): one cell of every stack check 5's domain names (design S5 §3,
//! check 5), at the record's level, below a `?` ancestor (the optional group `opt`) and below a
//! `*` ancestor (the Map collection `account`), and the readable, claim, `cells!` and initializer
//! cases that cover every pair of the domain's dimensions (form, side, path, stack, mark) within
//! each form (the coverage ruling): each form's marks are met on every stack, and the side and
//! the path are spread over the stack × mark grid by an orthogonal array, so each of their pairs
//! with each other, with the stack and with the mark is met too.
//!
//! The configuration is one tree ([`configuration`]), from which the base's source, each cell's
//! layers and path, and each case's text and spelling are written, so the rendered sentence and
//! the oracle's reading of it come from one place (check 2's template agreement compares them).

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::sync::LazyLock;

use super::cells_oracle::build::{
    alias, bind, call, cell, entries, exact, lit, named, open, record, seq, some, splice, var, wild,
};
use super::cells_oracle::{
    Context, Entry, EntryCase, Form, Group, Layer, Notation, Order, RecordRest, Sentence, Spelling,
    Template,
};
use super::{
    Base, BaseText, Case, CaseSpec, Command, Family, ItemBuilder, OwnReason, Packaging, Side,
};

/// A cell's multiplicity.
#[derive(Clone, Copy)]
enum Mult {
    One,
    Opt,
    Many(Order),
}

/// A cell's content.
#[derive(Clone)]
enum Content {
    Comp,
    Leaf(Notation),
    Group(String, Vec<Decl>),
}

/// One declared cell.
#[derive(Clone)]
struct Decl {
    name: String,
    mult: Mult,
    content: Content,
}

fn one(name: &str, content: Content) -> Decl {
    Decl {
        name: name.to_owned(),
        mult: Mult::One,
        content,
    }
}

fn opt(name: &str, content: Content) -> Decl {
    Decl {
        name: name.to_owned(),
        mult: Mult::Opt,
        content,
    }
}

fn many(name: &str, order: Order, content: Content) -> Decl {
    Decl {
        name: name.to_owned(),
        mult: Mult::Many(order),
        content,
    }
}

fn group(head: &str, children: Vec<Decl>) -> Content {
    Content::Group(head.to_owned(), children)
}

const fn leaf(notation: Notation) -> Content {
    Content::Leaf(notation)
}

/// The cells of every stack, their names prefixed by `p` and their groups' heads by `head`:
/// the cells below the optional group `opt` (`h`) and in the Map collection's instance (`a`).
fn every(p: &str, head: &str) -> Vec<Decl> {
    let n = |suffix: &str| format!("{p}{suffix}");
    let h = |suffix: &str| format!("{head}{suffix}");
    vec![
        one(&n("prog"), Content::Comp),
        one(&n("code"), Content::Comp),
        one(&n("pc"), leaf(Notation::Plain)),
        one(&n("stack"), leaf(Notation::List)),
        one(&n("seq"), leaf(Notation::Cons)),
        one(&n("env"), leaf(Notation::Map)),
        one(&n("set"), leaf(Notation::Set)),
        one(
            &n("frame"),
            group(&h("g"), vec![one(&n("a"), leaf(Notation::Plain))]),
        ),
        opt(&n("counter"), leaf(Notation::Plain)),
        opt(&n("olist"), leaf(Notation::List)),
        opt(&n("omap"), leaf(Notation::Map)),
        opt(
            &n("ogroup"),
            group(&h("o"), vec![one(&n("oa"), leaf(Notation::Plain))]),
        ),
        one(
            &n("queue"),
            group(
                &h("queue"),
                vec![many(
                    &n("job"),
                    Order::List,
                    group(&h("job"), vec![one(&n("pay"), leaf(Notation::Plain))]),
                )],
            ),
        ),
        one(
            &n("shelf"),
            group(
                &h("shelf"),
                vec![many(
                    &n("bag"),
                    Order::Set,
                    group(&h("obj"), vec![one(&n("key"), leaf(Notation::Plain))]),
                )],
            ),
        ),
        one(
            &n("bank"),
            group(
                &h("bank"),
                vec![many(
                    &n("acct"),
                    Order::Map,
                    group(&h("acct"), vec![one(&n("id"), leaf(Notation::Plain))]),
                )],
            ),
        ),
    ]
}

/// The base's configuration, outermost cells first.
fn configuration() -> Vec<Decl> {
    let int = || leaf(Notation::Plain);
    let mut account = vec![one("id", int())];
    account.extend(every("a", "A"));
    vec![
        one("k", Content::Comp),
        one("prog", Content::Comp),
        one("aux", group("Aux", vec![one("code", Content::Comp)])),
        one("pc", int()),
        one("stack", leaf(Notation::List)),
        one("seq", leaf(Notation::Cons)),
        one("env", leaf(Notation::Map)),
        one("set", leaf(Notation::Set)),
        one("frame", group("G", vec![one("a", int()), one("b", int())])),
        opt("counter", int()),
        opt("olist", leaf(Notation::List)),
        opt("omap", leaf(Notation::Map)),
        opt("ogroup", group("O", vec![one("oa", int())])),
        opt("opt", group("H", every("h", "H"))),
        one(
            "queue",
            group(
                "Queue",
                vec![many(
                    "job",
                    Order::List,
                    group("Job", vec![one("payload", int())]),
                )],
            ),
        ),
        one(
            "shelf",
            group(
                "Shelf",
                vec![many(
                    "bag",
                    Order::Set,
                    group("Obj", vec![one("key", int())]),
                )],
            ),
        ),
        one(
            "bank",
            group(
                "Bank",
                vec![many("account", Order::Map, group("Acct", account))],
            ),
        ),
    ]
}

static CONFIGURATION: LazyLock<Vec<Decl>> = LazyLock::new(configuration);

/// Whether `decl` is a plain group whose only child is a collection or the second computation:
/// the base's sentences name it only on the way to that child, so it is no cell of its own.
fn wrapper(decl: &Decl) -> bool {
    matches!(
        (&decl.mult, &decl.content),
        (Mult::One, Content::Group(head, _)) if head == "Aux" || head.ends_with("ueue")
            || head.ends_with("helf") || head.ends_with("ank")
    )
}

fn content_layer(content: &Content) -> Layer {
    match content {
        Content::Comp => Layer::Computation,
        Content::Leaf(notation) => Layer::Leaf(*notation),
        Content::Group(head, children) => Layer::Group(Group {
            name: head.clone(),
            children: children
                .iter()
                .map(|child| (child.name.clone(), own(child)))
                .collect(),
        }),
    }
}

/// A cell's own layers (P1).
fn own(decl: &Decl) -> Vec<Layer> {
    let mut layers = Vec::with_capacity(2);
    match decl.mult {
        Mult::One => {}
        Mult::Opt => layers.push(Layer::Optional),
        Mult::Many(order) => layers.push(Layer::Instances(order)),
    }
    layers.push(content_layer(&decl.content));
    layers
}

/// The cell `name`, the layers its marked ancestors put above it (`CellKind::path`), and its
/// parent's head (the `cells!` key's type).
fn find(name: &str) -> Option<(&'static Decl, Vec<Layer>, Option<&'static str>)> {
    fn search(
        decls: &'static [Decl],
        name: &str,
        path: &mut Vec<Layer>,
        parent: Option<&'static str>,
    ) -> Option<(&'static Decl, Vec<Layer>, Option<&'static str>)> {
        for decl in decls {
            if decl.name == name {
                return Some((decl, path.clone(), parent));
            }
            if let Content::Group(head, children) = &decl.content {
                let marked = match decl.mult {
                    Mult::One => None,
                    Mult::Opt => Some(Layer::Optional),
                    Mult::Many(order) => Some(Layer::Instances(order)),
                };
                let pushed = marked.is_some();
                path.extend(marked);
                if let Some(found) = search(children, name, path, Some(head)) {
                    return Some(found);
                }
                if pushed {
                    path.pop();
                }
            }
        }
        None
    }
    search(&CONFIGURATION, name, &mut Vec::new(), None)
}

fn decl(name: &str) -> &'static Decl {
    find(name)
        .unwrap_or_else(|| panic!("the kinds base has no cell `{name}`"))
        .0
}

/// Whether the kinds base declares `cell` as a cell of its own ([`super::entry_cases::declares`]).
#[must_use]
pub fn declares(cell: &str) -> bool {
    find(cell).is_some_and(|(decl, ..)| !wrapper(decl))
}

/// The kinds base's cell `cell`'s own layers.
///
/// # Panics
///
/// Panics if the base declares no cell `cell`.
#[must_use]
pub fn stack(cell: &str) -> Vec<Layer> {
    own(decl(cell))
}

fn type_name(decl: &Decl) -> String {
    let content = match &decl.content {
        Content::Comp => "KSequence".to_owned(),
        Content::Leaf(Notation::Plain) => "Int".to_owned(),
        Content::Leaf(Notation::List) => "List".to_owned(),
        Content::Leaf(Notation::Cons) => "Ints".to_owned(),
        Content::Leaf(Notation::Map) => "Map".to_owned(),
        Content::Leaf(Notation::Set) => "Set".to_owned(),
        Content::Group(head, _) => head.clone(),
    };
    match decl.mult {
        Mult::Opt => format!("Option<{content}>"),
        _ => content,
    }
}

fn attribute(decl: &Decl) -> String {
    let nested = matches!(decl.content, Content::Group(..));
    let mut parts = Vec::new();
    match decl.mult {
        Mult::One => {}
        Mult::Opt => parts.push("multiplicity = \"?\"".to_owned()),
        Mult::Many(order) => {
            parts.push("multiplicity = \"*\"".to_owned());
            parts.push(format!(
                "cell_type = \"{}\"",
                match order {
                    Order::List => "List",
                    Order::Set => "Set",
                    Order::Map => "Map",
                }
            ));
        }
    }
    if nested {
        parts.push("nested".to_owned());
    }
    if parts.is_empty() {
        "#[k::cell]".to_owned()
    } else {
        format!("#[k::cell({})]", parts.join(", "))
    }
}

fn structs(decls: &[Decl], out: &mut String) {
    for decl in decls {
        if let Content::Group(head, children) = &decl.content {
            let _ = write!(out, "#[k::cell]\npub struct {head} {{\n");
            for child in children {
                let _ = write!(
                    out,
                    "    {}\n    pub {}: {},\n",
                    attribute(child),
                    child.name,
                    type_name(child)
                );
            }
            out.push_str("}\n\n");
            structs(children, out);
        }
    }
}

/// A cell's base value, text and spelling: what the base's initializer writes in it (a
/// collection's, one instance's template).
fn default(decl: &Decl, top: bool) -> (String, Spelling) {
    let content = match &decl.content {
        Content::Comp if top && decl.name == "k" => {
            ("k::k![pgm]".to_owned(), kmac(vec![var("pgm")]))
        }
        Content::Comp => ("k::k![]".to_owned(), kmac(vec![])),
        Content::Leaf(Notation::Plain) => ("0".to_owned(), lit()),
        Content::Leaf(Notation::List) => ("list::empty()".to_owned(), call(vec![])),
        Content::Leaf(Notation::Cons) => ("IntList::IntsEmpty()".to_owned(), call(vec![])),
        Content::Leaf(Notation::Map) => (
            "k::map![]".to_owned(),
            Spelling::MapLit(entries(vec![], exact())),
        ),
        Content::Leaf(Notation::Set) => ("set::empty()".to_owned(), call(vec![])),
        Content::Group(head, children) => {
            let fields = children
                .iter()
                .map(|child| (child.name.clone(), default(child, false)))
                .collect::<Vec<_>>();
            let text = fields
                .iter()
                .map(|(name, (text, _))| format!("{name}: {text}"))
                .collect::<Vec<_>>()
                .join(", ");
            (
                format!("{head} {{ {text} }}"),
                Spelling::Record(record(
                    head,
                    fields
                        .iter()
                        .map(|(name, (_, spelling))| (name.as_str(), spelling.clone()))
                        .collect(),
                    RecordRest::Exact,
                )),
            )
        }
    };
    match decl.mult {
        Mult::Opt => (
            format!("k::absent!({})", content.0),
            Spelling::Absent(Box::new(content.1)),
        ),
        _ => content,
    }
}

fn kmac(items: Vec<Spelling>) -> Spelling {
    Spelling::KMacro(seq(items, exact()))
}

/// The base's initializer fields: each top-level cell's value, with `value` (text) in `cell`'s
/// place, a collection's or the second computation's written inside its parent.
fn initializer_fields(cell: Option<(&str, &str)>, item: &mut ItemBuilder) {
    for decl in CONFIGURATION.iter() {
        item.push("            ");
        let replaced = |name: &str| cell.filter(|(at, _)| *at == name).map(|(_, value)| value);
        match &decl.content {
            Content::Group(head, children) if wrapper(decl) => {
                let child = &children[0];
                item.push(&format!("{}: {head} {{ ", decl.name));
                if let Some(value) = replaced(&child.name) {
                    item.entry(&child.name, value);
                } else {
                    item.push(&format!("{}: {}", child.name, default(child, false).0));
                }
                item.push(" }");
            }
            _ => {
                if let Some(value) = replaced(&decl.name) {
                    item.entry(&decl.name, value);
                } else {
                    item.push(&format!("{}: {}", decl.name, default(decl, true).0));
                }
            }
        }
        item.push(",\n");
    }
}

const HEADER: &str = "impl Machine {\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {\n        Self {\n";
const FOOTER: &str = "        }\n    }\n}\n";

const BEFORE_COMMANDS: &str = r#"use k::KResult;
use k::builtin::{Int, KSequence, List, Map, Set, list, set};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
    Ints: k::KItem;
}

/// A cons list of `Int`s, the cons leaf's sort.
#[k::constructors(sort = Ints, result = KResult)]
#[k::cons_list]
#[k::precedence((IntsEmpty, IntsCons))]
#[rustfmt::skip]
pub enum IntList {
    #[k::syntax(".Ints")] IntsEmpty(),
    #[k::syntax("{head} : {tail}")] IntsCons { head: Int, tail: Ints },
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
"#;

static AFTER_COMMANDS: LazyLock<String> = LazyLock::new(|| {
    let mut out = String::from("}\n\n");
    structs(&CONFIGURATION, &mut out);
    out.push_str("#[k::configuration]\npub struct Machine {\n");
    for decl in CONFIGURATION.iter() {
        let _ = write!(
            out,
            "    {}\n    pub {}: {},\n",
            attribute(decl),
            decl.name,
            type_name(decl)
        );
    }
    out.push_str("}\n\n");
    out
});

static INITIALIZER: LazyLock<String> = LazyLock::new(|| {
    let mut item = ItemBuilder::new();
    item.push(HEADER);
    initializer_fields(None, &mut item);
    item.push(FOOTER);
    item.text
});

pub(super) fn base() -> BaseText {
    BaseText {
        before_commands: BEFORE_COMMANDS,
        after_commands: AFTER_COMMANDS.as_str(),
        initializer: INITIALIZER.as_str(),
        after_initializer: "",
    }
}

/// The cell of each of check 5's stacks, at the record's level, below `?` and below `*`.
const CELLS: [[&str; 3]; 15] = [
    ["prog", "hprog", "aprog"],
    ["pc", "hpc", "apc"],
    ["stack", "hstack", "astack"],
    ["seq", "hseq", "aseq"],
    ["env", "henv", "aenv"],
    ["set", "hset", "aset"],
    ["frame", "hframe", "aframe"],
    ["counter", "hcounter", "acounter"],
    ["olist", "holist", "aolist"],
    ["omap", "homap", "aomap"],
    ["ogroup", "hogroup", "aogroup"],
    ["job", "hjob", "ajob"],
    ["bag", "hbag", "abag"],
    ["account", "hacct", "aacct"],
    ["code", "hcode", "acode"],
];

/// A rule case's side: a subject the result leaves, a result over the cell the subject
/// matches, and one over a cell it does not (Q1's overwrite).
#[derive(Clone, Copy, Eq, PartialEq)]
enum RuleSide {
    Subject,
    Result,
    Overwrite,
}

impl RuleSide {
    const ALL: [Self; 3] = [Self::Subject, Self::Result, Self::Overwrite];

    const fn name(self) -> &'static str {
        match self {
            Self::Subject => "subject",
            Self::Result => "result",
            Self::Overwrite => "overwrite",
        }
    }
}

/// The record head and first child a record spelling on `decl` writes: its own group's, else
/// the top-level group `G`'s.
fn head(decl: &Decl) -> (String, String) {
    match &decl.content {
        Content::Group(head, children) => (head.clone(), children[0].name.clone()),
        _ => ("G".to_owned(), "a".to_owned()),
    }
}

/// A spelling: its text, its reading, and the `cells!` parameters its binders need.
struct Written {
    text: String,
    spelling: Spelling,
    binders: Vec<(&'static str, String)>,
}

fn written(text: impl Into<String>, spelling: Spelling) -> Written {
    Written {
        text: text.into(),
        spelling,
        binders: Vec::new(),
    }
}

const INT: &str = "k::Term<k::builtin::Int>";
const ITEM: &str = "k::KItem";

/// The type of a binder that is `decl`'s whole content (below presence).
fn whole(decl: &Decl) -> String {
    match &decl.content {
        Content::Leaf(Notation::Plain) => INT.to_owned(),
        Content::Leaf(Notation::List) => "k::Term<k::builtin::List>".to_owned(),
        Content::Leaf(Notation::Map) => "k::Term<k::builtin::Map>".to_owned(),
        Content::Leaf(Notation::Set) => "k::Term<k::builtin::Set>".to_owned(),
        Content::Group(head, _) => format!("crate::{head}"),
        _ => ITEM.to_owned(),
    }
}

/// The readable (and claim) spelling of `mark` on `decl`.
fn readable_mark(mark: &str, decl: &Decl) -> Written {
    let (h, f) = head(decl);
    let rec_x = || Spelling::Record(record(&h, vec![(f.as_str(), bind("x"))], RecordRest::Open));
    match mark {
        "presence:some" => written("Some(x)", some(bind("x"))),
        "presence:none" => written("None", Spelling::Missing),
        "seq" => written("[x, ..]", Spelling::Brackets(seq(vec![bind("x")], open()))),
        "setinst" => written(
            format!("{{ {h} {{ {f}: x, .. }}, .. }}"),
            Spelling::Braces(seq(vec![rec_x()], open())),
        ),
        "map" => written(
            "{ y -> x, .. }",
            Spelling::MapRead(entries(vec![(bind("y"), bind("x"))], open())),
        ),
        "value:binder" => written("x", bind("x")),
        "value:_" => written("_", wild()),
        "value:literal" => written("0", lit()),
        "value:record" => written(format!("{h} {{ {f}: x, .. }}"), rec_x()),
        other => panic!("no readable mark {other}"),
    }
}

/// The `cells!` spelling of `mark` on `decl` on `side`, with its subject binders' types.
fn cells_mark(mark: &str, decl: &Decl, side: RuleSide) -> Written {
    let (h, f) = head(decl);
    let fragment =
        || Spelling::Fragment(record(&h, vec![(f.as_str(), bind("x"))], RecordRest::Open));
    let fragment_text = format!("k::fragment![crate::{h} {{ {f}: x, .. }}]");
    let leaf_type = || match &decl.content {
        Content::Leaf(Notation::Cons) | Content::Comp | Content::Group(..) => ITEM.to_owned(),
        Content::Leaf(_) => whole(decl),
    };
    let (text, spelling, binder) = match mark {
        "presence:some" => (
            "Some(k::configuration::Cell(x))".to_owned(),
            some(cell(bind("x"))),
            Some(leaf_type()),
        ),
        "presence:none" => ("None".to_owned(), Spelling::Missing, None),
        "leaf" => (
            "k::configuration::Cell(x)".to_owned(),
            cell(bind("x")),
            Some(leaf_type()),
        ),
        "comp" if side == RuleSide::Subject => (
            "k::configuration::KCell(x, ..)".to_owned(),
            Spelling::KCell(seq(vec![bind("x")], open())),
            Some(ITEM.to_owned()),
        ),
        "comp" => (
            "k::configuration::KCell(x)".to_owned(),
            Spelling::KCell(seq(vec![bind("x")], exact())),
            None,
        ),
        "listinst" => (
            format!("[{fragment_text}, ..]"),
            Spelling::InstList(seq(vec![fragment()], open())),
            Some(INT.to_owned()),
        ),
        "setinst" => (
            format!("{{ {fragment_text}, .. }}"),
            Spelling::InstSet(seq(vec![fragment()], open())),
            Some(INT.to_owned()),
        ),
        "value:binder" => (
            "x".to_owned(),
            bind("x"),
            Some(match decl.mult {
                Mult::Many(_) => {
                    let (head, _) = head(decl);
                    format!("crate::{head}")
                }
                _ => whole(decl),
            }),
        ),
        "value:_" => ("_".to_owned(), wild(), None),
        "value:fragment" => (fragment_text, fragment(), Some(INT.to_owned())),
        other => panic!("no cells! mark {other}"),
    };
    Written {
        text,
        spelling,
        binders: match (side, binder) {
            (RuleSide::Subject, Some(ty)) => vec![("x", ty)],
            _ => Vec::new(),
        },
    }
}

/// The initializer value of `mark` on `decl`.
fn init_mark(mark: &str, decl: &Decl) -> Written {
    let inner = || match decl.mult {
        Mult::Opt => {
            let mut plain = decl.clone();
            plain.mult = Mult::One;
            default(&plain, false)
        }
        _ => ("0".to_owned(), lit()),
    };
    let record_of = || match (&decl.content, decl.mult) {
        (Content::Group(..), _) => {
            let mut plain = decl.clone();
            plain.mult = Mult::One;
            default(&plain, false)
        }
        _ => (
            "G { a: 0, b: 0 }".to_owned(),
            Spelling::Record(record(
                "G",
                vec![("a", lit()), ("b", lit())],
                RecordRest::Exact,
            )),
        ),
    };
    match mark {
        "presence:some" => {
            let (text, spelling) = inner();
            written(format!("Some({text})"), some(spelling))
        }
        "presence:absent" => {
            let (text, spelling) = inner();
            written(
                format!("k::absent!({text})"),
                Spelling::Absent(Box::new(spelling)),
            )
        }
        "presence:none" => written("None", Spelling::Missing),
        "comp" => written("k::k![pgm]", kmac(vec![var("pgm")])),
        "seq" => written("[0]", Spelling::Brackets(seq(vec![lit()], exact()))),
        "map" => written(
            "k::map![0 -> 1]",
            Spelling::MapLit(entries(vec![(lit(), lit())], exact())),
        ),
        "value:literal" => written("0", lit()),
        "value:record" => {
            let (text, spelling) = record_of();
            written(text, spelling)
        }
        "value:call" => written("Cmd::Go()", call(vec![])),
        "value:cfgvar" => written("pgm", var("pgm")),
        other => panic!("no initializer mark {other}"),
    }
}

/// What a matched result's subject writes in the cell: the cell's content bound whole, or
/// matched from its front with an anonymous rest, in the form's spelling.
fn other(form: Form, decl: &Decl) -> Written {
    let cells = form == Form::Cells;
    let (h, f) = head(decl);
    match (decl.mult, &decl.content) {
        (Mult::Many(Order::List), _) if cells => Written {
            text: format!("[old @ k::fragment![crate::{h} {{ {f}: _, .. }}], instances0 @ ..]"),
            spelling: Spelling::InstList(seq(
                vec![alias(
                    "old",
                    Spelling::Fragment(record(&h, vec![(f.as_str(), wild())], RecordRest::Open)),
                )],
                named("instances0"),
            )),
            binders: Vec::new(),
        },
        (Mult::Many(_), _) if cells => written(
            "{ instances0 @ .. }",
            Spelling::InstSet(seq(vec![], named("instances0"))),
        ),
        (Mult::Many(Order::List), _) => written(
            format!("[{h} {{ {f}: _, .. }}, ..]"),
            Spelling::Brackets(seq(
                vec![Spelling::Record(record(
                    &h,
                    vec![(f.as_str(), wild())],
                    RecordRest::Open,
                ))],
                open(),
            )),
        ),
        (Mult::Many(_), _) => written("{ .. }", Spelling::Braces(seq(vec![], open()))),
        (_, Content::Comp) if cells => Written {
            text: "k::configuration::KCell(old, ..)".to_owned(),
            spelling: Spelling::KCell(seq(vec![bind("old")], open())),
            binders: vec![("old", ITEM.to_owned())],
        },
        (_, Content::Comp) => written(
            "[old, ..]",
            Spelling::Brackets(seq(vec![bind("old")], open())),
        ),
        (Mult::Opt, Content::Leaf(_)) if cells => Written {
            text: "Some(k::configuration::Cell(old))".to_owned(),
            spelling: some(cell(bind("old"))),
            binders: vec![("old", whole(decl).replace("crate::Ints", ITEM))],
        },
        (Mult::Opt, _) => Written {
            text: "Some(old)".to_owned(),
            spelling: some(bind("old")),
            binders: vec![("old", whole(decl))],
        },
        (_, Content::Leaf(notation)) if cells => Written {
            text: "k::configuration::Cell(old)".to_owned(),
            spelling: cell(bind("old")),
            binders: vec![(
                "old",
                if *notation == Notation::Cons {
                    ITEM.to_owned()
                } else {
                    whole(decl)
                },
            )],
        },
        _ => Written {
            text: "old".to_owned(),
            spelling: bind("old"),
            binders: vec![("old", whole(decl))],
        },
    }
}

/// The names a result case's subject and command bind.
const BOUND: [&str; 4] = ["x", "y", "old", "instances0"];

fn entry(cell: &str, side: Side, spelling: Spelling) -> Entry {
    let (decl, path, _) = find(cell).unwrap_or_else(|| panic!("no kinds cell `{cell}`"));
    Entry {
        cell: cell.to_owned(),
        side,
        path,
        stack: own(decl),
        spelling,
    }
}

/// The `cells!` key of `cell`: a top-level cell by its name, a nested one through its parent's
/// type.
fn key(cell: &str) -> String {
    match find(cell) {
        Some((_, _, Some(parent))) => format!("crate::{parent}::{cell}"),
        _ => cell.to_owned(),
    }
}

/// One generated case and its reading.
pub(super) struct Generated {
    pub(super) case: Case,
    pub(super) entry: EntryCase,
}

fn readable_case(family: Family, side: RuleSide, cell_name: &str, mark: &Written) -> Generated {
    let (form, sentence) = if family == Family::Claim {
        (Form::Claim, Sentence::Claim)
    } else {
        (Form::Readable, Sentence::Rule)
    };
    let decl = decl(cell_name);
    let spec = CaseSpec {
        family,
        base: Base::Kinds,
        side: if side == RuleSide::Subject {
            Side::Subject
        } else {
            Side::Result
        },
        kind: None,
        slot: vec![
            side.name().to_owned(),
            "kinds".to_owned(),
            cell_name.to_owned(),
        ],
        construct: mark.text.clone(),
    };
    let arity = if side == RuleSide::Subject { 0 } else { 2 };
    let command = Command::for_case(&spec.id(), arity);
    let label = format!("case_{}", spec.tag());
    let (block, attribute) = match family {
        Family::Claim => ("k::claims!", "    #[k::claim(all_paths)]\n"),
        _ => ("k::rules!", ""),
    };
    let mut item = ItemBuilder::new();
    item.push(block)
        .push(" {\n    for Machine;\n    use Cmd::*;\n\n")
        .push(attribute)
        .push("    ")
        .push(&label)
        .push(": { ");
    let mut entries = Vec::new();
    let mut context = Context::default();
    let k_subject = |arguments| {
        entry(
            "k",
            Side::Subject,
            Spelling::Brackets(seq(vec![call(arguments)], open())),
        )
    };
    let k_result = || entry("k", Side::Result, Spelling::Brackets(seq(vec![], open())));
    match side {
        RuleSide::Subject => {
            item.push(&format!("k: [{}(), ..], ", command.name))
                .entry(cell_name, &mark.text)
                .push(" } => { k: [..] };\n}\n");
            entries.push(k_subject(vec![]));
            entries.push(k_result());
        }
        RuleSide::Result | RuleSide::Overwrite => {
            item.push(&format!("k: [{}(x, y), ..], ", command.name));
            entries.push(k_subject(vec![bind("x"), bind("y")]));
            context.bound = BOUND.map(str::to_owned).to_vec();
            if side == RuleSide::Result {
                let subject = other(form, decl);
                item.push(&format!("{cell_name}: {}, ", subject.text));
                entries.push(entry(cell_name, Side::Subject, subject.spelling.clone()));
                context.other = Some(subject.spelling);
            }
            item.push("} => { k: [..], ")
                .entry(cell_name, &mark.text)
                .push(" };\n}\n");
            entries.push(k_result());
        }
    }
    let case = spec.finish(Packaging::Shared(command), &item);
    Generated {
        case,
        entry: EntryCase {
            form,
            entry: entry(
                cell_name,
                if side == RuleSide::Subject {
                    Side::Subject
                } else {
                    Side::Result
                },
                mark.spelling.clone(),
            ),
            context,
            template: Template {
                sentence,
                entries,
                guard: false,
                variables: Vec::new(),
            },
        },
    }
}

fn cells_case(side: RuleSide, cell_name: &str, mark: &Written) -> Generated {
    let decl = decl(cell_name);
    let entry_side = if side == RuleSide::Subject {
        Side::Subject
    } else {
        Side::Result
    };
    let spec = CaseSpec {
        family: Family::Cells,
        base: Base::Kinds,
        side: entry_side,
        kind: None,
        slot: vec![
            side.name().to_owned(),
            "kinds".to_owned(),
            cell_name.to_owned(),
        ],
        construct: mark.text.clone(),
    };
    let tag = spec.tag();
    let arity = if side == RuleSide::Subject { 0 } else { 2 };
    let command = Command::for_case(&spec.id(), arity);
    let mut parameters: Vec<(&str, String)> = Vec::new();
    if side != RuleSide::Subject {
        parameters.push(("x", INT.to_owned()));
        parameters.push(("y", INT.to_owned()));
    }
    parameters.extend(mark.binders.iter().cloned());
    let subject = (side == RuleSide::Result).then(|| other(Form::Cells, decl));
    if let Some(subject) = &subject {
        parameters.extend(subject.binders.iter().cloned());
    }
    let mut item = ItemBuilder::new();
    item.push(&format!(
        "#[k::rule(label = \"case-{tag}\")]\npub fn case_{tag}(\n"
    ));
    for (name, ty) in &parameters {
        item.push(&format!("    {name}: {ty},\n"));
    }
    let key = key(cell_name);
    let tail = || Spelling::KCell(seq(vec![], splice("tail")));
    let mut entries = Vec::new();
    let mut context = Context::default();
    if side == RuleSide::Subject {
        item.push(&format!(
            "    k::cells! {{ k: k::configuration::KCell(crate::Cmd::{}(), tail @ ..), ",
            command.name
        ))
        .entry(&key, &mark.text)
        .push(concat!(
            ", state @ .. }: crate::Machine,\n",
            ") -> crate::Machine {\n",
            "    k::cells! { k: k::configuration::KCell(..tail), ..state }\n",
            "}\n",
        ));
        entries.push(entry(
            "k",
            Side::Subject,
            Spelling::KCell(seq(vec![call(vec![])], named("tail"))),
        ));
    } else {
        item.push(&format!(
            "    k::cells! {{ k: k::configuration::KCell(crate::Cmd::{}(x, y), tail @ ..), ",
            command.name
        ));
        entries.push(entry(
            "k",
            Side::Subject,
            Spelling::KCell(seq(vec![call(vec![bind("x"), bind("y")])], named("tail"))),
        ));
        context.bound = BOUND.map(str::to_owned).to_vec();
        context.bound.push("tail".to_owned());
        if let Some(subject) = subject {
            item.push(&format!("{key}: {}, ", subject.text));
            entries.push(entry(cell_name, Side::Subject, subject.spelling.clone()));
            context.other = Some(subject.spelling);
        }
        item.push(
            "state @ .. }: crate::Machine,\n) -> crate::Machine {\n    k::cells! { k: k::configuration::KCell(..tail), ",
        )
        .entry(&key, &mark.text)
        .push(", ..state }\n}\n");
    }
    entries.push(entry("k", Side::Result, tail()));
    let case = spec.finish(Packaging::Shared(command), &item);
    Generated {
        case,
        entry: EntryCase {
            form: Form::Cells,
            entry: entry(cell_name, entry_side, mark.spelling.clone()),
            context,
            template: Template {
                sentence: Sentence::Rule,
                entries,
                guard: false,
                variables: Vec::new(),
            },
        },
    }
}

fn init_case(cell_name: &str, mark: &Written) -> Generated {
    let spec = CaseSpec {
        family: Family::Init,
        base: Base::Kinds,
        side: Side::Initializer,
        kind: None,
        slot: vec!["kinds".to_owned(), cell_name.to_owned()],
        construct: mark.text.clone(),
    };
    let mut item = ItemBuilder::new();
    item.push(HEADER);
    initializer_fields(Some((cell_name, &mark.text)), &mut item);
    item.push(FOOTER);
    let case = spec.finish(Packaging::Own(OwnReason::Initializer), &item);
    let init_stack = |name: &str| {
        let mut stack = stack(name);
        if matches!(stack.first(), Some(Layer::Instances(_))) {
            stack.remove(0);
        }
        stack
    };
    let mut entries = Vec::new();
    for decl in CONFIGURATION.iter() {
        let field = match &decl.content {
            Content::Group(_, children) if wrapper(decl) => &children[0],
            _ => decl,
        };
        if field.name == cell_name {
            continue;
        }
        let top = std::ptr::eq(field, decl);
        entries.push(Entry {
            cell: field.name.clone(),
            side: Side::Initializer,
            path: Vec::new(),
            stack: init_stack(&field.name),
            spelling: default(field, top).1,
        });
    }
    Generated {
        case,
        entry: EntryCase {
            form: Form::Init,
            entry: Entry {
                cell: cell_name.to_owned(),
                side: Side::Initializer,
                path: Vec::new(),
                stack: init_stack(cell_name),
                spelling: mark.spelling.clone(),
            },
            context: Context {
                bound: vec!["pgm".to_owned()],
                other: None,
                written: false,
            },
            template: Template {
                sentence: Sentence::Initializer,
                entries,
                guard: false,
                variables: vec![("pgm".to_owned(), true)],
            },
        },
    }
}

/// The marks of each form, in check 5's order (`tests/cells_oracle.rs` `marks`).
const RULE_MARKS: [&str; 9] = [
    "presence:some",
    "presence:none",
    "seq",
    "setinst",
    "map",
    "value:binder",
    "value:_",
    "value:literal",
    "value:record",
];
const CELLS_MARKS: [&str; 9] = [
    "presence:some",
    "presence:none",
    "leaf",
    "comp",
    "listinst",
    "setinst",
    "value:binder",
    "value:_",
    "value:fragment",
];
const INIT_MARKS: [&str; 10] = [
    "presence:some",
    "presence:absent",
    "presence:none",
    "comp",
    "seq",
    "map",
    "value:literal",
    "value:record",
    "value:call",
    "value:cfgvar",
];

/// Every case of the kinds base. In each rule form, the case of stack `i` and mark `j` is on
/// side `(i + j) mod 3` and path `(i + 2j) mod 3`: for a fixed stack or mark, each side and each
/// path occurs, and `(i, j) -> (i + j, i + 2j)` takes every side × path pair (its determinant is
/// 1 mod 3), so every pair of dimensions is met. An initializer names its cell at the record's
/// level, so each stack takes each initializer mark.
fn generate() -> Vec<Generated> {
    let mut out = Vec::new();
    for family in [Family::Readable, Family::Claim, Family::Cells] {
        let marks: &[&str] = if family == Family::Cells {
            &CELLS_MARKS
        } else {
            &RULE_MARKS
        };
        for (i, cells) in CELLS.iter().enumerate() {
            for (j, mark) in marks.iter().enumerate() {
                let side = RuleSide::ALL[(i + j) % 3];
                let cell_name = cells[(i + 2 * j) % 3];
                let decl = decl(cell_name);
                out.push(if family == Family::Cells {
                    cells_case(side, cell_name, &cells_mark(mark, decl, side))
                } else {
                    readable_case(family, side, cell_name, &readable_mark(mark, decl))
                });
            }
        }
    }
    for cells in &CELLS {
        for mark in INIT_MARKS {
            out.push(init_case(cells[0], &init_mark(mark, decl(cells[0]))));
        }
    }
    out
}

static GENERATED: LazyLock<BTreeMap<String, EntryCase>> = LazyLock::new(|| {
    generate()
        .into_iter()
        .map(|generated| (generated.case.id, generated.entry))
        .collect()
});

/// The kinds base's cases.
pub(super) fn cases(cases: &mut Vec<Case>) {
    cases.extend(generate().into_iter().map(|generated| generated.case));
}

/// The reading of a kinds-base case.
///
/// # Panics
///
/// Panics if `case` is no case of the kinds base.
#[must_use]
pub fn entry_case(case: &Case) -> EntryCase {
    GENERATED
        .get(&case.id)
        .unwrap_or_else(|| panic!("{} is no kinds-base case", case.id))
        .clone()
}

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
    Template, collect_groups,
};
use super::k7::{Ground, K7, Removed, Run, SkipKind, Status};
use super::machine;
use super::{
    Base, BaseText, Case, CaseSpec, Command, Family, ItemBuilder, OwnReason, Packaging, Side,
};

mod groups;

/// A cell's multiplicity.
#[derive(Clone, Copy)]
pub(super) enum Mult {
    One,
    Opt,
    Many(Order),
}

/// A cell's content.
#[derive(Clone)]
pub(super) enum Content {
    Comp,
    Leaf(Notation),
    Group(String, Vec<Decl>),
}

/// One declared cell.
#[derive(Clone)]
pub(super) struct Decl {
    pub(super) name: String,
    pub(super) mult: Mult,
    pub(super) content: Content,
}

pub(super) fn one(name: &str, content: Content) -> Decl {
    Decl {
        name: name.to_owned(),
        mult: Mult::One,
        content,
    }
}

pub(super) fn opt(name: &str, content: Content) -> Decl {
    Decl {
        name: name.to_owned(),
        mult: Mult::Opt,
        content,
    }
}

pub(super) fn many(name: &str, order: Order, content: Content) -> Decl {
    Decl {
        name: name.to_owned(),
        mult: Mult::Many(order),
        content,
    }
}

pub(super) fn group(head: &str, children: Vec<Decl>) -> Content {
    Content::Group(head.to_owned(), children)
}

pub(super) const fn leaf(notation: Notation) -> Content {
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
pub(super) fn wrapper(decl: &Decl) -> bool {
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
pub(super) fn own(decl: &Decl) -> Vec<Layer> {
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
    find_in(&CONFIGURATION, name)
}

/// The cell `name` of the configuration `tree` ([`find`]).
pub(super) fn find_in(
    tree: &'static [Decl],
    name: &str,
) -> Option<(&'static Decl, Vec<Layer>, Option<&'static str>)> {
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
    search(tree, name, &mut Vec::new(), None)
}

/// The outermost `?` or `*` ancestor of the cell `name`, if any. A subject that matches a cell
/// below one matches it through that ancestor: an entry naming the cell itself is refused for
/// the ancestor whatever it spells (S1 (b)), so a result case's subject written there would be
/// a second refused entry, and the sentence's answer would not be the case's own (P4 over a
/// sentence).
fn marked_ancestor(name: &str) -> Option<&'static Decl> {
    fn search(decls: &'static [Decl], name: &str, ancestors: &mut Vec<&'static Decl>) -> bool {
        for decl in decls {
            if decl.name == name {
                return true;
            }
            if let Content::Group(_, children) = &decl.content {
                ancestors.push(decl);
                if search(children, name, ancestors) {
                    return true;
                }
                ancestors.pop();
            }
        }
        false
    }
    let mut ancestors = Vec::new();
    search(&CONFIGURATION, name, &mut ancestors)
        .then(|| {
            ancestors
                .into_iter()
                .find(|decl| !matches!(decl.mult, Mult::One))
        })
        .flatten()
}

/// A matched result's subject entry: the cell it names (the result's cell, or its outermost
/// marked ancestor where it has one, [`marked_ancestor`], matched whole), what it writes, its
/// entry, and the result's other side (the subject's entry of the result's own cell, if any).
fn matched(form: Form, cell: &str) -> (&'static str, Written, Entry, Option<Spelling>) {
    let matched = marked_ancestor(cell).unwrap_or_else(|| decl(cell));
    let subject = other(form, matched);
    let entry = entry(&matched.name, Side::Subject, subject.spelling.clone());
    let own = (matched.name == cell).then(|| subject.spelling.clone());
    (&matched.name, subject, entry, own)
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

/// The kinds base's groups, at any depth ([`super::cells_oracle::Context::groups`]).
#[must_use]
pub fn groups() -> Vec<Group> {
    let mut groups = Vec::new();
    for decl in CONFIGURATION.iter() {
        collect_groups(&own(decl), &mut groups);
    }
    groups
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

pub(super) fn type_name(decl: &Decl) -> String {
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

pub(super) fn attribute(decl: &Decl) -> String {
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

pub(super) fn structs(decls: &[Decl], out: &mut String) {
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
pub(super) fn default(decl: &Decl, top: bool) -> (String, Spelling) {
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
    initializer_fields_in(&CONFIGURATION, cell, item);
}

/// [`initializer_fields`] over the configuration `tree`.
pub(super) fn initializer_fields_in(
    tree: &[Decl],
    cell: Option<(&str, &str)>,
    item: &mut ItemBuilder,
) {
    for decl in tree {
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

pub(super) const HEADER: &str = "impl Machine {\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {\n        Self {\n";
pub(super) const FOOTER: &str = "        }\n    }\n}\n";

pub(super) const BEFORE_COMMANDS: &str = r#"use k::KResult;
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
    /// A subject whose rule writes no cell (`=> { }`).
    NoChange,
    /// A subject that also names the first child of the cell's group.
    Descendant,
}

impl RuleSide {
    const ALL: [Self; 3] = [Self::Subject, Self::Result, Self::Overwrite];

    /// The side of the case's own entry.
    const fn entry_side(self) -> Side {
        match self {
            Self::Result | Self::Overwrite => Side::Result,
            _ => Side::Subject,
        }
    }

    const fn name(self) -> &'static str {
        match self {
            Self::Subject => "subject",
            Self::Result => "result",
            Self::Overwrite => "overwrite",
            Self::NoChange => "nochange",
            Self::Descendant => "descendant",
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

pub(super) const INT: &str = "k::Term<k::builtin::Int>";
pub(super) const ITEM: &str = "k::KItem";

/// The type of a binder that is `decl`'s whole content (below presence).
pub(super) fn whole(decl: &Decl) -> String {
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
        side: side.entry_side(),
        kind: None,
        slot: vec![
            side.name().to_owned(),
            "kinds".to_owned(),
            cell_name.to_owned(),
        ],
        construct: mark.text.clone(),
    };
    let arity = if side.entry_side() == Side::Subject {
        0
    } else {
        2
    };
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
        RuleSide::NoChange => {
            item.push(&format!("k: [{}(), ..], ", command.name))
                .entry(cell_name, &mark.text)
                .push(" } => { };\n}\n");
            entries.push(k_subject(vec![]));
        }
        RuleSide::Descendant => {
            let (_, child) = head(decl);
            item.push(&format!("k: [{}(), ..], ", command.name))
                .entry(cell_name, &mark.text)
                .push(&format!(", {child}: y }} => {{ k: [..] }};\n}}\n"));
            entries.push(k_subject(vec![]));
            entries.push(entry(&child, Side::Subject, bind("y")));
            entries.push(k_result());
        }
        RuleSide::Result | RuleSide::Overwrite => {
            item.push(&format!("k: [{}(x, y), ..], ", command.name));
            entries.push(k_subject(vec![bind("x"), bind("y")]));
            context.bound = BOUND.map(str::to_owned).to_vec();
            if side == RuleSide::Result {
                let (name, subject, written, other) = matched(form, cell_name);
                item.push(&format!("{name}: {}, ", subject.text));
                entries.push(written);
                context.other = other;
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
            entry: entry(cell_name, side.entry_side(), mark.spelling.clone()),
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
    let subject = (side == RuleSide::Result).then(|| matched(Form::Cells, cell_name));
    if let Some((_, subject, ..)) = &subject {
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
        if let Some((name, subject, written, other)) = subject {
            item.push(&format!("{}: {}, ", self::key(name), subject.text));
            entries.push(written);
            context.other = other;
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
    let mut generated = Generated {
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
                records: Vec::new(),
                other: None,
                written: false,
                groups: Vec::new(),
            },
            template: Template {
                sentence: Sentence::Initializer,
                entries,
                guard: false,
                variables: vec![("pgm".to_owned(), true)],
            },
        },
    };
    // An initializer needs no driver: K7 reads it before any step, so its plan is the value
    // each cell's initializer denotes, written as K7's grounds.
    let entry_outcome = generated.entry.outcome();
    let refused = !entry_outcome.admits() || generated.entry.rule_outcome(entry_outcome).is_some();
    let (plan, removed) = init_plan(cell_name, &mark.text, refused);
    generated.case.k7 = plan;
    if let Some(removed) = removed {
        generated.case.removed = removed;
    }
    generated
}

/// What the kinds base's cells hold when an initializer case's run starts, by K7 path: every
/// cell the base's own initializer writes, with the value it denotes and the program `go` in
/// `k`. Each optional cell is written `k::absent!(..)`, so it starts absent (decision NT-12-6);
/// an optional group's absence (`ogroup`, `opt`) is not read, since K7's reader reads a cell by
/// a leaf's path, and a present one is read at its child (`ogroup.oa`);
/// each collection's initializer writes one instance's template, so it starts with no instance
/// (K7's reader reads a Map collection's instances as a set, by their children's values).
fn kinds_cells() -> Vec<(&'static str, Ground)> {
    let go = || Ground::ctor("Cmd::Go", Vec::new());
    vec![
        ("k", Ground::Seq(vec![go()])),
        ("prog", Ground::Seq(Vec::new())),
        ("aux.code", Ground::Seq(Vec::new())),
        ("pc", Ground::Int(0)),
        ("stack", Ground::List(Vec::new())),
        ("seq", Ground::ctor("IntList::IntsEmpty", Vec::new())),
        ("env", Ground::map(Vec::new())),
        ("set", Ground::Set(Vec::new())),
        ("frame.a", Ground::Int(0)),
        ("frame.b", Ground::Int(0)),
        ("counter", Ground::Absent),
        ("olist", Ground::Absent),
        ("omap", Ground::Absent),
        ("queue.job[payload]", Ground::List(Vec::new())),
        ("shelf.bag{key}", Ground::Set(Vec::new())),
        ("bank.account{id}", Ground::Set(Vec::new())),
    ]
}

/// The K7 path of the kinds base's top-level cell `cell` an initializer case writes.
fn kinds_path(cell: &str) -> &'static str {
    match cell {
        "code" => "aux.code",
        "job" => "queue.job[payload]",
        "bag" => "shelf.bag{key}",
        "account" => "bank.account{id}",
        // A group's children are read below its path.
        "frame" => "frame",
        "ogroup" => "ogroup",
        other => kinds_cells()
            .into_iter()
            .map(|(path, _)| path)
            .find(|path| *path == other)
            .unwrap_or_else(|| panic!("no kinds cell path `{other}`")),
    }
}

/// What `value` gives the kinds base's cell `cell` when the run starts with the program `go`,
/// by K7 path, or `None` where the generator states nothing (the cell is then unread). A
/// computation holds `pgm` (`go`) or `0` as its one item; a List leaf's `[0]` is that list; the
/// cons leaf's `[0]` is `0 : .Ints`; an optional cell's `Some(v)` holds `v` (the group's, at its
/// child) and its `k::absent!(..)` is absent; a group's exact record holds its fields.
fn kinds_value(cell: &str, value: &str) -> Option<Vec<(&'static str, Ground)>> {
    let go = || Ground::ctor("Cmd::Go", Vec::new());
    let path = kinds_path(cell);
    let one = |ground| Some(vec![(path, ground)]);
    match (cell, value) {
        ("prog" | "code", "k::k![pgm]" | "pgm" | "[pgm]") => one(Ground::Seq(vec![go()])),
        ("prog" | "code", "k::k![0]" | "0" | "[0]") => one(Ground::Seq(vec![Ground::Int(0)])),
        ("pc", "0") | ("counter", "Some(0)") => one(Ground::Int(0)),
        ("stack", "[0]") => one(Ground::List(vec![Ground::Int(0)])),
        ("seq", "[0]") => one(Ground::ctor(
            "IntList::IntsCons",
            vec![
                Ground::Int(0),
                Ground::ctor("IntList::IntsEmpty", Vec::new()),
            ],
        )),
        ("env", "k::map![0 -> 1]") => one(Ground::map(vec![(Ground::Int(0), Ground::Int(1))])),
        ("frame", "G { a: 0, b: 0 }") => Some(vec![
            ("frame.a", Ground::Int(0)),
            ("frame.b", Ground::Int(0)),
        ]),
        ("olist", "Some(list::empty())") => one(Ground::List(Vec::new())),
        ("omap", "Some(k::map![])") => one(Ground::map(Vec::new())),
        ("ogroup", "Some(O { oa: 0 })") => Some(vec![("ogroup.oa", Ground::Int(0))]),
        ("counter" | "olist" | "omap", _) if value.starts_with("k::absent!(") => {
            one(Ground::Absent)
        }
        // An absent optional group is not read ([`kinds_cells`]): the base's reading stands.
        ("ogroup", _) if value.starts_with("k::absent!(") => Some(Vec::new()),
        _ => None,
    }
}

/// Why a kinds collection's initializer case reads nothing of its spelling.
pub(super) const KINDS_TEMPLATE_UNREAD: &str = "a collection's initializer writes one instance's template, and the collection starts with no instance: the kinds base has no driver command that creates one, so no run reads the template";

/// K7's plan for the kinds base's initializer case of `cell` written `value`, and what its
/// dependency check states where the run without it is the same: a value `outcome` refuses is
/// refused at K2 and has no run; otherwise the run starts with `go`, takes no step, and the
/// cells hold the base's values ([`kinds_cells`]) with the case's in place of its cell's, the
/// cell left unread (liveness) where the generator states no value. A collection's case reads
/// none of its template ([`KINDS_TEMPLATE_UNREAD`]).
fn init_plan(cell: &str, value: &str, refused: bool) -> (K7, Option<Removed>) {
    if refused {
        return (K7::skip(SkipKind::Value, machine::REFUSED_AT_K2), None);
    }
    let base = || {
        K7::Run(Run {
            program: "go".to_owned(),
            variables: Vec::new(),
            depth: 0,
            steps: 0,
            cells: kinds_cells()
                .into_iter()
                .map(|(path, ground)| (path.to_owned(), ground))
                .collect(),
            status: Status::Value,
            forward_only: Vec::new(),
            applies: true,
        })
    };
    let path = kinds_path(cell);
    let collection = matches!(cell, "job" | "bag" | "account");
    let K7::Run(mut run) = base() else {
        unreachable!("the base plan is a run");
    };
    // The cell's base reading, and any reading below it, gives way to the case's.
    let owned = |at: &str| at == path || at.starts_with(&format!("{path}."));
    if collection {
        // The collection starts with no instance whatever its template: the run reads the
        // base's cells, the collection empty, as the base's own initializer states them.
        run.status = Status::Liveness;
        return (
            K7::Run(run),
            Some(Removed::Unchanged(machine::TEMPLATE_UNCHANGED)),
        );
    }
    run.cells.retain(|(at, _)| !owned(at));
    match kinds_value(cell, value) {
        Some(readings) => run.cells.extend(
            readings
                .into_iter()
                .map(|(at, ground)| (at.to_owned(), ground)),
        ),
        None => run.status = Status::Liveness,
    }
    let at_base = kinds_cells();
    let same = run.status == Status::Value
        && run.cells.len() == at_base.len()
        && at_base.iter().all(|(path, ground)| {
            run.cells
                .iter()
                .any(|(at, read)| at == path && read == ground)
        });
    (
        K7::Run(run),
        same.then_some(Removed::Unchanged(machine::BASE_VALUE)),
    )
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
    out.extend(listed());
    out
}

/// The cases the ticket lists beside the array: a rule that writes no cell
/// (`rule-changes-no-cell`), a rule naming a group and a cell below it (`group-and-descendant`),
/// L4's 2-child group record written whole, `Some(_)` in a result, and a `cells!` result
/// fragment whose bare `..` leaves `b` open over a matched group. L4's record naming one of the two children
/// is written in both forms, readable `G { a: x }` and its `cells!` fragment (D-4).
fn listed() -> Vec<Generated> {
    let frame = decl("frame");
    let g = |fields: Vec<(&str, Spelling)>, text: &str, rest| {
        written(text, Spelling::Record(record("G", fields, rest)))
    };
    let mut out = Vec::new();
    for family in [Family::Readable, Family::Claim] {
        out.push(readable_case(
            family,
            RuleSide::Descendant,
            "frame",
            &readable_mark("value:binder", frame),
        ));
        for side in [RuleSide::Subject, RuleSide::Result] {
            out.push(readable_case(
                family,
                side,
                "frame",
                &g(
                    vec![("a", bind("x")), ("b", bind("y"))],
                    "G { a: x, b: y }",
                    RecordRest::Exact,
                ),
            ));
            out.push(readable_case(
                family,
                side,
                "frame",
                &g(vec![("a", bind("x"))], "G { a: x }", RecordRest::Exact),
            ));
        }
        out.push(readable_case(
            family,
            RuleSide::Result,
            "counter",
            &written("Some(_)", some(wild())),
        ));
    }
    out.push(readable_case(
        Family::Readable,
        RuleSide::NoChange,
        "pc",
        &readable_mark("value:binder", decl("pc")),
    ));
    out.push(cells_case(
        RuleSide::Result,
        "frame",
        &cells_mark("value:fragment", frame, RuleSide::Result),
    ));
    for side in [RuleSide::Subject, RuleSide::Result] {
        out.push(cells_case(
            side,
            "frame",
            &Written {
                text: "k::fragment![crate::G { a: x }]".to_owned(),
                spelling: Spelling::Fragment(record(
                    "G",
                    vec![("a", bind("x"))],
                    RecordRest::Exact,
                )),
                binders: if side == RuleSide::Subject {
                    vec![("x", INT.to_owned())]
                } else {
                    Vec::new()
                },
            },
        ));
    }
    out.extend(groups::cases());
    for (cell, text) in groups::INITIALIZERS {
        out.push(init_case(
            cell,
            &written(text, super::sweep::read(Form::Init, text)),
        ));
    }
    out
}

static GENERATED: LazyLock<BTreeMap<String, EntryCase>> = LazyLock::new(|| {
    generate()
        .into_iter()
        .map(|generated| (generated.case.id, generated.entry))
        .collect()
});

/// Whether `case` is one of the kinds base's groups ([`groups`]), item 3b's sentences of
/// several entries and listed single entries.
pub(super) fn of_group(case: &Case) -> bool {
    case.base == Base::Kinds
        && case
            .id
            .split('/')
            .nth(1)
            .is_some_and(|segment| groups::GROUPS.iter().any(|group| group.tag == segment))
}

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

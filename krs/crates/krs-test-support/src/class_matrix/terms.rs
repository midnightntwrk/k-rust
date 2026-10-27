//! Term positions: every shape of term at the argument positions of every sentence form.
//!
//! Each hole is a position whose sort is `KItem` (a field of `Hold`, `Pair`, a command, or the
//! functions `Probe` and `Size`), which every sort but `K` lies below, so a construct is judged
//! by whether its shape may stand there, not by its sort. A guard is the exception: the hole is
//! the whole condition, a `Bool`.
//!
//! The constructs name the command family's variants through their enum, `Cmd::Hold(x)`, which
//! resolves in every form; the import axis ([`Family::Import`]) writes them bare under a
//! module-level `use Cmd::*;` instead.

use super::{
    Base, BaseText, Case, CaseSpec, Command, Family, ItemBuilder, OwnReason, Packaging, Side,
};

const BEFORE_COMMANDS: &str = r#"use k::builtin::{Int, KSequence, List, Map, list};
use k::{KItem, KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

/// A closed token sort, for `k::lexeme!`.
#[k::token(regex = r"w[a-z]*")]
pub struct Word(pub String);

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("hold({a})")] Hold { a: KItem },
    #[k::syntax("pair({a}, {b})")] Pair { a: KItem, b: KItem },
"#;

const IMPORTED_BEFORE_COMMANDS: &str = r#"use k::builtin::{Int, KSequence, List, Map, list};
use k::{KItem, KResult, Term};

use Cmd::*;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

/// A closed token sort, for `k::lexeme!`.
#[k::token(regex = r"w[a-z]*")]
pub struct Word(pub String);

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("hold({a})")] Hold { a: KItem },
    #[k::syntax("pair({a}, {b})")] Pair { a: KItem, b: KItem },
"#;

const AFTER_COMMANDS: &str = r#"}

/// A function of two items, which the equation forms define.
#[k::function(partial, sort = Int, syntax = "probe({a}, {b})")]
pub struct Probe {
    pub a: Term<KItem>,
    pub b: Term<KItem>,
}

/// A function of one item, which writes an item into an `Int` result.
#[k::function(partial, sort = Int, syntax = "size({a})")]
pub struct Size {
    pub a: Term<KItem>,
}

/// A nested group, for `k::fragment!`.
#[k::cell]
pub struct Frame {
    #[k::cell]
    pub ret: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub stack: List,
    #[k::cell(nested)]
    pub frame: Frame,
}

"#;

const INITIALIZER: &str = r#"impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: k::map![],
            stack: list::empty(),
            frame: Frame { ret: 0 },
        }
    }
}
"#;

pub(super) fn base(imported: bool) -> BaseText {
    BaseText {
        before_commands: if imported {
            IMPORTED_BEFORE_COMMANDS
        } else {
            BEFORE_COMMANDS
        },
        after_commands: AFTER_COMMANDS,
        initializer: INITIALIZER,
        after_initializer: "",
    }
}

/// The constructs: one or more spellings of each `TermTree` shape, and the literal kinds.
/// Every spelling that reads a binder reads `x`, which each template binds.
const CONSTRUCTS: [&str; 26] = [
    // Reference: a binder, and a zero-argument variant named by its path alone.
    "x",
    "Cmd::Go",
    // Application: a variant with no argument and with one, a builtin and a user function.
    "Cmd::Go()",
    "Cmd::Hold(x)",
    "k::builtin::int::add(1, 2)",
    "Size(x)",
    // Literal: Int, negative Int, Bool, String, Float.
    "1",
    "-1",
    "true",
    "\"s\"",
    "1.5",
    // Wildcard.
    "_",
    // The token islands.
    "k::id!(\"$x\")",
    "k::bytes!(b\"ab\")",
    "k::anonymous!(Int, \"_V\")",
    "k::lexeme!(Word, \"word\")",
    // OrBool, Cell, SortTest.
    "k::or_bool!(true, false)",
    "k::fragment![crate::Frame { ret: 1 }]",
    "k::is!(Int, x)",
    "k::project!(Int, x)",
    // As, Or, Matches, Let, Closure, Rewrite.
    "y @ Cmd::Hold(_)",
    "Cmd::Go() | Cmd::Hold(_)",
    "k::matches!(x, Cmd::Hold(_))",
    "{ let y = x; y }",
    "k::ml::exists(|v: Int| k::ml::equals(v, 0))",
    "k::rewrite!(_ => 1)",
];

/// The constructs of the import axis: bare variants, which only a module-level import names.
const IMPORTED_CONSTRUCTS: [&str; 2] = ["Go()", "Hold(x)"];

/// One term position of one form: its template, in which `HOLE` is the construct, `TAG` the
/// case's hash, `NAME` its command, `UPPER` its hash in upper case, and `USES` the block's
/// import of the command family (empty on the import axis).
#[derive(Clone, Copy)]
struct Slot {
    form: &'static str,
    position: &'static str,
    side: Side,
    template: &'static str,
    /// Whether rustc parses the position as Rust before the form's macro reads it
    /// ([`Case::rustc_parses`](super::Case::rustc_parses)).
    rustc_parses: bool,
}

const fn slot(
    form: &'static str,
    position: &'static str,
    side: Side,
    template: &'static str,
) -> Slot {
    Slot {
        form,
        position,
        side,
        template,
        rustc_parses: false,
    }
}

impl Slot {
    /// The slot, at a position rustc parses: a fn body an attribute macro reads, or a `const`
    /// value.
    const fn parsed_by_rustc(self) -> Self {
        Self {
            rustc_parses: true,
            ..self
        }
    }
}

/// The term positions. A `#[k::rule]` fn, a `for Stmt` rule and a readable record keep their
/// cases apart by a command over two items, `NAME(x, ..)`, which also binds `x`; the equation
/// forms by the first argument of `Probe`, a command with no field. The shorthand, the constant
/// and the initializer name items of their own.
const SLOTS: [Slot; 29] = [
    slot(
        "rule",
        "subject",
        Side::Subject,
        concat!(
            "#[k::rule(label = \"case-TAG\")]\n",
            "fn case_TAG(k::term![Cmd::NAME(x, HOLE)",
            "]: Term<Stmt>) -> Term<Stmt> {\n",
            "    Cmd::Hold(x)\n}\n"
        ),
    ),
    slot(
        "rule",
        "result",
        Side::Result,
        concat!(
            "#[k::rule(label = \"case-TAG\")]\n",
            "fn case_TAG(k::term![Cmd::NAME(x, _)",
            "]: Term<Stmt>) -> Term<Stmt> {\n",
            "    Cmd::Hold(HOLE)\n}\n"
        ),
    )
    .parsed_by_rustc(),
    slot(
        "rule",
        "guard",
        Side::Guard,
        concat!(
            "#[k::rule(label = \"case-TAG\")]\n",
            "#[k::requires(HOLE)]\nfn case_TAG(k::term![Cmd::NAME(x, _)",
            "]: Term<Stmt>) -> Term<Stmt> {\n",
            "    Cmd::Hold(x)\n}\n"
        ),
    ),
    slot(
        "rule",
        "subject-depth-2",
        Side::Subject,
        concat!(
            "#[k::rule(label = \"case-TAG\")]\n",
            "fn case_TAG(k::term![Cmd::NAME(x, Cmd::Hold(HOLE))",
            "]: Term<Stmt>) -> Term<Stmt> {\n",
            "    Cmd::Hold(x)\n}\n"
        ),
    ),
    slot(
        "local-rule",
        "subject",
        Side::Subject,
        concat!(
            "#[k::rule(label = \"case-TAG\")]\n",
            "fn case_TAG(k::term![Cmd::NAME(k::rewrite!(x => Cmd::Go()), HOLE)]: Term<Stmt>) {}\n"
        ),
    ),
    slot(
        "equation",
        "subject",
        Side::Subject,
        concat!(
            "#[k::equation]\nfn case_TAG(k::term![Probe(Cmd::NAME(), HOLE)",
            "]: Term<Int>) -> Term<Int> {\n",
            "    0\n}\n"
        ),
    ),
    slot(
        "equation",
        "result",
        Side::Result,
        concat!(
            "#[k::equation]\nfn case_TAG(k::term![Probe(Cmd::NAME(), x)",
            "]: Term<Int>) -> Term<Int> {\n",
            "    Size(HOLE)\n}\n"
        ),
    )
    .parsed_by_rustc(),
    slot(
        "equation",
        "guard",
        Side::Guard,
        concat!(
            "#[k::equation]\n#[k::requires(HOLE)]\nfn case_TAG(k::term![Probe(Cmd::NAME(), x)",
            "]: Term<Int>) -> Term<Int> {\n",
            "    0\n}\n"
        ),
    ),
    slot(
        "equation",
        "subject-depth-2",
        Side::Subject,
        concat!(
            "#[k::equation]\nfn case_TAG(k::term![Probe(Cmd::NAME(), Cmd::Hold(HOLE))",
            "]: Term<Int>) -> Term<Int> {\n",
            "    0\n}\n"
        ),
    ),
    slot(
        "table",
        "subject",
        Side::Subject,
        "k::equations! {\n    for Probe;\n\n    case_TAG: (Cmd::NAME(), HOLE) => 0;\n}\n",
    ),
    slot(
        "table",
        "result",
        Side::Result,
        "k::equations! {\n    for Probe;\n\n    case_TAG: (Cmd::NAME(), x) => Size(HOLE);\n}\n",
    ),
    slot(
        "table",
        "subject-depth-2",
        Side::Subject,
        "k::equations! {\n    for Probe;\n\n    case_TAG: (Cmd::NAME(), Cmd::Hold(HOLE)) => 0;\n}\n",
    ),
    slot(
        "shorthand",
        "result",
        Side::Result,
        "#[k::function(partial, internal)]\npub fn FTAG(x: Term<KItem>) -> Term<Int> {\n    Size(HOLE)\n}\n",
    )
    .parsed_by_rustc(),
    slot(
        "simplification",
        "subject",
        Side::Subject,
        concat!(
            "#[k::simplification]\nfn case_TAG(k::term![Probe(Cmd::NAME(), HOLE)",
            "]: Term<Int>) -> Term<Int> {\n",
            "    0\n}\n"
        ),
    ),
    slot(
        "simplification",
        "result",
        Side::Result,
        concat!(
            "#[k::simplification]\nfn case_TAG(k::term![Probe(Cmd::NAME(), x)",
            "]: Term<Int>) -> Term<Int> {\n",
            "    Size(HOLE)\n}\n"
        ),
    )
    .parsed_by_rustc(),
    slot(
        "sort-rule",
        "subject",
        Side::Subject,
        "k::rules! {\n    for Stmt;\nUSES\n    case_TAG: Cmd::NAME(x, HOLE) => Cmd::Hold(x);\n}\n",
    ),
    slot(
        "sort-rule",
        "result",
        Side::Result,
        "k::rules! {\n    for Stmt;\nUSES\n    case_TAG: Cmd::NAME(x, _) => Cmd::Hold(HOLE);\n}\n",
    ),
    slot(
        "sort-rule",
        "subject-depth-2",
        Side::Subject,
        "k::rules! {\n    for Stmt;\nUSES\n    case_TAG: Cmd::NAME(x, Cmd::Hold(HOLE)) => Cmd::Hold(x);\n}\n",
    ),
    slot(
        "readable",
        "subject",
        Side::Subject,
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, HOLE), ..] } => { k: [..] };\n}\n",
    ),
    slot(
        "readable",
        "result",
        Side::Result,
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..] } => { k: [Cmd::Hold(HOLE), ..] };\n}\n",
    ),
    slot(
        "readable",
        "map-key",
        Side::Subject,
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], env: { HOLE -> v, .. } } => { k: [..] };\n}\n",
    ),
    slot(
        "readable",
        "list-element",
        Side::Subject,
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], stack: [HOLE, ..] } => { k: [..] };\n}\n",
    ),
    slot(
        "readable",
        "result-list-element",
        Side::Result,
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], stack: [_, ..] } => { k: [..], stack: [HOLE, ..] };\n}\n",
    ),
    slot(
        "readable",
        "subject-depth-2",
        Side::Subject,
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, Cmd::Hold(HOLE)), ..] } => { k: [..] };\n}\n",
    ),
    slot(
        "claim",
        "subject",
        Side::Subject,
        "k::claims! {\n    for Machine;\nUSES\n    #[k::claim(all_paths)]\n    case_TAG: { k: [Cmd::NAME(x, HOLE), ..] } => { k: [..] };\n}\n",
    ),
    slot(
        "claim",
        "result",
        Side::Result,
        "k::claims! {\n    for Machine;\nUSES\n    #[k::claim(all_paths)]\n    case_TAG: { k: [Cmd::NAME(x, _), ..] } => { k: [Cmd::Hold(HOLE), ..] };\n}\n",
    ),
    slot(
        "init",
        "item",
        Side::Initializer,
        concat!(
            "impl Machine {\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {\n        Self {\n            k: k::k![pgm, ",
            "Cmd::Hold(HOLE)",
            "],\n            env: k::map![],\n            stack: list::empty(),\n            frame: Frame { ret: 0 },\n        }\n    }\n}\n"
        ),
    ),
    slot(
        "init",
        "item-depth-2",
        Side::Initializer,
        concat!(
            "impl Machine {\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {\n        Self {\n            k: k::k![pgm, ",
            "Cmd::Hold(Cmd::Hold(HOLE))",
            "],\n            env: k::map![],\n            stack: list::empty(),\n            frame: Frame { ret: 0 },\n        }\n    }\n}\n"
        ),
    ),
    slot(
        "constant",
        "value",
        Side::Result,
        "#[k::constant]\npub const KUPPER: Stmt = Cmd::Hold(HOLE);\n",
    )
    .parsed_by_rustc(),
];

/// The term family: 29 slots × 26 constructs, and the import axis: 29 slots × 2 bare
/// variants.
pub(super) fn cases(cases: &mut Vec<Case>) {
    for slot in SLOTS {
        for construct in CONSTRUCTS {
            cases.push(case(Family::Terms, slot, construct));
        }
        for construct in IMPORTED_CONSTRUCTS {
            cases.push(case(Family::Import, slot, construct));
        }
    }
}

fn case(family: Family, slot: Slot, construct: &str) -> Case {
    let imported = family == Family::Import;
    let spec = CaseSpec {
        family,
        base: if imported {
            Base::Imported
        } else {
            Base::Terms
        },
        side: slot.side,
        kind: None,
        slot: vec![slot.form.to_owned(), slot.position.to_owned()],
        construct: construct.to_owned(),
    };
    let tag = spec.tag();
    let arity = match slot.form {
        "equation" | "table" | "simplification" => 0,
        _ => 2,
    };
    let command = Command::with_fields(&spec.id(), arity, "KItem");
    let template = slot
        .template
        .replace("TAG", &tag)
        .replace("NAME", &command.name)
        .replace("UPPER", &tag.to_uppercase())
        .replace("USES", if imported { "" } else { "    use Cmd::*;\n" });
    let (before, after) = template
        .split_once("HOLE")
        .expect("every template has a hole");
    let mut item = ItemBuilder::new();
    item.push(before).term(construct).push(after);
    let packaging = if slot.form == "init" {
        Packaging::Own(OwnReason::Initializer)
    } else {
        Packaging::Shared(command)
    };
    let mut case = spec.finish(packaging, &item);
    case.rustc_parses = slot.rustc_parses;
    case
}

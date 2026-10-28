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
//!
//! Each slot declares its hole's [`Position`] as the openings from its slot's root, and each
//! spelling its [`Node`]s.

use super::positions::Construct as C;
use super::positions::Form::{
    CellsRule, Constant, EquationFn, EquationTable, Initializer, LocalRule, ReadableClaim,
    ReadableRule, RuleFn, Simplification, SortRule,
};
use super::positions::Opening::{
    Argument, AsBody, FragmentField, FunctionArgument, LetBody, LetPattern, LetValue, ListElement,
    MapKey, MatchesPattern, MatchesSubject, OrBoolOperand, OrBranch, PredicateBody,
    PredicateOperand, RewriteLeft, RewriteRight, SortTestOperand, UpdateBase, UpdateField,
};
use super::positions::Slot as Part;
use super::positions::{Node, Position, Spelling, TermCase, node};
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

/// The constructs: one or more spellings of each `TermTree` shape, and the literal kinds, each
/// with its nodes. Every spelling that reads a binder reads `x`, which each template binds.
const SPELLINGS: [Spelling; 29] = [
    // Reference: a binder, and a zero-argument variant named by its path alone.
    spelling("x", &[node(C::Reference, &[])]),
    spelling("Cmd::Go", &[node(C::Constructor, &[])]),
    // Application: a variant with no argument and with one, a builtin and a user function.
    spelling("Cmd::Go()", &[node(C::Constructor, &[])]),
    spelling(
        "Cmd::Hold(x)",
        &[node(C::Constructor, &[]), node(C::Reference, &[Argument])],
    ),
    spelling(
        "k::builtin::int::add(1, 2)",
        &[
            node(C::BuiltinApplication, &[]),
            node(C::Literal, &[FunctionArgument]),
            node(C::Literal, &[FunctionArgument]),
        ],
    ),
    spelling(
        "Size(x)",
        &[
            node(C::FunctionApplication, &[]),
            node(C::Reference, &[FunctionArgument]),
        ],
    ),
    // Literal: Int, negative Int, Bool, String, Float.
    spelling("1", &[node(C::Literal, &[])]),
    spelling("-1", &[node(C::Literal, &[])]),
    spelling("true", &[node(C::Literal, &[])]),
    spelling("\"s\"", &[node(C::Literal, &[])]),
    spelling("1.5", &[node(C::Literal, &[])]),
    // Wildcard.
    spelling("_", &[node(C::Wildcard, &[])]),
    // The token islands.
    spelling("k::id!(\"$x\")", &[node(C::IdToken, &[])]),
    spelling("k::bytes!(b\"ab\")", &[node(C::BytesToken, &[])]),
    spelling("k::anonymous!(Int, \"_V\")", &[node(C::Anonymous, &[])]),
    spelling("k::lexeme!(Word, \"word\")", &[node(C::Lexeme, &[])]),
    // OrBool, Cell, SortTest.
    spelling(
        "k::or_bool!(true, false)",
        &[
            node(C::OrBool, &[]),
            node(C::Literal, &[OrBoolOperand]),
            node(C::Literal, &[OrBoolOperand]),
        ],
    ),
    spelling(
        "k::fragment![crate::Frame { ret: 1 }]",
        &[node(C::Fragment, &[]), node(C::Literal, &[FragmentField])],
    ),
    spelling(
        "k::is!(Int, x)",
        &[
            node(C::SortTest, &[]),
            node(C::Reference, &[SortTestOperand]),
        ],
    ),
    spelling(
        "k::project!(Int, x)",
        &[
            node(C::SortTest, &[]),
            node(C::Reference, &[SortTestOperand]),
        ],
    ),
    // As, Or, Matches, Let, Closure, Rewrite.
    spelling(
        "y @ Cmd::Hold(_)",
        &[
            node(C::As, &[]),
            node(C::Constructor, &[AsBody]),
            node(C::Wildcard, &[AsBody, Argument]),
        ],
    ),
    spelling(
        "Cmd::Go() | Cmd::Hold(_)",
        &[
            node(C::Or, &[]),
            node(C::Constructor, &[OrBranch]),
            node(C::Constructor, &[OrBranch]),
            node(C::Wildcard, &[OrBranch, Argument]),
        ],
    ),
    spelling(
        "k::matches!(x, Cmd::Hold(_))",
        &[
            node(C::Matches, &[]),
            node(C::Reference, &[MatchesSubject]),
            node(C::Constructor, &[MatchesPattern]),
            node(C::Wildcard, &[MatchesPattern, Argument]),
        ],
    ),
    spelling(
        "{ let y = x; y }",
        &[
            node(C::Let, &[]),
            node(C::Reference, &[LetPattern]),
            node(C::Reference, &[LetValue]),
            node(C::Reference, &[LetBody]),
        ],
    ),
    spelling(
        "k::ml::exists(|v: Int| k::ml::equals(v, 0))",
        &[
            node(C::MlPredicate, &[]),
            node(C::MlPredicate, &[PredicateBody]),
            node(C::Reference, &[PredicateBody, PredicateOperand]),
            node(C::Literal, &[PredicateBody, PredicateOperand]),
        ],
    ),
    spelling(
        "k::rewrite!(_ => 1)",
        &[
            node(C::Rewrite, &[]),
            node(C::Wildcard, &[RewriteLeft]),
            node(C::Literal, &[RewriteRight]),
        ],
    ),
    // A `let` pattern's alias and alternatives.
    spelling(
        "{ let y @ Cmd::Hold(_) = x; y }",
        &[
            node(C::Let, &[]),
            node(C::As, &[LetPattern]),
            node(C::Constructor, &[LetPattern, AsBody]),
            node(C::Wildcard, &[LetPattern, AsBody, Argument]),
            node(C::Reference, &[LetValue]),
            node(C::Reference, &[LetBody]),
        ],
    ),
    spelling(
        "{ let (Cmd::Go() | Cmd::Hold(_)) = x; x }",
        &[
            node(C::Let, &[]),
            node(C::Or, &[LetPattern]),
            node(C::Constructor, &[LetPattern, OrBranch]),
            node(C::Constructor, &[LetPattern, OrBranch]),
            node(C::Wildcard, &[LetPattern, OrBranch, Argument]),
            node(C::Reference, &[LetValue]),
            node(C::Reference, &[LetBody]),
        ],
    ),
    // A record update, whose base `x` is no alias of a matched record.
    spelling(
        "Cmd::Pair { a: x, ..x }",
        &[
            node(C::RecordUpdate, &[]),
            node(C::Reference, &[UpdateField]),
            node(C::Reference, &[UpdateBase]),
        ],
    ),
];

/// The constructs of the import axis: bare variants, which only a module-level import names.
const IMPORTED_SPELLINGS: [Spelling; 2] = [
    spelling("Go()", &[node(C::Constructor, &[])]),
    spelling(
        "Hold(x)",
        &[node(C::Constructor, &[]), node(C::Reference, &[Argument])],
    ),
];

const fn spelling(text: &'static str, nodes: &'static [Node]) -> Spelling {
    Spelling { text, nodes }
}

/// One term position of one form: its template, in which `HOLE` is the construct, `TAG` the
/// case's hash, `NAME` its command, `UPPER` its hash in upper case, `USES` the block's import
/// of the command family (empty on the import axis), and `BINDERS` a `cells!` rule's binder
/// parameters ([`binders`]).
#[derive(Clone, Copy)]
struct Slot {
    form: &'static str,
    position: &'static str,
    side: Side,
    /// Where the hole stands, which the oracle reads.
    at: Position,
    template: &'static str,
    /// Whether rustc parses the position as Rust before the form's macro reads it
    /// ([`Case::rustc_parses`](super::Case::rustc_parses)).
    rustc_parses: bool,
}

const fn slot(
    form: &'static str,
    position: &'static str,
    side: Side,
    at: Position,
    template: &'static str,
) -> Slot {
    Slot {
        form,
        position,
        side,
        at,
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

/// The term positions. A `#[k::rule]` fn, a `cells!` rule, a `for Stmt` rule and a readable
/// record keep their cases apart by a command over two items, `NAME(x, ..)`, which also binds
/// `x`; the equation forms by the first argument of `Probe`, a command with no field. The
/// shorthand, the constant and the initializer name items of their own.
///
/// The `cells!` slots are the value inside `KCell(..)`, the reference spelling of a readable
/// record's computation cell: the subject reads `KCell(NAME(x, HOLE), tail @ ..)`, the result
/// writes `KCell(Hold(HOLE), ..tail)`.
const SLOTS: [Slot; 31] = [
    slot(
        "rule",
        "subject",
        Side::Subject,
        Position::at(RuleFn, Part::Subject, &[Argument]),
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
        Position::at(RuleFn, Part::Result, &[Argument]),
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
        Position::at(RuleFn, Part::Requires, &[]),
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
        Position::at(RuleFn, Part::Subject, &[Argument, Argument]),
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
        Position::at(LocalRule, Part::Subject, &[Argument]),
        concat!(
            "#[k::rule(label = \"case-TAG\")]\n",
            "fn case_TAG(k::term![Cmd::NAME(k::rewrite!(x => Cmd::Go()), HOLE)]: Term<Stmt>) {}\n"
        ),
    ),
    slot(
        "cells",
        "subject",
        Side::Subject,
        Position::at(CellsRule, Part::Subject, &[Argument]),
        concat!(
            "#[k::rule(label = \"case-TAG\")]\n",
            "pub fn case_TAG(\nBINDERS",
            "    k::cells! { k: k::configuration::KCell(Cmd::NAME(x, HOLE), tail @ ..), state @ .. }: Machine,\n",
            ") -> Machine {\n",
            "    k::cells! { k: k::configuration::KCell(..tail), ..state }\n}\n"
        ),
    ),
    slot(
        "cells",
        "result",
        Side::Result,
        Position::at(CellsRule, Part::Result, &[Argument]),
        concat!(
            "#[k::rule(label = \"case-TAG\")]\n",
            "pub fn case_TAG(\nBINDERS",
            "    k::cells! { k: k::configuration::KCell(Cmd::NAME(x, _), tail @ ..), state @ .. }: Machine,\n",
            ") -> Machine {\n",
            "    k::cells! { k: k::configuration::KCell(Cmd::Hold(HOLE), ..tail), ..state }\n}\n"
        ),
    ),
    slot(
        "equation",
        "subject",
        Side::Subject,
        Position::at(EquationFn, Part::Subject, &[FunctionArgument]),
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
        Position::at(EquationFn, Part::Result, &[FunctionArgument]),
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
        Position::at(EquationFn, Part::Requires, &[]),
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
        Position::at(EquationFn, Part::Subject, &[FunctionArgument, Argument]),
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
        Position::at(EquationTable, Part::Subject, &[FunctionArgument]),
        "k::equations! {\n    for Probe;\n\n    case_TAG: (Cmd::NAME(), HOLE) => 0;\n}\n",
    ),
    slot(
        "table",
        "result",
        Side::Result,
        Position::at(EquationTable, Part::Result, &[FunctionArgument]),
        "k::equations! {\n    for Probe;\n\n    case_TAG: (Cmd::NAME(), x) => Size(HOLE);\n}\n",
    ),
    slot(
        "table",
        "subject-depth-2",
        Side::Subject,
        Position::at(EquationTable, Part::Subject, &[FunctionArgument, Argument]),
        "k::equations! {\n    for Probe;\n\n    case_TAG: (Cmd::NAME(), Cmd::Hold(HOLE)) => 0;\n}\n",
    ),
    slot(
        "shorthand",
        "result",
        Side::Result,
        Position::at(EquationFn, Part::Result, &[FunctionArgument]),
        "#[k::function(partial, internal)]\npub fn FTAG(x: Term<KItem>) -> Term<Int> {\n    Size(HOLE)\n}\n",
    )
    .parsed_by_rustc(),
    slot(
        "simplification",
        "subject",
        Side::Subject,
        Position::at(Simplification, Part::Subject, &[FunctionArgument]),
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
        Position::at(Simplification, Part::Result, &[FunctionArgument]),
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
        Position::at(SortRule, Part::Subject, &[Argument]),
        "k::rules! {\n    for Stmt;\nUSES\n    case_TAG: Cmd::NAME(x, HOLE) => Cmd::Hold(x);\n}\n",
    ),
    slot(
        "sort-rule",
        "result",
        Side::Result,
        Position::at(SortRule, Part::Result, &[Argument]),
        "k::rules! {\n    for Stmt;\nUSES\n    case_TAG: Cmd::NAME(x, _) => Cmd::Hold(HOLE);\n}\n",
    ),
    slot(
        "sort-rule",
        "subject-depth-2",
        Side::Subject,
        Position::at(SortRule, Part::Subject, &[Argument, Argument]),
        "k::rules! {\n    for Stmt;\nUSES\n    case_TAG: Cmd::NAME(x, Cmd::Hold(HOLE)) => Cmd::Hold(x);\n}\n",
    ),
    slot(
        "readable",
        "subject",
        Side::Subject,
        Position::at(ReadableRule, Part::Subject, &[Argument]),
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, HOLE), ..] } => { k: [..] };\n}\n",
    ),
    slot(
        "readable",
        "result",
        Side::Result,
        Position::at(ReadableRule, Part::Result, &[Argument]),
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..] } => { k: [Cmd::Hold(HOLE), ..] };\n}\n",
    ),
    slot(
        "readable",
        "map-key",
        Side::Subject,
        Position::at(ReadableRule, Part::Subject, &[MapKey]),
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], env: { HOLE -> v, .. } } => { k: [..] };\n}\n",
    ),
    slot(
        "readable",
        "list-element",
        Side::Subject,
        Position::at(ReadableRule, Part::Subject, &[ListElement]),
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], stack: [HOLE, ..] } => { k: [..] };\n}\n",
    ),
    slot(
        "readable",
        "result-list-element",
        Side::Result,
        Position::at(ReadableRule, Part::Result, &[ListElement]),
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], stack: [_, ..] } => { k: [..], stack: [HOLE, ..] };\n}\n",
    ),
    slot(
        "readable",
        "subject-depth-2",
        Side::Subject,
        Position::at(ReadableRule, Part::Subject, &[Argument, Argument]),
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, Cmd::Hold(HOLE)), ..] } => { k: [..] };\n}\n",
    ),
    slot(
        "claim",
        "subject",
        Side::Subject,
        Position::at(ReadableClaim, Part::Subject, &[Argument]),
        "k::claims! {\n    for Machine;\nUSES\n    #[k::claim(all_paths)]\n    case_TAG: { k: [Cmd::NAME(x, HOLE), ..] } => { k: [..] };\n}\n",
    ),
    slot(
        "claim",
        "result",
        Side::Result,
        Position::at(ReadableClaim, Part::Result, &[Argument]),
        "k::claims! {\n    for Machine;\nUSES\n    #[k::claim(all_paths)]\n    case_TAG: { k: [Cmd::NAME(x, _), ..] } => { k: [Cmd::Hold(HOLE), ..] };\n}\n",
    ),
    slot(
        "init",
        "item",
        Side::Initializer,
        Position::at(Initializer, Part::Value, &[Argument]),
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
        Position::at(Initializer, Part::Value, &[Argument, Argument]),
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
        Position::at(Constant, Part::Value, &[Argument]),
        "#[k::constant]\npub const KUPPER: Stmt = Cmd::Hold(HOLE);\n",
    )
    .parsed_by_rustc(),
];

/// The term family: 31 slots × 29 constructs, and the import axis: 31 slots × 2 bare
/// variants.
pub(super) fn cases(cases: &mut Vec<Case>) {
    for slot in SLOTS {
        for spelling in SPELLINGS {
            cases.push(case(Family::Terms, slot, spelling));
        }
        for spelling in IMPORTED_SPELLINGS {
            cases.push(case(Family::Import, slot, spelling));
        }
    }
}

fn case(family: Family, slot: Slot, spelling: Spelling) -> Case {
    let construct = spelling.text;
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
        .replace("USES", if imported { "" } else { "    use Cmd::*;\n" })
        .replace("BINDERS", &binders(slot, construct));
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
    case.term = Some(TermCase {
        position: slot.at,
        nodes: spelling.nodes,
    });
    case
}

/// A `cells!` rule's binder parameters, which declare every subject binder once in the order
/// the binders first occur: the command's `x`, then the alias `y` of `y @ P` in the subject (an
/// alias counts before the binders inside its pattern). Each is typed by the `KItem` field it
/// fills. A result's `y @ P` binds nothing, and a `let`'s or a closure's names are their own.
fn binders(slot: Slot, construct: &str) -> String {
    if slot.form != "cells" {
        return String::new();
    }
    let mut binders = String::from("    x: KItem,\n");
    if slot.side == Side::Subject && construct.starts_with("y @ ") {
        binders.push_str("    y: KItem,\n");
    }
    binders
}

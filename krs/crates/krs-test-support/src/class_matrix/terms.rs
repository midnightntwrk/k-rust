//! Term positions: every construct and notation at the positions of every sentence form, their
//! roots included, and inside the positions the constructs open (depth 2).
//!
//! Each hole is a position whose sort is `KItem` (a field of `Hold`, `Pair`, a command, the
//! functions `Probe` and `Size`, or a root declared `Term<KItem>`), which every sort but `K` lies
//! below, so a construct is judged by whether its shape may stand there, not by its sort. A guard
//! is the exception: the hole is the whole condition, a `Bool`.
//!
//! The constructs name the command family's variants through their enum, `Cmd::Hold(x)`, which
//! resolves in every form; the import axis ([`Family::Import`]) writes them bare under a
//! module-level `use Cmd::*;` instead.
//!
//! The slots ([`slots`]) are of three kinds, each declaring its hole's [`Position`] as the
//! openings from its slot's root:
//! - an argument position of a form, `Cmd::NAME(x, HOLE)`, as S0 made them;
//! - a slot's root, the empty path: a fn's, an equation's, a simplification's, a context's and a
//!   static clause's whole subject, a `for KItem` clause's (bare and in `k::term!`), a result's
//!   and a value's root, and an item of the computation cell;
//! - a position a construct opens, at one host per kind (matched, evaluated, built, guard): the
//!   opener's own nodes stand at the host, and the construct at the opener's hole, so a depth-2
//!   case's ID names its opener, `terms/sort-rule/result/let-body/Size(x)`.
//!
//! Each spelling ([`spellings`]) declares its [`Node`]s, which the oracle ([`super::oracle`])
//! reads with the slot's position.

use std::fmt::Write as _;

use super::positions::Construct as C;
use super::positions::Form::{
    Alias, CellsClaim, CellsLocalRule, CellsRule, Constant, Context, ContextAlias, Desugar,
    EquationFn, EquationTable, Initializer, LocalRule, ReadableClaim, ReadableRule, RuleFn,
    Simplification, SortRule,
};
use super::positions::Opening::{
    Argument, AsBody, ComputationItem, FragmentField, FunctionArgument, LetBody, LetPattern,
    LetValue, ListElement, MapKey, MapValue, MatchesPattern, MatchesSubject, OrBoolOperand,
    OrBranch, PredicateBody, PredicateOperand, RewriteLeft, RewriteRight, SortTestOperand,
    UpdateBase, UpdateField,
};
use super::positions::Slot as Part;
use super::positions::{Form, Node, Opening, Position, TermCase, node};
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

/// One construct's spelling: its text, the text a readable clause writes where a sort is named
/// (a turbofish names the marker in reference code and the sort in a readable clause), and its
/// nodes.
struct Spelling {
    text: &'static str,
    readable: Option<&'static str>,
    nodes: Vec<Node>,
}

impl Spelling {
    /// The text written at a slot of `form`.
    fn text(&self, form: Form) -> &'static str {
        match (self.readable, form) {
            (Some(readable), ReadableRule | ReadableClaim | SortRule) => readable,
            _ => self.text,
        }
    }
}

fn spelling(text: &'static str, nodes: &[Node]) -> Spelling {
    Spelling {
        text,
        readable: None,
        nodes: nodes.to_vec(),
    }
}

/// The constructs: one or more spellings of each `TermTree` shape, every literal kind, every
/// construct of `Construct`, every notation form, and the collection forms, each with its nodes.
/// Every spelling that reads a binder reads `x`, which each template binds.
#[expect(
    clippy::too_many_lines,
    reason = "One list of the closed catalog; each entry is one spelling and its nodes."
)]
fn spellings() -> Vec<Spelling> {
    vec![
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
    ]
}

/// The constructs of the import axis: bare variants, which only a module-level import names.
fn imported_spellings() -> Vec<Spelling> {
    vec![
        spelling("Go()", &[node(C::Constructor, &[])]),
        spelling(
            "Hold(x)",
            &[node(C::Constructor, &[]), node(C::Reference, &[Argument])],
        ),
    ]
}

/// The binders a `cells!` sentence declares, in the order they first occur: `x`, the alias `y` of
/// a subject construct `y @ P` (an alias counts before the binders inside its pattern), and the
/// value `v` of a map entry the subject reads.
#[derive(Clone, Copy)]
enum Binder {
    X,
    Alias,
    Value,
}

/// One term position of one form: its template, in which `HOLE` is the construct, `TAG` the
/// case's hash, `NAME` its command, `UPPER` its hash in upper case, `USES` the block's import
/// of the command family (empty on the import axis), and `BINDERS` a `cells!` sentence's binder
/// parameters ([`Slot::binders`]).
struct Slot {
    form: &'static str,
    position: &'static str,
    /// The construct the hole stands in at depth 2, which names the case's third ID segment.
    opener: Option<&'static str>,
    side: Side,
    /// Where the hole stands, or for depth 2 the opener: the oracle reads it.
    at: Position,
    /// The openings from the slot's root to `at`.
    path: Vec<Opening>,
    /// The opener's nodes before its hole and after it, relative to `at`.
    before: Vec<Node>,
    after: Vec<Node>,
    /// The openings from `at` to the hole.
    hole: Vec<Opening>,
    /// The outer construct's text before and after the hole, at depth 2.
    around: (String, String),
    /// Whether alternatives in the hole are grouped: an alias's pattern binds tighter than `|`.
    groups_alternatives: bool,
    template: String,
    /// Whether rustc parses the position as Rust before the form's macro reads it
    /// ([`Case::rustc_parses`](super::Case::rustc_parses)).
    rustc_parses: bool,
    /// The number of the command's fields.
    arity: usize,
    /// The command's production marker, for a static clause that expands it.
    marker: Option<&'static str>,
    /// The binders of a `cells!` sentence, in first-occurrence order; empty for another form.
    binders: &'static [Binder],
}

fn slot(
    form: &'static str,
    position: &'static str,
    side: Side,
    (at_form, part, path): (Form, Part, &[Opening]),
    template: &'static str,
) -> Slot {
    Slot {
        form,
        position,
        opener: None,
        side,
        at: Position::at(at_form, part, path),
        path: path.to_vec(),
        before: Vec::new(),
        after: Vec::new(),
        hole: Vec::new(),
        around: (String::new(), String::new()),
        groups_alternatives: false,
        template: template.to_owned(),
        rustc_parses: false,
        arity: 2,
        marker: None,
        binders: &[],
    }
}

impl Slot {
    /// The slot, at a position rustc parses: a fn body an attribute macro reads, or a `const`
    /// value.
    fn parsed_by_rustc(self) -> Self {
        Self {
            rustc_parses: true,
            ..self
        }
    }

    /// The slot, whose command has `arity` fields.
    fn arity(self, arity: usize) -> Self {
        Self { arity, ..self }
    }

    /// The slot, whose command is a production marked `marker`.
    fn marked(self, marker: &'static str) -> Self {
        Self {
            marker: Some(marker),
            ..self
        }
    }

    /// The slot, in a `cells!` sentence that declares `binders`.
    fn binding(self, binders: &'static [Binder]) -> Self {
        Self { binders, ..self }
    }

    /// A `cells!` sentence's binder parameters, one line each, typed by the `KItem` field or map
    /// value each fills. A result's or a condition's `y @ P` binds nothing, and a `let`'s or a
    /// closure's names are their own.
    fn binders(&self, construct: &str) -> String {
        let mut binders = String::new();
        for binder in self.binders {
            let name = match binder {
                Binder::X => "x",
                Binder::Value => "v",
                Binder::Alias if self.side == Side::Subject && construct.starts_with("y @ ") => "y",
                Binder::Alias => continue,
            };
            writeln!(binders, "    {name}: KItem,").expect("writing to a String cannot fail");
        }
        binders
    }
}

const RULE_SUBJECT: &str = concat!(
    "#[k::rule(label = \"case-TAG\")]\n",
    "fn case_TAG(k::term![Cmd::NAME(x, HOLE)",
    "]: Term<Stmt>) -> Term<Stmt> {\n",
    "    Cmd::Hold(x)\n}\n"
);

const RULE_GUARD: &str = concat!(
    "#[k::rule(label = \"case-TAG\")]\n",
    "#[k::requires(HOLE)]\nfn case_TAG(k::term![Cmd::NAME(x, _)",
    "]: Term<Stmt>) -> Term<Stmt> {\n",
    "    Cmd::Hold(x)\n}\n"
);

const LOCAL_RULE_SUBJECT: &str = concat!(
    "#[k::rule(label = \"case-TAG\")]\n",
    "fn case_TAG(k::term![Cmd::NAME(k::rewrite!(x => Cmd::Go()), HOLE)]: Term<Stmt>) {}\n"
);

const SORT_RULE_RESULT: &str =
    "k::rules! {\n    for Stmt;\nUSES\n    case_TAG: Cmd::NAME(x, _) => Cmd::Hold(HOLE);\n}\n";

const READABLE_MAP_KEY: &str = "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], env: { HOLE -> v, .. } } => { k: [..] };\n}\n";

const CELLS_CLAIM_GUARD: &str = concat!(
    "#[k::claim(all_paths, label = \"case-TAG\")]\n",
    "#[k::requires(HOLE)]\n",
    "pub fn case_TAG(\nBINDERS",
    "    k::cells! { k: k::configuration::KCell(Cmd::NAME(x, _), tail @ ..), state @ .. }: Machine,\n",
    ") -> Machine {\n",
    "    k::cells! { k: k::configuration::KCell(..tail), ..state }\n}\n"
);

/// A `cells!` rule: the binders, `SUBJECT` and `RESULT`, the cell entries of either side.
fn cells_rule(subject: &str, result: &str) -> String {
    format!(
        "#[k::rule(label = \"case-TAG\")]\npub fn case_TAG(\nBINDERS    k::cells! {{ {subject}, state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ {result}, ..state }}\n}}\n"
    )
}

/// A `cells!` sentence's computation cell reading the command: `KCell(Cmd::NAME(x, _), tail @ ..)`.
const CELLS_COMMAND: &str = "k: k::configuration::KCell(Cmd::NAME(x, _), tail @ ..)";

/// The result's computation cell that drops the command.
const CELLS_TAIL: &str = "k: k::configuration::KCell(..tail)";

/// The term positions, in three kinds ([module docs](self)). A `#[k::rule]` fn, a `cells!`
/// rule, a `for Stmt` rule and a readable record keep their cases apart by a command over two
/// items, `NAME(x, ..)`, which also binds `x`; a context by one over three, `NAME(h, x, ..)`,
/// whose `h` is its hole; the equation forms by the first argument of `Probe`, a command with no
/// field. A root case keeps its sentence apart by its label or its fn's name, or by a command
/// item after the root; the shorthand, the constant and the initializer name items of their own.
///
/// The `cells!` slots are the value inside `KCell(..)`, the reference spelling of a readable
/// record's computation cell: the subject reads `KCell(NAME(x, HOLE), tail @ ..)`, the result
/// writes `KCell(Hold(HOLE), ..tail)`. Every path into a computation cell steps into its item
/// ([`Opening::ComputationItem`]), and into a map's key or value from the cell's value.
#[expect(
    clippy::too_many_lines,
    reason = "One list of the closed slot set; each entry is one position."
)]
fn slots() -> Vec<Slot> {
    use Binder::{Alias as Y, Value as V, X};
    let mut slots = vec![
        // A `#[k::rule]` fn.
        slot(
            "rule",
            "subject",
            Side::Subject,
            (RuleFn, Part::Subject, &[Argument]),
            RULE_SUBJECT,
        ),
        slot(
            "rule",
            "subject-root",
            Side::Subject,
            (RuleFn, Part::Subject, &[]),
            concat!(
                "#[k::rule(label = \"case-TAG\")]\n",
                "fn case_TAG(k::term![HOLE]: Term<KItem>) -> Term<KItem> {\n",
                "    Cmd::Go()\n}\n"
            ),
        ),
        slot(
            "rule",
            "result",
            Side::Result,
            (RuleFn, Part::Result, &[Argument]),
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
            "result-root",
            Side::Result,
            (RuleFn, Part::Result, &[]),
            concat!(
                "#[k::rule(label = \"case-TAG\")]\n",
                "fn case_TAG(k::term![Cmd::NAME(x, _)",
                "]: Term<Stmt>) -> Term<KItem> {\n",
                "    HOLE\n}\n"
            ),
        )
        .parsed_by_rustc(),
        slot(
            "rule",
            "guard",
            Side::Guard,
            (RuleFn, Part::Requires, &[]),
            RULE_GUARD,
        ),
        slot(
            "rule",
            "subject-depth-2",
            Side::Subject,
            (RuleFn, Part::Subject, &[Argument, Argument]),
            concat!(
                "#[k::rule(label = \"case-TAG\")]\n",
                "fn case_TAG(k::term![Cmd::NAME(x, Cmd::Hold(HOLE))",
                "]: Term<Stmt>) -> Term<Stmt> {\n",
                "    Cmd::Hold(x)\n}\n"
            ),
        ),
        // A single-body `#[k::rule]` fn. Its subject's root holds the rewrite's host: a rule
        // whose root holds no rewrite changes nothing, so it has no root slot.
        slot(
            "local-rule",
            "subject",
            Side::Subject,
            (LocalRule, Part::Subject, &[Argument]),
            LOCAL_RULE_SUBJECT,
        ),
        // A `cells!` rule.
        slot(
            "cells",
            "subject",
            Side::Subject,
            (CellsRule, Part::Subject, &[ComputationItem, Argument]),
            "",
        ),
        slot(
            "cells",
            "result",
            Side::Result,
            (CellsRule, Part::Result, &[ComputationItem, Argument]),
            "",
        ),
        slot(
            "cells",
            "item-root",
            Side::Subject,
            (CellsRule, Part::Subject, &[ComputationItem]),
            "",
        ),
        slot(
            "cells",
            "result-item-root",
            Side::Result,
            (CellsRule, Part::Result, &[ComputationItem]),
            "",
        ),
        slot(
            "cells",
            "map-key",
            Side::Subject,
            (CellsRule, Part::Subject, &[MapKey]),
            "",
        ),
        slot(
            "cells",
            "map-value",
            Side::Subject,
            (CellsRule, Part::Subject, &[MapValue]),
            "",
        ),
        slot(
            "cells",
            "result-map-key",
            Side::Result,
            (CellsRule, Part::Result, &[MapKey]),
            "",
        ),
        slot(
            "cells",
            "result-map-value",
            Side::Result,
            (CellsRule, Part::Result, &[MapValue]),
            "",
        ),
        // A single-body `cells!` rule, a `cells!` claim and a context alias.
        slot(
            "cells-local",
            "subject",
            Side::Subject,
            (CellsLocalRule, Part::Subject, &[ComputationItem, Argument]),
            concat!(
                "#[k::rule(label = \"case-TAG\")]\n",
                "pub fn case_TAG(\nBINDERS",
                "    k::cells! { k: k::configuration::KCell(Cmd::NAME(k::rewrite!(x => Cmd::Go()), HOLE), ..), state @ .. }: Machine,\n",
                ") {\n}\n"
            ),
        )
        .binding(&[X, Y]),
        slot(
            "cells-claim",
            "subject",
            Side::Subject,
            (CellsClaim, Part::Subject, &[ComputationItem, Argument]),
            concat!(
                "#[k::claim(all_paths, label = \"case-TAG\")]\n",
                "pub fn case_TAG(\nBINDERS",
                "    k::cells! { k: k::configuration::KCell(Cmd::NAME(x, HOLE), tail @ ..), state @ .. }: Machine,\n",
                ") -> Machine {\n",
                "    k::cells! { k: k::configuration::KCell(..tail), ..state }\n}\n"
            ),
        )
        .binding(&[X, Y]),
        slot(
            "cells-claim",
            "item-root",
            Side::Subject,
            (CellsClaim, Part::Subject, &[ComputationItem]),
            concat!(
                "#[k::claim(all_paths, label = \"case-TAG\")]\n",
                "pub fn case_TAG(\nBINDERS",
                "    k::cells! { k: k::configuration::KCell(HOLE, Cmd::NAME(x, _), tail @ ..), state @ .. }: Machine,\n",
                ") -> Machine {\n",
                "    k::cells! { k: k::configuration::KCell(..tail), ..state }\n}\n"
            ),
        )
        .binding(&[Y, X]),
        slot(
            "cells-claim",
            "result-item-root",
            Side::Result,
            (CellsClaim, Part::Result, &[ComputationItem]),
            concat!(
                "#[k::claim(all_paths, label = \"case-TAG\")]\n",
                "pub fn case_TAG(\nBINDERS",
                "    k::cells! { k: k::configuration::KCell(Cmd::NAME(x, _), tail @ ..), state @ .. }: Machine,\n",
                ") -> Machine {\n",
                "    k::cells! { k: k::configuration::KCell(HOLE, ..tail), ..state }\n}\n"
            ),
        )
        .binding(&[X]),
        slot(
            "cells-claim",
            "result",
            Side::Result,
            (CellsClaim, Part::Result, &[ComputationItem, Argument]),
            concat!(
                "#[k::claim(all_paths, label = \"case-TAG\")]\n",
                "pub fn case_TAG(\nBINDERS",
                "    k::cells! { k: k::configuration::KCell(Cmd::NAME(x, _), tail @ ..), state @ .. }: Machine,\n",
                ") -> Machine {\n",
                "    k::cells! { k: k::configuration::KCell(Cmd::Hold(HOLE), ..tail), ..state }\n}\n"
            ),
        )
        .binding(&[X]),
        slot(
            "cells-claim",
            "guard",
            Side::Guard,
            (CellsClaim, Part::Requires, &[]),
            CELLS_CLAIM_GUARD,
        )
        .binding(&[X]),
        slot(
            "context-alias",
            "subject",
            Side::Subject,
            (ContextAlias, Part::Subject, &[ComputationItem, Argument]),
            concat!(
                "#[k::context_alias(name = case_TAG, here = site)]\n",
                "fn case_TAG(\nBINDERS",
                "    k::cells! { k: k::configuration::KCell(site, Cmd::NAME(x, HOLE), tail @ ..), state @ .. }: Machine,\n",
                ") {\n}\n"
            ),
        )
        .binding(&[X, Y]),
        slot(
            "context-alias",
            "item-root",
            Side::Subject,
            (ContextAlias, Part::Subject, &[ComputationItem]),
            concat!(
                "#[k::context_alias(name = case_TAG, here = site)]\n",
                "fn case_TAG(\nBINDERS",
                "    k::cells! { k: k::configuration::KCell(site, HOLE, Cmd::NAME(x, _), tail @ ..), state @ .. }: Machine,\n",
                ") {\n}\n"
            ),
        )
        .binding(&[Y, X]),
        // A context, whose command's first field is its hole.
        slot(
            "context",
            "subject",
            Side::Subject,
            (Context, Part::Subject, &[Argument]),
            "#[k::context(hole = h)]\nfn case_TAG(k::term![Cmd::NAME(h, x, HOLE)]: Term<Stmt>) {}\n",
        )
        .arity(3),
        slot(
            "context",
            "subject-root",
            Side::Subject,
            (Context, Part::Subject, &[]),
            "#[k::context(hole = x)]\nfn case_TAG(k::term![HOLE]: Term<KItem>) {}\n",
        ),
        slot(
            "context",
            "guard",
            Side::Guard,
            (Context, Part::Requires, &[]),
            "#[k::context(hole = h)]\n#[k::requires(HOLE)]\nfn case_TAG(k::term![Cmd::NAME(h, x, _)]: Term<Stmt>) {}\n",
        )
        .arity(3),
        // The equation forms.
        slot(
            "equation",
            "subject",
            Side::Subject,
            (EquationFn, Part::Subject, &[FunctionArgument]),
            concat!(
                "#[k::equation]\nfn case_TAG(k::term![Probe(Cmd::NAME(), HOLE)",
                "]: Term<Int>) -> Term<Int> {\n",
                "    0\n}\n"
            ),
        )
        .arity(0),
        slot(
            "equation",
            "subject-root",
            Side::Subject,
            (EquationFn, Part::Subject, &[]),
            "#[k::equation]\nfn case_TAG(k::term![HOLE]: Term<KItem>) -> Term<KItem> {\n    0\n}\n",
        )
        .arity(0),
        slot(
            "equation",
            "result",
            Side::Result,
            (EquationFn, Part::Result, &[FunctionArgument]),
            concat!(
                "#[k::equation]\nfn case_TAG(k::term![Probe(Cmd::NAME(), x)",
                "]: Term<Int>) -> Term<Int> {\n",
                "    Size(HOLE)\n}\n"
            ),
        )
        .parsed_by_rustc()
        .arity(0),
        slot(
            "equation",
            "guard",
            Side::Guard,
            (EquationFn, Part::Requires, &[]),
            concat!(
                "#[k::equation]\n#[k::requires(HOLE)]\nfn case_TAG(k::term![Probe(Cmd::NAME(), x)",
                "]: Term<Int>) -> Term<Int> {\n",
                "    0\n}\n"
            ),
        )
        .arity(0),
        slot(
            "equation",
            "subject-depth-2",
            Side::Subject,
            (EquationFn, Part::Subject, &[FunctionArgument, Argument]),
            concat!(
                "#[k::equation]\nfn case_TAG(k::term![Probe(Cmd::NAME(), Cmd::Hold(HOLE))",
                "]: Term<Int>) -> Term<Int> {\n",
                "    0\n}\n"
            ),
        )
        .arity(0),
        // A table row names its function in the table's header, so its subject has no root of
        // its own; its result is the function's sort, `Int`, whose root the shorthand's covers.
        slot(
            "table",
            "subject",
            Side::Subject,
            (EquationTable, Part::Subject, &[FunctionArgument]),
            "k::equations! {\n    for Probe;\n\n    case_TAG: (Cmd::NAME(), HOLE) => 0;\n}\n",
        )
        .arity(0),
        slot(
            "table",
            "result",
            Side::Result,
            (EquationTable, Part::Result, &[FunctionArgument]),
            "k::equations! {\n    for Probe;\n\n    case_TAG: (Cmd::NAME(), x) => Size(HOLE);\n}\n",
        )
        .arity(0),
        slot(
            "table",
            "subject-depth-2",
            Side::Subject,
            (EquationTable, Part::Subject, &[FunctionArgument, Argument]),
            "k::equations! {\n    for Probe;\n\n    case_TAG: (Cmd::NAME(), Cmd::Hold(HOLE)) => 0;\n}\n",
        )
        .arity(0),
        slot(
            "shorthand",
            "result",
            Side::Result,
            (EquationFn, Part::Result, &[FunctionArgument]),
            "#[k::function(partial, internal)]\npub fn FTAG(x: Term<KItem>) -> Term<Int> {\n    Size(HOLE)\n}\n",
        )
        .parsed_by_rustc(),
        slot(
            "shorthand",
            "result-root",
            Side::Result,
            (EquationFn, Part::Result, &[]),
            "#[k::function(partial, internal)]\npub fn FTAG(x: Term<KItem>) -> Term<KItem> {\n    HOLE\n}\n",
        )
        .parsed_by_rustc(),
        slot(
            "simplification",
            "subject",
            Side::Subject,
            (Simplification, Part::Subject, &[FunctionArgument]),
            concat!(
                "#[k::simplification]\nfn case_TAG(k::term![Probe(Cmd::NAME(), HOLE)",
                "]: Term<Int>) -> Term<Int> {\n",
                "    0\n}\n"
            ),
        )
        .arity(0),
        slot(
            "simplification",
            "subject-root",
            Side::Subject,
            (Simplification, Part::Subject, &[]),
            "#[k::simplification]\nfn case_TAG(k::term![HOLE]: Term<KItem>) -> Term<KItem> {\n    0\n}\n",
        )
        .arity(0),
        slot(
            "simplification",
            "result",
            Side::Result,
            (Simplification, Part::Result, &[FunctionArgument]),
            concat!(
                "#[k::simplification]\nfn case_TAG(k::term![Probe(Cmd::NAME(), x)",
                "]: Term<Int>) -> Term<Int> {\n",
                "    Size(HOLE)\n}\n"
            ),
        )
        .parsed_by_rustc()
        .arity(0),
        slot(
            "simplification",
            "result-root",
            Side::Result,
            (Simplification, Part::Result, &[]),
            concat!(
                "#[k::simplification]\nfn case_TAG(k::term![Probe(Cmd::NAME(), x)",
                "]: Term<KItem>) -> Term<KItem> {\n",
                "    HOLE\n}\n"
            ),
        )
        .parsed_by_rustc()
        .arity(0),
        // The static clauses, whose command is the production a subject's clause expands. A root
        // case's clause names a construct of its own, and its command is no production.
        slot(
            "desugar",
            "subject",
            Side::Subject,
            (Desugar, Part::Subject, &[Argument]),
            "#[k::desugar]\nfn case_TAG(k::term![Cmd::NAME(x, HOLE)]: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Hold(x)\n}\n",
        )
        .marked("#[k::desugar]"),
        slot(
            "desugar",
            "subject-root",
            Side::Subject,
            (Desugar, Part::Subject, &[]),
            "#[k::desugar]\nfn case_TAG(k::term![HOLE]: Term<KItem>) -> Term<KItem> {\n    Cmd::Go()\n}\n",
        ),
        slot(
            "desugar",
            "result-root",
            Side::Result,
            (Desugar, Part::Result, &[]),
            "#[k::desugar]\nfn case_TAG(k::term![Cmd::NAME(x, _)]: Term<Stmt>) -> Term<KItem> {\n    HOLE\n}\n",
        )
        .parsed_by_rustc()
        .marked("#[k::desugar]"),
        slot(
            "desugar",
            "result",
            Side::Result,
            (Desugar, Part::Result, &[Argument]),
            "#[k::desugar]\nfn case_TAG(k::term![Cmd::NAME(x, _)]: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Hold(HOLE)\n}\n",
        )
        .parsed_by_rustc()
        .marked("#[k::desugar]"),
        slot(
            "alias",
            "subject",
            Side::Subject,
            (Alias, Part::Subject, &[Argument]),
            "#[k::alias]\nfn case_TAG(k::term![Cmd::NAME(x, HOLE)]: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Hold(x)\n}\n",
        )
        .marked("#[k::alias]"),
        slot(
            "alias",
            "subject-root",
            Side::Subject,
            (Alias, Part::Subject, &[]),
            "#[k::alias]\nfn case_TAG(k::term![HOLE]: Term<KItem>) -> Term<KItem> {\n    Cmd::Go()\n}\n",
        ),
        slot(
            "alias",
            "result-root",
            Side::Result,
            (Alias, Part::Result, &[]),
            "#[k::alias]\nfn case_TAG(k::term![Cmd::NAME(x, _)]: Term<Stmt>) -> Term<KItem> {\n    HOLE\n}\n",
        )
        .parsed_by_rustc()
        .marked("#[k::alias]"),
        slot(
            "alias",
            "result",
            Side::Result,
            (Alias, Part::Result, &[Argument]),
            "#[k::alias]\nfn case_TAG(k::term![Cmd::NAME(x, _)]: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Hold(HOLE)\n}\n",
        )
        .parsed_by_rustc()
        .marked("#[k::alias]"),
        // A `for Sort` clause: the subject's root bare and in its optional `k::term!` wrapper,
        // which reads it alike, over `KItem`, whose clause a value of any sort may root.
        slot(
            "sort-rule",
            "subject",
            Side::Subject,
            (SortRule, Part::Subject, &[Argument]),
            "k::rules! {\n    for Stmt;\nUSES\n    case_TAG: Cmd::NAME(x, HOLE) => Cmd::Hold(x);\n}\n",
        ),
        slot(
            "sort-rule",
            "subject-root",
            Side::Subject,
            (SortRule, Part::Subject, &[]),
            "k::rules! {\n    for KItem;\nUSES\n    case_TAG: HOLE => Cmd::Go();\n}\n",
        ),
        slot(
            "sort-rule",
            "subject-root-term",
            Side::Subject,
            (SortRule, Part::Subject, &[]),
            "k::rules! {\n    for KItem;\nUSES\n    case_TAG: k::term![HOLE] => Cmd::Go();\n}\n",
        ),
        slot(
            "sort-rule",
            "result",
            Side::Result,
            (SortRule, Part::Result, &[Argument]),
            SORT_RULE_RESULT,
        ),
        slot(
            "sort-rule",
            "result-root",
            Side::Result,
            (SortRule, Part::Result, &[]),
            "k::rules! {\n    for KItem;\nUSES\n    case_TAG: Cmd::NAME(x, _) => HOLE;\n}\n",
        ),
        slot(
            "sort-rule",
            "subject-depth-2",
            Side::Subject,
            (SortRule, Part::Subject, &[Argument, Argument]),
            "k::rules! {\n    for Stmt;\nUSES\n    case_TAG: Cmd::NAME(x, Cmd::Hold(HOLE)) => Cmd::Hold(x);\n}\n",
        ),
        // A readable record.
        slot(
            "readable",
            "subject",
            Side::Subject,
            (ReadableRule, Part::Subject, &[ComputationItem, Argument]),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, HOLE), ..] } => { k: [..] };\n}\n",
        ),
        slot(
            "readable",
            "item-root",
            Side::Subject,
            (ReadableRule, Part::Subject, &[ComputationItem]),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [HOLE, Cmd::NAME(x, _), ..] } => { k: [..] };\n}\n",
        ),
        slot(
            "readable",
            "result",
            Side::Result,
            (ReadableRule, Part::Result, &[ComputationItem, Argument]),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..] } => { k: [Cmd::Hold(HOLE), ..] };\n}\n",
        ),
        slot(
            "readable",
            "result-item-root",
            Side::Result,
            (ReadableRule, Part::Result, &[ComputationItem]),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..] } => { k: [HOLE, ..] };\n}\n",
        ),
        slot(
            "readable",
            "guard",
            Side::Guard,
            (ReadableRule, Part::Requires, &[]),
            "k::rules! {\n    for Machine;\nUSES\n    #[k::requires(HOLE)]\n    case_TAG: { k: [Cmd::NAME(x, _), ..] } => { k: [..] };\n}\n",
        ),
        slot(
            "readable",
            "map-key",
            Side::Subject,
            (ReadableRule, Part::Subject, &[MapKey]),
            READABLE_MAP_KEY,
        ),
        slot(
            "readable",
            "map-value",
            Side::Subject,
            (ReadableRule, Part::Subject, &[MapValue]),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], env: { x -> HOLE, .. } } => { k: [..] };\n}\n",
        ),
        slot(
            "readable",
            "list-element",
            Side::Subject,
            (ReadableRule, Part::Subject, &[ListElement]),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], stack: [HOLE, ..] } => { k: [..] };\n}\n",
        ),
        slot(
            "readable",
            "result-list-element",
            Side::Result,
            (ReadableRule, Part::Result, &[ListElement]),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], stack: [_, ..] } => { k: [..], stack: [HOLE, ..] };\n}\n",
        ),
        slot(
            "readable",
            "subject-depth-2",
            Side::Subject,
            (ReadableRule, Part::Subject, &[ComputationItem, Argument, Argument]),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, Cmd::Hold(HOLE)), ..] } => { k: [..] };\n}\n",
        ),
        // A readable claim.
        slot(
            "claim",
            "subject",
            Side::Subject,
            (ReadableClaim, Part::Subject, &[ComputationItem, Argument]),
            "k::claims! {\n    for Machine;\nUSES\n    #[k::claim(all_paths)]\n    case_TAG: { k: [Cmd::NAME(x, HOLE), ..] } => { k: [..] };\n}\n",
        ),
        slot(
            "claim",
            "item-root",
            Side::Subject,
            (ReadableClaim, Part::Subject, &[ComputationItem]),
            "k::claims! {\n    for Machine;\nUSES\n    #[k::claim(all_paths)]\n    case_TAG: { k: [HOLE, Cmd::NAME(x, _), ..] } => { k: [..] };\n}\n",
        ),
        slot(
            "claim",
            "result",
            Side::Result,
            (ReadableClaim, Part::Result, &[ComputationItem, Argument]),
            "k::claims! {\n    for Machine;\nUSES\n    #[k::claim(all_paths)]\n    case_TAG: { k: [Cmd::NAME(x, _), ..] } => { k: [Cmd::Hold(HOLE), ..] };\n}\n",
        ),
        slot(
            "claim",
            "result-item-root",
            Side::Result,
            (ReadableClaim, Part::Result, &[ComputationItem]),
            "k::claims! {\n    for Machine;\nUSES\n    #[k::claim(all_paths)]\n    case_TAG: { k: [Cmd::NAME(x, _), ..] } => { k: [HOLE, ..] };\n}\n",
        ),
        // An initializer and a constant.
        slot(
            "init",
            "item",
            Side::Initializer,
            (Initializer, Part::Value, &[ComputationItem, Argument]),
            "",
        ),
        slot(
            "init",
            "item-root",
            Side::Initializer,
            (Initializer, Part::Value, &[ComputationItem]),
            "",
        ),
        slot(
            "init",
            "item-depth-2",
            Side::Initializer,
            (Initializer, Part::Value, &[ComputationItem, Argument, Argument]),
            "",
        ),
        slot(
            "constant",
            "value",
            Side::Result,
            (Constant, Part::Value, &[Argument]),
            "#[k::constant]\npub const KUPPER: Stmt = Cmd::Hold(HOLE);\n",
        )
        .parsed_by_rustc(),
        slot(
            "constant",
            "value-root",
            Side::Result,
            (Constant, Part::Value, &[]),
            "#[k::constant]\npub const KUPPER: KItem = HOLE;\n",
        )
        .parsed_by_rustc(),
    ];
    for slot in &mut slots {
        let (template, binders): (String, &'static [Binder]) = match (slot.form, slot.position) {
            ("cells", "subject") => (
                cells_rule(
                    "k: k::configuration::KCell(Cmd::NAME(x, HOLE), tail @ ..)",
                    CELLS_TAIL,
                ),
                &[X, Y],
            ),
            ("cells", "result") => (
                cells_rule(
                    CELLS_COMMAND,
                    "k: k::configuration::KCell(Cmd::Hold(HOLE), ..tail)",
                ),
                &[X],
            ),
            ("cells", "item-root") => (
                cells_rule(
                    "k: k::configuration::KCell(HOLE, Cmd::NAME(x, _), tail @ ..)",
                    CELLS_TAIL,
                ),
                &[Y, X],
            ),
            ("cells", "result-item-root") => (
                cells_rule(CELLS_COMMAND, "k: k::configuration::KCell(HOLE, ..tail)"),
                &[X],
            ),
            ("cells", "map-key") => (
                cells_rule(
                    &format!(
                        "{CELLS_COMMAND}, env: k::configuration::Cell(k::map![HOLE -> v, ..])"
                    ),
                    CELLS_TAIL,
                ),
                &[X, Y, V],
            ),
            ("cells", "map-value") => (
                cells_rule(
                    &format!(
                        "{CELLS_COMMAND}, env: k::configuration::Cell(k::map![x -> HOLE, ..])"
                    ),
                    CELLS_TAIL,
                ),
                &[X, Y],
            ),
            ("cells", "result-map-key") => (
                cells_rule(
                    &format!("{CELLS_COMMAND}, env: k::configuration::Cell(_)"),
                    &format!("{CELLS_TAIL}, env: k::configuration::Cell(k::map![HOLE -> 1])"),
                ),
                &[X],
            ),
            ("cells", "result-map-value") => (
                cells_rule(
                    &format!("{CELLS_COMMAND}, env: k::configuration::Cell(_)"),
                    &format!("{CELLS_TAIL}, env: k::configuration::Cell(k::map![x -> HOLE])"),
                ),
                &[X],
            ),
            ("init", position) => (
                initializer(match position {
                    "item" => "Cmd::Hold(HOLE)",
                    "item-root" => "HOLE",
                    _ => "Cmd::Hold(Cmd::Hold(HOLE))",
                }),
                &[],
            ),
            _ => continue,
        };
        slot.template = template;
        slot.binders = binders;
    }
    slots
}

/// An initializer whose computation cell holds `pgm` and `item`.
fn initializer(item: &str) -> String {
    format!(
        "impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {{\n        Self {{\n            k: k::k![pgm, {item}],\n            env: k::map![],\n            stack: list::empty(),\n            frame: Frame {{ ret: 0 }},\n        }}\n    }}\n}}\n"
    )
}

/// The term family: every slot × every construct, and the import axis: every slot of depth 1 ×
/// 2 bare variants.
pub(super) fn cases(cases: &mut Vec<Case>) {
    let spellings = spellings();
    let imported = imported_spellings();
    for slot in slots() {
        for spelling in &spellings {
            cases.push(case(Family::Terms, &slot, spelling));
        }
        if slot.opener.is_none() {
            for spelling in &imported {
                cases.push(case(Family::Import, &slot, spelling));
            }
        }
    }
}

fn case(family: Family, slot: &Slot, spelling: &Spelling) -> Case {
    let construct = spelling.text(slot.at.form);
    let imported = family == Family::Import;
    let mut segments = vec![slot.form.to_owned(), slot.position.to_owned()];
    segments.extend(slot.opener.map(str::to_owned));
    let spec = CaseSpec {
        family,
        base: if imported {
            Base::Imported
        } else {
            Base::Terms
        },
        side: slot.side,
        kind: None,
        slot: segments,
        construct: construct.to_owned(),
    };
    let tag = spec.tag();
    let command = Command::with_fields(&spec.id(), slot.arity, "KItem").marked(slot.marker);
    let template = slot
        .template
        .replace("TAG", &tag)
        .replace("NAME", &command.name)
        .replace("UPPER", &tag.to_uppercase())
        .replace("USES", if imported { "" } else { "    use Cmd::*;\n" })
        .replace("BINDERS", &slot.binders(construct));
    let (before, after) = template
        .split_once("HOLE")
        .expect("every template has a hole");
    let mut item = ItemBuilder::new();
    item.push(before);
    if slot.opener.is_some() {
        let grouped = slot.groups_alternatives
            && spelling
                .nodes
                .first()
                .is_some_and(|node| node.construct == C::Or);
        let (open, close) = if grouped { ("(", ")") } else { ("", "") };
        item.inside(
            &format!("{}{open}", slot.around.0),
            construct,
            &format!("{close}{}", slot.around.1),
        );
    } else {
        item.term(construct);
    }
    item.push(after);
    let packaging = if slot.form == "init" {
        Packaging::Own(OwnReason::Initializer)
    } else {
        Packaging::Shared(command)
    };
    let mut case = spec.finish(packaging, &item);
    case.rustc_parses = slot.rustc_parses;
    let mut nodes = slot.before.clone();
    nodes.extend(spelling.nodes.iter().map(|node| node.below(&slot.hole)));
    nodes.extend(slot.after.iter().cloned());
    case.term = Some(TermCase {
        position: slot.at,
        path: slot.path.clone(),
        nodes,
    });
    case
}

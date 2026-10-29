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
    Argument, AsBody, ComputationItem, FragmentField, FunctionArgument, Instance, LetBody,
    LetPattern, LetValue, ListElement, MapKey, MapValue, MatchesPattern, MatchesSubject,
    OrBoolOperand, OrBranch, PredicateBody, PredicateOperand, RewriteLeft, RewriteRight,
    SetElement, SortTestOperand, UpdateBase, UpdateField,
};
use super::positions::Slot as Part;
use super::positions::{Form, Node, Notation, Opening, Position, TermCase, node};
use super::{
    Base, BaseText, Case, CaseSpec, Command, Family, ItemBuilder, OwnReason, Packaging, Side,
};

const BEFORE_COMMANDS: &str = r#"use k::builtin::{Int, KSequence, List, Map, list};
use k::{KItem, KResult, Term};

k::sorts! {
    Stmt;
    Items;
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
    Items;
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

/// A cons list of items, whose elements bracket notation reads.
#[k::constructors(sort = Items, result = KResult)]
#[k::cons_list]
#[rustfmt::skip]
pub enum Seq {
    #[k::syntax("nil")] Nil(),
    #[k::syntax("cons({head}, {tail})")] Cons { head: KItem, tail: Items },
}

/// A parametric constructor, whose turbofish names its instance.
#[k::constructor(sort = S, syntax = "wrap({inner})")]
pub struct Wrap<S: ?Sized> {
    pub inner: Term<S>,
}

/// A nested group, for `k::fragment!`.
#[k::cell]
pub struct Frame {
    #[k::cell]
    pub ret: Int,
}

/// The parent of the `member` collection.
#[k::cell]
pub struct Pool {
    #[k::cell(multiplicity = "*", cell_type = "List", nested)]
    pub member: Member,
}

/// One instance of the `member` collection, whose child holds a command: an initializer writes
/// a value of its cell's own sort.
#[k::cell]
pub struct Member {
    #[k::cell]
    pub item: Stmt,
}

/// The parent of the Set collection `token`.
#[k::cell]
pub struct Tray {
    #[k::cell(multiplicity = "*", cell_type = "Set", nested)]
    pub token: Token,
}

/// One instance of the `token` collection.
#[k::cell]
pub struct Token {
    #[k::cell]
    pub mark: Stmt,
}

/// The parent of the Map collection `row`, keyed by an instance's first child.
#[k::cell]
pub struct Table {
    #[k::cell(multiplicity = "*", cell_type = "Map", nested)]
    pub row: Row,
}

/// One instance of the `row` collection.
#[k::cell]
pub struct Row {
    #[k::cell]
    pub id: Stmt,
    #[k::cell]
    pub value: Stmt,
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
    #[k::cell]
    pub seq: Items,
    #[k::cell(nested)]
    pub pool: Pool,
    #[k::cell(nested)]
    pub tray: Tray,
    #[k::cell(nested)]
    pub table: Table,
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
            seq: Seq::Nil(),
            pool: Pool { member: Member { item: Cmd::Go() } },
            tray: Tray { token: Token { mark: Cmd::Go() } },
            table: Table { row: Row { id: Cmd::Go(), value: Cmd::Go() } },
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

/// A binary notation form over the binder and a literal, `x + 1`.
fn binary(text: &'static str, notation: Notation) -> Spelling {
    spelling(
        text,
        &[
            node(C::Notation(notation), &[]),
            node(C::Reference, &[FunctionArgument]),
            node(C::Literal, &[FunctionArgument]),
        ],
    )
}

/// The constructs: one or more spellings of each `TermTree` shape, every literal kind, every
/// construct of `Construct`, every notation form, and the collection forms, each with its nodes.
/// Every spelling that reads a binder reads `x`, which each template binds.
#[expect(
    clippy::too_many_lines,
    reason = "One list of the closed catalog; each entry is one spelling and its nodes."
)]
fn spellings() -> Vec<Spelling> {
    let mut spellings = vec![
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
        // A record update, whose base `x` is no alias of a matched record, and an open record.
        spelling(
            "Cmd::Pair { a: x, ..x }",
            &[
                node(C::RecordUpdate, &[]),
                node(C::Reference, &[UpdateField]),
                node(C::Reference, &[UpdateBase]),
            ],
        ),
        spelling(
            "Cmd::Pair { a: x, .. }",
            &[node(C::OpenRecord, &[]), node(C::Reference, &[Argument])],
        ),
        // A turbofish instance of the parametric `Wrap`: the marker in reference code, the sort
        // in a readable clause.
        Spelling {
            text: "Wrap::<dyn k::KItemSort>(x)",
            readable: Some("Wrap::<KItem>(x)"),
            nodes: vec![node(C::Turbofish, &[]), node(C::Reference, &[Argument])],
        },
        // The notation forms (`krs_syntax::notation`), each with the call it denotes: a binary
        // operator of each class, the connectives, the unary operators over a term the
        // position does not sort (`!x` and `-x` over a `KItem` choose no domain), and a method.
        binary("x + 1", Notation::Arithmetic),
        binary("x & 1", Notation::Bitwise),
        binary("x << 1", Notation::Shift),
        binary("x < 1", Notation::Comparison),
        binary("x == 1", Notation::Equality),
        spelling(
            "x && true",
            &[
                node(C::Notation(Notation::AndThen), &[]),
                node(C::Reference, &[FunctionArgument]),
                node(C::Literal, &[FunctionArgument]),
            ],
        ),
        spelling(
            "x || true",
            &[
                node(C::Notation(Notation::OrElse), &[]),
                node(C::Reference, &[FunctionArgument]),
                node(C::Literal, &[FunctionArgument]),
            ],
        ),
        spelling(
            "!(x < 1)",
            &[
                node(C::Notation(Notation::Not), &[]),
                node(C::Notation(Notation::Comparison), &[FunctionArgument]),
                node(C::Reference, &[FunctionArgument, FunctionArgument]),
                node(C::Literal, &[FunctionArgument, FunctionArgument]),
            ],
        ),
        spelling(
            "-(x + 1)",
            &[
                node(C::Notation(Notation::Negation), &[]),
                node(C::Notation(Notation::Arithmetic), &[FunctionArgument]),
                node(C::Reference, &[FunctionArgument, FunctionArgument]),
                node(C::Literal, &[FunctionArgument, FunctionArgument]),
            ],
        ),
        binary("x.add::<Int>(1)", Notation::Method),
        // The call `x + 1` and `x.add::<Int>(1)` denote.
        spelling(
            "k::builtin::int::add(x, 1)",
            &[
                node(C::BuiltinApplication, &[]),
                node(C::Reference, &[FunctionArgument]),
                node(C::Literal, &[FunctionArgument]),
            ],
        ),
        // A set's singleton, K's `SetItem(x)`: the constructor of a set's elements, a value,
        // which a pattern matches as a set; a set is looked up by its elements as a map by its
        // keys, so its element reads as a key does.
        spelling(
            "k::builtin::set::item(x)",
            &[node(C::Constructor, &[]), node(C::Reference, &[SetElement])],
        ),
        // `|` over operands a domain takes: the bitwise operator where a term is computed, the
        // alternatives' spelling where a pattern is read, its operands the branches.
        spelling(
            "x | 1",
            &[
                node(C::Notation(Notation::BitwiseOr), &[]),
                node(C::Reference, &[OrBranch]),
                node(C::Literal, &[OrBranch]),
            ],
        ),
    ];
    // A map literal, in the facade's path and bare: `map::update(map::empty(), x, 1)`, its nodes
    // in the walker's order, the denoted call's. And list brackets with a rest.
    for text in ["k::map![x -> 1]", "map![x -> 1]"] {
        spellings.push(spelling(
            text,
            &[
                node(C::Notation(Notation::MapLiteral), &[]),
                node(C::Notation(Notation::CollectionValue), &[FunctionArgument]),
                node(C::Reference, &[FunctionArgument]),
                node(C::Literal, &[FunctionArgument]),
            ],
        ));
    }
    spellings.push(spelling(
        "[x, ..]",
        &[
            node(C::ListBrackets, &[]),
            node(C::Reference, &[ListElement]),
            node(C::Rest, &[ListElement]),
        ],
    ));
    spellings
}

/// The collection notation (`krs_syntax::notation`), each form beside the call it denotes, which
/// its accept entry names in `same_k_as`: an index of a `Map` and of a `List`, a method of each
/// collection whose receiver its row chooses (`update` is a `Map`'s here and `len` a `List`'s),
/// and `contains_key`, whose receiver is the call's second argument. Each receiver is a builtin
/// collection term, so that it has its collection's sort wherever it stands; its nodes are in the
/// walker's order, the denoted call's.
fn notation_spellings() -> Vec<Spelling> {
    let map = || node(C::Constructor, &[FunctionArgument]);
    let x = || node(C::Reference, &[FunctionArgument]);
    let one = || node(C::Literal, &[FunctionArgument]);
    let list_of_x = || {
        [
            node(C::Constructor, &[FunctionArgument]),
            node(C::Reference, &[FunctionArgument, ListElement]),
        ]
    };
    let set_of_x = || {
        [
            node(C::Constructor, &[FunctionArgument]),
            node(C::Reference, &[FunctionArgument, SetElement]),
        ]
    };
    let index = || node(C::Notation(Notation::Index), &[]);
    let method = || node(C::Notation(Notation::CollectionMethod), &[]);
    let call = || node(C::BuiltinApplication, &[]);
    let with = |head: Node, operands: &[Node]| {
        let mut nodes = vec![head];
        nodes.extend_from_slice(operands);
        nodes
    };
    let list_index = [list_of_x().as_slice(), &[one()]].concat();
    let list_len = list_of_x();
    let set_to_list = set_of_x();
    let mut spellings = Vec::new();
    for (written, denoted, operands) in [
        (
            "k::builtin::map::empty()[x]",
            "k::builtin::map::get(k::builtin::map::empty(), x)",
            vec![map(), x()],
        ),
        (
            "k::builtin::list::item(x)[0]",
            "k::builtin::list::get(k::builtin::list::item(x), 0)",
            list_index,
        ),
        (
            "k::builtin::map::empty().update(x, 1)",
            "k::builtin::map::update(k::builtin::map::empty(), x, 1)",
            vec![map(), x(), one()],
        ),
        (
            "k::builtin::list::item(x).len()",
            "k::builtin::list::size(k::builtin::list::item(x))",
            list_len.to_vec(),
        ),
        (
            "k::builtin::set::item(x).to_list()",
            "k::builtin::set::to_list(k::builtin::set::item(x))",
            set_to_list.to_vec(),
        ),
        (
            "k::builtin::map::empty().contains_key(x)",
            "k::builtin::map::in_keys(x, k::builtin::map::empty())",
            vec![x(), map()],
        ),
    ] {
        let head = if written.ends_with(']') {
            index()
        } else {
            method()
        };
        spellings.push(Spelling {
            text: written,
            readable: None,
            nodes: with(head, &operands),
        });
        spellings.push(Spelling {
            text: denoted,
            readable: None,
            nodes: with(call(), &operands),
        });
    }
    spellings.extend(literal_spellings());
    spellings
}

/// The collection literals (`krs_syntax::is_collection_literal`), each beside the calls it
/// denotes, which its accept entry names in `same_k_as`: a map of two entries, each written over
/// the map before it; a ground map; a set of two elements, joined; a map and a set written over a
/// rest; and the values: the empty map and set, and a set's singleton. Each literal's nodes are in the walker's order, the denoted calls'.
#[expect(
    clippy::too_many_lines,
    reason = "One table of the literals and the calls they denote, node by node."
)]
fn literal_spellings() -> Vec<Spelling> {
    let at = |construct: C, depth: usize| node(construct, &vec![FunctionArgument; depth]);
    let element = |construct: C, depth: usize| {
        let mut path = vec![FunctionArgument; depth];
        path.push(SetElement);
        node(construct, &path)
    };
    let mut spellings = Vec::new();
    for (written, denoted, literal, call) in [
        (
            "map![x -> 1, 2 -> 3]",
            "k::builtin::map::update(k::builtin::map::update(k::builtin::map::empty(), x, 1), 2, 3)",
            vec![
                at(C::Notation(Notation::MapLiteral), 0),
                at(C::Notation(Notation::MapLiteral), 1),
                at(C::Notation(Notation::CollectionValue), 2),
                at(C::Reference, 2),
                at(C::Literal, 2),
                at(C::Literal, 1),
                at(C::Literal, 1),
            ],
            vec![
                at(C::BuiltinApplication, 0),
                at(C::BuiltinApplication, 1),
                at(C::Constructor, 2),
                at(C::Reference, 2),
                at(C::Literal, 2),
                at(C::Literal, 1),
                at(C::Literal, 1),
            ],
        ),
        (
            "map![x -> 1, ..k::builtin::map::empty()]",
            "k::builtin::map::update(k::builtin::map::empty(), x, 1)",
            vec![
                at(C::Notation(Notation::MapLiteral), 0),
                at(C::Constructor, 1),
                at(C::Reference, 1),
                at(C::Literal, 1),
            ],
            vec![
                at(C::BuiltinApplication, 0),
                at(C::Constructor, 1),
                at(C::Reference, 1),
                at(C::Literal, 1),
            ],
        ),
        // A ground map, which an initializer and a constant can hold whole.
        (
            "map![0 -> 1]",
            "k::builtin::map::update(k::builtin::map::empty(), 0, 1)",
            vec![
                at(C::Notation(Notation::MapLiteral), 0),
                at(C::Notation(Notation::CollectionValue), 1),
                at(C::Literal, 1),
                at(C::Literal, 1),
            ],
            vec![
                at(C::BuiltinApplication, 0),
                at(C::Constructor, 1),
                at(C::Literal, 1),
                at(C::Literal, 1),
            ],
        ),
        (
            "map![]",
            "k::builtin::map::empty()",
            vec![at(C::Notation(Notation::CollectionValue), 0)],
            vec![at(C::Constructor, 0)],
        ),
        (
            "set![x, 1]",
            "k::builtin::set::union(k::builtin::set::item(x), k::builtin::set::item(1))",
            vec![
                at(C::Notation(Notation::SetLiteral), 0),
                at(C::Notation(Notation::CollectionValue), 1),
                element(C::Reference, 1),
                at(C::Notation(Notation::CollectionValue), 1),
                element(C::Literal, 1),
            ],
            vec![
                at(C::BuiltinApplication, 0),
                at(C::Constructor, 1),
                element(C::Reference, 1),
                at(C::Constructor, 1),
                element(C::Literal, 1),
            ],
        ),
        (
            "set![x, ..k::builtin::set::empty()]",
            "k::builtin::set::union(k::builtin::set::empty(), k::builtin::set::item(x))",
            vec![
                at(C::Notation(Notation::SetLiteral), 0),
                at(C::Constructor, 1),
                at(C::Notation(Notation::CollectionValue), 1),
                element(C::Reference, 1),
            ],
            vec![
                at(C::BuiltinApplication, 0),
                at(C::Constructor, 1),
                at(C::Constructor, 1),
                element(C::Reference, 1),
            ],
        ),
        // A set's singleton, a value whose element a key or a pattern reads as `set::item`'s.
        (
            "set![x]",
            "k::builtin::set::item(x)",
            vec![
                at(C::Notation(Notation::CollectionValue), 0),
                element(C::Reference, 0),
            ],
            vec![at(C::Constructor, 0), element(C::Reference, 0)],
        ),
        (
            "set![]",
            "k::builtin::set::empty()",
            vec![at(C::Notation(Notation::CollectionValue), 0)],
            vec![at(C::Constructor, 0)],
        ),
    ] {
        spellings.push(Spelling {
            text: written,
            readable: None,
            nodes: literal,
        });
        // The map written over a rest denotes the call `m.update(x, 1)` denotes, which the
        // collection methods' spellings hold already.
        if !written.contains("..") || !written.starts_with("map!") {
            spellings.push(Spelling {
                text: denoted,
                readable: None,
                nodes: call,
            });
        }
    }
    spellings
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
    /// `z`, a name the pattern binds in a key only.
    Fresh,
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
    /// Whether alternatives in the hole are grouped: an alias's pattern binds tighter than `|`,
    /// and a `let` statement takes no alternatives ungrouped.
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
    /// Whether each case is rendered alone ([`Packaging::Alone`]).
    own_package: bool,
    /// Which of the terms and notation spellings the slot holds.
    holds: Holds,
}

/// Which of the terms and notation spellings a slot holds; the import axis's two bare variants
/// stand at every slot of depth 1.
#[derive(Clone, Copy)]
enum Holds {
    /// Every spelling.
    All,
    /// The spellings that read the name `x` (`true`) or those that do not (`false`): an alias
    /// clause's root slots, whose base binds or reads `x` around the hole, so that the clause's
    /// subject binds exactly the names its result reads. A spelling of the other reading stands
    /// at the root slot's twin; the import axis's `Hold(x)` and `Go()` stand at both, and pin the
    /// names rules there.
    ReadingX(bool),
    /// The listed spellings only: a position of one host whose construct is judged, before what
    /// stands in it, by what its head resolves to.
    Only(&'static [&'static str]),
}

impl Holds {
    fn admits(self, text: &str) -> bool {
        match self {
            Self::All => true,
            Self::ReadingX(reads) => reads_x(text) == reads,
            Self::Only(texts) => texts.contains(&text),
        }
    }
}

/// Whether a spelling reads the name `x`, outside its string literals.
fn reads_x(text: &str) -> bool {
    let mut outside = String::new();
    let mut quoted = false;
    for character in text.chars() {
        if character == '"' {
            quoted = !quoted;
        } else if !quoted {
            outside.push(character);
        }
    }
    outside
        .split(|character: char| !(character.is_alphanumeric() || character == '_'))
        .any(|word| word == "x")
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
        own_package: false,
        holds: Holds::All,
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

    /// The slot, whose cases are rules over the whole subject, each rendered alone.
    fn alone(self) -> Self {
        Self {
            own_package: true,
            ..self
        }
    }

    /// The slot, holding only the spellings `holds` admits.
    fn holding(self, holds: Holds) -> Self {
        Self { holds, ..self }
    }

    /// The slot, in a `cells!` sentence that declares `binders`.
    fn binding(self, binders: &'static [Binder]) -> Self {
        Self { binders, ..self }
    }

    /// The position `opener` opens at this host: `text` replaces the host's hole and holds the
    /// new one, `before` and `after` are the opener's nodes before and after its hole, and `hole`
    /// the openings from the opener to it.
    fn open(
        &self,
        opener: &'static str,
        text: &str,
        before: &[Node],
        hole: &[Opening],
        after: &[Node],
    ) -> Self {
        let (prefix, suffix) = text.split_once("HOLE").expect("an opener has a hole");
        let outer = |nodes: &[Node]| nodes.iter().cloned().map(Node::outer).collect();
        Self {
            form: self.form,
            position: self.position,
            opener: Some(opener),
            side: self.side,
            at: self.at,
            path: self.path.clone(),
            before: outer(before),
            after: outer(after),
            hole: hole.to_vec(),
            around: (prefix.to_owned(), suffix.to_owned()),
            groups_alternatives: matches!(opener, "as-body" | "let-pattern"),
            template: self.template.clone(),
            rustc_parses: self.rustc_parses,
            arity: self.arity,
            marker: self.marker,
            binders: self.binders,
            own_package: self.own_package,
            holds: self.holds,
        }
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
                Binder::Fresh => "z",
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

const ALIAS_SUBJECT: &str = "#[k::alias]\nfn case_TAG(k::term![Cmd::NAME(x, HOLE)]: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Hold(x)\n}\n";

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
       )
        .alone(),
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
        // A single-body `#[k::rule]` fn. Its subject's root holds the rewrite's host; a root that
        // holds no rewrite makes a rule that changes nothing (a rule of the table), and `_`, an
        // alias and an island there are the root's own mistakes.
        slot(
            "local-rule",
            "subject",
            Side::Subject,
            (LocalRule, Part::Subject, &[Argument]),
            LOCAL_RULE_SUBJECT,
        ),
        slot(
            "local-rule",
            "subject-root",
            Side::Subject,
            (LocalRule, Part::Subject, &[]),
            "#[k::rule(label = \"case-TAG\")]\nfn case_TAG(k::term![HOLE]: Term<KItem>) {}\n",
       )
        .alone(),
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
            "guard",
            Side::Guard,
            (Simplification, Part::Requires, &[]),
            concat!(
                "#[k::simplification]\n#[k::requires(HOLE)]\nfn case_TAG(k::term![Probe(Cmd::NAME(), x)",
                "]: Term<Int>) -> Term<Int> {\n",
                "    0\n}\n"
            ),
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
        // case's clause names a construct of its own, and its command is no production. An alias
        // clause also runs backwards when a result is printed, so its bases read both ways: the
        // subject holds no `_`, and the result reads every name the subject binds. A root's
        // construct is judged at a base of its own reading: one that binds `x` at the subject's
        // root beside a result that reads it, one that binds none beside `Cmd::Go()`; at the
        // result's root, one that reads `x` beside a subject that binds it, one that reads none
        // beside a subject that binds none. A desugar clause runs one way.
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
            ALIAS_SUBJECT,
        )
        .marked("#[k::alias]"),
        slot(
            "alias",
            "subject-root",
            Side::Subject,
            (Alias, Part::Subject, &[]),
            "#[k::alias]\nfn case_TAG(k::term![HOLE]: Term<KItem>) -> Term<KItem> {\n    Cmd::Go()\n}\n",
        )
        .holding(Holds::ReadingX(false)),
        slot(
            "alias",
            "subject-root-binding",
            Side::Subject,
            (Alias, Part::Subject, &[]),
            "#[k::alias]\nfn case_TAG(k::term![HOLE]: Term<KItem>) -> Term<KItem> {\n    Cmd::Hold(x)\n}\n",
        )
        .holding(Holds::ReadingX(true)),
        slot(
            "alias",
            "result-root",
            Side::Result,
            (Alias, Part::Result, &[]),
            "#[k::alias]\nfn case_TAG(k::term![Cmd::NAME(x)]: Term<Stmt>) -> Term<KItem> {\n    HOLE\n}\n",
        )
        .parsed_by_rustc()
        .arity(1)
        .marked("#[k::alias]")
        .holding(Holds::ReadingX(true)),
        slot(
            "alias",
            "result-root-ground",
            Side::Result,
            (Alias, Part::Result, &[]),
            "#[k::alias]\nfn case_TAG(k::term![Cmd::NAME()]: Term<Stmt>) -> Term<KItem> {\n    HOLE\n}\n",
        )
        .parsed_by_rustc()
        .arity(0)
        .marked("#[k::alias]")
        .holding(Holds::ReadingX(false)),
        slot(
            "alias",
            "result",
            Side::Result,
            (Alias, Part::Result, &[Argument]),
            "#[k::alias]\nfn case_TAG(k::term![Cmd::NAME(x)]: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Pair(x, HOLE)\n}\n",
        )
        .parsed_by_rustc()
        .arity(1)
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
       )
        .alone(),
        slot(
            "sort-rule",
            "subject-root-term",
            Side::Subject,
            (SortRule, Part::Subject, &[]),
            "k::rules! {\n    for KItem;\nUSES\n    case_TAG: k::term![HOLE] => Cmd::Go();\n}\n",
       )
        .alone(),
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
        // A cons list's element and a List collection's instance's child, matched as the values
        // the list holds (decision D1).
        slot(
            "readable",
            "cons-element",
            Side::Subject,
            (ReadableRule, Part::Subject, &[ListElement]),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], seq: [HOLE, ..] } => { k: [..] };\n}\n",
        ),
        slot(
            "readable",
            "collection-child",
            Side::Subject,
            (ReadableRule, Part::Subject, &[ListElement, Argument, Argument]),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], member: [Member { item: Cmd::Hold(HOLE) }, ..] } => { k: [..] };\n}\n",
        ),
        // A Set collection's instance is its element, which the set is looked up by; a Map
        // collection pairs an instance's key cell with the whole instance as the value, so both
        // its cells are matched. Both are written in braces.
        slot(
            "readable",
            "set-instance-child",
            Side::Subject,
            (
                ReadableRule,
                Part::Subject,
                &[Instance, SetElement, Argument, Argument],
            ),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], token: { Token { mark: Cmd::Hold(HOLE) }, .. } } => { k: [..] };\n}\n",
        ),
        slot(
            "readable",
            "map-key-child",
            Side::Subject,
            (ReadableRule, Part::Subject, &[Instance, Argument, Argument]),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], row: { Row { id: Cmd::Hold(HOLE), value: Cmd::Go() }, .. } } => { k: [..] };\n}\n",
        ),
        slot(
            "readable",
            "map-value-child",
            Side::Subject,
            (ReadableRule, Part::Subject, &[Instance, Argument, Argument]),
            "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, _), ..], row: { Row { id: Cmd::Go(), value: Cmd::Hold(HOLE) }, .. } } => { k: [..] };\n}\n",
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
        // An initializer whose parameter `x` is a configuration variable, which its computation
        // cell reads, so a spelling that reads `x` reads a value there, as in a sentence.
        slot(
            "init",
            "variable-item",
            Side::Initializer,
            (Initializer, Part::Value, &[ComputationItem, Argument]),
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
            ("init", "variable-item") => (variable_initializer("Cmd::Hold(HOLE)"), &[]),
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
    // A computation item's root comes before the case's command, so a pattern there can match
    // another case's command, whose rule's tail then matches the rest: each such case is rendered
    // alone.
    for slot in &mut slots {
        if slot.position == "item-root" && slot.side == Side::Subject {
            slot.own_package = true;
        }
    }
    slots.extend(openers());
    slots
}

/// An initializer whose computation cell holds `pgm` and `item`.
fn initializer(item: &str) -> String {
    format!(
        "impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt) -> Self {{\n        Self {{\n            k: k::k![pgm, {item}],\n            env: k::map![],\n            stack: list::empty(),\n            frame: Frame {{ ret: 0 }},\n            seq: Seq::Nil(),\n            pool: Pool {{ member: Member {{ item: Cmd::Go() }} }},\n            tray: Tray {{ token: Token {{ mark: Cmd::Go() }} }},\n            table: Table {{ row: Row {{ id: Cmd::Go(), value: Cmd::Go() }} }},\n        }}\n    }}\n}}\n"
    )
}

/// An initializer whose computation cell holds `pgm`, its configuration variable `x` of sort
/// `KItem`, and `item`.
fn variable_initializer(item: &str) -> String {
    format!(
        "impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt, x: KItem) -> Self {{\n        Self {{\n            k: k::k![pgm, x, {item}],\n            env: k::map![],\n            stack: list::empty(),\n            frame: Frame {{ ret: 0 }},\n            seq: Seq::Nil(),\n            pool: Pool {{ member: Member {{ item: Cmd::Go() }} }},\n            tray: Tray {{ token: Token {{ mark: Cmd::Go() }} }},\n            table: Table {{ row: Row {{ id: Cmd::Go(), value: Cmd::Go() }} }},\n        }}\n    }}\n}}\n"
    )
}

/// The positions constructs open (depth 2): each opener at one host per kind where it can stand,
/// matched (a `#[k::rule]` fn's subject), evaluated (a readable map key), built (a `for Stmt`
/// clause's result) and guard (a `#[k::rule]` fn's condition), with the single-body rule's
/// subject for a rewrite's sides and a claim's condition for a predicate's body; a set's element
/// stands in a pattern only, where its D2 reading differs from a constructor's argument.
#[expect(
    clippy::too_many_lines,
    reason = "One list of the openers and their hosts; each entry is one position."
)]
fn openers() -> Vec<Slot> {
    // An alias clause's subject, matched and built backwards: a set's concatenation there is
    // judged by its head, before the element it holds, so three elements stand for every one.
    let alias_subject = slot(
        "alias",
        "subject",
        Side::Subject,
        (Alias, Part::Subject, &[Argument]),
        ALIAS_SUBJECT,
    )
    .marked("#[k::alias]");
    let matched = slot(
        "rule",
        "subject",
        Side::Subject,
        (RuleFn, Part::Subject, &[Argument]),
        RULE_SUBJECT,
    );
    let evaluated = slot(
        "readable",
        "map-key",
        Side::Subject,
        (ReadableRule, Part::Subject, &[MapKey]),
        READABLE_MAP_KEY,
    );
    let built = slot(
        "sort-rule",
        "result",
        Side::Result,
        (SortRule, Part::Result, &[Argument]),
        SORT_RULE_RESULT,
    );
    let guard = slot(
        "rule",
        "guard",
        Side::Guard,
        (RuleFn, Part::Requires, &[]),
        RULE_GUARD,
    );
    let local = slot(
        "local-rule",
        "subject",
        Side::Subject,
        (LocalRule, Part::Subject, &[Argument]),
        LOCAL_RULE_SUBJECT,
    );
    let claim_guard = slot(
        "cells-claim",
        "guard",
        Side::Guard,
        (CellsClaim, Part::Requires, &[]),
        CELLS_CLAIM_GUARD,
    )
    .binding(&[Binder::X]);
    // A record update's base is the alias `p` of the record the subject matches.
    let update_built = slot(
        "sort-rule",
        "result",
        Side::Result,
        (SortRule, Part::Result, &[Argument]),
        "k::rules! {\n    for Stmt;\nUSES\n    case_TAG: Cmd::NAME(x, p @ Cmd::Pair { .. }) => Cmd::Hold(HOLE);\n}\n",
    );
    let update_evaluated = slot(
        "readable",
        "map-key",
        Side::Subject,
        (ReadableRule, Part::Subject, &[MapKey]),
        "k::rules! {\n    for Machine;\nUSES\n    case_TAG: { k: [Cmd::NAME(x, p @ Cmd::Pair { .. }), ..], env: { HOLE -> v, .. } } => { k: [..] };\n}\n",
    );

    let let_value = [node(C::Reference, &[LetValue])];
    let let_pattern = |host: &Slot, body: &str, result: C| {
        host.open(
            "let-pattern",
            &format!("{{ let HOLE = x; {body} }}"),
            &[node(C::Let, &[])],
            &[LetPattern],
            &[let_value[0].clone(), node(result, &[LetBody])],
        )
    };
    let let_body = |host: &Slot| {
        host.open(
            "let-body",
            "{ let y = x; HOLE }",
            &[
                node(C::Let, &[]),
                node(C::Reference, &[LetPattern]),
                let_value[0].clone(),
            ],
            &[LetBody],
            &[],
        )
    };
    let matches_pattern = |host: &Slot| {
        host.open(
            "matches-pattern",
            "k::matches!(x, HOLE)",
            &[node(C::Matches, &[]), node(C::Reference, &[MatchesSubject])],
            &[MatchesPattern],
            &[],
        )
    };
    let or_branch = |host: &Slot| {
        host.open(
            "or-branch",
            "HOLE | Cmd::Go()",
            &[node(C::Or, &[])],
            &[OrBranch],
            &[node(C::Constructor, &[OrBranch])],
        )
    };
    let as_body =
        |host: &Slot| host.open("as-body", "y @ HOLE", &[node(C::As, &[])], &[AsBody], &[]);
    let function_argument = |host: &Slot| {
        host.open(
            "function-argument",
            "Size(HOLE)",
            &[node(C::FunctionApplication, &[])],
            &[FunctionArgument],
            &[],
        )
    };
    let update_field = |host: &Slot| {
        host.open(
            "update-field",
            "Cmd::Pair { a: HOLE, ..p }",
            &[node(C::RecordUpdate, &[])],
            &[UpdateField],
            &[node(C::Reference, &[UpdateBase])],
        )
    };
    let closure_body = |host: &Slot| {
        host.open(
            "closure-body",
            "k::ml::exists(|w: Int| HOLE)",
            &[node(C::MlPredicate, &[])],
            &[PredicateBody],
            &[],
        )
    };
    // A construct beside a name the pattern binds nowhere else, which makes the key a selection:
    // in a readable key, a `cells!` key and a set's element.
    let cells_key = slot(
        "cells",
        "map-key",
        Side::Subject,
        (CellsRule, Part::Subject, &[MapKey]),
        "",
    );
    let cells_key = Slot {
        template: cells_rule(
            &format!("{CELLS_COMMAND}, env: k::configuration::Cell(k::map![HOLE -> v, ..])"),
            CELLS_TAIL,
        ),
        binders: &[Binder::X, Binder::Alias, Binder::Fresh, Binder::Value],
        ..cells_key
    };
    let beside_fresh = |host: &Slot| {
        host.open(
            "beside-fresh",
            "Cmd::Pair { a: HOLE, b: z }",
            &[node(C::Constructor, &[])],
            &[Argument],
            &[node(C::Fresh, &[Argument])],
        )
    };
    vec![
        alias_subject
            .open(
                "set-concat",
                "k::builtin::set::concat(k::builtin::set::item(x), k::builtin::set::item(HOLE))",
                &[
                    node(C::Concatenation, &[]),
                    node(C::Constructor, &[Argument]),
                    node(C::Reference, &[Argument, SetElement]),
                    node(C::Constructor, &[Argument]),
                ],
                &[Argument, SetElement],
                &[],
            )
            .holding(Holds::Only(&["x", "1", "Cmd::Hold(x)"])),
        beside_fresh(&evaluated),
        beside_fresh(&cells_key),
        matched.open(
            "set-element-beside-fresh",
            "k::builtin::set::item(Cmd::Pair { a: HOLE, b: z })",
            &[
                node(C::Constructor, &[]),
                node(C::Constructor, &[SetElement]),
            ],
            &[SetElement, Argument],
            &[node(C::Fresh, &[SetElement, Argument])],
        ),
        let_pattern(&built, "x", C::Reference),
        let_pattern(&guard, "true", C::Literal),
        let_pattern(&evaluated, "x", C::Reference),
        let_body(&built),
        let_body(&guard),
        let_body(&evaluated),
        matches_pattern(&built),
        matches_pattern(&guard),
        matches_pattern(&evaluated),
        local.open(
            "rewrite-left",
            "k::rewrite!(HOLE => Cmd::Go())",
            &[node(C::Rewrite, &[])],
            &[RewriteLeft],
            &[node(C::Constructor, &[RewriteRight])],
        ),
        local.open(
            "rewrite-right",
            "k::rewrite!(_ => HOLE)",
            &[node(C::Rewrite, &[]), node(C::Wildcard, &[RewriteLeft])],
            &[RewriteRight],
            &[],
        ),
        or_branch(&matched),
        or_branch(&evaluated),
        as_body(&matched),
        as_body(&evaluated),
        function_argument(&built),
        function_argument(&evaluated),
        matched.open(
            "set-element",
            "k::builtin::set::item(HOLE)",
            &[node(C::Constructor, &[])],
            &[SetElement],
            &[],
        ),
        update_field(&update_built),
        update_field(&update_evaluated),
        closure_body(&guard),
        closure_body(&claim_guard),
    ]
}

/// The term family: every slot × every construct, the import axis: every slot of depth 1 × 2
/// bare variants, and the notation family: every slot × the collection notation and its calls.
pub(super) fn cases(cases: &mut Vec<Case>) {
    let spellings = spellings();
    let imported = imported_spellings();
    let notation = notation_spellings();
    for slot in slots() {
        for spelling in &spellings {
            if slot.holds.admits(spelling.text(slot.at.form)) {
                cases.push(case(Family::Terms, &slot, spelling));
            }
        }
        for spelling in &notation {
            if slot.holds.admits(spelling.text(slot.at.form)) {
                cases.push(case(Family::Notation, &slot, spelling));
            }
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
            && spelling.nodes.first().is_some_and(|node| {
                matches!(node.construct, C::Or | C::Notation(Notation::BitwiseOr))
            });
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
    } else if slot.own_package {
        Packaging::Alone(command)
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

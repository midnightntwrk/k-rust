//! IMP in the proposed KRS **authoring surface** (layer 1).
//!
//! This file is a visualization, not compiling code: it renders what the M4
//! IMP port (`tests/m4/rust-definition/src/imp.rs`, 522 lines) would look
//! like if the authoring-layer constructs proposed in `draft/readability/`
//! were built, composed per 08's two-surface strategy. Every construct here
//! is defined by its expansion to the explicit reference surface — see
//! `imp.expanded.rs` in this directory, which is what `krs expand` would
//! show. Nothing here changes the IR or the semantics; the oracle is still
//! `../../fixtures/imp.k` over the M3B expression/calculation theory.
//!
//! Constructs from the proposal folder:
//!   [01.1] bare `KCell`/`Cell` via ordinary `use` imports
//!   [01.2] no `#[allow(unused_imports)] use k::{cells, map};` apology
//!   [01.3] bare `#[k::strict]`/`#[k::seqstrict]` defaults (layer-1 spelling)
//!   [01.4] bare-ident `group = stmt` (layer-1 spelling)
//!   [01.6] `k::subsorts!` one-line-per-edge block
//!   [02a]  associativity folded into the precedence chain (layer-1 spelling)
//!   [02b]  `#[k::tier]` precedence tiers inside a `#[k::constructors]` enum
//!   [03a]  unmentioned cells framed implicitly
//!   [03b]  anonymous shared tail: bare `..` in pattern and result
//!   [03c]  binder sorts inferred; explicit params required where they narrow
//!   [03d]  in-place `=>` rewrites inside `cells!`; `()` right side = K's `.K`
//!   [04]   `k::rules!` — one named line per simple term rewrite
//!
//! Revisions from the first review round (rationale in README §"Round 2"):
//!   [r2a] productions lead with their concrete syntax:
//!         `#[k::syntax(Sort = "…", group = …, avoid)]` is always the first
//!         attribute, so a grammar scans as a column of templates — K's own
//!         reading order (`syntax Stmt ::= "…" [attributes]`)
//!   [r2b] pretty-printing defaults to the syntax template's own spacing; an
//!         explicit `#[k::format("…")]` (named placeholders plus `%n`/`%i`/
//!         `%d` layout codes) appears only where layout differs
//!   [r2c] K's map-update sugar `e [ k <- v ]` is gone; the builtin is an
//!         ordinary term function `map::update(e, k, v)`, like `int::add`
//!   [r2d] map entries spell `k -> v`; `=>` is reserved for rewrites

use k::Term;
use k::builtin::{Bool, Id, Int, KSequence, Map, bool, int, map};
use k::configuration::{Cell, KCell};

// ---------------------------------------------------------------------------
// Sorts (expr.k EXPR-SYNTAX)
// ---------------------------------------------------------------------------

#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait KResult {}

#[k::sort]
#[k::bracket("({value})")]
pub trait Expr {}

#[k::sort]
pub trait Value: Expr + KResult {}

#[k::sort]
pub trait Stmt {}

// One line per subsort edge. The Rust marker impls these require (`KItem`,
// `KResult`, `Expr` are supertraits of `Value`) are generated; the expansion
// shows them explicitly. [01.6]
k::subsorts! {
    Int: Value;
    Bool: Value;
    Id: Expr;   // calc.k's `syntax Expr ::= Id`
}

// ---------------------------------------------------------------------------
// Expression grammar (expr.k:13-32)
//
// Variant order *is* grammar structure, exactly like K's syntax block:
// `#[k::tier(..)]` opens a new, weaker precedence tier (K's `> left:`) and
// variant adjacency continues the current tier (K's `|`). No group strings,
// no separate precedence/associativity blocks — "does `+` bind tighter than
// `==`?" is answered by vertical position. [02b]
//
// Bare `#[k::strict]`/`#[k::seqstrict]` default to "all fields, declaration
// order" and to the definition's strictness-result sort (`KResult`), as in
// K; partial strictness stays explicit (`&&`, `||`). [01.3] The templates'
// spacing is also the pretty-print format — `"-{value}"` prints without a
// space — so no production here needs a format attribute. [r2b]
// ---------------------------------------------------------------------------

#[k::constructors(sort = Expr, result = KResult)]
#[rustfmt::skip] // keep the table layout: one production per line pair
pub enum Op {
    #[k::tier] // tightest
    #[k::syntax("-{value}")] #[k::strict]
    Neg { value: Term<dyn Expr> },
    #[k::syntax("!{value}")] #[k::strict]
    Not { value: Term<dyn Expr> },

    #[k::tier(left)]
    #[k::syntax("{lhs} * {rhs}")] #[k::seqstrict]
    Mul { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} / {rhs}")] #[k::seqstrict]
    Div { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::tier(left)]
    #[k::syntax("{lhs} + {rhs}")] #[k::seqstrict]
    Add { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} - {rhs}")] #[k::seqstrict]
    Sub { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::tier(left)]
    #[k::syntax("{lhs} >= {rhs}")] #[k::seqstrict]
    Ge { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} > {rhs}")] #[k::seqstrict]
    Gt { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} <= {rhs}")] #[k::seqstrict]
    Le { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} < {rhs}")] #[k::seqstrict]
    Lt { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::tier(left)]
    #[k::syntax("{lhs} == {rhs}")] #[k::seqstrict]
    Eq { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} != {rhs}")] #[k::seqstrict]
    Ne { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::tier(left)]
    #[k::syntax("{lhs} && {rhs}")] #[k::strict(sequence = [lhs])]
    And { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::tier(left)]
    #[k::syntax("{lhs} || {rhs}")] #[k::strict(sequence = [lhs])]
    Or { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
}

// ---------------------------------------------------------------------------
// Statement grammar (calc.k CALC-SYNTAX + imp.k IMP-SYNTAX)
//
// Kept as per-production structs *on purpose*: the family is small, its
// productions carry individual doc comments and flags, and the rules below
// then refer to the heads unqualified. Tiered enum (above) and struct form
// (here) are both layer-1 options; the working style guidance is "enum for
// operator tables, structs for statement-shaped grammars". [02b §closed]
//
// Every production leads with `#[k::syntax(Stmt = "…")]`: the concrete
// syntax is the first thing on every item, so this section scans as a
// column of templates. [r2a] Template spacing is the pretty-print default;
// only `Sequence` and `Block` have real layout to declare. [r2b]
// ---------------------------------------------------------------------------

#[k::syntax(Stmt = "{name} = {value};", group = stmt)]
#[k::strict(sequence = [value])]
pub struct Assign {
    pub name: Term<Id>,
    pub value: Term<dyn Expr>,
}

// K's group name is `seq-stmt`; KRS groups are Rust idents.
#[k::syntax(Stmt = "{first} {second}", group = seq_stmt)]
#[k::format("{first}%n{second}")]
pub struct Sequence {
    pub first: Term<dyn Stmt>,
    pub second: Term<dyn Stmt>,
}

/// Dangling else: `avoid` makes the parser prefer the `IfThen` reading.
#[k::syntax(Stmt = "if ({condition}) {then_branch} else {else_branch}", group = stmt, avoid)]
#[k::strict(sequence = [condition])]
pub struct IfThenElse {
    pub condition: Term<dyn Expr>,
    pub then_branch: Term<dyn Stmt>,
    pub else_branch: Term<dyn Stmt>,
}

#[k::syntax(Stmt = "if ({condition}) {body}", group = stmt)]
pub struct IfThen {
    pub condition: Term<dyn Expr>,
    pub body: Term<dyn Stmt>,
}

/// Deliberately not strict: the `[while]` rule unfolds the loop instead.
#[k::syntax(Stmt = "while ({condition}) {body}", group = stmt)]
pub struct While {
    pub condition: Term<dyn Expr>,
    pub body: Term<dyn Stmt>,
}

#[k::syntax(Stmt = "{{{body}}}", group = stmt)]
#[k::format("{{%i%n{body}%d%n}}")]
pub struct Block {
    pub body: Term<dyn Stmt>,
}

#[k::syntax(Stmt = "{{}}", group = stmt)]
pub struct EmptyBlock;

// calc.k's `syntax priority stmt > seq-stmt`, with the tier's associativity
// stated in the same breath. [02a]
k::precedence! {
    stmt > right seq_stmt
}

// ---------------------------------------------------------------------------
// Configuration (calc.k:22-24)
// ---------------------------------------------------------------------------

/// The oracle's fixed two-cell calculation state.
#[k::configuration]
pub struct Machine {
    #[k::cell(color = "green")]
    pub k: KCell<KSequence>,
    #[k::cell(color = "yellow")]
    pub env: Cell<Map<Id, Term<dyn Value>>>,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] program: Term<dyn Stmt>,
        #[k::config_var(name = "ENV")] environment: Map<Id, Term<dyn Value>>,
    ) -> Self {
        Self {
            k: KCell::new(k::k![program]),
            env: Cell::new(environment),
        }
    }
}

// ---------------------------------------------------------------------------
// Expression rules (expr.k EXPR-RULES)
//
// One named rule per line. Clause names are the item identities (stable
// `StableItemId`s — reordering clauses changes nothing); the block is
// unordered and expands to 18 independent `#[k::rule]` fns; both sides are
// the existing pattern/term grammars over real, navigable paths. `use
// Op::*;` scopes variant names inside the block only. [04]
// ---------------------------------------------------------------------------

k::rules! {
    for Term<dyn Expr>;
    use Op::*;

    eval_neg:     Neg { value }           => int::sub(0, value);
    eval_not:     Not { value }           => bool::not(value);

    eval_add:     Add { lhs, rhs }        => int::add(lhs, rhs);
    eval_sub:     Sub { lhs, rhs }        => int::sub(lhs, rhs);
    eval_mul:     Mul { lhs, rhs }        => int::mul(lhs, rhs);
    eval_div:     Div { lhs, rhs }        => int::div(lhs, rhs);

    eval_ge:      Ge { lhs, rhs }         => int::ge(lhs, rhs);
    eval_gt:      Gt { lhs, rhs }         => int::gt(lhs, rhs);
    eval_le:      Le { lhs, rhs }         => int::le(lhs, rhs);
    eval_lt:      Lt { lhs, rhs }         => int::lt(lhs, rhs);

    eval_bool_eq: Eq { lhs, rhs }         => bool::eq(lhs, rhs);
    eval_int_eq:  Eq { lhs, rhs }         => int::eq(lhs, rhs);
    eval_bool_ne: Ne { lhs, rhs }         => bool::ne(lhs, rhs);
    eval_int_ne:  Ne { lhs, rhs }         => int::ne(lhs, rhs);

    and_true:     And { lhs: true, rhs }  => rhs;
    and_false:    And { lhs: false, .. }  => false;
    or_true:      Or { lhs: true, .. }    => true;
    or_false:     Or { lhs: false, rhs }  => rhs;
}

// ---------------------------------------------------------------------------
// Control flow (calc.k CALC + imp.k IMP)
//
// Unmentioned cells and the computation tail are framed implicitly (K's
// trailing `...`) [03a, 03b]; binder sorts are inferred from the constructor
// fields they appear under, and an explicit `Term<...>` parameter is
// *required* whenever a rule narrows a binder below its field sort — that
// is K's `V:Value`, semantic content, not documentation [03c]; the rewrite
// arrow `=>` sits inside the cell so unchanged context is written once, and
// `()` on the right is K's `.K` [03d]. `=>` always means "rewrites to";
// map entries are `k -> v` [r2d]. The two-sided pre/post fn form stays
// legal (and is the `krs expand` rendering of all of these); style guidance
// says in-place for single-focus rules, which all nine of these are.
// ---------------------------------------------------------------------------

/// `[step]`: expose the right-associated statement pair as K sequencing.
#[k::rule]
pub fn step(cells! { k: KCell(Sequence(first, second) => k![first, second], ..) }: Machine) {}

/// `[var]`: replace an identifier at the head of `k` with its mapped value.
#[k::rule]
pub fn var(
    name: Term<Id>,
    cells! {
        k: KCell(name => value, ..),
        env: Cell(map![name -> value, ..]),  // pattern only: env is unchanged
    }: Machine,
) {}

/// `[assign]`: consume a value assignment and update the environment map.
/// (`value: Term<dyn Value>` is load-bearing: without the narrowing, the
/// rule would fire on unevaluated expressions.)
#[k::rule]
pub fn assign(
    value: Term<dyn Value>,
    cells! {
        k: KCell(Assign(name, value) => (), ..),
        env: Cell(e => map::update(e, name, value)),
    }: Machine,
) {}

/// `[if-true]`: select the true branch of an evaluated conditional.
#[k::rule(label = "if-true")]
pub fn if_true(
    cells! { k: KCell(IfThenElse(true, then_branch, _) => then_branch, ..) }: Machine,
) {}

/// `[if-false]`: select the false branch of an evaluated conditional.
#[k::rule(label = "if-false")]
pub fn if_false(
    cells! { k: KCell(IfThenElse(false, _, else_branch) => else_branch, ..) }: Machine,
) {}

/// `[if-else]`: normalize the no-else form with an explicit empty branch.
#[k::rule(label = "if-else")]
pub fn if_else(
    cells! {
        k: KCell(IfThen(condition, body) => IfThenElse(condition, body, EmptyBlock()), ..),
    }: Machine,
) {}

/// `[while]`: unfold one loop test without making the constructor strict.
#[k::rule(label = "while")]
pub fn while_loop(
    cells! {
        k: KCell(
            While(condition, body)
                => IfThen(condition, Block(Sequence(body, While(condition, body)))),
            ..
        ),
    }: Machine,
) {}

/// `[block]`: expose a nonempty block body followed by an empty block.
#[k::rule(label = "block")]
pub fn block(cells! { k: KCell(Block(body) => k![body, EmptyBlock()], ..) }: Machine) {}

/// `[done]`: remove an empty block from the computation cell.
#[k::rule(label = "done")]
pub fn done(cells! { k: KCell(EmptyBlock() => (), ..) }: Machine) {}

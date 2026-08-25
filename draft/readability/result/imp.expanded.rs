//! IMP in the KRS **reference surface** (layer 2): the deterministic
//! `krs expand` rendering of `imp.rs` in this directory.
//!
//! This is what the authoring surface is *defined to mean*. Every layer-1
//! construct expands to the explicit forms below, which are — deliberately —
//! the forms of today's M4 port (`tests/m4/rust-definition/src/imp.rs`).
//! Auditors, diff tools, and agents debugging a lowering read this file;
//! humans author `imp.rs`. Identities the expansion generates rather than
//! the author writing are marked `[generated]`:
//!
//!   - tier group names (`op_tier0`..`op_tier6`) derive from the enum's item
//!     path plus tier ordinal — stable under reformatting, unlike the
//!     span-derived nonces of freestanding chain blocks (02b §expansion);
//!   - frame binders (`state`, `tail`) and map remainders (`rest`) are
//!     hygienic variables, rendered here with readable names (03a/03b);
//!   - inferred binder declarations are printed as explicit typed parameters
//!     (03c), and in-place `=>` rules are printed two-sided (03d);
//!   - each `k::rules!` clause is printed as an independent `#[k::rule]` fn
//!     whose name is the clause name (04);
//!   - `#[k::syntax(Sort = "…", …)]` production attributes print as full
//!     `#[k::constructor(sort = …, syntax = …, …)]` items (r2a), and
//!     pretty-print formats the author never wrote — derived from the
//!     syntax template's spacing (r2b) — are materialized as explicit
//!     `format = "…"` arguments wherever they differ from the
//!     space-separated default. Formats are named templates in both layers;
//!     K's positional `%N` codes are produced only at `.k` emission.
//!
//! Reference-surface conventions: fully crate-rooted paths everywhere (no
//! reliance on the author's imports), every strictness argument spelled out,
//! separate `precedence!`/`associativity!` blocks. Explicitness is this
//! layer's job; density is the other file's.

use k::Term;
use k::builtin::{Bool, Id, Int, Map, bool, int, map};
// [generated] Note: the `#[allow(unused_imports)] use k::{cells, map};`
// preamble of the old port is gone — island-macro consumption no longer
// leaks an import obligation into the definition (01.2).

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

// [generated] from `k::subsorts! { Int: Value; Bool: Value; Id: Expr; }`.
// The plain impls are the Rust marker membership `Value`'s supertraits
// require; only the `#[k::subsort]` impls declare object-language subsorts.
impl KItem for Int {}
impl KResult for Int {}
impl Expr for Int {}

#[k::subsort]
impl Value for Int {}

impl KItem for Bool {}
impl KResult for Bool {}
impl Expr for Bool {}

#[k::subsort]
impl Value for Bool {}

#[k::subsort]
impl Expr for Id {}

// ---------------------------------------------------------------------------
// Expression grammar (expr.k:13-32)
//
// The enum item survives expansion unchanged — variants are the rustc-real
// constructor identities. The `#[k::tier]` markers are gone: each variant
// now names its tier group explicitly, and the tier ordering/associativity
// appear as the freestanding chain blocks after the enum.
// ---------------------------------------------------------------------------

#[k::constructors(sort = Expr)]
pub enum Op {
    // [generated] group `op_tier0` = tier ordinal 0 of `Op` (tightest);
    // the formats are derived from the templates' spacing (no space).
    #[k::syntax("-{value}", group = "op_tier0", format = "-{value}")]
    #[k::strict(sequence = [value], result = KResult)]
    Neg { value: Term<dyn Expr> },
    #[k::syntax("!{value}", group = "op_tier0", format = "!{value}")]
    #[k::strict(sequence = [value], result = KResult)]
    Not { value: Term<dyn Expr> },

    #[k::syntax("{lhs} * {rhs}", group = "op_tier1")]
    #[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
    Mul { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} / {rhs}", group = "op_tier1")]
    #[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
    Div { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::syntax("{lhs} + {rhs}", group = "op_tier2")]
    #[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
    Add { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} - {rhs}", group = "op_tier2")]
    #[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
    Sub { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::syntax("{lhs} >= {rhs}", group = "op_tier3")]
    #[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
    Ge { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} > {rhs}", group = "op_tier3")]
    #[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
    Gt { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} <= {rhs}", group = "op_tier3")]
    #[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
    Le { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} < {rhs}", group = "op_tier3")]
    #[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
    Lt { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::syntax("{lhs} == {rhs}", group = "op_tier4")]
    #[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
    Eq { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
    #[k::syntax("{lhs} != {rhs}", group = "op_tier4")]
    #[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
    Ne { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::syntax("{lhs} && {rhs}", group = "op_tier5")]
    #[k::strict(sequence = [lhs], result = KResult)]
    And { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },

    #[k::syntax("{lhs} || {rhs}", group = "op_tier6")]
    #[k::strict(sequence = [lhs], result = KResult)]
    Or { lhs: Term<dyn Expr>, rhs: Term<dyn Expr> },
}

// [generated] from the `#[k::tier]` sequence on `Op`.
k::precedence! {
    op_tier0 > op_tier1 > op_tier2 > op_tier3 > op_tier4 > op_tier5 > op_tier6
}

// [generated] one entry per `#[k::tier(left)]`; tier 0 declared none.
k::associativity! {
    left: op_tier1;
    left: op_tier2;
    left: op_tier3;
    left: op_tier4;
    left: op_tier5;
    left: op_tier6;
}

// ---------------------------------------------------------------------------
// Statement grammar (calc.k CALC-SYNTAX + imp.k IMP-SYNTAX)
//
// The struct productions print as full `#[k::constructor]` items: groups in
// canonical string form, strictness arguments spelled in full, and every
// non-default format materialized. Formats the author never wrote (all but
// `Sequence`'s and `Block`'s) are [generated] from template spacing.
// ---------------------------------------------------------------------------

#[k::constructor(
    sort = Stmt,
    syntax = "{name} = {value};",
    group = "stmt",
    format = "{name} = {value};",
)]
#[k::strict(sequence = [value], result = KResult)]
pub struct Assign {
    pub name: Term<Id>,
    pub value: Term<dyn Expr>,
}

#[k::constructor(
    sort = Stmt,
    syntax = "{first} {second}",
    group = "seq_stmt",
    format = "{first}%n{second}",
)]
pub struct Sequence {
    pub first: Term<dyn Stmt>,
    pub second: Term<dyn Stmt>,
}

/// Dangling else: `avoid` makes the parser prefer the `IfThen` reading.
#[k::constructor(
    sort = Stmt,
    syntax = "if ({condition}) {then_branch} else {else_branch}",
    group = "stmt",
    avoid = true,
    // K's original adds a `% ` escape after the `)`; treated as a plain
    // space here, same compromise as the current M4 port.
    format = "if ({condition}) {then_branch} else {else_branch}",
)]
#[k::strict(sequence = [condition], result = KResult)]
pub struct IfThenElse {
    pub condition: Term<dyn Expr>,
    pub then_branch: Term<dyn Stmt>,
    pub else_branch: Term<dyn Stmt>,
}

#[k::constructor(
    sort = Stmt,
    syntax = "if ({condition}) {body}",
    group = "stmt",
    format = "if ({condition}) {body}",
)]
pub struct IfThen {
    pub condition: Term<dyn Expr>,
    pub body: Term<dyn Stmt>,
}

/// Deliberately not strict: the `[while]` rule unfolds the loop instead.
#[k::constructor(
    sort = Stmt,
    syntax = "while ({condition}) {body}",
    group = "stmt",
    format = "while ({condition}) {body}",
)]
pub struct While {
    pub condition: Term<dyn Expr>,
    pub body: Term<dyn Stmt>,
}

#[k::constructor(
    sort = Stmt,
    syntax = "{{{body}}}",
    group = "stmt",
    format = "{{%i%n{body}%d%n}}",
)]
pub struct Block {
    pub body: Term<dyn Stmt>,
}

#[k::constructor(
    sort = Stmt,
    syntax = "{{}}",
    group = "stmt",
    format = "{{}}",
)]
pub struct EmptyBlock;

// [generated] the merged `stmt > right seq_stmt` chain prints as the two
// canonical blocks.
k::precedence! {
    stmt > seq_stmt
}

k::associativity! {
    right: seq_stmt;
}

// ---------------------------------------------------------------------------
// Configuration (calc.k:22-24)
// ---------------------------------------------------------------------------

/// The oracle's fixed two-cell calculation state.
#[k::configuration]
pub struct Machine {
    #[k::cell(color = "green")]
    pub k: k::configuration::KCell<k::builtin::KSequence>,
    #[k::cell(color = "yellow")]
    pub env: k::configuration::Cell<Map<Id, Term<dyn Value>>>,
}

// [generated] lint hygiene is injected by `#[k::init]`, not authored (01.5).
#[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]
impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] program: Term<dyn Stmt>,
        #[k::config_var(name = "ENV")] environment: Map<Id, Term<dyn Value>>,
    ) -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![program]),
            env: k::configuration::Cell::new(environment),
        }
    }
}

// ---------------------------------------------------------------------------
// Expression rules (expr.k EXPR-RULES)
//
// [generated] each fn below is one clause of the `k::rules!` block; the
// clause name is the fn name and the `use Op::*;` scope prints as qualified
// heads.
// ---------------------------------------------------------------------------

#[k::rule]
pub fn eval_neg(Op::Neg { value }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::sub(0, value)
}

#[k::rule]
pub fn eval_not(Op::Not { value }: Term<dyn Expr>) -> Term<dyn Expr> {
    bool::not(value)
}

#[k::rule]
pub fn eval_add(Op::Add { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::add(lhs, rhs)
}

#[k::rule]
pub fn eval_sub(Op::Sub { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::sub(lhs, rhs)
}

#[k::rule]
pub fn eval_mul(Op::Mul { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::mul(lhs, rhs)
}

#[k::rule]
pub fn eval_div(Op::Div { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::div(lhs, rhs)
}

#[k::rule]
pub fn eval_ge(Op::Ge { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::ge(lhs, rhs)
}

#[k::rule]
pub fn eval_gt(Op::Gt { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::gt(lhs, rhs)
}

#[k::rule]
pub fn eval_le(Op::Le { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::le(lhs, rhs)
}

#[k::rule]
pub fn eval_lt(Op::Lt { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::lt(lhs, rhs)
}

#[k::rule]
pub fn eval_bool_eq(Op::Eq { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    bool::eq(lhs, rhs)
}

#[k::rule]
pub fn eval_int_eq(Op::Eq { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::eq(lhs, rhs)
}

#[k::rule]
pub fn eval_bool_ne(Op::Ne { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    bool::ne(lhs, rhs)
}

#[k::rule]
pub fn eval_int_ne(Op::Ne { lhs, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    int::ne(lhs, rhs)
}

#[k::rule]
pub fn and_true(Op::And { lhs: true, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    rhs
}

#[k::rule]
pub fn and_false(Op::And { lhs: false, rhs: _ }: Term<dyn Expr>) -> Term<dyn Expr> {
    false
}

#[k::rule]
pub fn or_true(Op::Or { lhs: true, rhs: _ }: Term<dyn Expr>) -> Term<dyn Expr> {
    true
}

#[k::rule]
pub fn or_false(Op::Or { lhs: false, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    rhs
}

// ---------------------------------------------------------------------------
// Control flow (calc.k CALC + imp.k IMP)
//
// [generated] every rule prints two-sided: the in-place `=>` splits into
// pattern and result (03d); the frame binders `state`/`tail`/`rest` are
// materialized (03a/03b); inferred binders print as typed parameters (03c).
// ---------------------------------------------------------------------------

/// `[step]`: expose the right-associated statement pair as K sequencing.
#[k::rule]
pub fn step(
    first: Term<dyn Stmt>,
    second: Term<dyn Stmt>,
    cells! {
        k: k::configuration::KCell(Sequence(first, second), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(first, second, ..tail),
        ..state
    }
}

/// `[var]`: replace an identifier at the head of `k` with its mapped value.
#[k::rule]
pub fn var(
    name: Term<Id>,
    value: Term<dyn Value>,
    cells! {
        k: k::configuration::KCell(name, tail @ ..),
        env: k::configuration::Cell(map![name -> value, rest @ ..]),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(value, ..tail),
        ..state
    }
}

/// `[assign]`: consume a value assignment and update the environment map.
#[k::rule]
pub fn assign(
    name: Term<Id>,
    value: Term<dyn Value>,
    e: Term<Map>,
    cells! {
        k: k::configuration::KCell(Assign(name, value), tail @ ..),
        env: k::configuration::Cell(e),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map::update(e, name, value)),
        ..state
    }
}

/// `[if-true]`: select the true branch of an evaluated conditional.
#[k::rule(label = "if-true")]
pub fn if_true(
    then_branch: Term<dyn Stmt>,
    cells! {
        k: k::configuration::KCell(IfThenElse(true, then_branch, _), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(then_branch, ..tail),
        ..state
    }
}

/// `[if-false]`: select the false branch of an evaluated conditional.
#[k::rule(label = "if-false")]
pub fn if_false(
    else_branch: Term<dyn Stmt>,
    cells! {
        k: k::configuration::KCell(IfThenElse(false, _, else_branch), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(else_branch, ..tail),
        ..state
    }
}

/// `[if-else]`: normalize the no-else form with an explicit empty branch.
#[k::rule(label = "if-else")]
pub fn if_else(
    condition: Term<dyn Expr>,
    body: Term<dyn Stmt>,
    cells! {
        k: k::configuration::KCell(IfThen(condition, body), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(IfThenElse(condition, body, EmptyBlock()), ..tail),
        ..state
    }
}

/// `[while]`: unfold one loop test without making the constructor strict.
#[k::rule(label = "while")]
pub fn while_loop(
    condition: Term<dyn Expr>,
    body: Term<dyn Stmt>,
    cells! {
        k: k::configuration::KCell(While(condition, body), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(
            IfThen(
                condition,
                Block(Sequence(body, While(condition, body)))
            ),
            ..tail
        ),
        ..state
    }
}

/// `[block]`: expose a nonempty block body followed by an empty block.
#[k::rule(label = "block")]
pub fn block(
    body: Term<dyn Stmt>,
    cells! {
        k: k::configuration::KCell(Block(body), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(body, EmptyBlock(), ..tail),
        ..state
    }
}

/// `[done]`: remove an empty block from the computation cell.
#[k::rule(label = "done")]
pub fn done(
    cells! {
        k: k::configuration::KCell(EmptyBlock(), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: k::configuration::KCell(..tail),
        ..state
    }
}

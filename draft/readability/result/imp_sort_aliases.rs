//! IMP authoring surface, **variant file** (rounds 3–5).
//!
//! Same definition as `imp.rs`, kept separate so the variants can be
//! compared against the baseline side by side. Two revisions accumulate
//! here:
//!
//!   [r3] **Sort aliases.** Each sort declaration generates a *pair* of
//!        names — a membership trait (`ExprSort`) and a type alias for the
//!        frequent spelling (`type Expr = Term<dyn ExprSort>;`) — so
//!        fields, binders, and cell payloads write `Expr`/`Stmt`/`Value`
//!        instead of `Term<dyn Expr>`/`Term<dyn Stmt>`/`Term<dyn Value>`.
//!        The wrapper survives only where the distinction is real:
//!        `Term<Id>` (a term of the closed builtin sort Id, as opposed to
//!        `Id` the builtin value type, e.g. the `Map` key). Honesty
//!        relocates as usual: hover on `Expr` shows the aliased type, and
//!        the expansion spells the traits (`#[k::sort] pub trait ExprSort
//!        {}`, `#[k::subsort] impl ValueSort for Int {}`). Known cost (see
//!        README §"Round 3"): sort recognition in the rule
//!        parser/collector becomes name-resolution-based instead of
//!        matching the `Term<…>` token shape — prototype-gated, like 03d.
//!
//!   [r4] **Co-located statement family.** The statement grammar is one
//!        `#[k::constructors]` enum, like `Op`: variant adjacency and
//!        `#[k::tier]` replace the `group = stmt` strings *and* the
//!        freestanding `k::precedence!` block (calc.k's
//!        `syntax priority stmt > seq-stmt` is the tier boundary before
//!        `Sequence`). Family enums default to the `<Sort>Syntax` naming
//!        convention when no natural family name (like `Op`) exists, since
//!        the sort itself owns the `Stmt` name; rule heads stay
//!        unqualified via `use self::StmtSyntax::*;` — proposal 04's
//!        head-resolution extension applied at module scope. See README
//!        §"Round 4".
//!
//!   [r5] **Configuration rules as match-style tables.** All rules use the
//!        `k::rules!` arm form; the fn/`cells!` spelling survives only as
//!        the reference surface. `for Stmt in k;` heads a table pinned to
//!        the head of the computation cell (K's `<k> P => R … </k>`,
//!        Redex's context-closure) — seven of the nine control-flow rules
//!        turn out to be pure term rewrites there. The two genuinely
//!        multi-cell rules match the machine directly: the k cell is a
//!        *sequence*, matched with slice patterns (`[head, ..]`, bare `..`
//!        = shared tail), the env cell is a map (`{ k -> v, .. }`),
//!        unmentioned cells are framed, and `where` carries sort
//!        narrowing. Labels default to the clause name with `_` → `-`;
//!        `r#while` names the K label `while`. Supersedes [03d]'s in-place
//!        arrow in this variant. See README §"Round 5".
//!
//! Everything else — [01.x], [02x], [03a–c], [04], [r2x] — is as in
//! `imp.rs`.

use k::Term;
use k::builtin::{Bool, Id, Int, KSequence, Map, bool, int, map};
use k::configuration::{Cell, KCell};

// ---------------------------------------------------------------------------
// Sorts (expr.k EXPR-SYNTAX)
//
// One entry per sort; each generates the trait/alias pair described above.
// Supertrait bounds are written on the sort names, as in K. [r3]
// ---------------------------------------------------------------------------

k::sorts! {
    KItem;
    KResult;
    #[k::bracket("({value})")]
    Expr;
    Value: Expr + KResult;
    Stmt;
}

// One line per subsort edge; sort names resolve to the membership traits.
// [01.6, r3]
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
// variant adjacency continues the current tier (K's `|`). [02b]
// With the sort aliases the table finally reads like an ordinary Rust AST:
// the production, not the sort spelling, dominates each line. [r3]
// ---------------------------------------------------------------------------

#[k::constructors(sort = Expr, result = KResult)]
#[rustfmt::skip] // keep the table layout: one production per line pair
pub enum Op {
    #[k::tier] // tightest
    #[k::syntax("-{value}")] #[k::strict]
    Neg { value: Expr },
    #[k::syntax("!{value}")] #[k::strict]
    Not { value: Expr },

    #[k::tier(left)]
    #[k::syntax("{lhs} * {rhs}")] #[k::seqstrict]
    Mul { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} / {rhs}")] #[k::seqstrict]
    Div { lhs: Expr, rhs: Expr },

    #[k::tier(left)]
    #[k::syntax("{lhs} + {rhs}")] #[k::seqstrict]
    Add { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} - {rhs}")] #[k::seqstrict]
    Sub { lhs: Expr, rhs: Expr },

    #[k::tier(left)]
    #[k::syntax("{lhs} >= {rhs}")] #[k::seqstrict]
    Ge { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} > {rhs}")] #[k::seqstrict]
    Gt { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} <= {rhs}")] #[k::seqstrict]
    Le { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} < {rhs}")] #[k::seqstrict]
    Lt { lhs: Expr, rhs: Expr },

    #[k::tier(left)]
    #[k::syntax("{lhs} == {rhs}")] #[k::seqstrict]
    Eq { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} != {rhs}")] #[k::seqstrict]
    Ne { lhs: Expr, rhs: Expr },

    #[k::tier(left)]
    #[k::syntax("{lhs} && {rhs}")] #[k::strict(sequence = [lhs])]
    And { lhs: Expr, rhs: Expr },

    #[k::tier(left)]
    #[k::syntax("{lhs} || {rhs}")] #[k::strict(sequence = [lhs])]
    Or { lhs: Expr, rhs: Expr },
}

// ---------------------------------------------------------------------------
// Statement grammar (calc.k CALC-SYNTAX + imp.k IMP-SYNTAX)
//
// One co-located family, exactly like K's syntax block: adjacency continues
// a tier and `#[k::tier(..)]` opens the next, weaker one, so calc.k's
// `syntax priority stmt > seq-stmt` is the tier boundary before `Sequence`
// — no group strings and no freestanding precedence block remain. [r4]
// Productions keep syntax-first attributes and spacing-derived formats
// [r2a, r2b]; `Term<Id>` stays where the term-vs-value distinction is
// real. [r3]
// ---------------------------------------------------------------------------

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip] // keep the table layout: one production per line pair
pub enum StmtSyntax {
    #[k::tier]
    #[k::syntax("{name} = {value};")] #[k::strict(sequence = [value])]
    Assign { name: Term<Id>, value: Expr },

    /// Dangling else: `avoid` makes the parser prefer the `IfThen` reading.
    #[k::syntax("if ({condition}) {then_branch} else {else_branch}", avoid)]
    #[k::strict(sequence = [condition])]
    IfThenElse { condition: Expr, then_branch: Stmt, else_branch: Stmt },

    #[k::syntax("if ({condition}) {body}")]
    IfThen { condition: Expr, body: Stmt },

    /// Deliberately not strict: the `[while]` rule unfolds the loop instead.
    #[k::syntax("while ({condition}) {body}")]
    While { condition: Expr, body: Stmt },

    #[k::syntax("{{{body}}}")] #[k::format("{{%i%n{body}%d%n}}")]
    Block { body: Stmt },

    #[k::syntax("{{}}")]
    EmptyBlock,

    #[k::tier(right)] // looser than every statement form: calc.k's `stmt > seq-stmt`
    #[k::syntax("{first} {second}")] #[k::format("{first}%n{second}")]
    Sequence { first: Stmt, second: Stmt },
}

// Dequalifies the rule heads below — the same head-resolution extension
// `k::rules!` uses for `Op`, applied at module scope. [04, r4]
use self::StmtSyntax::*;

// ---------------------------------------------------------------------------
// Configuration (calc.k:22-24)
// ---------------------------------------------------------------------------

/// The oracle's fixed two-cell calculation state.
#[k::configuration]
pub struct Machine {
    #[k::cell(color = "green")]
    pub k: KCell<KSequence>,
    #[k::cell(color = "yellow")]
    pub env: Cell<Map<Id, Value>>,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] program: Stmt,
        #[k::config_var(name = "ENV")] environment: Map<Id, Value>,
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
// One named rule per line; the block expands to 18 independent `#[k::rule]`
// fns; `use Op::*;` scopes variant names inside the block only. [04]
// ---------------------------------------------------------------------------

k::rules! {
    for Expr;
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
// One-line match-style arms, same table form as the expression rules — the
// fn/`cells!` spelling is now purely the reference surface. `for Stmt in k`
// pins every clause to the head of the computation cell (K's
// `<k> P => R … </k>`); the right side is a term, a spliced sequence
// (`k![…]`), or `()` for "nothing" (K's `.K`). Clauses are unordered and
// expand to independent named rules — overlapping clauses are a
// diagnostic, never first-wins; labels default to the clause name with
// `_` → `-` (`r#while` → K's `while`). [r5]
// ---------------------------------------------------------------------------

k::rules! {
    for Stmt in k;

    /// Expose the right-associated statement pair as K sequencing.
    step:     Sequence(s1, s2) => k![s1, s2];

    /// Select the branch of an evaluated conditional.
    if_true:  IfThenElse(true, s1, _)  => s1;
    if_false: IfThenElse(false, _, s2) => s2;

    /// Normalize the no-else form with an explicit empty branch.
    if_else:  IfThen(c, s) => IfThenElse(c, s, EmptyBlock());

    /// Unfold one loop test without making the constructor strict.
    r#while:  While(c, s) => IfThen(c, Block(Sequence(s, While(c, s))));

    /// Expose a nonempty block body followed by an empty block.
    block:    Block(s) => k![s, EmptyBlock()];

    /// Remove an empty block from the computation cell.
    done:     EmptyBlock() => ();
}

// The two rules that genuinely touch more than the k head match the
// machine itself: slice patterns for the sequence cell, map patterns for
// the environment; unmentioned cells are framed [03a], bare `..` is the
// shared tail [03b], and `where` carries the sort narrowing that K writes
// as `X:Id` / `V:Value` — load-bearing, not decoration [03c].
k::rules! {
    for Machine;

    /// Replace an identifier at the head of `k` with its mapped value.
    var: { k: [name, ..], env: { name -> value, .. } } => { k: [value, ..] }
        where name: Term<Id>;

    /// Consume a value assignment and update the environment map.
    assign: { k: [Assign(name, value), ..], env: e }
         => { k: [..], env: map::update(e, name, value) }
        where value: Value;
}

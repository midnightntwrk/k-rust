//! IMP authoring surface, **round-6 variant**.
//!
//! Same definition as `imp_sort_aliases.rs` (which accumulates rounds 3–5),
//! revised by the round-6 review: a mechanical consistency audit of the
//! variant against its own stated rules, a prior-art survey of the grammar
//! surface (LALRPOP, rust-peg, pest, rust-sitter, parse-display, rustc's
//! AST conventions), and an idiom audit of the configuration/builtins
//! sections that rounds 1–5 never touched. See README §"Round 6" for the
//! evidence behind each change. Revisions:
//!
//!   [r6a] **The evocative-Rust contract, stated once.** The rule grammar
//!         deviates from literal Rust in exactly four places, all listed
//!         here (previously only the third was documented):
//!         (1) constructor application `C(a, b)` is K-application sugar
//!             over the named-field production; arguments bind positionally
//!             in declaration order (named-field patterns would push the
//!             `while` clause to 147 columns);
//!         (2) a binder repeated within one pattern (`var`'s `name`) is an
//!             equality constraint — K's non-linear matching, not Rust's;
//!         (3) slice patterns over the k cell desugar (by-value slice
//!             patterns on `Vec` are E0508);
//!         (4) `..` on a result's slice/map is the *same* anonymous
//!             tail/remainder the pattern bound.
//!         Everything else in this file is literal Rust syntax.
//!
//!   [r6b] **Sort narrowing restated (supersedes round 3's absolute rule).**
//!         A binder's sort is inferred from all of its occurrences,
//!         including the argument sorts of builtins on the right (K's own
//!         behavior for `rule X + Y => X +Int Y`); literal patterns
//!         (`true`/`false`) are self-narrowing. An explicit `where` is
//!         required only where inference fails (`assign`'s `value: Value`)
//!         or where the narrowing is what separates two otherwise-
//!         overlapping clauses — which is why the `Eq`/`Ne` clauses now
//!         carry the `where` clauses round 5 omitted: without them the
//!         promised overlap diagnostic fires on the definition itself, and
//!         `eval_bool_eq` applied to Ints builds an ill-sorted term.
//!
//!   [r6c] **Rule-table headers defined.** `for Sort;` means K rule
//!         completion: every clause is anchored at the *head of the
//!         computation cell* with an implicit shared tail — exactly what K
//!         gives a cell-less rule. The `in k` spelling of round 5 is gone
//!         (it named the same anchor and made `for Expr;` look like a
//!         different, more permissive construct, an oracle-parity hazard).
//!         The header sort constrains the clause's *left-hand side*; the
//!         right side is a term, a spliced sequence (`k![…]`), or `()` for
//!         K's `.K` — the latter two meaningful because of the anchor.
//!         `for Machine;` heads rules that match cells beyond the k head.
//!
//!   [r6d] **`Term<…>` is gone from the authoring surface.** Round 3 kept
//!         `Term<Id>` where "the term-vs-value distinction is real: the
//!         `Map` key" — but that is precisely where it failed to typecheck
//!         (a `Term<Id>` key against the `Map<Id, _>` env). Closed builtin
//!         sorts are now self-denoting in layer 1: `Id` is the sort
//!         everywhere, and the expansion spells `Term<Id>` where the
//!         reference surface needs it. `use k::Term;` disappears.
//!
//!   [r6e] **Strictness arguments are field lists.** `strict` means "any
//!         order", so its argument cannot be named `sequence`; the
//!         attribute now mirrors K's `strict(1)`/`seqstrict(1,2)` with
//!         field names instead of positions: bare = all fields, or
//!         `#[k::strict(lhs)]` / `#[k::seqstrict(lhs, rhs)]`. The names
//!         `strict`/`seqstrict` stay (uniform K vocabulary; no Rust
//!         precedent exists to conform to; the .k review view prints them).
//!
//!   [r6f] **`<Sort>Syntax` naming kept — because sorts are open.** The
//!         round-6 survey soft-recommended rustc's `Stmt`/`StmtKind`
//!         pairing for Rust familiarity. Rejected on this design's own
//!         terms: KRS keeps sorts open (the r2 decision — traits plus
//!         subsort impls, constructors addable from any module), so a
//!         production enum is one *contribution* to a sort, never its
//!         definition, and `Kind` — rustc's name for the exhaustive
//!         discriminated union — imports exactly the wrong mental model
//!         (`Op` is already, deliberately, not all of `Expr`, and IMP's
//!         `Stmt` productions come from two source modules). `Syntax`
//!         names what the enum actually is: a block of concrete syntax
//!         contributed to the sort. Natural family names (`Op`) still
//!         win when they exist. The rustc precedent stays recorded as
//!         the counter-argument in the README.
//!
//!   [r6g] **Wrapper-free configuration.** `Cell<T>`/`KCell<KSequence>`
//!         are pure phantom markers whose information is derivable: a
//!         `#[k::cell]` field *is* a leaf cell (the attribute becomes
//!         mandatory and meaningful), and the computation cell is the one
//!         of sort `KSequence` (`KCell`'s generic admits nothing else
//!         today). Both wrappers are injected by expansion; layer 2 is
//!         unchanged. Config-var names derive from the init parameters
//!         (`pgm` → `$PGM`), and `main` defaults to the variable that
//!         initializes the computation cell — the `#[k::config_var]`
//!         parameter attributes survive only as overrides. The `Cell`
//!         name itself is kept in layer 2: it is K's own word, and the
//!         committed multiplicity family (`OptionalCell`, `SetCells`, …)
//!         is where the wrapper carries real information.
//!
//!   [r6h] **`use` scope policy.** Every `k::rules!` block imports the
//!         heads it uses, block-locally; the module-scope
//!         `use self::StmtSyntax::*;` of round 4 is gone (two families
//!         sharing a variant name would turn a shadow into a hard
//!         ambiguity at module scope).
//!
//!   [r6i] **Binder names in rules are K-style metavariables** (`c`, `s1`)
//!         by stated convention — rules are one-line tables and the
//!         constructor's field names carry the documentation. Grammar
//!         fields keep descriptive names.
//!
//!   [r7]  **Post-write-up amendments** (10-first-principles.md §9 plus
//!         review):
//!         (1) `KItem`/`KResult` are no longer declared here — they are
//!             framework sorts (the any-term sort; the evaluated-value
//!             sort), imported like `Int`/`Bool`, so `k::sorts!` declares
//!             only this language's own categories. `KItem` was unused;
//!             `KResult` is still extended through the `Value` bound.
//!         (2) `result = KResult` carries its gloss where it appears: it
//!             defines "evaluated" for the strictness attributes.
//!         (3) `#[k::bracket]` spells its delimiters directly —
//!             `#[k::bracket("(", ")")]`: this sort may be wrapped in
//!             these delimiters for grouping, producing no node. This
//!             replaces the template form `"({value})"`, whose hole named
//!             no declared field and read as opaque even to reviewers.
//!
//!   [r8]  **Two legibility fixes from review** (constructs a K-naive
//!         reader could not decode on their face):
//!         (1) `#[k::tier]` → `#[k::precedence]` / `#[k::precedence(left)]`.
//!             "Tier" named neither the domain nor the direction. The
//!             marker is now the domain word with the yacc/LALRPOP
//!             lineage (`%left`/`%right`); each marker opens a group
//!             binding weaker than the one before (the first, required,
//!             is the tightest — `// tightest` comment by convention);
//!             unmarked adjacent variants join the current group; the
//!             argument is associativity. (An intermediate attempt
//!             encoded the direction in the names, `#[k::tightest]`/
//!             `#[k::looser(..)]`; review verdict: invented ordering
//!             words read as gibberish — a recognized word half-implied
//!             beats an invented word fully-specified.)
//!         (2) `k::subsorts!` folded into `k::sorts!` as `impl` lines.
//!             `Int: Value;` was an inverted assertion; membership now
//!             reads grouped by the sort being populated, directly under
//!             its declaration: `impl Value for Int, Bool;` — elided Rust
//!             impl syntax, which the `impl` keyword keeps unambiguous
//!             next to declarations. A comma list is one impl per type in
//!             the (unchanged) expansion. Blocks stay colocatable: a
//!             feature module may carry a `k::sorts!` of just `impl`
//!             lines.
//!
//! Everything else — [01.x], [02x], [03a–c], [04], [r2x], [r3], [r4],
//! [r5] — is as in `imp.rs` and `imp_sort_aliases.rs`.

use k::KResult;
use k::builtin::{Bool, Id, Int, KSequence, Map, bool, int, map};

// ---------------------------------------------------------------------------
// Sorts (expr.k EXPR-SYNTAX)
//
// One entry per sort; each generates a membership trait (`ExprSort`) and a
// type alias for the frequent spelling (`type Expr = Term<dyn ExprSort>;`).
// Supertrait bounds are written on the sort names. [r3] Framework sorts
// (`KResult`, the evaluated-value sort) are imported, not declared. [r7]
// `#[k::bracket]` gives the sort's grouping delimiters: `(e)` parses as
// plain `e` and creates no node. [r7] `impl` lines declare membership of
// existing types, under the sort they populate. [r8]
// ---------------------------------------------------------------------------

k::sorts! {
    #[k::bracket("(", ")")]
    Expr;
    impl Expr for Id;           // a bare identifier is an expression

    Value: Expr + KResult;
    impl Value for Int, Bool;   // a value is an integer or a boolean

    Stmt;
}

// ---------------------------------------------------------------------------
// Expression grammar (expr.k:13-32)
//
// Variant order *is* grammar structure: each `#[k::precedence(..)]`
// marker opens a group binding weaker than the one before (the first is
// the tightest); unmarked adjacent variants join the current group; the
// argument is associativity, yacc's `%left`/`%right`. [02b, r8]
// Bare `#[k::strict]`/`#[k::seqstrict]` cover all fields; a field list
// (`#[k::strict(lhs)]`) restricts them — K's `strict(1)` with names. [r6e]
// `result = KResult` defines "evaluated" for those attributes: a subterm
// is done once it reaches that sort. [r7]
// ---------------------------------------------------------------------------

#[k::constructors(sort = Expr, result = KResult)]
#[rustfmt::skip] // keep the table layout: one production per line pair
pub enum Op {
    #[k::precedence] // tightest
    #[k::syntax("-{value}")] #[k::strict]
    Neg { value: Expr },
    #[k::syntax("!{value}")] #[k::strict]
    Not { value: Expr },

    #[k::precedence(left)]
    #[k::syntax("{lhs} * {rhs}")] #[k::seqstrict]
    Mul { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} / {rhs}")] #[k::seqstrict]
    Div { lhs: Expr, rhs: Expr },

    #[k::precedence(left)]
    #[k::syntax("{lhs} + {rhs}")] #[k::seqstrict]
    Add { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} - {rhs}")] #[k::seqstrict]
    Sub { lhs: Expr, rhs: Expr },

    #[k::precedence(left)]
    #[k::syntax("{lhs} >= {rhs}")] #[k::seqstrict]
    Ge { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} > {rhs}")] #[k::seqstrict]
    Gt { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} <= {rhs}")] #[k::seqstrict]
    Le { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} < {rhs}")] #[k::seqstrict]
    Lt { lhs: Expr, rhs: Expr },

    #[k::precedence(left)]
    #[k::syntax("{lhs} == {rhs}")] #[k::seqstrict]
    Eq { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} != {rhs}")] #[k::seqstrict]
    Ne { lhs: Expr, rhs: Expr },

    #[k::precedence(left)]
    #[k::syntax("{lhs} && {rhs}")] #[k::strict(lhs)]
    And { lhs: Expr, rhs: Expr },

    #[k::precedence(left)]
    #[k::syntax("{lhs} || {rhs}")] #[k::strict(lhs)]
    Or { lhs: Expr, rhs: Expr },
}

// ---------------------------------------------------------------------------
// Statement grammar (calc.k CALC-SYNTAX + imp.k IMP-SYNTAX)
//
// One co-located family: calc.k's `syntax priority stmt > seq-stmt` is
// the `#[k::precedence(right)]` boundary before `Sequence`. [r4, r8]
// [r4] `<Sort>Syntax` is the default family name when no natural name
// (like `Op`) exists — named for what the enum is, a contribution of
// concrete syntax to a sort no single enum owns (sorts are open). [r6f]
// ---------------------------------------------------------------------------

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip] // keep the table layout: one production per line pair
pub enum StmtSyntax {
    #[k::precedence] // tightest
    #[k::syntax("{name} = {value};")] #[k::strict(value)]
    Assign { name: Id, value: Expr },

    /// Dangling else: `avoid` makes the parser prefer the `IfThen` reading.
    #[k::syntax("if ({condition}) {then_branch} else {else_branch}", avoid)]
    #[k::strict(condition)]
    IfThenElse { condition: Expr, then_branch: Stmt, else_branch: Stmt },

    #[k::syntax("if ({condition}) {body}")]
    IfThen { condition: Expr, body: Stmt },

    /// Deliberately not strict: the `[while]` rule unfolds the loop instead.
    #[k::syntax("while ({condition}) {body}")]
    While { condition: Expr, body: Stmt },

    #[k::syntax("{{{body}}}")] #[k::format("{{%i%n{body}%d%n}}")]
    Block { body: Stmt },

    // Zero-field tuple variant on purpose: `EmptyBlock()` is then a legal
    // Rust pattern *and* constructor at every use site. [r6a fix]
    #[k::syntax("{{}}")]
    EmptyBlock(),

    #[k::precedence(right)] // weakest: calc.k's `stmt > seq-stmt`
    #[k::syntax("{first} {second}")] #[k::format("{first}%n{second}")]
    Sequence { first: Stmt, second: Stmt },
}

// ---------------------------------------------------------------------------
// Configuration (calc.k:22-24)
//
// A `#[k::cell]` field is a leaf cell; the computation cell is the one of
// sort `KSequence`. Wrappers (`Cell<…>`, `KCell`) belong to the expansion.
// Config-var names derive from the init parameters (`pgm` → `$PGM`), and
// the variable that initializes the computation cell is `main`. [r6g]
// ---------------------------------------------------------------------------

/// The oracle's fixed two-cell calculation state.
#[k::configuration]
pub struct Machine {
    /// K's computation cell: the continuation, head-first.
    #[k::cell(color = "green")]
    pub k: KSequence,
    #[k::cell(color = "yellow")]
    pub env: Map<Id, Value>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt, env: Map<Id, Value>) -> Self {
        Self { k: k![pgm], env }
    }
}

// ---------------------------------------------------------------------------
// Expression rules (expr.k EXPR-RULES)
//
// `for Expr;` anchors every clause at the head of the computation cell —
// K's completion of a cell-less rule — with the tail framed. [r6c]
// Binder sorts are inferred from all occurrences, including the builtins on
// the right; the `Eq`/`Ne` clauses carry the `where` narrowing that is the
// only thing separating them. [r6b] The block expands to 18 independent
// `#[k::rule]` fns named by clause; `use` is block-local. [04, r6h]
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

    eval_bool_eq: Eq { lhs, rhs }         => bool::eq(lhs, rhs)  where lhs: Bool, rhs: Bool;
    eval_int_eq:  Eq { lhs, rhs }         => int::eq(lhs, rhs)   where lhs: Int,  rhs: Int;
    eval_bool_ne: Ne { lhs, rhs }         => bool::ne(lhs, rhs)  where lhs: Bool, rhs: Bool;
    eval_int_ne:  Ne { lhs, rhs }         => int::ne(lhs, rhs)   where lhs: Int,  rhs: Int;

    and_true:     And { lhs: true, rhs }  => rhs;
    and_false:    And { lhs: false, .. }  => false;
    or_true:      Or { lhs: true, .. }    => true;
    or_false:     Or { lhs: false, rhs }  => rhs;
}

// ---------------------------------------------------------------------------
// Control flow (calc.k CALC + imp.k IMP)
//
// Same anchoring as above [r6c]: the header sort constrains the pattern;
// the right side is a Stmt, a spliced sequence (`k![…]` — K's `~>`), or
// `()` (K's `.K`). Four clauses are pure term rewrites; `step`, `block`,
// and `done` use the anchor's splice/erase forms. Clauses are unordered and
// expand to independent named rules — overlap is a diagnostic, never
// first-wins; labels default to the clause name with `_` → `-`
// (`r#while` names the K label `while`). [r5]
// ---------------------------------------------------------------------------

k::rules! {
    for Stmt;
    use StmtSyntax::*;

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

// The two rules that touch more than the k head match the machine itself:
// slice patterns for the sequence cell, map patterns for the environment.
// Unmentioned cells are framed [03a]; a cell that appears in the pattern
// but not in the result is unchanged (`var`'s env); bare `..` is the shared
// tail/remainder [03b, r6a]; a repeated binder is an equality constraint
// [r6a]; `where` carries the narrowing inference cannot supply [r6b].
k::rules! {
    for Machine;
    use StmtSyntax::Assign;

    /// Replace an identifier at the head of `k` with its mapped value.
    var: { k: [name, ..], env: { name -> value, .. } } => { k: [value, ..] }
        where name: Id;

    /// Consume a value assignment and update the environment map.
    assign: { k: [Assign(name, value), ..], env: e }
         => { k: [..], env: map::update(e, name, value) }
        where value: Value;
}

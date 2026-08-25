# The authoring surface, from first principles

This document states the end state — the authoring surface as rendered in
[`result/imp_round6.rs`](result/imp_round6.rs) — and justifies every
construct in it from first principles, for a reader who is a Rust
developer, has never seen the K framework, but knows the project's goals.
It is deliberately written *without* appealing to "K does it this way":
where a construct survives only because of the backend seam, that is said
explicitly and counted as a cost. Constructs that fail this test are
listed at the end as open work, not papered over.

The one paragraph of goals the reader is assumed to know: we want
**executable formal definitions of programming languages** — grammar and
operational semantics as one machine-checkable artifact — authored mostly
by AI agents, reviewed by humans, and executed/verified by an existing
mature rewrite engine that serves as the correctness oracle. The
definition is the spec; deviation must be mechanically impossible.

---

## 0. Five constraints that shape everything

Everything below is derived from these. They are argued in
[07-prior-art](07-prior-art.md) and [08-surface-strategy](08-surface-strategy.md);
here they are only restated.

**C1 — The surface must be real Rust, resolvable by stock tooling.**
Every verification-adjacent Rust project that embedded a foreign
expression language (Verus, Prusti, Creusot, Flux, Kani) ended up with no
completion, no goto-def, and no rename inside its specs; the only
documented escape routes are forking rust-analyzer or staying
Rust-shaped. We take the second. Consequence: every name in a definition
must be a real Rust item that `rust-analyzer` resolves — no binders
inside strings, no invented expression grammar.

**C2 — A definition is data, not code.** Nothing in a definition
executes. Grammar declarations, state declarations, and rules are
*descriptions* consumed by a collector; rule "bodies" are deleted at
expansion. Rust's type system is used as a checker and a naming/identity
service (traits, `TypeId`), not as an evaluator. This is why the surface
can afford to look like ordinary Rust while meaning something else: the
meaning is always "declare a fact," never "run this."

**C3 — Two surfaces, one meaning.** Mature spec tools converge on a
compact form for authoring and an explicit form for auditing (Verus's
block-and-attribute duality, Flux's three spellings). We build that in:
every compact construct is *defined* by its deterministic expansion to an
explicit reference surface (`krs expand`), which is itself valid,
fully-spelled-out Rust. Density lives in layer 1; total explicitness
lives in layer 2; nothing lives only in prose.

**C4 — The oracle is an external rewrite engine.** The definition lowers
to the K framework's format and runs on its verified backends. This buys
an execution engine, a symbolic executor, and a prover we do not have to
write — and costs a vocabulary seam: a handful of attribute names and one
review artifact (`.k` emission) speak the backend's language. Each such
term is a deliberate, glossed carve-out (they are inventoried in §8).

**C5 — Stable identity and provenance.** Humans and tools must be able
to point at "rule `while`" across reorderings, reformattings, and
refactors. Every production and rule is (or expands to) a named Rust
item; nothing derives identity from source position.

---

## 1. What a language definition has to say

Strip away all notation and a small-step language definition contains
exactly five kinds of facts:

1. **Syntactic categories and their unions** — "an expression is an
   integer, a boolean, a variable, or one of these operator forms";
   categories that can be *extended later* by other modules.
2. **Productions** — for each construct: its shape (fields and their
   categories), its concrete syntax, and its parse precedence.
3. **Evaluation order** — which subterms are reduced to values before
   the construct itself can step, and in what order.
4. **Machine state** — the components of a program configuration (the
   continuation, an environment, a store, …) and their initial values.
5. **Transition rules** — named, unordered rewrites: "a state matching
   *this* steps to *that*."

The surface gives each kind of fact the most native Rust spelling that
can carry it. The next five sections take them in file order, each with
the actual round-6 code, the reasoning, and the rejected alternatives.

---

## 2. Categories: marker traits, with a type alias for the term type

```rust
use k::KResult; // framework sort: "evaluated value" — imported, not declared

k::sorts! {
    #[k::bracket("(", ")")]  // Exprs may be parenthesized for grouping; no node
    Expr;
    impl Expr for Id;           // a bare identifier is an expression

    Value: Expr + KResult;
    impl Value for Int, Bool;   // a value is an integer or a boolean

    Stmt;
}
```

**Why traits.** A syntactic category ("sort") is an *open union*: the
set of expression forms must be extensible from other modules and crates
after the fact — that is what makes definitions composable and lets a
core language be extended by feature modules. Rust has exactly one
mechanism for open, post-hoc membership of types in a set: traits.
A closed `enum Expr` is the natural spelling of a *fixed* union and is
used for that (§3); the category itself must be a trait. Membership of
one category in another (`Value: Expr` — every value is an expression)
is a supertrait bound; membership of a concrete type is an `impl` line,
written directly under the sort it populates, grouped the way a reader
asks the question: "what is a `Value`?" — "an integer or a boolean."
The `impl` keyword is what lets declarations and memberships share one
block without ambiguity: the two kinds of line no longer share a shape.

**Why the terse block is still honest Rust.** `Value: Expr + KResult;`
is Rust's supertrait syntax with `trait` and `{}` elided;
`impl Value for Int, Bool;` is Rust's impl syntax with the body elided
and a comma list meaning one impl per type (`trait_set!` establishes
the block shape). The expansion spells the real items:
`#[k::sort] pub trait ExprSort {}`, `#[k::subsort] impl ValueSort for Int {}`.
Blocks are colocatable: a feature module extending a language carries
its own `k::sorts!` of just `impl` lines next to the grammar it adds.

**Why each sort gets two names.** A sort is used two ways: rarely, as a
*membership* bound; constantly, as the *type of a term of that sort* —
a dynamically-shaped tree node, `Term<dyn ExprSort>`. Measured on this
specimen, spelling the wrapper at every field made ~16% of code lines
half sort-plumbing. So the declaration generates a pair — the trait
(`ExprSort`) and an alias for the frequent job
(`type Expr = Term<dyn ExprSort>;`) — and fields read like any Rust AST:
`Mul { lhs: Expr, rhs: Expr }`. Hover shows the aliased type, so nothing
is hidden, merely defaulted. (Whether the rare name should be a suffix
or a generated `sort::Expr` module path — Rust's `fmt::Result` answer to
two-things-one-name — is open; see §9.)

**Rejected: `Term<…>` in the authoring layer at all.** Round 3 kept
`Term<Id>` where "the term/value distinction is real"; the round-6 audit
showed the one place that claim pointed at (map keys) is where it fails
to typecheck. Layer 1 now has no `Term` anywhere; the distinction lives
in the expansion, which is its natural home under C3.

---

## 3. Productions: an enum whose order is the precedence table

```rust
#[k::constructors(sort = Expr, result = KResult)]
#[rustfmt::skip]
pub enum Op {
    #[k::precedence] // tightest
    #[k::syntax("-{value}")] #[k::strict]
    Neg { value: Expr },
    ...
    #[k::precedence(left)]
    #[k::syntax("{lhs} * {rhs}")] #[k::seqstrict]
    Mul { lhs: Expr, rhs: Expr },
    #[k::syntax("{lhs} / {rhs}")] #[k::seqstrict]
    Div { lhs: Expr, rhs: Expr },
    ...
}
```

**Why an enum.** An enum of struct variants is how every Rust developer
already writes an AST. The variants are real constructors with named
fields — patterns in rules resolve to them, rustdoc documents them,
rename refactors them. One deliberate difference from a plain AST: the
declaration also carries the concrete syntax and (derived from it) the
pretty-printer. That is a *conflation* — parser rule, constructor, and
printer are three artifacts — and it is chosen with eyes open: for a
definition whose whole point is that spec and implementation cannot
drift, the three artifacts must be generated from one declaration, or
the drift we exist to prevent reappears between them.

**Why the syntax is a format-string attribute.** `#[k::syntax("{lhs} * {rhs}")]`
is `std::format!` syntax with named placeholders bound to the variant's
fields — the exact design of `parse-display`, which derives both
`Display` and `FromStr` from one `#[display("{a}__{b}")]` template, and
of `thiserror`'s `#[error("{field}")]`. Escaping is std's (`"{{{body}}}"`
is literally what `format!` prints a braced value with — verified, not
assumed). The known limitation of string templates — no IDE support
*inside* the literal on stable Rust — is fenced by construction: every
placeholder must name a field of the variant, exactly once, checked at
expansion, so a stale rename is a compile error on the template rather
than silent breakage. Constraints beyond structure never go inside the
string (parse-display layers its regexes as sibling field attributes;
our equivalent, the hole's category, is already the field's type).

**Why precedence is positional.** Each `#[k::precedence(..)]` marker
opens a group binding weaker than the one before (the first, required,
is the tightest); adjacent unmarked variants join the current group;
the argument is associativity, in yacc's `%left`/`%right` sense. The
alternative — explicit numeric levels — was surveyed and loses on the
evidence:
rust-peg's `precedence!{}` (`--` separators) and pest's `PrattParser`
(`.op()` call order) are purely positional; LALRPOP's
`#[precedence(level="N")]` turns out to be positional in disguise
(un-annotated alternatives inherit the previous level, and collected
levels are sorted and deduplicated — the number carries nothing position
doesn't); only rust-sitter is truly numeric, inheriting that from
tree-sitter's C API. Rust developers already accept declaration order as
semantics in load-bearing places (derived `Ord`, discriminants, `match`
arms, `serde(untagged)`). The marker is named for the *domain*, not the
direction: an experiment with direction-carrying names
(`#[k::tightest]`/`#[k::looser]`) failed review — invented ordering
words read as gibberish, while `precedence` carries the yacc/LALRPOP
lineage every grammar author knows; a recognized word half-implied
beats an invented word fully-specified. What the name leaves implicit
is rustdoc's job, stated loudly: direction (first = tightest, matching
K and LALRPOP, the *inverse* of pest and rust-peg), the marker's scope
(it relates groups, not the variant it sits on), and `left` =
left-associative. Fusing associativity into the marker avoids a real
LALRPOP footgun (its separate `#[assoc]` silently resets at each new
level). The honest cost: moving a variant
across a group boundary is a silent grammar change in this file —
mitigated because the expansion (`group = "op_tierN"`) and the emitted
grammar make it a visible diff in review, plus a golden test for exactly
that reorder.

**Why a family enum doesn't own its sort.** `Op` is *not* all of `Expr`
— `Int`, `Bool`, and `Id` reach `Expr` through §2's membership edges,
and other modules may add more forms later. An enum here is a
*contribution* of productions to an open sort, never its definition.
That is why the default family name is `<Sort>Syntax` (a block of
concrete syntax contributed to `Stmt`) and not rustc's `<Sort>Kind`:
`Kind` names the exhaustive discriminated union that *is* the type, and
its familiarity would teach precisely the wrong model. Natural family
names (`Op`) win when they exist.

---

## 4. Evaluation order: two attributes instead of hand-written plumbing

```rust
#[k::syntax("{lhs} + {rhs}")] #[k::seqstrict]
Add { lhs: Expr, rhs: Expr },

#[k::syntax("{lhs} && {rhs}")] #[k::strict(lhs)]
And { lhs: Expr, rhs: Expr },
```

**The fact being declared.** In a small-step semantics, `Add` cannot
step until both operands are values; `&&` must evaluate only its left
operand (short-circuit). Written by hand — in any Rust interpreter, or
in structural operational semantics — this is congruence-rule plumbing:
"to evaluate `a + b`, first focus `a`, remember the context `_ + b`,
evaluate to a value, plug it back, repeat for `b`." Every construct
needs it; almost none of it is interesting. The attribute generates it:
`#[k::seqstrict]` means "evaluate all fields, left to right, before this
construct rewrites"; `#[k::strict]` means "evaluate them in any order" —
the extra freedom Rust expressions themselves don't have (Rust fixes
left-to-right; the unordered variant is what admits parallel and
symbolic evaluation). A field list restricts the set:
`#[k::strict(lhs)]` is short-circuit `&&` in one token. "Evaluated" is
defined as "reached the `result` sort named on the container"
(`result = KResult` — values, §2). Constructs that must *not* evaluate
a subterm simply omit the attribute (`While` — the loop unfolds
syntactically instead; its doc comment says so).

**The names are a seam carve-out.** `strict`/`seqstrict` are the
backend's terms for exactly these two annotations, and the generated
review artifact prints them; renaming to something self-describing
(`#[k::eval(order = ...)]`) would leave the project half-translated,
with every attribute a guess about which dictionary to look it up in.
This is a justified cost under C4, not a first-principles win — it is
inventoried as such in §8, and the mitigation is real: the attribute's
rustdoc (which hover shows — attribute names being one thing stock
rust-analyzer *does* resolve) leads with the one-line Rust-relative
gloss above.

---

## 5. Machine state: a plain struct, one field per component

```rust
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
```

**Why a struct of plain fields.** "Which components make up a program
state" is a question Rust answers with a struct; the hand-written
precedents (minirust's machine state, revm, every CEK interpreter) do
exactly this, with no wrapper types. Each field is one state component
("cell"): a name, a content type, presentation metadata. Earlier
iterations wrapped every field (`Cell<Map<…>>`, `KCell<KSequence>`);
inspection of the implementation showed both wrappers are zero-sized
phantom markers whose entire information content is derivable — so the
authoring layer drops them and the expansion injects them. Wrapper
types return only where they carry real information the field type
cannot (multiplicity: an optional cell, a set of per-thread cells).

**The `k` field is the continuation.** One component is universal: the
sequence of things left to do — the continuation stack of a CEK
machine, spelled head-first. Its content type `KSequence` and the
splice `k![pgm]` (build a continuation from these terms) are the
machine's native vocabulary for it; the field's one-line doc comment
carries the CEK gloss. The short name `k` is load-bearing beyond
brevity: it is the emitted component name in the oracle artifact and
the anchor the rule tables address (§6).

**Initialization is a real (checked, inert) function.** The `init` fn
maps external inputs — the program, an initial environment — to a
state. It is rustc-checked (`Self { … }` against the real field types)
but rigidly declarative: the parser rejects statements, control flow,
and mutation; it is a struct literal with names, per C2. Input names
lower to the oracle's configuration variables by derivation (`pgm` →
`$PGM`; the input that feeds the continuation is the main program), so
the common case carries zero annotations; attributes exist as
overrides. The fn form, rather than field-level `init = …` attributes,
is deliberate: realistic machines (the MIR semantics: 12 components,
11 constant initializers, fresh-value intrinsics) need an expression
position that attributes — inert token soup — cannot check.

---

## 6. Rules: named, unordered rewrites in match-arm shape

The reference form (C3's layer 2) is one attribute fn per rule — a real
named item carrying identity, docs, and provenance; the evidence from
production interpreters (wasmi and wasmtime both abandoned the big
`match` for per-rule generated handlers) says per-rule items are the
scalable shape. The authoring form compresses each rule to one line:

```rust
k::rules! {
    for Stmt;
    use StmtSyntax::*;

    /// Unfold one loop test without making the constructor strict.
    r#while:  While(c, s) => IfThen(c, Block(Sequence(s, While(c, s))));

    /// Remove an empty block from the computation cell.
    done:     EmptyBlock() => ();
}
```

**Why match-arm shape.** `name: pattern => result;` is the one
pattern-to-result construct every Rust developer reads fluently, and
one visual line per rule with a fixed arrow spine is the convergent
design of every rule-table system surveyed (Cranelift ISLE, Maude,
Redex, ascent, smlang). Two semantic differences from `match`, both
stated where the construct is defined: clauses are **unordered** (each
expands to an independent named rule; overlap is a *diagnostic*, ISLE's
posture — never silent first-match-wins), and the set is deliberately
non-exhaustive (a state no rule matches is stuck, which is meaningful).
Clause names are the rule identities (C5); `r#while` is the ordinary
Rust spelling for a keyword-named item.

**Why a header instead of per-rule state plumbing.** `for Stmt;`
declares once what every clause shares: the left side is a `Stmt`, and
the rewrite applies at the head of the continuation — the only place a
small-step rule fires. This is Redex's context-closure ("declare the
context on the arrow, not in every rule") applied to the continuation;
it is also why a right side may be a spliced sequence (`k![s1, s2]` —
replace one to-do item with two) or `()` (remove it). Under that
anchor, seven of nine control-flow rules are one-liners and four are
pure term rewrites. Rules that genuinely read or write *other* state
components match the machine itself:

```rust
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
```

Struct-pattern shape for the state, slice patterns for the sequence,
map patterns for the environment; components not mentioned are
unchanged (framing), as is a component matched but absent from the
result (`var`'s `env`). `where` carries category narrowing that
matching alone cannot: `assign`'s `value: Value` is semantics, not
annotation — without it the rule would fire on an unevaluated
right-hand side. Narrowing is otherwise *inferred* from occurrences
(the builtin on the right fixes the operands' sorts), and an explicit
`where` is also required when narrowing is all that separates two
clauses — the integer and boolean equality rules — because otherwise
the overlap diagnostic could not tell them apart, correctly.

**The deviations contract.** The rule grammar is evocative rather than
literal Rust in exactly four places, all documented as one contract in
the file header: (1) constructor application `While(c, s)` over
named-field variants — positional K-application sugar, because the
legal named-field spelling pushes the `while` rule from 72 to 147
columns and buries the rewrite under field-name noise; (2) a binder
repeated within a pattern (`var`'s `name`) is an equality constraint —
non-linear matching, which Rust patterns forbid but every rewrite
formalism needs; (3) by-value slice patterns desugar (E0508); (4) a
result-side `..` is the *same* tail the pattern bound. Everything else
is literal Rust. The alternatives to this contract are strictly worse
on the project's own constraints: full legality explodes the tables
(and was measured doing so); full string-DSL freedom loses C1
entirely (egg's documented failure mode: pattern variables inside
strings, unchecked, untooled — its successor abandoned embedding
altogether). Four named deviations, stated once, checkable by the
expander, is the disciplined middle.

---

## 7. Builtin operations: term constructors that look like what they are

```rust
eval_add: Add { lhs, rhs } => int::add(lhs, rhs);
```

`int::add` is not a function call — nothing in a definition executes
(C2). It constructs a term naming the backend's integer-addition
operation, and it is spelled as a lowercase module path on purpose:
the module namespaces distinct operation *types* (each carrying its
`TypeId` identity — the mechanism that lets tooling resolve it and the
collector key on it), which is the live `std::str::from_utf8` shape,
not the deprecated `std::i32::MAX` one. The tempting alternatives are
rejected for honesty, not feasibility: `Int::add` associated functions
were verified to work end-to-end but make term constructors look like
ordinary inherent methods precisely where they are not; operator
overloading (`lhs + rhs`) and method sugar (`e.update(k, v)`) are
blocked on semantics — these operations are partial and symbolic, and
the boolean ones do not short-circuit, so borrowing Rust's operator
traits would promise Rust behavior the oracle does not deliver. The
visual difference between `int::add(lhs, rhs)` and native `+` *is* the
signal that this is object-language, not meta-language.

---

## 8. The honest ledger

What a skeptical Rust developer is still entitled to dislike, and what
each item costs and buys:

| Item | Cost | Why it stands |
|---|---|---|
| Brace-macro rule tables | rustfmt won't format inside; r-a heuristics only (measured, gated by LSP goldens) | rustfmt's hands-off policy is what *preserves* the table layout; blocks stay small and per-family; every clause expands to a plain fn item that has full tooling |
| Four evocative deviations (§6) | not literal Rust semantics | stated as one contract; each alternative measured worse; expander enforces them |
| `#[rustfmt::skip]` on grammar enums | opts out of formatting | the attribute-pair-per-line table *is* the readable form; a formatting policy decision, recorded |
| Seam vocabulary: `strict`, `seqstrict`, `k`, `KSequence`, `KResult`, the `.k` artifact | jargon for the K-naive reader | C4 carve-outs, inventoried; each carries a Rust-relative gloss at its declaration; renaming halves would fork the vocabulary from the review artifact |
| String syntax templates | no IDE inside the literal (stable-Rust limitation, universal) | std-format shape, field-checked at expansion so staleness is a compile error; structure never grows inside strings |
| Declaration order is semantic (tiers) | silent under reorder in layer 1 | visible in layer 2 and the emitted grammar; reorder golden test; precedented by rust-peg/pest/derived-`Ord` |

And the claim this table supports: **every remaining line of overhead
relative to a bespoke notation buys either tooling (C1), identity (C5),
or auditability (C3)** — the specimen stands at 128 code lines against
the notation-optimal 108 of the original hand-tuned definition, and
each of the 20 extra lines is accounted for by an item header or an
import.

## 9. What writing this down surfaced (deltas beyond round 6)

The test for this document was: any construct justifiable only as
inherited convention should fail loudly. Findings:

1. **`KItem;` and `KResult;` should not be declared by the definition.**
   They are framework concepts (the any-term sort; the finished-value
   sort) that every definition would re-declare identically — the audit
   already flagged that the original definition *doesn't* declare them.
   They belong in the `k::` prelude, imported like `Int` and `Bool`,
   leaving `k::sorts!` to declare only the language's own categories
   (and extend `KResult` via ordinary bounds: `Value: Expr + KResult`).
   The block stops mixing framework machinery with the language being
   defined. → **adopted (round 7)**; §2's specimen shows the result.
2. **`result = KResult` on `#[k::constructors]` needs its §4 gloss at
   the declaration site**, not in a document: it is the definition of
   "evaluated" for the strictness attributes, and nothing on the line
   says so. Attribute-rustdoc fix, same mechanism as the
   `strict`/`seqstrict` gloss. → **adopted (round 7)** as a section
   comment in the mock; becomes attribute rustdoc in the real surface.
3. **The bracket attribute was the one template whose hole named no
   field** (`#[k::bracket("({value})")]` on a sort) — and in review it
   read as opaque even to project members. Replaced by spelling the two
   delimiters directly, `#[k::bracket("(", ")")]`, which removes the
   unchecked magic name and says what the construct means. →
   **adopted (round 7)**.
4. **Two more constructs failed the on-its-face test in review, fixed
   as round 8** (they postdate the first draft of this document; §2/§3
   show the results): `#[k::tier]` named neither the domain nor the
   direction — replaced, after one failed iteration (direction-carrying
   names `tightest`/`looser` read as gibberish in review), by
   `#[k::precedence(assoc)]` markers, the domain word with the
   yacc/LALRPOP lineage; and `k::subsorts!`'s edge list (`Int: Value;`)
   read as inverted assertions — folded into `k::sorts!` as `impl`
   lines grouped under the sort they populate, the `impl` keyword
   making the one-block form unambiguous.
5. Still open from round 6, unchanged by this exercise: the default
   associativity of a group opened without an argument
   (`#[k::precedence]` on a binary-operator group — fully-associative
   like LALRPOP's default, or non-associative); `ExprSort` suffix vs
   generated
   `sort::Expr` module; sealing sorts against out-of-block impls; the
   overlap checker's mechanism (cross-table, sort-aware); the `const`
   initializer alternative to the init fn.

Nothing else failed the test: sorts-as-traits, template syntax,
positional tiers, the wrapper-free machine struct, the rule tables, and
the builtin spelling all justify without reference to the backend's
conventions; the seam carve-outs of §8 justify *through* C4.

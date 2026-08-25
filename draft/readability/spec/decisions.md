# Decision register (settled — do not re-litigate)

Every decision the readability investigation settled, stated as a rule an
implementer can follow, with one line of rationale and a citation into the
deliberation record (`draft/readability/`, cited as doc numbers, and
`draft/readability/result/README.md`, cited as round numbers `rN`) for
anyone who needs the full argument. **The citations are for rationale
only; this register is the normative statement.** If a statement here ever
contradicts the specimen `imp.rs`, the specimen wins and this file has a
bug — report it, don't guess.

## A. Architecture

- **A1 — Two surfaces.** Layer 1 (authoring, this spec's `imp.rs`) is what humans and agents write; deterministic `krs expand` projects it to the byte-exact layer-2 reference in `imp.expanded.rs`.
  Layer 2's ceremony is constitutive (stable identity and provenance anchors) and is not to be cleaned up. [08; r6]
- **A2 — Every layer-1 construct is defined by its expansion.** Valid Rust
  outer syntax, identical resolved IR, stable identities and spans. No
  layer-1 form may exist without a specified layer-2 rendering. [08]
- **A3 — The emitted `.k` is a first-class review view** (for the IMP
  specimen it is essentially the original `expr.k`/`calc.k`/`imp.k`).
  The full K-mirror DSL was rejected. [05, 05b]
- **A4 — Stay Rust-shaped.** No construct may depend on tooling that
  doesn't exist: rustc/rust-analyzer must see real items where the design
  promises them, measured by LSP goldens, never assumed. No stringly
  embedded languages beyond the checked `#[k::syntax]` templates. [07 §2]

## B. Sorts

- **B1 — `k::sorts!` declares sorts; `impl` lines declare membership.**
  `Value: Expr + KResult;` is elided supertrait syntax; `impl Value for
  Int, Bool;` is elided impl syntax, one impl per type in the expansion
  (`#[k::subsort] impl ValueSort for Int {}`). Membership sits under the
  sort it populates. The separate `k::subsorts!` block is gone. [r8.2,
  superseding r6]
- **B2 — Sort aliases.** Each sort generates a membership trait
  (`ExprSort`) and a type alias (`type Expr = Term<dyn ExprSort>;`); the
  frequent job gets the good name. `Term<…>` never appears in layer 1
  (closed builtin sorts are self-denoting); the expansion spells it. [r3,
  r6d]
- **B3 — Framework sorts are imported, not declared.** `use k::KResult;`
  — the sorts block declares only the language's own categories. [r7.1]
- **B4 — `#[k::bracket("(", ")")]`** names the sort's grouping delimiters
  directly (no template, no magic hole name); bracket delimiters are
  tight in the pretty-print default. [r7.3]

## C. Grammar

- **C1 — Enum families are the default** for all grammars
  (`#[k::constructors(sort = …, result = …)]`); per-production structs are
  the exception, reserved for productions needing standalone Rust type
  identity or their own rustdoc page. [r4]
- **C2 — Family naming**: a natural name when one exists (`Op`), else
  `<Sort>Syntax` (`StmtSyntax`). `<Sort>Kind` rejected: under the open-sort
  model an enum is a *contribution* to a sort, never its definition, and
  `Kind` teaches exactly that wrong assumption. [r4, r6f]
- **C3 — Syntax-first attribute.** `#[k::syntax("template", …)]` is always
  the production's first attribute, so a grammar section scans as a column
  of templates in K's own reading order. On structs it is the proc-macro
  driver; on enum variants an inert helper of `#[k::constructors]`. [r2a]
- **C4 — Templates use std `format!` escaping** (`"{{{body}}}"`), no KRS
  dialect; documented deviations table + did-you-mean-`{{` diagnostic.
  Placeholders name fields and are checked 1:1 against them at expansion.
  [r6 validated; existing krs-syntax behavior]
- **C5 — Template spacing is the pretty-print default.** `#[k::format]`
  exists only for real layout, as the same named-placeholder template plus
  K's layout codes (`%n`, `%i`, `%d`). Positional `%N` codes are gone from
  both layers; K codes are generated at `.k` emission. K's `% ` escape is
  treated as a plain space (accepted compromise). [r2b]
- **C6 — Strictness keeps K's names.** Bare `#[k::strict]`/`#[k::seqstrict]`
  = all fields; a field list (`#[k::strict(lhs)]`) restricts — K's
  `strict(1)` with names. `result = KResult` is hoisted onto
  `#[k::constructors]` and defines "evaluated". Discoverability lives in
  attribute rustdoc, not renaming. [r6e; r6 validated]
- **C7 — Precedence is one enum-level chain attribute.**
  `#[k::precedence((Neg, Not) > left (Mul, Div) > …)]`: elements are
  parenthesized member lists, optionally prefixed by associativity
  (`left`/`right`/`non_assoc`; bare = **no associativity constraint**,
  which is K's bare `>` — an unannotated priority block imposes no
  same-tier nesting restriction, so iterated unary `!!x` parses and
  ambiguous same-tier binary nesting surfaces as K's ambiguity error at
  the use site) and an optional group name
  (`stmt (…) > right seq_stmt (…)`; `left`/`right`/`non_assoc` reserved
  in name position). `non_assoc` maps to K's explicit non-associativity
  (`syntax non-assoc` in emitted K, equivalent to an inline `non-assoc:`
  block) and forbids members as leftmost/rightmost direct children of
  members — it is opt-in only, never the bare default: applying it to
  self-nesting tiers (unary operators, statement sorts) rejects valid programs.
  *(Corrects the earlier "bare = non-associative" wording, which was an
  unverified assumption falsified against the K manual — see resolved
  open-questions §8.)* `>` reads "binds tighter than". Checking is exhaustive
  and local: every variant appears exactly once — missing, unknown
  (did-you-mean), duplicate are hard expansion-time errors. Variant order
  in the enum body is purely presentational. Layer 2: per-variant
  `group = …` plus freestanding `precedence!`/`associativity!` blocks with
  generated (`op_tier0`…) or author-named identities; the freestanding
  `k::precedence!` chain block survives as the names-only case for
  cross-family precedence. Positional tier markers are rejected (two
  rounds of review + ecosystem survey). [r9; 11]
- **C8 — Nullary constructors are zero-field tuple variants**
  (`EmptyBlock()`) so the same spelling is a legal Rust pattern and
  constructor everywhere. [r6a]
- **C9 — Enum tables carry `#[rustfmt::skip]`** to keep the
  attribute-pair-per-line table layout (stable, intended tool; the macro
  tables don't need it). [16 §H; r round-2 item 4]
- **C10 — `avoid`** (dangling-else) and production doc comments are
  layer-1 constructs carried to layer 2 and the emitted `.k`. [r2a]

## D. Configuration

- **D1 — Wrapper-free `#[k::configuration]` struct.** `Cell<…>`/`KCell`
  belong to the expansion (they are injectable `PhantomData` markers).
  `#[k::cell]` marks leaf cells (carries metadata like `color`); the
  computation cell is the field of sort `KSequence`. [r6g]
- **D2 — The init fn stays** (`#[k::init]`), rustc-checked; config-var
  names derive from its parameters (`pgm` → `$PGM`); `main` defaults to
  the variable that initializes the computation cell. `#[k::config_var]`
  survives as override and `parser_module` carrier. [r6g]

## E. Rules

- **E1 — `k::rules!` tables; `for Sort;` is K rule completion**: every
  clause is anchored at the head of the computation cell with the tail
  framed (never unanchored context-closure — an oracle-parity hazard).
  The right side is a term, a spliced sequence `k![a, b]` (K's `~>`), or
  `()` (K's `.K`). `use` is block-local. [r5, r6c, r6h; 09]
- **E2 — Clauses are unordered and expand to independent named rules.**
  Overlap is a static diagnostic (ISLE posture), never first-wins.
  Labels default to the clause name with `_` → `-`; raw identifiers
  (`r#while`) cover K labels that are Rust keywords. [r5]
- **E3 — Binder sorts are inferred from all occurrences** (K's own
  behavior); literals self-narrow; explicit `where` narrowing is required
  exactly where inference fails or where narrowing is semantics (K's
  `V:Value` — without it a rule fires too early) or separates overlapping
  clauses (the `Eq`/`Ne` pairs). Binders are K-style metavariables by
  convention (`c`, `s1`), not descriptive names. [r6b, r6i; round-1
  item 3]
- **E4 — `=>` belongs to rewrites alone**; map entries spell `k -> v`
  (`map![name -> value, ..]`). [round-2 item 1]
- **E5 — The evocative-Rust contract** (stated deviations from literal
  Rust, documented not hidden): positional constructor application on
  named-field variants, non-linear binders (a name twice = equality
  constraint), slice patterns on the k sequence (`[head, ..]`, head-first
  — K's cons cell, not a Vec stack), result-side `..` (the framed tail).
  [r6a]
- **E6 — Builtins are term functions** (`int::add(lhs, rhs)`,
  `map::update(e, k, v)` — persistent update returning a new map); K's
  `E[X <- V]` sugar is removed from the language. Lowercase builtin
  modules (`k::builtin::{int, bool, map}`). No method-call sugar (blocked
  by r10: K functions are partial/symbolic; no Rust trait resolution in
  term position). [r2c; r6 validated]
- **E7 — Multi-cell rules are the anonymous cell record (candidate A).**
  Rules touching more than the k head use `for Machine;` with
  `{ cell: pat, … } => { cell: term, … }` — the record mirrors the
  configuration struct and the layer-2 expansion nearly 1:1 (truest to
  mechanism; easiest to debug). A cell in the pattern but absent from the
  result is unchanged (framed) — the invisible-frame convention is
  accepted, mitigated by documentation (the Verus precedent). Multi-cell
  rules are laid out multi-line, one cell per line (single-cell table
  clauses stay one-liners) — **conditional on `krs fmt` enforcing the
  layout (F1)**; the recorded fallback if that ever fails is the
  trailing-per-cell-clause form (14 §C/D). Costs accepted knowingly: no
  rustc/rust-analyzer support inside the record pattern (RFC 2584
  territory), the for-Sort/for-Machine mechanism cliff. [12, 13, 14
  §Verdict; 16]
- **E8 — The fn/`cells!` form is purely the reference surface** and the
  graduation target for rules that outgrow `pattern => result (+ where)`.
  [r5]

## F. Tooling (co-deliverables, not afterthoughts)

- **F1 — `krs fmt`, built after verusfmt.** Workspace-member binary;
  krs-syntax is its parser (one grammar — no duplication); `pretty`-crate
  Wadler layout; comments as first-class trivia; elide-and-splice rustfmt
  coexistence with the block-indent fixpoint as a tested invariant;
  `--stdin` + `--check` day one; RA `overrideCommand` delivery via a
  checked-in `rust-analyzer.toml`; in-binary idempotence check by
  default; cargo-metadata discovery; blocking CI job; four test layers +
  corpus refresh; `k::rules!` braces mandated (paren/bracket forms
  linted). Full decision with adopted/deviation lists: 16 §Verdict.
- **F2 — Overlap diagnostic.** After semantic sort inference, the compiler collects readable `HeadRule` declarations in deterministic stable-identity order and unifies their normalized configuration pre-patterns.
  The unifier is cross-table (`for Machine` can overlap `for Stmt` at the k head), sort-aware (`where` refinements separate the `Eq`/`Ne` pairs), constructor- and literal-aware, and preserves repeated-variable equality constraints.
  Two framed map-item requirements remain conservatively overlapping because distinct entries may satisfy them.
  The first overlapping pair is a typed lowering error; rule order is never a tie-breaker. [r5, r6b; resolved 2026-08-26]
- **F3 — The four method gates** every construct must pass: (1) rustc/
  rust-analyzer visibility, measured by the m1 LSP goldens; (2) the
  collector's re-parse of authored source with byte-exact provenance
  anchors; (3) the `ProvenanceRole` catalog as a frozen protocol seam;
  (4) stable item identity (no span-derived nonces in anything authors
  reorder). [readability README §Method]
- **F4 — Fail-fast expansion diagnostics** are part of every construct's
  definition (precedence-chain totality C7, template↔field agreement C4,
  reorder/rename producing compile errors not silent staleness). [r9;
  07 §1]
- **F5 — Canonical `k::rules!` layout: deterministic collapse,
  whole-table alignment.** Single-cell clauses are one line each
  after any interior source comment is normalized to leading position
  per F7; multi-cell rules never collapse — one cell per line. No
  width-based collapse heuristics. Expanded multi-cell rules use the
  normative specimen's 14 §Verdict placement: the label and opening
  pattern brace share a line; the closing pattern brace, `=>`, and
  opening result brace share a line; `where` starts its own
  clause-level line after the result. The `:`, `=>`, and `where`
  columns are aligned across the **entire `k::rules!` block**, not per
  blank-line group: concept
  separation belongs in separate `k::rules!` blocks, so sub-grouping
  implicit in whitespace is a fragile signal the formatter must not
  depend on. Blank lines between clauses are preserved verbatim as
  presentation but carry no formatter semantics. Accepted consequence:
  one long label reflows the whole table (bounded by table size — a
  table that reflows too much is a table that wants splitting); an
  edit-stability fixture pins that renaming a label changes only
  column-padding whitespace, never structure. Only the layout of
  trailing clause comments — aligned comment column or fixed gutter —
  remains for snapshot fixtures to settle. [14 §Verdict; 16 §I; user
  decision 2026-08-23, resolving open-questions §1–2]
- **F6 — Formatting is provenance-preserving re-anchoring.** After
  `krs fmt`, byte offsets are recomputed; stable identities, the
  provenance-key topology, and the semantic payload (parse equality)
  are unchanged; the new anchors are byte-exact against the formatted
  text. This invariant is a check in the formatter's test ladder,
  discharging gates F3.2/F3.4 under reformatting. [16 §I; resolving
  open-questions §3]
- **F7 — Trivia is a gap-classified facade; DSL-body comments are
  line comments only.** krs-syntax keeps `syn` and every grammar
  production unchanged; trivia (comments/whitespace) is recovered by
  classifying the byte **gaps** between proc-macro2's tokens
  (`span-locations`), with a totality assertion (tokens ∪ trivia =
  every byte — union token ranges first, doc-comment desugaring
  shares one range). One lexical authority (`trivia::lex_gaps`);
  nothing else may ever scan source for `//`. New
  `parse_*_source_with_trivia -> (Ast, TriviaTable)` entry points
  beside the untouched existing ones; trivia keyed by byte offset,
  attached to **tokens** (cedar's first-`\n` split: gap text before
  the first newline trails the left token, the rest leads the right
  token), never to AST nodes. Three in-binary oracles: ordered comment-payload
  preservation (on loss, keep the author's original bytes),
  span-blind DSL token-payload equality after re-parsing (the semantic-payload
  part of F6), idempotence — plus a UUID-injection comment fuzz
  target (dropped and reordered are distinct failures). Rowan-CST
  rewrite is the named escape hatch, triggered by a comment-placement
  handler table exceeding ~15 entries or multi-error recovery becoming
  a hard requirement.
  **Non-doc `/* */` block comments are a hard error inside DSL macro
  bodies** (`k::rules!`/`cells!`/`map!`), diagnosed by `krs fmt` and
  the collector's source re-parse (proc macros cannot see comments;
  `fmt --check` is the blocking gate, F1). Scope: DSL bodies only —
  host Rust stays rustfmt's domain; `/** */` doc comments are
  unaffected (structural, `#[doc]`). Rationale: trailing comments are
  then provably newline-free, making the attachment split exact and
  idempotent, and it deletes the inline-between-tokens, multi-line
  reindentation, and nesting failure classes outright (Zig removed
  multiline comments language-wide for this reason; cedar's clean
  model exists because it only has `//`; zero occurrences in the KRS
  corpus at decision time). A `//` comment interior to a clause is
  normalized to leading position above the clause. The gap classifier
  still lexes block comments (for good error spans), so relaxing the
  ban later is purely additive. [investigation:
  `draft/investigations/fmt-trivia-architecture/REPORT.md`; user
  decision 2026-08-23, resolving open-questions §4]

# Prior art: what other Rust-embedded DSLs teach us

Distilled from a survey of Rust DSL-embedding projects (verification tools,
grammar frameworks, rewriting engines, attribute-macro infrastructure),
keeping only what bears on the KRS surface question. Items are ordered by
how directly they affect the proposals in this folder.

## 1. String-literal templates can never get real IDE support on stable

The most consequential finding, measured empirically against thiserror's
`#[error("{field}")]` (the closest cousin of KRS's
`syntax = "{lhs} + {rhs}"`):

- `proc_macro::Literal::subspan` is **nightly-only** and its tracking issue
  (rust#54725) explicitly defers it. On stable, every span inside a string
  literal *is* the span of the whole literal (`syn::LitStr` docs say so
  outright).
- Measured rust-analyzer behavior inside `{field}`: goto-def jumps to the
  string literal itself; hover shows the macro's *generated* binding over a
  wrong-length range; completion returns null; renaming the field updates
  the field and **silently leaves the string stale**.

Consequences for KRS:

- **The current surface is better protected than thiserror, by accident of
  architecture**: KRS validates template↔field agreement at expansion time
  (every `{field}` must name a real field, used exactly once —
  `crates/krs-syntax/src/grammar.rs:28-110`), so a rust-analyzer field
  rename produces a *compile error on the stale template*, not silent
  breakage. Keep that property; add a golden test for exactly this rename
  path.
- **Never rewrite the literal.** thiserror loses rustc's sub-literal
  format-arg spans because it re-emits a modified string; a macro that
  parses/validates and emits separately keeps whatever rustc gives. KRS's
  templates are inert descriptor data today — keep them that way.
- **Do not move more meaning into strings.** This bounds proposals 02/04:
  their gains must come from relocating *item-level* structure (tiers,
  clauses), not from richer template strings. It also supplies the long-term
  question for the templates themselves: if placeholder-position tooling
  ever matters, the escape is a non-string spelling (token-list attribute
  args), not nightly `subspan`.

## 2. Nobody has IDE support inside embedded spec languages — and the field's verdict favors KRS's bet

Verified across Kani, Prusti, Creusot, Flux, and Verus: all erase or
token-munge their spec attributes under plain `cargo build`, and none get
completion/goto-def/hover inside spec expressions from stock rust-analyzer.
The universal workaround (`rust-analyzer.check.overrideCommand`) buys
diagnostics squiggles only. rust-analyzer's own trajectory offers no fix:
helper-attribute completion covers attribute *names* only ("anything can go
inside"), and verus-analyzer — a genuine r-a fork — still documents that
goto-def "may fail within requires/ensures expressions."

The honest option space the survey converges on: (a) fork rust-analyzer,
(b) ship a cooperating LSP, or (c) **keep the embedded language literally
Rust-shaped and accept the expressiveness ceiling**. KRS chose (c) at the
charter level ("every name resolves"), and the survey shows that choice is
not conservatism — it is the only lane where the tooling story actually
works today. This *raises* the value of proposals 01–03 (which stay inside
Rust item/pattern shapes) relative to 04 (function-like macro block) and is
one more nail for 05 (full DSL).

It also sharpens the gate for 03d/04: rust-analyzer heuristics over macro
input tokens are the *best available* mechanism, are strongest for
attribute-macro inputs, and must be measured (the m1 LSP goldens), never
assumed.

## 3. Dual surfaces are the convergent outcome, not a design failure

Verus began as a `verus! { }` block language and then **added** an
attribute surface (`#[verus_spec(...)]` on ordinary fns) with the stated
rationale: minimize changes to executable code, adopt incrementally,
preserve readability for non-experts. Flux ships three spellings of the
same specs. Lesson for this folder: proposal 03d's "both the two-sided fn
form and the in-place form stay legal" and 04's "simple rules in the block,
complex rules as fns" are the pattern mature tools land on. Corpus style
guidance is how you keep dual surfaces from becoming dialects.

## 4. egg/egglog: the nearest neighbors, and two specific lessons

egg's `rewrite!("assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))")` gets
K-density rules by going fully stringly-typed — no goto-def, no rename, no
type checking on pattern variables. Proposal 04 deliberately takes the
*shape* (named one-line arrow clauses) while rejecting the mechanism: both
sides of a `k::rules!` clause are real KRS grammars over real paths.

egglog (3.0, actively maintained; egg's own README now points to it) is the
closest living relative of the whole KRS project: its `(datatype ...)` is
pure sugar over an open `(sort S)` plus independently addable constructors —
K's open-sort model, in Rust, shipping. Its surface is s-expressions, so it
is no model for KRS *syntax*, but its sort/constructor core is worth reading
when KRS's semantic layer evolves, and it confirms there is no Rust-native
K competitor occupying this niche (K's real backends remain Haskell and
C++/LLVM; the KORE JSON-RPC protocol is the interop seam).

## 5. darling: the cheapest large diagnostics win

KRS parses attributes with raw `syn`. darling (the serde-attr-style derive
framework) demonstrably delivers, in one compile pass: multiple errors each
at its exact sub-attribute span, did-you-mean on unknown keys *and* unknown
values (`Unknown field: 'stricct'. Did you mean 'strict'?`), typed enums for
value sets, and presence/span-carrying wrappers (`Flag`, `SpannedValue`).
For a surface whose vocabulary is ~23 attributes with keyed arguments, this
is directly the "diagnostic compatibility" the charter promises. Whether by
adopting darling in `krs-syntax` or replicating its two disciplines —
accumulate errors instead of failing fast; keep spans on every parsed
field — this belongs in the Phase-0/1 bucket alongside proposal 01.

Two adjacent tricks worth stealing regardless:

- `#[diagnostic::on_unimplemented(message = "...")]` (stable since 1.78) on
  KRS's sort traits, so a Rust-side bound failure says "`Foo` is not a
  declared Expr production" instead of a generic trait error. Creusot
  already does this for its logic traits.
- Decide *explicitly* whether unknown attribute keys are errors (darling, K)
  or warnings (Rust's own `#[diagnostic::…]` chose warnings for
  forward-compatibility). KRS's raw-escape-hatch story suggests: errors for
  typed attributes, with `#[k::raw_attr]` as the deliberate bypass.

## 6. Attribute-namespace hazards worth recording

- Derive-helper attribute names are global and unnamespaced; collisions are
  a lint (or a hard error against builtins). KRS's `#[k::syntax]` helper on
  enum variants — currently matched by the literal path `k::syntax`
  (`crates/krs-syntax/src/enum_constructor.rs:388-394`) — sidesteps the
  worst of this by being path-qualified, but the hard-coded `k` prefix
  breaks under facade renames (noted in proposal 02b's build list). A short
  bare helper like `#[tier]` would be a collision risk; keep helpers
  path-qualified.
- `#![register_tool]` is disqualified by its own charter ("only for
  ignorable attributes"); nightly's `macro_attr` (RFC 3697) may eventually
  offer language-native attribute grammars but is not a planning basis.

## 7. Operator lexing for future spec surfaces

If KRS ever grows richer condition syntax (`requires`, claims): Creusot's
pearlite parses `==>` as glued `==` + `>` and chooses sigils that are
lexically valid but syntactically free in position (`^` prefix, `@`
postfix); anything not decomposable into Rust's pre-glued tokens (Verus's
`&&&`, `=~=`) forced Verus into a 63k-line syn fork. Constraint to remember
before inventing notation inside any island: **new operators must decompose
into Rust's token gluing.** (This is also why 03d's `=>` is safe: it is a
single Rust token.)

## 8. ungrammar's critique, aimed at K itself

rust-analyzer's ungrammar makes a point directly about K's design: the
grammar you parse with and the tree shape you program against are different
artifacts, and conflating them serves neither. K conflates them (a
production is simultaneously parser rule, term constructor, and
pretty-printer). KRS inherits the conflation deliberately — fidelity to K is
the goal — but the observation explains a chunk of Cause 1's irreducible
weight: one KRS declaration is carrying three artifacts' worth of facts
(Rust type, concrete syntax, format string). The proposals compress the
spelling; the conflation itself is K's, and out of scope.

## Out of scope, recorded for other tracks

The survey also produced findings about *building* a rewrite engine in Rust
(rowan vs cstree kind-tag width, salsa incrementality, interning patterns
from rustc, open-extensibility crates: inventory/linkme/typetag hazards
including RUSTSEC-2024-0407 and linkme's wasm/cross-crate issues). KRS
lowers to K's existing backends, so none of that binds the surface
proposals; it belongs to any future native-engine or panopticon discussion.
One item does bind today: KRS already uses `inventory` for descriptor
registration, and the survey's notes on its platform caveats (silent no-op
on unsupported platforms; undefined iteration order — harmless here because
the collector re-sorts by stable identity) are worth a line in the
implementation docs.

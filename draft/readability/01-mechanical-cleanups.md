# Proposal 01: Mechanical cleanups (no new surface concepts)

**Status: bug-class items (1.1, 1.2, 1.5) recommended unconditionally** —
they are fixes to the reference surface's implementation, they change the
baseline every other proposal is measured against, and they benefit any
authoring layer that lowers through the same expansions. **The default-style
items (1.3, 1.6's implied impls, and to a degree 1.4) are
strategy-dependent** (see 08): they make the reference surface more
implicit, which is worth it only if humans keep authoring directly in it.
Under the two-surface strategy 08 recommends, those items are instead
delivered as authoring-layer spellings that expand to today's fully
explicit forms — same reader benefit, and the reference surface stays
canonical.

## 1.1 Un-force the `k::configuration::KCell` path (implementation bug, not a style choice)

The single largest per-rule noise source — `k: k::configuration::KCell(...)`
written twice per rule — turns out to be *forced by an implementation detail*,
not by design:

- The `cells!` parser matches cell wrappers by **last path segment only**
  (`crates/krs-syntax/src/state_macro.rs:826-829`): `KCell(...)` and
  `Cell(...)` with any prefix, including none, already parse.
- But the rule expansion emits a wrapper existence check as a `use` item:
  `use #path as _;` (`crates/krs-macros/src/expand.rs:1462,1935,2207,2717`).
  A `use` path at function scope resolves from the crate/extern root, so it
  only compiles when the author spells the full crate-rooted path. Bare
  `KCell` — or any `use`-imported alias — parses and then fails the generated
  check.

**Fix:** emit the check with the path in *type position* instead of `use`
position (type paths respect lexical `use` imports), e.g. a never-called
closure parameter `|_: &#path<_>| {}` or a `PhantomData::<#path<_>>`
expression. Then authors write:

```rust
use k::configuration::{Cell, KCell};

#[k::rule(label = "done")]
pub fn done(
    cells! {
        k: KCell(EmptyBlock(), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: KCell(..tail),
        ..state
    }
}
```

`done` drops from 12 lines to 10 and, more importantly, the cell name and
payload become the optically dominant tokens. The same fix applies to the
configuration struct's field types (`KCell<KSequence>` instead of
`k::configuration::KCell<k::builtin::KSequence>` — already legal there, since
struct fields are ordinary rustc-checked positions).

## 1.2 Absorb the `#[allow(unused_imports)]` hack

imp.rs:11-14 carries:

```rust
// Whole-rule parsing consumes these compiler-owned islands before rustc's
// ordinary unused-import analysis can observe the invocations.
#[allow(unused_imports)]
use k::{cells, map};
```

This leaks the expansion strategy into every definition file. Since
`#[k::rule]` knows exactly which island macros it consumed, and it already
resolves the real facade alias via `facade_path()`
(`crates/krs-macros/src/expand.rs:4644-4658`), the expansion can emit a
reference to the *facade-qualified* macro names it consumed (or simply not
require the import at all: the macros are matched by last segment and never
actually invoked, so the `use` is pure ceremony today). Either way, the
author-visible `#[allow]` + apology comment disappears.

## 1.3 Defaults for the always-identical strictness arguments

Every strictness attribute in imp.rs spells `sequence = [<all fields in
declaration order>]` and `result = KResult`:

```rust
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
```

K's equivalents (`[seqstrict]`, result sort `KResult`) are defaults, and they
are the right defaults — in a 20-production grammar the exceptions are what
deserve ink, not the rule. Proposed:

- `#[k::seqstrict]` bare = all fields, declaration order.
- `#[k::strict]` bare = all fields, any order.
- `#[k::strict(sequence = [lhs])]` = current explicit form for partial
  strictness (`&&`, `||`, `if`).
- `result = KResult` becomes the default when the definition declares a sort
  literally named `KResult` (or via one explicit crate-level declaration,
  e.g. `#[k::sort] #[k::strictness_result] pub trait KResult {}`);
  `result = ...` stays available per-attribute for overrides.

This is a pure attribute-parser default (`crates/krs-syntax/src/grammar.rs:918-1000`);
the descriptor and IR are unchanged. The explicit form remains the reference
surface, and `krs expand` shows it — exactly the ergonomic-macro contract in
design.md.

Objection to record: the design charter values explicitness where K hides
semantics in defaults, and `result = KResult` is genuine semantic content.
Counter: the charter's own test is whether a compact spelling "hides the
feature an author most needs to notice." A result sort that is identical on
every production of the definition is not that feature; the production whose
result sort *differs* is — and it still says so explicitly.

## 1.4 Accept identifier groups: `group = additive`

Constructor attributes require `group = "additive"` (a string, validated to be
identifier-shaped — `crates/krs-syntax/src/attribute.rs:2036-2055`), while
`precedence!`/`associativity!` require bare idents. So the same name is
quoted on one side of the join and unquoted on the other, and the quotes
suggest arbitrary strings are meaningful when they are not (the emitted K
name is a hash, `krsgroup-<hash>`, `crates/krs-compiler/src/lowering.rs:536`).
Accept a bare ident in the attribute (keep the string form for
back-compat). Cosmetically small; consistency matters because Cause 2 fixes
(proposal 02) make groups more prominent, not less.

## 1.5 Move host-lint pressure into the expansion

`#[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]` on the
`Machine` impl (imp.rs:271) is the host lint system critiquing code that is
never called. Generated items should carry the necessary `#[allow]`s
themselves; declaration impls the author writes (`#[k::init]`) can have them
injected by the attribute. Authors should never write clippy attributes for
non-host semantics.

## 1.6 Subsort declarations: one line per edge

Stating "Int is a Value (and hence Expr and KResult)" currently takes four
impls (imp.rs:31-36). Two of the four (`impl KItem`, `impl KResult`) are
*ordinary Rust marker impls* carrying no K meaning — kept only so Rust-side
trait bounds line up — and the comment above them has to explain that
distinction. Two cheap improvements, either or both:

- Let `#[k::subsort]` decorate several impls at once through a small item
  macro: `k::subsorts! { Int: Value; Bool: Value; Id: Expr; }` expanding to
  the exact impls + descriptors of today's form (each edge keeps its own
  provenance anchor; the block is parsed by the same `krs-syntax` parser from
  both the macro and the collector).
- Or keep per-impl attributes but have `#[k::subsort]` on `impl Value for
  Int` *imply and generate* the supertrait marker impls that Rust requires
  (`Expr`, `KResult`, `KItem` are supertraits of `Value` — the impls are
  mechanical consequences). This deletes the two-impl preamble and its
  explanatory comment.

The second option is the more Rust-shaped one: it mirrors how a Rust reader
already thinks ("to impl Value you must impl its supertraits"), and the
generated impls are real rustc-checked items, so coherence errors still
surface at legal subsort diamonds exactly as `tests/m1/ui/src/blanket_coherence.rs`
demonstrates.

## 1.7 What stays as-is (and why)

- **`Term<dyn Expr>`** keeps its `dyn`. It is the honest Rust spelling for an
  open sort, r2 already rejected the marker-struct alternative
  (`draft/investigations/r2-open-sorts.md:395-432` — "the only material win
  is shorter `Term<Instr>` spelling"), and the rule parser's `Term`-last-
  segment contract (`crates/krs-syntax/src/rule.rs:735`) means type aliases
  can't hide it. The volume of `Term<dyn …>` mentions instead falls via
  proposals 02–04, which remove the *positions* where it must be written.
- **`format = "..."` strings.** They are optional today and only needed for
  exact K pretty-print parity; no change proposed beyond fixing the escape
  gap noted at imp.rs:211-213.
- **Explicit rule labels.** `label = "if-true"` carries real content (K
  parity, hyphens not expressible in fn names). Keep.

## Net effect on imp.rs

These cleanups alone take imp.rs from 522 lines to roughly 420 and, more
importantly, cut the *worst-line* noise: no more triple-`k::` paths inside
rule patterns, no unused-import apology, no strictness attributes wrapping to
a second line. The structural verbosity (one struct per production, frame
bindings in every rule) remains — that is what proposals 02–04 address.

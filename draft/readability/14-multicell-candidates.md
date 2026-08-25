# 14: The multi-cell rule form — candidate menu

Every candidate rendered on the **same two rules** (IMP's `var` and
`assign`, the only multi-cell rules in the specimen), so the forms can be
compared line by line. Single-cell tables (`for Stmt`, `for Expr`) are
unaffected by this choice and stay as in `result/imp_round9.rs`. Evidence
citations are one-liners into [13-multicell-rule-prior-art](13-multicell-rule-prior-art.md).

## Verdict (2026-08-21 review): A, plus an enforced formatter

Review picked **A (the anonymous cell record, status quo)**, on a
criterion the menu's pro/con lines underweighted: A is the form **most
true to what is going on** — the record mirrors the `Machine`
configuration struct and the layer-2 `cells!` expansion nearly 1:1, so
rules are the easiest to debug and work with. The round-9 critique that
triggered the pin is real but is a **layout failure, not a syntax
failure**: the same rule, one cell per line, reads fine. Compare the
one-liner form above (§A) with:

```rust
var: {
    k: [name, ..],
    env: { name -> value, .. },
} => {
    k: [value, ..],
}
where name: Id;
```

(The exact canonical layout — where `=>` and `where` sit, alignment,
when a rule may collapse back to one line — is formatter-design work,
not decided here. Single-cell table clauses must stay one-liners; that
is the tables' whole point.)

**Consequence: the readability problem converts into a tooling
requirement.** Multi-line A only beats C/D if the layout is
*guaranteed* — hand-maintained layout rots, and rustfmt categorically
never formats brace-delimited macro bodies (maintainer-confirmed, 09
§D; today that fact *preserves* hand layout, but preservation is not
enforcement). Whether/how projects ship enforced macro formatting is
the next survey — pinned in
[15-formatter-pin](15-formatter-pin.md).

Costs accepted knowingly (recorded, not disputed): no rustc/
rust-analyzer support inside the record pattern (13 §B — the `$:pat`
finding), the invisible unchanged-cell convention stays
(mitigation stays documentation, the Verus precedent, 13 §A), the
`for Sort`/`for Machine` mechanism cliff stays, and the evocative-Rust
deviations (E0529 slices, E0416 non-linear binders, map patterns)
remain items of the r6a contract. **Fallback**: if the formatter survey
concludes enforced macro formatting is not viable, C/D remain the
evidence-backed alternative; doc 13's findings are unchanged by this
verdict. *(Update, same day: the survey ran and concluded it IS viable
— decision: build `krs fmt` after verusfmt, see
[16-formatter-prior-art](16-formatter-prior-art.md) §Verdict. The
fallback clause is released; C/D stay recorded purely as the
alternative rule form.)*

---

The K original, for reference (calc.k:28-34):

```k
rule [var]:
  <k> X:Id => V ... </k>
  <env> X |-> V ... </env>

rule [assign]:
  <k> X = V:Value ; => .K ... </k>
  <env> E => E [ X <- V ] </env>
```

---

## A. Status quo (round 6/9): anonymous cell record

```rust
k::rules! {
    for Machine;
    use StmtSyntax::Assign;

    var: { k: [name, ..], env: { name -> value, .. } } => { k: [value, ..] }
        where name: Id;

    assign: { k: [Assign(name, value), ..], env: e }
         => { k: [..], env: map::update(e, name, value) }
        where value: Value;
}
```

- The `{ … }` record is RFC 2584 — syntax Rust specified and declined
  (13 §B); pattern side can never be a real Rust pattern (`$:pat` rejects
  it), so no rustc parsing/diagnostics/rename.
- "Cell in pattern but absent from result = unchanged" is invisible.
- Separate form from `for Sort;` — the mechanism cliff.

## B. Named struct pattern with an explicit frame base (`..pre`)

```rust
k::rules! {
    for Machine;
    use StmtSyntax::Assign;

    var: Machine { k: [name, ..], env: map![name -> value, ..] }
      => Machine { k: [value, ..], ..pre }
        where name: Id;

    assign: Machine { k: [Assign(name, value), ..], env: e }
         => Machine { k: [..], env: map::update(e, name, value), ..pre }
        where value: Value;
}
```

(`pre` is the implicitly-bound matched machine, Verus's word. A bare
`..` result would be E0797 — broken-looking Rust — so the base is
mandatory; it is also what makes the frame *visible*.)

- Pattern side is a genuine `syn::Pat` → rustc parser, rust-analyzer
  rename/highlight for free (13 §B); `..pre` is Lamport's own preferred
  record idiom (13 §H item 1).
- Still a different form from the single-cell tables (the cliff stays);
  slice-on-`Vec` (E0529) and the non-linear `name` binder (E0416) remain
  documented deviations; map pattern dialect survives.
- One `Machine {` + one `..pre` of overhead *per side per rule*; at KMIR
  width this is 2 lines of ceremony on ~12 lines of payload.

## C. Trailing per-cell clauses — pattern reads, arrow writes

The `for Machine` table disappears; `var`/`assign` rejoin the sort
tables and grow one clause per touched cell. **No `=>` inside a cell
clause = read-only (K parity: presence of `=>` inside the cell is
exactly K's read/write distinction, 13 §E).**

```rust
k::rules! {
    for Expr;
    var: name => value
        where name: Id,
        env: map![name -> value, ..];              // read: no arrow

    // ...the 18 eval clauses, unchanged...
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    assign: Assign(name, value) => ()
        where value: Value,
        env: e => map::update(e, name, value);     // write: arrow

    // ...the 7 control-flow clauses, unchanged...
}
```

- The evidence favorite's skeleton: Verus ships this clause structure
  (13 §A); K's rules grow exactly this way (one line per added cell,
  no form switch — 13 §E); KMIR authors at 11 cells already write flat
  per-cell lines (13 §E item 2); clause sequencing dissolves the
  non-linear-binder problem (13 §B).
- `tokio::select!`-family shape (`pattern = source, if guard => body`)
  is the macro clause Rust readers already parse (13 §B).
- Cost: `var` still spends two lines and a map pattern on "look name up".

## D. C plus expression-position reads (`env[name]`) — the composite

Same as C, but a cell used *only* as a read collapses into expression
position. `var` becomes a one-liner; the map pattern and the non-linear
binder vanish from the language.

```rust
k::rules! {
    for Expr;
    var: name => env[name]
        where name: Id;
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    assign: Assign(name, value) => ()
        where value: Value,
        env: e => map::update(e, name, value);
}
```

- Read-only-ness falls out of expression position — the adopted pattern
  everywhere (reads derived from position; standalone read annotations
  have no adoption record, 13 §H item 4). 54–73% of non-k cell mentions
  in real semantics are pure reads (13 §F), so the one-liner case is the
  common case.
- **Carries the one open semantic decision** (13 §D): `env[name]` must
  lower to the binding-match (rule-inapplicable when absent — what K's
  `var` means) even though every Rust reading of `[]` makes a missing
  key an event. Mitigations: document the lowering loudly, or spell it
  visibly unlike indexing (see E). Write side must stay clause-shaped
  (`env[name] = v` is exactly what Rust refuses, E0594).
- Sub-choice inside C/D: does the write clause name a binder
  (`env: e => map::update(e, …)`) or is the cell name its own pre-state
  (`env => map::update(env, …)`)? Verus does the latter (`pre.env`
  implied). One binder fewer per rule; slightly more magic.

## E. Keyword clauses (Verus-flavored spelling of C/D)

Same structure as D, but writes and failable reads get keywords instead
of arrows — the Verus vocabulary (`require`/`update`/`have`, 13 §A).

```rust
k::rules! {
    for Expr;
    var: name => value
        where name: Id
        have env[name => value];        // require key present + bind

    // or with D's expression read:  var: name => env[name] where name: Id;
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    assign: Assign(name, value) => ()
        where value: Value
        update env = map::update(env, name, value);
}
```

- `have`/`update` make the failure mode explicit at the use site
  (`have` = rule-inapplicable-if-absent, visibly not std indexing) —
  the reconciliation 13 §D points at.
- Cost: two new keywords in a surface that otherwise spends its budget
  on Rust's own vocabulary; `update env = …` reads as assignment, which
  is honest for the semantics but breaks the file's `pattern => result`
  rhythm.

## F. Tuple-scrutinee `match` (the reviewer's sketch)

```rust
k::rules! {
    for Machine;
    use StmtSyntax::Assign;

    match (k, env) {
        var:    ([name, ..], map![name -> value, ..]) => ([value, ..], _)
            where name: Id,
        assign: ([Assign(name, value), ..], e) => ([..], map::update(e, name, value))
            where value: Value,
    }
}
```

(`_` in a result slot = unchanged; labels on arms are not Rust and
would need attribute spelling in a stricter variant.)

- The one strength: `match`'s silhouette, parsed instantly; `bitmatch`
  proves a macro may keep the silhouette while swapping the pattern
  language (13 §B).
- Weakest empirical support of the menu: no surveyed interpreter or
  model checker tuple-matches state (revm: zero; rustc: only under
  borrow-checker duress — 13 §C); cells become positional (the reader
  keeps a scrutinee-order map in their head — at 3+ cells this is the
  ascent positional-tuple complaint, 09 §D); E0416 fires identically;
  keeps the cliff and adds a second nesting level.

---

## Width stress test (the KMIR 11-cell rule, sketched in form D)

`termReturnSome` (kmir.md:227-243), the widest realistic KMIR rule —
the shape any candidate must survive:

```rust
k::rules! {
    for KItem;
    use TerminatorKind::Return;

    term_return_some: k![ExecTerminator(Terminator(Return, _)), ..]
        => k![SetLocalValue(dest, decrement_ref(value)), ExecBlockIdx(target)]
        where
        current_func: _ => caller,
        current_body: _ => get_blocks(functions, caller),
        caller:       caller => new_caller,
        dest:         dest => new_dest,
        target:       SomeBasicBlockIdx(target) => new_target,
        unwind:       _ => unwind,
        locals:       list![TypedValue(value, _, _), ..] => new_locals,
        current_span: _ => new_span,
        stack: list![StackFrame(new_caller, new_dest, new_target,
                                unwind, new_locals, new_span), rest @ ..] => rest,
        functions: functions;                       // read-only
}
```

One line per cell, reads distinguishable at a glance (no arrow), no
nesting — the same shape the KMIR authors hand-write in K (flat cell
lines, parent tags commented out). Form B at this width adds
`Machine { … }`/`..pre` wrapping around 11 positional-order-free lines;
form F needs an 11-tuple scrutinee with positional `_` slots.

---

## Relationships

C is the skeleton; D = C + expression reads; E = C/D with keywords
instead of arrows. Choosing D or E still means building C's clause
machinery. B is compatible as the *expansion target's* frame spelling
(`..pre` in layer 2) even if layer 1 chooses C/D/E. A and F are
standalone alternatives.

Open regardless of choice (from doc 12, unchanged): the `env[name]`
lowering decision (only bites D), the no-k-head escape hatch (layer-2
only, per 13 §E), and the overlap diagnostic (cross-table, sort-aware,
plus 13's two new spec lines).

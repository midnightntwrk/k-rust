# 12: PINNED — the multi-cell rule form (`for Machine`)

**Status: RESOLVED (2026-08-21, same day).** After the evidence pass
([13-multicell-rule-prior-art](13-multicell-rule-prior-art.md)) and the
candidate menu ([14-multicell-candidates](14-multicell-candidates.md)),
review chose to **keep the anonymous cell record (candidate A)** — it is
the form truest to the mechanism (mirrors the configuration struct and
the layer-2 expansion, easiest to debug) — and reframed the readability
critique below as a **layout problem**: properly formatted (one cell per
line), the form reads fine. The successor question — enforcing that
layout, since rustfmt never formats brace-macro bodies — is pinned in
[15-formatter-pin](15-formatter-pin.md) for a fresh session. The
original pin text is preserved below for the record.

## The agreed critique

- The anonymous cell record `{ k: […], env: {…} } => { k: […] }` is no
  Rust idiom at all: struct patterns require a type name; Rust has no
  anonymous record patterns and no map patterns. A Rust reader has
  nothing to hang it on — it is K's cell markup transliterated into
  braces.
- The convention "cell present in the pattern but absent from the result
  = unchanged" is invisible.
- It stacks three bracket dialects (cell record, slice pattern, map
  pattern) plus the non-linear-binder deviation, all spent on two rules.
- The mechanism cliff: `for Sort;` and `for Machine;` are different
  forms with different pattern languages. K's own cell-less/cell-ful
  distinction is real (cell-less rules are configuration-completed into
  `<k>` — so `for Sort` itself is *not* the mistake) but **gradual**: a
  K rule that starts touching `<env>` stays the same rule form and grows
  one line. Moving a KRS rule across the boundary means rewriting it
  into a different construct.

## Directions tabled so far (analysis side)

1. **Name the type**: `Machine { k: […], .. } => Machine { k: […], .. }`
   — pattern side becomes essentially real Rust (struct pattern; `..`
   rest is Rust's own "not touching the rest" = K framing); result side
   is struct-update-shaped. Cheap; keeps the cliff.
2. **Trailing cell clauses on the one table form** (Ott: complex rules
   grow downward; DynSem: mention only what you touch; ascent: extras
   are flat prefixed items):
   ```rust
   assign: Assign(name, value) => ()
       where value: Value,
       env: e => map::update(e, name, value);
   ```
   `for Machine` disappears for IMP; rule cost proportional to what it
   touches; no form switch anywhere on the gradient.
3. **Cell reads in expression position**:
   ```rust
   var: name => env[name]  where name: Id;
   ```
   K parity is exact — `Map "[" KItem "]"` is K's builtin lookup
   (verified: k-distribution `domains.md:271`, `MAP.lookup`) and
   `RHO[X]` is established K rule style. Kills the map-pattern dialect
   and the non-linear-binder deviation (its only IMP use) in one move;
   a cell used only as an expression is read-only, which also recovers
   03d's read/write-set annotation without the in-place arrow.

## Reviewer counter-sketch (from the round-9 session)

Expected "idiomatic Rust" shape is a tuple-scrutinee match over the
touched cells:

```rust
match (k, env) {
    (Assign(name, value), e) => …
}

match (k, env) {
    (Assign(name, value), e) if value > 5 => …
}

// or with cell-name binders:
match (k, env) {
    (
        k @ { Assign(name, value), .. },
        env @ e,
    ) => …
}
```

Reviewer's own stated reservation: verbosity — if this `match` shape
leaked into the single-cell tables (the `StmtSyntax` rules) it "would be
a disaster for readability", which is the problem being solved in the
first place. Note doc 09 §B's finding cuts both ways here: hand-written
Rust machines almost never tuple-match all cells at once (they split by
state kind into flat single-scrutinee matches) — but `match` *is* the
one construct every Rust reader parses instantly.

## Questions the follow-up must answer

- Where is the k-head anchor spelled: table header (`for Stmt;`),
  scrutinee (`match (k, env)`), or per clause?
- Is the multi-cell form a *different* form or a gradual extension of
  the single-cell one? (The cliff is the core complaint.)
- Where does read vs write live: pattern position, expression position
  (`env[name]`), or DynSem-style per-cell modes declared once on the
  configuration (doc 09 §C flagged this as "a future KRS idea")?
- Semantics of `env[name]` if adopted: lower to the binding-match form
  (`<env> X |-> V … </env>`, rule inapplicable when absent) or to K's
  partial lookup function (stuck term when absent) — they differ under
  symbolic execution; pick and document.
- The generality escape hatch: rules that touch no k head at all
  (KMIR-scale machines, 12 cells) — full-machine form vs graduation to
  the layer-2 fn form.
- Overlap-diagnostic implications for whichever form wins (it must stay
  cross-table and sort-aware).

## Evidence already in hand

Doc 09 (rule prior art; Redex context-closure, Maude/DynSem framing,
E0508 on by-value slice patterns, RustPython's rule-as-comment);
result/README rounds 5–6 (why the current form exists); the K-gradience
correction above. Specimens to stress in the follow-up: IMP `var` /
`assign`; a KMIR multi-cell rule; a rule with no k-head involvement.

**Update (2026-08-21, post-pin):**
[13-multicell-rule-prior-art](13-multicell-rule-prior-art.md) now holds
the targeted evidence for every question above — Verus's
`state_machine!` as direction 2 shipped, the verified rustc facts (the
anonymous record is closed RFC 2584; E0797 makes direction 1's result
side ill-formed without a `..pre` base; E0416 survives tuple scrutinees;
let-chains are the modern multi-source match), the census showing
tuple-matching state is unattested outside borrow-checker workarounds,
the `env[name]` lowering evidence (binding-match vs partial `M[K]`
under the Haskell backend, and production semantics' unanimous
avoidance of the partial form), the measured cell-count gradient
(multi-cell = 6.5–16% of rules, max width 26), the near-absence of
no-k-head rules (20 of 5,837; KMIR 0), and the KMIR specimens. Read it
before the follow-up session; the pin itself stays open.

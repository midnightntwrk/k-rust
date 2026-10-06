# Open questions (decided-to-be-open — do not silently resolve)

Everything the investigation deliberately left undecided. An implementing
agent hitting one of these must surface it as a decision request (or take
the marked default and flag it), never pick silently. Items are grouped by
what they block.

## Blocks `krs fmt` (decision F1)

1. ~~**Canonical layout design**~~ (16 §I) — **RESOLVED
   (2026-08-23, decisions F5/F7)**: single-cell clauses are one line
   each after interior comments normalize to leading position;
   multi-cell rules never collapse, one cell per line; no width-based
   heuristics. Expanded rules use the exact `=>`/`where` placement in
   the normative specimen and 14 §Verdict sketch. The sole remaining
   layout choice is the trailing-comment column vs fixed gutter in
   item 4 below.
2. ~~**Column alignment in single-cell tables**~~ — **RESOLVED
   (2026-08-23, decision F5): the formatter emits alignment across the
   whole `k::rules!` block.** `:`, `=>`, and `where` columns align
   table-wide, not per blank-line group (whitespace-implicit
   sub-concepts are fragile; separate concepts belong in separate
   blocks). Blank lines are preserved but carry no formatter
   semantics. The formatter's edit-stability fixture pins that a label rename changes only the label token and table-padding whitespace.
3. ~~**Provenance/span safety under reformatting**~~ — **RESOLVED
   (2026-08-23, decision F6)**: formatting is provenance-preserving
   re-anchoring — stable IDs, provenance-key topology, and semantic
   payload unchanged; anchors recomputed byte-exact against the new
   text; checked in the formatter's test ladder (gates F3.2/F3.4).
4. ~~**The krs-syntax public API and trivia model**~~ (16 §I) —
   **RESOLVED (2026-08-23, decision F7)**: the narrow facade — `syn`
   and all grammar productions unchanged; trivia recovered by
   classifying the byte gaps between proc-macro2's tokens, totality
   asserted; `parse_*_source_with_trivia -> (Ast, TriviaTable)` entry
   points beside the untouched existing ones; cedar-style
   token-attached leading/trailing; three in-binary oracles plus a
   UUID-injection comment fuzz target; rowan-CST rewrite as the named
   escape hatch (>~15 placement handlers or multi-error recovery).
   **Additionally: non-doc `/* */` is a hard error inside DSL macro
   bodies** — DSL comments are line comments only, enforced by
   `krs fmt`/collector (macros cannot see comments); interior clause
   comments normalize to leading position.
   **Remaining sub-item, still open**: whether trailing clause comments form their own aligned column or sit at a fixed two-space gutter.
   Both behaviors have stable snapshots and CLI policies; `aligned` is the provisional recommended default, not yet the frozen decision.

## Blocks the rule engine

5. ~~**Overlap-diagnostic mechanism**~~ — **RESOLVED (2026-08-26, decision F2)**: run deterministic pattern unification after semantic sort inference over readable `HeadRule` declarations.
   The implementation is cross-table, sort-, constructor-, literal-, and repeated-variable-aware; ambiguous framed map-item requirements remain conservatively overlapping.
   Focused unifier tests and an end-to-end duplicated-IMP-rule regression pin the typed diagnostic.
6. **`{ .. }` in a cell position**: tail-only map pattern or all-framed
   cell record? Not exercised by IMP; the grammar must rule on it before
   larger definitions. [result README open list]
7. **The no-k-head escape hatch** for machine rules that don't touch the
   computation cell — layer-2 only per 13 §E, exact spelling open.
   [14 §Relationships]

## Blocks the grammar surface

8. ~~**Default associativity of a bare (unprefixed) precedence group**~~
   — **RESOLVED (2026-08-23): bare = no associativity constraint.** The
   specimen's assumption ("K's bare `>` is non-associative") was wrong;
   it was never checked against the oracle. Evidence:
   - K user manual (`inspirations/runtimeverification/k/docs/`
     `user_manual.md`, "symbol priority and associativity"): the bare
     `>` example grammar is explicitly described as *still ambiguous*
     until `left:`/`right:` annotations are added; `non-assoc` is a
     separate opt-in (block prefix, `syntax non-assoc`, or production
     attribute).
   - Empirical: bare-tier iterated unary (`!!true`) parses under
     kompile; adding explicit `non-assoc` breaks valid IMP statement
     nesting — so non-associative-by-default is both unfaithful to K
     and un-implementable without regressions.
   Decision recorded in C7 (updated): bare emits no associativity
   annotation; `non_assoc` is an explicit keyword mapping to K's
   non-associativity. Qualification lives in `tests/precedence-associativity`: it pins
   `!!true` parsing under a bare tier, `non_assoc` rejecting same-tier
   direct nesting, and the emitted `syntax non-assoc` sentence. The
   public `constructors` macro rustdoc for its enum-level
   `#[k::precedence]` helper records the bare default.
   [result README open list; falsified vs K manual]
9. ~~**`ExprSort` trait suffix vs a generated `mod sort { trait Expr }`**~~ — **RESOLVED by the compiling IMP expansion**: generate `ExprSort` and the short `type Expr = Term<dyn ExprSort>` alias.
   This keeps ordinary author references short while giving the marker trait a collision-free Rust identity.
   Sealing sorts against out-of-definition implementations remains a separate future hardening question.
10. **Tier-group naming for cross-family references**: generated
    (`op_tier1`) vs author-named via the chain's name position — both
    exist; the style-guide rule for when to name is unwritten.

## Blocks configuration

11. ~~**Leaf-vs-nested cell discrimination once wrappers are injected**~~ — **RESOLVED by the compiling IMP surface**: every readable leaf field must carry `#[k::cell]`.
    The attribute carries cell properties, and the field sort identifies the computation cell; missing helpers and unsupported nested shapes fail locally.
12. **`const`-initializer alternative to the init fn**
    (`k::config_vars! { … }` + `const MACHINE`) — sketch only; field
    default values confirmed still unstable (E0658). Default: init fn
    (D2). [result README open list]

## Deferred / out of scope for the IMP authoring surface

13. **Method-call term sugar** (`e.update(k, v)`) — deferred and
    policy-blocked (r10: no Rust trait resolution in term position);
    would need a closed sort-directed method table. [result README]
14. **`imp-verification.k`** (`[simplification]` rules, regex `token` productions) — explicitly out of the readable IMP specimen's scope, and the next thing a reader looks for.
    The four `[simplification]` lemmas are expressed with the explicit `#[k::simplification]` function form (`tests/imp/rust-definition/src/verification.rs`); the readable `k::rules!` tables have no simplification spelling.
    The `$`-prefixed `Id` token production has no authored counterpart: claims write such identifiers with `k::id!("$n")`.
15. **Exact-parity `% ` format escape** — currently a plain space, same
    compromise as the IMP port (C5).
16. **Style-guide item to write**: doc-comment policy on rule clauses (the control-flow table documents every clause, while the eval table documents none).
    The `k::builtin::map` facade and alias-safe `map::update` identity are implemented and no longer part of this open item.

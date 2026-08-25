# 13: Prior art for the multi-cell rule form

Companion to [12-machine-rules-pin](12-machine-rules-pin.md) (the pinned
question) and [09-rule-prior-art](09-rule-prior-art.md) (which covered the
single-cell table redesign). Doc 09 established the general landscape
(Redex/Maude/DynSem framing, smlang/ISLE/ascent/egg, hand-written Rust
machines); this doc records the two targeted evidence passes doc 12's open
questions still needed, run 2026-08-21:

- **§A–D: Rust ecosystem and language facts.** Every rustc claim was
  verified empirically on `rustc 1.97.1` by compiling probe programs;
  error codes are verbatim compiler output, not recalled.
- **§E–G: local K-corpus measurements** (KMIR / KWasm / KEVM /
  pl-tutorial / kimp, K 7.1.337), full-corpus scripted counts plus
  compiler-source reading — the specimens and lowering facts doc 12 said
  the follow-up must have.

A third pass (spec formalisms: TLA+ `UNCHANGED`, ASM update sets, CHR,
Event-B, Alloy, ~25 others) ran under the review expectation of being
low-yield. Most of it indeed confirms §A–G and is not repeated; **§H
keeps only the items that add a reason, a counterexample, or a construct
the Rust/K passes could not supply.** No §A–G verdict changed.

## A. The headline: doc 12's direction 2 is shipped, in Rust, for verification

**Verus's `state_machine!`** (`verus-lang/verus`,
`source/state_machines_macros/`, book under
`source/docs/state_machines/src/`) is a proc-macro DSL for named-cell
state machines whose transitions mention only the cells they touch — the
closest existing thing to a KRS configuration rule, and it is
keyword-for-keyword doc 12's "trailing cell clauses" direction:

```rust
transition!{
    t0_enter_via_flag() {
        require pre.thread_0 == ThreadState::Waiting;   // read = path expr
        require pre.flag_1 == false;                    // guard = keyword
        update thread_0 = ThreadState::Critical;        // write = keyword
    }
}
```

The load-bearing details:

1. **"Unmentioned cells are unchanged" is its documented core convention**:
   *"Any field for which no `update` statement appears will implicitly
   maintain its value from the `pre` state."* The closest prior art's
   answer to the invisible-frame critique is a distinct **write keyword**
   plus documentation — not a syntactic frame marker.
2. **`require` vs `assert` is exactly the rule-inapplicable vs
   proof-obligation axis**, given two different keywords (see §D).
3. **`require let Some(x) = pre.x_opt;`** — a refutable pattern as a
   trailing clause, documented as deliberately extending Rust ("which
   would ordinarily be disallowed because of the refutable pattern").
4. **Map cells get binding clauses**: `have env >= [k => let v];`
   desugars to `require env.dom().contains(k)` + a binding. Because the
   clauses are *sequenced*, `k` is a bound **expression** by the time the
   map clause runs — **the non-linear-binder deviation dissolves without
   being permitted** (its only IMP use is exactly this shape). Note Verus
   and `maplit` both spell map entries `k => v` where KRS round 2 chose
   `->`.
5. **Per-operation read/write modes exist**: `readonly!` vs `transition!`,
   plus `birds_eye` as the declared escape hatch for unrestricted reads —
   the shipped version of doc 09 §C's "declare modes once" idea.

Corroboration from practice: **stateright**'s actor models (its Paxos
example) write `match msg { Put(..) if state.proposal.is_none() => {
state.to_mut().ballot = …; } }` — one scrutinee (the message ≈ the k
head), other cells in the guard, per-field writes; its TLA+-transliterated
two-phase-commit drops `UNCHANGED` entirely because clone-and-mutate makes
"unchanged" the default. And **revm** converged on the same decomposition
by necessity: one macro per cell (`popn!` = stack, `gas!` = gas), and free
functions taking `&mut gas, &mut memory` — one argument per touched cell —
exactly where `&mut self` breaks (its migration guide records *replacing*
a macro with the explicit-cell-argument fn because the macro hid a
borrow-splitting problem; issue #2359's thread names "changing which cells
a rule mentions" as the ecosystem pain point).

## B. Rust language facts (all verified on rustc 1.97.1)

| Fact | Evidence | Consequence for doc 12 |
|---|---|---|
| The anonymous record `{ k: …, env: e }` is **RFC 2584 "Structural Records"** — fully specified (patterns with `..`, FRU, a type grammar) and **closed unmerged by the lang team, 2021-04** ("does not fit our current priorities") | rust-lang/rfcs#2584 | Doc 12's "no Rust idiom at all" softens to *"the syntax Rust specified and then declined"* — readers have nothing to hang it on and never will, but the shape is not arbitrary |
| `Machine { k: v, .. }` **as an expression is a hard error**: functional record update requires a base | **E0797** "base expression required after `..`" | Direction 1's result side as sketched is *broken-looking* Rust — worse than non-Rust. The legal spelling `Machine { k: v, ..pre }` gains an explicit frame anchor (Verus's `pre`), which arguably *fixes* the invisible-frame complaint. Even RFC 2584 required a base after `..` |
| A slice pattern **cannot apply to a `Vec`-typed field at all** | **E0529** "expected an array or slice, found `Vec<Stmt>`" | Stronger than doc 09's E0508 note (a move error): `k: [Assign(..), ..]` is *type*-incorrect on the obvious k-cell representation, by value or by reference. `deref_patterns` (rust#87121) would fix it, someday |
| Non-linear binders rejected **per pattern** — a tuple scrutinee changes nothing | **E0416**, verified in the exact KRS shape | Neither direction 1 nor the `match (k, env)` sketch rescues the deviation; only *sequencing* clauses does (§A item 4, and let-chains below) |
| The reviewer's `k @ { … }` cell binder is doubly illegal | `{…}` after `@` is RFC-2584 syntax; whole-plus-parts binding of non-`Copy` data is **E0382** partial move | The counter-sketch's binder form cannot be repaired into real Rust |
| Rust has **no map patterns and no live proposal** for them | rfcs search; adjacent: #2584 closed, #542 (map literals), #87121 | The `map!` pattern dialect is a permanent deviation if kept; directions 2 and 3 both eliminate it |
| Rust's own 2026 idiom for "match several things at once" is **let-chains** (stable 1.88, edition-2024-only — verified error on 2021), not a tuple scrutinee | `if let [Assign(n, v), ..] = &m.k[..] && let Some(old) = m.env.get(n) { … }` | One refutable pattern per source, sequenced, later patterns using earlier binders — structurally direction 2, and it dissolves E0416. RFC 3573's `is` operator is the same shape infix; Verus already ships `is` |
| A macro's `$:pat` accepts `S { a, .. }` and `[x, ..]` but **rejects `{ k: …, env: e }`** ("no rules expected `{`") | macro_rules probe | Real Rust patterns in pattern position get rustc's parser, rustc's diagnostics, rust-analyzer binder rename/highlighting, and `syn::Pat` for free; the anonymous record forfeits all four and must be tt-munched |

Macro-shape precedent for a match-lookalike with different semantics
exists on both sides: `bitmatch` keeps `match`'s silhouette while
replacing the pattern language entirely (string bit-patterns with implied
binders — a far larger deviation than anything KRS contemplates, shipped
and readable), and `tokio::select!` / `crossbeam_channel::select!` are the
established *clause-per-source* forms (`pattern = source, if guard =>
handler`; `recv(r1) -> msg => …`), with tokio's leading `biased;`
directive as precedent for header items like `for Machine;`.

## C. Nobody tuple-matches machine state (doc 09 §B, strengthened to a census)

Measured, not sampled: **revm** (the EVM interpreter — 8-field named-cell
state struct) contains **zero** `match (` over state in its entire
interpreter crate; **Boa** (JS engine, table-macro'd VM) never
destructures its `Vm`/`Context`; **stateright** matches the
action/message, never the state. The only codebase found that ever
tuple-matches state components is **rustc const-eval** — twice, both times
as a documented borrow-checker workaround with the NLL RFC cited in the
comment (`memory.rs:812` "We have NLL problem case #3 here…"). Two
codebases are *forced* into the shape and complain in the source; none
chooses it. Combined with E0416/E0382 above and the reviewer's own
verbosity reservation, the `match (k, env)` counter-sketch now has the
weakest empirical support of the four candidates. Its one real asset —
`match`'s instantly-parsed silhouette — is available to a table form
anyway (`bitmatch` proves the silhouette survives a replaced pattern
language; `k::rules!` clauses already have it).

## D. `env[name]`: three Rust readings, and what the K oracle actually does

**Rust side.** Every Rust reading of `map[key]` makes a missing key an
*event*: std `HashMap::Index` **panics** (`.expect("no entry found for
key")`, and rfcs#997 records that missing-key-panics is *why* Rust
withholds `map[k] = v`); `serde_json::Value` returns `Null` (documented
"concise and careless"); Verus's `vstd::Map` is total-but-unspecified
off-domain with a `recommends` lint. **There is no Rust precedent for
"silently inapplicable."** Secondary trap: reads via `env[name]` invite
writes via `env[name] = value`, which std rejects (E0594) but serde_json
and Verus both *do* ship — the write side must be explicitly decided,
not left to association.

**K side.** The two candidate lowerings are observably different under
the Haskell backend, and real semantics have voted:

- `Map "[" KItem "]"` is genuinely **partial** (`[function]`, no `total`
  — `domains.md:271`), with the definedness axiom `#Ceil(M[K]) => {K
  in_keys(M) #Equals true} …` (`domains.md:411`). When the key is not
  provably present, the term stays **unevaluated and the prover halts**
  on a residual `in_keys` obligation (K's own regression
  `lookup-55-spec.k.out`: "Prover: backend terminated because the
  configuration cannot be rewritten further").
- A missing **binding-match** (`<env> X |-> V …</env>`) just means "the
  rule does not apply and we can proceed to trying other rules"
  (booster-description.md:141-142) — which is what IMP's `var` means.
- **No production semantics exposes the partial form.** KEVM wraps it
  (`#lookup … [function, total]` + `in_keys` + `[owise]`,
  evm-types.md:415-429); KMIR — zero `|->` in 787 rules — wraps every
  lookup in a total `orDefault`-sentinel function and documents that the
  map was moved out of the rule pattern *for the symbolic backend's sake*
  (rt/value.md:140-142, 171-180); KWasm guards with explicit `requires I
  in_keys(LOCALS)` (wasm.md:601-613 shows all three spellings in 13
  lines). The manual's own advice: "The most preferred option is to
  write total functions and avoid the entire issue"
  (user_manual.md:1455). The price of partiality in the wild is 176
  `[preserves-definedness]` annotations in KMIR and 89 in KEVM;
  pl-tutorial, pure binding-match, needs zero.
- The booster's map-matching limit (concrete-keys-only unification,
  booster.md:178) does **not** bite `var`: its key is bound by the k-head
  before the map is touched, which the LLVM matcher classifies as a
  supported "lookup" rather than a "map choice"
  (llvm-backend matching README:614-627).
- **kimp's own two rules are already asymmetric**: `var` binding-matches,
  `assign` takes the whole map and functionally updates
  (calc.k:26-34). A read spelled in expression position lowering to
  binding-match, plus a write spelled as a trailing clause, reproduces
  the oracle exactly.
- No K doc anywhere recommends one style over the other (exhaustive
  grep; tutorial 16 demonstrates both without a verdict). The lowering
  is KRS's decision to make **and document loudly** — nothing exists to
  inherit.

**Net:** the two passes tension and then resolve. Rust intuition says a
failed `[]` must be an event; the oracle evidence says the *useful*
semantics for a rule-position read is rule-inapplicability, and the
partial-lookup alternative is the one every production semantics
engineers away from. Verus shows the reconciliation: its plain `[]` is
the total-unspecified read, while **failable access is a differently
spelled clause** (`have env >= [name => let value];` = require +
bind). If KRS adopts an expression-position read, either accept the
documented-lowering cost of `[]`-means-binding-match, or give the
failable read a spelling that is visibly not std indexing. Recorded as
the follow-up's choice; the evidence above is what it must be weighed
against.

## E. The K corpus, measured: how much weight the multi-cell form carries

Full-corpus scripted counts (method and caveats in the session records;
the 0-cell bucket mixes configuration-completed transitions with
function/simplification equations, which only strengthens the headline):

| corpus | rules | >1 cell | share | max cells |
|---|---|---|---|---|
| kimp (the specimen) | 31 | 2 | 6.5% | 2 |
| KRS imp.rs | 27 | 2 | 7.4% | 2 |
| KMIR | 787 | 74 | 9.4% | 11 |
| KWasm | 883 | 128 | 14.5% | 19 |
| KEVM | 3449 | 554 | 16.1% | 26 |
| pl-tutorial | 687 | 203 | 29.6% | — |

Three findings with design force:

1. **The multi-cell form is a minority construct at every scale** (never
   >30%) — but it grows in *width*, not just count. A form tolerable at
   2 cells and unreadable at 11 fails at Starstream scale.
2. **At 11 cells, practitioners already write the trailing-clause
   shape.** KMIR's widest rule (`termReturnSome`, kmir.md:227-243) is
   flat one-cell-per-line — with the nesting parent tags
   **commented out** (`//<currentFrame>`) purely for the reader.
   Configuration abstraction means K authors never spell structure they
   don't rewrite; the "record" view of the machine appears nowhere in
   rule text.
3. **Rules touching no k-head barely exist**: 20 of 5,837 rules across
   five corpora — 15 are KEVM's `rule [[ f(X) => V ]] <cells>`
   *function-context* form (reads only; "It is an error to have a
   rewrite inside function context", user_manual.md:2186 — the **one**
   machine-checked read-only construct in K), and 5 are KOOL's
   static-checker fixpoint rules (multiplicity-`*` cell matching, cell
   deletion via `=> .Bag`). **KMIR — doc 12's 12-cell worry case — has
   zero.** The escape hatch needs a layer-2 door (K compiles an
   `<env>`-only rule to a fully anchored top-level rewrite; verified by
   compilation), not a layer-1 surface.

Two more lowering facts the redesign must respect: the anchor cell is
**declared, not hard-named** (`ConfigurationInfo.getComputationCell()`;
KWasm's is `<instrs>`) — so `for Machine`-successor forms should read the
configuration for which field is the computation cell rather than
hard-coding `k`; and the backend **indexes rules by the k-head symbol**
(booster-description.md:140) — a header-position anchor (`for Stmt;`) is
an honest surface for the thing the backend actually keys on. K itself
never switches rule form across the 0→1→2→26-cell gradient (kimp
expr.k:41 → calc.k:26 → calc.k:28 is the three-rung specimen; the delta
is literally one line per cell).

## F. Read vs write: what the evidence licenses

- Measured across the corpora, **54–73% of non-computation-cell mentions
  are pure reads** (no `=>` inside the cell): KMIR 63%, KWasm 73%, KEVM
  54%. An expression-position read covers the genuine majority case —
  but 27–46% are writes, so it cannot be the whole mechanism.
- **K has no machine-checked read/write distinction for transition
  rules.** The website's claim that rules "make it explicit which parts
  are read-only, write-only, read-write" is unimplemented prose — no
  attribute, pass, or checker exists; local `=>` is documented as
  *concision* ("lifted to the top of the rule by duplicating the
  surrounding context"). A checked read-set would put KRS ahead of K,
  not at parity — doc 03d's annotation reading survives, its
  "K-concurrency rationale" framing does not.
- K **rejects rewrite-free rules** ("Rules must have at least one
  rewrite.", CheckRewrite.java:178) — a purely-read rule form would have
  no lowering target.
- Salsa is the counter-example for *inferring* read-sets: it observes
  them at runtime; a static overlap diagnostic can't. Bevy's
  `FilteredAccess` is the precedent for *declaring* them — with a
  directly transferable warning for the overlap diagnostic's spec:
  *"a `read` or `write` in `access` should not be considered to imply a
  `with` access"* — i.e. a rule that merely **mentions** a cell must
  register a read, not only one that binds it.

## G. Layer-2 gaps surfaced in passing (bug-class list, independent of the redesign)

Read against the K corpus, today's `cells!`/`map!` grammar
(crates/krs-syntax/src/state_macro.rs) cannot express three things real
semantics use: **nested cell patterns** (`cells!` selects flat top-level
leaves only; state_rule.rs has no `Nested` handling — KMIR's
`<currentFrame>` has no KRS spelling), **rewrites inside cell values**
(K's `<store>… L |-> (I => I +Int 1) …</store>`; in `map!`, `=>` is the
entry separator), and **multi-key functional updates** (single-key
`MapBody::Update` only). None blocks the IMP specimen; all three block
KMIR-scale fidelity and should land on the layer-2 build list whatever
layer 1 becomes.

## H. Formalism pass: what earned its keep

Across ~30 formalisms surveyed, the frame convention is **overwhelmingly
invisible** (ASM, Maude, K, Event-B, Promela, SAL, UPPAAL, Murphi, P,
mCRL2, Bluespec, DynSem, CBS, CakeML, Clean, CHR, separation logic…);
explicit frames survive only in TLA+/Alloy-style systems and
`modifies`-clause verifiers. The dividing line is principled, stated in
one sentence by Ivy: *"Because there is no aliasing in Ivy, the values of
all other variables remain unchanged by the assignment."* Explicit frames
are forced by exactly two things — rules that are **relations** over
(s, s′) (TLA+: "an action is a formula, and formulas aren't executed") or
**heap aliasing**. KRS rules are operational rewrites over fixed,
distinctly-named, non-aliasing cells: *neither reason binds*. That is the
missing justification for §A's "documented convention" answer — the
invisible frame is not a Verus habit, it is what operational rule systems
correctly do.

The verdict-relevant items:

1. **Explicit frames fail silently at exactly KMIR scale.** The
   canonical Raft TLA+ spec (13 variables, 23 `UNCHANGED` clauses) needed
   hand-rolled variable bundles (`logVars == <<log, commitIndex>>`) just
   to keep frames writable — and a rule that wrote `commitIndex'` while
   framing `logVars` was **identically false and silently unfireable for
   four years** in the world's most-copied spec (tlaplus/tlaplus#677;
   ongardie/raft.tla PR #6). Frame cost is O(cells − touched) *per
   rule*; the grouping abstraction it forces leaks the moment a rule
   touches part of a group. This closes doc 12's question (a): the fix
   for the invisible-frame complaint is **not** an explicit frame.
   Lamport's own escape hatch seals it: *Specifying Systems* §3.2
   re-specifies the same system with state as one record and prefers
   `[chan EXCEPT !.val = d]` — struct-update with an invisible frame,
   i.e. `..pre`.
2. **The invisible frame's own silent failure is the write conflict**
   (ASM: an inconsistent update set fires as a no-op; AsmetaL's tools
   catch "only trivial" conflicts statically). New spec line for the
   overlap diagnostic, alongside §F's Bevy item: detect two clauses of
   one rule writing the same cell, statically.
3. **CHR simpagation is the read/write split in pattern position**:
   `kept \ removed <=> guard | body`, with the manual's stated rationale
   being verbatim the KRS problem — it exists as "an optimization of
   simplification rules of the form `c1, c2 <=> c1, body`", i.e. to
   remove "rewrite X back to itself" boilerplate. CHR's `active`/
   `passive` head positions (the active constraint is the focus; partner
   constraints are found by store lookup) are an operational reading of
   "the k-head anchors, other cells are looked up" — worth having on the
   table next to expression-position reads in the follow-up.
4. **Optional read-set clauses do not get adopted.** JML has both
   `assignable` (writes) and `accessible` (reads); its own manual calls
   `accessible` "a seldom-used feature". Morgan's specification
   statement — the most frame-conscious formalism surveyed — declares
   *only* the write set. What does get adopted is a mode attached to a
   thing you already name (Iris `l ↦{dq} v`, VST `readable_share`, Rust
   `&`/`&mut`). Supports §F: reads as expression position (free), writes
   as clauses; never a standalone read-list annotation.
5. **A static effect system buys the right to delete frames.** Quint
   (Informal's TLA+ successor) **removed its `UNCHANGED` keyword** once
   an inferred `Read[V] & Update[V]` effect system landed; Bluespec
   infers read/write sets and surfaces them in conflict diagnostics
   ("calls to `x.write` vs `x.read`"), with annotations only as
   overrides. This is the trade the overlap diagnostic already commits
   KRS to — the formalism record says it's sufficient.
6. **The graduated form is near-universal; the cliff is the anomaly.**
   Almost every surveyed system scales 1→N components by list arity
   (ASM's guarded-multi-update normal form even carries a lemma that
   nesting is sugar over the flat table). The systems *with* a cliff are
   cautionary: Turnstile hard-codes two contexts (its authors: "requires
   an overhaul"); Event-B's merely *cosmetic* `begin`/`when`/`where`
   header switch is condemned by its own FAQ as having "created more
   confusion than anything else" — a first-party warning about form
   switches driven by whether an optional part is present, which is
   exactly the `for Sort;`/`for Machine;` split.
7. **Two design constraints to record**: (i) NuSMV deprecated its one
   implicit-frame construct because implicit frames cannot coexist with
   a relational escape hatch (`TRANS`) — so KRS rules must remain the
   only way to constrain the step relation, or frames stop being
   derivable; (ii) simultaneous multi-cell updates get misread as
   sequential (Gurevich's own proofreading remark; AsmetaL grew explicit
   `par`/`seq` keywords) — a result form listing several cell writes
   should make simultaneity unmistakable. Two ergonomic footnotes from
   mCRL2's named-update form (the closest syntax to trailing clauses in
   the family): resolve binders against the matched configuration, not
   lexical scope (issue #981), and never print identity updates (#1079).
8. **P's event ladder** is the cleanest precedent that a control move
   is an *optional clause of the same rule form*: `on E do {…}` (data
   only) / `on E goto S;` (control only) / `on E goto S with {…}`
   (both) — three degrees of one construct, no rule-kind split.

## Synthesis: doc 12's questions, answered by evidence

- **Where is the k-head anchor spelled?** Header position. The backend
  indexes on the k-head symbol; the anchor cell is declared
  configuration data; K never moves the anchor as rules grow. A
  scrutinee-position anchor (`match (k, env)`) reintroduces the cliff
  and has no analogue in K's model or in any surveyed Rust codebase.
- **Different form or gradual extension?** Gradual, via trailing per-cell
  clauses on the one table form — the only direction that matches K's
  gradience, and the one that is *shipped* (Verus), *converged on by
  necessity* (revm, KMIR at 11 cells), *echoed by Rust's own trajectory*
  (let-chains, `is`), and *shaped like the macro clauses Rust readers
  already parse* (`select!`). It also uniquely dissolves E0416 (by
  sequencing) and the map-pattern dialect. Direction 1's honest form
  requires `..pre` (E0797) — worth keeping in mind as the *frame
  spelling* even inside direction 2's expansion story; direction 4 is
  empirically unattested and doubly illegal as sketched.
- **Where does read vs write live?** The corpus says reads dominate
  non-k-cell mentions (54–73%), so an expression-position read earns its
  keep; writes need a clause form regardless. Verus's precedent: reads
  are path/expression-shaped, writes and failable binds are
  keyword-shaped clauses, per-operation modes exist (`readonly!`,
  `birds_eye`). Any checked read-set is KRS going beyond K — by choice,
  not parity — and §H item 4's negative result bounds the spelling: a
  standalone read-list annotation has no adoption record anywhere;
  derive reads from position (expression position, or CHR's kept-side),
  never from an optional clause.
- **`env[name]` semantics?** The genuine open choice, now with its
  evidence assembled (§D): binding-match matches the oracle's `var` and
  every production semantics' practice, but contradicts all three Rust
  readings of `[]`; the reconciliations are "document the lowering
  loudly" or "spell the failable read visibly unlike std indexing"
  (Verus's `have`). Do not expose K's partial `M[K]` at layer 1 in any
  case.
- **The no-k-head escape hatch?** Keep the layer-2 door (K compiles
  such rules), skip the layer-1 surface: 20 in 5,837 rules corpus-wide,
  zero in KMIR; the read-only half of the need is K's `[[ ]]`
  function-context form — the one construct where K machine-checks
  read-only-ness — which maps to an ordinary KRS function rule with
  read-only cell parameters, not to a rewrite form.
- **Overlap diagnostic implications?** Unchanged in posture
  (cross-table, sort-aware, per doc 06); two new spec lines: from Bevy,
  mention-implies-read must be registered explicitly or disjointness is
  computed unsoundly; from ASM (§H item 2), same-rule write conflicts
  are the invisible frame's own silent-failure mode and belong to the
  same checker.

### Corrections to earlier docs

- Doc 09 §B / result-README round 5: the slice-pattern caveat cites
  E0508 (move out of a slice); the operative error on a `Vec`-typed
  cell is **E0529** — the pattern is type-incorrect entirely, not merely
  move-incorrect.
- Doc 12 "no Rust idiom at all": soften per §B — the form is RFC 2584,
  specified and declined; additionally its result side is ill-formed
  under *any* Rust, real or proposed (FRU base requirement survives even
  in the RFC).
- Doc 12's `domains.md:271` / `MAP.lookup` citation: verified correct,
  with the sharpening that the hook is partial and its definedness
  axiom, symbolic behavior, and production avoidance are as recorded in
  §D.

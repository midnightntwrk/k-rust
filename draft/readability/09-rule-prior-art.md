# Prior art for configuration-rule syntax (rounds 5 research)

Companion to [07-prior-art](07-prior-art.md), which surveyed Rust
verification/DSL tooling generally. This doc records a targeted survey run
while redesigning the *configuration-rule* surface (the `cells!` fn form),
condensed from four research passes: Rust rule/transition DSLs, hand-written
abstract machines in Rust, semantics frameworks beyond K, and a deep dive on
ascent's real-world developer experience. The design it fed is rendered in
[result/imp_sort_aliases.rs](result/imp_sort_aliases.rs) (round 5) and
argued in [result/README.md](result/README.md).

## A. Rust rule/transition-table DSLs

- **smlang** is the closest existing thing to a rule table:
  `SrcState + Event [guard] / action = DstState`, one row per transition,
  sigils instead of keywords, the eye reads down the `=` column. Two
  warnings: guards/actions are bare idents resolving to a generated trait
  (no goto-def), and overlapping guards resolve by **textual order** —
  order silently leaking into a table that looks unordered.
- **rust-fsm** offers a *grouped* left-hand side
  (`HalfOpen => { Successful => Closed, Unsuccessful => Open }`) — a shape
  worth remembering for families of rules sharing a pattern. Its `[..]`
  means output while smlang's means guard: sigil budgets don't transfer
  between crates.
- **ascent / crepe** (Datalog): `head <-- body;` clause rows with Rust
  embedded as *prefixed keyword items* (`if expr`, `let x = ..`,
  `for p in ..`, `?pat` bindings) — flat, never nested. The readability
  mechanism is one visual line per rule with a fixed arrow spine.
- **egg**: `rewrite!("name"; "(+ ?a ?b)" => "(+ ?b ?a)")` — the documented
  failure mode (issues #219, #287): pattern variables inside strings get no
  arity check, no rename, no tooling. Egglog abandoned embedding entirely
  for a standalone s-expr language.
- **Cranelift ISLE** is the best-engineered "unordered rule set" in Rust:
  typed non-string patterns, `(rule PRIO pattern expr)`, and — the part
  worth stealing — an explicit stance that the program is *an unordered
  list of rules* backed by a **static overlap checker** that forces
  explicit priorities when two same-priority rules can both fire.
- **Bevy ECS** (rules as fns whose typed params declare state access):
  framing-by-signature maps beautifully to cells, but the model **cannot
  express value-shape matching** — a `Query<&K>` selects by component type,
  so `Sequence(s1, s2)` moves into the body and the discriminating pattern
  vanishes from the signature. Many unordered rules over the same `&mut`
  data is precisely ECS's ambiguity case (`.chain()`/`.before()` — i.e.
  imposed order). Rules-as-lens-fns is not our answer.

## B. How Rust developers hand-write abstract machines

Surveyed: Aiken's UPLC CEK machine (the most-run Rust CEK in existence),
KittyCAD's KCL machine, rufus, aams (Abstracting Abstract Machines port),
RustPython's frame loop, rustc const-eval/Miri `step.rs`, wasmi/wasmtime.

- The dominant idiom: split the step by state kind (`compute`/`return`),
  each a **flat single-scrutinee match** — on the focused term in one, the
  popped continuation frame in the other. Tuple-matching all cells at once
  (`match (ctrl, kont)`) is essentially unattested.
- **By-value slice patterns on `Vec` are illegal** (E0508: cannot move out
  of a non-copy slice). So `k: [head, ..] => k: [head', ..]` can never be
  literal Rust `match`; a macro must desugar it. The spelling is
  *evocative* Rust, not real Rust — same status as the rest of the rule
  grammar, but worth stating. Also: Rust developers read a `Vec` stack top
  as `[.., top]`; head-at-front reads as a queue/cons — matching K's k
  cell, but the mental model should be documented.
- Post-state via **struct-update syntax** (`State { k: .., ..state }`) is
  the most Rust-native "only these cells change" — the two-sided reference
  form is already this shape.
- RustPython writes the rewrite rule *as a comment* above each arm
  (`// Stack: [container, start, stop] -> [result]`) — the code cannot say
  what the comment says. That comment is the notation a rule DSL should be.
- At production scale (wasmi, wasmtime/Pulley) the big match is abandoned
  for per-rule macro-generated handlers — evidence *for* KRS's premise.
- Honest counterpoint: `match` is ordered with fallthrough and its main
  payoff (exhaustiveness) is meaningless for a deliberately non-exhaustive
  rule set. A rule table must therefore only *look* like match arms while
  expanding to independent unordered rules — which is exactly the
  `k::rules!` contract.

## C. Semantics frameworks beyond K

- **PLT Redex**: the highest-value import. `reduction-relation` rules can
  omit contexts entirely — the `with`/`context-closure` shortcut declares
  the context *once on the arrow*, and rules inside are bare term rewrites.
  A rule mentions a context only when it *manipulates* it (`call/cc`),
  never merely to be inside one. `k::rules! { for Stmt in k; … }` is
  exactly a `with` shortcut.
- **Maude**: flat labeled rule lists (`rl [label] : lhs => rhs .`);
  implicit framing at *two* levels (unmentioned objects in the ACI soup,
  unmentioned attributes within an object), implemented as sugar over an
  explicit frame variable — the same layer-1/layer-2 discipline KRS uses.
- **DynSem**: rules mention only the state components they touch, with a
  read-only/read-write **mode split declared once per component** — modes
  are the principled version of implicit framing. Costs stated in the
  paper: fixed component set per arrow, and threading makes premise order
  load-bearing. (A future KRS idea: declare cell modes on the
  configuration, not per rule.)
- **Ott**: complex rules grow *downward* (premises above the line), the
  conclusion stays one line — a table stays scannable if extra machinery
  goes below the arrow line, never into it.
- **Nobody else puts the rewrite arrow inside the matched context.**
  Maude, Redex, Stratego, DynSem, Ott, egglog, Soufflé are all two-sided.
  K is the outlier, and K's own stated rationale is *concurrency*
  (in-place arrows delimit read/write sets so overlapping reads need not
  interleave), not readability. Implication: 03d's in-place arrow is a
  read-set annotation to keep for the rules that need it, not the default
  readability device.

## D. ascent DX in the wild (deep dive)

What users praise is the **embedding**, not the syntax ("like JSX for
Datalog/Rust"; "embedding into the host language is actually *huge*").
The complaints cluster on three things, none of which is the arrow:

1. **No modularity**: an `ascent!{}` block cannot be factored across files
   (proc macros see only their own tokens), so schemas are copy-pasted —
   "a nail in the coffin for reusability". KRS structurally avoids this:
   grammar and configuration are real items outside the blocks, the
   collector sees the whole crate, and `k::rules!` blocks stay small and
   per-family.
2. **Tooling cliff inside brace-macros**: rustfmt categorically never
   formats brace-delimited macro bodies (maintainer-confirmed); ascent
   ships a nightly-only fmt config and has an open "hard to contribute"
   issue about it. rust-analyzer applies one blanket `macro` token inside.
   Author's verdict on better errors: "not really feasible, as the error
   message is coming from the Rust compiler". For KRS this hardens the
   existing m1 LSP-golden gate on `k::rules!`, and turns the rustfmt
   non-formatting of macro bodies from a bug into the mechanism that
   *preserves* the table layout.
3. **Positional tuples hurt documentation** — users annotate columns with
   trailing comments. KRS rules bind named constructor fields, so this
   failure mode is already avoided.

Long rules do strain the clause form (an 18-line production ascent rule
with nested bindings, hand-aligned because rustfmt won't help). The
`k::rules!` guidance stands: a rule that outgrows `pattern => result
(+ where)` graduates to the fn form.

## Synthesis → the round-5 design

1. One-row-per-rule tables with an arrow spine are the convergent answer
   (smlang, ascent, ISLE, Maude, Redex, Soufflé) — configuration rules
   join `k::rules!` as match-style arms.
2. Redex's context-closure: `for Stmt in k;` heads a table whose clauses
   are bare term rewrites pinned to the k-cell head; right-hand sides may
   splice sequences (`k![…]`) or erase (`()`), which makes 7 of IMP's 9
   control-flow rules one-liners. Only genuinely multi-cell rules match
   the machine.
3. The k cell is matched with slice patterns (`[head, ..]`), the env cell
   with map patterns (`{ k -> v, .. }`), post-states are struct-update
   shaped — evocative Rust, desugared by the macro, with the E0508 caveat
   documented rather than hidden.
4. From ISLE: unordered clauses with a **static overlap diagnostic** and
   an explicit-priority escape hatch — never smlang's silent first-wins.
5. From ascent: clause extras stay flat prefixed items (`where …;`), never
   nested; blocks stay small; no binder ever lives inside a string.
6. The in-place arrow (03d) is demoted from default to special-purpose
   (its honest meaning is a read/write-set annotation, per K's own
   rationale); the fn/`cells!` form remains the reference surface every
   clause expands to.

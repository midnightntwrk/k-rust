# F1: the M2 fragment, specification

State: landed in kcore-spec beside F0, 2026-11-07, with the recommendations of §11 taken as decided (Sebastien: "if you think from first principles those are right, let's keep making progress"; review does not block). This document has for F1 the role STATEMENTS.md has for F0.
The Lean is `KcoreSpec/F1/` (namespace `F1`), built by `lake build`. F0's modules, statements and proofs are unchanged; F0's definition-independent pieces are reused: `Reordered`, the KORE builders of Emit.lean, the translation, Γ_cons and the closure construction. Drafted in `../m2-spec/` (history: ../findings/M2-spec-draft.md); section references to `M2Spec/X.lean` below are `KcoreSpec/F1/X.lean`.
Proved since landing (three axioms, guarded in `KcoreSpec/F1/Checks.lean`): peano's nine properties over F1 (`KcoreSpec/F1/PeanoProofs.lean`), peano's KORE in F1 by the kernel (`test/F1Check.lean`), and subject reduction for cores that `ok` and `srReady` accept (`KcoreSpec/F1/SubjectReduction.lean`: `rhs_sorted`, `step_of_apply`, `Eval.sorted_of`, `hook_sorted`; the order and map laws in `OrderLaws.lean`), which `wf` gives (`NamesApart.lean`; `rhs_sorted_wf`, `step_of_apply_wf`, `Eval.sorted_wf` in `StepIffWf.lean`). `step_ofF0` (`OfF0Theory.lean`; F1's step is F0's on F0 definitions; restated 2026-11-08 with `hooksApart` on the image, since the first statement is false: `OfF0Counterexample.lean`, an F0 function may be named like an F1 hook) is proved (2026-11-08): the signatures agree (`OfF0Sig.lean`), F0 matching is F1 matching under a well-sorted σ with the same values in both directions (`OfF0Match.lean`), and evaluation agrees in both directions (`OfF0Eval.lean`). Soundness and completeness are `KCore.Sound` and `KCore.Complete`, with `sound` and `complete` proved from `wf` and `Obligations` (`KcoreSpec/Sound.lean`); the library has no `sorry`. `Exec.step_iff` (the executable step lists `Step`'s successors, for some fuel; `StepIffWf.lean`) is proved from `wf` alone (2026-11-08). First from two decidable conditions on the core besides `wf`: `step_iff_of` (`StepIff.lean`) assumes `srReady` (function labels distinct, subsorts closed under composition) and `matchReady` (subsorts irreflexive, no constructor named like a map pattern symbol). Its parts: canonical maps (`MapLaws.lean`: one canonical representation, `union` defined exactly on keys apart), the matcher sound (`MatchSound.lean`, maps included) and complete on well-sorted patterns (`MatchComplete.lean` without map symbols, with at most one match; `MatchMap.lean` on rule patterns with maps, through `mapDecomp`), the executable evaluation sound (`EvalSound.lean`) and complete (`EvalComplete.lean`, by the mutual recursor), and the listed successors are steps (`StepSound.lean`). For peano it holds with no `sorry` (`test/F1Check.lean`, `peano_step_iff`). Then `wf` gives both (`NamesApart.lean`: `srReady_of_wf`, `matchReady_of_wf`), from `namesOK` (function labels distinct, cell and user sorts apart, no user sort `KItem`), the shape of generated cell names, `subsortsOK` and `hooksApart`.
Marks: [V] checked by running or by kernel proof; [I] inference or argument.

## 1. Scope

F1 is F0 plus the following:
- several configuration cells and the fresh counter;
- Bool and Int: domain values, the interpreted INT, BOOL and KEQUAL hooks, and their domain theories in Γ_D;
- `requires` on rules and on function clauses;
- Map values, map patterns modulo associativity, commutativity and unit, and the MAP theory (decisions of findings/M2.2-collections-probe.md);
- four coverage limits:
  - productions without `symbol(…)`;
  - rule labels;
  - rule attributes that do not change ground steps (`concrete`, kompile's `cool-like`, `cool`);
  - `$PGM` of sort K, KItem, Int or Bool;
- Int and Bool as subsorts of a user sort (`syntax Exp ::= Int`).

The shape of the fragment is kept: `F1 k := parse k = some d ∧ wf d ∧ Reordered d.emit k` (`Fragment.lean`), with F1's `parse` (Parse.lean, unreviewed).

What is complete, and what is not:

| Part | Draft | Evidence |
|---|---|---|
| Frozen layer: Core, Value, Hooks, Evaluation, Step | complete for the scope | elaborates; four steps and two evaluations proved with no `sorry` on fn.k and a two-cell Map store [V] |
| `wf` (DefinitionWf, Fragment) | complete for the scope | accepts peano, fn.k and the store; coverage tested positive and negative [V] |
| `emit` | complete for the scope: the configuration's text from the cell tree (Q8), one of three fixed texts (Q9) | 35 definitions are in F1 end to end, 24 of them corpus definitions (§12) [V] |
| `parse` (unreviewed), the executable step (checked layer) | written; `step_iff` proved from `wf` (`StepIffWf.lean`) | the M2.1 differential on every F1 subject (§12) [V] |
| Run certificates (checked layer, `Cert.lean`, `Tie.lean`) | `checkRun_sound` (M2.5); `checkRunT_sound` with stuckness (`stuckCheck_sound`) and the hoisted subsort list, and `reordered_of_permsOK` (M2.5b), all proved from `wf` | 39 krust runs on 36 subjects (673 steps) kernel-checked, 36 of them about the definition parsed from the KORE text, 33 with stuckness (findings/M2.5-certificates.md) [V] |
| Theory audit of the fixed texts | done (F1-AUDIT.md) | no false axiom; nothing curated beyond the simplification lemmas Γ_D already leaves out |
| Statements: soundness and completeness | proved | `KCore.Sound` and `KCore.Complete`, with `sound` and `complete` proved from `wf` and `Obligations` (`KcoreSpec/Sound.lean`); no `sorry` |

## 2. The core (Core.lean, FixedSignature.lean)

Against F0, four additions:
1. **`Term.dv s lit`**, a domain value in a pattern or a right-hand side. Hooked symbols are applied with `Term.app`, like functions.
2. **`req : Option Term`** on clauses and rules: the `requires`, a Bool term. `none` stands for `\top`.
3. **`config : Cell`**, the user's configuration as a cell tree (`leaf name contentSort | node name children`).
   - The generated cells wrap it: `<generatedTop>` holds the user's root cell and `<generatedCounter>` of sort Int.
   - The cell sorts, the cell constructors (`<x>`, `noX`, `<x>-fragment`) and the subsorts `XCell < XCellOpt` are computed from the tree, as kompile derives them.
   - F0's configuration is `leaf "k" "K"`. For it, F1 computes exactly F0's constructor list, subsorts and cell sorts, in F0's order (`#guard` in Peano.lean) [V].
   - The order rule matches krust's output for `<T> <k/> <state/> </T>` too [V, by reading the store's KORE].
4. **`pgmSort` may be K, KItem, Int or Bool**, as in `configuration <k> $PGM:K </k>`.

**Why the fresh counter needs nothing [V, store.k].** kompile compiles `!I:Int` into the rule itself:
- it matches `<generatedCounter> #Fresh </generatedCounter>`;
- it puts `freshInt(#Fresh +Int 0)` where `!I` was;
- it writes `#Fresh +Int 1` back to the counter.

So the counter is an ordinary cell, and `freshInt`, an identity function of the INT module, is interpreted like a hook. `step_new` proves such a step.

CHOICE: cell names are alphanumeric (`wf`). That makes the sort name `Cap(name)Cell` and the label `Lbl'-LT-'name'-GT-'` without mangling. It is forced by nothing; mangling can be added when a corpus definition needs it.

## 3. Values (Value.lean)

1. **`GroundTerm.map es`**: a finite map with its entries in canonical form, keys strictly increasing in a total order `GroundTerm.cmp`. This is M2.2's candidate. Equal finite maps are equal values, so equality stays structural.
   CHOICE (M2.2 §1.2): a canonical sorted list rather than a quotient.
2. **Domain values in canonical form only, and only for Bool, Int and KConfigVar.**
   - The canonical forms: `"true"`/`"false"`; for Int, `0`, or an optional `-` followed by digits that do not start with `0`.
   - F0 accepted any literal of any unparameterized base sort, including `\dv{SortMap{}}("x")`.
   - Why the change [I]:
     - with an INT theory in Γ_D, `"05"` and `"5"` would be two values denoting one element, which breaks `ModelsStandard` (distinct values denote distinct elements);
     - and a map has no domain values once maps are values.
   - Consequence: an F0 configuration whose counter is `"00"` is not an F1 configuration (Q6).

List and Set have no ground values in F1: they have no constructors, and their literals are not domain values. They come in M3.

## 4. The interpreted hooks (Hooks.lean)

`hook f vs : Option (Option GroundTerm)` gives three outcomes:
- `none`: `f` is not an interpreted symbol;
- `some none`: `f` is interpreted and undefined at `vs`;
- `some (some v)`: `f` is interpreted and has value `v`.

The symbols interpreted, keyed by the KORE names the fixed text declares (`FixedSignature.hookSigs`):
- **BOOL:** `notBool`, `andBool`, `andThenBool`, `orBool`, `orElseBool`, `xorBool`, `impliesBool`, `==Bool`, `=/=Bool`.
- **INT:**
  - `+Int`, `-Int`, `*Int`;
  - truncating `/Int` and `%Int`, and Euclidean `divInt` and `modInt`, all undefined at 0;
  - `<Int`, `<=Int`, `>Int`, `>=Int`, `==Int`, `=/=Int`;
  - `minInt`, `maxInt`, `absInt`;
  - `freshInt` (the identity, as its fixed-text equation says).
- **KEQUAL:** `==K`, `=/=K`, as equality of values.
- **MAP:**
  - `.Map`, `|->`, and `_Map_` (union of two maps with disjoint keys, undefined otherwise);
  - `Map:update`, `_[_<-undef]`, and `Map:lookup` (undefined off the keys);
  - `Map:lookupOrDefault`, `in_keys`, `size`.

This one function is what a reviewer checks against the documented meaning of each hook in K's `domains.md`. The domain theories in Γ_D are read off it (§8), not written symbol by symbol.

### 4.1 CHOICE versus forced

| Item | Status |
|---|---|
| Int is ℤ, Bool is the two-element Boolean algebra | forced by the hooks' documented meaning |
| `/Int`, `%Int`, `divInt`, `modInt` undefined at 0 | CHOICE among "undefined" and "unconstrained". Undefined (⊥) makes evaluation strict and keeps `ModelsStandard`. Unconstrained would let models disagree on `x /Int 0`. |
| `_Map_` undefined on overlapping keys | CHOICE (M2.2 §1.2), consistent with `_Map_` not being `total` in the KORE |
| `Map:lookup` undefined off the keys | same reasoning |
| `andThenBool`, `orElseBool` strict, like `andBool`, `orBool` | CHOICE (Q10). K documents them as short-circuit. They differ only when the second argument is undefined. |
| `==K` is equality of values | forced, given `ModelsStandard` (distinct values denote distinct elements) |
| `#if` (`ite`, sort-parametric) not interpreted | scope (Q11) |

### 4.2 Hooks are strict

Every argument is evaluated, and an undefined argument makes the application undefined. This is the matching-logic reading of an application with an argument `⊥`, since `f(⊥) = ⊥` by propagation [I].

### 4.3 Why the graph of `hook` is enough for maps [I]

A step over ground configurations only ever evaluates `_Map_` on ground maps, and those are canonical values.
- **Commutativity and definedness on disjoint keys:** on ground values these are instances of the graph, `_Map_(⟦m₁⟧, ⟦m₂⟧) = ⟦m₁ ∪ m₂⟧` or `⊥`.
- **Distinctness of different canonical maps:** this makes the denotations of different maps different elements.
- **No junk:** this is what rules out a map pattern `K |-> V M` matching through a non-ground element M. It is stated as a μ-axiom (`mapNoJunk`).

## 5. Matching, evaluation, step (Evaluation.lean, Step.lean)

### 5.1 Matching is denotational (decision 2 of M2.2)

`PatVal c σ p v` says that pattern `p` denotes `v` under σ:
- a constructor builds a constructor term;
- `.Map`, `|->` and `_Map_` denote their hook values;
- an injection is put in normal form;
- an as-pattern requires that its variable's value is the value denoted.

A rule or clause matches under σ when σ is **well-sorted** (every variable has a value of its sort) and the pattern denotes the value.

Why [I]:
- **This is what matching logic says.** A valuation ranges over the sorts of the variables, and `L = x` holds exactly when L denotes x.
- **It covers what F0's algorithm could not:**
  - A map pattern `K |-> V M` has several matches: one per entry whose key K may take.
  - A non-linear pattern needs no extra machinery: kompile binds a key in the k cell and matches it in the state map (store.k's `get`).
- **The matcher becomes a checked-layer algorithm**, proved equal to `PatVal`, just as `step_iff` proves the executable step equal to `Step`.

Why σ must be well-sorted [I]: otherwise `inj{Nat,KItem}(N)` would denote `inj{State,KItem}(st)` under `σ(N) = inj{State,Nat}(st)`, a term that is not a value. F0's `matchTerm` excluded this with its `le a' a` test; F1 excludes it through σ's sorts.

On F0's patterns (linear, built from constructors and injections) the two readings agree. That is `step_ofF0` (OfF0Theory.lean; proved 2026-11-08).

### 5.2 Evaluation states definedness

`EvalTerm c σ t r` and `Eval c f vs r` now have `r : Option GroundTerm`, with `none` meaning undefined (`⊥`).

**Why it is forced by `requires` [I].**
- A clause applies when its patterns match under σ and its `requires` evaluates to `true`.
- In the KORE, an equation's premise is `\equals(req, \dv{SortBool{}}("true"))`, and an `[owise]` equation negates the conjunction of each competitor's `requires` and patterns (fr.k, krust's output [V]).
- So a clause whose `requires` is undefined, such as `x /Int 0 > 1`, does not apply, and the next clause or the catch-all decides.
- For first-match to stay an **inductive** definition, "does not evaluate to `true`" has to be derivable positively. The relation cannot mention its own negation.
- So undefinedness is a result:
  - a hook may return it;
  - it propagates through constructors, hooks and calls;
  - a function whose clauses all fail and which has no catch-all is undefined there (`Eval.undef`);
  - a non-terminating evaluation still has no derivation.
- `Fails c vs cl` is the positive "this clause does not apply": for every well-sorted σ that matches, the clause has a `requires` whose result is not `true`.

**The alternative**, rejected for the draft (Q2), was to keep F0's `EvalTerm c σ t v` and restrict `requires` to total expressions. "Total" would then be a transitive syntactic check over hooks and functions, and it would reject `M[K]` and `/Int` in conditions.

F0's `Eval c f vs v` is F1's `Eval c f vs (some v)`.

### 5.3 Step

```lean
inductive Step (c : Semantics) : Config c → Config c → Prop where
  | rule {x y} (r : Rule) (mem : r ∈ c.rules) (σ : Subst)
      (hσ : c.WellSorted r.vars σ) (hmatch : PatVal c σ r.lhs x.val)
      (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
      (heval : EvalTerm c σ r.rhs (some y.val)) : Step c x y
```

It is still one constructor for every definition. Rule priorities and `ensures` remain outside the fragment.

## 6. `wf` (DefinitionWf.lean)

Against F0:
- **Terms** may contain canonical domain values and interpreted hooks, at their declared sorts.
- **`requires`** is a Bool term over constructors, hooks and earlier functions. A self call inside a `requires` must decrease, like one in a right-hand side.
- **Rule left-hand sides:**
  - may repeat a variable, as kompile's non-linear patterns do, but must bind every variable;
  - a map pattern is a `_Map_` tree of elements `k |-> v`, `.Map`, and at most one variable of sort Map (the frame).
- **Function clauses** stay as in F0: linear, no map patterns (Q12), and pairwise non-overlapping patterns. Non-overlap is what makes first-match equal to the KORE equations' meaning: the KORE gives no clause precedence except through `[owise]`.
- **Totality is coverage** (Q4):
  - Either there is a catch-all clause, or the clauses without `requires` cover every well-sorted argument vector.
  - `covers` is the classic usefulness check over the user sorts' generators. Base sorts, K and KItem are covered only by a variable.
  - Running out of fuel answers `false`, so the check can only reject more.
  - fn.k's `size(z)`, `size(c(T))` is total by coverage; without `size(z)` it is rejected [V].
- **Declarations** may take Int, Bool and Map and return KItem (`syntax KItem ::= go(Int)`). `$PGM` may be K, KItem, Int or Bool.
- **Subsorts** stay of depth one, each subsort below at most one user sort; the subsort may now be Int or Bool (`syntax Exp ::= Int`, Q19). A value of `Exp` holding 5 is `inj{Int,Exp}(5)`, the same shape as a user subsort, so nothing else changes.
- **Rule attributes** without arguments are allowed only when they leave the rule's ground steps unchanged (`inertRuleAttrs`: `concrete`, `cool-like`, `cool`; Q18). `owise` and `priority` order rules, `symbolic` makes a rule never fire on ground terms, `anywhere` changes where it matches: definitions using them are not in F1 (their KORE is rejected by `wf` or by the round trip) [V: clock, symbolic-owise, concrete-symbolic].
- **Cells** are named apart, alphanumerically, with exactly one leaf `k` of content K.
- **No user symbol is named like an interpreted hook** (`hooksApart`, inside `namesOK`; 2026-11-08, Q22). Evaluation reads a name in `hookSigs` as the hook whatever the definition declares. With a fixed text that does not declare that hook (`none` lacks BOOL's and INT's), such a name is the user's own symbol in the KORE, with the user's clauses, so its meaning and `Step` would differ: `F1/Witnesses.lean`'s `hookDef` (a user `notBool_` defined as the identity) passed every other condition and stepped `run(z)` to `out(false)` where its KORE means `out(true)` [V]. `isHook_iff` (HooksApart.lean) proves the names `isHook` reads are exactly `hookSigs`'. No corpus definition is affected (findings/work/m24/diag.out: 35 in F1, none rejected by it) [V].

## 7. `emit` (Emit.lean, Prelude.lean)

F0's generator, with its definition-independent builders reused. The user module is the fixed text, then the definition's sentences; F1 compares up to sentence order, so the order is not kompile's. What is new:
- a domain value is written `\dv{SortS{}}("lit")`;
- a `requires` replaces the `\top{R}()` of an equation's premise and of each owise exclusion, and the `\top{C}()` of a rule's left-hand side, by `\equals{SortBool{},·}(req, \dv{SortBool{}}("true"))`;
- `symbol'Kywd'` is written only when there is one;
- **attributes are sorted by name**, as kompile writes them [V on 35 definitions]: id, `concrete`, `cool-like`, `label`, location, source, `owise`. This answers Q15: `cool-like` sits after the id and before the label;
- equations, not only rules, may carry `label{}("…")` [V: clock, owise-competitors];
- `$PGM:K` is initialized as `<k> project:K(#unboxKConfigValue(Init[$PGM])) </k>` (fr.k [V]).

**The configuration's text (Q8)** is generated from the cell tree `<generatedTop> config <generatedCounter/> </generatedTop>`, for every cell x [V: one cell, three cells (`<t><k/><c/></t>`), four cells (`<top><k/><mem/><n/></top>`), the store]:
- sorts `XCell`, `XCellOpt` (not for the top cell), `XCellFragment` (nodes);
- the cell constructor (location and source for the user's cells: the configuration's), `noXCell`, the fragment constructor, with their functional, injectivity and no-junk axioms (F0's builders, over F1's computed constructors);
- the initializer `initXCell`: of `Init:Map` when the cell holds `$PGM`, otherwise of no argument, declared `functional`/`total` with a functional axiom exactly when the initial value is always defined (constructors and total hooks only: `<state> .Map </state>` yes, `<store> a |-> 1 b |-> 2 </store>` no, since `_Map_` is partial) [V: map-framing];
- the initializer's equation (the presentation carries each leaf's initial value and each equation's id);
- `getGeneratedCounterCell` and its equation;
- `isX`/`projectX` for each cell sort, with the user's sorts.

**The fixed text (Q9)** is one of three constants, chosen by `Presentation.prelude`: none (peano), BOOL, INT (which brings BOOL; MAP adds nothing because the K prelude declares Map) [V]. Each was cut from krust's output for small definitions written for the purpose (`probe/extract_fixed.py`): the sentences common to all of them minus the configuration's text and the KItem no-junk axiom. The none text is F0's fixed text plus `import K` and the three `⊤ ∨ ⊥` axioms F0's `emit` wrote [V]. Each text's axioms are audited (F1-AUDIT.md).

Two shapes of kompile's output the generator reproduces from the presentation, both outside Γ_D's meaning:
- under INT, the selector-inverse lemma's attribute is `simplification{}("")`, otherwise `simplification{}()`; the translation reads the attribute's name only;
- **KItem's constructors** (Q17): kompile orders constructors by the name of the module that declares them, so a user constructor of sort KItem from a module named before `K-RUST-CONFIGURATION-VALUES` comes before the fixed `#KConfigValue`. That order shows inside KItem's no-junk axiom and the distinctness axioms with `#KConfigValue` (`¬(go ∧ #KConfigValue)` against `¬(#KConfigValue ∧ go)`). The presentation records how many user KItem constructors come first (`kconfigPos`); the axioms say the same in either order.

## 8. Statements (Statements.lean)

Soundness and completeness keeps its form. For every well-formed definition and a step function that lists `Step`'s successors (`StepIs`), five things hold:
- `StdModelOK`: Γ_D ∪ Γ_closure has a standard model;
- `ModelsStandard`: its models are standard;
- `OutputsGround`: every listed successor is a ground configuration;
- `StepSound`: every listed successor holds in every model of Γ_D;
- `StepComplete`: in every model of Γ_D ∪ Γ_closure, every step goes to a listed successor.

### 8.1 What changes

- **Ground terms are F1's values.** They are read as KORE by `GroundTerm.kore`, which writes a map as `_Map_` of its entries in key order, or `.Map` when empty.
  - CHOICE: the statements now quantify over values (`c.sortOf t = some topCellSort`) instead of KORE patterns with `groundSort`. The two are the same set through `GroundTerm.kore`; that is a checked-layer lemma.
- **Γ_D** = the curated translation of `emit c p` + Γ_cons + the arity schema of domain values + **ΓDom**. ΓDom has three parts:
  1. the graph of each interpreted symbol on ground values of its argument sorts, `f(⟦v̄⟧) = ⟦hook f v̄⟧`, or `⊥` where `hook` says undefined;
  2. distinct values of Int, Bool or Map denote distinct elements;
  3. no junk in Map.

  This settles `Q-domain-theories` for INT, BOOL, KEQUAL and MAP by a schema read off one frozen function, rather than one hand-written axiom per law.
- **`ModelsStandard` compares values, not skeletons.** Distinct values of one sort denote distinct elements. F0 compared skeletons because it had no domain theory (decision D1); with ΓDom (2), literals and maps are distinct too.
- **Γ_closure** is F0's construction over F1's rule patterns. A rule with `requires` contributes `∃x̄. (L ∧ ⌈req = true⌉ ∧ y ∈ R)`, with its left-hand side as written.
- **Γ_cons is built from F1's constructors** (`consItems`, F0's item builders over F1's computed constructor list, every cell's included). It was F0's `Cons.items` on a constructor view, exact for `<k>` only.
- **The step function is any one that `StepIs` the step relation** (Q14). F1's executable step now exists in the checked layer (Exec.lean); `step_iff` is proved (2026-11-08), so fixing `refStep` to it is now a statement decision, not a proof gap.

### 8.2 Obligations this creates (root track) [I]

- **The standard model (hooks on canonical values) must satisfy every non-simplification axiom of the fixed text.** The BOOL and INT texts add 24 and 31 such axioms; F1-AUDIT.md checks each against the standard model and finds none false. The proof is `StdModelOK`.

## 9. Peano in F1 (Peano.lean, Checks.lean)

- Every F0 core is an F1 core (`ofF0`).
- Peano's KORE is in F1: F1's `parse` reads it, `wf` accepts it, and `emit` gives it back up to sentence order (`#guard decide (F1 KCore.Peano.kore)`) [V]. A single kernel decision of it exceeds 12 GB (§12); the kernel route is F0Route's split, not yet written for F1.
- Peano's frozen properties are stated over F1's `Step` with the same text as PeanoProperties.lean [V: they elaborate].
- **One meaning moves (Q5).**
  - `pred_succ.statement : ∀ N : GroundTerm, Pred (s N) N` was true in F0 because `matchTerm` bound N to any ground term, ill-sorted ones included.
  - In F1, σ must be well-sorted. For an ill-sorted N no σ matches the first clause, so the catch-all gives `z`, and the statement is false for junk N.
  - `pred_succ_nat`, the statement for N of sort Nat, is proved with no `sorry` [V].
  - The right statement quantifies over values: `∀ N : Value peano "Nat"`.
- `step_ofF0` (F1's step is F0's on F0 definitions) needs F0's `wf` as a hypothesis, which the first draft lacked: F0's matching is untyped, so a rule whose variable is declared at a sort other than its position's could bind it to a value of another sort, which F1's well-sorted σ excludes [I]. Stated with the hypothesis, and since 2026-11-08 also with `hooksApart` on the image (the statement without it is refuted in `OfF0Counterexample.lean`); proved 2026-11-08.

## 10. Review cone

Cones were measured with kcore-spec's `#review_cone` on the draft (`cone/`), against F0's (findings/work/review-cone/):

| Cone | F0 | F1 draft | What grew |
|---|---:|---:|---|
| (i) user core: peano's statements | 298 | 597 | the generic frozen layer, 216 → 458 lines (Core +67 for cells, Value +44 for maps and canonical literals, Hooks 82 new, Evaluation +65 for `PatVal`, `Fails`, definedness). Also 132 lines because the draft's peano goes through `ofF0` and F0's data; native F1 data would be about 80. |
| (ii) emit route: `emit`, `wf` | 722 | 1,181 | F1's Emit.lean (251 in the cone, with the configuration's text and the attribute order), Prelude.lean (13), Definition.lean (82), DefinitionWf.lean (269, `wf` is now a root of this cone); the KORE syntax it builds (150) |
| (iii) root track | 2,437 | 2,459 | not comparable: F1's statements take any step function (no `refStep` body in the cone), Hooks/ΓDom are new; `parse` read by its type only |

The new generic frozen text a reviewer reads once is about 240 lines, of which Hooks.lean (82) is the part that needs domain knowledge.

## 11. Open questions, with recommendations

| | Question | Recommendation |
|---|---|---|
| Q1 | Denotational matching in the frozen layer (`PatVal`, well-sorted σ) | **Yes**: the matching-logic reading; maps and non-linear patterns need it |
| Q2 | Definedness-explicit evaluation (`Option` results, `Eval.undef`, strict hooks) | **Yes**; the alternative restricts `requires` to total expressions |
| Q3 | Function clauses stay pairwise apart by patterns, so clauses disambiguated only by exclusive `requires` (`f(N) = 1 requires N > 0`, `f(N) = 2 requires N <= 0`) are rejected and need an `[owise]` | **Keep for F1**; a certificate route (the user proves exclusivity) later if the corpus needs it |
| Q4 | Totality by coverage, where clauses with `requires` do not count | **Yes** |
| Q5 | Peano's statements move from `∀ N : GroundTerm` to values of the variable's sort | **Restate over `Value`**; that is what was meant, and ill-sorted junk never occurs in an evaluation from a configuration |
| Q6 | Domain values canonical only | **Yes** |
| Q7 | Domain theories as the graph of `hook` + distinctness + Map no-junk | **Yes**; it makes Hooks.lean the one thing to review |
| Q8 | Cell text in `emit`, and Γ_cons over F1's constructors | **Done** (§7, §8.1) |
| Q9 | The prelude as a family indexed by imports | **Done**: three texts (none, BOOL, INT), cut from krust's output and audited (§7, F1-AUDIT.md) |
| Q10 | `andThenBool`/`orElseBool` strict | **Strict in F1**, with a differential case. Laziness needs a non-strict hook kind |
| Q11 | `#if` (`ite`) | Defer: it is sort-parametric, and F1's terms have no sort arguments |
| Q12 | No map patterns in function clauses | **Yes for F1**: no clause with several matches |
| Q13 | `ModelsStandard` over values | **Yes** |
| Q14 | Soundness and completeness over any `StepIs` step function | Temporary. Fix `refStep` to the checked layer's executable step once it exists, as F0 did at M1.4 |
| Q15 | Position of the `cool-like` attribute | **Answered**: kompile sorts a sentence's attributes by name; `emit` does the same (§7) |
| Q16 | `Eval.undef` for a function with no applicable clause (outside `wf`) | **Keep**: it is what the positive "fails" reading needs, and `wf` (coverage) never reaches it |
| Q17 | KItem's constructor order around `#KConfigValue` depends on module names | CHOICE taken: **the presentation records it** (`kconfigPos`); the axioms mean the same in either order. The alternative, comparing modulo the order of a distinctness pair and of no-junk disjuncts, would add an invariance obligation to `reordered_sameModels` |
| Q18 | Which rule attributes F1 admits | CHOICE taken: **`concrete`, `cool-like`, `cool`** (they leave ground steps unchanged); `owise`, `priority`, `symbolic`, `anywhere`, `non-executable` stay out. Rules with priorities are the next semantic extension the corpus asks for (flow-clock, symbolic-owise) |
| Q19 | Int and Bool below a user sort (`syntax Exp ::= Int`) | CHOICE taken: **allowed**, depth one; it is what moved arithmetic and casted-chain into F1 |
| Q20 | Depth-one subsorts, one user supersort per sort | **Keep for F1; revisit for IMP**. IMP-shaped definitions put Int below two user sorts (`AExp`, `KResult`) and fail here (flow-fuzz-imp, kink's imp, pl-tutorial imp); lifting it reaches injection normal forms and F0's name-separation argument (NamesApart) |
| Q21 | The fixed texts are one per prelude key, picked by the presentation | CHOICE taken: `parse` picks the key by a symbol each text declares (`_-Int_`, `_andBool_`); the key decides nothing about soundness, since the whole text must still be reproduced |
| Q22 | A user constructor or function named like an interpreted hook | CHOICE taken (2026-11-08): **rejected by `wf`** (`hooksApart`). Evaluation dispatches hooks by name, so accepting the name would make `Step` use the hook where the KORE has the user's symbol; the alternative, dispatching by the imports' declarations, would put the prelude key into the frozen evaluation |

## 12. Evidence (revision 2)

- **F1 membership end to end** (`F1 k`, compiled): the 9 probe definitions, peano, fn.k, the store, and 23 of the T3 census's 94 definitions of classes F0, F0+BI and F0+BI+coll (10 of 26, 12 of 42 and 1 of 26). F0's check took 2 of them unedited. Why the others fail: findings/M2-spec-draft.md, revision 2.
- **The execution differential** of F1's executable step against krust on all of them: 9,140 configurations, 1,820 transitions, 108 configurations with several successors, 0 differences, 0 errors.
- **Kernel:** for peano, `wf d` (2.5 GB, 9 s) and `Reordered d.emit kore` (6.3 GB, 51 s) pass as separate decisions; `F1 kore` as one decision exceeds 12 GB; the `parse` stage by `kernel_rfl` passes (3.3 GB, 9 s), and `peano_F1 : F1 kore` follows from the three (`scratch/kc/KC/Final.lean`, three axioms). The stage was first rejected because the cause was a comparison `s == srt "KItem"` in `kconfigPosOf`: Lean v4.34.0 derives `BEq` for the nested `Kore.KSort` as an opaque (partial) function, which compiled code runs and the kernel cannot unfold, so the kernel's value of `parse` stayed stuck there. It is now `decide (s = srt "KItem")` (kore-lean's hand-written `DecidableEq`, which reduces). Not a divergence between the evaluators: the kernel never computed another value. `scratch/kc/KC/Opaque.lean` lists the opaque constants reachable from `parse`, `wf`, `emit` (F1 and F0) and `Reordered`: none, apart from `String.Internal.append` inside panic messages, which no successful evaluation reaches (the same holds for F0, whose kernel checks pass).
- **Theory audit** of the fixed texts: F1-AUDIT.md (no false axiom).


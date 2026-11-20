# KCore: specification (formerly F2, the M3 fragment)

**P1.4 (2026-11-09): F2 is `KCore`.** Its modules are `KcoreSpec/*.lean`, namespace `KCore`; F0 and F1 are removed. The KORE and matching-logic helpers they shared (KORE builders and readers, `Reordered` and its hint check, the translation, Γ_cons's items, `kernel_rfl`) are `KcoreSpec/Kore/`, namespace `KoreAML`. F2's fragment predicate `F2 k` is `Tied k`. F1's three fixed texts are `KCore.fixedNone`, `fixedBool`, `fixedInt`. The tests are `test/{Peano,KinkDet,NI,KernelTie,Ph,Probe}` with their scripts. The sections below are F2's text: read "F2" as KCore, and the F0 and F1 modules they cite as history (findings/P1.4-invariants-certificates-kcore.md).


**P2.1 (2026-11-09): derived tables and the generator.** The checked decisions read a definition's derived tables from an argument `T : Tables` (`Tables.lean`, `TablesChecked.lean`; `Det.*` take `T`), checked once by `T = tables c`; `Step` and the frozen definitions are unchanged. `kcore gen definition.kore OUTDIR NAME` (`KcoreGen.lean`, `lake build kcore`; `gen/gen.sh`, `gen/build.sh`) writes a definition's package; the example definitions' packages and their users' modules are `examples/` (`examples/run.sh`), replacing the hand-written `test/Peano`, `test/KinkDet`, `test/NI`, `test/Ph`, `test/KernelTie` and `test/Probe` (findings/P2.1-generator.md).

State: landed in kcore-spec beside F0 and F1, 2026-11-08 (M3.2), with the recommendations of §11 (Q23–Q37) and of the theory audit (KCORE-AUDIT.md) taken as decided (Sebastien's standing instruction: review does not block).
This document has for F2 the role F1-SPEC.md has for F1; every section it does not change is F1-SPEC.md's.
The Lean is `KcoreSpec/` (namespace `F2`), built by `lake build`. F0's and F1's modules, statements and proofs are unchanged; F1's three fixed texts are reused as F1's constants (`F1.fixedNone`, `F1.fixedBool`, `F1.fixedInt`). Drafted in `../m3-spec/` (history: ../findings/M3.0-spec-draft.md, ../findings/M3.1-theory-audit.md, ../findings/M3.2-f2-landing.md).
Marks: [V] checked by running or by kernel proof; [I] inference or argument; CHOICE: a decision not forced by the KORE's meaning.

Proved on landing (three axioms, guarded in `KcoreSpec/Checks.lean`):
- **`Exec.step_iff`** from `wf` alone (`StepIffWf.lean`), priorities included:

  ```lean
  theorem step_iff (d : Definition) (hwf : wf d = true) (x y : Config d.sem) :
      Step d.sem x y ↔ ∃ n, (successorsN d.sem n x.val).any (same · y.val) = true
  ```

  `step_iff_of` (`StepIff.lean`) proves it from the two decidable conditions `srReady` and `matchReady`, which `wf` gives (`NamesApart.lean`: `srReady_of_wf`, `matchReady_of_wf`). The priority premise needs one more argument than F1's proof, the one Q36 names: fuel monotonicity of the applicability test (§8).
- **Subject reduction** (`SubjectReduction.lean`, `rhs_sorted_wf`, `step_of_apply_wf`, `Eval.sorted_wf`), F1's proof carried over: the set hooks, `keys` and `removeAll` return values of their declared sorts (`hook_sorted`, `SetLaws.lean`), and the sort predicates are well-formed functions (`sortPreds_ctx`).
- **The closure of the declared subsorts is transitive** whatever the pairs (`NamesApart.declaredClosure_trans`): `Nat.repeat` composes with the declared pairs once per pair, and a shortest chain never repeats a sort.
- **Peano and the probe `f2-examples/prio.kore` are in F2 by the kernel** (since P2.1 by their generated packages' ties: `examples/peano/Peano/Tie.lean`, `examples/prio/Prio/Tie.lean`, built by `examples/run.sh`), each from three kernel facts in separate processes (§12).

Proved: soundness (`sound`, Sound.lean, §9) and completeness (`complete`, Sound.lean, §9).

Extended 2026-11-09 (M3.3, Q37 decided; §2.5): partial functions, functions declared `[total]`,
lookup patterns in function clauses, and clauses apart only by `requires`. `step_iff`, subject
reduction and determinism are re-proved over the extended `wf`; `Det.clausesExclusive_sound`
says what the new determinism condition means (`FnExclusive.lean`).

Changed 2026-11-10 (P2.3, findings/P2.3-builtins-by-module.md): **builtins by module**.
- The builtin library is a list of K modules (`Builtins.lean`, `library`): each module's declarations as numbers (sorts, sorts below KItem, token and byte sorts, subsorts, constructors, parameter symbols, total symbols, the ids of its sorts' generated equations) and its text (prelude/builtin.kore: its declarations and hand-written axioms as krust writes them). A definition imports the modules its KORE holds a sentence of (`Presentation.imports`, read off each builtin sentence's `Source` and `Location`).
- `Semantics.lib` is the union of the imported modules' sorts, subsorts and constructors (`libOf`); `wf` checks it (`Presentation.ok`) and the facts the generic theorems read of it (`Lib.ok`, in `idsOK`).
- Every builtin function or hooked symbol that Hooks.lean does not interpret is a parameter (`libParams`); the ones the rules and functions apply are the first `Semantics.params` (`paramsOK`).
- `emit` writes the builtin part from the kernel text, each imported module's text, and the axioms kompile generates from the signature for the library's sorts, constructors, subsorts and total symbols, by the generators it uses for the user's (`libBlocks`). The six fixed texts are gone.
- The registry numbers every library sort and symbol (FixedSignature.lean, BuiltinNames.lean): 28 sorts, 315 symbols. `Bytes` is a byte sort: its values are the literals of characters below 256 (`dvOK`).

Changed 2026-11-09 (P1.3, findings/P1.3-hooks-features.md): **parameter symbols**.
- A definition's own hooked symbols are `Semantics.params`. One whose `hook{}` attribute names an interpreted registry hook (`regHookNames`) has its meaning; any other is a parameter, interpreted by `Semantics.hooks`, with `c.withHooks H` the definition under the interpretation H.
- Evaluation's case `EvalTerm.param` reads `paramVal`, which keeps only values of the declared result sort. `wf` checks the parameters (`paramsOK`), `emit` writes them as `hooked-symbol`, and Γ_D gets their graphs. Patterns do not admit them.
- Determinism's ground refutation evaluates only constructor-and-hook terms. The decided conditions are equal on every interpretation, by kernel `rfl` (`Params.lean`).

Changed 2026-11-09 (P1.1, ARCHITECTURE.md §8, findings/P1.1-interning.md): **symbols and sorts are numbers**, literals are typed.
- A registry (`FixedSignature.lean`) numbers the builtin sorts and symbols with fixed names. A definition's own sorts and symbols are numbered after it, densely, in a fixed order: the cells' sorts then the user's, and after one sort predicate per own sort, the cells' symbols, the constructors and the functions (`Semantics.ownSorts`, `ownSyms`, `predOf`).
- `wf` checks the numbering (`idsOK`). The names are tables in the core, read only by `emit` and the translation; `Step`, evaluation and every decision compare numbers.
- A cell carries the numbers of its sorts and symbols (`CellIds`). The facts `NamesApart.lean` drew from the shape of names now come from the numbering.
- Literals are `Lit.int`, `Lit.bool`, `Lit.tok`, so every literal is canonical, and `parse` refuses a non-canonical Int text.
- Sections below that write symbols or sorts as strings describe their names; the core holds their numbers.

## 1. Scope

F2 is F1 plus what IMP's KORE asks for, read off the KORE (kink's `examples/imp`, the six other IMP definitions of the corpus, and the 16 other corpus definitions that came in with them):

| Addition | What in the KORE asks for it [V] | Section |
|---|---|---|
| several supersorts, chains of subsorts | `syntax KResult ::= Int \| Bool` beside `syntax AExp ::= Int \| Id`; DOMAINS' own `Int < IOInt`; kimp's `Int < Value < Expr` | §3 |
| rule priorities and `[owise]` rules | `priority{}("40")`, `owise{}()` on rewrite axioms (flow-clock, symbolic-owise) | §4 |
| generated sort predicates as functions | `strict`'s heating and cooling rules: `requires true andBool notBool isKResult(kseq(inj{AExp,KItem}(HOLE), dotk))` | §2.3 |
| freezer constructors | `#freezer_+_0(K) : KItem`, declared without location and source | §7 |
| Set values, `keys`, `Set:in` | IMP's declaration rule: `requires notBool (X in keys(Rho))`, kompiled to `Set:in(inj{Id,KItem}(X), keys(Rho))` | §5, §6 |
| token sorts with domain values | `\dv{SortId{}}("n")` in every IMP program and pattern | §5 |
| the builtin library and three more fixed texts | `imports DOMAINS` (kink's IMP: 3,118 fixed sentences), `INT` with `ID-SYNTAX` (kimp, collimp), `INT` with `ID` (imp-llvm) | §2.2, §7 |
| several top-level cells, configuration variables other than `$PGM` | `configuration <k> $PGM:Stmt </k> <env> $ENV:Map </env>` (kimp) | §2.4, §7 |
| definitions over several files | kimp's constructors and rules come from `expr.k` and `calc.k` through `requires` | §7 |
| attributes copied onto heating and cooling rules | `symbol'Kywd'{}("inc")`, `format{}("%1%2")` | §7 |

The heating and cooling rules need nothing else: they are ordinary rewrite rules over `kseq`, freezers, injections and as-patterns, with a `requires`. kompile writes no `heat` attribute; cooling rules carry `cool`, which F1 already admits as inert.

The shape of the fragment is F1's: `F2 k := parse k = .ok d ∧ wf d ∧ Reordered d.emit k` (Tie.lean, formerly Fragment.lean), with F2's `parse` (Parse.lean, unreviewed).

Out of F2, on purpose: `ensures`; sort-parametric symbols and `#if` (Q11); List values; Set and List patterns in left-hand sides (Q30); String hooks (String values exist, their hooks are uninterpreted); map patterns with a free key in function clauses; clauses that overlap other than as §2.5 allows. Partial functions, `[total]` functions and clauses apart by `requires` are in F2 since 2026-11-09 (§2.5); `fnOK` does not refuse a function with no clause (§2.5).

| Part | State | Evidence |
|---|---|---|
| Frozen layer: FixedSignature, Core, Value, Hooks, Evaluation, Step | landed from the draft; one reorder in `hookTable` (§13) | step cone 676 lines (§10) |
| Reviewed layer: Definition, DefinitionWf, Prelude, Emit, Tie (formerly Fragment), Statements | landed; `predsApart` added to `namesOK` (§13); Statements written on landing (§9) | 64 of 127 texts in F2, the draft's set exactly (§12) |
| Checked layer: Parse, Exec | landed; `parse` reads a priority without `String.toNat?` (§13) | `step_iff` proved; the differential rerun (§12) |
| Theory audit | KCORE-AUDIT.md | no axiom false in F2's standard model |

## 2. The core (Core.lean, FixedSignature.lean)

### 2.1 `Rule.prio`

A rule carries its priority, a natural number, smaller first. Without an attribute it is 50, with `owise` 200, with `priority(n)` n: K's documented defaults. The presentation records whether `priority{}("n")` was written (`RulePres.prioAttr`), so that `emit` writes the attribute back; the number is semantic, the spelling is not.

### 2.2 `Semantics.lib`: the builtin library

Importing DOMAINS adds sorts with values (String, Id), sorts with constructors (`IOError` with 70 constructors, `IOFile`, `Stream`), a KItem constructor (`#systemResult`), and subsorts (`Int < IOInt`, `String < IOString`, `IOError < IOInt, IOFile, IOString`); importing BYTES adds `Bytes`, `Endianness` and `Signedness`. These decide which ground terms are values and which sorts lie below KItem, so they belong to the semantics: `Lib` is a structure of sorts below KItem, subsorts, token sorts, byte sorts and constructors, and a definition's is the union of its imported modules' (`libOf`, Builtins.lean), checked by `Presentation.ok`.

CHOICE (Q31, revised by P2.3): one entry per K module, any union of them; not one entry per import set.

### 2.3 Generated sort predicates are functions

kompile writes, for every sort X below KItem, `isX(kseq(inj{X,KItem}(V), dotk)) = true` and an `[owise]` equation giving `false`; and `isK(K) = true`, `isKItem(kseq(I, dotk)) = true` with its `owise`. They are functions of the definition: `Semantics.sortPreds` builds exactly those clauses for each predicate that labels no function of `fns` (one that does is that function; `idsOK` keeps every function of `fns` off a registry symbol), `allFns = fns ++ sortPreds`, and `lookupFn` reads `allFns`. So `isKResult(kseq(inj{Int,KItem}(5), dotk))` is `true` exactly when the item's value injected into KResult is a value of KResult (`inj{Int,KResult}(5)`, since `Int < KResult`).
Why [I]: the equations are axioms of the KORE, so evaluation must give `isKResult` their meaning; reading them through the generic clauses adds no new meaning to review (Q27).

### 2.4 Several top-level cells

`config : List Cell`. With several top-level cells kompile gives the counter no `Opt` sort, no `noGeneratedCounterCell` and no place in the top cell's fragment (`Cell.counterOpt`, `topSorts`, `topCtors`). These change the signature, so they are frozen; they are what kompile declares (Q32).

### 2.5 Functions: partial, total, lookups, clauses apart by `requires` (2026-11-09, Q37)

**Partial functions.** A function declared without `[total]` (kompile writes only `function` on its symbol) may be partial. Where none of its clauses applies and it has no catch-all, the text does not determine the application: its sentences are the equations, each under its premise, and none speaks of a point where no premise holds; user_manual.md:540-544 bounds a function to at most one value there. So the function has the interpretation's value at such a point, and none where the interpretation gives none (`Eval.rest`, `Semantics.fnRest`, Evaluation.lean), and Γ states that value's graph, ⊥ where there is none (`ΓFallback`, Faithful.lean). With the equations this fixes `f(X̄)` to the first applying clause's value, and to the interpretation's where none applies; under `HookParams.none` that is no value. The statements over Γ hold for every interpretation, so a step that depends on such a point is one `Step` has exactly under the interpretations that give the value it needs.
A function with no clause is an uninterpreted symbol, which K treats as a parameter. `fnOK` holds of it, whether or not something applies it: it is `f.clauses.all (clauseOK f heads)`, each clause checked (`clauseOK`: patterns of the argument sorts, each map pattern with at most one frame, binding every variable; a Bool `requires` and `ensures`; a right-hand side of the result sort), and `Fn` has no field for a catch-all, which is a clause among `clauses` (priority 200). No equation speaks of such a function, so its value at every argument list of its sorts is the interpretation's (`Eval.rest`, `Semantics.fnRest`).

**Total functions.** `Fn.total` (Core.lean) records `[total]`: kompile then writes `functional` and `total` on the symbol (attributes in its order: `function`, `functional`, location, source, keyword, `total`) and the functional axiom `∃y. f(X̄) = y` (`prodAxioms`). That axiom is meaning, and Γ does not hold it: Γ holds no functional axiom of a function, so `Consistent` is the statement that the theory without the `[total]` axioms has a model, and the theory with them is the separate statement `has_model_total` (REVIEW-FA finding 2, decided 2026-11-15). `wf` does not refuse a `[total]` declaration (`fnOK` does not read `Fn.total`). `totalOK` confirms one where it can: a catch-all, or the clauses without `requires` cover the argument sorts; and every right-hand side total over the total hooks, the constructors, the sort predicates, the total functions before it and itself (self calls end by the certificate). A `[total]` function `totalOK` does not confirm is in `totalObligations` (DefinitionWf.lean), and its totality, a value at every argument list of its sorts, is an owed fact of `Obligations` (`CoreObligations`' second conjunct, Obligations.lean): every statement that reads the obligations assumes it, so where it is false, as under the reading of partial functions it can be, those statements say nothing of the text.
Example [V, `../findings/work/m33/niprobe.txt`]: k2lean's security checker `imp-sec.k` declares `conf` total, but `conf(X = _;, G) => lev(X, G) ==K hi` calls `lev`, which no clause defines at an identifier the labelling does not bind. So `conf(x = 1;, G)` is ⊥ where `x` is unlabelled, and `∃y. conf(…) = y` is false: `conf` is in `totalObligations` and its owed fact is false.

**Lookup patterns.** A clause argument may contain a map pattern `K |-> V M` with at most one frame (`noMapIn`), and a variable may occur more than once (`binds` replaces `linearCover`), provided the match fixes every variable (`clauseFixed`, by `uniq`, the condition determinism reads for rules): K's variables fixed by the arguments before it fix V and M, since a map's keys are unique. So a clause has at most one instance at given arguments, and the executable evaluation's first match is the relation's (`EvalComplete.lean`, through `uniqList_sound`, now in `Uniq.lean`). Example: `lev(X:Id, X |-> L:Level _:Map) => L`. A free key (`storeOk((K |-> V) E)`) has one instance per binding and stays outside F2.

**Clauses apart by `requires`.** Two clauses whose patterns overlap are allowed when they have one variable list and one pattern list and their `requires` exclude each other (`clausesExclusive`): one asserts a Bool literal the other negates, or one asserts `t ==K a` and the other `t ==K b` for ground values a ≠ b (`reqsExclusive`). `Det.clausesExclusive_sound` [V, three axioms] proves that two such clauses never both apply at one argument list, so the first-match reading of `Eval` is the meaning of all the equations, as for clauses apart by their patterns. Example: `sec(if (C) S1 else S2, G)` at `lev(C, G) ==K lo` and at `lev(C, G) ==K hi`.

**Membership** [V, `../findings/work/m32/diag.sh` on the 127 texts]: no text leaves F2 and none enters (64 of 127); four texts that fail on other conditions no longer fail on functions, and `kreg-fresh1`'s emit differs by one sentence fewer (a total function now emitted).

## 3. Several supersorts

- `Semantics.declaredClosure`: the transitive closure of the declared pairs (the user's and the library's). `subsorts` is it, plus the cells' `X < XOpt`, plus every sort below KItem.
- `wf` (`subsortsOK`): each declared pair `a < b` has a user sort b and a user or library value sort a; the closure is irreflexive; pairs are declared once. Depth and the number of supersorts are free.
- Values are unchanged: an injection is never nested, so a value of sort b holding an element of sort a has one representation through any chain (`inj{Int,Expr}(5)`).
- `PatVal`'s injection normal form is unchanged: `inj{AExp,KItem}(HOLE)` with `HOLE = inj{Int,AExp}(5)` and `inj{KResult,KItem}(V)` with `V = inj{Int,KResult}(5)` both denote `inj{Int,KItem}(5)`.
- Function-clause overlap uses common lower bounds (`meet`).
- Coverage stays conservative (Q35).

Proved on landing: the closure is transitive (`declaredClosure_trans`), and `subsorts` is transitive and irreflexive under `wf` (`subsorts_trans_of_wf`, `subsorts_irrefl_of_wf`): the user's, the library's and the cell sorts are apart and none is KItem (`predsApart`, §13), and a cell sort's `Opt` sort is no cell sort.

### 3.1 The injection theory (root track) [I]

The KORE's INJ composition axiom is false on non-chains (KCORE-AUDIT.md §4) and is `[simplification]`, so Γ_D leaves it out; Γ_cons states Cons-Coh on every chain of `subsorts`, which holds the closure.
F1's Cons-Dist `¬(inj{A,N}(x) = inj{B,N}(y))` for incomparable A, B is inconsistent with Cons-Coh as soon as A and B share a lower bound (KCORE-AUDIT.md §5: for every DOMAINS definition, through `IOError < IOInt, IOString`). Γ_cons states instead (`distLbItem`, Statements.lean):

    x ∈ ⟦A⟧ ∧ y ∈ ⟦B⟧ ∧ inj{A,N}(x) = inj{B,N}(y) → ⋁_{C ∈ lowerBounds(A,B)} ∃z:C. x = inj{C,A}(z) ∧ y = inj{C,B}(z)

for incomparable A, B with a common lower bound, and F1's Cons-Dist when they have none. It is true in the term model: equal injections have one core, whose own sort lies below both (KCORE-AUDIT.md §5).

## 4. Priorities and `owise`

kompile encodes priorities on rewrite rules only as attributes (`priority{}("40")`, `owise{}()`); it writes no negated competitor into a rule's premise, unlike an `[owise]` equation. Read with attributes ignored, an `owise` rule would fire beside the rules it yields to.

F2's meaning (Q23): a rule r applies to x under σ when σ is well-sorted, `lhs` denotes x and `req` evaluates to `true`. r rewrites x only if no rule of a smaller priority applies to x:

    lhs ∧ ⌈req = true⌉ ∧ ¬ ⋁_{r' : prio r' < prio r} ∃x̄'. (lhs' ∧ ⌈req' = true⌉)  ⇒  rhs

the negated-competitor premise kompile writes for `[owise]` equations, at every priority level. In Step.lean, `Step.rule` has `hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val`; `NotApplies` says that under every well-sorted σ' under which `lhs'` denotes x, r''s `requires` evaluates to something other than `true` (`RuleReqFails`). It is a positive statement, so `Step` stays one non-recursive constructor.
- A rule that applies blocks lower priorities whether or not its right-hand side is defined (Q26).
- An undefined `requires` does not block; a non-terminating one has no derivation, so it blocks.
- Equal priorities do not block each other.

Γ_D reads the two attributes into that premise (§9).

## 5. Values (Value.lean)

- `GroundTerm.set es`: elements strictly increasing in `GroundTerm.cmp`, each of sort KItem; equal sets are equal values.
- Token sorts: every literal of the library's token sorts (Id, and String under `coreIdString` and `domains`) is a value; distinct literals are distinct values. CHOICE (Q28): no lexical check.

## 6. Hooks (Hooks.lean)

F1's, plus `keys(M)`, `removeAll(M, S)`, `.Set`, `SetItem`, `_Set_` and `|Set` (union), `intersectSet`, `Set:difference`, `Set:in`, `<=Set`, `size` of a set. `Set:choice` stays uninterpreted.
`_Set_` is the union of two disjoint sets, undefined where they share a member (Q29), as `_Map_` is on maps sharing a key; `|Set` is union, total. K's sources state this reading (domains.md's prose, `|Set`'s defining rule, SET-KORE-SYMBOLIC's `#Ceil` lemma); the text's `[idem]` axiom `_Set_(S, S) = S` contradicts them and is not read (`UnreadReason.setIdempotence`; KCORE-AUDIT.md §3).

## 7. `wf`, `emit` and `parse`

`wf` against F1: functions as §2.5; subsorts and overlap as §3; declarations, cells and terms over the library's value sorts and constructors; the sort predicates callable in right-hand sides and `requires` (`rhsCtx`); `owise` and `priority` read into `prio`, the copied attributes `symbol'Kywd'`, `format`, `colors` inert (`inertArgAttrs`); and, added on landing, `predsApart` (§13).
`emit`: KItem's fixed constructors (the library's and `#KConfigValue`) as one block after the first `kconfigPos` user KItem constructors; freezers without location and source; a `src` per sentence from another file; priorities as `owise{}()` or `priority{}("n")`; several top-level cells, initializers reading `Init`, the counter equation's variables (`counterVars`); the builtin part by module (§2.2: the kernel text, the imported modules' texts, and the library's generated axioms; `simplification` written with or without an argument, `Presentation.simpArg`), its hand-written axioms audited one by one (KCORE-AUDIT.md §10).
`parse` (unreviewed): the imported modules read off the builtin sentences' sources and lines, the library's sorts excluded from the user's, user symbols from every file, freezers, priorities, the copied attributes, KItem's fixed block; the imported modules' parameter symbols the rules and functions apply.

## 8. The executable step (Exec.lean, checked layer)

For every rule, `ruleMatches` lists the well-sorted matches with their `requires` value (`some true`, `some false`, or `none` out of fuel). The applying rules are those with a match whose value is not `some false`; among them, the rules of the smallest priority give the successors of their matches with value `some true` (Q36).

Why `step_iff` holds [V, StepIff.lean]:
- `←`: a listed successor's rule r has the smallest applying priority, so every rule of a smaller priority has only `some false` values at that fuel (`successorsN_mem`). Given any well-sorted σ' under which such a rule's left-hand side denotes x, the matcher listed a σ₀ agreeing with σ' on the rule's variables (`rule_match_complete`); its `requires` evaluated there to a non-`true` result, and so it does under σ' (`req_sound`, through `evalT_congr` and `evalT_sound`). That is `NotApplies`.
- `→`: by `hprio`, every listed match of every rule of a smaller priority has a `requires` evaluating to a non-`true` result; they are finitely many, so one fuel N computes all of them, and every larger fuel too (`fuel_list` from `evalT_mono`). At `max N nq nr` none of those rules applies, the stepping rule does, so its priority is the minimum and its successor is listed (`successorsN_of`).
- The fuel monotonicity of the applicability test is exactly this: a value `some b` computed at some fuel is computed at every larger fuel (`evalT_mono_le`); `none` blocks lower priorities and lists nothing, so fuel never lets a lower rule fire.

Determinism [V, Determinism.lean, DetSound.lean]: `Det.deterministic_of` gives `Step c x y → Step c x y' → y = y'` from `ok`, `srReady`, `matchReady` and a decidable condition `detOK c`. Every rule's match must fix the variables of its right-hand side (`uniq`). Every two distinct rules of one priority must be apart (`apart`): their left-hand sides clash (`meet`), or their `requires`, read over one rule's variables through the subpatterns `meet` pairs, contain a literal the sorts refute, a literal without variables that evaluates to another value, or two complementary literals; or the two rules are alike (`sameRule`). Rules of different priorities need no check: the step by the larger one carries `hprio`, which says the smaller does not apply. A definition with genuine overlaps lists them: `Det.deterministic_except` from `detOKExcept c ovl` says two successors are equal or a listed pair of rules both apply, and `Det.witnessed_of` turns a decided `witnessOK` (both rules apply at a configuration x, and x has two different successors) into the fact that the listed pair is real (kink's IMP: its two `strict` pairs, both witnessed; `test/KinkDet/`, run by `test/kink-det.sh`). On the corpus 49 of the 64 F2 texts pass, and the 15 others fail only on genuine overlaps (findings/M3.3-imp-properties.md §3).

## 9. Statements (SoundDefs.lean, Sound.lean)

The statements are over the matching-logic theory of the definition's semantics, `Γ d.sem` (Faithful.lean), built from `Semantics` alone; `Γstep d.sem` is the step's closure axiom.
Statements.lean holds what they are built from (`GroundTerm.kore`, `den`, `distLbItem`, `applies`, `StepFn`, `StepIs`) and the decidable conditions they assume (`Semantics.coreOK`); Obligations.lean holds what they assume of the functions (`FnHyp`) and the named obligations (`CoreObligations`, `Obligations`).

- **Soundness** (`Sound d`): `Γ d.sem ∪ Γstep d.sem` has a model, and every `Step d.sem x y` gives `Γ d.sem ⊧ ⟦x⟧ ⇒ •⟦y⟧`.
  `sound (hwf : wf d = true) (hob : Obligations d) : Sound d` is proved, and `sound_withHooks` for every interpretation of the parameters under the obligations stated for it, of a definition without an open generator.
  `wf` decides the conditions the theory reads beyond `okAll` and `srReady` (`faithOK`, FaithOK.lean); `hypSound_of` (HypWf.lean) gives `HypSound` from `wf` alone, and `hypModel_of` gives `HypModel` from `wf` and `Obligations`.
- **Completeness** (`Complete d ref`): for a step function `ref` with `StepIs d.sem ref`, `(Γ d.sem ∪ Γstep d.sem) ⊧ ⟦x⟧ ⇒ ◦ ⋁_{y ∈ ref x} ⟦y⟧` for every configuration x.
  `complete (hwf) (hob) : Complete d ref` is proved, and `complete_withHooks` for every interpretation of the parameters under the obligations stated for it, of a definition without an open generator (`step_complete`, FaithfulComplete.lean): the closure axiom puts a successor of x's element in a rule's disjunct at a valuation of the rule's variables in their sorts; the left-hand side read downwards (`patVal_backC`) makes that valuation a well-sorted substitution of values (every variable of a rule occurs in its left-hand side), the `requires` and the right-hand side read upwards at it (`evalTerm_den4`, with `evalTerm_total`) evaluate to `true` and to a configuration denoting the successor, and a rule of a smaller priority that applied would put x's element in its `applies` (`applies_holds`), which the disjunct negates.

## 10. Review cone

`#review_cone` on F2 as landed (`test/ReviewCone.lean`, into `../findings/work/review-cone/f2-*.txt`):

| Cone | F1 | F2 | File |
|---|---:|---:|---|
| the step relation (`Step`) | 458 | 818 | `f2-i-step.txt` (F1's: `../m3-spec/cone/f1-step.txt`) |
| the emit route (`emit`, `Definition.emit`, `wf`) | 1,193 | 2,850 | `f2-ii-emit-route.txt` |
| the root track (`Sound`, `Complete`, `StepIs`, `wf`, `Tied`; `parse` by its type) | 2,381 | 4,297 | `f2-iii-root-track.txt` |

The step cone's largest parts are Core.lean (193 lines), Hooks.lean (149), FixedSignature.lean (143), Evaluation.lean (142) and Value.lean (130). The emit route adds to them chiefly Emit.lean (371), DefinitionWf.lean (358, `wf`'s checks), Definition.lean (216), the builtin data and names (346) and FaithOK.lean (162, the theory's decidable conditions, a conjunct of `wf`). The root track adds the theory Γ that `Sound` and `Complete` speak of: Faithful.lean (376), Kore/Translate.lean (294) and Statements.lean (85), with Sound.lean's two definitions (12).

## 11. Decisions (Q23–Q37, as recommended in the draft)

| | Question | Decision |
|---|---|---|
| Q23 | Priorities and `[owise]` on rewrite rules | **Given meaning** (§4): Step's `hprio`, Γ_D's negated-competitor premise read from the attributes |
| Q24 | Several supersorts and chains | **Allowed** (§3), a strict partial order closed by `declaredClosure` |
| Q25 | Cons-Dist with injections from sorts sharing a lower bound | **Refined** to the disjunction over common lower bounds (§3.1, `distLbItem`) |
| Q26 | Does a higher-priority rule whose right-hand side is undefined block? | **Yes** |
| Q27 | The `isX` predicates as functions (`sortPreds`) | **Yes** |
| Q28 | Token literals | **Every literal a value, distinct literals distinct**; no lexical check |
| Q29 | `_Set_` | **Disjoint union, partial** |
| Q30 | Set and List patterns in left-hand sides | **Matched** (`collPatternHooks`: `SetItem(P) S` one match per member, findings/RD-3-wasm-mir.md §10) |
| Q31 | The builtin library as a frozen enumeration, six fixed texts | **Replaced** (P2.3): the library by K module, any union of modules |
| Q32 | The counter's missing `Opt` sort with several top-level cells | **Kept**: the signature kompile declares |
| Q33 | Definitions over several files | **Yes**, a `src` per presentation record |
| Q34 | Theory audit of the three new fixed texts | **Done** (KCORE-AUDIT.md) |
| Q35 | `covers` with chains | **Conservative** |
| Q36 | Out-of-fuel `requires` in the executable step | **Blocks, gives nothing**; `step_iff` for some fuel, proved (§8) |
| Q37 | Clauses apart only by `requires`, partial functions without catch-all | **Decided 2026-11-09** (§2.5): where no clause of a partial function applies it has the interpretation's value, and none where the interpretation gives none (`Eval.rest`, `Semantics.fnRest`), and Γ states that value's graph (`ΓFallback`); no axiom closes a function; `[total]` never refused by `wf`: one `totalOK` does not confirm is an owed fact (`totalObligations`; REVIEW-FA finding 2); clauses apart by exclusive `requires` (`clausesExclusive`, proved sound); lookup patterns whose match fixes every variable |

## 12. Evidence

- **Membership** [V, compiled; `../findings/work/m32/diag.sh`, output `../findings/work/m32/diag-all.txt`]: on the 127 texts of the M3.0 run, the landed F2 gives the draft's verdicts exactly (64 in F2, each failing text the same first failure); `predsApart` rejects none.
- **Kernel** [V]: peano and `f2-examples/prio.kore` are in F2 (the generated `Peano.tied`, `Prio.tied` since P2.1; before, `test/KernelTie/Final.lean`: `peano_F2`, `prio_F2`, and `Exec.step_iff` for both, three axioms). Each of the six facts in its own process under the 12 GiB address-space cap, one thread (`test/kernel-tie.sh`): peano's `parse` 14 s and 3.8 GB peak resident, `wf` 5 s and 2.6 GB, `Reordered` 22 s and 6.4 GB; the probe's 8 s and 3.9 GB, 4 s and 2.6 GB, 16 s and 6.7 GB. The six in one process exceed the cap (`std::bad_alloc`). The probe's `parse` first failed in the kernel: it read a priority with `String.toNat?`, whose iterators reach an opaque well-founded fixpoint in Lean v4.34.0 (§13).
- **IMP by the kernel: not attempted**; it stays compiled-checked (M3.0). kink's IMP text is about 700 kB against peano's 108 kB, with the 586 kB DOMAINS fixed text; peano's single `Reordered` decision already takes 6.4 GB, so IMP's would not fit the 12 GiB cap as one decision. A route would split `Reordered` per sentence block, as F0Route does for F0 and `F1/Tie.lean`'s permutation hint does for F1, and `parse` per stage; neither is written for F2.
- **The differential rerun** [V] on the landed step against krust (`../m3-spec/diff/run-landed.sh`, `table-landed.md`): the programs of the IMP definitions, the IMP definitions on enumerated configurations, and a sample of the rest, plus the new probe; 26 runs, 15,190 configurations, 13,158 transitions, 0 differences, 0 errors. The 23 subjects run at M3.0's caps give M3.0's counts exactly (../findings/M3.2-f2-landing.md §4).
- **Theory audit**: KCORE-AUDIT.md.

## 13. Changes on landing, and what proved false

Nothing stated in the draft proved false. Five changes, each argued from the semantics:
1. **`predsApart` in `namesOK`** (Tie.lean): the functions evaluation reads (`allFns`) have distinct labels. `lookupFn` takes the first function of a label, so a user function named like a sort predicate, or a user sort named like a library sort (two predicates `LblisInt`), would make "the function f" ambiguous between the core and the KORE. The declaration check of `namesOK` already excludes both when the fixed text declares the library's sorts and predicates, as the six texts do, but deriving it from `namesOK` needs a decision over the fixed texts; stated on the core it is where evaluation reads it, and it gives `step_iff` the distinct labels, the separation of user, library and cell sorts, and `KItem ∉` user sorts at once (`NamesApart.preds_facts`). It rejects no text of the 127 [V].
2. **`hookTable`'s order**: `removeAll` before `keys`, as in `hookSigs` (`HooksApart.hookTable_names` compares the two lists). Lookup is by name and the names are distinct, so no meaning changes.
3. **`parse` reads `priority{}("n")` with `digitsVal`**, not `String.toNat?` (§12): the same value on digit strings; the round trip checks the rest.
4. **`step_of_apply` takes the priority premise**, since `Step` has it: a rule application is a step when, in addition, no rule of a smaller priority applies.
5. **Statements.lean written** (§9): not drafted in M3.0.
